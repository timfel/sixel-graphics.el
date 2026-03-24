;;; sixel-graphics.el --- Display images in terminal Emacs via Sixel -*- lexical-binding: t; -*-

;; Copyright (C) 2026

;; Author: Tim Felgentreff <timfelgentreff@gmail.com>
;; Version: 0.1.0
;; Keywords: terminals, images, multimedia
;; Package-Requires: ((emacs "29.0"))
;; URL: https://github.com/timfel/sixel-graphics.el

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;;; Commentary:

;; Display images in terminal Emacs using Sixel graphics.
;;
;; This is a Sixel port of `kitty-graphics.el'.  It keeps the same broad
;; integration strategy: overlays reserve blank screen space in Emacs buffers
;; and a refresh pass paints terminal graphics at the corresponding terminal
;; coordinates.
;;
;; Unlike Kitty graphics there is no terminal-side placement ID to update in
;; place, so refreshes explicitly clear old regions before drawing the current
;; image payload.

;;; Code:

(require 'cl-lib)
(require 'subr-x)
(require 'url-parse)
(require 'url-util)

;; Forward declarations for optional dependencies.
(declare-function org-element-context "org-element" ())
(declare-function org-element-type "org-element" (element))
(declare-function org-element-property "org-element" (property element))
(declare-function org-attach-dir "org-attach" (&optional create-if-not-exists-p))
(declare-function org-link-preview "org" (&optional arg beg end))
(declare-function org-link-preview-region "org" (&optional include-linked refresh beg end))
(declare-function org-fold-folded-p "org-fold" (&optional pos spec-or-alias))
(declare-function org--latex-preview-region "org" (beg end))
(declare-function org-clear-latex-preview "org" (&optional beg end))
(declare-function org--make-preview-overlay "org" (beg end movefile imagetype))
(declare-function org-combine-plists "org" (a b))
(declare-function doc-view-mode-p "doc-view" ())
(declare-function doc-view-insert-image "doc-view" (file &rest args))
(declare-function doc-view-enlarge "doc-view" (factor))
(declare-function doc-view-scale-reset "doc-view" ())
(declare-function dired-get-file-for-visit "dired" ())
(declare-function markdown-overlays--resolve-image-url "markdown-overlays" (url))
(declare-function evil-local-set-key "evil" (state key def))
(defvar org-format-latex-options)
(defvar dirvish-image-exts)
(defvar dirvish-preview-dispatchers)
(defvar dirvish--available-preview-dispatchers)

(defgroup sixel-graphics nil
  "Display images in terminal Emacs via Sixel."
  :group 'multimedia
  :prefix "sixel-graphics-")

(defcustom sixel-graphics-max-width 120
  "Maximum image width in terminal columns for inline images."
  :type 'integer
  :group 'sixel-graphics)

(defcustom sixel-graphics-max-height 40
  "Maximum image height in terminal rows for inline images."
  :type 'integer
  :group 'sixel-graphics)

(defcustom sixel-graphics-render-delay 0.03
  "Delay in seconds before coalesced image refresh work runs."
  :type 'number
  :group 'sixel-graphics)

(defcustom sixel-graphics-encoder-program "img2sixel"
  "Program used to encode raster images to Sixel."
  :type 'string
  :group 'sixel-graphics)

(defcustom sixel-graphics-encoder-args nil
  "Extra arguments passed to `sixel-graphics-encoder-program'."
  :type '(repeat string)
  :group 'sixel-graphics)

(defcustom sixel-graphics-identify-program "identify"
  "Optional program used to probe source image dimensions."
  :type 'string
  :group 'sixel-graphics)

(defcustom sixel-graphics-cache-size 128
  "Maximum number of cached Sixel payload entries."
  :type 'integer
  :group 'sixel-graphics)

(defcustom sixel-graphics-temp-file-limit 32
  "Maximum number of unreferenced temporary image files to keep around."
  :type 'integer
  :group 'sixel-graphics)

(defcustom sixel-graphics-temp-directory
  (locate-user-emacs-file "sixel-graphics-cache/")
  "Directory used for temporary image files created from SHR image data."
  :type 'directory
  :group 'sixel-graphics)

(defcustom sixel-graphics-cell-width 8
  "Fallback terminal cell width in pixels."
  :type 'integer
  :group 'sixel-graphics)

(defcustom sixel-graphics-cell-height 16
  "Fallback terminal cell height in pixels."
  :type 'integer
  :group 'sixel-graphics)

(defcustom sixel-graphics-debug nil
  "When non-nil, append debug messages to `sixel-graphics--log-file'."
  :type 'boolean
  :group 'sixel-graphics)

(defvar sixel-graphics-mode)
(defvar sixel-graphics--log-file "/tmp/sixel-graphics.log")
(defvar sixel-graphics--probe-result nil)
(defvar sixel-graphics--terminal-kind 'unknown)
(defvar sixel-graphics--cache (make-hash-table :test #'equal))
(defvar sixel-graphics--cache-lru nil)
(defvar sixel-graphics--temp-files nil)
(defvar sixel-graphics--render-timer nil)
(defvar sixel-graphics--refresh-pending nil)

(defvar-local sixel-graphics--overlays nil)
(defvar-local sixel-graphics--image-scale 1.0)
(defvar-local sixel-graphics--doc-view-overlay nil)
(defvar-local sixel-graphics--doc-view-scale 1.0)
(defvar-local sixel-graphics--doc-view-current-file nil)

(defun sixel-graphics--log (fmt &rest args)
  "Append a debug message using FMT and ARGS."
  (when sixel-graphics-debug
    (let ((msg (concat (format-time-string "%H:%M:%S.%3N ")
                       (apply #'format fmt args)
                       "\n")))
      (ignore-errors
        (append-to-file msg nil sixel-graphics--log-file)))))

(defun sixel-graphics--env (name)
  "Return environment variable NAME if it is non-empty."
  (let ((value (getenv name)))
    (and (stringp value)
         (not (string-empty-p value))
         value)))

(defun sixel-graphics--detect-terminal-kind ()
  "Return a symbol describing the current terminal family."
  (let ((wt-session (sixel-graphics--env "WT_SESSION"))
        (wt-profile-id (sixel-graphics--env "WT_PROFILE_ID"))
        (tty-type (downcase (or (frame-parameter nil 'tty-type) "")))
        (term-program (downcase (or (sixel-graphics--env "TERM_PROGRAM") "")))
        (term (downcase (or (sixel-graphics--env "TERM") ""))))
    (cond
     ((or wt-session wt-profile-id) 'windows-terminal)
     ((string-match-p "mlterm" tty-type) 'mlterm)
     ((string-match-p "xterm" tty-type) 'xterm)
     ((string-match-p "mlterm" term) 'mlterm)
     ((string-match-p "xterm" term) 'xterm)
     ((string-match-p "contour" term-program) 'contour)
     ((string-match-p "foot" term) 'foot)
     (t 'unknown))))

(defun sixel-graphics--terminal-supports-sixel-p (terminal-kind)
  "Return non-nil when TERMINAL-KIND is a likely Sixel-capable terminal."
  (memq terminal-kind '(windows-terminal mlterm xterm contour)))

(defun sixel-graphics--encoder-available-p ()
  "Return the configured encoder path, or nil."
  (when (and sixel-graphics-encoder-program
             (not (string-empty-p sixel-graphics-encoder-program)))
    (executable-find sixel-graphics-encoder-program)))

(defun sixel-graphics--identify-available-p ()
  "Return the configured identify tool path, or nil."
  (when (and sixel-graphics-identify-program
             (not (string-empty-p sixel-graphics-identify-program)))
    (executable-find sixel-graphics-identify-program)))

(defun sixel-graphics--query-cell-size ()
  "Return the current frame's cell size as (WIDTH . HEIGHT)."
  (let ((width (frame-char-width))
        (height (frame-char-height)))
    (cons (if (> width 1) width sixel-graphics-cell-width)
          (if (> height 1) height sixel-graphics-cell-height))))

(defun sixel-graphics--probe-terminal ()
  "Probe the current terminal for Sixel support."
  (let* ((tty (not (display-graphic-p)))
         (terminal-kind (sixel-graphics--detect-terminal-kind))
         (encoder (sixel-graphics--encoder-available-p))
         (heuristic-support
          (and tty (sixel-graphics--terminal-supports-sixel-p terminal-kind)))
         (cell-size (sixel-graphics--query-cell-size))
         (supported (and tty encoder heuristic-support)))
    (setq sixel-graphics--terminal-kind terminal-kind)
    (setq sixel-graphics--probe-result
          (list :time (current-time)
                :tty tty
                :terminal-kind terminal-kind
                :tty-type (frame-parameter nil 'tty-type)
                :encoder encoder
                :heuristic-support heuristic-support
                :cell-size cell-size
                :supported supported))
    (sixel-graphics--log
     "probe tty=%s terminal=%s encoder=%s supported=%s cell=%S"
     tty terminal-kind encoder supported cell-size)
    sixel-graphics--probe-result))

(defun sixel-graphics--ensure-probed ()
  "Return the cached probe result, probing first if needed."
  (or sixel-graphics--probe-result
      (sixel-graphics--probe-terminal)))

(defun sixel-graphics--supported-p ()
  "Return non-nil if the current session appears to support Sixel."
  (plist-get (sixel-graphics--ensure-probed) :supported))

(defun sixel-graphics-reprobe-terminal ()
  "Re-run terminal probing and report the current status."
  (interactive)
  (setq sixel-graphics--probe-result nil)
  (let* ((result (sixel-graphics--probe-terminal))
         (supported (plist-get result :supported)))
    (message "sixel-graphics: %s terminal=%s encoder=%s"
             (if supported "supported" "unsupported")
             (plist-get result :terminal-kind)
             (or (plist-get result :encoder) "missing"))))

(defun sixel-graphics--file-signature (file)
  "Return a cache identity for FILE."
  (let* ((file (expand-file-name file))
         (attrs (file-attributes file)))
    (unless attrs
      (error "Image file does not exist: %s" file))
    (list file
          (file-attribute-size attrs)
          (file-attribute-modification-time attrs))))

(defun sixel-graphics--cache-key (kind identity width height)
  "Build a cache key for KIND, IDENTITY, WIDTH and HEIGHT."
  (list :kind kind
        :identity identity
        :width width
        :height height
        :terminal sixel-graphics--terminal-kind))

(defun sixel-graphics--cache-touch (key)
  "Move KEY to the front of the LRU list."
  (setq sixel-graphics--cache-lru
        (cons key (delete key sixel-graphics--cache-lru))))

(defun sixel-graphics--cache-put (key entry)
  "Store ENTRY under KEY and update LRU state."
  (puthash key (plist-put entry :last-use (current-time))
           sixel-graphics--cache)
  (sixel-graphics--cache-touch key)
  (while (and (> (hash-table-count sixel-graphics--cache)
                 (max 1 sixel-graphics-cache-size))
              sixel-graphics--cache-lru)
    (let ((victim (car (last sixel-graphics--cache-lru))))
      (remhash victim sixel-graphics--cache)
      (setq sixel-graphics--cache-lru (butlast sixel-graphics--cache-lru)))))

(defun sixel-graphics--cache-get (key)
  "Return cached value for KEY, or nil."
  (when-let ((entry (gethash key sixel-graphics--cache)))
    (sixel-graphics--cache-touch key)
    entry))

(defun sixel-graphics--clear-cache ()
  "Clear the encoded payload cache."
  (interactive)
  (clrhash sixel-graphics--cache)
  (setq sixel-graphics--cache-lru nil))

(defun sixel-graphics--fit-size (width height max-width max-height
                                      &optional allow-upscale)
  "Fit WIDTH and HEIGHT within MAX-WIDTH and MAX-HEIGHT.

When ALLOW-UPSCALE is non-nil, scaling larger than the source size is
permitted."
  (cond
   ((or (<= width 0) (<= height 0))
    (cons width height))
   ((or (null max-width) (null max-height))
    (cons width height))
   (t
    (let* ((wscale (/ (float max-width) width))
           (hscale (/ (float max-height) height))
           (scale (min (if allow-upscale wscale (min 1.0 wscale))
                       (if allow-upscale hscale (min 1.0 hscale)))))
      (cons (max 1 (floor (* width scale)))
            (max 1 (floor (* height scale))))))))

(defun sixel-graphics--pixel-size-to-cells (width height)
  "Convert pixel WIDTH and HEIGHT to terminal cell dimensions."
  (pcase-let ((`(,cell-width . ,cell-height) (sixel-graphics--query-cell-size)))
    (cons (max 1 (ceiling (/ (float width) (max 1 cell-width))))
          (max 1 (ceiling (/ (float height) (max 1 cell-height)))))))

(defun sixel-graphics--image-file-p (file)
  "Return non-nil if FILE looks like a supported raster image."
  (and (stringp file)
       (string-match-p (image-file-name-regexp) file)))

(defun sixel-graphics--payload-pixel-size (payload)
  "Return PAYLOAD raster size as (WIDTH . HEIGHT), or nil."
  (when (and (stringp payload)
             (string-match "\"[0-9]+;[0-9]+;\\([0-9]+\\);\\([0-9]+\\)" payload))
    (cons (string-to-number (match-string 1 payload))
          (string-to-number (match-string 2 payload)))))

(defun sixel-graphics--image-pixel-size-from-identify (file)
  "Return FILE image dimensions from `identify', or nil."
  (when-let ((identify (sixel-graphics--identify-available-p)))
    (with-temp-buffer
      (when (zerop (process-file identify nil t nil "-format" "%w %h" file))
        (goto-char (point-min))
        (when (re-search-forward "\\([0-9]+\\) \\([0-9]+\\)" nil t)
          (cons (string-to-number (match-string 1))
                (string-to-number (match-string 2))))))))

(defun sixel-graphics--encode-file-raw (file &optional width height)
  "Encode FILE as Sixel at WIDTH and HEIGHT."
  (let* ((file (expand-file-name file))
         (identity (sixel-graphics--file-signature file))
         (width-arg (when width (number-to-string width)))
         (height-arg (when height (number-to-string height)))
         (key (sixel-graphics--cache-key 'payload identity width-arg height-arg))
         (cached (sixel-graphics--cache-get key)))
    (or cached
        (progn
          (unless (file-readable-p file)
            (error "Image file is not readable: %s" file))
          (unless (sixel-graphics--encoder-available-p)
            (error "Sixel encoder not found: %s" sixel-graphics-encoder-program))
          (with-temp-buffer
            (let ((status (apply #'process-file
                                 sixel-graphics-encoder-program
                                 nil t nil
                                 (append sixel-graphics-encoder-args
                                         (when width
                                           (list "-w" width-arg))
                                         (when height
                                           (list "-h" height-arg))
                                         (list file)))))
              (unless (zerop status)
                (error "Sixel encoding failed for %s" file))
              (let* ((payload (buffer-string))
                     (pixel-size (or (sixel-graphics--payload-pixel-size payload)
                                     (and width height (cons width height)))))
                (unless pixel-size
                  (error "Could not determine Sixel raster size for %s" file))
                (pcase-let ((`(,cols . ,rows)
                             (sixel-graphics--pixel-size-to-cells
                              (car pixel-size) (cdr pixel-size))))
                  (let ((entry (list :source file
                                     :payload payload
                                     :pixel-width (car pixel-size)
                                     :pixel-height (cdr pixel-size)
                                     :cols cols
                                     :rows rows)))
                    (sixel-graphics--cache-put key entry)
                    entry)))))))))

(defun sixel-graphics--image-pixel-size (file)
  "Return FILE image dimensions as (WIDTH . HEIGHT)."
  (let* ((file (expand-file-name file))
         (identity (sixel-graphics--file-signature file))
         (key (sixel-graphics--cache-key 'size identity nil nil))
         (cached (plist-get (sixel-graphics--cache-get key) :value)))
    (or cached
        (let ((size (or (sixel-graphics--image-pixel-size-from-identify file)
                        (let ((entry (sixel-graphics--encode-file-raw file)))
                          (cons (plist-get entry :pixel-width)
                                (plist-get entry :pixel-height))))))
          (unless size
            (error "Could not determine image dimensions for %s" file))
          (sixel-graphics--cache-put key (list :value size))
          size))))

(defun sixel-graphics--prepare-entry (file max-cols max-rows &optional scale)
  "Return a cached Sixel entry for FILE sized for MAX-COLS and MAX-ROWS."
  (let* ((scale (or scale 1.0))
         (source-size (sixel-graphics--image-pixel-size file))
         (cell-size (sixel-graphics--query-cell-size))
         (base-limits (cons (* (max 1 max-cols) (car cell-size))
                            (* (max 1 max-rows) (cdr cell-size))))
         (base-size (sixel-graphics--fit-size
                     (car source-size) (cdr source-size)
                     (car base-limits) (cdr base-limits)))
         (base-cells (sixel-graphics--pixel-size-to-cells
                      (car base-size) (cdr base-size)))
         (target-limits (cons (* (max 1 (round (* scale (car base-cells))))
                                 (car cell-size))
                              (* (max 1 (round (* scale (cdr base-cells))))
                                 (cdr cell-size))))
         (scaled-size (sixel-graphics--fit-size
                       (car source-size) (cdr source-size)
                       (car target-limits) (cdr target-limits)
                       (> scale 1.0))))
    (sixel-graphics--encode-file-raw file
                                    (car scaled-size)
                                    (cdr scaled-size))))

(defun sixel-graphics--terminal-object (&optional window)
  "Return the terminal object for WINDOW or the selected window."
  (frame-terminal (window-frame (or window (selected-window)))))

(defun sixel-graphics--send (string &optional window)
  "Send STRING to WINDOW's terminal."
  (when (and string (not (string-empty-p string)))
    (send-string-to-terminal string (sixel-graphics--terminal-object window))))

(defun sixel-graphics--sync-begin ()
  "Begin synchronized output if the terminal supports it."
  (ignore-errors
    (sixel-graphics--send "\e[?2026h")))

(defun sixel-graphics--sync-end ()
  "End synchronized output if the terminal supports it."
  (ignore-errors
    (sixel-graphics--send "\e[?2026l")))

(defun sixel-graphics--move-cursor (column row)
  "Return a control sequence that moves the cursor to COLUMN and ROW."
  (format "\e[%d;%dH" row column))

(defun sixel-graphics--save-cursor ()
  "Return a control sequence that saves the cursor position."
  "\e7")

(defun sixel-graphics--restore-cursor ()
  "Return a control sequence that restores the cursor position."
  "\e8")

(defun sixel-graphics--clear-rect (window column row columns rows)
  "Clear a rectangle in WINDOW at COLUMN/ROW with size COLUMNS/ROWS."
  (when (and (> columns 0) (> rows 0))
    (let ((chunks (list (sixel-graphics--save-cursor))))
      (dotimes (offset rows)
        (push (sixel-graphics--move-cursor column (+ row offset)) chunks)
        (push (format "\e[%dX" columns) chunks))
      (push (sixel-graphics--restore-cursor) chunks)
      (sixel-graphics--send (apply #'concat (nreverse chunks)) window))))

(defun sixel-graphics--render-entry (window entry column row)
  "Render ENTRY in WINDOW with its top-left corner at COLUMN and ROW."
  (when-let ((payload (plist-get entry :payload)))
    (sixel-graphics--send
     (concat (sixel-graphics--save-cursor)
             (sixel-graphics--move-cursor column row)
             payload
             (sixel-graphics--restore-cursor))
     window)))

(defun sixel-graphics--make-blank-display (cols rows)
  "Create a blank display string of COLS columns and ROWS lines."
  (mapconcat (lambda (_)
               (propertize (make-string cols ?\s) 'face 'default))
             (number-sequence 1 rows)
             "\n"))

(defun sixel-graphics--make-overlay (beg end entry &optional props)
  "Create an overlay from BEG to END for ENTRY and optional PROPS."
  (let* ((cols (plist-get entry :cols))
         (rows (plist-get entry :rows))
         (ov (make-overlay beg end nil t nil)))
    (overlay-put ov 'display
                 (concat (sixel-graphics--make-blank-display cols rows) "\n"))
    (overlay-put ov 'face 'default)
    (overlay-put ov 'sixel-graphics t)
    (overlay-put ov 'sixel-graphics-entry entry)
    (overlay-put ov 'sixel-graphics-cols cols)
    (overlay-put ov 'sixel-graphics-rows rows)
    (while props
      (overlay-put ov (pop props) (pop props)))
    (push ov sixel-graphics--overlays)
    ov))

(defun sixel-graphics--cleanup-overlay-files (ov)
  "Delete any temporary file owned by overlay OV."
  (when-let ((file (overlay-get ov 'sixel-graphics-delete-file)))
    (overlay-put ov 'sixel-graphics-delete-file nil)
    (setq sixel-graphics--temp-files (delete file sixel-graphics--temp-files))
    (ignore-errors
      (when (file-exists-p file)
        (delete-file file)))))

(defun sixel-graphics--temp-file-in-use-p (file)
  "Return non-nil when FILE is still referenced by a live overlay."
  (cl-some
   (lambda (buf)
     (with-current-buffer buf
       (cl-some
        (lambda (ov)
          (and (overlay-buffer ov)
               (equal (overlay-get ov 'sixel-graphics-delete-file) file)))
        sixel-graphics--overlays)))
   (buffer-list)))

(defun sixel-graphics--prune-temp-files ()
  "Delete oldest unreferenced temporary image files beyond the configured limit."
  (while (> (length sixel-graphics--temp-files)
            (max 0 sixel-graphics-temp-file-limit))
    (let ((victim (car (last sixel-graphics--temp-files))))
      (if (sixel-graphics--temp-file-in-use-p victim)
          (setq sixel-graphics--temp-files
                (append (butlast sixel-graphics--temp-files) (list victim)))
        (setq sixel-graphics--temp-files (butlast sixel-graphics--temp-files))
        (ignore-errors
          (when (file-exists-p victim)
            (delete-file victim)))))))

(defun sixel-graphics--register-temp-file (file)
  "Register FILE in the temporary image cache."
  (setq sixel-graphics--temp-files
        (cons file (delete file sixel-graphics--temp-files)))
  (sixel-graphics--prune-temp-files))

(defun sixel-graphics--ensure-temp-directory ()
  "Return the directory used for temporary SHR image files."
  (let ((dir (file-name-as-directory
              (expand-file-name sixel-graphics-temp-directory))))
    (unless (file-directory-p dir)
      (make-directory dir t))
    dir))

(defun sixel-graphics--clear-temp-files ()
  "Delete all registered temporary image files."
  (dolist (file sixel-graphics--temp-files)
    (ignore-errors
      (when (file-exists-p file)
        (delete-file file))))
  (setq sixel-graphics--temp-files nil))

(defun sixel-graphics--decode-file-url (url)
  "Return a local path for file URL string URL, or nil."
  (when (and (stringp url)
             (string-prefix-p "file:" url))
    (let* ((parsed (url-generic-parse-url url))
           (path (url-filename parsed)))
      (when (stringp path)
        (url-unhex-string path)))))

(defun sixel-graphics--resolve-shr-image-file (url)
  "Resolve SHR image URL or file name URL to a local readable path."
  (let* ((file-url-path (sixel-graphics--decode-file-url url))
         (expanded (and (stringp url)
                        (expand-file-name url default-directory))))
    (cond
     ((and (stringp url) (file-exists-p url)) url)
     ((and file-url-path (file-exists-p file-url-path)) file-url-path)
     ((and expanded (file-exists-p expanded)) expanded)
     (t nil))))

(defun sixel-graphics--content-type-extension (content-type)
  "Return a filename suffix for CONTENT-TYPE."
  (pcase content-type
    ((or 'image/jpeg "image/jpeg") ".jpg")
    ((or 'image/gif "image/gif") ".gif")
    ((or 'image/webp "image/webp") ".webp")
    ((or 'image/svg+xml "image/svg+xml") ".svg")
    ((or 'image/bmp "image/bmp") ".bmp")
    ((or 'image/tiff "image/tiff") ".tif")
    (_ ".png")))

(defun sixel-graphics--overlay-window (ov)
  "Return a visible window for OV's buffer, or nil."
  (when-let ((buf (overlay-buffer ov)))
    (get-buffer-window buf)))

(defun sixel-graphics--in-folded-region-p (pos)
  "Return non-nil if POS is inside a structurally folded region."
  (or (and (fboundp 'org-fold-folded-p)
           (condition-case nil
               (org-fold-folded-p pos)
             (error nil)))
      (let ((inv (get-char-property pos 'invisible)))
        (and inv (not (eq inv 'org-link))))))

(defun sixel-graphics--overlay-screen-pos (ov)
  "Return (ROW . COL) for OV, or nil when OV is not visible."
  (let* ((buf (overlay-buffer ov))
         (pos (overlay-start ov))
         (win (and buf (get-buffer-window buf))))
    (when (and win pos
               (pos-visible-in-window-p pos win)
               (not (sixel-graphics--in-folded-region-p pos)))
      (let* ((edges (window-edges win))
             (win-top (nth 1 edges))
             (win-left (nth 0 edges))
             (win-pos (posn-at-point pos win)))
        (when win-pos
          (let* ((col-row (posn-col-row win-pos))
                 (row (cdr col-row))
                 (posn-col (car col-row))
                 (body-left (nth 0 (window-body-edges win)))
                 (buf-col (with-current-buffer buf
                            (save-excursion
                              (goto-char pos)
                              (current-column))))
                 (col (if (> (- posn-col buf-col) (- body-left win-left))
                          (+ body-left buf-col)
                        (+ win-left posn-col))))
            (cons (+ win-top row 1)
                  (1+ col))))))))

(defun sixel-graphics--overlay-clear-placement (ov &optional window)
  "Clear OV's previously rendered region using WINDOW when available."
  (let ((row (overlay-get ov 'sixel-graphics-last-row))
        (col (overlay-get ov 'sixel-graphics-last-col))
        (cols (overlay-get ov 'sixel-graphics-last-cols))
        (rows (overlay-get ov 'sixel-graphics-last-rows)))
    (when (and row col cols rows)
      (sixel-graphics--clear-rect
       (or window (sixel-graphics--overlay-window ov) (selected-window))
       col row cols rows))
    (overlay-put ov 'sixel-graphics-last-row nil)
    (overlay-put ov 'sixel-graphics-last-col nil)
    (overlay-put ov 'sixel-graphics-last-cols nil)
    (overlay-put ov 'sixel-graphics-last-rows nil)))

(defun sixel-graphics--refresh-overlay (ov win-bottom)
  "Refresh overlay OV, constrained by WIN-BOTTOM."
  (let* ((entry (overlay-get ov 'sixel-graphics-entry))
         (cols (or (plist-get entry :cols)
                   (overlay-get ov 'sixel-graphics-cols)))
         (rows (or (plist-get entry :rows)
                   (overlay-get ov 'sixel-graphics-rows)))
         (pos (sixel-graphics--overlay-screen-pos ov))
         (window (or (sixel-graphics--overlay-window ov)
                     (selected-window)))
         (last-row (overlay-get ov 'sixel-graphics-last-row))
         (last-col (overlay-get ov 'sixel-graphics-last-col)))
    (if (and pos
             (<= (car pos) win-bottom)
             (<= (+ (car pos) rows -1) win-bottom))
        (let ((new-row (car pos))
              (new-col (cdr pos)))
          (unless (and (eql new-row last-row)
                       (eql new-col last-col))
            (when last-row
              (sixel-graphics--overlay-clear-placement ov window))
            (overlay-put ov 'sixel-graphics-last-row new-row)
            (overlay-put ov 'sixel-graphics-last-col new-col)
            (overlay-put ov 'sixel-graphics-last-cols cols)
            (overlay-put ov 'sixel-graphics-last-rows rows))
          (sixel-graphics--render-entry window entry new-col new-row))
      (when last-row
        (sixel-graphics--overlay-clear-placement ov window)))))

(defun sixel-graphics--refresh ()
  "Refresh all visible overlays."
  (when (and sixel-graphics-mode
             (not (display-graphic-p)))
    (sixel-graphics--sync-begin)
    (unwind-protect
        (walk-windows
         (lambda (win)
           (with-current-buffer (window-buffer win)
             (when sixel-graphics--overlays
               (setq sixel-graphics--overlays
                     (cl-delete-if-not #'overlay-buffer sixel-graphics--overlays))
               (let ((win-bottom (nth 3 (window-edges win))))
                 (dolist (ov sixel-graphics--overlays)
                   (sixel-graphics--refresh-overlay ov win-bottom))))))
         nil 'visible)
      (sixel-graphics--sync-end))))

(defun sixel-graphics--schedule-refresh ()
  "Schedule a Sixel refresh using leading-edge debounce."
  (if sixel-graphics--render-timer
      (setq sixel-graphics--refresh-pending t)
    (setq sixel-graphics--refresh-pending nil)
    (run-at-time 0 nil #'sixel-graphics--refresh)
    (setq sixel-graphics--render-timer
          (run-at-time
           sixel-graphics-render-delay nil
           (lambda ()
             (setq sixel-graphics--render-timer nil)
             (when sixel-graphics--refresh-pending
               (setq sixel-graphics--refresh-pending nil)
               (sixel-graphics--refresh)))))))

(defun sixel-graphics--on-window-scroll (win _new-start)
  "Handle window scroll for WIN."
  (when (buffer-local-value 'sixel-graphics--overlays (window-buffer win))
    (sixel-graphics--schedule-refresh)))

(defun sixel-graphics--on-buffer-change (_frame-or-window)
  "Handle visible buffer changes."
  (let ((visible-bufs nil))
    (walk-windows (lambda (w) (push (window-buffer w) visible-bufs))
                  nil 'visible)
    (dolist (buf (buffer-list))
      (with-current-buffer buf
        (when sixel-graphics--overlays
          (if (memq buf visible-bufs)
              (dolist (ov sixel-graphics--overlays)
                (when (overlay-buffer ov)
                  (sixel-graphics--overlay-clear-placement ov (selected-window))))
            (dolist (ov sixel-graphics--overlays)
              (when (overlay-buffer ov)
                (sixel-graphics--overlay-clear-placement ov (selected-window))))))))
    (when sixel-graphics--render-timer
      (cancel-timer sixel-graphics--render-timer))
    (setq sixel-graphics--refresh-pending nil
          sixel-graphics--render-timer
          (run-at-time 0.1 nil
                       (lambda ()
                         (setq sixel-graphics--render-timer nil)
                         (sixel-graphics--refresh))))))

(defun sixel-graphics--on-window-change (_frame)
  "Handle window configuration changes."
  (setq sixel-graphics--probe-result nil)
  (dolist (buf (buffer-list))
    (with-current-buffer buf
      (dolist (ov sixel-graphics--overlays)
        (when (overlay-buffer ov)
          (sixel-graphics--overlay-clear-placement ov (selected-window))))))
  (when sixel-graphics--render-timer
    (cancel-timer sixel-graphics--render-timer))
  (setq sixel-graphics--refresh-pending nil
        sixel-graphics--render-timer
        (run-at-time 0.1 nil
                     (lambda ()
                       (setq sixel-graphics--render-timer nil)
                       (sixel-graphics--refresh)))))

(defun sixel-graphics--on-redisplay ()
  "Post-command hook to schedule refresh."
  (sixel-graphics--schedule-refresh))

(defun sixel-graphics--remove-overlay (ov)
  "Remove overlay OV and clear its previously rendered region."
  (when-let ((buf (overlay-buffer ov)))
    (with-current-buffer buf
      (sixel-graphics--overlay-clear-placement ov)
      (sixel-graphics--cleanup-overlay-files ov)
      (delete-overlay ov)
      (setq sixel-graphics--overlays (delq ov sixel-graphics--overlays)))))

;;;###autoload
(defun sixel-graphics-remove-images (&optional beg end)
  "Remove all `sixel-graphics' overlays in region BEG..END."
  (interactive)
  (dolist (ov (overlays-in (or beg (point-min)) (or end (point-max))))
    (when (overlay-get ov 'sixel-graphics)
      (sixel-graphics--remove-overlay ov))))

;;;###autoload
(defun sixel-graphics-clear-all ()
  "Remove all Sixel overlays from all buffers and clear the payload cache."
  (interactive)
  (dolist (buf (buffer-list))
    (with-current-buffer buf
      (when sixel-graphics--overlays
        (sixel-graphics-remove-images))))
  (sixel-graphics--clear-cache)
  (sixel-graphics--clear-temp-files))

;;;###autoload
(defun sixel-graphics-image (file &optional beg end max-cols max-rows)
  "Display image FILE in the current buffer from BEG to END."
  (interactive "fImage file: ")
  (unless (sixel-graphics--supported-p)
    (user-error "Terminal does not support Sixel graphics"))
  (let* ((max-c (or max-cols sixel-graphics-max-width))
         (max-r (or max-rows sixel-graphics-max-height))
         (abs-file (expand-file-name file))
         (entry (sixel-graphics--prepare-entry abs-file max-c max-r))
         (start (or beg (point)))
         (stop (or end (point))))
    (let ((ov (sixel-graphics--make-overlay
               start stop entry
               (list 'sixel-graphics-file abs-file
                     'sixel-graphics-max-cols max-c
                     'sixel-graphics-max-rows max-r
                     'sixel-graphics-scale 1.0))))
      (sixel-graphics--schedule-refresh)
      ov)))

(defun sixel-graphics--display-image-centered (file max-cols max-rows
                                                   &optional win-cols win-rows scale)
  "Display FILE centered in the current buffer."
  (let* ((entry (sixel-graphics--prepare-entry file max-cols max-rows scale))
         (img-cols (plist-get entry :cols))
         (img-rows (plist-get entry :rows))
         (wc (or win-cols max-cols))
         (wr (or win-rows max-rows))
         (h-pad (max 0 (/ (- wc img-cols) 2)))
         (v-pad (max 0 (/ (- wr img-rows) 2))))
    (dotimes (_ v-pad)
      (insert "\n"))
    (insert (make-string h-pad ?\s))
    (let ((img-start (point)))
      (insert "\n")
      (let ((ov (sixel-graphics--make-overlay
                 img-start (point) entry
                 (list 'sixel-graphics-file (expand-file-name file)
                       'sixel-graphics-max-cols max-cols
                       'sixel-graphics-max-rows max-rows
                       'sixel-graphics-scale (or scale 1.0)))))
        (sixel-graphics--schedule-refresh)
        ov))))

(defun sixel-graphics--on-org-cycle (&rest _args)
  "Handle org visibility changes."
  (when (and sixel-graphics-mode sixel-graphics--overlays)
    (dolist (ov sixel-graphics--overlays)
      (when (overlay-buffer ov)
        (sixel-graphics--overlay-clear-placement ov (selected-window))))
    (sixel-graphics--schedule-refresh)))

(defun sixel-graphics--org-display-inline-images-tty (&optional _include-linked beg end)
  "Display inline org images in the current buffer."
  (when (derived-mode-p 'org-mode)
    (let ((start (or beg (point-min)))
          (stop (or end (point-max))))
      (save-restriction
        (widen)
        (save-excursion
          (goto-char start)
          (while (re-search-forward "\\[\\[\\(file:\\|attachment:\\|[./~]\\)"
                                    stop t)
            (let* ((context (org-element-context))
                   (type (org-element-type context)))
              (when (eq type 'link)
                (let* ((link-beg (org-element-property :begin context))
                       (link-end (org-element-property :end context))
                       (path (org-element-property :path context))
                       (link-type (org-element-property :type context))
                       (file (cond
                              ((string= link-type "file") path)
                              ((string= link-type "attachment")
                               (ignore-errors
                                 (require 'org-attach)
                                 (when-let ((dir (org-attach-dir)))
                                   (expand-file-name path dir))))
                              (t path))))
                  (when (and file
                             (file-exists-p (expand-file-name file))
                             (sixel-graphics--image-file-p file)
                             (not (cl-some
                                   (lambda (ov) (overlay-get ov 'sixel-graphics))
                                   (overlays-in link-beg link-end))))
                    (condition-case err
                        (sixel-graphics-image
                         (expand-file-name file)
                         link-beg link-end
                         sixel-graphics-max-width
                         sixel-graphics-max-height)
                      (error
                       (message "sixel-graphics: %s: %s"
                                file
                                (error-message-string err))))))))))))))

(defun sixel-graphics--org-display-advice (orig-fn &rest args)
  "Around advice for `org-display-inline-images'."
  (if (and sixel-graphics-mode (not (display-graphic-p)))
      (apply #'sixel-graphics--org-display-inline-images-tty args)
    (apply orig-fn args)))

(defun sixel-graphics--org-remove-advice (orig-fn &rest args)
  "Around advice for `org-remove-inline-images'."
  (when (and sixel-graphics-mode (not (display-graphic-p)))
    (sixel-graphics-remove-images))
  (apply orig-fn args))

(defun sixel-graphics--org-toggle-advice (orig-fn &rest args)
  "Around advice for `org-toggle-inline-images'."
  (if (and sixel-graphics-mode (not (display-graphic-p)))
      (if (cl-some (lambda (ov) (overlay-get ov 'sixel-graphics))
                   (overlays-in (point-min) (point-max)))
          (sixel-graphics-remove-images)
        (sixel-graphics--org-display-inline-images-tty))
    (apply orig-fn args)))

(defun sixel-graphics--org-link-preview-advice (orig-fn &optional arg beg end)
  "Around advice for `org-link-preview'."
  (if (and sixel-graphics-mode (not (display-graphic-p)))
      (cond
       ((equal arg '(4))
        (sixel-graphics-remove-images beg end))
       ((equal arg '(64))
        (sixel-graphics-remove-images))
       (t
        (sixel-graphics--org-display-inline-images-tty nil beg end)))
    (funcall orig-fn arg beg end)))

(defun sixel-graphics--org-link-preview-region-advice
    (orig-fn &optional include-linked refresh beg end)
  "Around advice for `org-link-preview-region'."
  (if (and sixel-graphics-mode (not (display-graphic-p)))
      (sixel-graphics--org-display-inline-images-tty include-linked beg end)
    (funcall orig-fn include-linked refresh beg end)))

(defun sixel-graphics--org-latex-preview-advice (orig-fn &optional arg beg end)
  "Around advice for `org-latex-preview'."
  (if (and sixel-graphics-mode (not (display-graphic-p)))
      (cond
       ((equal arg '(4))
        (sixel-graphics--org-clear-latex-preview beg end))
       ((equal arg '(16))
        (sixel-graphics--org-clear-latex-preview))
       (t
        (let ((start (or beg (if (use-region-p) (region-beginning) (point-min))))
              (stop (or end (if (use-region-p) (region-end) (point-max)))))
          (let ((org-format-latex-options
                 (org-combine-plists
                  org-format-latex-options
                  (list :foreground
                        (let ((fg (face-attribute 'default :foreground nil)))
                          (if (and (stringp fg)
                                   (not (string-prefix-p "unspecified" fg)))
                              fg
                            "Black"))
                        :background "Transparent"))))
            (cl-letf (((symbol-function 'clear-image-cache) #'ignore))
              (org--latex-preview-region start stop))))))
    (funcall orig-fn arg beg end)))

(defun sixel-graphics--org-make-preview-overlay-advice (orig-fn beg end movefile imagetype)
  "Around advice for `org--make-preview-overlay'."
  (if (and sixel-graphics-mode (not (display-graphic-p)))
      (when (and movefile (file-exists-p movefile))
        (unless (cl-some (lambda (ov) (overlay-get ov 'sixel-graphics))
                         (overlays-in beg end))
          (when-let ((ov (sixel-graphics-image movefile beg end)))
            (overlay-put ov 'org-overlay-type 'org-latex-overlay)
            (overlay-put ov 'modification-hooks
                         (list (lambda (o after &rest _)
                                 (when after
                                   (sixel-graphics--remove-overlay o)))))
            ov)))
    (funcall orig-fn beg end movefile imagetype)))

(defun sixel-graphics--org-clear-latex-preview (&optional beg end)
  "Remove Sixel LaTeX preview overlays in region BEG..END."
  (let ((start (or beg (point-min)))
        (stop (or end (point-max))))
    (dolist (ov (overlays-in start stop))
      (when (and (overlay-get ov 'sixel-graphics)
                 (eq (overlay-get ov 'org-overlay-type) 'org-latex-overlay))
        (sixel-graphics--remove-overlay ov)))))

(defun sixel-graphics--image-mode-render ()
  "Render the current file centered in Sixel image mode."
  (when-let ((file (buffer-file-name)))
    (when (sixel-graphics--image-file-p file)
      (let ((inhibit-read-only t)
            (win-w (max 1 (- (window-body-width) 2)))
            (win-h (max 1 (- (window-body-height) 2))))
        (dolist (ov (overlays-in (point-min) (point-max)))
          (when (overlay-get ov 'sixel-graphics)
            (sixel-graphics--remove-overlay ov)))
        (erase-buffer)
        (sixel-graphics--display-image-centered
         file
         (min win-w sixel-graphics-max-width)
         (min win-h sixel-graphics-max-height)
         win-w win-h sixel-graphics--image-scale)
        (goto-char (point-min))
        (set-buffer-modified-p nil)))))

(defun sixel-graphics-image-increase-size ()
  "Zoom in on the image in Sixel image mode."
  (interactive)
  (setq sixel-graphics--image-scale (* sixel-graphics--image-scale 1.25))
  (sixel-graphics--image-mode-render))

(defun sixel-graphics-image-decrease-size ()
  "Zoom out on the image in Sixel image mode."
  (interactive)
  (setq sixel-graphics--image-scale (max 0.1 (* sixel-graphics--image-scale 0.8)))
  (sixel-graphics--image-mode-render))

(defun sixel-graphics-image-reset-size ()
  "Reset image zoom in Sixel image mode."
  (interactive)
  (setq sixel-graphics--image-scale 1.0)
  (sixel-graphics--image-mode-render))

(defun sixel-graphics--image-mode-advice (orig-fn &rest args)
  "Around advice for `image-mode'."
  (if (and sixel-graphics-mode (not (display-graphic-p)))
      (progn
        (major-mode-suspend)
        (setq major-mode 'sixel-graphics-image-mode
              mode-name "Image[Sixel]")
        (let ((map (make-sparse-keymap)))
          (set-keymap-parent map special-mode-map)
          (define-key map (kbd "q") #'kill-current-buffer)
          (define-key map (kbd "+") #'sixel-graphics-image-increase-size)
          (define-key map (kbd "=") #'sixel-graphics-image-increase-size)
          (define-key map (kbd "-") #'sixel-graphics-image-decrease-size)
          (define-key map (kbd "0") #'sixel-graphics-image-reset-size)
          (use-local-map map))
        (when (fboundp 'evil-local-set-key)
          (evil-local-set-key 'normal (kbd "+") #'sixel-graphics-image-increase-size)
          (evil-local-set-key 'normal (kbd "=") #'sixel-graphics-image-increase-size)
          (evil-local-set-key 'normal (kbd "-") #'sixel-graphics-image-decrease-size)
          (evil-local-set-key 'normal (kbd "0") #'sixel-graphics-image-reset-size)
          (evil-local-set-key 'normal (kbd "q") #'kill-current-buffer))
        (setq-local buffer-read-only t)
        (add-hook 'window-size-change-functions
                  (lambda (_frame)
                    (when (eq major-mode 'sixel-graphics-image-mode)
                      (sixel-graphics--image-mode-render)))
                  nil t)
        (sixel-graphics--image-mode-render)
        (set-buffer-modified-p nil))
    (apply orig-fn args)))

(defun sixel-graphics--shr-put-image-advice (orig-fn spec alt &rest args)
  "Around advice for `shr-put-image'."
  (if (and sixel-graphics-mode (not (display-graphic-p)))
      (let* ((start (point))
             (flags (car args))
             (data (if (consp spec) (car spec) spec))
             (content-type (and (consp spec) (cadr spec)))
             (size (cdr (assq 'size flags)))
             (suffix (sixel-graphics--content-type-extension content-type))
             (file nil))
        (setq alt (string-trim (or alt "")))
        (when (length= alt 0)
          (setq alt "*"))
        (insert alt)
        (let ((end (point)))
          (when (and (stringp data)
                     (> (length data) 0))
            (setq file (make-temp-file
                        (expand-file-name "sixel-shr-"
                                          (sixel-graphics--ensure-temp-directory))
                        nil suffix))
            (with-temp-file file
              (set-buffer-multibyte nil)
              (insert data))
            (sixel-graphics--register-temp-file file)
            (sixel-graphics--log
             "shr image content-type=%S bytes=%s size=%S"
             content-type (length data) size)
            (condition-case err
                (let ((ov (sixel-graphics-image file start end)))
                  (when ov
                    (overlay-put ov 'sixel-graphics-delete-file file)))
              (error
               (sixel-graphics--log "shr image failed: %S" err)
               (setq sixel-graphics--temp-files
                     (delete file sixel-graphics--temp-files))
               (ignore-errors
                 (when (file-exists-p file)
                   (delete-file file))))))))
    (apply orig-fn spec alt args)))

(defun sixel-graphics--doc-view-mode-p-advice (orig-fn type)
  "Around advice for `doc-view-mode-p'."
  (if (and sixel-graphics-mode (not (display-graphic-p)))
      (cl-letf (((symbol-function 'display-graphic-p) (lambda (&rest _) t)))
        (funcall orig-fn type))
    (funcall orig-fn type)))

(defun sixel-graphics--doc-view-render-current ()
  "Render the current doc-view page via Sixel."
  (when (and sixel-graphics--doc-view-current-file
             (file-exists-p sixel-graphics--doc-view-current-file))
    (when sixel-graphics--doc-view-overlay
      (sixel-graphics--remove-overlay sixel-graphics--doc-view-overlay)
      (setq sixel-graphics--doc-view-overlay nil))
    (let ((inhibit-read-only t)
          (win-w (max 1 (- (window-body-width) 1)))
          (win-h (max 1 (- (window-body-height) 1))))
      (erase-buffer)
      (setq sixel-graphics--doc-view-overlay
            (sixel-graphics--display-image-centered
             sixel-graphics--doc-view-current-file
             win-w win-h win-w win-h sixel-graphics--doc-view-scale))
      (goto-char (point-min)))))

(defun sixel-graphics--doc-view-insert-image-advice (orig-fn file &rest args)
  "Around advice for `doc-view-insert-image'."
  (if (and sixel-graphics-mode (not (display-graphic-p)))
      (when (and file (file-exists-p file))
        (setq sixel-graphics--doc-view-current-file file)
        (sixel-graphics--doc-view-render-current))
    (apply orig-fn file args)))

(defun sixel-graphics--doc-view-enlarge-advice (orig-fn factor)
  "Around advice for `doc-view-enlarge'."
  (if (and sixel-graphics-mode (not (display-graphic-p)))
      (when sixel-graphics--doc-view-current-file
        (setq sixel-graphics--doc-view-scale (* sixel-graphics--doc-view-scale factor))
        (sixel-graphics--doc-view-render-current))
    (funcall orig-fn factor)))

(defun sixel-graphics--doc-view-scale-reset-advice (orig-fn &rest args)
  "Around advice for `doc-view-scale-reset'."
  (if (and sixel-graphics-mode (not (display-graphic-p)))
      (when sixel-graphics--doc-view-current-file
        (setq sixel-graphics--doc-view-scale 1.0)
        (sixel-graphics--doc-view-render-current))
    (apply orig-fn args)))

;;;###autoload
(defun sixel-graphics-dired-preview ()
  "Preview the image at point in dired."
  (interactive)
  (unless (derived-mode-p 'dired-mode)
    (user-error "Not in a dired buffer"))
  (let ((file (dired-get-file-for-visit)))
    (unless (sixel-graphics--image-file-p file)
      (user-error "Not an image file"))
    (let* ((buf-name (format "*sixel-preview: %s*" (file-name-nondirectory file)))
           (buf (get-buffer-create buf-name))
           (win (display-buffer-in-side-window
                 buf '((side . right) (window-width . 0.5)))))
      (with-current-buffer buf
        (let ((inhibit-read-only t))
          (erase-buffer)
          (insert (format " %s\n\n" (file-name-nondirectory file))))
        (setq-local buffer-read-only t)
        (let ((map (make-sparse-keymap)))
          (define-key map (kbd "q")
            (lambda ()
              (interactive)
              (let ((preview-win (get-buffer-window (current-buffer))))
                (sixel-graphics-remove-images)
                (kill-buffer (current-buffer))
                (when (window-live-p preview-win)
                  (delete-window preview-win)))))
          (use-local-map map))
        (sixel-graphics-image
         file (point-min) (point-max)
         (min (- (window-width win) 2) sixel-graphics-max-width)
         (min (- (window-height win) 3) sixel-graphics-max-height))
        (goto-char (point-min))))))

(defun sixel-graphics--dirvish-preview (file _ext preview-window _dv)
  "Dirvish preview dispatcher for FILE in PREVIEW-WINDOW."
  (when (and sixel-graphics-mode
             (not (display-graphic-p))
             (sixel-graphics--supported-p))
    (let* ((buf-name (format " *sixel-dirvish: %s*" (file-name-nondirectory file)))
           (buf (get-buffer-create buf-name))
           (max-cols (min (- (window-width preview-window) 2)
                          sixel-graphics-max-width))
           (max-rows (min (- (window-height preview-window) 3)
                          sixel-graphics-max-height)))
      (with-current-buffer buf
        (let ((inhibit-read-only t))
          (sixel-graphics-remove-images)
          (erase-buffer)
          (insert (format "\n %s\n\n" (file-name-nondirectory file))))
        (setq-local buffer-read-only t)
        (sixel-graphics-image file (point-min) (point-max) max-cols max-rows)
        (goto-char (point-min)))
      `(buffer . ,buf))))

(defun sixel-graphics--install-dirvish ()
  "Install the dirvish preview dispatcher."
  (with-eval-after-load 'dirvish
    (unless (assq 'sixel-image dirvish--available-preview-dispatchers)
      (push (cons 'sixel-image
                  (list :doc "Preview images using Sixel graphics"
                        :require nil))
            dirvish--available-preview-dispatchers))
    (defalias 'dirvish-sixel-image-dp
      (lambda (file ext preview-window dv)
        (when (and (boundp 'dirvish-image-exts)
                   (member ext dirvish-image-exts))
          (sixel-graphics--dirvish-preview file ext preview-window dv))))
    (unless (memq 'sixel-image dirvish-preview-dispatchers)
      (setq dirvish-preview-dispatchers
            (cons 'sixel-image dirvish-preview-dispatchers)))))

(defun sixel-graphics--uninstall-dirvish ()
  "Remove the dirvish preview dispatcher."
  (when (boundp 'dirvish-preview-dispatchers)
    (setq dirvish-preview-dispatchers
          (delq 'sixel-image dirvish-preview-dispatchers)))
  (when (boundp 'dirvish--available-preview-dispatchers)
    (setq dirvish--available-preview-dispatchers
          (assq-delete-all 'sixel-image dirvish--available-preview-dispatchers)))
  (when (fboundp 'dirvish-sixel-image-dp)
    (fmakunbound 'dirvish-sixel-image-dp)))

(defun sixel-graphics--markdown-overlays-fontify-image-advice
    (orig-fn start end url-start url-end)
  "Around advice for `markdown-overlays--fontify-image'."
  (if (and sixel-graphics-mode (not (display-graphic-p)))
      (when-let* ((url (buffer-substring-no-properties url-start url-end))
                  (path (markdown-overlays--resolve-image-url url))
                  ((file-exists-p path))
                  ((sixel-graphics--image-file-p path)))
        (condition-case nil
            (sixel-graphics-image path start end
                                 sixel-graphics-max-width
                                 sixel-graphics-max-height)
          (error nil)))
    (funcall orig-fn start end url-start url-end)))

(defun sixel-graphics--markdown-overlays-fontify-image-file-path-advice
    (orig-fn start end path-start path-end)
  "Around advice for `markdown-overlays--fontify-image-file-path'."
  (if (and sixel-graphics-mode (not (display-graphic-p)))
      (when-let* ((raw (buffer-substring-no-properties path-start path-end))
                  (path (markdown-overlays--resolve-image-url raw))
                  ((file-exists-p path))
                  ((sixel-graphics--image-file-p path)))
        (condition-case nil
            (sixel-graphics-image path start end
                                 sixel-graphics-max-width
                                 sixel-graphics-max-height)
          (error nil)))
    (funcall orig-fn start end path-start path-end)))

(defun sixel-graphics--kill-buffer-hook ()
  "Clean up Sixel overlays when the current buffer is killed."
  (when sixel-graphics--overlays
    (dolist (ov sixel-graphics--overlays)
      (when (overlay-buffer ov)
        (sixel-graphics--overlay-clear-placement ov (selected-window))))
    (setq sixel-graphics--overlays nil)))

(defun sixel-graphics--install-hooks ()
  "Install refresh hooks."
  (add-hook 'window-scroll-functions #'sixel-graphics--on-window-scroll)
  (add-hook 'window-size-change-functions #'sixel-graphics--on-window-change)
  (add-hook 'window-buffer-change-functions #'sixel-graphics--on-buffer-change)
  (add-hook 'post-command-hook #'sixel-graphics--on-redisplay)
  (add-hook 'kill-buffer-hook #'sixel-graphics--kill-buffer-hook))

(defun sixel-graphics--uninstall-hooks ()
  "Remove refresh hooks."
  (remove-hook 'window-scroll-functions #'sixel-graphics--on-window-scroll)
  (remove-hook 'window-size-change-functions #'sixel-graphics--on-window-change)
  (remove-hook 'window-buffer-change-functions #'sixel-graphics--on-buffer-change)
  (remove-hook 'post-command-hook #'sixel-graphics--on-redisplay)
  (remove-hook 'kill-buffer-hook #'sixel-graphics--kill-buffer-hook))

(defun sixel-graphics--install-integrations ()
  "Install advice on org, image-mode, shr, doc-view and others."
  (with-eval-after-load 'org
    (advice-add 'org-display-inline-images :around #'sixel-graphics--org-display-advice)
    (advice-add 'org-remove-inline-images :around #'sixel-graphics--org-remove-advice)
    (advice-add 'org-toggle-inline-images :around #'sixel-graphics--org-toggle-advice)
    (when (fboundp 'org-link-preview)
      (advice-add 'org-link-preview :around #'sixel-graphics--org-link-preview-advice))
    (when (fboundp 'org-link-preview-region)
      (advice-add 'org-link-preview-region
                  :around
                  #'sixel-graphics--org-link-preview-region-advice))
    (add-hook 'org-cycle-hook #'sixel-graphics--on-org-cycle)
    (advice-add 'org-latex-preview :around #'sixel-graphics--org-latex-preview-advice)
    (advice-add 'org--make-preview-overlay
                :around
                #'sixel-graphics--org-make-preview-overlay-advice))
  (with-eval-after-load 'image-mode
    (advice-add 'image-mode :around #'sixel-graphics--image-mode-advice))
  (with-eval-after-load 'shr
    (advice-add 'shr-put-image :around #'sixel-graphics--shr-put-image-advice))
  (with-eval-after-load 'doc-view
    (advice-add 'doc-view-mode-p :around #'sixel-graphics--doc-view-mode-p-advice)
    (advice-add 'doc-view-insert-image
                :around
                #'sixel-graphics--doc-view-insert-image-advice)
    (advice-add 'doc-view-enlarge :around #'sixel-graphics--doc-view-enlarge-advice)
    (advice-add 'doc-view-scale-reset
                :around
                #'sixel-graphics--doc-view-scale-reset-advice))
  (with-eval-after-load 'markdown-overlays
    (advice-add 'markdown-overlays--fontify-image
                :around
                #'sixel-graphics--markdown-overlays-fontify-image-advice)
    (advice-add 'markdown-overlays--fontify-image-file-path
                :around
                #'sixel-graphics--markdown-overlays-fontify-image-file-path-advice))
  (sixel-graphics--install-dirvish))

(defun sixel-graphics--uninstall-integrations ()
  "Remove installed advice."
  (advice-remove 'org-display-inline-images #'sixel-graphics--org-display-advice)
  (advice-remove 'org-remove-inline-images #'sixel-graphics--org-remove-advice)
  (advice-remove 'org-toggle-inline-images #'sixel-graphics--org-toggle-advice)
  (when (fboundp 'org-link-preview)
    (advice-remove 'org-link-preview #'sixel-graphics--org-link-preview-advice))
  (when (fboundp 'org-link-preview-region)
    (advice-remove 'org-link-preview-region
                   #'sixel-graphics--org-link-preview-region-advice))
  (remove-hook 'org-cycle-hook #'sixel-graphics--on-org-cycle)
  (advice-remove 'org-latex-preview #'sixel-graphics--org-latex-preview-advice)
  (advice-remove 'org--make-preview-overlay
                 #'sixel-graphics--org-make-preview-overlay-advice)
  (advice-remove 'image-mode #'sixel-graphics--image-mode-advice)
  (advice-remove 'shr-put-image #'sixel-graphics--shr-put-image-advice)
  (advice-remove 'doc-view-mode-p #'sixel-graphics--doc-view-mode-p-advice)
  (advice-remove 'doc-view-insert-image
                 #'sixel-graphics--doc-view-insert-image-advice)
  (advice-remove 'doc-view-enlarge #'sixel-graphics--doc-view-enlarge-advice)
  (advice-remove 'doc-view-scale-reset
                 #'sixel-graphics--doc-view-scale-reset-advice)
  (advice-remove 'markdown-overlays--fontify-image
                 #'sixel-graphics--markdown-overlays-fontify-image-advice)
  (advice-remove 'markdown-overlays--fontify-image-file-path
                 #'sixel-graphics--markdown-overlays-fontify-image-file-path-advice)
  (sixel-graphics--uninstall-dirvish))

;;;###autoload
(define-minor-mode sixel-graphics-mode
  "Display images in terminal Emacs via Sixel graphics."
  :global t
  :lighter " Sixel"
  :group 'sixel-graphics
  (if sixel-graphics-mode
      (if (sixel-graphics--supported-p)
          (progn
            (sixel-graphics--install-hooks)
            (sixel-graphics--install-integrations)
            (message "Sixel display mode enabled"))
        (setq sixel-graphics-mode nil)
        (message "sixel-graphics: terminal not supported"))
    (sixel-graphics--uninstall-hooks)
    (sixel-graphics--uninstall-integrations)
    (sixel-graphics-clear-all)
    (when sixel-graphics--render-timer
      (cancel-timer sixel-graphics--render-timer))
    (setq sixel-graphics--render-timer nil
          sixel-graphics--refresh-pending nil)))

(provide 'sixel-graphics)

;;; sixel-graphics.el ends here
