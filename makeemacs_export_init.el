;; this modified org-mode ob-coq and coq-inferior.el code is
;; from http://alan.petitepomme.net/tips/executing_coq.html
;; ERRATA
;; (defun org-babel-execute:coq (body param)
;;  (let ((full-body (org-babel-expand-body:generic body params))
;; to
;; (defun org-babel-execute:coq (body param)
;;   (let ((full-body (org-babel-expand-body:generic body param))


(require 'package)
(add-to-list 'load-path (expand-file-name "~/.emacs.d/elpa"))
;; for package htmlize
;; (add-to-list 'package-archives '("melpa" . "http://melpa.org/packages/") t)
(package-initialize)

;; ;; Load company-coq when opening Coq files
;;(add-hook 'coq-mode-hook #'company-coq-mode)

;; Open .v files with Proof-General's coq-mode
;;(require 'proof-site)
;; Open .v files with Proof General's Coq mode
(load (expand-file-name "~/.emacs.d/lisp/PG/generic/proof-site"))

(require 'org)
(require 'ob)
;;(require 'ob-coq)
(require 'ox)
(require 'ox-html)
(require 'ox-org)

(setq org-confirm-babel-evaluate nil)
(setq org-babel-tangle-lang-exts
      (cons '("coq" . "v")
	    (assq-delete-all "coq" org-babel-tangle-lang-exts)))
(setq org-babel-default-header-args
      (cons '(:tangle . "yes")
	    (assq-delete-all :tangle org-babel-default-header-args)))

(setq org-html-head-include-default-style nil)
(setq org-html-head "<link rel=\"stylesheet\" type=\"text/css\" href=\"./code/style.css\"/>")
(setq org-html-postamble nil)
(setq org-export-time-stamp-file nil
      org-html-footnotes-section 
"<div id=\"footnotes\">
<div class=\"footnotes\"><!--%s--></div>
<div id=\"text-footnotes\">%s</div></div>" )

(require 'comint)

(defvar coq-program-name "coqtop")

(defvar coq-buffer)

(define-derived-mode inferior-coq-mode comint-mode "Run Coq"
  ""
  (setq comint-prompt-regexp "^[^<]* < *"))

(defun coq-args-to-list (string)
  (let ((where (string-match "[ \t]" string)))
    (cond ((null where) (list string))
    ((not (= where 0))
     (cons (substring string 0 where)
     (coq-args-to-list (substring string (+ 1 where)
             (length string)))))
    (t (let ((pos (string-match "[^ \t]" string)))
         (if (null pos)
       nil
     (coq-args-to-list (substring string pos
             (length string)))))))))

(defun run-coq (cmd)
  (interactive (list (if current-prefix-arg
       (read-string "Run Coq: " coq-program-name)
       coq-program-name)))
  (if (not (comint-check-proc "*coq*"))
      (let ((cmdlist (coq-args-to-list cmd)))
  (set-buffer (apply 'make-comint "coq" (car cmdlist)
         nil (cdr cmdlist)))
  (inferior-coq-mode)))
  (setq coq-program-name cmd)
  (setq coq-buffer "*coq*")
  (switch-to-buffer "*coq*"))

(defun coq-proc ()
  "Return the current coq process.  See variable `coq-buffer'."
  (let ((proc (get-buffer-process (if (eq major-mode 'inferior-coq-mode)
              (current-buffer)
              coq-buffer))))
    (or proc
  (error "No current process.  See variable `coq-buffer'"))))

(org-babel-do-load-languages
 'org-babel-load-languages
 '((coq . t)))

;; I need to redefine these function, as they have some issues.

;;(defun org-babel-coq-split-phrases (body)
;;  (split-string body "\\.[ \t\n\r]+"))

;;(defun org-babel-coq-split-phrases (body)
;;  (split-string (replace-regexp-in-string "(\\*\\(.\\|[ \t\n\r]\\)+\\*)" "" body) "\\.[ \t\n\r]+"))

(defun org-babel-coq-split-phrases (body)
  ;; comments up to depth 3
  (unless (eq (string-match-p "(\\*\\(\\((\\*\\(\\((\\*\\(\\w\\|\\W\\)*?\\*)\\)\\|\\w\\|\\W\\)*?\\*)\\)\\|\\w\\|\\W\\)*?\\*)" body) nil)
    (setq body (replace-regexp-in-string "(\\*\\(\\((\\*\\(\\((\\*\\(\\w\\|\\W\\)*?\\*)\\)\\|\\w\\|\\W\\)*?\\*)\\)\\|\\w\\|\\W\\)*?\\*)" "" body)))
  (split-string body "\\.[ \t\n\r]+"))
  
(defun org-babel-coq-run-one-phrase (phrase session)
  (let ((pt (lambda ()
        (marker-position
         (process-mark (get-buffer-process (current-buffer)))))))
    (org-babel-coq-clean-prompt
     (org-babel-comint-in-buffer session
       (let ((start (funcall pt)))
   (with-temp-buffer
     (insert phrase)
     (comint-send-region (coq-proc) (point-min) (point-max))
     (comint-send-string (coq-proc)
      (if (string= (buffer-substring (- (point-max) 1) (point-max)) ".")
    "\n"
        ".\n")))
   (while (equal start (funcall pt)) (sleep-for 0.1))
   (buffer-substring start (funcall pt)))))))

(defun org-babel-execute:coq (body param)
  (let ((full-body (org-babel-expand-body:generic body param))
        (session (org-babel-coq-initiate-session)))
    (let ((phrases (org-babel-coq-split-phrases full-body))
          results)
      (while phrases
        (unless (string-match "^\s*\\'" (car phrases))
          (setq results
                (cons (org-babel-coq-run-one-phrase (car phrases) session) results)))
        (setq phrases (cdr phrases)))
      (apply #'concat (reverse results)))))

(defun org-babel-coq-initiate-session ()
  "Initiate a coq session.
If there is not a current inferior-process-buffer in SESSION then
create one.  Return the initialized session."
  (unless (fboundp 'run-coq)
    (error "`run-coq' not defined, load coq-inferior.el"))
  (save-window-excursion (run-coq coq-program-name))
  (sit-for 0.1)
  (get-buffer org-babel-coq-buffer))

(setq coq-program-name (concat "coqtop -R " (expand-file-name ".") " OOO1337777"))
