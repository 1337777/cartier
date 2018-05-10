(require 'package)
(add-to-list 'load-path (expand-file-name "~/.emacs.d/elpa"))
;; for package htmlize
;; (add-to-list 'package-archives '("melpa" . "http://melpa.org/packages/") t)
(package-initialize)

(require 'org)
(require 'ob)
;;(require 'ob-coq)
(require 'ox)
(require 'ox-html)
(require 'ox-org)

;;;;;;;;;;;;;;;;;change export;;;;;;;;;;;;;;;;;;;
(load (expand-file-name "./makeemacs_export_init.el"))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;(show-paren-mode 1)
;;(menu-bar-mode 0)
(setq make-backup-files nil
      vc-handled-backends nil)

(setq org-export-default-language "en"
      org-export-html-extension "html"
      org-html-postamble nil
      org-export-with-timestamps t
      org-export-time-stamp-file nil
      org-export-with-section-numbers t
      org-export-with-tags 'not-in-toc
      org-export-skip-text-before-1st-heading nil
      org-export-with-sub-superscripts '{}
      org-export-with-LaTeX-fragments t
      org-export-with-archived-trees nil
      org-export-highlight-first-table-line t
      org-export-latex-listings-w-names nil
      org-html-head-include-default-style nil
      org-html-head "<link rel=\"stylesheet\" type=\"text/css\" href=\"./code/style.css\"/>"
      org-export-htmlize-output-type 'css
      org-startup-folded nil
      org-export-allow-BIND t
      org-publish-list-skipped-files t
      org-publish-use-timestamps-flag t
      org-confirm-babel-evaluate nil)


(eval-after-load "org-html"
'(setq org-html-scripts
       (concat org-html-scripts "\n"
	       "<script type=\"text/javascript\">
    function rpl(expr,a,b) {
      var i=0
      while (i!=-1) {
         i=expr.indexOf(a,i);
         if (i>=0) {
            expr=expr.substring(0,i)+b+expr.substring(i+a.length);
            i+=b.length;
         }
      }
      return expr
    }

    function show_org_source(){
       document.location.href = rpl(document.location.href,\"html\",\"org.html\");
    }
</script>
")))

;; re-export everything regardless of whether or not it's been modified
;; (setq org-publish-use-timestamps-flag nil)

(setq worg-base (expand-file-name "./"))
(setq worg-htmlroot (expand-file-name "./"))
(setq worg-base-directory worg-base)
(setq worg-base-style-directory (concat worg-base "style/"))
(setq worg-base-code-directory (concat worg-base "code/"))
(setq worg-base-color-themes-directory (concat worg-base "color-themes/"))
(setq worg-base-images-directory (concat worg-base "images/"))
(setq worg-publish-directory worg-htmlroot)
(setq worg-publish-style-directory (concat worg-htmlroot "style/"))
(setq worg-publish-code-directory (concat worg-htmlroot "code/"))
(setq worg-publish-sources-directory (concat worg-htmlroot "sources/"))
(setq worg-publish-color-themes-directory (concat worg-htmlroot "color-themes/"))
(setq worg-publish-images-directory (concat worg-htmlroot "images/"))

(defun set-org-publish-project-alist ()
  "Set publishing projects for Orgweb and Worg."
  (interactive)
  (setq org-publish-project-alist
	`(("worg" 
	   :components ("worg-pages" "worg-code" "worg-sources")
	   )
	  ("worg-pages"
	   :base-directory ,worg-base-directory
	   :base-extension "org"
	   :exclude "FIXME"
	   :makeindex t
	   :auto-sitemap t
	   :sitemap-ignore-case t
	   :html-extension "html"
	   :publishing-directory ,worg-publish-directory
	   :publishing-function (org-html-publish-to-html ( lambda (pl fn dn) (org-babel-tangle-file fn (concat (file-name-as-directory dn) (file-name-base fn) ".v") "coq") ))
	   :htmlized-source t
;;	   :section-numbers nil
	   :with-toc t
;;	   :table-of-contents nil
	   :with-timestamps t
	   :timestamps nil
	   :html-style nil  ;; org-html-head-include-default-style
	   :html-head "<link rel=\"stylesheet\" type=\"text/css\" href=\"./code/style.css\"/>"
	   :recursive t
;;	   :html-preamble nil
;;           :html-preamble "<p><a href=\"index.html\">top</a> | <a href=\"theindex.html\">index</a> | <a \
;;href=\"sitemap.html\">sitemap</a> | <a href=\"https://github.com/1337777/OOO1337777\">edit</a></p>"
;;	   :html-preamble ,(with-temp-buffer (insert-file-contents "/home/emacs/git/worg/preamble.html") (buffer-string))
	   :html-postamble nil
;;	   :html-postamble "<div id=\"show_source\"><input type=\"button\" value=\"Show Org source\" onClick='show_org_source()'></div><div id=\"license\"><p>Documentation from the http://orgmode.org/worg/ website (either in its HTML format or in its Org format) is licensed under the <a href=\"http://www.gnu.org/copyleft/fdl.html\">GNU Free Documentation License version 1.3</a> or later.  The code examples and css stylesheets are licensed under the <a href=\"http://www.gnu.org/licenses/gpl.html\">GNU General Public License v3</a> or later.</p></div>"
	   )
	  ("worg-code"
	   :base-directory ,worg-base-code-directory
	   :base-extension "v\\|css\\|js\\|sh" ;;"v\\|html\\|css\\|png\\|js\\|sh\\|bz2\\|el\\|sty\\|awk\\|pl"
	   :publishing-directory ,worg-publish-code-directory
	   :recursive t
	   :publishing-function (org-publish-attachment (lambda (pl fn dn) (htmlize-file fn dn)))
	   )
	  ("worg-sources"
	   :base-directory ,worg-base-directory
	   :base-extension "org"
	   :exclude "theindex\\.org\\|sitemap\\.org"
	   :publishing-directory ,worg-publish-sources-directory
	   :recursive t
	   :publishing-function org-publish-attachment )
	  ("worg-images"
	   :base-directory ,worg-base-directory
	   :base-extension "png\\|jpg\\|gif\\|pdf\\|csv\\|css\\|tex"
	   :publishing-directory ,worg-publish-images-directory
	   :recursive t
	   :publishing-function org-publish-attachment)
	  ("worg-extra"
	   :base-directory ,worg-base-style-directory
	   :base-extension "css"
	   :publishing-directory ,worg-publish-style-directory
	   :publishing-function org-publish-attachment)
)))

(set-org-publish-project-alist)

(defun worg-fix-symbol-table ()
  (when (string-match "org-symbols\\.html" buffer-file-name)
    (goto-char (point-min))
    (while (re-search-forward "<td>&amp;\\([^<;]+;\\)" nil t)
      (replace-match (concat "<td>&" (match-string 1)) t t))))

(defun publish-worg nil
   "Publish Worg."
   (interactive)
   (add-hook 'org-publish-after-export-hook 'worg-fix-symbol-table)
   (let ((org-format-latex-signal-error nil)
	 (worg-base-directory worg-base)
	 (worg-base-code-directory (concat worg-base "code/"))
	 (worg-base-color-themes-directory (concat worg-base "color-themes/"))
	 (worg-base-images-directory (concat worg-base "images/"))
	 (worg-publish-directory worg-htmlroot))
     (set-org-publish-project-alist)
     (message "Emacs %s" emacs-version)
     (org-version)
     (ignore-errors (org-publish-project "worg"))
     (kill-emacs)))

(defun publish-orgweb nil
   "Publish Org web pages."
   (interactive)
   (add-hook 'org-publish-after-export-hook 'worg-fix-symbol-table)
   (let ((org-format-latex-signal-error nil)
	 (org-export-with-sub-superscripts nil))
     (set-org-publish-project-alist)
     (org-publish-project "orgweb")))

(defun parse-org-quotes ()
  "Create ~/orgmode.org/org-quotes.js from org-quotes.org."
  (interactive)
  (load (concat worg-base "code/elisp/worg-fortune.el"))
  (worg-write-fortune-file
   (concat worg-base "org-quotes.org")
   "~/orgmode.org/org-quotes.js"
   120
   "r_text[%d] = \"%s\";" "\n"
   'worg-fortune-insert-javascript-pre
   'worg-fortune-insert-javascript-post))
