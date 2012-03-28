(push "~/work/sandbox/emacs/" load-path)

(load "show-char")

(add-hook 'c-mode-hook '(lambda () (setq mode-require-final-newline nil)))

(blink-cursor-mode 0)
(global-set-key "\C-z" 'scroll-down)
(global-set-key "\C-\\" 'undo)
(proofgeneral)
(global-linum-mode 5)
(column-number-mode t)
(add-hook 'coq-mode-hook
	  '(lambda ()
	     (define-key coq-keymap [(control ?f)] 'coq-SearchConstant)
	     (define-key coq-keymap [(control ?a)] 'coq-SearchAbout)))

(setq completion-ignore-case t)
(setq completion-ignored-extensions
      (append completion-ignored-extensions '(".v.d" ".vo" ".glob")))

(setq inhibit-startup-message t)

(setq startup-dir (pwd))
(setq frame-title-format
      '("Emacs %b -- " startup-dir))

(custom-set-variables
  ;; custom-set-variables was added by Custom.
  ;; If you edit it by hand, you could mess it up, so be careful.
  ;; Your init file should contain only one such instance.
  ;; If there is more than one, they won't work right.
 '(dabbrev-case-distinction nil)
 '(dabbrev-case-fold-search nil)
 '(dabbrev-case-replace nil)
 '(global-hl-line-mode t)
 '(global-visual-line-mode nil)
 '(initial-frame-alist (quote ((menu-bar-lines . 1) (tool-bar-lines . 0) (width . 220) (height . 60))))
 '(make-backup-files nil)
 '(mouse-wheel-progressive-speed nil)
 '(mouse-wheel-scroll-amount (quote (1 ((shift) . 1) ((control)))))
 '(proof-electric-terminator-enable nil)
 '(proof-three-window-enable t)
 '(scroll-bar-mode (quote right))
 '(scroll-preserve-screen-position 1)
 '(tool-bar-mode nil))
(custom-set-faces
  ;; custom-set-faces was added by Custom.
  ;; If you edit it by hand, you could mess it up, so be careful.
  ;; Your init file should contain only one such instance.
  ;; If there is more than one, they won't work right.
 '(hl-line ((t (:inherit highlight :background "light grey")))))
