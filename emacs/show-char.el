(defun show-current-char ()
  (let ((ch (following-char)))
    (format " [U+%04X %s] " ch (get-char-code-property ch 'name))))

(easy-mmode-define-minor-mode show-char-mode
  "Toggle Show char mode."
  t
  (:eval (show-current-char)))

