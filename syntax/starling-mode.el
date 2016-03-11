(defconst starling-font-lock-keywords-1
  (list
   ;; These are the main structural keywords.
   (cons (regexp-opt '("view" "method" "constraint")) font-lock-keyword-face)
   ;; Colour in function definitions.
   '("method\\s-+\\([a-zA-Z_][a-zA-Z0-9_]*\\)" 1 font-lock-function-name-face))
  "Minimal highlighting expressions for Starling mode.")

(defconst starling-font-lock-keywords-2
  (append
   starling-font-lock-keywords-1
   (list
    ;; Treat view assertions as doc comments.
    '("{|[^|]*|}" . font-lock-doc-face)
    ;; Add colouring for remaining keywords.
    (cons (regexp-opt '("search" "shared" "thread" "if" "else" "do" "while")) font-lock-keyword-face)
    (cons (regexp-opt '("int" "bool")) font-lock-type-face)))
  "Additional highlighting expressions for Starling mode.")

(defconst starling-font-lock-keywords-3
  (append
   starling-font-lock-keywords-2
   (list
    ;; Treat true and false as constants.
    (cons (regexp-opt '("true" "false")) font-lock-constant-face))
   '(;; Treat func names in a view as function-names.
     ("view\\s-+\\([a-zA-Z_][a-zA-Z0-9_]*\\)" 1 font-lock-function-name-face)
     ;; Treat func names in a constraint as function-names.
     ("constraint\\s-+" "\\([a-zA-Z_][a-zA-Z0-9_]*\\)([^)]*)" nil nil (1 font-lock-function-name-face))
     ;; Warn about an indefinite constraint.
     ("constraint\\s-+" "->\\s-+\\([?]\\)\\s-*;" nil nil (1 font-lock-warning-face))
     ;; Treat emp as builtin inside a constraint.
     ("constraint\\s-+" "emp" nil nil (0 font-lock-builtin-face))
     ;; Warn about the ends of an atomic command.
     ("\\(<\\)[^>]*\\(>\\)\\s-*;"
      (1 font-lock-warning-face)
      (2 font-lock-warning-face))))
  "Yet more highlighting expressions for Starling mode.")

(defconst starling-font-lock-keywords
  starling-font-lock-keywords-3
  "Default highlighting expressions for Starling mode.")

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.cvf\\'" . starling-mode))

(define-derived-mode starling-mode c-mode
  "Starling"
  "Major mode for editing Starling scripts."
  (setq font-lock-defaults '(starling-font-lock-keywords)))

(provide 'starling-mode)
