;;; Directory Local Variables
;;; For more information see (info "(emacs) Directory Variables")

((c++-mode
  (eval . (let ((dir
                 (replace-regexp-in-string "\n$" "/"
                  (shell-command-to-string "git rev-parse --show-toplevel"))))
            (setq flycheck-clang-include-path
                  (list (concat dir "build/src")
                        (concat dir "src")))))
  (flycheck-clang-language-standard . "c++1y")))
