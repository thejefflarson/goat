;;; Directory Local Variables
;;; For more information see (info "(emacs) Directory Variables")

((c++-mode
  (eval . (let ((dir (file-name-directory (expand-file-name ".dir-locals.el"))))
            (setq flycheck-clang-include-path
                  (list (concat dir "build/src")
                        (concat dir "src")))))
  (flycheck-clang-language-standard . "c++1y")))
