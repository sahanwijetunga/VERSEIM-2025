;; -*- lexical-binding: t; -*-

(TeX-add-style-hook
 "using-minted-example"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("article" "")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("graphicx" "") ("minted" "") ("newunicodechar" "")))
   (TeX-run-style-hooks
    "latex2e"
    "article"
    "art10"
    "graphicx"
    "minted"
    "newunicodechar"))
 :latex)

