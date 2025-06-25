;; -*- lexical-binding: t; -*-

(TeX-add-style-hook
 "using-minted-example"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("article" "")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("fontspec" "") ("minted" "") ("xcolor" "svgnames")))
   (add-to-list 'LaTeX-verbatim-environments-local "minted")
   (add-to-list 'LaTeX-verbatim-environments-local "VerbatimWrite")
   (add-to-list 'LaTeX-verbatim-environments-local "VerbEnv")
   (add-to-list 'LaTeX-verbatim-environments-local "SaveVerbatim")
   (add-to-list 'LaTeX-verbatim-environments-local "VerbatimOut")
   (add-to-list 'LaTeX-verbatim-environments-local "LVerbatim*")
   (add-to-list 'LaTeX-verbatim-environments-local "LVerbatim")
   (add-to-list 'LaTeX-verbatim-environments-local "BVerbatim*")
   (add-to-list 'LaTeX-verbatim-environments-local "BVerbatim")
   (add-to-list 'LaTeX-verbatim-environments-local "Verbatim*")
   (add-to-list 'LaTeX-verbatim-environments-local "Verbatim")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "Verb")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "Verb*")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "EscVerb")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "EscVerb*")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "Verb*")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "Verb")
   (TeX-run-style-hooks
    "latex2e"
    "article"
    "art10"
    "fontspec"
    "minted"
    "xcolor")
   (LaTeX-add-minted-newmints
    '("lean" "lean4" "inline")
    '("leancode" "lean4" "ed")))
 :latex)

