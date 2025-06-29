;; -*- lexical-binding: t; -*-

(TeX-add-style-hook
 "using-minted-plus-beamer"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("beamer" "svgnames")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("inputenc" "utf8") ("fontenc" "T1") ("graphicx" "") ("longtable" "") ("wrapfig" "") ("rotating" "") ("ulem" "normalem") ("amsmath" "") ("amssymb" "") ("capt-of" "") ("hyperref" "") ("mathrsfs" "") ("tikz-cd" "") ("fontspec" "") ("unicode-math" "") ("amsthm" "") ("thmtools" "") ("cleveref" "") ("minted" "") ("newunicodechar" "") ("biblatex" "")))
   (TeX-run-style-hooks
    "latex2e"
    "beamer"
    "beamer10"
    "inputenc"
    "fontenc"
    "graphicx"
    "longtable"
    "wrapfig"
    "rotating"
    "ulem"
    "amsmath"
    "amssymb"
    "capt-of"
    "hyperref"
    "mathrsfs"
    "tikz-cd"
    "fontspec"
    "unicode-math"
    "amsthm"
    "thmtools"
    "cleveref"
    "minted"
    "newunicodechar"
    "biblatex")
   (TeX-add-symbols
    "Z"
    "Q"
    "R"
    "C"
    "F"
    "N"
    "LL"
    "pp"
    "xx"
    "yy"
    "vv"
    "ww")
   (LaTeX-add-labels
    "sec:one"
    "sec:\"finite-algebra\""))
 :latex)

