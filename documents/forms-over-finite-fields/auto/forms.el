;; -*- lexical-binding: t; -*-

(TeX-add-style-hook
 "forms"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("article" "11pt")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("inputenc" "utf8") ("fontenc" "T1") ("graphicx" "") ("longtable" "") ("wrapfig" "") ("rotating" "") ("ulem" "normalem") ("amsmath" "") ("amssymb" "") ("capt-of" "") ("hyperref" "") ("xcolor" "svgnames") ("mathrsfs" "") ("tikz-cd" "") ("svg" "") ("geometry" "top=25mm" "bottom=25mm" "left=25mm" "right=30mm") ("amsthm" "") ("thmtools" "") ("cleveref" "") ("stmaryrd" "") ("minted" "") ("titlesec" "") ("mathalfa" "cal=boondox") ("calc" "")))
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
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "href")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperimage")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperbaseurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "nolinkurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "Verb")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "Verb*")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "EscVerb")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "EscVerb*")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "Verb*")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "Verb")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (TeX-run-style-hooks
    "latex2e"
    "article"
    "art11"
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
    "xcolor"
    "mathrsfs"
    "tikz-cd"
    "svg"
    "geometry"
    "amsthm"
    "thmtools"
    "cleveref"
    "stmaryrd"
    "minted"
    "titlesec"
    "mathalfa"
    "calc")
   (TeX-add-symbols
    '("cslcitation" 2)
    '("cslbibitem" 2)
    '("cslindent" 1)
    '("cslrightinline" 1)
    '("cslleftmargin" 1)
    '("cslblock" 1)
    '("descriptionlabel" 1)
    "totdeg"
    "content"
    "Mat"
    "Hom"
    "Aut"
    "Gal"
    "A"
    "B"
    "FF"
    "LF"
    "HH"
    "X"
    "ff"
    "pp"
    "Z"
    "Nat"
    "Q"
    "R"
    "C"
    "F"
    "PP"
    "Poly"
    "oldpar")
   (LaTeX-add-labels
    "sec:orgd8fff33"
    "sec:orgfe330e3"
    "lemma:non-deg-condition"
    "lemma:orthog-sum"
    "sec:equivalence-of-forms"
    "lemma:isomorphism-preserves-nondegen"
    "sec:alternating-forms"
    "lemma:alt-skew"
    "lemma:hyperbolic-equiv"
    "lemma:hyperbolic-even-dimensional"
    "theorem:alternating-forms-are-hyperbolic"
    "corollary:alternating-forms-classified"
    "sec:symmetric-forms")
   (LaTeX-add-environments
    '("cslbibliography" 2)
    "referee"
    "solution")
   (LaTeX-add-lengths
    "cslhangindent"
    "csllabelsep"
    "csllabelwidth")
   (LaTeX-add-thmtools-declaretheorems
    "theorem"
    "proposition"
    "corollary"
    "lemma"
    "remark"
    "problem"
    "ex"
    "definition"))
 :latex)

