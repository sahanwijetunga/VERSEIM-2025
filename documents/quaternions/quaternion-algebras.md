author: George McNinch
date: 2025-06-08 11:12:23 EDT (george@valhalla)
header-includes:
``{=latex}; `%%--------------------------------------------------------------------------------`{=latex}; ``{=latex}; `\usepackage[svgnames]{xcolor}`{=latex}; `\usepackage{mathrsfs}`{=latex}; `\usepackage{tikz-cd}`{=latex}; `\usepackage{svg}`{=latex}; `\usepackage[top=25mm,bottom=25mm,left=25mm,right=30mm]{geometry}`{=latex}; ``{=latex}; ``{=latex}; `\usepackage{amsthm}`{=latex}; `\usepackage{thmtools}`{=latex}; `\usepackage{cleveref}`{=latex}; `\usepackage{stmaryrd}`{=latex}; ``{=latex}; `%%\usepackage[outputdir=build]{minted}`{=latex}; `\usepackage{minted}`{=latex}; `\usemintedstyle{tango}`{=latex}; `\usepackage[svgnames]{xcolor}`{=latex}; `\setminted[bash]{bgcolor=NavajoWhite}`{=latex}; `\setminted[python]{bgcolor=Lavender}`{=latex}; `\setminted[sage]{bgcolor=Lavender}`{=latex}; ``{=latex}; `\usepackage{titlesec}`{=latex}; `%%\newcommand{\sectionbreak}{\clearpage}`{=latex}; ``{=latex}; ``{=latex}; `\renewcommand{\descriptionlabel}[1]{\hspace{\labelsep}#1}`{=latex}; ``{=latex}; ``{=latex}; `\usepackage[cal=boondox]{mathalfa}`{=latex}; ``{=latex}; ``{=latex}; `\newenvironment{referee}{\color{red}}{\color{black}}`{=latex}; ``{=latex}; `\numberwithin{equation}{section}`{=latex}; ``{=latex}; `\declaretheorem[numberwithin=subsection,Refname={Theorem,Theorems}]{theorem}`{=latex}; `\declaretheorem[sibling=theorem,name=Proposition,Refname={Proposition,Propositions}]{proposition}`{=latex}; `\declaretheorem[sibling=theorem,name=Corollary,Refname={Corollary,Corollaries}]{corollary}`{=latex}; `\declaretheorem[sibling=theorem,name=Lemma,Refname={Lemma,Lemmas}]{lemma}`{=latex}; `\declaretheorem[sibling=theorem,name=Remark,style=remark,Refname={Remark,Remarks}]{remark}`{=latex}; `\declaretheorem[sibling=theorem,name=Problem,style=remark,Refname={Problem,Problems}]{problem}`{=latex}; `\declaretheorem[sibling=theorem,name=Example,style=remark,Refname={Example,Examples}]{ex}`{=latex}; `\declaretheorem[sibling=theorem,name=Definition,style=remark,Refname={Definition,Definitions}]{definition}`{=latex}; ``{=latex}; `\crefname{equation}{}{}`{=latex}; ``{=latex}; `%%--------------------------------------------------------------------------------`{=latex}; ``{=latex}; `\newenvironment{solution}`{=latex}; `{\par \color{red}\hrulefill \newline \noindent \textbf{Solution:} \vspace{2mm}}`{=latex}; `{\vspace{2mm} \color{black}}`{=latex}; ``{=latex}; ``{=latex}; `\newcommand{\totdeg}{\operatorname{totdeg}}`{=latex}; `\newcommand{\content}{\operatorname{content}}`{=latex}; ``{=latex}; `\newcommand{\Mat}{\operatorname{Mat}}`{=latex}; ``{=latex}; `\newcommand{\Aut}{\operatorname{Aut}}`{=latex}; `\newcommand{\Gal}{\operatorname{Gal}}`{=latex}; ``{=latex}; `\newcommand{\A}{\mathscr{A}}`{=latex}; `\newcommand{\B}{\mathscr{B}}`{=latex}; `\newcommand{\FF}{\mathscr{F}}`{=latex}; `\newcommand{\LF}{\mathcal{LF}}`{=latex}; ``{=latex}; `\newcommand{\HH}{\mathcal{H}}`{=latex}; `\newcommand{\X}{\mathscr{X}}`{=latex}; ``{=latex}; `\newcommand{\ff}{\mathfrak{f}}`{=latex}; `\newcommand{\pp}{\mathfrak{p}}`{=latex}; ``{=latex}; `\newcommand{\Z}{\mathbb{Z}}`{=latex}; `\newcommand{\Nat}{\mathbb{N}}`{=latex}; `\newcommand{\Q}{\mathbb{Q}}`{=latex}; `\newcommand{\R}{\mathbb{R}}`{=latex}; `\newcommand{\C}{\mathbb{C}}`{=latex}; `\newcommand{\F}{\mathbb{F}}`{=latex}; ``{=latex}; `\newcommand{\PP}{\mathbb{P}}`{=latex}; ``{=latex}; `\newcommand{\Poly}{\mathcal{P}}`{=latex}; `%%--------------------------------------------------------------------------------`{=latex}; `<div style="display: none"> \(`{=html}; ``{=html}; `%%--------------------------------------------------------------------------------`{=html}; ``{=html}; `\usepackage[svgnames]{xcolor}`{=html}; `\usepackage{mathrsfs}`{=html}; `\usepackage{tikz-cd}`{=html}; `\usepackage{svg}`{=html}; `\usepackage[top=25mm,bottom=25mm,left=25mm,right=30mm]{geometry}`{=html}; ``{=html}; ``{=html}; `\usepackage{amsthm}`{=html}; `\usepackage{thmtools}`{=html}; `\usepackage{cleveref}`{=html}; `\usepackage{stmaryrd}`{=html}; ``{=html}; `%%\usepackage[outputdir=build]{minted}`{=html}; `\usepackage{minted}`{=html}; `\usemintedstyle{tango}`{=html}; `\usepackage[svgnames]{xcolor}`{=html}; `\setminted[bash]{bgcolor=NavajoWhite}`{=html}; `\setminted[python]{bgcolor=Lavender}`{=html}; `\setminted[sage]{bgcolor=Lavender}`{=html}; ``{=html}; `\usepackage{titlesec}`{=html}; `%%\newcommand{\sectionbreak}{\clearpage}`{=html}; ``{=html}; ``{=html}; `\renewcommand{\descriptionlabel}[1]{\hspace{\labelsep}#1}`{=html}; ``{=html}; ``{=html}; `\usepackage[cal=boondox]{mathalfa}`{=html}; ``{=html}; ``{=html}; `\newenvironment{referee}{\color{red}}{\color{black}}`{=html}; ``{=html}; `\numberwithin{equation}{section}`{=html}; ``{=html}; `\declaretheorem[numberwithin=subsection,Refname={Theorem,Theorems}]{theorem}`{=html}; `\declaretheorem[sibling=theorem,name=Proposition,Refname={Proposition,Propositions}]{proposition}`{=html}; `\declaretheorem[sibling=theorem,name=Corollary,Refname={Corollary,Corollaries}]{corollary}`{=html}; `\declaretheorem[sibling=theorem,name=Lemma,Refname={Lemma,Lemmas}]{lemma}`{=html}; `\declaretheorem[sibling=theorem,name=Remark,style=remark,Refname={Remark,Remarks}]{remark}`{=html}; `\declaretheorem[sibling=theorem,name=Problem,style=remark,Refname={Problem,Problems}]{problem}`{=html}; `\declaretheorem[sibling=theorem,name=Example,style=remark,Refname={Example,Examples}]{ex}`{=html}; `\declaretheorem[sibling=theorem,name=Definition,style=remark,Refname={Definition,Definitions}]{definition}`{=html}; ``{=html}; `\crefname{equation}{}{}`{=html}; ``{=html}; `%%--------------------------------------------------------------------------------`{=html}; ``{=html}; `\newenvironment{solution}`{=html}; `{\par \color{red}\hrulefill \newline \noindent \textbf{Solution:} \vspace{2mm}}`{=html}; `{\vspace{2mm} \color{black}}`{=html}; ``{=html}; ``{=html}; `\newcommand{\totdeg}{\operatorname{totdeg}}`{=html}; `\newcommand{\content}{\operatorname{content}}`{=html}; ``{=html}; `\newcommand{\Mat}{\operatorname{Mat}}`{=html}; ``{=html}; `\newcommand{\Aut}{\operatorname{Aut}}`{=html}; `\newcommand{\Gal}{\operatorname{Gal}}`{=html}; ``{=html}; `\newcommand{\A}{\mathscr{A}}`{=html}; `\newcommand{\B}{\mathscr{B}}`{=html}; `\newcommand{\FF}{\mathscr{F}}`{=html}; `\newcommand{\LF}{\mathcal{LF}}`{=html}; ``{=html}; `\newcommand{\HH}{\mathcal{H}}`{=html}; `\newcommand{\X}{\mathscr{X}}`{=html}; ``{=html}; `\newcommand{\ff}{\mathfrak{f}}`{=html}; `\newcommand{\pp}{\mathfrak{p}}`{=html}; ``{=html}; `\newcommand{\Z}{\mathbb{Z}}`{=html}; `\newcommand{\Nat}{\mathbb{N}}`{=html}; `\newcommand{\Q}{\mathbb{Q}}`{=html}; `\newcommand{\R}{\mathbb{R}}`{=html}; `\newcommand{\C}{\mathbb{C}}`{=html}; `\newcommand{\F}{\mathbb{F}}`{=html}; ``{=html}; `\newcommand{\PP}{\mathbb{P}}`{=html}; ``{=html}; `\newcommand{\Poly}{\mathcal{P}}`{=html}; `%%--------------------------------------------------------------------------------`{=html}; `\)</div>`{=html}
keywords: quaternions, number-theory
title: Quaternion algebras

``{=latex}

`%%--------------------------------------------------------------------------------`{=latex}

``{=latex}

`\usepackage[svgnames]{xcolor}`{=latex}

`\usepackage{mathrsfs}`{=latex}

`\usepackage{tikz-cd}`{=latex}

`\usepackage{svg}`{=latex}

`\usepackage[top=25mm,bottom=25mm,left=25mm,right=30mm]{geometry}`{=latex}

``{=latex}

``{=latex}

`\usepackage{amsthm}`{=latex}

`\usepackage{thmtools}`{=latex}

`\usepackage{cleveref}`{=latex}

`\usepackage{stmaryrd}`{=latex}

``{=latex}

`%%\usepackage[outputdir=build]{minted}`{=latex}

`\usepackage{minted}`{=latex}

`\usemintedstyle{tango}`{=latex}

`\usepackage[svgnames]{xcolor}`{=latex}

`\setminted[bash]{bgcolor=NavajoWhite}`{=latex}

`\setminted[python]{bgcolor=Lavender}`{=latex}

`\setminted[sage]{bgcolor=Lavender}`{=latex}

``{=latex}

`\usepackage{titlesec}`{=latex}

`%%\newcommand{\sectionbreak}{\clearpage}`{=latex}

``{=latex}

``{=latex}

`\renewcommand{\descriptionlabel}[1]{\hspace{\labelsep}#1}`{=latex}

``{=latex}

``{=latex}

`\usepackage[cal=boondox]{mathalfa}`{=latex}

``{=latex}

``{=latex}

`\newenvironment{referee}{\color{red}}{\color{black}}`{=latex}

``{=latex}

`\numberwithin{equation}{section}`{=latex}

``{=latex}

`\declaretheorem[numberwithin=subsection,Refname={Theorem,Theorems}]{theorem}`{=latex}

`\declaretheorem[sibling=theorem,name=Proposition,Refname={Proposition,Propositions}]{proposition}`{=latex}

`\declaretheorem[sibling=theorem,name=Corollary,Refname={Corollary,Corollaries}]{corollary}`{=latex}

`\declaretheorem[sibling=theorem,name=Lemma,Refname={Lemma,Lemmas}]{lemma}`{=latex}

`\declaretheorem[sibling=theorem,name=Remark,style=remark,Refname={Remark,Remarks}]{remark}`{=latex}

`\declaretheorem[sibling=theorem,name=Problem,style=remark,Refname={Problem,Problems}]{problem}`{=latex}

`\declaretheorem[sibling=theorem,name=Example,style=remark,Refname={Example,Examples}]{ex}`{=latex}

`\declaretheorem[sibling=theorem,name=Definition,style=remark,Refname={Definition,Definitions}]{definition}`{=latex}

``{=latex}

`\crefname{equation}{}{}`{=latex}

``{=latex}

`%%--------------------------------------------------------------------------------`{=latex}

``{=latex}

`\newenvironment{solution}`{=latex}

`{\par \color{red}\hrulefill \newline \noindent \textbf{Solution:} \vspace{2mm}}`{=latex}

`{\vspace{2mm} \color{black}}`{=latex}

``{=latex}

``{=latex}

`\newcommand{\totdeg}{\operatorname{totdeg}}`{=latex}

`\newcommand{\content}{\operatorname{content}}`{=latex}

``{=latex}

`\newcommand{\Mat}{\operatorname{Mat}}`{=latex}

``{=latex}

`\newcommand{\Aut}{\operatorname{Aut}}`{=latex}

`\newcommand{\Gal}{\operatorname{Gal}}`{=latex}

``{=latex}

`\newcommand{\A}{\mathscr{A}}`{=latex}

`\newcommand{\B}{\mathscr{B}}`{=latex}

`\newcommand{\FF}{\mathscr{F}}`{=latex}

`\newcommand{\LF}{\mathcal{LF}}`{=latex}

``{=latex}

`\newcommand{\HH}{\mathcal{H}}`{=latex}

`\newcommand{\X}{\mathscr{X}}`{=latex}

``{=latex}

`\newcommand{\ff}{\mathfrak{f}}`{=latex}

`\newcommand{\pp}{\mathfrak{p}}`{=latex}

``{=latex}

`\newcommand{\Z}{\mathbb{Z}}`{=latex}

`\newcommand{\Nat}{\mathbb{N}}`{=latex}

`\newcommand{\Q}{\mathbb{Q}}`{=latex}

`\newcommand{\R}{\mathbb{R}}`{=latex}

`\newcommand{\C}{\mathbb{C}}`{=latex}

`\newcommand{\F}{\mathbb{F}}`{=latex}

``{=latex}

`\newcommand{\PP}{\mathbb{P}}`{=latex}

``{=latex}

`\newcommand{\Poly}{\mathcal{P}}`{=latex}

`%%--------------------------------------------------------------------------------`{=latex}

`<div style="display: none"> \(`{=html}

``{=html}

`%%--------------------------------------------------------------------------------`{=html}

``{=html}

`\usepackage[svgnames]{xcolor}`{=html}

`\usepackage{mathrsfs}`{=html}

`\usepackage{tikz-cd}`{=html}

`\usepackage{svg}`{=html}

`\usepackage[top=25mm,bottom=25mm,left=25mm,right=30mm]{geometry}`{=html}

``{=html}

``{=html}

`\usepackage{amsthm}`{=html}

`\usepackage{thmtools}`{=html}

`\usepackage{cleveref}`{=html}

`\usepackage{stmaryrd}`{=html}

``{=html}

`%%\usepackage[outputdir=build]{minted}`{=html}

`\usepackage{minted}`{=html}

`\usemintedstyle{tango}`{=html}

`\usepackage[svgnames]{xcolor}`{=html}

`\setminted[bash]{bgcolor=NavajoWhite}`{=html}

`\setminted[python]{bgcolor=Lavender}`{=html}

`\setminted[sage]{bgcolor=Lavender}`{=html}

``{=html}

`\usepackage{titlesec}`{=html}

`%%\newcommand{\sectionbreak}{\clearpage}`{=html}

``{=html}

``{=html}

`\renewcommand{\descriptionlabel}[1]{\hspace{\labelsep}#1}`{=html}

``{=html}

``{=html}

`\usepackage[cal=boondox]{mathalfa}`{=html}

``{=html}

``{=html}

`\newenvironment{referee}{\color{red}}{\color{black}}`{=html}

``{=html}

`\numberwithin{equation}{section}`{=html}

``{=html}

`\declaretheorem[numberwithin=subsection,Refname={Theorem,Theorems}]{theorem}`{=html}

`\declaretheorem[sibling=theorem,name=Proposition,Refname={Proposition,Propositions}]{proposition}`{=html}

`\declaretheorem[sibling=theorem,name=Corollary,Refname={Corollary,Corollaries}]{corollary}`{=html}

`\declaretheorem[sibling=theorem,name=Lemma,Refname={Lemma,Lemmas}]{lemma}`{=html}

`\declaretheorem[sibling=theorem,name=Remark,style=remark,Refname={Remark,Remarks}]{remark}`{=html}

`\declaretheorem[sibling=theorem,name=Problem,style=remark,Refname={Problem,Problems}]{problem}`{=html}

`\declaretheorem[sibling=theorem,name=Example,style=remark,Refname={Example,Examples}]{ex}`{=html}

`\declaretheorem[sibling=theorem,name=Definition,style=remark,Refname={Definition,Definitions}]{definition}`{=html}

``{=html}

`\crefname{equation}{}{}`{=html}

``{=html}

`%%--------------------------------------------------------------------------------`{=html}

``{=html}

`\newenvironment{solution}`{=html}

`{\par \color{red}\hrulefill \newline \noindent \textbf{Solution:} \vspace{2mm}}`{=html}

`{\vspace{2mm} \color{black}}`{=html}

``{=html}

``{=html}

`\newcommand{\totdeg}{\operatorname{totdeg}}`{=html}

`\newcommand{\content}{\operatorname{content}}`{=html}

``{=html}

`\newcommand{\Mat}{\operatorname{Mat}}`{=html}

``{=html}

`\newcommand{\Aut}{\operatorname{Aut}}`{=html}

`\newcommand{\Gal}{\operatorname{Gal}}`{=html}

``{=html}

`\newcommand{\A}{\mathscr{A}}`{=html}

`\newcommand{\B}{\mathscr{B}}`{=html}

`\newcommand{\FF}{\mathscr{F}}`{=html}

`\newcommand{\LF}{\mathcal{LF}}`{=html}

``{=html}

`\newcommand{\HH}{\mathcal{H}}`{=html}

`\newcommand{\X}{\mathscr{X}}`{=html}

``{=html}

`\newcommand{\ff}{\mathfrak{f}}`{=html}

`\newcommand{\pp}{\mathfrak{p}}`{=html}

``{=html}

`\newcommand{\Z}{\mathbb{Z}}`{=html}

`\newcommand{\Nat}{\mathbb{N}}`{=html}

`\newcommand{\Q}{\mathbb{Q}}`{=html}

`\newcommand{\R}{\mathbb{R}}`{=html}

`\newcommand{\C}{\mathbb{C}}`{=html}

`\newcommand{\F}{\mathbb{F}}`{=html}

``{=html}

`\newcommand{\PP}{\mathbb{P}}`{=html}

``{=html}

`\newcommand{\Poly}{\mathcal{P}}`{=html}

`%%--------------------------------------------------------------------------------`{=html}

`\)</div>`{=html}

# Some references

-   [Some notes of Keith Conrad
    (UConn)](https://kconrad.math.uconn.edu/blurbs/ringtheory/quaternionalg.pdf)

-   first chapter of [Gille-Szamuely - “Central Simple Algebras and
    Galois
    Cohomology”](https://www.cambridge.org/core/books/central-simple-algebras-and-galois-cohomology/B4A8F430A0D6C5A59722BD48AEF94C05)

# Quaternion algebras, defined

If $k$ is a field, an *algebra* $A$ over $k$ is a $k$-vector space $A$
together with operations $+:A \times A \to A$ and
$\cdot:A \times A \to A$ which satisfy the axioms of a *ring*.

Here, we are going to insist that the algebra $A$ be finite dimensional
as a $k$-vector space, and that there is a multiplicative identity
element $1 \in A$.

Given a field $\ell$ containing $k$ (a “field extension of $k$”) we can
form an $\ell$-algebra $A_\ell$ by *extension of scalars*. (Really, this
is the tensor product: $A_\ell = A \otimes_k
\ell$).

The algebra $A$ is said to be *central simple* over $k$ if for some
field extension $\ell$ of $k$ and for some $n \in \Nat$, the
$\ell$-algebra $A_\ell$ is isomorphic as $\ell$-algebras to
$\Mat_n(\ell)$, the algebra of $n \times n$ matrices over $\ell$.

Now, a *quaternion algebra* is a central simple algebra $Q$ over $k$
with $\dim Q = 4$. Thus for some field extension $\ell$ of $k$, the
$\ell$-algebra $Q_\ell$ is isomorphic to $\Mat_{2}(k)$

# A description of quaternion algebras

A quaternion algebra $Q$ over $k$ can be described in a explicit manner.
The case where $k$ has characteristic 2 is slightly different and I'll
omit it here, so suppose that $k$ has characteristic $\ne 2$.

Given $a,b \in k$ non-zero elements, we define the $k$-algebra $(a,b)_k$
to be the $k$-vector space with basis $1,i,j,ij$ where the
multiplication satisfies $$i^2 = a, j^2 = b, ij = -ji$$

<div class="theorem" markdown="1">

Suppose that $k$ does not have characteristic 2. If $Q$ is a quaternion
algebra over $k$, there are non-zero elements $a,b \in
k$ for which $Q \simeq (a,b)_k$.

</div>

If $\alpha = s + ti + uj + vij \in (a,b)_k$ for $s,t,u,v \in k$, the
conjugate $\overline{\alpha}$ is defined to be

$$\begin{equation*}
\overline{\alpha} = s - ti - uj - vij
\end{equation*}$$

<div class="proposition" markdown="1">

The assignment $N:(a,b)_k \to k$ given by $N(\alpha) = \alpha \cdot
\overline{\alpha} = s^2 - at^2 - bu^2 + abv$ defines a non-degenerate
quadratic form on the vector space $(a,b)_k$.

</div>

We call this quadratic form $N$ the *norm* – or the *norm form* – of the
quaternion algebra $(a,b)_k$.

<div class="theorem" markdown="1">

The quaternion algebra $(a,b)_k$ is a division algebra if and only if
the norm $N$ does not vanish at any nonzero element of $(a,b)_k$; i.e.
$N(\alpha) = 0 \implies \alpha = 0$.

</div>

# Associated conics

Associated with the quaternion algebra $(a,b)_k$ is the conic $C=C(a,b)$
which is the set of solutions to the equation $ax^2 +
by^2 = z^2$ in the projective plane $\PP^2$. In turn, we can consider
the field of rational functions $k(C)$ on this conic; it is the field of
fractions of the algebra $k[x,y]/\langle ax^2 + by^2 -
1\rangle.$ One sometimes calls $k(C)$ the “function field of $C$”.

We may now state an important theorem due to Witt:

<div class="theorem" markdown="1">

Let $Q_1 = (a_1,b_1)_k$ and $Q_2 = (a_2,b_2)_k$ be quaternion algebras
over $k$, and let $C_1$ and $C_2$ be the associated conics. The algebra
$Q_1$ and $Q_2$ are isomorphic if and only if the the function fields
$k(C_1)$ and $k(C_2)$ are isomorphic.

</div>

In particular, Witt's theorem shows that two quaternion algebras are
isomorphic if and only if the associated conics are isomorphic as
algebraic curves.
