# General theory of fractal path integrals with applications to many-body theories and statistical physics

Masuo Suzuki

Department of Physics, Faculty of Science, University of Tokyo, Bunkyo-Ku, Hongo, Tokyo 113, Japan

(Received 26 March 1990; accepted for publication 12 September 1990)

A general scheme of fractal decomposition of exponential operators is presented in any order m. Namely, exp[ $x ( A + B ) ] = S _ { m } ( x ) + O ( x ^ { m + 1 } )$ for any positive integer m, where $S_{m}(x) = e^{t_{1}A}e^{t_{2}B}e^{t_{3}A}e^{t_{4}B} \cdots e^{t_{M}A}$ with finite M depending on m. A general recursive scheme of construction of $\{ t _ { j } \}$ is given explicitly. It is proven that some of $[ t _ { j } ]$ should be negative for m≥3 and for any finite M (nonexistence theorem of positive decomposition). General systematic decomposition criterions based on a new type of time-ordering are also formulated. The decomposition ex $\mathrm{kp}[x(A + B)] = [S_m(x/n)]^n + O(x^{m+1}/n^m)$ yields a new efficient approach to quantum Monte Carlo simulations.

## I. INTRODUCTION

The concept of fractal path integrals is introduced in this paper, namely, a general new scheme of fractal decomposition of exponential operators is presented together with some explicit real and complex representations. A brief report of the present idea has already been given in a previous letter.'

The main purpose of the present paper is to find a systematic series of approximants of the form

$$
f _ { m } \left( A , B \right) = e ^ { t _ { 1 } A } e ^ { t _ { 2 } B } e ^ { t _ { 3 } A } e ^ { t _ { 4 } B } \cdots e ^ { t _ { M } A } ,\tag{1.1}
$$

for the exponential operator ex $\mathtt { p } [ x ( A + B ) ]$ with real or complex numbers $\{ t _ { j } \} ^ { j }$ with finite M. Namely, the product operator (1.1) for integer m plays a role of the mth approximant of $\exp[x(A + B)]$ in the sense that

$$
\exp[x(A + B)] = f_m(A,B) + O(x^{m+1})\tag{1.2}
$$

for small x.

The above new scheme (1.2) with (1.1) is very useful in studying theoretically quantum many-body systems using the following generalized Trotter formula:²-5

$$
\exp \left[ x ( A + B ) \right] = \left[ f _ { m } \left( \frac { A } { n } , \frac { B } { n } \right) \right] ^ { n } + O \left( \frac { x ^ { m + 1 } } { n ^ { m } } \right)\tag{1.3}
$$

for the approximant $f _ { m } \left( A \mathrm { , } B \right)$ in (1.2). Thus we find that the convergence of our new scheme is extremely rapid for $x / n   \ll   1$ . This choice of decomposition is practically important in quantum Monte Carlo simulations.47

In Sec. II, a general recursion method' is presented to explicitly obtain the decomposition formula (1.2) and some symmetry relations of decomposition are derived, particularly concerning the relation between the $( 2 m - 1 )$ th and 2mth approximants. In Sec. III, some typical schemes of real decomposition are presented explicitly. Complex decomposition is given in Sec. IV. The proof of nonexistence of“positive decomposition" [i.e., (1.1) with all positive $\{ t _ { j } \} ]$ is given in Sec. V. In Sec. VII, a general method to expand the product (1.1) in a power series of the operators A and B is proposed. This is a time-ordering method analogous to Feynman's time-ordering technique. Sum rules concerning the coefficients of the power-series expansion of the exponential operator exp $[ x ( A + B ) ]$ are also derived. These sum rules are conveniently used in reducing the number of equations to determine the parameters $\{ t _ { j } ^ { \gamma } \}$ in (1.1), as will be seen later. In Sec. VII, general decomposition conditions are derived explicitly. In Sec. VIII, a fractal-temperature quantum Monte Carlo method is formulated with an emphasis on the rapid convergence of it. In Sec. IX, a fractal-time Monte Carlo method is discussed with some possible applications to nuclear physics and to chemical reactions. A combination of the present fractal decomposition and Sorella's method is proposed in Sec. X. Summary and discussion are given in Sec. XI.

## II. RECURSION METHOD AND SYMMETRY PROPERTIES OF DECOMPOSITION

It is extremely complicated to determine the parameters $\{ t _ { j } \}$ in such a primitive way as we expand (1.1) and equate each term thus obtained to the corresponding term of the original exponential operator exp $[ x ( A + B ) ]$ , as will be seen in Sec. VII.

In the present section, we devise a recursion method to find a systematic series of approximants (1.1), namely, we have the following fractal decomposition theorem.'

Theorem 1 (construction theorem): For the exponential operator exp $x(A_{1} + A_{2} + \cdots + A_{q})$ , we consider the following (m — 1)th approximant:

$$
\exp \left( x \sum_{j = 1}^{q} A_{j} \right) = Q_{m - 1}(x) + O(x^{m}).\tag{2.1}
$$

Then, the mth approximant $\mathcal { Q } _ { m } ( x )$ is constructed as follows:

$$
\mathcal { Q } _ { m } ( x ) = \prod _ { j = 1 } ^ { r } \mathcal { Q } _ { m - 1 } ( p _ { m , j } x ) ,\tag{2.2}
$$

for $\Gamma \geqslant 2 ,$ , where the parameters $\{ p _ { m , j } \}$ are the solutions of the following decomposition condition that

$$
\sum_{j = 1}^{r} p_{m,j}^{m} = 0, \quad  with  \quad \sum_{j = 1}^{r} p_{m,j} = 1.\tag{2.3}
$$

400

The proof is easily given from the following identity:

$$
\exp \left( x \sum_{k = 1}^{q} A_{k} \right) = \prod_{j = 1}^{r} \exp \left( p_{m, j} x \sum_{k = 1}^{q} A_{k} \right).\tag{2.4}
$$

First, we substitute the (m — 1)th approximant $Q _ { m \textrm { - } 1 } ( p _ { m , j } x )$ in each factor of (2.4). The decomposition condition (2.3) is derived both from the requirement that the sum of the uncontrollable mth-order terms in (2.4)

$$
x ^ { m } \biggl ( \sum _ { j \; = \; 1 } ^ { r } p _ { m , j } ^ { m } \biggr ) \biggl ( \sum _ { k \; = \; 1 } ^ { q } A _ { k } \biggr ) ^ { m }\tag{2.5}
$$

should vanish, and from the requirement that the corresponding sum of the mth-order terms in each $Q _ { m \textrm { -- } 1 } ( p _ { m , j } x )$ should also vanish. In order to study the latter condition explicitly, we write the mth-order term of $\mathcal { Q } _ { m \textrm { -- } 1 } ( x )$ as

$$
\left[ Q _ { m - 1 } ( x ) \right] _ { m } = x ^ { m } P _ { m } \left( \left\{ A _ { j } \right\} \right) .\tag{2.6}
$$

Then, the sum of the mth-order terms in each factor of the right-hand side of (2.4) is given by

$$
x ^ { m } \biggl ( \sum _ { j = 1 } ^ { r } p _ { m , j } ^ { m } \biggr ) P _ { m } \left( \left\{ A _ { j } \right\} \right) .\tag{2.7}
$$

Fortunately we find that the two uncontrollable expressions (2.5) and (2.7) vanish under the single common condition

$$
\sum _ { y = 1 } ^ { r } p _ { m , j } ^ { m } = 0 .\tag{2.8}
$$

Thus we arrive at Theorem 1. It should be remarked here that only cross terms of each factor $\mathcal { Q } _ { m \textrm { -- } 1 } ( p _ { m , j } x )$ in (2.2) contribute to the mth-order term of $Q _ { m } ( x )$ . This is one of the reasons why the convergence of the present new scheme is very rapid and why it is physical in the sense that quantum coherence comes from the noncommutativity of the operators A and $B ,$ namely, the cross effect.

Next, we discuss the equivalence theorem.2 between the (2m-1)th and 2mth approximants, when they are symmetric, namely,

$$
Q_{2m - 1}(-x)Q_{2m - 1}(x) = 1.\tag{2.9}
$$

We have the following theorem.

Theorem 2 (symmetry theorem): We assume that the original operator $F ( x )$ with a parameter x is symmetric in the sense that

$$
F ( x ) F ( - x ) = 1 ; \quad F ( 0 ) = 1 ,\tag{2.10}
$$

and for it we construct, in general, a symmetric (2m — 1 ) thorder approximant $G _ { 2 m \textrm { -- } 1 } ( x )$ , namely,

$$
F ( x ) = G _ { 2 m - 1 } ( x ) + O ( x ^ { 2 m } ) ,\tag{2.11}
$$

where

$$
G _ { 2 m - 1 } ( x ) G _ { 2 m - 1 } ( - x ) = 1.\tag{2.12}
$$

Then, $G _ { 2 m \textrm { -- } 1 } ( x )$ is also correct up to the order of x²', namely,

$$
G _ { 2 m \mathrm { ~ - ~ } 1 } \left( x \right) = G _ { 2 m } \left( x \right) .\tag{2.13}
$$

This theorem was mentioned briefly in Ref. 2 without detailed proof. The proof is given as follows. First, we put

$$
F ( x ) = G _ { 2 m - 1 } ( x ) + x ^ { 2 m } R _ { 2 m } ( \{ A _ { j } \} ) + O ( x ^ { 2 m + 1 } ) .\tag{2.14}
$$

Then, from (2.10), we have

$$
\begin{align*}R_{2m} \left( \left\{ A_j \right\} \right) G_{2m-1} \left( -x \right) \quad & \\+ \quad & G_{2m-1} \left( x \right) R_{2m} \left( \left\{ A_j \right\} \right) = O(x),\end{align*}\tag{2.15}
$$

using the symmetry property (2.12). As we have $G _ { 2 m   -   1 } ( 0 ) = 1$ (unit operator) from (2.10) and (2.12), we arrive finally at

$$
R _ { 2 m } \left( \left\{ A _ { j } \right\} \right) = 0 ,\tag{2.16}
$$

by putting $x   =   0$ in (2.15), namely, we have the desired relation (2.13).

This theorem is particularly useful when the odd approximant $G _ { 2 m - 1 } ( x )$ is easily obtained, as will be seen later.

## III. REAL DECOMPOSITION BASED ON THE RECURSION METHOD

In the present section, we explicitly derive some typical schemes of real decomposition using the general recursion method.

The simplest decomposition of exp[x(A + B) ] is

$$
f_{1}(A,B)=e^{xA}e^{AB}\tag{3.1}
$$

as is well known. This is of the first order of x. The simplest second-order decomposition is given by the following symmetric product:1-5

$$
S ( x ) = e ^ { ( x / 2 ) A } e ^ { x B } e ^ { ( x / 2 ) A } ,
$$

namely,

(3.2)

$$
e^{x(A + B)} = S(x) + O(x^3).\tag{3.3}
$$

First, we consider the case $r = 3$ in Theorem 1. Namely, we start from the following identity

$$
e ^ { x ( A \; + \; B ) } = e ^ { s x ( A \; + \; B ) } e ^ { ( 1 \; - \; 2 s ) x ( A \; + \; B ) } e ^ { s x ( A \; + \; B ) } ,\tag{3.4}
$$

The third-order symmetric approximant $S _ { 3 } \left( x \right)$ is given by

$$
S _ { 3 } ( x ) = S ( s x ) S ( ( 1 - 2 s ) x ) S ( s x ) ,\tag{3.5}
$$

where the parameter s is given by the real solution of the equation

$$
2 s ^ { 3 } + ( 1 - 2 s ) ^ { 3 } = 0 ,\tag{3.6}
$$

according to Theorem 1, namely,

$$
s = 1 / ( 2 - 3 { \sqrt { 2 } } ) = 1 . 3 5 1 2 \ldots\tag{3.7}
$$

Thus the simplest real decomposition of third order is given explicitly by

$$
\begin{align*}S_{3}(x) = & e^{(s/2)xA}e^{sxB}e^{[(1-s)/2]xA}e^{(1-2s)xB} \\& \times e^{[(1-s)/2]xA}e^{sxB}e^{(s/2)xA},\end{align*}
$$

with s in (3.7). This is symmetric in the sense that

(3.8)

$$
S_{3}(x)S_{3}(-x)=1.\tag{3.9}
$$

Then, we can supply Theorem 2 to obtain the fourth-order approximant $S _ { 4 } \left( x \right)$ as

$$
S _ { 4 } ( x ) = S _ { 3 } ( x ) .\tag{3.10}
$$

In general, the (2m — 1)th and 2mth approximants, $S _ { 2 m \textrm { -- } 1 } ( x )$ and $S _ { 2 m } \left( x \right)$ , are determined recursively as

$$
\begin{align*}S_{2m - 1}(x) = & S_{2m}(x) \\= & S_{2m - 3}(k_m x)S_{2m - 3}((1 - 2k_m)x) \\& \times S_{2m - 3}(k_m x),\end{align*}
$$

where

(3.11)

$$
k _ { m } = ( 2 - 2 ^ { 1 / ( 2 m   -   1 ) } ) ^ { -   1 } .\tag{3.12}
$$

It should be noted here that all the parameters $\{ k _ { m } \}$ are larger than unity (i.e., $k _ { m } > 1 )$ , and consequently that this series of approximants is not convergent in the limit $m   \to   \infty$ Thus this scheme of decomposition is not practical for large m.

Next, we try to find a practical scheme of real decomposition, namely, for real $t _ { m }$ whose magnitude is less than unity $( \mathrm { i . e . , } | t _ { m } | < 1 )$ . For this purpose, we consider' the following symmetric real decomposition for the exponential operator

$$
\begin{aligned}F(x) & \equiv \exp \left[ x \left( A_1 + A_2 + \cdots + A_q \right) \right] \\& = S_{2m}^*(x) + O(x^{2m+1}).\end{aligned}\tag{3.13}
$$

From Theorems 1 and 2, we have the recursion formula'

$$
\begin{aligned}S_{2m}^{*}(x) &= S_{2m - 1}^{*}(x) \\&= \left[ S_{2m - 3}^{*}(p_m x) \right]^2 S_{2m - 3}^{*}((1 - 4p_m)x) \\&\quad \times \left[ S_{2m - 3}^{*}(p_m x) \right]^2 \quad (3)\end{aligned}\tag{3.14}
$$

with the first- (or second-) order symmetrized decomposition²

$$
S _ { 1 } ^ { * } ( x ) = S ( x ) \equiv e ^ { ( x / 2 ) A _ { 1 } } e ^ { ( x / 2 ) A _ { 2 } } \cdots e ^ { ( x / 2 ) A _ { q } } \quad \times e ^ { x A _ { q } } e ^ { ( x / 2 ) A _ { q } } \cdots e ^ { ( x / 2 ) A _ { 2 } } e ^ { ( x / 2 ) A _ { q } }\tag{3.15}
$$

where the parameter $p _ { m }$ is the real solution of the equation'

$$
4 p _ { m } ^ { 2 m - 1 } + ( 1 - 4 p _ { m } ) ^ { 2 m - 1 } = 0 ,
$$

$$
\mathrm { i . e . , ~ } p _ { m } = ( 4 - 4 ^ { 1 / ( 2 m \mathrm { ~ - ~ } 1 ) } ) ^ { \mathrm { ~ - ~ } 1 } .\tag{3.16}
$$

In this scheme, we have

$$
\begin{array} { r } { \frac { 1 } { 3 } < p _ { m } < \frac { 1 } { 2 } \mathrm { a n d } | 1 - 4 p _ { m } | < \frac { 2 } { 3 } , } \end{array}\tag{3.17}
$$

for all m $( \geqslant 2 )$ . The parameters $\{ t _ { j } \}$ in (1.1) for the 2mthorder approximant are given by the product of some combinations of

$$
p _ { 2 } , p _ { 3 } , . . . , p _ { m } , 1 - 4 p _ { 2 } , 1 - 4 p _ { 3 } , . . . , 1 - 4 p _ { m } .\tag{3.18}
$$

Therefore, we have

$$
\lim _ { m \rightarrow \infty } t _ { j } = 0 ,\tag{3.19}
$$

for all j. Namely, each separation of the present decomposition becomes infinitesimally small for $m \to \infty$ and its structure is asymptotically fractal8,º as shown in Fig. 1. The convergence of $S _ { m } ^ { * } ( x )$ to the original exponential operator $F ( x )$ in the Banach space will be discussed elsewhere.

There are many other alternative kinds of decomposition of the form (1.1) with real numbers $\{ t _ { j } \}$ . For more general schemes, see Sec. VII.

## IV. COMPLEX DECOMPOSITION

It is much easier to find complex decomposition of the form (1.1), namely, with complex $\{ t _ { j } \}$ . For this purpose, only Theorem 1 is sufficient, because the decomposition condition (2.3) in Theorem 1 has always some complex solutions for any integer m.

![](images/page_2_image_25.jpg)

FIG. 1. Fractal structure of the decomposition $S _ { m } ^ { * } ( x )$ (a) S\*(x) = S\*(x); $t _ { 1 } = t _ { 1 1 } = \sharp p _ { 2 }$ $t_{5} = t_{7} = \frac{1}{2}(1 - 3p_{2})$ $t _ { \mathrm { s } } = 1 - 4 p _ { 2 } ,$ others $= p _ { 2 } ,$ (b) S(x) = S \*(x); the number j denotes $t _ { i } ; t _ { i } = t _ { 5 i } = \frac { 1 } { 2 } p _ { 2 } p _ { 3 } ,$ $t_{5}=t_{7}=t_{15}=t_{17}=t_{35}=t_{37}=t_{45}=t_{47}=\frac{1}{2}(1-3p_{2})p_{3},t_{6}=t_{16}=t_{36}$ $t_{46} = (1 - 4p_2)p_3, \quad t_{21} = t_{31} = \frac{1}{2}p_2(1 - 3p_3), \quad t_{22} = t_{23} = t_{24} = t_{28}$ $t_{23} = t_{30} = p_{2}(1 - 4p_{3}), \quad t_{25} = t_{27} = \left\{ (1 - 3p_{2})(1 - 4p_{3}), \quad t_{26} = (1 - 3p_{2})(1 - 4p_{3}) \right\}$ $= \left( 1 - 4 p _ { 2 } \right) \left( 1 - 4 p _ { 3 } \right)$ others =P2P3; where P2 = 0.414 490 771 794 375 $7 \ldots ,$ and $p _ { 3 } = 0 . 3 7 3$ 065 827 733 272 8... . Furthermore, all $t _ { j }$ are measured in the unit of x.

For example, we consider the case $r = 2 .$ Then, the third-order decomposition is given' by

$$
\mathcal { Q } _ { 3 } ^ { \{ 2 \} } ( x ) = S ( a x ) S ( \overline { { a } } x ) ,\tag{4.1}
$$

with $S ( x )$ defined by (3.15) and with $\vec { a } = 1 - a = \mathrm { c o m p l e }$ X conjugate of $a ,$ where a and ā are the solutions of the equation

$$
3a^{2}-3a+1=0,\quad \mathrm{i.e.,} \quad a=(3\pm\sqrt{3}i)/6.\tag{4.2}
$$

More explicitly we haveo

$$
Q _ { 3 } ^ { ( 2 ) } ( x ) = e ^ { ( a / 2 ) x A } e ^ { a x B } e ^ { ( 1 / 2 ) x A } e ^ { \bar { a } x B } e ^ { ( 1 / 2 ) \bar { a } x A }\tag{4.3}
$$

for $q = 2$ in (3.15).

In general, the mth order approximant is recursively given by

$$
Q _ { m } ^ { ( 2 ) } ( x ) = Q _ { m - 1 } ^ { ( 2 ) } ( p _ { m } x ) Q _ { m - 1 } ^ { ( 2 ) } ( ( 1 - p _ { m } ) x ) ,\tag{4.4}
$$

with the decomposition condition

$$
p _ { m } ^ { m } + ( 1 - p _ { m } ) ^ { m } = 0 , \quad \mathrm { i . e . , } \quad p _ { m } = ( 1 + \exp ( i \pi / m ) ) ^ { - 1 } .\tag{4.5}
$$

Clearly, we have $\textstyle { \frac { 1 } { 2 } } < | p _ { m } | < 1$ for $m \geqslant 2$ and

$$
\operatorname* { l i m } _ { m \to \infty } p _ { m } = { \textstyle { \frac { 1 } { 2 } } } .\tag{4.6}
$$

It is easy to find many other series of complex decomposition. The fractal structure of complex decomposition is much simpler than that of real decomposition.

## V. NONEXISTENCE THEOREM OF POSITIVE DECOMPOSITION

In Sec. III, we have given explicitly real decomposition of the form (1.1) using the recursion formula (Theorem 1). Now arises a question whether there exists positive real decomposition (i.e., all $t _ { J }   >   0 )$ or not. To answer this question, we have the following theorem.

Theorem 3 (nonexistence theorem of positive decomposition): There exists no decomposition of the form

$$
e ^ { x ( A + B ) } = e ^ { t _ { 1 } A } e ^ { t _ { 2 } B } e ^ { t _ { 3 } A } e ^ { t _ { 4 } B } \cdots e ^ { t _ { M } A } + O ( x ^ { m + 1 } ) ,\tag{5.1}
$$

with all $t _ { j }$ positive and finite M for $m \geqslant 3$ and for noncommutable operators A and B.

As a corollary of this theorem, we have the proposition that there exists no real positive decomposition

$$
\exp \left( x \sum_{j = 1}^{q} A_{j} \right) = e^{t_{11} A_{1}} e^{t_{12} A_{2}} \cdots e^{t_{1q} A_{q}} \cdots + O(x^{m + 1}),\tag{5.2}
$$

for m≥3 and for a finite number of products, where $q \geqslant 2$

In order to prove Theorem 3, it is sufficient to prove it for $m = 3$ . For this purpose, it is convenient to note that the term $A B ^ { 2 }$ in the product

$$
e^{x t_{1} y} e^{x s_{1} B} e^{x t_{1} A} e^{x s_{2} B} \cdots e^{x s_{p} B} e^{x t_{p} A}\tag{5.3}
$$

is, in general, given by

$$
\frac{x^{3}}{2}\sum_{j = 0}^{p - 1}t_{j}\left( \sum_{k = j + 1}^{p}s_{k} \right)^{2}AB^{2}.\tag{5.4}
$$

This has to be equal to $A B ^ { 2 } / 6 ,$ namely, we have

$$
\sum_{j = 0}^{p - 1} t_j \left( \sum_{k = j + 1}^{p} s_k \right)^2 = \frac{1}{3}\tag{5.5}
$$

Similarly, for the term $B A ^ { 2 }$ we have

$$
\sum _ { j = 1 } ^ { p } s _ { j } ( \sum _ { k = j } ^ { p } t _ { k } ) ^ { 2 } = \frac { 1 } { 3 } .\tag{5.6}
$$

The existence of positive solutions $\{ t _ { j } \}$ and $\{ s _ { j } \}$ of Eqs. (5.5) and (5.6) is only the necessary condition for the existence of real positive decomposition. However, it is sufficient for the proof of Theorem 3, to show that there exist no positive real solutions in (5.5) and (5.6) under the conditions that

$$
\sum_{j = 0}^{p} t_{j} = 1 \text { and } \sum_{j = 1}^{p} s_{j} = 1.\tag{5.7}
$$

At a glance, it looks very difficult to prove the above statement. However, it is found to be possible by changing the variables $\{ t _ { j } \}$ as

$$
x _ { j } = \sqrt { s _ { j } }   \sum _ { k = j } ^ { p } t _ { k } ,\tag{5.8}
$$

for positive $s _ { j }$ . Then, Eq. (5.6) is transformed into the hypersphere

$$
x_{1}^{2}+x_{2}^{2}+\cdots+x_{p}^{2}=(1/\sqrt{3})^{2}.\tag{5.9}
$$

On the other hand, Eq. (5.5) is rewritten as

$$
\sum _ { j = 1 } ^ { p - 1 } \left\{ 1 - \left( \sum _ { k = j + 1 } ^ { p } s _ { k } \right) ^ { 2 } \right\} t _ { j } + t _ { p } = \frac { 2 } { 3 } ,
$$

using the relation $t _ { 0 } = 1 - t _ { 1 } - t _ { 2 } - \cdots - t _ { p }$ . This is again transformed into the following hyperplane:

(5.10)

$$
\sum_{j = 1}^{p} a_{j}x_{j} = \frac{2}{3}\tag{5.11}
$$

where

$$
a _ { j } = \sqrt { s _ { j } } \left( s _ { j } + 2 \sum _ { k = j + 1 } ^ { p } s _ { k } \right) \mathrm { a n d } a _ { p } = s _ { p } ^ { 3 / 2 }\tag{5.12}
$$

The distance R between this hyperplane and the origin in the p-dimensional space is given by

$$
R = \frac{2}{3} f \left( \left\{ s_j \right\} \right)^{-1/2},\tag{5.13}
$$

where

$$
f ( \{ s _ { j } \} ) = \sum _ { j = 1 } ^ { p } a _ { j } ^ { 2 } .\tag{5.14}
$$

If $R   \leq   1 / { \sqrt { 3 } } ,$ , there exists a real solution of the simultaneous equations (5.5) and (5.6). Otherwise, there exists no positive real solution. Now we try to find the maximum of the function $f ( \{ s _ { j } \} )$ in the range $0   <   s _ { i } < 1$ . If the maximum of $f ( \{ s _ { j } \} )$ is less than $4 / 3 ,$ then there exists no positive real solution of (5.5) and (5.6).

Now the maximum o $f _ { f } ( \{ s _ { j } \} )$ is shown to be given at the symmetric point

$$
s_{1}=s_{2}=s_{3}=\cdots=s_{p}=1/p.\tag{5.15}
$$

For the derivation of this statement, see the Appendix. Thus the maximum of $f ( \{ s _ { j } \} )$ is given by

$$
f_{\max}=f\left(\left\{\frac{1}{p}\right\}\right)=\frac{1}{3}\left(4-\frac{1}{p^{2}}\right).\tag{5.16}
$$

Clearly, we have

$$
f _ { \mathrm { m a x } } < \frac { 4 } { 3 } ,\tag{5.17}
$$

for finite p. Therefore, we finally arrive at the conclusion that there exists no real positive decomposition of the form (1.1) for $m = 3 .$ This yields immediately Theorem 3 for $m \geqslant 3$

It is interesting to remark that the function $f ( \{ s _ { j } \} )$ has the maximum value $4 / 3$ only in the limit $p   \to   \infty$ as seen from (5.16) In fact, the ordinary Trotter formula1,12

$$
e^{x(A + B)} = \lim_{n \to \infty} \left( e^{xA / n} e^{xB / n} \right)^n\tag{5.18}
$$

may be one of the examples for (5.1) with $p   \to   \infty$ and $m   \to   \infty$

From Theorem 3, we may conclude that our previous fractal decomposition with negative $\{ t _ { j } \}$ in Sec. III is substantial in its character. A physical meaning of this decomposition will be discussed later. Clearly, from our construction scheme of decomposition, there are many alternative schemes that always include some negative $\{ t _ { j } \dot { j }$ . In Sec. XI and Sec. XII, we discuss a systematic general scheme of decomposition.

## VI. TIME-ORDERING METHOD AND SUM RULES

According to Feynman's path integral method, for example, the density matrix of a quatum system is represented by some time-ordered exponential.13.14 More explicitly we frequently use the well-known formula

$$
e ^ { \beta ( A + B ) } = P \left[ \exp \left( \int _ { 0 } ^ { \beta } A ( \tau ) d \tau \right) \exp \left( \int _ { 0 } ^ { \beta } B ( \tau ) d \tau \right) \right]\tag{6.1}
$$

using the time-ordering operator $P ,$ namely,

$$
P ( A ( \tau _ { 1 } ) B ( \tau _ { 2 } ) ) = \left\{ \begin{aligned} A ( \tau _ { 1 } ) B ( \tau _ { 2 } ) , \quad \mathrm { f o r } \tau _ { 1 } < \tau _ { 2 } , \\ B ( \tau _ { 2 } ) A ( \tau _ { 1 } ) , \quad \mathrm { f o r } \tau _ { 2 } < \tau _ { 1 } . \end{aligned} \right.\tag{6.2}
$$

In the present section, we give an inverse formulation, namely, we propose here a general method to express the product of exponential operators (5.1) as a single exponential operator using the time-ordering method.

Now, we consider first the following product

$$
E(A,B)=e^{t_{1}A}e^{t_{2}B}e^{t_{3}A}e^{t_{4}B}\cdots e^{t_{M}A}\tag{6.3}
$$

Our purpose is to find any order of E (A,B) as efficiently as possible. A primitive and tedious method may be to expand each exponential operator into a power series of A or B and to collect the required terms. This is too complicated and not practical even for small M.

Our proposal is the following. First we write $t _ { j } A$ as $A _ { j }$ and $t _ { k } B$ as $B _ { k }$ . We introduce a time-ordering operator P as

$$
P ( A _ { j } A _ { k } ) = \left\{ \begin{aligned} { A _ { j } A _ { k } , \quad \mathrm { f o r } j < k , } \\ { A _ { k } A _ { j } , \quad \mathrm { f o r } k < j , } \end{aligned} \right.\tag{6.4}
$$

$$
P ( A _ { j } B _ { k } ) = \left\{ \begin{aligned} { A _ { j } B _ { k } , \quad \mathrm { f o r } j < k , } \\ { B _ { k } A _ { j } , \quad \mathrm { f o r } k < j , } \end{aligned} \right.\tag{6.5}
$$

etc., as usual. Then we may express E(A,B) as

$$
\begin{align*}E(A, B) &= P\Biggl( \exp\Biggl( \sum_{j = 1}^{\infty} A_{2j - 1} + \sum_{k = 1}^{\infty} B_{2k} \Biggr) \Biggr) \\&= P\Biggl( \exp\Biggl( \sum_{j = 1}^{\infty} A_{2j - 1} \Biggr) \exp\Biggl( \sum_{k = 1}^{\infty} B_{2k} \Biggr) \Biggr) \\&= \sum_{n = 0}^{\infty} \sum_{m = 0}^{\infty} \frac{1}{n!m!} P\Biggl( \Biggl( \sum_{j = 1}^{\infty} A_{2j - 1} \Biggr)^n \Biggl( \sum_{k = 1}^{\infty} B_{2k} \Biggr)^m \Biggr) .\end{align*}\tag{6.6}
$$

After the operation of the time-ordering P, we replace $A _ { j }$ and $B _ { k }$ by $t _ { i } A$ and $t _ { k } B ,$ respectively.

For example, the third-order term of the form $A ^ { 3 }$ is obtained as

$$
\frac{1}{3!} P \left( \sum_{j=1}^{\infty} A_{2j-1} \right)^3 = \frac{1}{3!} \left( \sum_{j=1}^{\infty} t_{2j-1} \right)^3 A^3,\tag{6.7}
$$

as it should be. The terms $AB^{2},B^{2}A$ , and BAB are obtained as

$$
\begin{align*}\frac{1}{1!2!} & P\Biggl( \Biggl( \sum_{j \; = \; 1}^{\infty} A_{2j \; - \; 1} \Biggr) \Biggl( \sum_{k \; = \; 1}^{\infty} B_{2k} \Biggr)^2 \Biggr) \\& = \frac{1}{2} \sum_{j \; = \; 1}^{\infty} t_{2j \; - \; 1} \Biggl( \sum_{k \; \geqslant j} t_{2k} \Biggr)^2 AB^2 \\& \quad + \frac{1}{2} \sum_{j \; = \; 2}^{\infty} t_{2j \; - \; 1} \Biggl( \sum_{k \leqslant j \; - \; 1}^{\infty} t_{2k} \Biggr)^2 B^2 A^2 \\& \quad + \frac{1}{2} \sum_{k \; + \; 1 \leqslant j \leqslant i} t_{2k}   t_{2j \; - \; 1}   t_{2i} BAB.\end{align*}\tag{6.8}
$$

This expression has already been used in deriving the relations (5.5). The terms $A^{2}B,BA^{2}$ , and ABA are given similarly. Clearly, from (6.8) we obtain the following sum rule, namely, the sum of the coefficients of $AB^{2},B^{2}A,$ and BAB is given by

$$
\frac{1}{2} \left( \sum_{j = 1}^{n} t_{2j - 1} \right) \left( \sum_{k = 1}^{n} t_{2k} \right)^2\tag{6.9}
$$

This kind of sum rule is very convenient in practical calculations, since the number of equations for the decomposition condition is highly reduced using this sum rule. For example, we consider the symmetric decomposition

$$
\begin{array} { r } { { e ^ { x ( A \; + \; B ) } = e ^ { p x A } e ^ { q x B } e ^ { r x A } e ^ { s x B } } } \\ { { \times   \quad \times   e ^ { r x A } e ^ { q x B } e ^ { p x A } + O ( x ^ { 4 } )   . } } \end{array}\tag{6.10}
$$

The whole correct third-order term of exp(x(A + B)) is given by

$$
\begin{aligned}(x^{3} / 6)(A+B)^{3} &=(x^{3} / 6)(A^{3}+A^{2} B+B A^{2}+A B A \\& \quad +A B^{2}+B^{2} A+B A B+B^{3}) .\end{aligned}\tag{6.11}
$$

On the other hand, the third-order term of the right-hand side of Eq. (6.10) is expressed in the form

$$
\begin{aligned}&\left(x^{3} / 6\right)\left(A^{3}+B^{3}\right)+\left\{\alpha\left(AB^{2}+B^{2} A\right)+\beta B A B\right. \\&\left.\quad+\gamma\left(A^{2} B+B A^{2}\right)+\delta A B A\right\} x^{3},\end{aligned}\tag{6.12}
$$

using the symmetry property of (6.10) with respect to transposition. Furthermore the above sum rule yields

$$
2\alpha + \beta = \frac{1}{2}  and  2\gamma + \delta = \frac{1}{2}.\tag{6.13}
$$

Consequently, if only the two coefficients are determined correctly, then all the other terms become automatically correct in the third order.

This reduction of the number of equations for decomposition conditions based on the sum rule has been one of our clues to try to find the proof of Theorem 3 (the nonexistence theorem of positive decomposition) in Sec. V. In fact, Eqs. (5.5) and (5.6) are now found to be necessary and sufficient conditions for the third-order symmetric decomposition, if we apply the above sum rule to this problem.

## VII. GENERAL CRITERIONS OF DECOMPOSITIONS

In this section, we study a general scheme of decomposition of the form

$$
\exp \left( x \sum_{k = 1}^{q} A_{k} \right) = \prod_{j = 1}^{p} \prod_{k = 1}^{q} \exp \left( t_{jk} A_{k} \right) + O(x^{m + 1})\tag{7.1}
$$

with the conditions

$$
\sum_{j = 1}^{p} t_{jk} = x, \quad  for all   k.\tag{7.2}
$$

First, we write $t _ { j k } A _ { k }$ as

$$
t _ { j k } A _ { k } = A _ { j k } .\tag{7.3}
$$

We introduce here the following time-ordering operator P:

$$
P ( \mathcal { A } _ { j k } \mathcal { A } _ { i r } ) = \left\{ \begin{aligned} { \mathcal { A } _ { j k } \mathcal { A } _ { i r } , \quad } & { { } \mathrm { f o r } j   <   i \mathrm { o r } } \\ { \quad } & { { } \mathrm { f o r } j   =   i , k   <   r , } \\ { \mathcal { A } _ { i r } \mathcal { A } _ { j k } , \quad } & { { } \mathrm { f o r } i   <   j \mathrm { o r } } \\ { \quad } & { { } \mathrm { f o r } i   =   j , r   <   k . } \end{aligned} \right.\tag{7.4}
$$

Then, we have

$$
\prod_{j = 1}^{p} \prod_{k = 1}^{q} \exp(t_{jk} A_k) = P \exp(\sum_{j,k} A_{jk}) \\= P \left( \prod_{k = 1}^{q} \exp(\sum_{j = 1}^{p} A_{jk}) \right).\tag{7.5}
$$

We obtain the following sum rules, namely, the sum of the coefficients of all the products of $p_{1}A_{1}^{'}s,p_{2}A_{2}^{'}s,\ldots,$ and $p _ { q }$ $A _ { q } \gamma _ { s }$ is given by

$$
\frac{m!}{p_{1}!p_{2}!\cdots p_{q}!}\times\frac{1}{m!}=\frac{1}{p_{1}!p_{2}!\cdots p_{q}!},\tag{7.6}
$$

$$
p _ { 1 } + p _ { 2 } + \cdots + p _ { q } = m .\tag{7.7}
$$

where

Some explicit applications of the present general scheme together with the sum rule will be given explicitly in the following. The coefficient of the product $A _ { k } A _ { l } A _ { n }$ , for example, is given by

$$
\sum _ { j = 1 } ^ { p } \sum _ { i = j } ^ { p } \sum _ { s = i } ^ { p } t _ { j k } t _ { i l } t _ { s p } = \frac { x ^ { 3 } } { 6 } ,\tag{7.8}
$$

for $l \neq k$ and $l \neq n$ . The coefficient of the product $A _ { k } A _ { l }$ is given by

$$
\sum _ { i = 1 } ^ { p } \left( \sum _ { j < i } t _ { j k } \right) ^ { 2 } t _ { i l } = \frac { x ^ { 3 } } { 3 } ,\tag{7.9}
$$

for k ≠1.

Next, we study the mth term of (5.1). It is given by

$$
\begin{align*}\frac{1}{m!} & P\Biggl( \sum_{j=1}^{m} A_{jj-1} + \sum_{k=1}^{m} B_{2k} \Biggr)^m \\& = \frac{1}{m!} P \sum_{k=m}^{m} m C_n \Biggl( \sum_{j=1}^{m} A_{2j-1} \Biggr)^n \Biggl( \sum_{k=1}^{m} B_{2k} \Biggr)^{m-n} \\& = \frac{1}{m!} \Biggl[ \Biggl( \sum_{j} t_{2j-1} \Biggr)^m A^m + m \sum_{j} t_{2j-1} \Biggl( \sum_{k,l} t_{2k} \Biggr)^{m-1} AB^{m-1} + m \sum_{j} t_{2j-1} \Biggl( \sum_{k,l-1} t_{2k} \Biggr)^{m-1} \\& \quad \times B^{m-1} A^{j} + \cdots + \sum_{j} \Biggl( \sum_{k,l-1} t_{2k} \Biggr)^{m-r} t_{2j-1} \Biggl( \sum_{l} t_{2k} \Biggr)^{r-1} B^{m-r} AB^{r-1} \\& \quad + \cdots + \sum_{j} \Biggl( \sum_{k,l_{2k-1}} t_{2k} \Biggr)^r t_{2j_{2k-1}} \Biggl( \sum_{l_{2k},k \leq j_{2j-1}} t_{2k} \Biggr)^r t_{2j_{2j-1}} \Biggl( \sum_{l_{2k},k \leq j_{2k-1}} t_{2k} \Biggr)^r t_{2j_{2k-1}} \cdots \times B^{r_1} AB^{r_2} AB^{r_1} \cdots + \cdots \Biggr] .\end{align*}\tag{7.10}
$$

In particular, the symmetric decomposition of the form

$$
e ^ { t _ { i } x . A } e ^ { s _ { i } x B } e ^ { t _ { i } x A } e ^ { s _ { i } x B } e ^ { t _ { i } x A } \cdots e ^ { s _ { p } x B } e ^ { t _ { p } x A } ,\tag{7.11}
$$

with the symmetry condition

$$
t _ { 0 } = t _ { p } , t _ { 1 } = t _ { p - 1 } , \ldots , s _ { 1 } = s _ { p } , s _ { 2 } = s _ { p - 1 } , \ldots .\tag{7.12}
$$

Then, the third-order decomposition condition is given by

$$
\sum_{k = 0}^{p} t_{k} \left( \sum_{j = k} s_{j} \right)^{2} = \frac{1}{3}\tag{7.13}
$$

$$
\sum_{k = 1}^{p} s_{k} \left( \sum_{j = k + 1}^{} t_{j} \right)^{2} = \frac{1}{3}
$$

and

$$
\sum_{j = 0}^{p} t_{j} = 1 \text { and } \sum_{j = 1}^{p} s_{j} = 1.\tag{7.14}
$$

with

(7.15)

This also gives the fourth-order decomposition condition owing to Theorem 2.

It is easily seen that the fractal decomposition in Sec. III is a special solution of (7.13) and (7.14). Consequently, there are many other real solutions in (7.13) and (7.14) with (7.15), as will be seen easily from the consideration on the number of equations of decomposition condition and the number of parameters. In fact, the former is four (cf. the condition on the second order is satisfied automatically owing to the symmetry property and the sum rule), and the latter is $( p + 1 )$ . Thus the relevant parameters $\{ t _ { j } , s _ { j } \}$ are redundant, when $p \geqslant 4$ The symmetric decomposition of third order for $p = 3$ (namely, $M = 2 p + 1 = 7 )$ is unique, as is seen from (3.8). This is the reason why the decomposition $S _ { 3 } \left( x \right)$ in (3.8) could be found first in the present study, and why there exists no real symmetric decomposition in the form (7.11) with (7.12) for $p   <   2$ (namely for $M { \leqslant } 5 )$

## VIII. FRACTAL-TEMPERATURE QUANTUM MONTE CARLO METHOD

The partition function

$$
Z = \mathrm{Tr} \exp( - \beta \mathcal{H} )\tag{8.1}
$$

may be calculated using the fractal decomposition introduced in the present paper. Now, we put

$$
\mathcal { H } = \mathcal { H } _ { 0 } + V .\tag{8.2}
$$

Then we have

$$
\begin{array} { r l } { Z = \mathrm { T r }   e ^ { - \beta ( \mathcal { N } _ { 0 } + V ) } } & { { } } \\ { = \underset { n \rightarrow \infty } { \operatorname* { l i m } }   [ { S _ { m } } ^ { * } ( - \beta / n ) ] ^ { n } , } \end{array}\tag{8.3}
$$

where $S _ { m } ^ { * } ( x )$ is given by (3.14) with the fractal numbers $\{ p _ { m } \}$ given in (3.16).

This new scheme is much better than the ordinary second-order decomposition

$$
Z _ { 2 } = \mathrm { T r } \left[ e ^ { - ( \beta / 2 n _ { 0 } ) \mathcal { N } _ { 0 } } e ^ { - ( \beta / n _ { 0 } ) \mathcal { V } _ { 0 } } e ^ { - ( \beta / 2 n _ { 0 } ) \mathcal { N } _ { 0 } } \right] ^ { n _ { 0 } } ,\tag{8.4}
$$

when the criterion

$$
(5\beta / n)^{2m - 2} \ll 1\tag{8.5}
$$

is satisfied. This criterion is easily derived from the following consideration. The number of products of partial Boltzmann factors $e ^ { i _ { r } A }$ and $e ^ { t , B }$ is estimated to be $( 2 \cdot 5 ^ { m - 1 } + 1 ) n$ for the approximant $S _ { 2 m } ^ { * } ( x )$ in (3.14). On the other hand, it is given by $2 n _ { 0 } + 1$ for the ordinary symmetric decomposition (8.4). For the same number of products, the accuracy of our new scheme is seen to be of the order of $\beta ^ { 2 m + 1 } / n ^ { 2 m }$ from the formula

$$
\begin{array} { r l } {  { \exp \left[ - \beta ( \mathcal { H } _ { 0 } + V ) \right] = \left[ S _ { 2 m } ^ { * } \left( - \beta / n \right) \right] ^ { n } } } \\ & { \quad + O ( \beta ^ { 2 m + 1 } / n ^ { 2 m } ) . } \end{array}\tag{8.6}
$$

The accuracy of the ordinary symmetric decomposition is of the order of

$$
O ( \beta ^ { 3 } / n _ { 0 } ^ { 2 } ) = O ( \beta ^ { 3 } / ( n ^ { 2 } \cdot 5 ^ { 2 m - 2 } ) ) .\tag{8.7}
$$

Thus our criterion is given by

$$
\beta ^ { 2 m + 1 } / n ^ { 2 m } \leqslant \beta ^ { 3 } / ( n ^ { 2 } \cdot 5 ^ { 2 m - 2 } ) .\tag{8.8}
$$

This yields (8.5). Therefore, our new scheme is extremely efficient when

$$
\beta   < n / 5 .\tag{8.9}
$$

Some explicit applications of the present fractal-temperature quantum Monte Carlo method will be reported elsewhere.

## IX. FRACTAL-TIME MONTE CARLO METHOD

It is also possible to formulate the following fractal-time path integral

$$
\langle a | e ^ { i t \cdot \vec { r } / \hbar } | b \rangle = \operatorname* { l i m } _ { n \to \infty } \langle a | [ S _ { m } ^ { * } ( i t / n \hbar ) ] ^ { n } | b \rangle\tag{9.1}
$$

with $S _ { m } ^ { * } ( x )$ in (3.14). This representation of the matrix elements of the transition operator $e ^ { i t  方  / \hbar }$ is very convenient from a practical point of view. In particular, this may be useful in studying nuclear and chemical reactions.

## X. A NEW EFFICIENT METHOD OF QUANTUM MONTE CARLO SIMULATIONS—COMBINATION OF THE FRACTAL DECOMPOSITION AND SORELLA'S METHOD

It is quite interesting to combine the present new scheme with Sorella's method.'5-19 We propose here a new idea to apply the present fractal scheme to Sorella's method, namely, that we make use of the fractal decomposition in constructing Sorella's orthogonalization scheme. This new idea will be applied to two-dimensional frustrated quantum systems in order to clarify the mechanism of the high. $\cdot T _ { c }$ superconductivity.

## XI. SUMMARY AND DISCUSSION

In the present paper, we have formulated a general scheme of fractal decomposition of the form (1.1). This has a fractal structure in our recursive scheme. It has been proven that some of the decomposition parameters $( t _ { j } )$ should be negative (nonexistence theorem of positive decomposition). This fact seems to have a very instructive physical meaning. That $\mathbf { i s } ,$ the negative time may be interpreted to express quantum fluctuation of holes or antiparticles. This new interpretation will be discussed in more detail elsewhere.

Hopefully, the present new fractal scheme of higherorder decomposition of exponential operators will be applied to many quantum many-body systems in near future.

## ACKNOWLEDGMENTS

The present author would like to thank Professor A. D. Bandrauk for informing his result (43) with (42) prior to publication, and also thank Dr. M. Takasu, N. Ito, N. Kawashima, N. Hatano, T. Kawarabayashi, and Y. Nonomura for useful discussions, particularly concerning some possible applications of the present new scheme to quantum Monte Carlo simulations.

This study is partially financed by the Scientific Research Fund of the Ministry of Education, Science and Culture.

## APPENDIX: DERIVATION OF THE MAXIMUM POINT (5.15)

From the expression (5.14) of the function $f ( \{ s _ { j } \} )$ , we have the derivative of it with respect to the variable $s _ { 2 }$ as

$$
\begin{aligned}\frac{\partial f}{\partial s_{2}} = & - \left( 1 + s_{2} + b_{2} \right)^{2} + 2\left\{ 1 - \left( s_{2} + b_{2} \right)^{2} \right\} \\& + \left( s_{2} + 2b_{3} \right)^{2} + 2s_{2}\left( s_{2} + 2b_{3} \right) = 0,\end{aligned}\tag{A1}
$$

where $b _ { 3 }$ is defned as

$$
b _ { j } = s _ { j } + s _ { j + 1 } + \cdots + s _ { p } .\tag{A2}
$$

The solution of (A1) with respect to $s _ { 2 }$ is given by

$$
s _ { 2 } = \frac { 1 } { 2 } ( 1 - b _ { 3 } ) .\tag{A3}
$$

By combining (A3) with (5.7), we obtain

$$
s_{1} = s_{2} = \frac{1}{2}(1 - b_{3}).\tag{A4}
$$

Similarly, we have

$$
\begin{aligned}\frac{\partial f}{\partial s_{3}} = 1 - 2b_{2} - 3b_{2}^{2} + 4s_{2}(s_{2} + 2b_{3}) \\+ (3s_{3} + 2b_{4})(s_{3} + 2b_{4}) = 0.\end{aligned}
$$

Using (A4) and (A5), we obtain

(A5)

$$
s_{1} = s_{2} = s_{3} = \frac{1}{3}(1 - b_{4}).\tag{A6}
$$

Successively, from the maximal condition

$$
\frac { \partial f } { \partial s _ { k } } = 0 ,\tag{A7}
$$

We obtain

$$
s _ { 1 } = s _ { 2 } = s _ { 3 } = \cdots = s _ { k } = ( 1 / k ) ( 1 - b _ { k + 1 } ) .\tag{A8}
$$

Finally, we arrive at the conclusion (5.15). It is also shown easily from the above expressions of derivatives $\{ \partial f / \partial s _ { j } \}$ that the symmetric point $s_{1}=s_{2}=s_{3}=\cdots=s_{p}=1/p$ is the maximum one of the function $f ( \{ s _ { j } \} )$ in the first zone $( s _ { j } > 0 )$ of the p-dimensional hyperspace.

'M. Suzuki, Phys. Lett. A 146, 319 (1990).

2M. Suzuki, J. Math. Phys. 26, 601 (1985).

M. Suzuki, Phys. Lett. A 113, 299 (1985).

\*M. Suzuki, J. Stat. Phys. 43, 883 (1986) and references cited therein.

M. Suzuki, in Ouantum Monte Carlo in Equilibrium and Nonequilibrium Systemns, edited by M. Suzuki (Springer-Verlag, Berlin, 1987), and references cited therein.

\*M. Suzuki, Prog. Theor. Phys. 56, 1454 (1976).

'M. Suzuki, S. Miyashita, and A. Kuroda, Prog. Theor. Phys. 58, 1377 (1977).

8 M. Suzuki, Prog. Theor. Phys. 71, 1397 (1984).

9B. B. Mandelbrot, The Fractal Geometry of Nature (Freeman, San Francisco, 1982).

1º A. D. Bandrauk (private communication, 1989).

" H. F. Trotter, Proc. Am. Math. Phys. 10, 545 (1959).

12M. Suzuki, Commun. Math. Phys. 51, 183 (1976).

13 R. P. Feynman and A. R. Hibbs, Quantum Mechanics and Path Integrals (McGraw-Hill, New York, 1965).

14 R. Kubo, J. Phys. Soc. Jpn. 17, 1100 (1962).

15 S. Sorella, E. Tosatti, S. Baroni, R. Car, and M. Parrinello, Int. J. Mod. Phys. B 2, 993 (1988). The author was informed by the referee that the need to orthogonalize the rows or columns of the matrices that arise in low-temperature quantum Monte Carlo simulations was pointed out first by G. Sugiyama and S. E. Koonin in Ann. Phys. 168, 1 (1986).

S. Sorella, S. Baroni, R. Car, and M. Parrinello, Europhys. Lett. 8, 663 (1989).

I7S. R. White, D.J. Scalapino, R. L. Sugar, E. Y. Loh, J. E. Gubernatis, and R. T. Scaletter, Phys. Rev. B 40, 506 (1989).

19 K. Kuroki, Master's thesis, Dept. of Physics, Univ. of Tokyo (1990).

1\* M. Imada and Y. Hatsugai, J. Phys. Soc. Jpn. 58, 3752 (1989).