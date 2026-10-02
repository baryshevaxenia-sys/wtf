# Conjecture 4: the range of the strongly separable split count $s(P)$

**Sources and conventions.** "Theorem 1.3/1.4" refer to `sylvester_radon.pdf`, "Theorem 2.17" to
`random_permutations_lectures_1-4.pdf`. The cyclic-collision results for $N=d+3$ (the identity
$T_2=2s$ and formula (1) of the request) are used as established; they are proved in
`C3_REPORT.md` (§6, §8). The file `wtf.pdf` mentioned in the request was not among the uploaded
files. Its role (machine-checked evidence for the two endpoint step sets) is taken over by
`RequestProject/FivePointBridge.lean` and `RequestProject/StrongSplits.lean`. Both build without
`sorry`.

**What is proved in prose and what is checked by machine.** All structural theorems below
(§4–§6, §8, §9) are proved in prose, by conceptual arguments. Exhaustive enumeration is never
used as a proof of them. The Lean file `RequestProject/StrongSplits.lean` contains only *exact
finite computations over the integers*:

- the values of $s$ for the explicit configurations used in this report;
- the Gale diagrams of the two endpoint step sets;
- the 768 normalized simple allowable sequences on five elements and their values of $s$;
- nineteen explicit integer realizations.

These are used as independent consistency checks, for the explicit examples, and for one
statement that is purely finite: the converse realizability statement in C4-C.

---

## 1. Executive verdict

| Claim | Verdict |
|---|---|
| **C4-A** $s(P)\le 2$ for simple $P$ with $N\ge5$ | **True.** It even holds for every *abstract* simple allowable sequence, realizable or not (Theorem 6.1). For $N=4$ it fails: $s=3$ always. |
| **C4-B** $s(P)\ge1$ for realizable simple $P$, $N=5$ | **True** (Theorem 5.6). The proof is conceptual, order type by order type. The convex-pentagon case reduces to the fact that a cyclic sequence of five *ear areas* with distinct neighbours has a strict local minimum. |
| **C4-C** the $s=0$ sequences are non-stretchable; stretchable $\Rightarrow s\in\{1,2\}$ | **True.** Non-stretchability follows from C4-B. Exactly 8 of the 768 normalized words have $s=0$ (machine count). They form **one** class under cyclic shift and reversal, and are closed under mirror relabelling. They are **not** closed under commutation moves, so "the eight periodic words" is invariant only under shift, reversal and relabelling. They are the circular sequence of the Goodman–Pollack "bad pentagon" and its mirror image. Conversely, every word with $s\ge1$ is realizable (finite check by explicit realizations). |
| **C4-D** $s=1$ and $s=2$ attained at $N=5$ | **True**, with explicit integer examples in every order type where the value can occur, plus direct geometric criteria. |
| Five-point theorem | $\mathbb P(\text{convex})=\frac16+\frac1{12}\mathbb E s\in[\frac14,\frac13]$, for exchangeable bridges and for exchangeable walks. Both endpoints are attained exactly, by step set **A** ($s=2$, probability $1/3$) and step set **B** ($s=1$, probability $1/4$). |
| $N\ge6$ | $s\in\{0,1,2\}$, and all three values are realizable for every $N\ge6$. The interval $[1-\frac N{(N-2)!},\,1-\frac N{(N-2)!}+\frac4{(N-1)!}]$ is sharp at both ends. There is **no** extra positive term in the lower bound for $N\ge6$. |
| Gaussian self-duality | Both statements are **true** (Proposition 9.1). They follow at once from the rotation invariance used in the Gaussian Gale construction (Theorem 1.3; Baryshnikov–Vitale). |

---

## 2. Literature search and novelty assessment

**Access.** Live searches were run against the arXiv API, OpenAlex and Semantic Scholar. The
search strings were those listed in the request, together with variants: "allowable sequence"
+ "block", "reduced word" + "longest element" + "bipartite inversion", "circular sequence" +
"point configuration", "strongly separable", "linear separations" + "planar point set",
"sweep" + "allowable graph". In addition, the 113 works that OpenAlex lists as citing
Goodman–Pollack (1980) were screened by title and abstract.

**MathSciNet and zbMATH were not accessible**, and neither was the full text of Goodman–Pollack
(1980) or of the *Oriented Matroids* book. Every novelty statement below is therefore
**provisional**.

| Source | Content relevant here | Bearing on $s(P)$ |
|---|---|---|
| J. E. Goodman, R. Pollack, *On the combinatorial classification of nondegenerate configurations in the plane*, J. Combin. Theory Ser. A **29** (1980) 220–235, doi:10.1016/0097-3165(80)90011-4 | Introduces allowable sequences (circular sequences) of planar point sets. Exhibits a simple allowable sequence on 5 elements, the "bad pentagon", that is not realizable. (Full text not accessed; content taken from the secondary sources below.) | **Related.** It supplies the non-realizable 5-element sequence, which turns out to be exactly our $s=0$ class (§5.6). It does not consider block transpositions or $s$. |
| J. E. Goodman, R. Pollack, *Proof of Grünbaum's conjecture on the stretchability of certain arrangements of pseudolines*, J. Combin. Theory Ser. A **29** (1980) 385–390 | Every simple arrangement of at most 8 pseudolines is stretchable. | **Related.** Hence every 5-element *order type* is realizable, so the bad pentagon fails only at the finer level of slopes. This is consistent with our finding that $s$ is not an order-type invariant. |
| J. E. Goodman, R. Pollack, *Allowable sequences and order types in discrete and computational geometry*, in: J. Pach (ed.), New Trends in Discrete and Computational Geometry, Springer 1993, 103–134 | Survey of allowable sequences, $k$-sets and semispaces. | **Related only.** No statement about consecutive complete-bipartite blocks was found in the accessible parts. |
| A. Björner, M. Las Vergnas, B. Sturmfels, N. White, G. M. Ziegler, *Oriented Matroids*, 2nd ed., Cambridge Univ. Press 1999 | Standard reference for rank-3 oriented matroids, pseudoline arrangements and allowable sequences. | **Not accessed**; no theorem number can be cited. Our §4.4 shows that $s$ is *not* a function of the rank-3 oriented matroid. |
| U. Hoffmann, K. Merckx, *A universality theorem for allowable sequences with applications*, arXiv:1801.05992 | Realizability of allowable sequences is $\exists\mathbb R$-complete. Discusses the GP bad pentagon. | **Related.** It confirms that realizability depends on more than the order type. Nothing on $s$. |
| A. Padrol, E. Philippe, *Sweeps, polytopes, oriented matroids, and allowable graphs of permutations*, arXiv:2102.06134 (Combinatorica, 2023/24), Fig. 10 | Sweep polytopes (zonotopes of all difference vectors). Fig. 10 draws the bad pentagon. | **Related.** The projection orders of $P$ are the vertices of the sweep zonogon, so a BTE is a special pair of vertices of that zonogon. The caption of Fig. 10 lists a sequence ($20312\,01320$ in position notation) that **is** realizable: `captionWord_realized` gives explicit coordinates, with $s=1$. The *picture* is the $s=0$ pinwheel, so the caption appears to be misprinted. |
| R. P. Stanley, *On the number of reduced decompositions of elements of Coxeter groups*, European J. Combin. **5** (1984) 359–372 | Counts reduced words of $w_0\in S_n$: $768$ for $n=5$ and $292\,864$ for $n=6$. | **Related.** Our counts agree with his (`reducedWords5_length`, `reducedWords6_length`). Nothing on block transpositions. |
| G. S. Warrington, *A combinatorial version of Sylvester's four-point problem*, Adv. Appl. Math. **45** (2010) 390–394, arXiv:0910.5945 | Sylvester-type convexity probability for random sorting networks (uniform reduced words). | **Related only.** It is the closest probabilistic analogue on the reduced-word side. |
| O. Angel, A. E. Holroyd, D. Romik, B. Virág, *Random sorting networks*, Adv. Math. **215** (2007) 839–868 | Uniform reduced words of $w_0$ and the conjectured geometric limit. | **Related only.** |
| H. Edelsbrunner, E. Welzl, *On the number of line separations of a finite set in the plane*, J. Combin. Theory Ser. A **38** (1985) 15–29 | Bounds on the number of linearly separable splits ($k$-sets). | **Related only.** Strongly separable splits are a very small subfamily, and the bound $\le2$ is of a different nature. |
| A. Asinowski, *Suballowable sequences and geometric permutations*, Discrete Math. **308** (2008) | Allowable-sequence techniques for geometric permutations. | **Related only.** |
| S. Felsner, J. E. Goodman, *Pseudoline arrangements*, ch. 5 of Handbook of Discrete and Computational Geometry, 3rd ed. (2017) | Survey of wiring diagrams and allowable sequences. | **Related only.** |
| Z. Kabluchko, M. Panzo, arXiv:2501.16166; M. Panzo, arXiv:2409.07927 | Distribution-free Radon/absorption statistics for walks and bridges. For $n=d+3$ the results concern a rank-one dual (cone version). | **Related**, as probabilistic context. No convex-position bounds for $d+3$ points were found there. |
| Chan, Kalai, Narayanan, Ter-Saakov, arXiv:2507.01353; Felsner, Pilz, Schnider, arXiv:2001.08419; R. Schneider (2020) on random Gale diagrams | Random Radon partitions; arrangements; random Gale diagrams. | **Related only.** |
| Yu. Baryshnikov, R. Vitale, *Regular simplices and Gaussian samples*, Discrete Comput. Geom. **11** (1994) 141–147 | Gaussian Gale duality. | **Implies** the Gaussian self-duality of §9, up to a short computation. |

No source was found that defines $s(P)$ (equivalently: block-transposition events, or
consecutive complete-bipartite inversion intervals in a circular sequence), that bounds it,
or that relates it to convex position of exchangeable walks. Within the limits stated above,
the following appear new: the bound $s\le2$ (Theorem 6.1), the five-point range (Theorem 5.6),
the identification of the bad pentagon as *the* $s=0$ class, and the sharp interval
$[\frac14,\frac13]$. The Gaussian statement is an immediate consequence of known results.

---

## 3. Corrected statement of Conjecture 4

**Theorem C4 (corrected).** Let $P$ be a simple planar configuration of $N$ points (no three
collinear, no two connecting lines parallel), and let $s(P)$ be its number of strongly
separable unordered splits.

1. $N=4$: $s(P)=3$ (C3_REPORT, Cor. 9.1; also recovered in §6.3).
2. $N\ge5$: $s(P)\le2$. More generally, every simple allowable sequence on $N\ge5$ elements has
   at most two block-transposition events per half-period.
3. $N=5$: $s(P)\in\{1,2\}$. Both values occur, and the set of values depends on the order type:
   - three hull vertices: always $s=2$;
   - four hull vertices: $s\in\{1,2\}$, depending on the slopes;
   - five hull vertices: $s\in\{1,2\}$, depending on the slopes.
4. $N\ge6$: $s(P)\in\{0,1,2\}$, and all three values occur for every $N\ge6$.

**Probabilistic corollary.** For an exchangeable bridge with five points, or an ordinary walk
with four exchangeable increments, in general position in $\mathbb R^2$:
$$\tfrac14\le\mathbb P(\text{convex position})=\tfrac16+\tfrac1{12}\mathbb E s(P)\le\tfrac13 ,$$
and both bounds are attained. For $N=d+3\ge6$:
$$1-\tfrac{d+3}{(d+1)!}\le\mathbb P(\text{convex position})\le1-\tfrac{d+3}{(d+1)!}+\tfrac4{(d+2)!},$$
again sharp at both ends.

---

## 4. Definition and equivalent characterizations of $s(P)$

### 4.1 Set-up

Let $M=\binom N2$. For a pair $\{x,y\}$ let $c_{xy}\in\mathbb{RP}^1$ be its *critical
direction*: the normal direction $u$ with $\langle u,p_x\rangle=\langle u,p_y\rangle$. By
simplicity the $M$ critical directions are distinct. Reading them in cyclic order gives the
**cyclic pair sequence** $\Pi(P)$, a cyclic word in which every pair occurs exactly once.
Sweeping $u$ through a half-turn swaps the pairs one at a time in the order $\Pi(P)$, each by
an adjacent transposition of the projection order (C3_REPORT, Lemma 8.1). An *abstract*
simple allowable sequence is any reduced word of the longest permutation $w_0\in S_N$, read
periodically. It too has a cyclic pair sequence: the pairs swapped in the second half-period
are the same, in the same order.

For a split $\{A,B\}$ let $X(A,B)=A\times B$ be its set of **cross pairs**. The other pairs,
those inside $A$ or inside $B$, are its **internal pairs**. For $N\ge3$ both sets are nonempty.

### 4.2 The contiguity lemma (proof form of the definition)

**Lemma 4.1 (contiguity).** For a simple planar $P$ and a nontrivial split $\{A,B\}$ the
following are equivalent.

- (a) $\{A,B\}$ is strongly separable.
- (b) Every internal critical direction lies in $\bar I(A,B)$, the image in $\mathbb{RP}^1$ of
  $I(A,B)\cup(-I(A,B))$.
- (c) In $\Pi(P)$ the cross pairs form one cyclic interval (equivalently, the internal pairs
  form one cyclic interval).
- (d) In the circular sequence, some projection order has the form $AB$ and is followed by the
  $|A||B|$ cross swaps consecutively, which turn it into $BA$ (a block-transposition event).

*Proof.* (a)⇔(b) is the characterization proved in `с3.pdf` / C3_REPORT §8.4.
(d)⇔(a) is C3_REPORT Prop. 8.4.

(b)⇒(c). $I=I(A,B)$ is an intersection of open half-circles $\{u:\langle u,a-b\rangle>0\}$.
It is nonempty because strong separability includes strict separability. So $I$ is an open
arc of length $<\pi$, and its image $\bar I\subset\mathbb{RP}^1$ is an open arc. On $I$ no
cross pair ties, so no cross critical direction lies in $\bar I$. By (b) every internal one
does. Hence $\bar I$ contains exactly the internal critical directions, and they form a
cyclic interval of $\Pi(P)$.

(c)⇒(d) and (a). Start the sweep at a direction $u_0$ just before the first cross pair of
the cross interval. During the cross interval every cross pair is swapped once and no
internal pair is swapped.

*Claim:* the order at $u_0$ is $AB$ or $BA$. Suppose instead that $a_1<b<a_2$ with
$a_i\in A$, $b\in B$. The internal pair $a_1a_2$ is never swapped, so $a_1<a_2$ throughout.
Both cross pairs are swapped, so at the end $b<a_1$ and $a_2<b$, giving $a_2<a_1$, a
contradiction. Symmetrically, no $a$ lies between two $b$'s. This proves the claim and gives
(d).

During the internal interval only internal swaps occur, and these preserve the block form.
So for every internal critical direction $c$ the projection along $c$ still puts all of $A$
strictly on one side of all of $B$. Cross pairs do not tie at $c$, by simplicity. Hence a line
with normal $c$, that is a line parallel to the internal pair, strictly separates $A$ from
$B$. This is (a). $\square$

The proof of (c)⇒(d) uses only the reduced-word property, so (c)⇔(d) holds for abstract
allowable sequences. **For abstract sequences we take (c) as the definition of a strongly
separable split.** Consequently $s(P)$ depends only on the cyclic pair sequence $\Pi(P)$.

### 4.3 Geometric forms: which are correct

1. *Every internal segment is parallel to a strictly separating line.* This is the definition.
   **True.**
2. *Internal and cross directions occupy complementary arcs.* **True**: Lemma 4.1(c). Using
   line directions instead of normals is a rotation by $90^\circ$.
3. *Common tangents.* For disjoint convex polygons $\operatorname{conv}A$ and
   $\operatorname{conv}B$, the directions of strictly separating lines form an open arc of
   $\mathbb{RP}^1$ bounded by the directions of the two inner common tangents $\ell_1,\ell_2$.
   Each $\ell_i$ passes through one point of $A$ and one of $B$, and these are the two cross
   pairs at the ends of the cross interval. **True form:** $\{A,B\}$ is strongly separable if
   and only if, after translating every internal segment to $O=\ell_1\cap\ell_2$, each one lies
   in the open double wedge at $O$ that contains neither $\operatorname{conv}A$ nor
   $\operatorname{conv}B$.
4. *Consecutive blocks on the hull boundary.* The hull vertices in $A$ form a cyclic block of
   the hull, and so do those in $B$. This is **necessary** (it holds for every strictly
   separable split) but **not sufficient**. Counterexample: `ex5_h5_s1`, a convex pentagon
   with $s=1$, has five consecutive-pair splits and five singleton splits, but only one of
   them is strongly separable. Further necessary conditions:
   - a singleton part is a hull vertex;
   - a two-point part is a hull *edge*;
   - for every internal pair $x,y$, the line $xy$ leaves the whole other part strictly on one
     side.

   None of these is sufficient.
5. *A special edge, diagonal or cell of the order type.* **False.** $s$ is not determined by
   the order type (§4.4). The correct characterizations are slope-sensitive: Lemmas 5.1–5.5.

### 4.4 Oriented-matroid formulation (Route C)

$s$ is **not** a function of the rank-3 oriented matroid (order type) of $P$. The endpoint
Gale diagrams `galeA` and `galeB` both consist of four hull vertices and one interior point.
For five points that is a single order type, yet $s=2$ for the first and $s=1$ for the second
(`galeA_spec`, `galeB_spec`). The convex pentagons `ex5_h5_s1` and `ex5_h5_s2` give a second
example.

What $s$ *does* depend on is the cyclic order of the $M$ difference directions. Equivalently,
it depends on the rank-2 oriented matroid of the difference vectors $\{p_y-p_x\}$, labelled by
pairs. Lemma 4.1(c) is a covector condition in that rank-2 oriented matroid: the cocircuits
indexed by cross pairs must fill one of the two arcs into which the cocircuits of two suitable
cross pairs cut the circle.

So the answer to Route C is negative: the strong condition does not correspond to a special
cocircuit interval of the rank-3 tope graph. The bound comes instead from the reduced-word
argument of §6.

---

## 5. Complete solution of the realizable five-point case

### 5.1 Singleton and pair splits (any $N$)

**Lemma 5.1 (vertex splits).** $\{v\}\mid P\setminus\{v\}$ is strongly separable if and only if
(i) $v$ is a hull vertex, and (ii) no segment joining two points of $P\setminus\{v\}$ has a
direction lying in the open interior angle of $\operatorname{conv}P$ at $v$. Here directions
are unoriented, so a direction "lies in the angle" if the line through $v$ with that direction
enters the angle.

*Proof.* A line of direction $\delta$ strictly separates $v$ from $B=P\setminus\{v\}$ if and
only if the line through $v$ of direction $\delta$ misses $\operatorname{conv}B$; then shift
it slightly. The lines through a hull vertex $v$ that meet $\operatorname{conv}B$ are those
whose directions lie in the closed angle between $vu$ and $vw$, where $u,w$ are the hull
neighbours of $v$. By simplicity no segment of $B$ is parallel to $vu$ or $vw$, so the closed
angle can be replaced by the open one. $\square$

**Lemma 5.2 (pair splits).** If a part of a strongly separable split has exactly two points
$a,b$, then $ab$ is a hull edge of $P$. In particular neither $a$ nor $b$ is interior.

*Proof.* Some line parallel to $ab$ has $a,b$ strictly on one side and all other points
strictly on the other. Hence the line $ab$ itself has every other point strictly on one
side. $\square$

### 5.2 Convex pentagons: ear areas

Let $v_0,\dots,v_4$ be the vertices in cyclic order. Put
$a_j=\operatorname{area}(v_{j-1}v_jv_{j+1})$, the area of the *ear* at $v_j$ (indices mod 5).

**Lemma 5.3.**

- (i) Adjacent ear areas are distinct.
- (ii) The pair split $\{v_i,v_{i+1}\}\mid\{v_{i+2},v_{i+3},v_{i+4}\}$ is strongly separable
  if and only if $a_{i+3}$ is a **strict local minimum** of the cyclic sequence
  $(a_0,\dots,a_4)$.
- (iii) Consequently there is at least one, and at most two, strongly separable pair splits.

*Proof.* (i) $a_3=a_4$ means $\operatorname{area}(v_2v_3v_4)=\operatorname{area}(v_3v_4v_0)$.
That says $v_2$ and $v_0$ are at the same distance from the line $v_3v_4$, so
$v_0v_2\parallel v_3v_4$, which simplicity excludes.

(ii) Take $i=1$, so $A=\{v_1,v_2\}$ and $B=\{v_3,v_4,v_0\}$, and check the internal pairs one
by one.

- $v_1v_2$ is a hull edge; shifting the line slightly works.
- For the diagonal $v_0v_3$, the line $v_0v_3$ has $v_4$ on one side and $v_1,v_2$ on the
  other. So a line parallel to it, shifted slightly towards $v_1,v_2$, separates.
- Edge $v_3v_4$: $v_3,v_4$ are extreme in the normal direction, so we need every point of $A$
  strictly farther from the line $v_3v_4$ than $v_0$. Along the convex chain
  $v_4,v_0,v_1,v_2,v_3$ the distance to the line $v_3v_4$ is strictly unimodal. Ties would
  produce a line parallel to $v_3v_4$, which simplicity excludes. So the minimum over
  $\{v_0,v_1,v_2\}$ is attained at an end of the chain, and the condition is
  $d(v_0)<d(v_2)$, i.e. $\operatorname{area}(v_3v_4v_0)<\operatorname{area}(v_2v_3v_4)$, i.e.
  $a_4<a_3$.
- Edge $v_4v_0$: in the same way the condition is
  $\operatorname{area}(v_4v_0v_3)<\operatorname{area}(v_4v_0v_1)$, i.e. $a_4<a_0$.

So the split is strongly separable if and only if $a_4<a_3$ and $a_4<a_0$.

(iii) Let $a_j$ be a global minimum. Its neighbours are $\ge a_j$ and, by (i), different from
it, so it is a strict local minimum. A cyclic sequence of length 5 has at most two strict
local minima, since two strict local minima cannot be adjacent. $\square$

With Lemma 5.1: **for a convex pentagon,
$s=\#\{\text{strict local minima of the ear areas}\}+\#\{v_j\text{ satisfying 5.1(ii)}\}\ge1$**,
and $s\le2$ by Theorem 6.1.

### 5.3 Four hull vertices and one interior point

Let the hull be $v_0v_1v_2v_3$, let $X$ be the intersection point of the diagonals, and let $p$
be the interior point. By general position $p$ lies off both diagonals, so after relabelling
$p$ lies in the open triangle $v_0v_1X$.

**Lemma 5.4.**

- (i) $\{v_2,v_3\}\mid\{v_0,v_1,p\}$ is always strongly separable.
- (ii) The other three edge-pair splits never are.
- (iii) $s=1+\#\{v_j:\text{5.1(ii) holds}\}$, so $s\in\{1,2\}$.

*Proof.* (i) Check the internal pairs.

- $v_2v_3$ is a hull edge.
- $v_0v_1$: we need $d(p)<\min(d(v_2),d(v_3))$, distances being taken to the line $v_0v_1$.
  Distance is affine along segments, and $X$ lies strictly inside both $v_0v_2$ and $v_1v_3$,
  so $d(X)<d(v_2)$ and $d(X)<d(v_3)$. Also $d(p)<d(X)$, since $p$ is interior to the triangle
  $v_0v_1X$, whose only vertex off the line is $X$.
- $v_0p$: at $v_0$ the ray towards $p$ lies strictly between the rays towards $v_1$ and
  towards $v_2$. So the line $v_0p$ has $v_1$ on one side and $v_2,v_3$ on the other. Shifting
  it slightly towards $v_2,v_3$ separates $\{v_0,v_1,p\}$ from $\{v_2,v_3\}$.
- $v_1p$: symmetric. The ray $v_1p$ lies between $v_1v_0$ and $v_1v_3$.

(ii) For $\{v_0,v_1\}$: the internal pair $v_2p$ has its ray at $v_2$ between $v_2v_1$ and
$v_2v_0$, because $p\in\triangle v_0v_1v_2$. So the line $v_2p$ separates $v_0$ from $v_1$,
and no line parallel to it can have $v_0,v_1$ on the same side of $v_2,p$.

For $\{v_1,v_2\}$: the line $v_0p$ separates $v_1$ from $v_2$, as shown in (i).

For $\{v_3,v_0\}$: the line $v_1p$ separates $v_0$ from $v_3$.

(iii) By Lemma 5.2 the only possible 2|3 splits are the edge pairs, and $\{p\}$ is not a part,
being interior. $\square$

### 5.4 Three hull vertices: the triangle lemma (any $N$)

**Lemma 5.5 (triangle lemma).** Let $\operatorname{conv}P$ be a triangle $v_0v_1v_2$, and let
the set $Q$ of interior points have $|Q|\ge1$.

- (i) Every strongly separable split is a singleton $\{v_i\}$.
- (ii) The three open angles of the triangle, viewed as arcs $J_0,J_1,J_2\subset\mathbb{RP}^1$,
  partition $\mathbb{RP}^1$ minus the three edge directions.
- (iii) $\{v_i\}$ is strongly separable if and only if no segment with both endpoints in $Q$
  has its direction in $J_i$. Hence
  $s=3-\#\{i:\text{some }Q\text{–}Q\text{ direction lies in }J_i\}$.

*Proof.* (i) Some part, say $A$, contains two vertices, say $v_0,v_1$. Separation by a line
parallel to $v_0v_1$ forces every point of $B$ to be farther from the line $v_0v_1$ than
every point of $A$. Since $v_2$ is the unique farthest point, $v_2\in B$.

If $B$ contained a point $q\in Q$, consider the internal pair $v_2q$. The line $v_2q$ passes
through the interior and leaves the triangle through the open edge $v_0v_1$, so it separates
$v_0$ from $v_1$. But the line through an internal pair must leave the other part strictly on
one side (§4.3(4)), so this is impossible. Hence $B=\{v_2\}$.

(ii) Translate the three angles to a common point: they tile a straight angle.

(iii) By Lemma 5.1, $\{v_2\}$ is strongly separable if and only if no direction of a segment
among $v_0,v_1,Q$ lies in $J_2$.
- The direction of $v_0v_1$ is an edge direction.
- The direction of $v_0q$, for $q\in Q$, lies in $J_0$ (the line $v_0q$ enters the angle at
  $v_0$).
- The direction of $v_1q$ lies in $J_1$.

Only $Q$–$Q$ directions remain. By simplicity none of them is an edge direction, so each lies
in exactly one $J_i$. $\square$

For $N=5$, $|Q|=2$: there is a single $Q$–$Q$ direction, which hits exactly one arc, so
**$s=2$ for every configuration of this order type.**

### 5.5 The five-point theorem

**Theorem 5.6.** Every realizable simple five-point configuration has $s(P)\in\{1,2\}$.

| order type | strongly separable splits | $s$ | depends on slopes? | examples (Lean) |
|---|---|---|---|---|
| convex pentagon | pair splits opposite the strict local minima of the ear areas, plus vertices satisfying 5.1(ii) | 1 or 2 | yes | `ex5_h5_s1` ($s=1$), `ex5_h5_s2` ($s=2$) |
| 4 + 1 | the edge opposite the triangle $v_iv_{i+1}X$ containing $p$, plus at most one vertex satisfying 5.1(ii) | 1 or 2 | yes | `ex5_h4_s1`, `ex5_h4_s2`, `galeB` ($s=1$), `galeA` ($s=2$) |
| 3 + 2 | the two triangle vertices whose angle does not contain the direction $pq$ | 2 | no | `ex5_h3` |

*Proof.* The lower bound comes from Lemmas 5.3, 5.4 and 5.5. The upper bound is Theorem 6.1.
For $N=5$ there are exactly three order types, all realizable. $\square$

**Deformations.** Within the 3+2 order type $s$ is constant. Within the other two order types,
moving the slopes while keeping the order type can change $s$: the pairs `ex5_h5_s1`/`ex5_h5_s2`
and `galeB`/`galeA` show this. On the set of simple configurations, $s$ is constant on each
connected component. It can change only when two connecting lines become parallel, because
$\Pi(P)$ changes only there.

### 5.6 Abstract sequences: C4-C

- **Machine count.** `sWord5_distribution` shows that among the $768$ normalized words
  (reduced words of $w_0\in S_5$, i.e. simple allowable sequences with identity start), the
  values $s=0,1,2$ occur $8,400,360$ times. By `sWord5_zero`, the eight words with $s=0$ are
  the four cyclic rotations of the position pattern $0132\,0132\,01$ and the four rotations of
  its reversal $0231\,0231\,02$. `sWord5_le_two` and `sWord6_le_two` are finite confirmations
  of Theorem 6.1 for $N=5,6$; they are not the proof.
- **Invariance.** Write $a\mapsto 3-a$ for the relabelling induced by conjugation by $w_0$.
  - Cyclic shift of the circular sequence acts on normalized words by
    $a_1a_2\cdots a_{10}\mapsto a_2\cdots a_{10}(3-a_1)$. It maps
    $0132013201\to1320132013\to3201320132\to2013201320\to0132013201$.
  - Reversal of the word exchanges the two families of four.
  - The mirror relabelling $a\mapsto3-a$ preserves the set.

  So the eight words form a **single orbit** under shift and reversal: one circular sequence
  up to reflection, with 5-fold rotational symmetry. This is the pinwheel "bad pentagon" of
  Goodman–Pollack. The set is **not** invariant under commutation moves:
  $0132013201\to0312013201$ (commuting the letters $1,3$) gives a word with $s\ge1$. This is
  as it must be, since commutation classes correspond to order types and $s$ is not an
  order-type invariant.
- **Non-stretchability (conceptual).** If one of the eight words were realized by a simple
  $P$, then $s(P)=0$. Whatever the order type of $P$, Lemmas 5.3, 5.4 and 5.5 produce a
  strongly separable split, which is a contradiction (Theorem 5.6). For the pentagon order type
  (the bad pentagon is drawn as a pinwheel pentagon) the contradiction is especially
  transparent: $s=0$ would require every ear area to have a strictly smaller neighbour, which
  is impossible for a finite cyclic sequence.
- **Converse (finite).** Every word with $s\ge1$ is realizable. `realizers_cover` exhibits
  nineteen integer configurations whose allowable sequences, read from every start, in both
  orientations and for the mirror image, exhaust all 760 such words. This direction is a
  finite verification, not a conceptual proof.

**C4-C, precise form.** A simple allowable sequence on five elements is stretchable if and
only if $s\ge1$. The $s=0$ sequences are exactly the bad-pentagon circular sequence and its
mirror image.

### 5.7 C4-D: attainability

Here is a direct geometric realization of both values, independent of the computer.

- **$s=2$:** any simple 3+2 configuration (Lemma 5.5), e.g.
  $(0,2),(3,4),(2,2),(2,3),(4,1)$.
- **$s=1$:** a 4+1 configuration in which no hull vertex satisfies 5.1(ii) (Lemma 5.4), e.g.
  $(3,0),(0,2),(1,3),(2,1),(0,1)$.

The exact values, and simplicity, are checked by `ex5_h3_spec` and `ex5_h4_s1_spec`, which
evaluate the *definition* (strong separability tested pair by pair).

---

## 6. Proof that $s\le2$ for $N\ge5$

**Theorem 6.1.** Every simple allowable sequence on $N\ge5$ elements, realizable or not, has
at most two strongly separable splits in the sense of Lemma 4.1(c). In particular $s(P)\le2$
for every simple planar $P$ with $N\ge5$.

The proof follows Route B and works in the cyclic pair sequence $\Pi$. For a strongly separable
split $\sigma$, its cross set $X_\sigma$ and its internal set $\mathrm{Int}_\sigma$ are
complementary cyclic intervals.

**Step 1: distinct splits have incomparable cross sets.** Suppose $X_\sigma\subseteq X_\tau$
with $\tau=\{C,D\}$, so $\mathrm{Int}_\tau\subseteq\mathrm{Int}_\sigma$. Every part of $\tau$
with at least 2 points spans a clique of internal pairs, so it lies inside one part of
$\sigma$.
- If $|C|,|D|\ge2$, they lie in different parts of $\sigma$ (else one part of $\sigma$ would
  be everything), and $\sigma=\tau$.
- If $|C|=1$, then $D$ ($|D|\ge2$) lies in a part of $\sigma$, which must be $D$ itself, and
  again $\sigma=\tau$.

**Step 2: cross sets always meet, and never cover $\Pi$.** Let $\sigma=\{A,B\}$ and
$\tau=\{C,D\}$.
- If $A\cap C$ and $B\cap D$ are both nonempty, a pair taken from them is cross for both.
  Otherwise, say $A\cap C=\emptyset$; then $A\subseteq D$ and $C\subseteq B$, and a pair from
  $A$ and $C$ is cross for both.
- The four cells $A\cap C$, $A\cap D$, $B\cap C$, $B\cap D$ partition $N\ge5$ points, so some
  cell has two points. That pair is internal for both, so $X_\sigma\cup X_\tau\ne\Pi$.

Cut the cycle at a pair outside $X_\sigma\cup X_\tau$. The two cross sets become intersecting,
incomparable intervals of a line. So, in the sweep direction or in the opposite direction,
$\Pi$ reads
$$[X_\sigma\setminus X_\tau]\,[X_\sigma\cap X_\tau]\,[X_\tau\setminus X_\sigma]\,[\mathrm{Int}_\sigma\cap\mathrm{Int}_\tau],\qquad\text{all four blocks nonempty.}\tag{6.1}$$
Reversing the sweep direction exchanges the roles of $\sigma$ and $\tau$. So we may assume
that (6.1) holds in the sweep direction for a suitable naming of the two splits.

**Step 3: two strongly separable splits never cross.** Suppose all four cells are nonempty, and
pick $p_1\in A\cap C$, $p_2\in A\cap D$, $p_3\in B\cap C$, $p_4\in B\cap D$. The six pairs among
them sort as follows:
- $13,24\in X_\sigma\setminus X_\tau$;
- $14,23\in X_\sigma\cap X_\tau$;
- $12,34\in X_\tau\setminus X_\sigma$.

At the start of the interval $X_\sigma$ the projection order is $AB$ or $BA$ (proof of
Lemma 4.1). Swapping the names $A,B$ (which permutes the $p_i$ but preserves the three
classes) we may take it to be $AB$, so $p_1,p_2$ precede $p_3,p_4$. Run the sweep through the
block $X_\sigma\setminus X_\tau$. The pairs $13$ and $24$ get inverted, while $14$ and $23$
are not yet inverted. The resulting order would satisfy
$$p_3<p_1<p_4<p_2<p_3 ,$$
a contradiction. So, after renaming, $A\subsetneq C$ and $D\subsetneq B$. Write
$Z=C\setminus A=B\setminus D\neq\emptyset$, so that $\sigma=\{A,Z\cup D\}$ and
$\tau=\{A\cup Z,D\}$.

Now $X_\sigma\setminus X_\tau=A\times Z$, $X_\sigma\cap X_\tau=A\times D$ and
$X_\tau\setminus X_\sigma=Z\times D$. The remaining block, $\mathrm{Int}$, is the set of pairs
inside $A$, inside $Z$ or inside $D$, and it is nonempty. By (6.1), possibly after exchanging
the names $A\leftrightarrow D$ (which reverses the direction), the cyclic order is
$$[A\times Z]\;[A\times D]\;[Z\times D]\;[\mathrm{Int}].\tag{6.2}$$

**Step 4: no third split.** Let $\varepsilon=\{E,F\}$ be a third strongly separable split. By
Step 3 it is non-crossing with both $\sigma$ and $\tau$. Choosing the name $E$ suitably, the
non-crossing conditions leave five cases:
- (a) $E\subsetneq A$;
- (b) $E\subsetneq D$;
- (c) $E\subsetneq Z$;
- (d) $E=Z$;
- (e) $E=D\cup Z'$ with $\emptyset\ne Z'\subsetneq Z$.

(Non-crossing with $\sigma$ lets us take $E\subseteq A$ or $E\subseteq Z\cup D$. In the second
case, non-crossing with $\tau$ gives $E\subseteq D$, $E\subseteq Z$ or $E\supseteq D$. The
excluded equalities would give $\varepsilon\in\{\sigma,\tau\}$.)

In each case $X_\varepsilon$ fails to be a cyclic interval in (6.2). In each case we name a
nonempty set of pairs that are internal to $\varepsilon$ but would have to lie inside the arc
$X_\varepsilon$:

- **(a)** $X_\varepsilon=E\times(A\setminus E)\cup E\times Z\cup E\times D$. It meets
  $\mathrm{Int}$ and $[A\times D]$ and misses $[Z\times D]$ entirely. Avoiding $[Z\times D]$,
  the arc must run $\mathrm{Int}\to[A\times Z]\to[A\times D]$, so it contains all of
  $[A\times Z]$, including $(A\setminus E)\times Z$. Those pairs are internal to $\varepsilon$.
- **(b)** Symmetric. $X_\varepsilon$ meets $[A\times D]$ and $\mathrm{Int}$ and misses
  $[A\times Z]$, so it contains $[Z\times D]\supseteq Z\times(D\setminus E)$, which is internal
  to $\varepsilon$.
- **(c)** $X_\varepsilon$ meets $[A\times Z]$ and $[Z\times D]$ and misses $[A\times D]$, so it
  contains all of $\mathrm{Int}$. If $|E|\ge2$, the pairs inside $E$ are internal to
  $\varepsilon$. If $|E|=1$, then $N=|A|+|D|+|Z\setminus E|+1\ge5$ forces one of
  $A,D,Z\setminus E$ to have two points, and that pair is internal to $\varepsilon$.
- **(d)** $X_\varepsilon=[A\times Z]\cup[Z\times D]$. These two blocks are separated on both
  sides by the nonempty blocks $[A\times D]$ and $\mathrm{Int}$, so $X_\varepsilon$ is not an
  arc.
- **(e)** $X_\varepsilon=(D\cup Z')\times(A\cup Z'')$ with $Z''=Z\setminus Z'$. It contains
  $[A\times D]$ and the pairs $Z'\times Z''\subseteq\mathrm{Int}$. An arc joining them passes
  through $[Z\times D]$, which contains the $\varepsilon$-internal pairs $Z'\times D$, or
  through $[A\times Z]$, which contains the $\varepsilon$-internal pairs $A\times Z''$.

All cases are contradictory, so $s\le2$. $\square$

### 6.2 Where $N\ge5$ is used, and Route A

The hypothesis $N\ge5$ enters twice: in Step 2 ($\mathrm{Int}_\sigma\cap\mathrm{Int}_\tau\neq\emptyset$)
and in case (c).

**Route A (angular intervals).** For two strongly separable splits, the separation arcs
$\bar I_\sigma=\mathrm{Int}_\sigma$ and $\bar I_\tau=\mathrm{Int}_\tau$ are
$[Z\times D][\mathrm{Int}]$ and $[\mathrm{Int}][A\times Z]$. So they **interlace**:
- they overlap in the common internal arc;
- neither is nested in the other;
- their endpoints alternate;
- the underlying splits are nested (compatible).

Interlacing alone does not exclude a third arc, since three pairwise interlacing arcs exist
on a circle. The bound needs the combinatorial content of Steps 3–4.

### 6.3 Why $N=4$ is different

For $N=4$ Step 2 fails exactly when all four cells are singletons. Then
$X_\sigma\cup X_\tau=\Pi$, $X_\sigma\cap X_\tau$ splits into two separate arcs, and (6.1) does
not hold, so crossing splits are allowed. Case (c) also survives with all blocks singletons.
Concretely:
- a convex quadrilateral $v_0v_1v_2v_3$ has the two crossing splits $\{v_0v_1|v_2v_3\}$ and
  $\{v_1v_2|v_3v_0\}$, plus one vertex split;
- a triangle with one interior point has three vertex splits (Lemma 5.5 with $Q$ a single
  point, so there is no $Q$–$Q$ direction).

So $s=3$, in agreement with C3_REPORT Cor. 9.1.

---

## 7. The sharp five-point convex-position theorem

**Theorem 7.1.** Let $N=5$, $d=2$. Consider either
- (bridge) $X_1,\dots,X_5\in\mathbb R^2$ exchangeable with $\sum X_i=0$, the points being
  $S_1,\dots,S_5$; or
- (walk) $Y_1,\dots,Y_4$ exchangeable, the points being $S_0=0,S_1,\dots,S_4$.

In either case assume the five points are almost surely in general affine position. Let $P$
be the planar Gale diagram of the step configuration. Then
$$\mathbb P(N_1=2)=\frac{\mathbb E s(P)}{12},\qquad\mathbb P(N_1=1)=\frac56-\frac{\mathbb E s(P)}6,\qquad\mathbb P(\text{convex position})=\mathbb P(N_1=0)=\frac16+\frac{\mathbb E s(P)}{12},$$
and
$$\frac14\le\mathbb P(\text{convex position})\le\frac13,\qquad\frac1{12}\le\mathbb P(N_1=2)\le\frac16,\qquad\frac12\le\mathbb P(N_1=1)\le\frac23 .$$
All bounds are attained.

*Proof.* Substitute $N=5$, $(N-1)!=24$, $(N-2)!=6$ into (1):
- $\mathbb P(N_1=2)=2\mathbb Es/24$;
- $\mathbb P(N_1=1)=5/6-4\mathbb Es/24$;
- $\mathbb P(N_1=0)=1-5/6+2\mathbb Es/24$.

Formula (1) holds for both models (C3_REPORT §6). In the bridge case Lemma 6.1 there is
applied with $G=\mathrm{Sym}(5)$. In the walk case it is applied with
$G=\mathrm{Stab}(5)$, the permutations fixing the closing step $X_5=-\sum Y_i$. The point set
$\{S_0,\dots,S_4\}$ is the point set of the closed walk, and Lemma 5.2 there matches
$\mathrm{Stab}(5)$ bijectively with the circular classes.

In both models, almost-sure general position implies condition (G) almost surely, and (G) is
equivalent to simplicity of $P$ (C3_REPORT Lemma 2.1). Theorem 5.6 then gives
$s(P)\in\{1,2\}$ almost surely, hence $1\le\mathbb Es\le2$. Sharpness is §10. $\square$

The walk and bridge statements differ only through the law of $P$. For a fixed multiset of
steps the two give the same value of $s$, but the counts are taken over $24$ and $120$
orderings respectively.

---

## 8. General $N=d+3$ consequences

**Theorem 8.1.** For $N=d+3\ge6$ and exchangeable bridges or walks in general position,
$$1-\frac{N}{(N-2)!}\le\mathbb P(\text{convex position})=1-\frac N{(N-2)!}+\frac{2\mathbb Es(P)}{(N-1)!}\le1-\frac N{(N-2)!}+\frac4{(N-1)!},$$
that is,
$$1-\frac{d+3}{(d+1)!}\le\mathbb P(\text{convex})\le1-\frac{d+3}{(d+1)!}+\frac4{(d+2)!}.$$
Both ends are attained. Also $0\le\mathbb P(N_1=2)\le4/(N-1)!$. For exchangeable laws every
value in the interval is attained.

*Proof.* The upper bound follows from (1) and Theorem 6.1. The lower bound is $s\ge0$.

**No extra term for $N\ge6$.** The value $s=0$ is realizable for every $N\ge6$:
- $N=6$: the convex hexagon `ex6_s0`, and the triangle configuration `ex6_tri_s0`;
- every $N\ge6$, conceptually by Lemma 5.5: choose three interior points whose pairwise
  directions lie in the three angle arcs (for instance a small, slightly perturbed copy of the
  triangle formed by the three median vectors; the median from $v_i$ lies in $J_i$). This
  gives $s=0$. Further interior points can be added generically.

*Heredity:* if $x$ is interior, any strongly separable split of $P\cup\{x\}$ restricts to a
strongly separable split of $P$, because all the defining conditions restrict and $\{x\}$
cannot be a part. So $s=0$ persists.

The value $s=2$ is realized by a triangle with a nearly collinear cluster of interior points,
whose pairwise directions all lie in one arc $J_i$ (Lemma 5.5; `ex6_s2`, `ex7_s2`, `ex8_s2`).
The value $s=1$ is realized by a cluster whose directions straddle exactly one edge direction
(`ex6_tri_s1`).

Every simple planar $P$ is the Gale diagram of some step configuration, namely its Gale dual
vector configuration in $\mathbb R^{N-3}$. That configuration sums to zero and satisfies (G).
A uniformly random ordering of it is therefore an exchangeable bridge with
$\mathbb P(\text{convex})$ equal to the endpoint value. The same configuration with the last
step fixed gives an exchangeable walk. Mixtures of two such laws give every intermediate
value. $\square$

**Exact values** (`convex_bounds_values`):

| $d$ | $N$ | interval | width |
|---|---|---|---|
| 2 | 5 | $[1/4,\,1/3]$ (needs $1\le s\le2$, Theorem 5.6) | $1/12$ |
| 3 | 6 | $[3/4,\,47/60]$ | $1/30$ |
| 4 | 7 | $[113/120,\,341/360]$ | $1/180$ |

For $N=5$ the lower end is $1/6+1/12=1/4$, not $1/6$, because $s\ge1$. For $N\ge6$ the lower
end $1-N/(N-2)!$ is sharp. The admissible range for *i.i.d.* (rather than merely
exchangeable) increments is not determined here and remains open.

---

## 9. Gaussian self-duality

**Proposition 9.1.**
1. *Bridge.* Let $X=(I-\tfrac1N\mathbf 1\mathbf 1^\top)$ applied to $N$ i.i.d. $N(0,I_d)$
   steps, i.e. Gaussian steps conditioned on sum zero, with $N=d+3$. Then the affine Gale
   diagram is affinely equivalent in law to an i.i.d. sample $\gamma_1,\dots,\gamma_N$ of
   $N(0,I_2)$.
2. *Walk.* Let $Y_1,\dots,Y_{N-1}$ be i.i.d. $N(0,I_d)$, with closing step $-\sum Y_i$. Then
   the affine Gale diagram is affinely equivalent in law to
   $(\gamma_1,\dots,\gamma_{N-1},0)$.

Here "affinely equivalent in law" means: there are versions of the two configurations that are
almost surely affine images of one another. Since $s$, $\Omega$ and all the statistics above
are affine invariants, their laws agree.

*Proof.* The dependency space is $\widetilde L=\{t:\sum t_ia_i=0\}=(\text{row space of }a)^\perp\ni\mathbf 1$,
and a Gale diagram is any $(v^1_i,v^2_i)_i$ where $\mathbf 1,v^1,v^2$ is a basis of
$\widetilde L$.

(1) The $d$ rows of $a$ are i.i.d. isotropic Gaussian vectors in $\mathbf 1^\perp$
($\dim N-1$). Their span is uniform on $\mathrm{Gr}(d,\mathbf 1^\perp)$, so
$W=\widetilde L\cap\mathbf 1^\perp$ is uniform on $\mathrm{Gr}(2,\mathbf 1^\perp)$. So is the
span of two independent isotropic Gaussians $h^k=(I-\tfrac1N\mathbf 1\mathbf 1^\top)g^k$,
$g^k\sim N(0,I_N)$. Hence one may take $p_i=(g^1_i-\bar g^1,\,g^2_i-\bar g^2)=\gamma_i-\bar\gamma$,
which is a translate of the i.i.d. sample.

(2) $\sum_{i<N}t_iY_i+t_N(-\sum Y_i)=\sum_{i<N}(t_i-t_N)Y_i$. So
$\widetilde L=\mathbb R\mathbf 1\oplus\{(v,0):v\in\ker Y\}$, where $\ker Y\subset\mathbb R^{N-1}$
is the orthogonal complement of $d$ i.i.d. standard Gaussian rows. It is uniform on
$\mathrm{Gr}(2,\mathbb R^{N-1})$, as is the span of $g^1,g^2\sim N(0,I_{N-1})$. Taking
$v^k=(g^k,0)$ gives $p_i=(g^1_i,g^2_i)$ for $i<N$ and $p_N=0$. $\square$

**Corollary 9.2** ($N=5$).
$$\mathbb P_{\rm Gauss\ walk}(\text{convex})=\frac16+\frac1{12}\mathbb Es(0,\gamma_1,\gamma_2,\gamma_3,\gamma_4),\qquad\mathbb P_{\rm Gauss\ bridge}(\text{convex})=\frac16+\frac1{12}\mathbb Es(\gamma_1,\dots,\gamma_5).$$
By Theorem 5.6 both lie in $[1/4,1/3]$. Since $s\in\{1,2\}$ and the 3+2 type forces $s=2$,
$$\mathbb Es=1+\mathbb P(s=2)=1+\mathbb P(\text{hull is a triangle})+\mathbb P(\text{4 or 5 hull vertices and }s=2).$$
Lemmas 5.3 and 5.4 turn the last term into explicit Gaussian integrals: ear-area comparisons,
plus the vertex conditions of Lemma 5.1. These integrals are **not** evaluated here.

**Novelty.** This is an immediate consequence of the rotation-invariance argument behind the
Gaussian Gale vectors of Theorem 1.3 in `sylvester_radon.pdf` and of Baryshnikov–Vitale
(1994). The only new ingredient is the bookkeeping of the walk case: the extra Gale point $0$
coming from the closing step.

---

## 10. Explicit endpoint examples

Step sets (each sums to $0$):
$$A=\{(-5,9),(-7,-1),(-6,6),(5,6),(13,-20)\},\qquad B=\{(9,6),(7,3),(9,-8),(6,-2),(-31,1)\}.$$

**Gale diagrams.** In each case $\mathbf 1$, $u$ and $w$ are linear dependences of the steps
and are linearly independent (`galeA_is_gale`, `galeB_is_gale`, `gale_rows_independent`). So
$p_i=(u_i,w_i)$ is an affine Gale diagram.

- $A$: $u=(-12,-6,17,0,0)$, $w=(-37,75,0,68,0)$, giving
  $P_A=\{(-12,-37),(-6,75),(17,0),(0,68),(0,0)\}$. It is simple, with hull $p_0p_2p_3p_1$ and
  interior point $p_4$ (type 4+1). Its strongly separable splits are $\{p_0\}$ (a vertex
  satisfying 5.1(ii)) and $\{p_1,p_3\}\mid\{p_0,p_2,p_4\}$ (the edge of Lemma 5.4(i)). So
  **$s=2$** (`galeA_spec`).
- $B$: $u=(83,-126,15,0,0)$, $w=(32,-54,0,15,0)$, giving
  $P_B=\{(83,32),(-126,-54),(15,0),(0,15),(0,0)\}$. It is simple, of type 4+1, with the single
  split $\{p_0,p_2\}\mid\{p_1,p_3,p_4\}$. So **$s=1$** (`galeB_spec`).

**Finite counting argument.** Take a uniformly random ordering of a fixed step multiset with
distinct steps. Every ordering has the same Gale diagram up to relabelling, so $s$ is constant
and $\mathbb E s=s$. Simplicity of $P$ is equivalent to general position of *every* ordering
(C3_REPORT Lemma 2.1). Theorem 7.1 then says that, of the $120$ orderings:

| | convex position | $N_1=1$ | $N_1=2$ | $\mathbb P(\text{convex})$ |
|---|---|---|---|---|
| general $s$ | $20+10s$ | $100-20s$ | $10s$ | $\frac16+\frac s{12}$ |
| $A$, $s=2$ | 40 | 60 | 20 | $1/3$ |
| $B$, $s=1$ | 30 | 80 | 10 | $1/4$ |

In the walk version (last step fixed, $24$ orderings) the convex counts are $4+2s$: $8$ for A
and $6$ for B.

These predictions agree with the **independent** exhaustive enumeration in
`FivePointBridge.lean`:
- `bridgeStats_A = (true, 40, 100, 20)` and `bridgeStats_B = (true, 30, 100, 10)` (general
  position of all 120 orderings, convex count, total number of interior points, number of
  orderings with two interior points);
- `walkStats_A` and `walkStats_B` give 8 and 6 convex orderings out of 24.

So **A gives the upper endpoint $1/3$ and B gives the lower endpoint $1/4$.** The identity
`endpoint_counts` records the arithmetic $20+10s$, $10s$.

Exact equality is not special to deterministic step sets. Adding small independent continuous
noise to the steps (before the random ordering) keeps $P$ simple with the same $s$, because
$s$ is locally constant. This gives exchangeable laws with densities attaining the endpoints.

---

## 11. Status table

| Claim | Status |
|---|---|
| Contiguity lemma 4.1 (s.s. ⟺ cross pairs form a cyclic interval ⟺ BTE) | **proved** (prose; (a)⇔(b)⇔(d) from C3) |
| Characterizations 4.3(1)–(3) | **proved** |
| "Consecutive on the hull" sufficient | **false**: counterexample `ex5_h5_s1` |
| $s$ determined by order type / rank-3 oriented matroid | **false**: `galeA` vs `galeB`, `ex5_h5_s1` vs `ex5_h5_s2` |
| $s(P)=3$ for $N=4$ | **proved** (C3; recovered in §6.3) |
| C4-A: $s\le2$ for $N\ge5$, also for abstract sequences | **proved** (Theorem 6.1); finite confirmation for $N=5,6$ in Lean |
| Unrestricted $s\le2$ | **false** at $N=4$ |
| C4-B: $s\ge1$ for realizable $N=5$ | **proved** (Theorem 5.6) |
| Ear-area, 4+1 and triangle lemmas (5.3–5.5) | **proved** |
| $s\ge1$ for abstract 5-element sequences | **false**: 8 words with $s=0$ (Lean count) |
| C4-C: $s=0$ words non-stretchable | **proved** (from C4-B); identification with the GP bad pentagon **already known** as a non-stretchable example (GP 1980) |
| C4-C: every $s\ge1$ word stretchable | **proved by finite verification** (19 realizers, Lean); no conceptual proof |
| "Eight periodic words" invariant under shift / reversal / relabelling | **proved** (one orbit); **false** under commutation moves |
| C4-D: $s=1,2$ attained at $N=5$ | **proved** (explicit examples, exact checks; geometric criteria) |
| $s\ge1$ for $N\ge6$ | **false**: `ex6_s0`, `ex7_s0`, `ex6_tri_s0`, and the triangle construction |
| Range $\{0,1,2\}$ for every $N\ge6$ | **proved** |
| $\mathbb P(\text{convex})=\frac16+\frac{\mathbb Es}{12}\in[\frac14,\frac13]$ at $N=5$, with formulas for $N_1=1,2$ | **proved** under the C3 results (bridge and walk) |
| Sharpness via A ($1/3$) and B ($1/4$) | **proved** (exact; Lean) |
| General $N=d+3$ interval, sharp, no extra term for $N\ge6$ | **proved** under the C3 results |
| Range for i.i.d. increments | **unresolved** |
| Gaussian self-duality (bridge and walk) | **proved**; essentially **already known** (Baryshnikov–Vitale; Thm 1.3 construction) |
| Value of $\mathbb E s$ for Gaussian samples | **unresolved** (not computed) |
| Novelty of $s$, $s\le2$, the five-point interval | apparently open in the literature searched; **provisional** (no MathSciNet/zbMATH access) |

## 12. Genuinely new results (provisionally)

1. **Contiguity lemma:** strong separability is equivalent to the cross pairs forming one cyclic
   interval of the circular pair sequence. This makes $s$ a statistic of abstract allowable
   sequences.
2. **Two-split theorem:** every simple allowable sequence on $N\ge5$ elements has at most two
   strongly separable splits. Any two are nested, with interlacing separation arcs. The value
   $3$ occurs only at $N=4$.
3. **Five-point range** $s\in\{1,2\}$ for realizable configurations, with an order-type
   classification:
   - ear-area minima for pentagons;
   - one forced edge split for the 4+1 type;
   - $s\equiv2$ for the 3+2 type, from the triangle lemma.
4. **Conceptual non-stretchability proof for the bad pentagon:** a convex pentagon always has a
   strict local minimum of ear areas. Together with the finite realizations, this gives the
   criterion "realizable ⟺ $s\ge1$" for five-element allowable sequences.
5. **Sharp five-point theorem** $\frac14\le\mathbb P(\text{convex position})\le\frac13$ for
   planar exchangeable walks and bridges, with explicit extremal step sets. Also sharp
   intervals for every $N=d+3\ge6$.
