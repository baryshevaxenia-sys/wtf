# Conjecture 2 (the "Stirling × Eulerian product formula"): literature check and proof

This report covers only Conjecture 2 of `RESEARCH_MAP.md` (§2.2). Conjectures 3 and 4 are not
considered. No numerical experiment is used as evidence for any claim below. The few exact
small-case computations that appear are labelled as such, and none of them is part of a proof.

**Files.**
* This report, `C2_REPORT.md`.
* `RequestProject/ChamberEulerian.lean`: a Lean 4 / Mathlib formalisation of the
  deterministic, combinatorial core. It builds with no `sorry`, and its theorems use only the
  standard axioms `propext`, `Classical.choice` and `Quot.sound`. What it covers and what it
  does not cover is listed in §5.4.

**Source note.** The prompt cites a file `wtf.pdf`, but it is not among the uploaded files.
The statement of C2 and the definition of the condition (NT) are therefore taken from the
prompt itself and from `RESEARCH_MAP.md` (§2, "Notation", and §2.2).

**Conventions.** $N\ge 2$ is the number of walk points. $A(n,j)$ is the number of
permutations of $[n]$ with $j$ descents, and $A_n(x)=\sum_j A(n,j)x^j$; for example
$A_2=1+x$, $A_3=1+4x+x^2$, $A_4=1+11x+11x^2+x^3$. ${n\brack k}$ are the unsigned Stirling
numbers of the first kind. $M_{N,d}=2\sum_{r\ge0}{N\brack d+2+2r}$. For a word or permutation
$\pi$ of $[N]$, $\operatorname{cdes}\pi=\#\{i\in[N]:\pi(i)>\pi(i+1)\}$ with $\pi(N+1)=\pi(1)$.

---

## 1. Executive literature verdict

**Verdict 3: the two factors are known separately, but their product interpretation seems
unstated.** The product itself is a short corollary of known results: one reindexing of a
sum, plus exchangeability. So it should be presented as a new and easy synthesis, not as a
substantial new theorem.

* **The Stirling factor is known exactly.** For a generic dependency space, the number of
  chambers met is $M_{N,d}$. Under exchangeability and general position this genericity holds
  almost surely, so the count is almost surely $M_{N,d}$. All of this is in
  Kabluchko–Vysotsky–Zaporozhets, GAFA 2017: Theorem 3.4, Lemma 6.2, and the proof of
  Theorem 2.1 in §6.1. The same count, in the language of "projection orders", is
  Godland–Kabluchko, Trans. AMS 2021, Theorem 1.1.
* **The Eulerian factor is known exactly.** $\sum_{\pi\in S_N}x^{\operatorname{cdes}\pi}=N\,x\,A_{N-1}(x)$
  is Fulman 2000, Corollary 1, restated as Petersen 2005, Proposition 1.1. For $N=d+2$ it is
  Lemma 4.4 of `sylvester_radon.pdf`.
* **The averaging device is standard.** It appears as "a uniformly chosen cone of a random
  tessellation equals a fixed-label cone conditioned to be non-trivial" in Godland–Kabluchko
  2021, Proposition 1.12 (after Hug–Schneider 2016), in KVZ 2017, eqs. (56)–(57), and in
  Step 3 of the proof of Theorem 1.4 in `sylvester_radon.pdf`.
* **The product was not found stated anywhere.** Neither the chamber-weighted cyclic-descent
  polynomial $\mathbb E H_L(x)=M_{N,d}\,xA_{N-1}(x)/(N-1)!$, nor the statement that a
  uniformly chosen met chamber has the cyclic Eulerian law, appears in any source I examined
  (see §2 and §2.1).
* **Two coefficients of C2 are already known theorems in disguise.** The coefficients of $x$
  and of $x^{N-1}$ are equivalent to the known expected number of vertices of the walk's
  convex hull: KVZ, Adv. Math. 2017, Theorem 1.2 with $k=0$ (see §5.3). For $N=d+2$ the whole
  polynomial is Theorem 1.4.

**The mathematics.** C2 is **true** for exchangeable bridges and for ordinary walks with
exchangeable increments, under general position almost surely. The prompt's formulation needs
three corrections or clarifications:

1. The **deterministic** version needs *genericity of the dependency space with respect to the
   braid arrangement*. General affine position of the points is not enough (§3, §4).
2. Route A ("apply Theorem 2.17 to an affine slice and double") **fails as stated**. Correct
   doubling needs a correction term (§7).
3. The underlying relabelling identity (3) holds for **every** set $L$, with no assumption at
   all (§5).

**Search coverage.** The search used live internet access: arXiv full texts, arXiv search,
and the OpenAlex bibliographic database, including the list of works citing KVZ GAFA 2017.
MathSciNet and zbMATH were not available. The full text of Barndorff-Nielsen–Baxter (1963)
could not be retrieved, so its content is taken from how KVZ describe it. Search strings and
the list of sources are in §2.1. The verdict is therefore final for the sources examined and
provisional for the rest of the literature.

---

## 2. Table of the closest known results

| # | Source | Exact location | What it proves | What it gives for C2 | Type of match |
|---|---|---|---|---|---|
| K1 | Z. Kabluchko, V. Vysotsky, D. Zaporozhets, *Convex hulls of random walks, hyperplane arrangements, and Weyl chambers*, GAFA 27 (2017) 880–918, doi:10.1007/s00039-017-0415-x, arXiv:1510.04073 | Lemma 3.1; Theorem 3.3; Theorem 3.4 | Restricting an arrangement to a generic subspace of codimension $d$ truncates the characteristic polynomial (Lemma 3.1). The number of regions met is $2(a_{d+1}+a_{d+3}+\dots)$ (Theorem 3.3). For type $A_{n-1}$ this is $2({n\brack d+1}+{n\brack d+3}+\dots)$ (Theorem 3.4) | With codimension $d+1$, i.e. the space $L\cap\mathbf 1^\perp$: $\lvert\mathcal W(L)\rvert=M_{N,d}$ for generic $L$ | Exact (factor $M_{N,d}$) |
| K2 | same paper | Lemma 3.5 | For a generic subspace, closed chambers meeting it non-trivially are exactly the open chambers meeting it (36). For any subspace of the same dimension the count of open chambers met is at most the generic count (38) | Settles open versus closed (§3.1). Gives $\lvert\mathcal W(L)\rvert\le M_{N,d}$ always | Exact |
| K3 | same paper | Lemma 6.1, Lemma 6.2, proof of Theorem 2.1 (§6.1), Theorem 2.1 | For an exchangeable bridge in which any $d$ of $S_1,\dots,S_{n-1}$ are linearly independent almost surely, $L\cap\ker A$ is almost surely generic with respect to $A(A_{n-1})$ (Lemma 6.2). The number of chambers met is almost surely constant (§6.1). $\mathbb P[0\in\operatorname{conv}(S_1..S_{n-1})]=\frac2{n!}({n\brack d+2}+{n\brack d+4}+\dots)$ (Theorem 2.1) | $\lvert\mathcal W(L)\rvert=M_{N,d}$ almost surely, for bridges. The chamber–absorption dictionary of §7.3 | Exact (probabilistic factor) |
| K4 | Kabluchko, Vysotsky, Zaporozhets, *Convex hulls of random walks: expected number of faces and face probabilities*, Adv. Math. 320 (2017) 595–629, doi:10.1016/j.aim.2017.09.002, arXiv:1612.00249 | Theorem 1.2 | $\mathbb E f_k(\operatorname{conv}(S_0..S_n))=\frac{2\,k!}{n!}\sum_{l}{n+1\brack d-2l}{d-2l\brace k+1}$ for exchangeable increments in general position | With $k=0$ this is **equivalent to the $x^1$ and $x^{N-1}$ coefficients of C2** (§5.3) | Partial: two coefficients |
| K5 | T. Godland, Z. Kabluchko, *Conical tessellations associated with Weyl chambers*, Trans. AMS (2021), doi:10.1090/tran/8445, arXiv:2004.10466 | Theorem 1.1; Theorem 2.16; Proposition 1.12; Theorems 1.5–1.6 | Under (A1), the tessellation of $\mathbb R^d$ by the hyperplanes $(y_i-y_j)^\perp$, whose cones are the *projection orders* $\{v:\langle v,y_{\sigma(1)}\rangle\le\dots\}$, has $2({n\brack n-d+1}+{n\brack n-d+3}+\dots)$ cones (Theorem 1.1). (A1) is equivalent to genericity (Theorem 2.16). A uniform random cone, under exchangeability, has the law of the fixed-label cone conditioned on being non-trivial (Proposition 1.12). Expected face numbers and conic intrinsic volumes of the uniform cone (Theorems 1.5–1.6) | Applied to the affine Gale diagram $p_1..p_N\in\mathbb R^{N-d-1}$, Theorem 1.1 is (6). Proposition 1.12 is the averaging device behind (7). Descent statistics of the uniform cone are **not** computed | Exact (factor $M$); same method |
| K6 | Z. Kabluchko, H. Panzo, *A refinement of the Sylvester problem: probabilities of combinatorial types*, Discrete Comput. Geom. (2026), doi:10.1007/s00454-026-00820-2, arXiv:2501.16166 | Theorem 3.17 (and Theorem 4.5 for positive hulls) | For an exchangeable walk with $d+1$ increments, $\mathbb P[\text{type }T^d_m]=\eta_{d,m}A(d+1,m)/(d+1)!$. The proof is via K4 and an Eulerian identity, not Gale duality | The $N=d+2$ case of C2 (§10) | Exact for $N=d+2$ only |
| K7 | X. Barysheva, `sylvester_radon.pdf` (attached; from the author's thesis) | Theorem 1.4; Lemmas 4.2, 4.3, 4.4; Step 3 of the proof; Corollary 4.7 | The Eulerian law of $\tau$ via the circular representation $g_i=G_i-G_{i+1}$; ties excluded by exchangeability; cyclic Eulerian count; averaging over the stabiliser of one index | The $N=d+2$ case of every step of the proof below. Lemma 4.2 is the $N=d+2$ case of §6 | Exact for $N=d+2$ |
| K8 | J. Fulman, *Affine shuffles, shuffles with cuts, the Whitehouse module, and patience sorting*, J. Algebra 231 (2000) 614–639, doi:10.1006/jabr.2000.8339; T. K. Petersen, *Cyclic descents and P-partitions*, J. Algebraic Combin. 22 (2005) 343–375, doi:10.1007/s10801-005-4532-5, arXiv:math/0405479 | Fulman Cor. 1; Petersen Prop. 1.1 | $\sum_{\pi\in S_n}t^{\operatorname{cdes}\pi}=n\,t\,A_{n-1}(t)$, in Petersen's normalisation $A_{n-1}(t)=\sum t^{\operatorname{des}+1}$, together with invariance of cdes under cyclic rotation | Identities (4)–(5) | Exact (Eulerian factor) |
| K9 | Zaporozhets, `random_permutations_lectures_1-4.pdf` | Theorem 2.17; Theorem 2.26 | Number of chambers meeting a convex set = number of cycle subspaces meeting it; absorption identity | Route A to (6), with the correction of §7.1 | Ingredient |
| K10 | T. Zaslavsky, *Facing up to arrangements*, Mem. AMS 154 (1975), doi:10.1090/memo/0154; R. Stanley, *An introduction to hyperplane arrangements* (IAS/Park City Math. Ser. 13, 2007), Theorem 2.5 | — | $\#\text{regions}=(-1)^{\mathrm{rk}}\chi(-1)$ | Route B (§7.2) | Ingredient |
| K11 | D. Hug, R. Schneider, *Random conical tessellations*, Discrete Comput. Geom. 56 (2016) 395–426; T. Cover, B. Efron, Ann. Math. Statist. 38 (1967) 213–220 | — | Uniform-cell averaging for generic central arrangements; counting orthants met by a generic subspace | Origin of the averaging device | Related |
| K12 | J. E. Goodman, R. Pollack, *On the combinatorial classification of nondegenerate configurations in the plane*, J. Combin. Theory Ser. A 29 (1980) 220–235, doi:10.1016/0097-3165(80)90011-4 | allowable sequences | A nondegenerate planar configuration of $N$ points has a periodic sequence of $2\binom N2$ projection orders | For $N=d+3$ (planar Gale diagram) this gives $M_{N,N-3}=2{N\brack N-1}=N(N-1)$ directly | Exact for $N=d+3$ |
| K13 | M. Develin, M. Macauley, V. Reiner, *Toric partial orders*, Trans. AMS 368 (2016) 2263–2287, arXiv:1211.4247 | — | Chambers of the toric braid arrangement correspond to cyclic classes of total orders | Explains why the cyclic statistic is natural. Does not imply C2 | Related only |
| K14 | O. Barndorff-Nielsen, G. Baxter, *Combinatorial lemmas in higher dimensions*, Trans. AMS 108 (1963) 313–325, doi:10.1090/S0002-9947-1963-0156261-1 | (full text not retrieved) | According to KVZ (Adv. Math. 2017, §1.1), it computes the probabilities of facets (faces of maximal dimension) | Not related to the chamber-descent statistic | Related only (secondary source) |
| K15 | Z. Kabluchko, *Random polyhedral cones I: distributional results via Gale duality*, arXiv:2602.08581 | §2 (Gale coupling) | Gale-dual coupling for i.i.d. uniform directions; spherical Sylvester problem | No Weyl chambers, walks or descents (checked by full-text search) | Not related |

### 2.1 Search log (formulations covered)

Full texts were downloaded and searched for: K1, K4, K5, K6, K8 (Petersen), K15, and also
Kabluchko–Vysotsky–Zaporozhets, *A multidimensional analogue of the arcsine law…* (Bernoulli
2019, arXiv:1610.02861); Godland–Kabluchko, *Conic intrinsic volumes of Weyl chambers*
(arXiv:2005.06205); Kabluchko, *An identity for the coefficients of characteristic polynomials
of hyperplane arrangements* (DCG 2021, arXiv:2008.06719); and Iksanov–Kabluchko–Marynych–Wachtel,
*Multinomial random combinatorial structures and r-versions of Stirling, Eulerian and Lah
numbers* (arXiv:2403.16448). None of these contains a descent or cyclic-descent statistic of
chambers met by a subspace.

All 41 works that cite KVZ GAFA 2017 (according to OpenAlex) were screened by title. The
relevant ones are already in the table. Queries run on arXiv and OpenAlex include "braid
arrangement generic subspace Eulerian", "cyclic descent enumerator chambers braid
arrangement", "restricted braid arrangement Stirling", "Weyl chambers intersected subspace
Stirling", "random walk Gale dual cyclic", "Weyl chamber conic intrinsic volumes Stirling",
"oriented matroid random relabeling", "toric braid arrangement cyclic descents", "projection
orders Eulerian", "Radon partitions random walk", "allowable sequences circular permutations
Eulerian", "chamber weighted Radon partitions", "Eulerian numbers random walk convex hull" and
"descents Weyl chambers random subspace". No hit states C2 or an equivalent.

The formulations listed in the prompt map onto sources as follows:

| Formulation | Where covered |
|---|---|
| Generic subspaces and braid chambers; characteristic polynomials of restrictions | K1, K10 |
| Conic intrinsic volumes and Grassmann angles of type-A chambers | arXiv:2005.06205; K1 §4 |
| Random-walk absorption | K1 Theorem 2.1, K9 Theorem 2.26 |
| Gale transforms of walks | K7, K15 |
| Projection orders and allowable sequences | K5, K12 |
| Toric and cyclic structures | K8, K13 |
| Oriented-matroid relabelling | no hits beyond K5 Proposition 1.12 |
| Cycle-index formulas with Stirling and Eulerian numbers | K6, arXiv:2403.16448 |

---

## 3. Corrected statement of C2

Let $a=(a_1,\dots,a_N)\in(\mathbb R^d)^N$ with $\sum a_i=0$, write $s_k=a_1+\dots+a_k$,
$L=L(a)=\{t:\sum t_ia_i=0\}$, and define $\mathcal W(L)$ (open chambers met), $D(w)$ and $H_L$
as in the prompt.

**Theorem A (deterministic; no assumptions).** For *every* subset $L\subseteq\mathbb R^N$,
$$\frac1{N!}\sum_{\sigma\in S_N}H_{\sigma L}(x)=\lvert\mathcal W(L)\rvert\,\frac{xA_{N-1}(x)}{(N-1)!},
\qquad
\frac1{(N-1)!}\sum_{\sigma\in S_N,\ \sigma(N)=N}H_{\sigma L}(x)=\lvert\mathcal W(L)\rvert\,\frac{xA_{N-1}(x)}{(N-1)!}.$$

**Theorem B (chamber count).** If $\operatorname{rank}(a)=d$, $N\ge d+2$, and $L/\mathbb R\mathbf1$
is in general position with respect to the braid arrangement (condition (G) of §4), then
$\lvert\mathcal W(L)\rvert=M_{N,d}$. Without (G), $\lvert\mathcal W(L)\rvert\le M_{N,d}$ still holds.

**Theorem C (C2, corrected).** Assume one of the following:

* **(bridge)** $(a_1,\dots,a_N)$ is exchangeable, $\sum a_i=0$ almost surely, and the points
  are in general position almost surely;
* **(walk)** $X_1,\dots,X_{N-1}$ are exchangeable, $a=(X_1,\dots,X_{N-1},-S_{N-1})$, and the
  points $S_0=0,S_1,\dots,S_{N-1}$ are in general position almost surely.

Here $N\ge d+2$, and "general position" can be weakened to "any $d$ of $S_1,\dots,S_{N-1}$ are
linearly independent almost surely". Then
$$\boxed{\ \mathbb E\,H_L(x)=M_{N,d}\,\frac{xA_{N-1}(x)}{(N-1)!}\ }$$
More strongly, conditionally on the unordered data (the multiset of steps for bridges, or of
increments for walks), $H_L$ averages to the same polynomial. Equivalently, a uniformly chosen
met chamber satisfies $\mathbb P(D=k)=A(N-1,k-1)/(N-1)!$ for $1\le k\le N-1$. The law of $D$
is the same as that of $1+\operatorname{des}$ of a uniform permutation of $N-1$ letters.

**What was changed relative to the prompt.**

* The deterministic identity holds for every $L$ (Theorem A). Only the value of
  $\lvert\mathcal W(L)\rvert$ needs genericity, and genericity is condition (G), not general
  position.
* For a single *fixed* closed walk in general position, $\lvert\mathcal W(L)\rvert=M_{N,d}$ can
  fail (§4.2). The probabilistic statement is unaffected, because exchangeability makes (G)
  hold almost surely.
* For ordinary walks no cyclic-shift argument is needed. The stabiliser average already equals
  the full average (Theorem A, second identity).

---

## 4. Minimal assumptions

### 4.1 The arrangement-genericity condition (G)

The flats of the braid arrangement are $F_\pi=\{t:\ t\text{ constant on the blocks of }\pi\}$,
where $\pi$ is a set partition of $[N]$ into $b$ blocks; $\dim F_\pi=b$. Writing
$t=\sum_B c_B\mathbf 1_B$ gives
$$L\cap F_\pi\cong\{c\in\mathbb R^b:\ \textstyle\sum_B c_B\,a_B=0\},\qquad a_B=\sum_{i\in B}a_i,$$
so $\dim(L\cap F_\pi)=b-\operatorname{rank}(a_B)_{B\in\pi}$. Since $\sum_Ba_B=0$, the rank is at
most $\min(b-1,d)$.

**(G)** For every set partition $\pi$ of $[N]$ into $b$ blocks,
$\operatorname{rank}\{a_B:B\in\pi\}=\min(b-1,d)$. Equivalently,
$\dim(L\cap F_\pi)=\max(1,b-d)$, or $\dim\big((L\cap F_\pi)/\mathbb R\mathbf1\big)=\max(0,b-1-d)$.

This is exactly the general-position condition (29) of K1 for the subspace $L\cap\mathbf1^\perp$,
which has codimension $d+1$ in $\mathbb R^N$. For the affine Gale diagram it is the condition
(A1)/(A2) of K5, Theorem 2.16.

### 4.2 General affine position does not imply (G)

**Counterexample 1 (square, N = 4, d = 2).** Take steps $a=(e_1,e_2,-e_1,-e_2)$. The points
$(1,0),(1,1),(0,1),(0,0)$ have no three collinear. But $a_1+a_3=0$, so (G) fails for
$\pi=\{\{1,3\},\{2,4\}\}$. Indeed $L=\{t_1=t_3,\ t_2=t_4\}$ meets **no** open chamber, so
$H_L=0$ while $M_{4,2}=2$. This is machine-checked as `chamberSet_square`. It is the
4-point analogue of the trapezoid that Barysheva mentions before Lemma 4.3. The Radon partition
here is the pair of diagonals, $\{s_1,s_3\}\mid\{s_2,s_4\}$, and it is induced by no chamber.

**Counterexample 2 (N = 5, d = 2, with chambers present).** Take steps
$a=\big((1,0),(-\tfrac12,\tfrac32),(0,1),(\tfrac32,-\tfrac12),(-2,-2)\big)$, with points
$(1,0),(\tfrac12,\tfrac32),(\tfrac12,\tfrac52),(2,2),(0,0)$. No three of these are collinear;
this was checked by hand, and also by exact rational arithmetic. We have
$a_1+a_3=a_2+a_4=(1,1)$ and $a_5=-2(1,1)$. Hence $t=(\alpha,\beta,\alpha,\beta,\gamma)\in L$
if and only if $\alpha+\beta=2\gamma$, so $(L\cap F_\pi)/\mathbb R\mathbf1\ne0$ for
$\pi=\{\{1,3\},\{2,4\},\{5\}\}$. Inside the plane $V=L/\mathbb R\mathbf1$, the two lines
$V\cap\{t_1=t_3\}$ and $V\cap\{t_2=t_4\}$ therefore coincide. A central arrangement of at most
9 distinct lines in a plane has at most 18 regions, so $\lvert\mathcal W(L)\rvert\le18<20=M_{5,2}$.
An exact rational computation, which is not part of the proof, finds exactly 9 distinct lines,
so $\lvert\mathcal W(L)\rvert=18$.

### 4.3 When (G) holds almost surely

| Assumption | Does it imply (G) almost surely? |
|---|---|
| General affine position only (deterministic) | **No** (§4.2) |
| (NT) of `RESEARCH_MAP.md` (pairwise distinct projections for generic functionals) | **No.** It only gives $L/\mathbb R\mathbf1\not\subset\{t_i=t_j\}$, which is the codimension-1 part of (G). Counterexample 2 satisfies (NT) and violates (G) |
| Exchangeable bridge, any $d$ of $S_1..S_{N-1}$ linearly independent almost surely | **Yes**: K1, Lemma 6.2 |
| Exchangeable walk increments $X_1..X_{N-1}$, any $d$ of $S_1..S_{N-1}$ linearly independent almost surely | **Yes** (proof below) |
| i.i.d. increments with a density, or more generally independent increments satisfying the hyperplane condition (Hy) | **Yes**: these give exchangeability plus general position (Lemma 4.1 of `sylvester_radon.pdf`; K1, Proposition 2.5) |

*Proof for walks.* Let $B^\ast$ be the block containing the closing index $N$. Then
$a_{B^\ast}=-\sum_{B\ne B^\ast}a_B$, so the rank equals that of the $b-1$ sums of $X$ over
disjoint non-empty subsets of $[N-1]$. By exchangeability of $(X_1,\dots,X_{N-1})$, their
joint law equals that of the sums over consecutive initial intervals
$(0,i_1],(i_1,i_2],\dots,(i_{b-2},i_{b-1}]$, which are
$S_{i_1},S_{i_2}-S_{i_1},\dots$. These span $\operatorname{span}(S_{i_1},\dots,S_{i_{b-1}})$,
which has dimension $\min(b-1,d)$ almost surely. There are finitely many partitions. $\square$

The bridge case is the same argument with all $N$ steps exchangeable (K1, Lemma 6.2). Under
exchangeability, the weak condition "any $d$ of $S_1..S_{N-1}$ linearly independent" is
equivalent to full general position almost surely, by the same interval reduction.

### 4.4 Open versus closed chambers, and the dimension convention

If $\operatorname{rank}(a)=d$ then $\dim L=N-d$ and $\dim(L/\mathbb R\mathbf1)=N-d-1$.

Under (G), a closed chamber $K_w$ satisfies $K_w\cap L\supsetneq\mathbb R\mathbf1$ if and only
if $K_w^\circ\cap L\ne\varnothing$. This is K1, Lemma 3.5, eq. (36), applied in the quotient.
Without (G), closed chambers can meet $L$ non-trivially while their interiors miss it:
Counterexample 1 gives $\mathcal W(L)=\varnothing$ even though $L/\mathbb R\mathbf1\ne0$
lies in some closed chambers. $D(w)$ is defined only through open chambers, since points on
walls have ties. The two notions are therefore **not** interchangeable without (G).

---

## 5. Deterministic relabelling lemma

### 5.1 $D(w)$ is well defined

$t\in K_w^\circ$ means $t_{w(1)}<\dots<t_{w(N)}$. The rank vector of $t$ is $w^{-1}$, since
the coordinate $t_i$ is the $w^{-1}(i)$-th smallest. Hence $t_i>t_{i+1}\iff w^{-1}(i)>w^{-1}(i+1)$,
so
$$D(w)=\operatorname{cdes}(w^{-1})\quad\text{for every }t\in K_w^\circ.$$
This is machine-checked as `cyclicDescents_eq_cdes_inv`.

### 5.2 Gale/Radon meaning of $D(w)$ (Section III.4 of the prompt)

For $t\in\mathbb R^N$ put $\lambda_i=t_i-t_{i+1}$, with $t_{N+1}=t_1$ and $s_0=s_N$. Then
$$\sum_i\lambda_i=0,\qquad \sum_i\lambda_is_i=\sum_it_i(s_i-s_{i-1})=\sum_it_ia_i.$$
This is machine-checked as `gale_identity`. The kernel of $t\mapsto\lambda$ is
$\mathbb R\mathbf1$. If the points affinely span $\mathbb R^d$, both $L/\mathbb R\mathbf 1$
and the space of affine dependences have dimension $N-d-1$. So $t\mapsto\lambda$ is a linear
**bijection from $L/\mathbb R\mathbf1$ onto the affine dependences** of $s_1,\dots,s_N$.

For $t\in K_w^\circ$, all $\lambda_i\ne0$, so $\lambda$ is a full-support dependence and
$\big(\{s_i:\lambda_i>0\},\{s_i:\lambda_i<0\}\big)$ is a *complete oriented Radon partition*,
with $D(w)=\#\{i:\lambda_i>0\}$.

* **Every complete oriented Radon partition arises, under (G).** Its set of realising
  dependences is a non-empty open cone in $L/\mathbb R\mathbf1$. By (G), no hyperplane
  $t_i=t_j$ contains $L/\mathbb R\mathbf1$, so the cone contains points with all coordinates
  distinct, which lie in some open chamber. Without (G) this can fail (Counterexample 1).
* **Several chambers can induce the same oriented partition.** The cone of a fixed sign
  pattern of $\lambda$ is cut further by the hyperplanes $t_i=t_j$ with $|i-j|\ge2$
  (cyclically). For example, at $N=5,d=2$ there are 20 chambers, but at most $2\cdot5=10$
  oriented complete partitions (10 exactly when no two linear Gale vectors are parallel).
* **The exception is a part of size 1, which is realised by exactly one chamber.** If
  $\lambda_i>0$ and $\lambda_j<0$ for all $j\ne i$, then
  $t_{i+1}<t_{i+2}<\dots<t_i$ cyclically, a complete order. Hence

  $$[x^1]H_L=[x^{N-1}]H_L=N_1:=\#\{i:\ s_i\in\operatorname{int}\operatorname{conv}(s_j:j\ne i)\}$$

  for every configuration in general position. This uses only that $s_i$ is interior if and
  only if a strictly positive affine representation exists, which holds in general position.
* **Opposite chambers.** $t\mapsto-t$ maps $K_w^\circ$ onto $K_{ww_0}^\circ$, with $w_0$ the
  reversal, and $D(ww_0)=N-D(w)$. Hence $H_L(x)=x^NH_L(1/x)$: a chamber and its opposite give
  the two orientations of the same unordered partition.

### 5.3 The coefficient of $x$ and the known vertex formula

By the last two items and Theorem C,
$$\mathbb E N_1=\frac{M_{N,d}}{(N-1)!},\qquad\text{i.e.}\qquad
\mathbb E f_0(\operatorname{conv})=N-\frac{2\sum_{r}{N\brack d+2+2r}}{(N-1)!}=\frac{2\sum_r{N\brack d-2r}}{(N-1)!}.$$
The last equality uses $\sum_{k\equiv d\,(2)}{N\brack k}=N!/2$. This is exactly K4,
Theorem 1.2 with $k=0$ and $n+1=N$. So the extreme coefficients of C2 are a known theorem. At
$N=5,d=2$: $\mathbb EN_1=20/24=5/6$, which matches the distribution-free value of $\mathbb EN_1$
used as a premise and the two Lean-checked five-point examples in `FivePointBridge.lean`.

### 5.4 The relabelling identity and its proof

Let $(\sigma t)_i=t_{\sigma^{-1}(i)}$ and $\sigma L=\{\sigma t:t\in L\}$. Then
$\sigma L=L(a\circ\sigma^{-1})$, since $\sum_i t_{\sigma^{-1}(i)}a_{\sigma^{-1}(i)}=\sum_jt_ja_j$:
it is the dependency space of the relabelled steps.

1. **Bijection.** $t\in K_w^\circ\iff\sigma t\in K_{\sigma w}^\circ$, because
   $(\sigma t)_{\sigma w(j)}=t_{w(j)}$. So $w\mapsto\sigma w$ is a bijection
   $\mathcal W(L)\to\mathcal W(\sigma L)$. Machine-checked as `chamberSet_relabel`.
2. **The rank word becomes uniform.** The chamber $\sigma w$ of $\sigma L$ has
   $D=\operatorname{cdes}((\sigma w)^{-1})=\operatorname{cdes}(w^{-1}\sigma^{-1})$. For fixed
   $w$, the map $\sigma\mapsto w^{-1}\sigma^{-1}$ is a bijection of $S_N$. So under a uniform
   relabelling, the rank word of a fixed chamber is a uniform permutation.
3. **Summation.**
   $$\sum_{\sigma}H_{\sigma L}(x)=\sum_{w\in\mathcal W(L)}\sum_{\sigma}x^{\operatorname{cdes}(w^{-1}\sigma^{-1})}
   =\lvert\mathcal W(L)\rvert\sum_{\pi\in S_N}x^{\operatorname{cdes}\pi}
   =\lvert\mathcal W(L)\rvert\,N\,x\,A_{N-1}(x),$$
   using (5) below. Dividing by $N!$ gives (3).
4. **Conventions.** Because the sum is over all of $S_N$, the identity does not depend on
   whether permutations act on the left or right, or on whether one uses $w$ or $w^{-1}$.
   Replacing descents by ascents would also give the same answer, by Eulerian symmetry. The
   Lean statement fixes one convention ($(\sigma t)=t\circ\sigma^{-1}$, $D(w)=\operatorname{cdes}w^{-1}$)
   and checks it exactly. In the stabiliser version below, the convention genuinely matters,
   and it is checked there too.
5. **Stabiliser version (ordinary walks).** Average only over $\sigma$ with $\sigma(p)=p$, where
   $p$ is the position of the closing increment. For fixed $w$, the map $\sigma\mapsto w^{-1}\sigma^{-1}$
   is a bijection onto $\{\pi:\pi(p)=w^{-1}(p)\}$. Now cdes is invariant under cyclic rotation
   of positions, $\pi\mapsto\pi\circ(i\mapsto i+j)$, and each rotation class (of size $N$)
   meets $\{\pi:\pi(p)=r\}$ exactly once. Hence
   $N\sum_{\pi(p)=r}x^{\operatorname{cdes}\pi}=\sum_\pi x^{\operatorname{cdes}\pi}$ for every
   $r$, and
   $$N\sum_{\sigma(p)=p}H_{\sigma L}(x)=\lvert\mathcal W(L)\rvert\sum_{\pi}x^{\operatorname{cdes}\pi}.$$
   This is the precise form of "each circular ordering has a unique representative with the
   closing increment in a prescribed position".

Identity (3) holds **for every subset $L\subseteq\mathbb R^N$**, linear or not, and with no
genericity, provided $\mathcal W(L)$ uses open chambers.

**Machine-checked (`RequestProject/ChamberEulerian.lean`).**

| Lean theorem | Content |
|---|---|
| `sum_radonPoly_relabel` | $\sum_\sigma H_{\sigma L}=\lvert\mathcal W(L)\rvert\sum_\pi X^{\operatorname{cdes}\pi}$ for any $L\subseteq\mathbb R^N$ |
| `sum_radonPoly_relabel_stab` | $N\sum_{\sigma(p)=p}H_{\sigma L}=\lvert\mathcal W(L)\rvert\sum_\pi X^{\operatorname{cdes}\pi}$ |
| `sum_X_pow_cdes` | $\sum_{\pi\in S_N}X^{\operatorname{cdes}\pi}=N\cdot X\cdot\sum_{\sigma\in S_{N-1}}X^{\operatorname{des}\sigma}$ |
| `card_cdes_eq` | $\#\{\pi\in S_N:\operatorname{cdes}\pi=k+1\}=N\cdot A(N-1,k)$ |
| `cyclicDescents_eq_cdes_inv` | $D(w)$ is well defined (§5.1) |
| `gale_identity` | The telescoping identity of §5.2 |
| `chamberSet_square` | Counterexample 1 |
| `chamberCount` checks (by `decide`) | $M_{3,1}=2$, $M_{4,2}=2$, $M_{5,2}=20$, $M_{6,3}=30$, $M_{6,2}=172$ |

**Not formalised:** the chamber count (Theorem B) and all probabilistic statements.

In the Lean file, positions are $0,\dots,N-1$ read cyclically. The distinguished position in
the stabiliser version is an arbitrary $p$, so it covers "the closing increment in the last
position".

**Novelty of (3).** No explicit statement was found. It is the cyclic Eulerian identity (K8)
transported by a reindexing, and the averaging device is that of K5, Proposition 1.12.

---

## 6. Cyclic Eulerian enumeration

**(4)** $\#\{w\in S_N:\operatorname{cdes}(w)=k\}=N\,A(N-1,k-1)$ for $1\le k\le N-1$ and
$N\ge2$. Also, $\operatorname{cdes}=0$ never occurs.

*Proof.* Cyclic rotation of positions preserves cdes and acts freely, with orbits of size $N$.
Each orbit contains exactly one word with the letter $1$ in position 1 (or, equally, the letter
$N$ in position $N$). For $w=1\,u$, where $u$ is a word in $\{2..N\}$, the step $1\to u_1$ is an
ascent and the wrap-around step $u_{N-1}\to1$ is a descent. So
$\operatorname{cdes}(w)=\operatorname{des}(u)+1$. $\square$ This is Fulman 2000, Cor. 1, and
Petersen 2005, Prop. 1.1. The Lean proof (`cdes_decomposeFin`, `sum_X_pow_cdes`) follows exactly
this route, with the representative $\pi(0)=0$.

**(5)** $\displaystyle\frac1{N!}\sum_{w\in S_N}x^{\operatorname{cdes}w}=\frac{N\,xA_{N-1}(x)}{N!}=\frac{xA_{N-1}(x)}{(N-1)!}.$

Sanity values, checked by `decide` in Lean: $\#\{\operatorname{des}=1\}$ in $S_3$ is $4$;
$\#\{\operatorname{cdes}=2\}$ in $S_4$ is $16=4\cdot4$; $\#\{\operatorname{cdes}=2\}$ in $S_5$
is $55=5\cdot11$.

---

## 7. Chamber-count theorem

**Theorem B.** Let $\operatorname{rank}(a)=d$, $N\ge d+2$, and assume (G). Then
$\lvert\mathcal W(L)\rvert=M_{N,d}=2\sum_{r\ge0}{N\brack d+2+2r}$.

### 7.1 Route A (Theorem 2.17): valid only with a correction term

Let $V=L\cap\mathbf1^\perp\cong L/\mathbb R\mathbf1$, with $m=\dim V=N-d-1$. For generic
$u\in V^\ast$, let $Q_u=V\cap\{\langle u,\cdot\rangle=1\}$.

* **Cycle side.** For $\sigma$ with cycle set $C(\sigma)$, write $t=\sum_\gamma c_\gamma\mathbf1_\gamma$.
  Then $F_\sigma\cap V\cong\{c:\sum_\gamma c_\gamma(a_\gamma,|\gamma|)=0\}$; this uses the
  lifted cycle sums of the proof of Theorem 2.26. Under (G),
  $\dim(F_\sigma\cap V)=\max(0,C(\sigma)-d-1)$. For $u$ outside the finitely many
  annihilators, $F_\sigma\cap Q_u\ne\varnothing$ if and only if $F_\sigma\cap V\ne0$, if and
  only if $C(\sigma)\ge d+2$. Both genericity of $V$ and genericity of $u$ are needed here. So
  $B_N(Q_u)=\sum_{k\ge d+2}{N\brack k}$.
* **Chamber side.** By Theorem 2.17, $A_N(Q_u)=B_N(Q_u)$. Under (G), a closed chamber meets
  $Q_u$ exactly when its region $R=K_w^\circ\cap V$ has $u>0$ somewhere: by K1 (36),
  $K_w\cap V=\overline R$.
* **The naive doubling is false.** A region can carry both signs of $u$. Let $r_m$ be the
  number of regions of a generic $m$-dimensional section. Using the symmetry $R\mapsto-R$, and
  the fact that $u$ changes sign on $R$ exactly when $u^\perp$ meets $R$,
  $$r_m=2A_N(Q_u)-r_{m-1}=2\sum_{k\ge N-m+1}{N\brack k}-r_{m-1},\qquad r_0=0.$$
  Here $r_{m-1}$ refers to $V\cap u^\perp$, which is again generic for generic $u$. Solving the
  recursion gives $r_m=2\sum_{j\ge0}{N\brack N-m+1+2j}=M_{N,d}$.
  The smallest counterexample to plain doubling is $N=4,d=1$: plain doubling gives
  $2({4\brack3}+{4\brack4})=14$, but the correct count is $2{4\brack3}=12$. Plain doubling is
  correct only when $m=1$, i.e. $N=d+2$.

So Route A proves (6), but only after adding this alternating correction. It also needs K1,
Lemma 3.5, to pass between closed and open chambers.

### 7.2 Route B (Zaslavsky): the clean proof

Under (G), the map $X\mapsto X\cap V$ is an isomorphism from the braid flats of codimension
$<m$ (in the quotient) onto the flats of the restricted arrangement, and all deeper flats
collapse to $\{0\}$. This is K1, Lemma 3.1. Since
$\chi_{\text{braid}}(q)=(q-1)\cdots(q-N+1)=\sum_k(-1)^k{N\brack N-k}q^{N-1-k}$, Zaslavsky's
theorem gives
$$r_m=\sum_{k<m}{N\brack N-k}\big(1+(-1)^{m+1+k}\big)=2\sum_{\substack{k<m\\ k\equiv m+1\ (2)}}{N\brack N-k}=M_{N,d}.$$
Each region of the restriction lies in exactly one open chamber, and $K^\circ_w\cap V$ is
convex, hence connected. So regions correspond to chambers met. This is K1, Theorem 3.4,
applied to $L\cap\mathbf 1^\perp$, which has codimension $d+1$ in $\mathbb R^N$.

### 7.3 Absorption form, and what was already known

Writing $t_{w(j)}=t_{w(1)}+\sum_{k<j}\mu_k$ with $\mu>0$ gives
$\sum_it_ia_i=-\sum_{k<N}\mu_ks_k(w)$. So
$$K_w^\circ\cap L\ne\varnothing\iff 0\in\operatorname{relint}\operatorname{conv}\big(s_1(w),\dots,s_{N-1}(w)\big):$$
the base point of the reordered closed walk lies inside the hull of the other points. This is
the change of variables in K1, Lemma 6.1. For an exchangeable bridge, averaging therefore gives
$\mathbb P[0\in\operatorname{int}\operatorname{conv}(S_1..S_{N-1})]=\mathbb E\lvert\mathcal W(L)\rvert/N!$,
which is K1, Theorem 2.1, via eqs. (56)–(57).

Already known: (6) under (G), as K1 Theorem 3.4 and K5 Theorem 1.1, and (6) almost surely
under exchangeability and general position, as K1 Lemma 6.2 and §6.1. For $N=d+3$, (6) reads
$N(N-1)=2\binom N2$, the length of a full period of the Goodman–Pollack allowable sequence of
the planar Gale diagram (K12). Note that "nondegenerate" in K12 is exactly (G) for $m=2$: no
three Gale points collinear and no two connecting lines parallel.

---

## 8. Exchangeable bridge corollary

Let $(a_1,\dots,a_N)$ be exchangeable with $\sum a_i=0$ almost surely. For each $\sigma$,
$a\circ\sigma^{-1}$ has the same law as $a$, so $\mathbb E H_{L(a)}=\mathbb E H_{\sigma L(a)}$.
(The map $a\mapsto H_{L(a)}$ is measurable, since membership in $\mathcal W$ is a semialgebraic
condition on $a$.) Averaging and applying Theorem A gives
$$\mathbb E H_L(x)=\mathbb E\lvert\mathcal W(L)\rvert\cdot\frac{xA_{N-1}(x)}{(N-1)!}\tag{7}$$
**with no general-position assumption at all.**

The strongest form: let $\mathcal G$ be the $\sigma$-field of relabelling-invariant events.
For exchangeable $a$, $\mathbb E[F(a)\mid\mathcal G]=\frac1{N!}\sum_\sigma F(a\circ\sigma^{-1})$.
Since $\lvert\mathcal W\rvert$ is relabelling invariant,
$$\mathbb E[H_L(x)\mid\mathcal G]=\lvert\mathcal W(L)\rvert\,\frac{xA_{N-1}(x)}{(N-1)!}\quad\text{almost surely.}$$
Consequently, conditionally on $\mathcal W\ne\varnothing$, a uniformly chosen met chamber has
$\mathbb P(D=k)=A(N-1,k-1)/(N-1)!$, *even if the chamber count is random*. By K1 (38), $\lvert\mathcal W\rvert\le M_{N,d}$ whenever $\operatorname{rank}(a)=d$,
so $\mathbb E\lvert\mathcal W\rvert\le M_{N,d}$. Under general position almost surely
(or K1's weaker condition), (G) holds almost surely (§4.3), so
$\lvert\mathcal W(L)\rvert=M_{N,d}$ almost surely, which gives (C2).

## 9. Ordinary-walk corollary

Let $X_1,\dots,X_{N-1}$ be exchangeable and $a_N=-S_{N-1}$. The full $N$-tuple is not
exchangeable, but it is invariant in law under all $\sigma$ with $\sigma(N)=N$. By the
stabiliser identity (§5.4, item 5),
$$\mathbb E H_L(x)=\mathbb E\Big[\frac1{(N-1)!}\sum_{\sigma(N)=N}H_{\sigma L}(x)\Big]=\mathbb E\lvert\mathcal W(L)\rvert\frac{xA_{N-1}(x)}{(N-1)!},$$
and (G) holds almost surely by §4.3. So **(C2) holds verbatim for ordinary walks, with no
additional assumption.**

The cyclic-shift argument suggested in the prompt is valid but not needed. A cyclic shift of
the steps translates the point set and cyclically relabels $t$, which preserves $D$; this
gives one way to see the rotation invariance used above. The orbit–transversal fact (each
rotation class meets $\{\pi(N)=r\}$ exactly once) is the precise form in which it enters. No
obstruction remains.

## 10. Reduction to Theorem 1.4

Let $N=d+2$. Then $M_{N,d}=2{N\brack N}=2$, and under (G) the space $L/\mathbb R\mathbf1$ is a
line meeting exactly two opposite chambers $w$ and $ww_0$, with $D$ and $N-D$. These are the
two orientations $\pm g$ of the unique dual vector. In Barysheva's notation $g_i=G_i-G_{i+1}$
(Lemma 4.2). Writing her walk $S_1,\dots,S_{d+2}$ as our closed walk with steps
$(X_2,\dots,X_{d+2},-(X_2+\dots+X_{d+2}))$, one checks that $G$ equals $t-t_{d+2}\mathbf 1$
for some $t\in L$, up to the cyclic shift of indices that sends our position $d+2$ to her
index 1. Since cdes is invariant under rotation, $D$ is the number of cyclic descents of
$(G_1,\dots,G_{d+2})$, which is her $N_+$. Thus $H_L=x^D+x^{N-D}$, and with $\tau=\min(D,N-D)$:

* for $k<N/2$: $[x^k]H_L=\mathbf 1\{\tau=k\}$, so
  $\mathbb P(\tau=k)=[x^k]\,2xA_{N-1}(x)/(N-1)!=2A(N-1,k-1)/(N-1)!$;
* for $k=N/2$: $[x^k]H_L=2\cdot\mathbf 1\{\tau=k\}$, so $\mathbb P(\tau=k)=A(N-1,k-1)/(N-1)!$.

With $N-1=d+1$, this is Theorem 1.4. The points $S_1,\dots,S_{d+2}$ of Theorem 1.4 are a
translate of a walk with the $d+1$ exchangeable increments $X_2,\dots,X_{d+2}$, so §9 applies.

The four levels of description differ as follows:

| Level | Count | Notes |
|---|---|---|
| Chamber | $M_{N,d}$ in total | |
| Oriented Radon partition (tope) | one or more chambers each | exactly one when a part has size 1 |
| Unordered partition | 2 topes each | |
| $\tau$ (smaller part size) | — | forgets which points are involved |

At $N=d+2$ all levels except $\tau$ coincide up to the factor 2.

## 11. Low-dimensional checks (exact, no Monte Carlo)

| Case | $M_{N,d}$ | $\mathbb EH_L(x)$ | Remarks |
|---|---|---|---|
| $N=3,d=1$ | $2{3\brack3}=2$ | $2\cdot\frac{x(1+x)}{2}=x+x^2$ | Holds **deterministically**: three distinct points on a line, the middle one against the outer two, so $H_L=x+x^2$ always |
| $N=4,d=2$ | $2{4\brack4}=2$ | $\frac13x(1+4x+x^2)$ | $\mathbb P(\tau=1)=\frac13$ and $\mathbb P(\tau=2)=\frac12\cdot\frac43=\frac23$. These are $2A(3,0)/3!$ and $A(3,1)/3!$, the $d=2$ case of Theorem 1.4 (Sylvester's four-point problem for walks: convex position with probability $2/3$) |
| $N=5,d=2$ | $2{5\brack4}=20$ | $\frac{20}{24}x(1+11x+11x^2+x^3)$ | Expected numbers of met chambers with $D=1,2,3,4$: $\frac56,\frac{55}6,\frac{55}6,\frac56$ |

All values of $M_{N,d}$ here are checked by `decide` in the Lean file.

**Why the $N=5,d=2$ case does not make convex position universal.** Convex position means
$N_1=0$. By §5.2, $N_1=[x^1]H_L$ exactly, so C2 fixes only $\mathbb EN_1=5/6$, which is the
known distribution-free value. It says nothing about $\mathbb P(N_1=0)$.

The coefficients $[x^2]$ and $[x^3]$ count chambers, and several chambers can lie in one tope.
For example, the tope of an oriented $2\mid3$ partition with positive part $\{s_i,s_j\}$ is
cut by the hyperplanes $t_k=t_l$ between the two increasing runs of $t$. So these coefficients
are not partition counts either.

Concretely: the two exchangeable five-point bridges of `FivePointBridge.lean` have
convex-position probabilities $1/3$ and $1/4$. Both are in general position for every
ordering, so (G) holds for them (§4.3), and both satisfy C2. Their common value
$\mathbb EN_1=5/6$ is exactly what C2 predicts.

## 12. Novelty table

| Item | Classification | Justification |
|---|---|---|
| 1. Deterministic relabelling identity (3) | **Immediate corollary of a known theorem** | (4)–(5) (Fulman 2000, Cor. 1; Petersen 2005, Prop. 1.1) plus the reindexing $\sigma\mapsto w^{-1}\sigma^{-1}$. No explicit statement found. Same averaging device as Godland–Kabluchko 2021, Prop. 1.12. Holds for all $L$ (Lean-checked) |
| 2. Chamber count (6) | **Explicitly known with a precise citation** | KVZ GAFA 2017, Thm 3.4 (codimension $d+1$) and Lemma 6.2 / §6.1. Equivalently Godland–Kabluchko 2021, Thm 1.1. For $N=d+3$, Goodman–Pollack 1980 |
| 3. Probabilistic product formula (C2) | **Known ingredients, apparently new synthesis** | Exact statement not found in the sources of §2–§2.1. Its $x^1$ and $x^{N-1}$ coefficients are KVZ Adv. Math. 2017, Thm 1.2 ($k=0$). Its $N=d+2$ case is Theorem 1.4 / Kabluchko–Panzo, Thm 3.17 |
| 4. Gale–Radon interpretation of $D(w)$ | **Immediate corollary of a known theorem** | For $N=d+2$ it is Barysheva, Lemma 4.2. The general case is the same telescoping (Lean: `gale_identity`), and the dual change of variables is in KVZ GAFA, Lemma 6.1 |
| 5. A uniform met chamber has the cyclic Eulerian law | **Known ingredients, apparently new synthesis** | Equivalent to item 3 (and true conditionally even when the count is random). Godland–Kabluchko compute other functionals of the uniform cone, but not descents |
| 6. Reduction to Theorem 1.4 at $N=d+2$ | **Explicitly known with a precise citation** | Theorem 1.4 of `sylvester_radon.pdf`; Kabluchko–Panzo 2026, Thm 3.17; Panzo 2025 (arXiv:2409.07927) for $k=1$ |

"Apparently new" here means only that the statement was not found in the sources examined,
listed in §2.1. The synthesis is short (§5, §8, §9), and a referee could reasonably call it
folklore-level given K5 and K8.

## 13. Final status

**Proved, after a correction of hypotheses. As a combination of results it is mostly known; as
a single stated formula it appears unstated.**

* **(C2) is proved** for exchangeable bridges and for ordinary walks with exchangeable
  increments, under general position almost surely, or under the weaker condition that any
  $d$ of $S_1,\dots,S_{N-1}$ are linearly independent almost surely.
* **The deterministic version needs (G).** "General position of the points" is not enough:
  Counterexample 1 ($N=4$) gives $\mathcal W=\varnothing$, and Counterexample 2 ($N=5$) gives
  $\lvert\mathcal W\rvert=18<20$.
* **The first false step in the prompt's proposed route** is Route A's "slice and double": the
  doubled slice count overcounts by $r_{m-1}$. The smallest instance is $N=4,d=1$, with
  $14\ne12$.
* **What is new** is only the observation that the cyclic Eulerian factor and the Stirling
  chamber count combine by a one-line averaging argument (Theorem A). Everything else is in
  KVZ 2017, Godland–Kabluchko 2021, Fulman/Petersen, and Barysheva.
