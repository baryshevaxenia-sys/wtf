# Radon partitions of exchangeable random walks beyond $d+2$ points: a research map

*Built on:* `sylvester_radon.pdf` (Barysheva, Theorem 1.4) and
`random_permutations_lectures_1-4.pdf` (Zaporozhets, Theorems 2.13, 2.16, 2.17, 2.26).

---

## 0. Status of the evidence (please read first)

* **Machine-checked (Lean 4, no `sorry`):** `RequestProject/FivePointBridge.lean`. It
  checks exact counts over all orderings of two explicit integer step sets in
  $\mathbb Z^2$. These counts give two exchangeable 5-point planar walks (and bridges),
  both in general position almost surely, with convex-position probabilities exactly
  $1/3$ and $1/4$ and the same expected number of interior points, $5/6$. This is the
  counterexample used in §2.8, and it shows the two extreme values in Conjecture 4 are
  attained. The Lean file only checks the finite counts. The step from "a uniformly
  random ordering of a fixed step set" to "an exchangeable sequence" is the definition
  of exchangeability, and is not formalized.
* **Exploratory computation only (Python, in `experiments/`, not a proof):**
  every other number below: Monte Carlo values, the exhaustive runs over all
  768 (N=5) and 292,864 (N=6) simple allowable sequences, and the dimension counts.
  These results are called "evidence", never "verification".
* **Literature.** In this session I could not reach arXiv, MathSciNet, zbMATH or any
  other online database, so **no live search was run**. The novelty classifications
  below come from the bibliographies of the two documents and from my own knowledge of
  the literature. A reference is cited with full data only when I am confident of it.
  Where I am not confident, I say so and give a search string. Treat every "apparently
  open" as *provisional until checked* (step 1 of the plan in §5).
* The premises in the task are used as premises and are not re-proposed: at
  $n=d+3$ the convex-position probability is not universal; $\mathbb E N_m$ is
  distribution-free; expected face numbers are known.

---

## 1. Structural preliminaries (the lens used for every conjecture)

### 1.1 The Gale–polygon dictionary

Let $a_1,\dots,a_N\in\mathbb R^d$ with $a_1+\dots+a_N=0$ span $\mathbb R^d$. They are
the steps of a closed walk (a bridge) through the points $s_k=a_1+\dots+a_k$, where
$s_N=0$. An ordinary walk $S_0=0,S_1,\dots,S_n$ is the bridge with $N=n+1$ steps
$(X_1,\dots,X_n,-S_n)$. Since $\tau$ is translation invariant, this also covers the
normalization $S_1,\dots,S_{d+2}$ of Theorem 1.4.

Let $\widetilde L=\{t\in\mathbb R^N:\sum_i t_ia_i=0\}$. This space has dimension
$N-d$ and contains $\mathbf 1$. For every $t\in\widetilde L$,

$$\lambda_k:=t_k-t_{k+1}\ (\text{indices mod }N)\quad\Longrightarrow\quad
\sum_k\lambda_k s_k=\sum_k t_k a_k=0,\qquad \sum_k\lambda_k=0,$$

and $t\mapsto\lambda$ is a bijection from $\widetilde L/\mathbb R\mathbf 1$ onto the
space of affine dependences of $s_1,\dots,s_N$. Now write $t_i=\langle u,p_i\rangle+c$,
where $p_1,\dots,p_N\in\mathbb R^{N-d-1}$ is the **affine Gale diagram of the step
vectors**. This gives:

> **Dictionary.** The linear Gale vectors of the point set $\{s_k\}$ are the *edge
> vectors* $p_k-p_{k+1}$ of the closed polygon $p_1\to p_2\to\dots\to p_N\to p_1$.
> The complete Radon partitions of $\{s_k\}$ correspond to the generic linear
> functionals $u$. The Radon partition of $u$ is the (cyclic descents, cyclic ascents)
> pattern of the cyclic sequence $(\langle u,p_1\rangle,\dots,\langle u,p_N\rangle)$
> read in walk order. For a walk, $P=\{q_1,\dots,q_n\}\cup\{0\}$, where the $q_i$ are
> the linear Gale vectors of the increments.

For $N=d+2$ the $p_i$ are real numbers, and this is exactly Lemma 4.2 of
`sylvester_radon.pdf`: the cyclic ascents of $(0,G_2,\dots,G_{d+2})$. For $N=d+3$ the
$p_i$ are **planar points**. As $u$ rotates, the projection order of $P$ runs through
the Goodman–Pollack *circular sequence* (allowable sequence) of $P$. This is a
periodic sequence of permutations in which each half-period is a reduced word of the
longest permutation $w_0\in S_N$. So the whole Radon structure of the walk is a
function of (circular sequence of $P$, labeling). This is **finer than the order type
of $P$** (a regular pentagon, which has parallel lines, is not generic).
*Evidence:* the dictionary was checked against a direct primal computation for 300
random 5-point planar bridges, with 0 mismatches (`experiments/check1.py`).

### 1.2 What exchangeability buys: uniform labels, and walk = bridge

If the steps are exchangeable, the labeled Gale diagram is invariant in law under
relabeling. Given the unlabeled data, the labels are therefore uniform, over $S_N$
for bridges and over the stabilizer of the closing point for walks. A cyclic shift of
the bridge steps only translates the point set. Hence for a *fixed* unlabeled Gale
diagram, the walk average equals the full $S_N$ average. This is the structural reason
why Theorem 1.4 covers walks and bridges with the same formula. It also shows that,
at a fixed Gale diagram, walks and bridges can only differ through the **law of the
unlabeled Gale data**.

### 1.3 Where Theorem 2.17 enters: the chambers met by the dependency space

A Weyl chamber $K_w\subset\mathbb R^N$ meets $\widetilde L$ in its interior exactly
when $w$ is a projection order of $P$. In primal terms, the bridge with steps reordered
by $w$ has its base point $s_N$ in the interior of the hull of the other points; this
is the event of Theorem 2.26. Apply Theorem 2.17 to the convex set

$$Q_u=\widetilde L\cap\mathbf 1^\perp\cap\{\langle u,t\rangle=1\}\qquad(u\text{ generic}).$$

Then $F_\sigma\cap Q_u\neq\emptyset$ holds if and only if the **lifted cycle sums**
$(a_\gamma,|\gamma|)\in\mathbb R^{d+1}$, $\gamma\in C(\sigma)$, are linearly dependent.
This is the same lifting as in the proof of Theorem 2.26. Generically it happens if
and only if $C(\sigma)\ge d+2$. Hence

$$A_N(Q_u)=B_N(Q_u)=\sum_{k\ge d+2}{N\brack k}\quad\text{(one side)},\qquad
\#\{\text{chambers met}\}=2\sum_{j\ge0}{N\brack d+2+2j}.$$

The second formula is Zaslavsky's count for a generic subspace, and it is consistent
with Kabluchko–Vysotsky–Zaporozhets (GAFA 2017). Checks: $N=d+2$ gives $2$ chambers
($\pm G$). $N=d+3$ gives $2{N\brack N-1}=N(N-1)$, and one side gives
$1+\binom N2$. A sampling run for $N=6,d=2$ found 167 of the predicted 172 chambers;
sampling misses thin chambers.

**Moral.** Theorem 2.17 controls *how many* chambers (projection orders) there are,
and this count is universal. Lemma 4.4 (cyclic ascents) controls the *Radon type of
each chamber* under random labels, and this is also universal. What is **not**
universal at $N\ge d+3$ is how different chambers are *glued together*: how many
projection orders fall into the same cyclic class, and the relative permutations
between chambers. The conjectures below separate these three layers.

---

## 2. The conjectures

Notation: $N$ is the number of points; $A(m,j)$ are the Eulerian numbers and
$A_m(x)=\sum_j A(m,j)x^j$; ${N\brack k}$ are the unsigned Stirling numbers of the
first kind. $N_m$ is the number of complete Radon partitions with parts of sizes
$m$ and $N-m$; in particular $N_1$ is the number of points that are not vertices of the
hull. "GP" means general affine position. "(NT)" is the tie-exclusion assumption: for
every generic linear functional on the Gale space the projected values are pairwise
distinct almost surely. This is the analogue of Lemma 4.3, and it is automatic for
i.i.d. steps with a density.

### 2.1 Conjecture 1: the lifting principle (Eulerian law of a canonically selected Radon partition)

**Statement.** Let $X_1,\dots,X_n$ be exchangeable in $\mathbb R^d$ with $n\ge d+1$,
and consider the $N=n+1$ points $S_0,\dots,S_n$. Let $Y_i\in\mathbb R^{n-1-d}$ be any
additional coordinates such that the pairs $(X_i,Y_i)$ are exchangeable (for example
$Y_i=f(X_i)$ with $f$ measurable, such as $f(x)=|x|^2$, or $Y_i$ i.i.d. and independent
of $X$), and assume the lifted walk in $\mathbb R^{n-1}$ is in GP. The lifted walk has
$N=(n-1)+2$ points, so it has a unique Radon partition $R^\ast$. By projection,
$R^\ast$ is also a Radon partition of $S_0,\dots,S_n$. Then

$$\mathbb P(\min|R^\ast|=k)=\frac{2A(N-1,k-1)}{(N-1)!}\qquad(k<N/2),$$

with the factor 2 dropped when $k=N/2$. This is the law of Theorem 1.4 **with the
dimension replaced by $N-2$**. When $Y$ is i.i.d. Gaussian and independent of $X$,
$R^\ast$ is the Radon partition of a uniformly random direction in the dependency
space (Euclidean structure inherited from the increment coordinates). Equivalently,
the **solid-angle-weighted Radon profile**
$\mathbb E\sum_R\alpha(R)\,\mathbf 1\{\min|R|=k\}$ is Eulerian, where $\alpha(R)$ is
the normalized angle of the cone of dependences realizing $R$.

**Assumptions.** Exchangeable increments; the lifted walk is in GP; ordinary walks
and bridges alike (for bridges use $N$ steps and a lift with the same exchangeability);
any $n\ge d+1$. The claim is a probability law (a selected-partition law), or an
angle-weighted expectation.

**Relation to Thm 1.4.** It is a direct *extension*. It is the annealed law of
direction D: randomize the Gale basis, or pick a canonical lift.

**Mechanism.** Apply Theorem 1.4 upstairs. In Gale language: a fixed direction $u$
together with uniformly random labels gives a uniformly random cyclic arrangement, and
Lemma 4.4 applies. Theorem 2.17 is not needed.

**$d+2$ case.** With no lift, this is Theorem 1.4 itself.

**$d=2$, $n=4$ (five points).** The selected partition has a singleton part with
probability $2A(4,0)/4!=1/12$ and type $2|3$ with probability $11/12$, for every law.
This does not constrain the convex-position probability, because it weights the
partitions by angles and not by counts. Monte Carlo (`check_lift.py`, $10^5$ samples
per case) gives 0.0828, 0.0838, 0.0825 and 0.0822 for Gaussian or Cauchy steps and a
paraboloid or independent-uniform lift.

**Plausibility.** Essentially certain; it is a corollary. The only obstruction is
checking GP of the lift for a deterministic $f$ (it can fail for special $f$).

**Novelty.** *Immediate reformulation of a known theorem* (Theorem 1.4 = Kabluchko–Panzo,
Thm 3.17). The angle-weighted reading may be new as a formulation.

**Ratings.** Beauty 6 · Plausibility 10 · Novelty 3 · Provable via Thm 2.17: 3 (not
needed) · Thesis usefulness 5 (a good first lemma and sanity check).

**Experiment.** $d=2$, $n=4$ and $d=3$, $n=5$: Gaussian, Cauchy and uniform-disc
steps, with lifts $f(x)=|x|^2$ and $f(x)=x_1^3$ and independent noise; compare the law
of $\min|R^\ast|$ with $2A(N-1,k-1)/(N-1)!$.

---

### 2.2 Conjecture 2: the Stirling × Eulerian product formula (chamber-weighted Radon profile)

**Statement.** Let the steps be exchangeable, the points in GP, and assume (NT).
For each Weyl chamber $K_w$ met by the dependency space, let $D(w)$ be the size of the
positive part of the Radon partition of the *actual* walk induced by any dependence in
$K_w$; this is well defined. Then

$$\boxed{\ \mathbb E\sum_{w:\,K_w\cap\widetilde L\neq\{0\}}x^{D(w)}
=\Bigl(2\sum_{j\ge0}{N\brack d+2+2j}\Bigr)\cdot\frac{x\,A_{N-1}(x)}{(N-1)!}\ }$$

for every $N\ge d+2$, for walks and bridges. Equivalently: a chamber chosen uniformly
among those met has an Eulerian Radon type, independently of the number of chambers.
Grouped by partition, $\mathbb E\sum_R \mathrm{ch}(R)\,x^{|R_+|}$ factorizes, where
$\mathrm{ch}(R)$ is the number of orderings of the dependency coordinates realized
inside the tope of $R$.

**Assumptions.** Exchangeable steps, GP, (NT); arbitrary $N$; the claim is a
generating-function identity for an expectation, deterministic after averaging over
labels.

**Relation to Thm 1.4.** A *refinement and extension*. At $N=d+2$ there are 2 chambers
with $D\in\{k,N-k\}$, and the identity is exactly Theorem 1.4.

**Mechanism (Theorem 2.17).** The Stirling factor is Theorem 2.17 applied to
$Q_u=\widetilde L\cap\mathbf 1^\perp\cap\{\langle u,t\rangle=1\}$ (§1.3): the Weyl chambers
met encode the absorption event of the reordered walk, and the cycle subspaces met
encode dependence among the lifted cycle sums $(a_\gamma,|\gamma|)$. The Eulerian factor
is Lemma 4.4, applied chamber by chamber: under uniform labels the rank vector of each
chamber is a uniform permutation, and its cyclic descents are Eulerian. The two factors
decouple because the chamber *count* is deterministic under genericity.

**$d=2$, $n=5$.** $20$ chambers, and
$\mathbb E\sum_w x^{D(w)}=\tfrac{20}{24}\,x(1+11x+11x^2+x^3)$. The expected number of
chambers of singleton type is $5/3$. This is *not* the tope count: the tope-counting
law is $\mathbb E N_1=5/6$, whereas an Eulerian law would give $5/12$. So tope
counting is not Eulerian, while angle weighting (C1) and chamber weighting (C2) are.
Nothing here forces the convex-position probability to be universal.

**Plausibility.** Very likely true. The main technical obstruction is genericity: the
dependency space must meet the braid arrangement generically (as in KVZ, Prop. 2.5 of
GAFA 2017), and (NT) must follow from exchangeability plus GP, as in Lemma 4.3.

**Novelty.** *Apparently open as a statement*, but the ingredients are known: the
chamber count (KVZ, GAFA 2017) and cyclic Eulerian counting (Lemma 4.4; Kabluchko–Panzo).
A two-factor formula of this shape may be implicit in Kabluchko–Panzo's method of
moments, so the classification is "unclear" until that paper has been checked line by
line.

**Ratings.** Beauty 8 · Plausibility 9 · Novelty 6 · Provable via Thm 2.17: 8 ·
Thesis usefulness 8.

**Experiment.** $d=2$, $N=5,6$ and $d=3$, $N=6$: sample a Gale diagram, list the
chambers met exactly (via linear programming, not sampling), and tabulate $D(w)$ over
all labelings.

---

### 2.3 Conjecture 3: the cyclic-collision formula (an exact replacement for "k = 1" of Thm 1.4)

**Statement.** Let the steps be exchangeable, the points in GP, and assume (NT), for
any $N\ge d+2$. Let $P$ be the affine Gale diagram of the steps, and $T_1$ the number of
projection orders of $P$ (the chambers met). Let $T_r(P)$ be the number of pairs
(cyclic word $c$ on the Gale points, $r$-set of cut positions of $c$) such that the
rotation of $c$ starting at each cut is a projection order. Then

$$\mathbb E\Bigl[\tbinom{N_1}{r}\Bigm|P\Bigr]=\frac{T_r(P)}{(N-1)!},\qquad
\mathbb P(\text{convex position})=1-\frac{\mathbb E\,\kappa(P)}{(N-1)!},$$

where $\kappa(P)$ is the number of **cyclic classes** of projection orders. Here $T_1$
is universal, and so is $\mathbb E N_1=T_1/(N-1)!$. For $N=d+3$ (planar Gale diagram),
$N_1\le2$, and

$$T_2(P)=2\,s(P),\qquad s(P)=\#\{\text{splits }A|B\text{ whose }|A||B|\text{ crossings are consecutive in the circular sequence of }P\}.$$

Equivalently, $s(P)$ counts the splits $A|B$ that are linearly separable and such that
every line through two points on the same side is parallel to some separating line.
This document calls them **strongly separable splits**; in allowable-sequence language
they are "block transpositions".

**Assumptions.** As stated; the claims concern a conditional law given the unlabeled
Gale data, and hence all factorial moments of $N_1$.

**Relation to Thm 1.4.** A *replacement*. For $N=d+2$: $\kappa=2$, so
$\mathbb P(\text{convex})=1-2/(d+1)!$ (Panzo). At $N=d+3$ the number of chambers
$N(N-1)$ is still universal, but chambers can **collide cyclically**, and each collision
is a strongly separable split. The whole failure of universality is therefore a
statement about cyclic collisions of Weyl chambers.

**Mechanism.** A point $s_i$ is interior exactly when the rotation of the label word
starting at $i+1$ is a projection order (Gale: the other $N-1$ polygon edges lie in an
open half-plane). Uniform labels turn counts of labelings into $T_r/(N-1)!$.
Theorem 2.17 gives $T_1$, the Stirling layer. The collisions ($T_2$) are the one piece
that Theorem 2.17 cannot see, because a union of rotated chambers is not convex.

**$d=2$, $N=5$.** Exhaustively over all 768 reduced words of $w_0\in S_5$
(`allwords.py`, `s_words.py`), the combinatorial $s$ reproduces the labeled count of
two-interior-point labelings exactly: 400 words with $s=1$ (30 convex labelings out of
120), 360 with $s=2$ (40 out of 120), and 8 with $s=0$ (20 out of 120). The 8 words
with $s=0$ are the periodic words such as $(0,1,3,2,0,1,3,2,0,1)$. None of them appeared
among 180,000 sampled point sets, which realized 759 of the 768 words. I believe these
are the non-realizable allowable sequences of Goodman–Pollack, but that must be
checked.

**Plausibility.** The identities are, in my assessment, true: the derivation above is
complete up to routine genericity checks, and the numerical checks agree at N=5,6,7.

**Novelty.** *Apparently open* (a new formulation). The Gale–polygon dictionary is
elementary linear algebra, and may be folklore in the oriented-matroid literature.

**Ratings.** Beauty 8 · Plausibility 9 · Novelty 7 · Provable via Thm 2.17: 6 (for the
universal half) · Thesis usefulness 9.

**Experiment.** Implement $\kappa(P)$ and $s(P)$ for $d=3$, $N=6$ and $d=4$, $N=7$,
and compare $1-\kappa/(N-1)!$ with a direct primal simulation for Gaussian and
Cauchy-coordinate steps.

---

### 2.4 Conjecture 4: the five-point sandwich and the one-parameter vertex law at $n=d+3$

**Statement.** (i) For every generic planar configuration, $s(P)\in\{0,1,2\}$; in
fact this holds for every simple allowable sequence. (ii) If $N=5$ and $P$ is realizable,
then $s(P)\in\{1,2\}$. Consequently, for every exchangeable walk or bridge with
$N=d+3$ points in GP, the vertex number $f_0=N-N_1$ has the one-parameter law

$$\mathbb P(f_0=N-2)=\frac{2\,\mathbb E s}{(d+2)!},\qquad
\mathbb P(f_0=N-1)=\frac{d+3}{(d+1)!}-\frac{4\,\mathbb E s}{(d+2)!},\qquad
\mathbb P(\text{convex})=1-\frac{d+3}{(d+1)!}+\frac{2\,\mathbb E s}{(d+2)!},$$

and the sharp universal bounds

$$\tfrac14\le \mathbb P(\text{5 planar walk points in convex position})\le\tfrac13,\qquad
1-\tfrac{d+3}{(d+1)!}\le\mathbb P(\text{convex})\le 1-\tfrac{d+3}{(d+1)!}+\tfrac{4}{(d+2)!}\ (d\ge3).$$

For $d=3$ the interval is $[3/4,\,47/60]$, and for $d=4$ it is $[113/120,\,341/360]$.
(iii) **Gaussian self-duality**, the analogue of Theorem 1.3: for i.i.d. Gaussian
bridges the affine Gale diagram of the steps is, up to affine equivalence, an i.i.d.
Gaussian sample in $\mathbb R^{N-d-1}$; for Gaussian walks it is an i.i.d. Gaussian
sample together with the origin. Hence
$\mathbb P_{\rm Gauss}(\text{convex})=\tfrac16+\tfrac1{12}\mathbb E\,s(0,g_1,\dots,g_4)$
for five planar walk points.

**Assumptions.** Exchangeable steps, GP, (NT); $n=d+3$; walks or bridges; the claim
concerns a full distribution (of $f_0$), bounds, and a mixture representation.

**Relation to Thm 1.4.** The honest $d+3$ analogue. At $d+2$ the law of the smaller
Radon part has *zero* free parameters. At $d+3$ the vertex law has *exactly one*,
$\mathbb E s$, and that parameter lies in a universal interval.

**Mechanism.** Conjecture 3, together with $N_1\le N-(d+1)=2$ (a hull needs at least
$d+1$ vertices), and a combinatorial lemma on reduced words of $w_0$ bounding the
number of block transpositions by 2. Theorem 2.17 supplies $T_1$.

**$d=2$, $n=5$.** This is the key case, and it **does not** claim universality. The
probability ranges over $[1/4,1/3]$, and both endpoints are attained. The Lean-checked
step sets $A=\{(-5,9),(-7,-1),(-6,6),(5,6),(13,-20)\}$ and
$B=\{(9,6),(7,3),(9,-8),(6,-2),(-31,1)\}$, taken in uniformly random order, give
40/120 resp. 30/120 convex orderings. Taking the last step as the closing step and
permuting the other four gives 8/24 resp. 6/24. Both have $100/120$ interior points on
average, and 20/120 resp. 10/120 orderings with two interior points. Monte Carlo for
i.i.d. steps ($2\cdot10^5$ samples each, exploratory): Gaussian 0.2956 (the Gale-side
prediction $\tfrac16+\mathbb E s/12$ with $\mathbb E s\approx1.566$ gives 0.2971),
Cauchy coordinates 0.3085, heavy-tailed radial law 0.3194. All lie in the interval.

**Plausibility.** (ii) and the Gaussian reduction are very likely. For (i):
$s\le 2$ held for **all 292,864** simple allowable sequences with $N=6$ (counts
182,464 / 100,320 / 10,080 for $s=0,1,2$) and in random samples up to $N=10$. The main
obstruction is proving $s\le2$ in general. A plausible route: two block transpositions
must use complementary halves of the half-period, and a third one would force a
crossing to be repeated.

**Novelty.** *Apparently open.* I know of no Sylvester-type result for $d+3$ walk
points, and the attached paper (§7, remark 1) lists the $n\ge d+3$ walk case as open.

**Ratings.** Beauty 9 · Plausibility 8 · Novelty 8 · Provable via Thm 2.17: 4 (the core
is allowable-sequence combinatorics) · Thesis usefulness 10.

**Experiment.** (a) Prove or refute $s\le2$ for $N=7$ by exhaustive enumeration in C
(about $1.1\cdot10^9$ reduced words, feasible with symmetry reduction). (b) Compute
$\mathbb E s$ for Gaussian samples by numerical integration and compare with
$10^7$-sample primal Monte Carlo. (c) For $d=3$, $N=6$, check
$\mathbb P(\text{convex})\in[0.75,0.7834]$ for several laws.

---

### 2.5 Conjecture 5: the hyperoctahedral labeled Radon law at $d+2$ (and its failure at $d+3$)

**Statement.** Let $(X_1,\dots,X_{d+1})$ be **sign-exchangeable**:
$(\varepsilon_iX_{\sigma(i)})_i\overset d=(X_i)_i$ for all $\sigma$ and all signs.
Assume GP, and no ties among $\pm$ the dual coordinates. Then the *labeled* Radon
partition of $S_0,\dots,S_{d+1}$ is universal:

$$\mathbb P(\text{Radon partition}=\{I,I^c\})=\frac{\#\{w\in B_{d+1}:\ \text{the cyclic sign pattern of }(0,w_1,\dots,w_{d+1},0)\text{ equals }I\}}{2^{d+1}(d+1)!},$$

where $w$ runs over the signed permutations of the values $1,\dots,d+1$ and $\lambda_i=w_i-w_{i+1}$.
Summing over $|I|$ gives back Theorem 1.4. Particular events are distribution-free: that
$S_0$ is alone in its part (the absorption event of KVZ), that the path splits into a
prefix and a suffix, and zigzag patterns. **Without sign symmetry the labeled law is
not universal**, and **at $d+3$ even sign symmetry does not give a universal law.**

**Assumptions.** Sign-exchangeable increments; ordinary walks (bridges are not
compatible with sign flips); $n=d+2$ points; the claim is a full joint law of a labeled
partition.

**Relation to Thm 1.4.** A refinement from the size of the smaller part to the partition
itself, at the price of a type-B symmetry assumption.

**Mechanism.** The dual vector in increment coordinates is a vector $t$ that is
sign-exchangeable, so its signed rank pattern is uniform on $B_{d+1}$. This is the
type-B analogue of Lemma 4.4. The type-B Theorem 2.17 (Weyl chambers
$t_{\sigma(1)}\ge\dots\ge t_{\sigma(n)}\ge0$ against signed cycle subspaces) is the
natural tool for the $d+3$ question, where it predicts non-universality through the
same collision mechanism as in C3.

**$d=2$ (4 points).** Predicted, with the positive part named and $S_0$ in the other
part: $\{S_1\}$: $1/8$; $\{S_2\}$: $1/8$; $\{S_3\}$: $1/24$; $S_0$ alone: $1/24$;
$\{S_1,S_2\}$: $1/4$; $\{S_1,S_3\}$: $1/3$; $\{S_2,S_3\}$: $1/12$. Monte Carlo
(`check_sym.py`) matches within $0.002$ for Gaussian and for symmetric Cauchy steps. A
non-symmetric law gives a clearly different table. The singleton total is $1/3$, which
is Theorem 1.4. **$d=2$, $n=5$ (5 points):** averaging over labels *and* signs of a
fixed planar Gale diagram gives different convex-position probabilities, for example
$1/3$, $5/16$ and $7/24$ (`check3.py`), so universality fails there, as the premise
requires.

**Plausibility.** Very likely true at $d+2$; false at $d+3$ in general.

**Novelty.** *Unclear.* It may be contained in the type-B/conic analysis of
Kabluchko–Panzo (their positive-hull and spherical models) or in Godland–Kabluchko's
work on positive hulls of random walks and bridges. I did not see the labeled
statement stated there. Search: "positive hulls of random walks and bridges Godland
Kabluchko", "Radon partition sign-symmetric random walk".

**Ratings.** Beauty 7 · Plausibility 9 (at $d+2$) · Novelty 5 · Provable via Thm 2.17: 3 ·
Thesis usefulness 7.

**Experiment.** $d=1$, $n=4$ (three increments on the line: exact enumeration) and
$d=3$, $n=6$: compare the labeled partition table for Gaussian, Laplace-radial and
symmetric Cauchy steps with the $B_{d+1}$ count, and repeat with non-symmetric steps.

---

### 2.6 Conjecture 6: linear universality (a maximal universality theorem at $n=d+3$)

**Statement.** Let $n=d+3\ge5$, with exchangeable steps, GP and (NT). A function $F$ of
the Radon profile $(N_1,\dots,N_{\lfloor N/2\rfloor})$ has a distribution-free
expectation **if and only if** $F$ is affine in the $N_k$, modulo the deterministic
relations. The deterministic relations are $\sum_kN_k=N$ and, for even $N$, the parity
identity: exactly $N/2$ of the $N$ complete Radon partitions have parts of even size
(for $N=6$ this means $N_2\equiv3$). In particular **no nonlinear statistic** of the
profile (variance, factorial moments, the indicator of convex position) is
distribution-free, and no nondegenerate profile statistic has a universal *law*.

**Assumptions.** $n=d+3$; exchangeable; the claim is about expectations (a
characterization of a vector space).

**Relation to Thm 1.4.** It explains exactly *why* Theorem 1.4 is special. At $d+2$ the
profile is a single number $\tau$, and every function of it is "linear in the
indicators", so the whole law is universal. At $d+3$ only first moments survive.

**Mechanism.** Given the circular sequence $\rho$ (a reduced word of $w_0$), the
labeled average of a statistic is a sum over arcs (single-arc terms, universal by
Theorem 2.17 and Lemma 4.4) plus multi-arc correlation terms, which depend on the
relative permutations between chambers. The conjecture says the multi-arc part never
cancels over all realizable $\rho$ unless it vanishes identically. A proof would need
enough realizable circular sequences to separate every nonlinear functional.

**$d=2$, $n=5$.** The profile is $N_1\in\{0,1,2\}$. The universal functions are
exactly $\mathrm{span}\{1,N_1\}$ (the averages at the two realizable values of $s$ give
rank 1), so convex position is not universal. This agrees with the premise.

**Evidence.** For $N=6$ (4 hull types observed), the profile laws are indexed by $s$,
and only $1,N_1$ are universal. For $N=7$, 16 sampled Gale diagrams give profile laws
on 7 profile types, and the space of functions with universal average has dimension
exactly **3**, namely $\mathrm{span}\{1,N_1,N_2\}$ (`check_univ.py`). The universal
values found there are $\mathbb E N_1=7/120$, $\mathbb E N_2=63/40$ and
$\mathbb E N_3=161/30$.

**Plausibility.** Plausible for the profile. It is likely to need care for richer
statistics (labeled f-vectors), where additional universal linear functionals appear.

**Novelty.** *Apparently open.*

**Ratings.** Beauty 9 · Plausibility 6 · Novelty 8 · Provable via Thm 2.17: 3 ·
Thesis usefulness 6.

**Experiment.** $N=8$ ($d=5$): 30 random Gale diagrams, exact label averages ($8!$
labelings each), and the rank of the difference matrix. The conjecture predicts
dimension $1+\#\{\text{free }N_k\}$.

---

### 2.7 Conjecture 7: Young-subgroup Theorem 2.17 and past–future Radon separation

**Statement.** (a) *(Young-subgroup version, deterministic.)* For a convex set
$Q\subset\mathbb R^{m}\times\mathbb R^{n-m}$, the number of pairs $(\sigma_1,\sigma_2)$
with $(K_{\sigma_1}\times K_{\sigma_2})\cap Q\neq\emptyset$ equals the number of pairs
$(\tau_1,\tau_2)$ with $(F_{\tau_1}\times F_{\tau_2})\cap Q\neq\emptyset$. Proof sketch:
apply Theorem 2.17 in one factor after fixing a chamber or a subspace in the other;
every slice stays convex. (b) *(Consequence.)* Let the increments be i.i.d.
and symmetric, with GP. Then the probability that **the past hull and the future hull
meet only at the present**, $\mathrm{conv}(S_0,\dots,S_m)\cap\mathrm{conv}(S_m,\dots,S_n)=\{S_m\}$,
is distribution-free:

$$\mathbb P=\mathbb E\,W_{C_m+C'_{n-m},\,d},\qquad W_{c,d}=2^{1-c}\sum_{k<d}\tbinom{c-1}{k},$$

where $C_m$ and $C'_{n-m}$ are the numbers of cycles of independent uniform
permutations. For $d=1$ this is $2p_mp_{n-m}$, with $p_k$ the Sparre Andersen
probabilities; this check holds exactly.

**Assumptions.** (a) is deterministic; (b) needs i.i.d. symmetric increments (or
exchangeable plus the symmetry and independence needed for Wendel's theorem), for any
$n$, and concerns a probability.

**Relation to Thm 1.4.** A Radon-type event ("no Radon partition separates the past from
the future except through $S_m$") with a cycle-index answer. It is a different
extension from Theorem 1.4: an extension of Theorems 2.13 and 2.26.

**Mechanism.** The past, reversed from $S_m$, and the future are two walks built from
disjoint blocks of increments. Separation is the event $\mathrm{pos}(\text{both})\neq\mathbb R^d$.
Theorem 2.13 for $S_m\times S_{n-m}$ turns this into cycle sums over disjoint blocks,
which are independent, and Wendel's theorem finishes the computation.

**$d+2$ and $d=2$, $n=5$.** These are not special here. At $n=d+2$ the event is one
specific labeled Radon type.

**Plausibility.** (a) is essentially certain; (b) is very likely true. For symmetric
laws the event has the same probability as "$S_m$ is a vertex".

**Novelty.** *Very likely contained in known work*: KVZ (GAFA 2017; the Bernoulli 2019
arcsine paper, where vertex probabilities of walk hulls appear) and
Barndorff-Nielsen–Baxter (1963). I include it because it is the cleanest thesis
exercise with the cycle-index machinery.

**Ratings.** Beauty 6 · Plausibility 9 · Novelty 2 · Provable via Thm 2.17: 9 ·
Thesis usefulness 6.

**Experiment.** $d=2$, $n=5$, $m=2$: Gaussian versus symmetric Cauchy steps, Monte Carlo
of the separation event against $\mathbb E W_{C_2+C'_3,2}$.

---

### 2.8 Negative control: "universal second moments" / "cyclic Theorem 2.17" (probably false; in fact refuted)

**Statement (to be refuted).** (a) The second factorial moments
$\mathbb E\binom{N_m}{2}$ are distribution-free for $n=d+3$ (direction B). (b)
Equivalently, in the form that universality would require: the number of **rotation
classes** of Weyl chambers met by a generic dependency space $\widetilde L\ni\mathbf 1$
depends only on $N$ and $\dim\widetilde L$ (a "cyclic Theorem 2.17").

**Why it fails.** By C3, $\kappa=N(N-1)-2s$ and $\mathbb E\binom{N_1}2=\mathbb E\,2s/(N-1)!$,
and $s$ varies. **Smallest counterexample:** $d=2$, $n=5$ with the step sets $A$ and $B$
of §2.4. Lean-verified: $\mathbb E\binom{N_1}{2}=20/120$ for $A$ and $10/120$ for $B$,
while $\mathbb E N_1=100/120$ for both. For (b): $\kappa=16$ versus $18$.

**Ratings.** Beauty 5 · Plausibility 0 (refuted for $m=1$) · Novelty n/a · Thesis
usefulness 7 (as a guardrail).

---

## 3. The universality hierarchy (direction H)

| level | valid for | examples |
|---|---|---|
| **Deterministic** (every configuration in GP) | all $N$ | the number of complete Radon partitions (for $N=d+3$ this is $N$; Cover/Eckhoff in general); for $N=d+3$: $N(N-1)$ chambers met, and the parity identity; Theorems 2.13, 2.16, 2.17, 2.26 |
| **After averaging over labels, for every fixed Gale diagram** | all $N$ | single-arc statistics: C1 (angle-weighted), C2 (chamber-weighted), $\mathbb E N_1$, and in general $\mathbb E N_m$ |
| **Distribution-free expectation** | exchangeable | the span of the above (conjecturally nothing else: C6); face numbers (KVZ) |
| **Universal law** | exchangeable | the whole Radon law at $N=d+2$ (Theorem 1.4); the labeled law at $d+2$ under sign symmetry (C5); selected partitions (C1). **Not** at $N\ge d+3$ for profile statistics (C4, C6, §2.8) |
| **One-parameter law** | exchangeable, $N=d+3$ | the vertex number: only $\mathbb E s$ is free (C4) |

On direction F: Theorem 2.16 (zonotopes of cycle sums) concerns *membership of a point
in path hulls*. Under the dictionary it becomes a statement about dependences with
bounded coefficients $0\le t\le 1$, and I did not find a Radon interpretation of it. So
I do not propose a conjecture based on it. Theorems 2.13 and 2.26 do translate: they
are the Stirling layer in C2 and C3, and they give C7.

---

## 4. Summary and recommendations

### 4.1 Ranked table

| rank | conjecture | beauty | plausibility | novelty | via Thm 2.17 | thesis | classification |
|---|---|---|---|---|---|---|---|
| 1 | C4 Five-point sandwich / one-parameter vertex law | 9 | 8 | 8 | 4 | 10 | apparently open |
| 2 | C3 Cyclic-collision formula | 8 | 9 | 7 | 6 | 9 | apparently open (new formulation) |
| 3 | C2 Stirling × Eulerian product | 8 | 9 | 6 | 8 | 8 | apparently open / unclear |
| 4 | C6 Linear universality | 9 | 6 | 8 | 3 | 6 | apparently open |
| 5 | C5 Hyperoctahedral labeled law | 7 | 9 | 5 | 3 | 7 | unclear |
| 6 | C7 Young-subgroup Thm 2.17 / past–future | 6 | 9 | 2 | 9 | 6 | very likely known |
| 7 | C1 Lifting principle | 6 | 10 | 3 | 3 | 5 | immediate reformulation of a known theorem |
| – | §2.8 Universal second moments | 5 | 0 | – | – | 7 | refuted (Lean-checked finite counterexample) |

### 4.2 Best conjecture for a diploma thesis
**C4, built on the dictionary of C3.** It has a clean statement: *for five points of any
planar exchangeable walk, the convex-position probability lies in $[1/4,1/3]$, both ends
are attained, and the value is $\tfrac16+\tfrac1{12}\mathbb E s$*. It has an elementary
but real combinatorial core ($s\le2$ for reduced words of $w_0$), a computational
component, and a Gaussian computation analogous to Theorem 1.3. It is also a genuine
answer to remark 1 of §7 of the attached paper.

### 4.3 Most beautiful conjecture
**C2, the Stirling × Eulerian product.** "Chambers met by the dependency space" times
"cyclic descents of a random circle". The first factor is Theorem 2.17 and the second is
Lemma 4.4, and together they give Theorem 1.4 at $N=d+2$. C6 is the deepest statement,
but it is less likely to be provable in six months.

### 4.4 Most likely to be false
Among the statements not already refuted: **C6 (linear universality) at larger $N$**,
where richer label-level statistics could produce extra universal functionals; also
the claim **$s\le2$ for all $N$** in C4(i). *Smallest tests:* the rank computation at
$N=8$, and exhaustive reduced words at $N=7$. (The §2.8 statement is refuted already at
$d=2$, $n=5$ by the explicit step sets $A$ and $B$.)

---

## 5. Six-month plan

**Month 1: literature verification.** Read Kabluchko–Panzo (arXiv:2501.16166) §3 in
full, to check whether C2 or C5 appear there implicitly. Read KVZ GAFA 2017 (the chamber
counts and genericity; Theorem 1.2 of the Adv. Math. 2017 paper), Kabluchko's Gale
duality paper (arXiv:2602.08581), White (arXiv:2507.05449), and Chan–Kalai–Narayanan–Ter-Saakov–White
(arXiv:2507.01353). Read Goodman–Pollack on allowable sequences (JCTA 1980), to identify
the 8 periodic words with $s=0$ as non-realizable. Search for "Sylvester problem random
walk five points", "Radon partitions random walk Gale", "allowable sequence block
transposition", and "cyclic descents Weyl chambers subspace". *Decision:* if C3 or C4
already appear, switch to C2 and C6.

**Month 2: low-dimensional experiments.** Reimplement `experiments/` in C or Julia.
Run exact label averages for $N\le8$; exhaustive reduced words for $N=7$ with
symmetry reduction; Gaussian $\mathbb E s$ by numerical integration; $10^7$-sample
Monte Carlo for Gaussian, Cauchy, uniform-disc and heavy-tailed radial steps, walks and
bridges. *Decision:* a single realizable $P$ with $s\ge3$ kills C4(i); keep C3 and
restate the bounds.

**Month 3: first rigorous lemma.** Write out the Gale–polygon dictionary (§1.1), and the
statement "labels are uniform given the unlabeled Gale data, and walk and bridge
averages agree" (§1.2) with a tie-exclusion lemma modeled on Lemma 4.3. Then prove C3's
identity $\mathbb E[\binom{N_1}{r}\mid P]=T_r/(N-1)!$ and $T_2=2s$ at $N=d+3$.

**Month 4: deterministic use of Theorem 2.17.** Prove the one-sided count
$A_N(Q_u)=\sum_{k\ge d+2}{N\brack k}$ and deduce the total chamber count; prove C2.
Optionally, write down the type-B analogue for sign-symmetric walks and the
Young-subgroup version (C7(a)).

**Month 5: Gale-duality translation and the combinatorial core.** Attack $s\le2$ for
simple allowable sequences: two block transpositions occupy complementary arcs of the
half-period. Prove $s\ge1$ for realizable 5-point sequences, or reduce it to
Goodman–Pollack's non-realizability. Prove the Gaussian self-duality of the Gale diagram
(the analogue of Theorem 1.3).

**Month 6: write-up and branch decisions.** *Pursue* whatever is proved (C2 and C3 are
very likely provable; C4 if $s\le2$ is proved). *Abandon* C6 if the rank tests at $N=8$
show extra universal functionals and no pattern appears. *Report* the negative control
(§2.8) as the precise sense in which "Theorem 1.4 does not extend".

**Abandon or pursue, criteria in one line each.** C1: done after month 3. C2: abandon
only if genericity fails for exchangeable laws (look for a counterexample with atoms).
C3: always pursue; it is the dictionary. C4: pursue while no realizable $s\ge3$ exists.
C5: pursue if Kabluchko–Panzo do not contain it. C6: pursue only with a clear
separating-family argument by month 5. C7: use as an exercise; do not claim novelty.

---

## 6. References

Confident bibliographic data (verify page numbers):

1. X. Barysheva, *The Sylvester–Radon problem for random walks and linear images of Gaussian samples* (attached, 2026); Thms 1.3–1.5, Lemmas 4.2–4.4.
2. D. Zaporozhets, *Random Permutations, Lectures 1–4* (attached); Thms 2.13, 2.16, 2.17, 2.24–2.26.
3. Z. Kabluchko, H. Panzo, *A refinement of the Sylvester problem: probabilities of combinatorial types*, Discrete Comput. Geom. (2026), arXiv:2501.16166; Thm 3.17.
4. H. Panzo, *Sylvester's problem for random walks and bridges*, Statist. Probab. Lett. (2025), arXiv:2409.07927.
5. Z. Kabluchko, V. Vysotsky, D. Zaporozhets, *Convex hulls of random walks, hyperplane arrangements, and Weyl chambers*, Geom. Funct. Anal. 27 (2017) 880–918.
6. Z. Kabluchko, V. Vysotsky, D. Zaporozhets, *Convex hulls of random walks: expected number of faces and face probabilities*, Adv. Math. 320 (2017) 595–629.
7. F. Frick, A. Newman, W. Pegden, *Youden's demon is Sylvester's problem*, Mathematika 71 (2025), arXiv:2407.02589.
8. M. White, *Radon partitions of random Gaussian polytopes*, arXiv:2507.05449; S. H. Chan, G. Kalai, B. Narayanan, N. Ter-Saakov, M. White, *Unimodality for Radon partitions of random vectors*, arXiv:2507.01353.
9. Z. Kabluchko, *Random polyhedral cones: distributional results via Gale duality*, arXiv:2602.08581.
10. J. E. Goodman, R. Pollack, *On the combinatorial classification of nondegenerate configurations in the plane*, J. Combin. Theory Ser. A 29 (1980) 220–235 (allowable sequences).
11. R. P. Stanley, *On the number of reduced decompositions of elements of Coxeter groups*, European J. Combin. 5 (1984) 359–372.
12. O. Barndorff-Nielsen, G. Baxter, *Combinatorial lemmas in higher dimensions*, Trans. Amer. Math. Soc. 108 (1963) 313–325.
13. J. G. Wendel, *A problem in geometric probability*, Math. Scand. 11 (1962) 109–111; T. M. Cover, B. Efron, *Geometrical probability and random points on a hypersphere*, Ann. Math. Statist. 38 (1967) 213–220.
14. T. K. Petersen, *Eulerian Numbers*, Birkhäuser, 2015 (cyclic descents, type-B Eulerian numbers); F. Brenti, *q-Eulerian polynomials arising from Coxeter groups*, European J. Combin. 15 (1994) 417–441.
15. E. Welzl, *Entering and leaving j-facets*, Discrete Comput. Geom. 25 (2001) 351–364 (Gale duality and continuous motion in rank 2).
16. G. M. Ziegler, *Lectures on Polytopes*, GTM 152, Lecture 6 (Gale diagrams); J. Matoušek, *Lectures on Discrete Geometry*, GTM 212, §5.6.

Less certain (search before citing): Z. Kabluchko, V. Vysotsky, D. Zaporozhets, *A
multidimensional analogue of the arcsine law for the number of positive terms in a random
walk*, Bernoulli (2019); V. Vysotsky, D. Zaporozhets, *Convex hulls of multidimensional
random walks*, Trans. AMS (2018); T. Godland, Z. Kabluchko (and coauthors), work on
conic intrinsic volumes of Weyl chambers and positive hulls of random walks and
bridges; M. Develin, M. Macauley, V. Reiner, *Toric partial orders*, Trans. AMS (2016)
(cyclic orders as toric chambers). These may bear on the cyclic-collision phenomenon.
