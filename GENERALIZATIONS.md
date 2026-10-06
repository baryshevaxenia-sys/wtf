# Theorem 1.4 of Barysheva's paper: generalizations, further results, and where the method stops

Throughout, points are numbered as in the paper, \(S_1,\dots,S_{d+2}\), with \(S_i=X_1+\dots+X_i\).
In Lean, indices start at `0`, so Lean index `i` is the paper's point \(S_{i+1}\).
Every Lean statement mentioned here builds without `sorry` and uses only the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

## 0. How the proof works, step by step (and what the Lean files contain)

Fix one realization. If \(g\) is the Radon dual vector of \(S\) and \(G_i=\sum_{m\ge i} g_m\), then
\(G_1=0\), \(\sum_m G_m X_m=0\), and \(g_i=G_i-G_{i+1}\) cyclically (Lemma 4.2). The relation
\(\sum G_m X_m=0\) is symmetric in the increments. So permuting \(X_2,\dots,X_{d+2}\) by \(\sigma\)
permutes the circle \((0,G_2,\dots,G_{d+2})\), and the Radon partition of the permuted walk is the
set of cyclic descents of the permuted circle. Averaging over the \((d+1)!\) permutations that fix
\(X_1\), and counting circular arrangements (Lemma 4.4), gives Eulerian numbers.

The Lean development follows these steps, one realization at a time:

| step | Lean |
|---|---|
| Lemma 4.4, cyclic Eulerian count | `card_fix_cycAsc_eq_eulerian` (`Patterns.lean`) |
| symmetry \(A(n,k)=A(n,n-1-k)\) | `eulerian_symm` |
| Lemma 4.2 and Step 2: duals of permuted walks are the cyclic differences of \(c\,G\circ\sigma\) | `affDep_walk_iff` (`Walk.lean`) |
| **Theorem 1.4, deterministic form** | `card_radonMin_walk` |
| Step 3, averaging (abstract) | `card_mul_measure_eq` (`Probability.lean`) |
| **Theorem 1.4, probabilistic form** | `prob_radonMin_walk` |

`card_radonMin_walk` assumes three things: the solutions of \(H_1=0,\ \sum H_jX_j=0\) form a line
spanned by some \(G\); \(G_1=0\); and the entries of \(G\) are pairwise distinct. In the paper these
facts come from general position (Lemma 2.1) and from the no-ties lemma (Lemma 4.3), which uses
exchangeability. **Lemmas 2.1 and 4.3 are not formalized.** `prob_radonMin_walk` therefore takes as
hypotheses that their conclusion holds almost surely and that the event \(\{\tau=k\}\) is
measurable. A concrete planar configuration (`xEx_counts` in `Examples.lean`) shows that these
hypotheses can be satisfied.

One small strengthening comes straight out of the proof. `prob_radonMin_walk` only uses invariance
of the law under permutations that fix the first increment. The paper's Lemma 4.3 also only uses
such permutations. So Theorem 1.4 holds whenever \((X_1,X_{\sigma(2)},\dots,X_{\sigma(d+2)})\)
has the same law as \((X_1,\dots,X_{d+2})\) for all \(\sigma\). Since \(\tau\) is translation
invariant, \(X_1\) plays no role at all (compare Remark 4.5).

---

## 1. Generalization A: necklace universality (the cyclic shape of the Radon partition)

The averaging argument proves more than the theorem states. Lemma 4.4 says that, as \(\sigma\)
ranges over permutations fixing 1, the circles \((0,G_{\sigma(2)},\dots)\) run through each
*rotation class* of circular arrangements exactly once. So **any rotation-invariant statistic of the
cyclic descent word has a universal law.** Read in time order, the cyclic descent word is the Radon
partition, written as a cyclic \(\pm\) word with \(+\) for \(g_i>0\).

**Theorem A.** Let the increments be exchangeable and satisfy (GP), with no ties as in Lemma 4.3.
Let \(\mathcal C\) be a set of \(\pm\) words of length \(d+2\) that is closed under cyclic rotation
and under exchanging \(+\) and \(-\). Then
\[
\mathbb P\big(\text{Radon word of }S_1,\dots,S_{d+2}\in\mathcal C\big)
=\frac{\#\{\pi\in \mathfrak S_{d+1}:\ \text{cyclic descent word of }(0,\pi_1,\dots,\pi_{d+1})\in\mathcal C\}}{(d+1)!}.
\]

Lean, deterministic form: `card_radonPat_walk` (`Generalizations.lean`) holds for every
rotation-invariant property `P` of patterns. Theorem 1.4 is the special case "the smaller part has
\(k\) elements".

**Example (d = 2), formally verified as `card_alternating_walk_d2`.** For four points of any planar
walk with exchangeable increments, the Radon partition is \(\{S_1,S_3\}\mid\{S_2,S_4\}\) for exactly
2 of the 6 orderings. Equivalently, the closed polygon \(S_1S_2S_3S_4\) is convex (simple, with all
four points as vertices) with probability \(1/3\). Together with Theorem 1.4 this gives a universal
three-way split for \(d=2\):

| event | probability |
|---|---|
| one point inside the triangle of the others (\(\tau=1\)) | \(1/3\) |
| \(\{S_1,S_3\}\mid\{S_2,S_4\}\): polygon \(S_1S_2S_3S_4\) convex | \(1/3\) |
| \(\{S_1,S_2\}\mid\{S_3,S_4\}\) or \(\{S_1,S_4\}\mid\{S_2,S_3\}\): polygon self-intersecting | \(1/3\) |

Other rotation-invariant statistics are covered the same way, for example the number of cyclic
runs (alternations) of the Radon partition in time order.

**The labelled partition is *not* universal under exchangeability alone.** Take \(d=1\). \(S_2\) is
the middle point iff \(X_2,X_3\) have the same sign. That has probability \(1/2\) for symmetric
increments and probability \(1\) for positive increments. Monte Carlo runs for \(d=2\) (table below)
show the same thing: individual labelled partitions change with the law, while their rotation
classes do not. So for exchangeable increments, the rotation class (Theorem A) is as far as the
argument goes.

## 2. Generalization B: symmetric increments give the whole labelled partition

If the law is also invariant under sign changes of the increments (for example i.i.d. symmetric
increments), one can average over the *hyperoctahedral group* of signed permutations fixing 1.
Flipping the sign of \(X_m\) flips the sign of \(G_m\). As \((\sigma,\varepsilon)\) varies, the
circle \((0,\pm G_{\sigma(2)},\dots)\) then runs through all signed arrangements of the values
\(|G_i|\). Its descent pattern depends only on the signed permutation, so **every** property of the
labelled Radon partition has a universal law.

**Theorem B.** If the law is invariant under permutations and sign changes, satisfies (GP), and has
no ties of the form \(|G_i|=|G_j|\) (see the sketch below), then for every set \(D\) of labelled
sign patterns
\[
\mathbb P(\text{Radon pattern}\in D)=\frac{\#\{w\in B_{d+1}:\ \text{descent pattern of }(0,w_1,\dots,w_{d+1},0)\in D\}}{2^{d+1}(d+1)!}.
\]

Lean: `card_radonPat_signedWalk`, which holds for every property `P` with no invariance needed.
For \(d=2\), `card_signed_pattern_d2` and `refCount_table` give the full verified table:

| labelled Radon partition | \(S_1\) alone | \(S_2\) alone | \(S_3\) alone | \(S_4\) alone | \(\{S_1S_2\}\mid\{S_3S_4\}\) | \(\{S_1S_4\}\mid\{S_2S_3\}\) | \(\{S_1S_3\}\mid\{S_2S_4\}\) |
|---|---|---|---|---|---|---|---|
| symmetric increments (verified) | 1/24 | 1/8 | 1/8 | 1/24 | 1/12 | 1/4 | 1/3 |
| Monte Carlo, Gaussian | .041 | .127 | .125 | .041 | .084 | .251 | .331 |
| Monte Carlo, skewed exponential | .000 | .169 | .166 | .000 | .000 | .332 | .334 |

For example, the *last* point of a symmetric planar walk lies inside the triangle of the first three
with probability \(1/24\), while the second point does so with probability \(1/8\). In the skewed
exponential row, the rotation-class sums are still \(1/3,1/3,1/3\), as Theorem A requires. The
Monte Carlo rows come from exploratory simulations (200 000 samples) and are not verified.

**Sketch of the sign version of Lemma 4.3.** Ties \(G_i=G_j\) are excluded exactly as in the paper.
A tie \(G_i=-G_j\) with \(2\le i<j\) means \(\langle c,g\rangle=0\) for
\(c=\mathbf 1_{[i,j-1]}+2\cdot\mathbf 1_{[j,d+2]}\). This gives a nonzero \(u\) with
\(\langle u,X_i\rangle=\langle u,X_j\rangle=1\) and \(\langle u,X_m\rangle=0\) otherwise, so the
family \(\{X_m\}_{m\ne 1,i,j}\cup\{X_i-X_j\}\) is linearly dependent. Flipping the sign of \(X_j\)
and permuting turns this into the family \(F_2\) of the paper, which is independent almost surely
by (GP). This argument is not formalized.

## 3. Generalization C: the conic (linear) problem gives type-B Eulerian numbers

Now drop the affine structure. Regard \(d+1\) walk points \(S_1,\dots,S_{d+1}\in\mathbb R^d\) as
*vectors*. In general linear position they have a unique linear dependence \(g\), and its sign
classes form the *linear Radon partition*: the positive hulls of the two classes meet outside 0. If
one class is empty, the vectors positively span \(\mathbb R^d\), i.e. 0 is in the interior of their
convex hull. The same Abel summation gives \(\sum G_mX_m=0\), but now **without** the constraint
\(G_1=0\), because there is no row of ones. So \(g_i=G_i-G_{i+1}\) with \(G_{d+2}:=0\): the circle
becomes a line ending in \(0\). The values \(G_i\) are no longer anchored at \(0\), so permutations
alone do not suffice. With sign-exchangeable increments one averages over all signed permutations,
and the count becomes the number of signed permutations \(w\) for which \((w_1,\dots,w_n,0)\) has
\(k\) ascents. This is the type-B Eulerian number \(B(n,k)\) (`eulerB`).

**Theorem C.** Let \(X_1,\dots,X_{d+1}\) have a law invariant under permutations and sign changes,
with the walk vectors in general linear position almost surely and no ties. Write \(n=d+1\). Then
for the smaller part \(\tau_{\rm lin}\) of the linear Radon partition,
\[
\mathbb P(\tau_{\rm lin}=k)=\frac{2B(n,k)}{2^n n!}\quad(2k<n),\qquad
\mathbb P(\tau_{\rm lin}=n/2)=\frac{B(n,n/2)}{2^n n!}.
\]
In particular, with \(k=0\),
\[
\mathbb P\big(\mathrm{pos}(S_1,\dots,S_{d+1})=\mathbb R^d\big)=\mathbb P\big(0\in\operatorname{int}\operatorname{conv}(S_1,\dots,S_{d+1})\big)=\frac{1}{2^d\,(d+1)!}.
\]

Lean: deterministic form `card_linRadonMin_signedWalk` (`Conic.lean`); probabilistic form
`prob_linRadonMin_walk`; symmetry \(B(n,k)=B(n,n-k)\) as `eulerB_symm`; values in `eulerB_table`:
\(B(2,\cdot)=1,6,1\), \(B(3,\cdot)=1,23,23,1\), \(B(4,\cdot)=1,76,230,76,1\). For example:

| d | \(\mathbb P(\tau_{\rm lin}=0)\) | \(\mathbb P(\tau_{\rm lin}=1)\) | \(\mathbb P(\tau_{\rm lin}=2)\) |
|---|---|---|---|
| 1 | 1/4 | 3/4 | |
| 2 | 1/24 | 23/24 | |
| 3 | 1/192 | 19/48 | 115/192 |

A Monte Carlo run for \(d=2\) with Gaussian and with uniform-square increments gave
\(\mathbb P(\tau_{\rm lin}=0)\approx 0.0415\), compared with \(1/24\approx0.0417\) (exploratory only).
The same averaging shows that the full *labelled* linear Radon partition has a universal law under
sign-exchangeability, with no rotation needed: averaging runs over the whole group \(B_n\). The
combinatorial core is `card_signed_snoc_eq`; only the \(\tau_{\rm lin}\) statement is formalized at
the walk level. The no-ties lemma needed here (the analogue of Lemma 4.3: \(G_i\ne0\), \(G_i\ne\pm G_j\)) follows by the
argument sketched in §2, comparing with the families obtained by deleting one vector. It is not
formalized.

The Kabluchko–Panzo paper cited in the uploaded paper treats conic analogues, including positive
hulls of walks. I have not checked whether Theorem C appears there in an equivalent form.

---

## 4. Where the method stops (exact counterexamples, kernel-checked)

Any exchangeable law can be realized by putting a fixed list of vectors in uniformly random order,
and then probabilities are proportions of orderings. `Counterexamples.lean` computes such
proportions exactly, checked by the kernel with `decide +kernel`.

1. **\(n=d+3\) points.** For five points of a planar walk, every ordering of the two vector lists
   used is in general position. Yet the probability of convex position is \(38/120\) for one list
   and \(30/120\) for the other (`fivePoints_not_universal`). So universality of the full
   combinatorial type fails beyond \(d+2\) points. In the method, the Gale dual is a sequence of
   vectors in \(\mathbb R^{n-d-1}\), and the count over orderings depends on its order type. In
   Monte Carlo runs the expected number of vertices stayed the same across laws (about 4.167),
   while the distribution changed (exploratory only).
2. **Several walks (open question 2 of the paper).** For two walks with two points each in the
   plane, the probability that one point lies inside the triangle of the other three is \(4/24\)
   for one list and \(16/24\) for another (`twoWalks_not_universal`). For a single 4-point walk,
   both lists give \(8/24=1/3\), as Theorem 1.4 predicts. So for \(r=2\) nothing of the Eulerian
   universality survives the passage from Gaussian to exchangeable steps, at least for \(\tau=1\).
   In the method, the constraint \(\sum_b G_{\text{first}(b)}=0\) couples the blocks, the averaging
   group shrinks, and the count depends on the values.
3. **Stationary, non-exchangeable increments (open question 3).** Let \(\theta\) be uniform and
   \(X_m=(\cos(\theta+m\alpha),\sin(\theta+m\alpha))\), with \(\alpha/2\pi\) irrational. This
   sequence is stationary, and ergodic because rotation by an irrational angle is ergodic. The
   points \(S_1,\dots,S_4\) are distinct and lie on a circle, so \(\mathbb P(\tau=1)=0\ne1/3\).
   This argument is in prose only; it is not formalized.

## 5. Summary

* **Generalizations obtained with the same method:**
  - Theorem 1.4 needs only invariance under permutations fixing the first increment.
  - Necklace universality (Theorem A) gives the law of every rotation-invariant feature of the
    Radon partition in time order, for example \(P(\{S_1,S_3\}\mid\{S_2,S_4\})=1/3\) for \(d=2\).
  - For symmetric increments, the whole labelled Radon partition has a universal law (Theorem B).
  - The conic version (Theorem C) gives type-B Eulerian numbers, including
    \(P(0\in\operatorname{int}\operatorname{conv}(S_1,\dots,S_{d+1}))=1/(2^d(d+1)!)\).
* **Limits:** universality fails for \(d+3\) points, for two walks, and for stationary
  non-exchangeable steps. The first two are exact, kernel-checked counterexamples; the third is a
  prose argument.
* **What is formalized:** everything in the Lean files is proved in Lean. That covers the
  combinatorics (Lemma 4.4, pattern universality, signed versions, Eulerian and type-B symmetry), the
  Gale-dual/walk link (Lemma 4.2 and its conic analogue), the deterministic counting theorems, and
  the averaging step. **Not formalized:** general position giving a one-dimensional dual space
  (Lemma 2.1), the no-ties lemmas (Lemma 4.3 and its signed and conic analogues), and measurability
  of the events. These enter the probabilistic theorems as explicit hypotheses.

Files: `RequestProject/Patterns.lean`, `SignedPatterns.lean`, `Walk.lean`, `Generalizations.lean`,
`Conic.lean`, `Probability.lean`, `Examples.lean`, `Counterexamples.lean`.
