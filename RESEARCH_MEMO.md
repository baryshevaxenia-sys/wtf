# Research memo: extending the Sylvester–Radon theorem for random walks (Theorem 1.4) from d+2 to n points

**Sources.** [SR] = *The Sylvester–Radon problem for random walks and linear images of Gaussian samples* (`sylvester_radon.pdf`).
[RP] = *Random Permutations, lecture notes 1–4* (`random_permutations_lectures_1-4.pdf`).

**Numbering.** Theorem 2.17 and the three results you called Corollaries 2.13, 2.16, 2.26 are all in **[RP]**, not in [SR]. In [RP] they are labelled *Theorem 2.13, 2.16, 2.26*. They are consequences of Theorem 2.17 (2.26 through 2.13), so calling them corollaries is accurate. Section 2 of [SR] contains only Lemma 2.1, Definition 2.2, Remark 2.3, Lemma 2.4 and Corollary 2.5. The memo uses the [RP] numbering throughout.

**How each claim was checked.**
* **[Lean]**: machine-checked in this project, with no `sorry` and only the standard axioms `propext`, `Classical.choice`, `Quot.sound`. No `native_decide` is used; the finite checks run through the kernel (`decide +kernel`).
* **[Proof]**: proved on paper in this memo. Not formalized.
* **[Numerics]**: exact integer or rational enumeration in throw-away scripts. Evidence only, not a verification.

---

## 0. Summary

1. **The literal generalization is false.** "For n = k walk points the law of the Radon type is universal" fails already for d = 2 and n = d+3 = 5. There are two exchangeable walks in ℝ², both surely in general position, whose five points are in convex position with probabilities 1/4 and 1/3. **[Lean]**, `RequestProject/SylvesterRadon/Counterexample.lean`, theorem `convexPosition_not_universal`.
2. **What does generalize is the expectation.** Let N_m(S) be the number of m-subsets I ⊂ [n] with conv S_I ∩ conv S_{I^c} ≠ ∅. Then E N_m(S) is universal for every n ≥ d+2 (Theorem A below). For n = d+2, N_m = 1{τ ∈ {m, n−m}}, so Theorem A is exactly Theorem 1.4. For n = d+3 the formula is explicit:
   E N_m = n·(A(n−2,m−1)+A(n−2,m−2)) / (n−2)!.
   Status: **[Proof]** for n = d+3 (elementary); **[Proof]** for general n, using standard hyperplane-arrangement facts (Zaslavsky's theorem, Euler characteristic). **[Numerics]** agree in every case tested.
3. **Gale duality supplies the mechanism.** The Gale dual of n walk points is the edge-vector configuration of a closed polygon on n points in ℝ^{n−d−1}. Exchangeability makes the cyclic order of the polygon uniformly random. For n = d+2 the polygon lives on a line, and counting depends only on the n values (Eulerian numbers, Lemma 4.4 of [SR]). For n ≥ d+3 the count over cyclic orders depends on the dual point configuration: that is the precise obstruction. Additive (linear) statistics survive after an Euler-characteristic cancellation, whose key input is the new Lemma M below.
4. **Role of [RP] Theorem 2.17.** Applied to affine sections of the Gale space, it counts the orderings (Weyl chambers) realized by the dual configuration. That is exactly the face-count input to Theorem A. Theorems 2.13, 2.16 and 2.26 are Theorem 2.17 for other convex sets Q. Their statistics depend on the position of a point in the walk, which is not universal on its own.

---

## 1. Precise statements

### 1.1 [SR] Theorem 1.4 (Sylvester–Radon problem for random walks)
Let X_1,…,X_{d+2} be exchangeable random vectors in ℝ^d, with S_i = X_1+…+X_i. Assume

**(GP)**: almost surely S_1,…,S_{d+2} are in general position, i.e. no d+1 of them lie on an affine hyperplane.

For d+2 points in general position the Radon partition {I, I^c} is unique, and τ_S = min(|I|, |I^c|). Then for 1 ≤ k < (d+2)/2,

  P(τ_S = k) = 2A(d+1, k−1)/(d+1)!,

and P(τ_S = (d+2)/2) = A(d+1, d/2)/(d+1)! when d is even. Here A(n, j) is the Eulerian number.

**Proof structure in [SR].**
* Lemma 2.1: the dual vector g ∈ ker Ŝ, where Ŝ is the matrix S with a row of ones appended, is unique up to scale and has no zero coordinates. The sign classes of g form the Radon partition.
* Lemma 4.2 (circular representation): write g_i = G_i − G_{i+1} cyclically, with G_1 = 0 and XG = 0.
* Lemma 4.3: exchangeability together with (GP) rules out ties among G_1,…,G_{d+2}.
* Lemma 4.4: over the (d+1)! cyclic orders of d+2 distinct reals, the number with j cyclic ascents is A(d+1, j−1).
* Step 3: average over the permutations fixing 1.

### 1.2 [RP] Theorem 2.17
Let Q ⊂ ℝ^n be convex. For σ ∈ Sym(n) put
* K_σ = {t : t_{σ(1)} ≥ … ≥ t_{σ(n)}} (Weyl chambers);
* F_σ = {t : t is constant on each cycle of σ}.

Then A_n(Q) := #{σ : K_σ ∩ Q ≠ ∅} equals B_n(Q) := #{σ : F_σ ∩ Q ≠ ∅}.

### 1.3 The three consequences of Theorem 2.17 in [RP]
For x_1,…,x_n ∈ ℝ^d, write s_k(σ) = x_{σ(1)}+…+x_{σ(k)}, and s_γ = Σ_{i∈γ} x_i for a cycle γ of σ.
* **Theorem 2.13.** For every y, Σ_σ 1{y ∈ pos(s_1(σ),…,s_n(σ))} = Σ_σ 1{y ∈ pos(s_γ : γ ∈ C(σ))}. Proof: Theorem 2.17 with Q = {t ≥ 0 : Σ t_i x_i = y}.
* **Theorem 2.16.** The same identity with conv(0, s_1(σ),…,s_n(σ)) on the left and the zonotopes ⊕_γ [0, s_γ] on the right. Proof: Q = {t ∈ [0,1]^n : Σ t_i x_i = y}.
* **Theorem 2.26.** #{σ : 0 ∉ conv(s_1(σ),…,s_n(σ))} = #{σ : 0 ∉ conv(s_γ : γ ∈ C(σ))}. Proof: lift to ℝ^{d+1} and apply Theorem 2.13.

### 1.4 The Gale transform used
Let x_1,…,x_n ∈ ℝ^d affinely span ℝ^d and put r = n−d−1. Choose a basis of ker X̂ ⊂ ℝ^n, where X̂ is the matrix with columns x_i and a row of ones appended. Its rows γ_1,…,γ_n ∈ ℝ^r form the **Gale dual**. Every kernel vector has the form (⟨u, γ_k⟩)_k with u ∈ ℝ^r. Standard facts, as in [SR] Remark 2.3:
* (G1) {x_i : i ∈ J} is affinely independent ⇔ {γ_k : k ∉ J} spans ℝ^r. Hence **(GP) ⇔ every r of the γ_k are linearly independent.**
* (G2) {I, I^c} is a Radon partition ⇔ there is u ≠ 0 with ⟨u, γ_k⟩ ≥ 0 on I and ≤ 0 on I^c. Under (GP), the zero set of such a u has at most r−1 elements, and the corresponding γ's are independent, so u can be perturbed to strict signs. Consequence: **Radon partitions ↔ topes (regions of the central arrangement {γ_k^⊥}), up to ±.** The number of m-subsets I with {I, I^c} Radon equals the number of topes whose positive part has m elements.

---

## 2. Where d+2 enters Theorem 1.4, and why n points cannot be handled the same way

* **In the statement.** For n = d+2, (GP) makes the Radon partition *unique* (Lemma 2.1 of [SR]). So τ is a single random variable, and the combinatorial type of the hull is a function of τ (Corollary 2.5). For n ≥ d+3 there are 2^{n−1} − Σ_{k≤d} C(n−1, k) Radon partitions (Cover–Eckhoff). There is no canonical τ; only the vector of counts (N_m)_m, or the order type, remains.
* **In the proof.** n = d+2 means r = n−d−1 = 1: the Gale dual consists of *real numbers*. Lemma 4.2 generalizes to all n (see §4.1, **[Lean]**). The Gale dual of the walk is always the set of edge vectors P_{σ(k)} − P_{σ(k+1)} of a *closed polygon* whose vertex set V = {P_1 = 0, P_2, …, P_n} lies in ℝ^r. Permuting the increments (σ(1) = 1) permutes the vertices (Step 2 of [SR]). Averaging therefore reduces any statistic Φ of the order type to

  (★) P(Φ(S) ∈ E) = E[ c_Φ(V) ] / (n−1)!, with c_Φ(V) = #{cyclic orders of V whose polygon has Φ ∈ E}.

  For r = 1, V is n distinct reals and c_Φ depends only on distinctness (Lemma 4.4). **For r ≥ 2, c_Φ(V) depends on the configuration V ⊂ ℝ^r.** This is the obstruction. The finite de Finetti representation (every exchangeable vector is a mixture of uniformly permuted fixed lists) shows that (★) is also sufficient: Φ has a universal law if and only if c_Φ is constant on configurations satisfying (GP).

---

## 3. What happens under Gale duality

| primal (walk) | Gale dual |
|---|---|
| n points S_1..S_n in ℝ^d | n edge vectors of a closed polygon on V ⊂ ℝ^r, r = n−d−1 |
| permuting increments (σ(1)=1) | changing the cyclic order of the polygon on the fixed vertex set V |
| (GP) for all permuted walks | every r edges of every Hamiltonian cycle on V are independent. Equivalently (§4.4), the differences {P_a − P_b} have the matroid of the rank-r truncation of the graphic matroid of K_n. |
| Radon partition {I, I^c} | tope of the edge-normal arrangement 𝒜_c = {(P_{c(k)} − P_{c(k+1)})^⊥} |
| m-subset side of a Radon partition | tope u whose height sequence ⟨u, P_{c(·)}⟩ has m cyclic descents |
| no ties (Lemma 4.3 of [SR]) | P_a ≠ P_b (r = 1). For general r: difference-genericity, which follows from (GP) (§4.4). |

* **Harder hypotheses.** Universality of the *law* would require c_Φ(V) to be constant for all V ⊂ ℝ^r with r ≥ 2. It is not (§5.1).
* **Easier hypotheses.** Genericity is automatic. Exchangeability plus (GP) already implies the full genericity needed on the dual side (§4.4). No density assumption is needed.

---

## 4. Theorems and proofs

Notation: n ≥ d+2, r = n−d−1, and

  N_m(S) = #{I ⊂ [n] : |I| = m, conv{S_i}_{i∈I} ∩ conv{S_j}_{j∉I} ≠ ∅},  1 ≤ m ≤ n−1.

Two simple facts:
* N_m = N_{n−m}.
* The number of Radon partitions with parts of sizes {m, n−m} is N_m for m ≠ n/2, and N_m/2 for m = n/2.

Equivalently, n choose m minus N_m is the number of **m-sets** of the point set (subsets cut off by a hyperplane).

**Combinatorial quantities.**
* For a composition α = (α_1,…,α_s) of n, colour n labelled beads with colours 1 < … < s, using α_b beads of colour b. M_m(α) is the number of cyclic orders of the beads in which no two neighbours have the same colour and exactly m steps go to a smaller colour.
* g(m′, k) = Σ_{i<k} c(m′, m′−i) + |Σ_{i<k} (−1)^i c(m′, m′−i)|, where c = unsigned Stirling numbers of the first kind. This is the number of regions of the rank-k truncation of the braid arrangement. In particular g(m′,1) = 2, g(m′,2) = m′(m′−1), and g(m′, m′−1) = m′!.

### Theorem A (expected Radon counts are universal for every n)
Let X_1,…,X_n be exchangeable in ℝ^d, S_i = X_1+…+X_i, n ≥ d+2, and assume (GP). Then for 1 ≤ m ≤ n−1,

  E N_m(S) = T_{n,r}(m) / (n−1)!,

where

  T_{n,r}(m) = Σ_{λ ⊢ n, n−ℓ(λ) ≤ r−1} (−1)^{n−ℓ(λ)} · g(ℓ(λ), r−n+ℓ(λ)) · [n! / (∏ λ_i! ∏_j mult_j(λ)!)] · M_m(λ).

Here M_m(λ) means M_m of any composition with parts λ; by Lemma M it does not depend on the order of the parts.

**Special cases.**
* **r = 1 (n = d+2).** Only λ = 1^n contributes: T = 2·A(n−1, m−1). This gives E N_m = 2A(d+1, m−1)/(d+1)!, which is **Theorem 1.4**, including the parity rule for m = n/2.
* **r = 2 (n = d+3).** T = n(n−1)·[A(n−2, m−1) + A(n−2, m−2)], so

  **E N_m(S) = n·(A(n−2, m−1) + A(n−2, m−2)) / (n−2)!.**

  For example, d = 2: E(#points inside the hull of the others) = 5/6, and E N_2 = 25/6. The Lean file checks the first value exactly for the two explicit walks (100 out of 120 orderings, `interior_count_xA`, `interior_count_xB`).
* **r = n−2 (d = 1).** E N_m = C(n, m) − 2, as it must be: points on a line have exactly two m-sets.
* **m = 1.** E N_1 = n − E f_0(conv S). This agrees with the known Stirling-number formula for expected vertex numbers of random walks ([SR] ref. [14]); checked numerically for several (n, d).

**Numerical check [Numerics].** Two independent brute-force computations agree with T_{n,r} for (n, r) = (5,1), (5,2), (5,3), (6,2), (6,3), (6,4), (7,2), (7,3), (7,4), (7,5), each on several random configurations:
* primal: hull-intersection tests over all n! orderings of random integer increments;
* dual: topes of polygons over all cyclic orders of random V.

A few values:

| (n,d) | T_{n,r}(1..n−1) |
|---|---|
| (5,2) | 20, 100, 100, 20 |
| (6,2) | 172, 992, 1512, 992, 172 |
| (6,3) | 30, 360, 660, 360, 30 |
| (7,2) | 1512, 9744, 18984, 18984, 9744, 1512 |
| (7,3) | 352, 4524, 10964, 10964, 4524, 352 |

### 4.1 Step 1: circular representation for general n [Lean]
`RequestProject/SylvesterRadon/WalkGale.lean`:
* `sum_smul_walkPoint`: Σ_k g_k S_k = Σ_i G_i x_i, with G_i = g_i+…+g_{n−1} (summation by parts).
* `walk_affineDependence_iff`: g is an affine dependence of the walk points ⇔ G_0 = 0 and Σ G_i x_i = 0.
* `cyclicDiff_affineDependence_iff`: under the cyclic convention G_0 = 0 = G_n, the cyclic differences g_k = G_k − G_{k+1} form an affine dependence ⇔ Σ G_i x_i = 0.
* `affineDependence_eq_cyclicDiff`: every affine dependence arises this way.
* `cyclicDiff_neg_iff`: negative coordinates of g ↔ cyclic ascents of G.

Taking a basis of the r-dimensional space of admissible G turns the Gale dual into the polygon edges P_{c(k)} − P_{c(k+1)}.

### 4.2 Step 2: averaging [Proof]
This repeats Steps 1–3 of [SR] word for word, using the polygon form of Step 2. On the almost-sure event where every permuted walk S^σ (σ(1) = 1) satisfies (GP):

  Σ_{σ(1)=1} N_m(S^σ) = Σ_{c cyclic order of V} #{topes of 𝒜_c with m positive coordinates} =: T(V).

Hence E N_m(S) = E T(V)/(n−1)!, and it remains to show that T(V) is a constant.

### 4.3 Step 3: Euler characteristic over the difference arrangement [Proof]
Let ℬ = {(P_a − P_b)^⊥ : a < b}. It refines every 𝒜_c and is essential. Each region ρ of 𝒜_c meets the sphere S^{r−1} in an open (r−1)-cell, which is partitioned into the ℬ-faces it contains. Additivity of the compactly supported Euler characteristic gives Σ_{F⊂ρ} (−1)^{dim(F∩S)} = (−1)^{r−1}.

Each ℬ-face F determines a weak order w_F of V (ties = blocks of a set partition π_F, with t(F) = n − |π_F|, and dim(F ∩ S) = r−1−t(F)). The face F lies inside a region of 𝒜_c exactly when no c-adjacent pair is tied, and that region's m equals the number of cyclic descents of c relative to w_F. Summing over c and ρ:

  T(V) = Σ_{ℬ-faces F} (−1)^{t(F)} · M_m(composition of w_F).

### 4.4 Step 4: (GP) ⇒ difference-genericity [Proof]
A forest F ⊂ E(K_n) with at most r edges has difference vectors spanning the same space as those of a *linear* forest on the same vertex blocks: the span of differences on a vertex set does not depend on the tree used. A linear forest with at most r ≤ n−2 edges lies inside a Hamiltonian cycle, and (GP) makes its edges independent by (G1). Hence the matroid of ℬ is the rank-r truncation of the graphic matroid of K_n.

Consequently, for every set partition π with t(π) ≤ r−1, the faces with tie partition π are the regions of a restriction whose intersection lattice is the rank-(r−t) truncation of the partition lattice of |π| blocks. There are g(|π|, r−t(π)) such faces (Zaslavsky's theorem). For t(π) ≥ r there are none.

*Link with [RP] Theorem 2.17.* Take Q = (generic affine hyperplane) ∩ L_V, where L_V = {(⟨u, P_i⟩)_i : u ∈ ℝ^k} ⊂ ℝ^m. Then Theorem 2.17 gives

  #(orderings realized with ⟨a, u⟩ > 0) = B_m(Q) = #{σ ∈ Sym(m) : cyc(σ) ≥ m−k+1} = Σ_{i<k} c(m, m−i).

This yields the recursion g(m,k) + g(m,k−1) = 2Σ_{i<k} c(m, m−i), which determines g. This is where Theorem 2.17 enters the proof.

### 4.5 Step 5: Lemma M [Proof, new]
**Lemma M.** M_m(α) depends only on the multiset of parts of α.

*Proof.* It suffices to swap two adjacent parts α_b = p and α_{b+1} = q. Count coloured cyclic words instead of bead arrangements (the two counts differ by the factor ∏ α_i! / n). In a valid word, the letters b and b+1 form maximal segments that alternate between b and b+1.

Define φ: swap b ↔ b+1 inside every segment of **odd** length, and leave even segments alone.
* Odd segments contain one more copy of their end letter, and even segments are balanced. So the content (p, q) becomes (q, p).
* Inside an odd segment the number of internal steps is even, and they alternate ascent/descent. Flipping them preserves the descent count.
* Steps into and out of a segment compare with letters < b or > b+1, so they are unchanged.
* If the whole circle uses only b and b+1, then p = q and the identity map works.

φ is an involution between valid words of contents α and α′ that preserves the number of cyclic descents. ∎

(Checked numerically for all 126 compositions of n = 2,…,7. [Numerics])

### 4.6 Assembly
By Steps 3–5, T(V) = Σ_π (−1)^{t(π)} g(|π|, r−t(π)) M_m(λ(π)). This is independent of V. Grouping the set partitions π by their type λ gives T_{n,r}(m). ∎

### 4.7 Elementary proof for n = d+3 (r = 2) [Proof]
Rotate u around the circle. The tope changes exactly when the ranking of V swaps a pair that is adjacent in c. There are n(n−1) swap events per full turn, each between two consecutive ranks i, i+1. So

  T(V) = Σ_events #{c : the swapped pair is c-adjacent and cdes_c = m}.

Cyclically rotating the values (v ↦ v+1 mod n) preserves the number of cyclic descents, because the top element contributes one ascent in and one descent out. So the summand does not depend on i. Gluing the adjacent pair gives A(n−2, m−1) + A(n−2, m−2). Hence T = n(n−1)(A(n−2, m−1) + A(n−2, m−2)). (GP) alone forces the needed genericity (no parallel differences), because any two disjoint or overlapping pairs lie on a common Hamiltonian cycle.

---

## 5. Counterexample and corrected statement

### 5.1 The distribution is not universal (n = d+3, d = 2) [Lean]
Take the "urn" walks: X_k = x_{σ(k)} with σ uniform in Sym(5). These are exchangeable (`urn_exchangeable`). Use

  xA = ((2,−1), (1,2), (1,−4), (0,−2), (2,3)),  xB = ((−1,−2), (−1,−1), (2,−2), (−1,−4), (−4,2)).

* All 120 orderings of each list give 5 points in the plane with no three collinear (`generalPosition_xA/xB`).
* P(convex position) = 30/120 = **1/4** for xA and 40/120 = **1/3** for xB (`prob_convex_xA/xB`).
* The combined statement is `convexPosition_not_universal`.
* Nevertheless, Σ_σ #{interior points} = 100 for both lists, as Theorem A predicts (`interior_count_xA/xB`).

For five points in the plane, the law of (N_1, N_2), the order type and the face vector all determine one another. Since N_1 + N_2 = 5 always, the law is a one-parameter family with the mean fixed. Random integer lists give P(convex)·120 ∈ {30, 32, …, 40} [Numerics]; the extreme values are not determined. The contrast is with n = d+2: the first four and the last four increments of each list give 16/24 convex orderings [Numerics], as Theorem 1.4 predicts (A(3,1)/3! = 2/3).

### 5.2 Corrected statement
* **k = n = d+2:** Theorem 1.4. The full law is universal.
* **k = n > d+2:** the full law of the Radon/order type is **not** universal (Lean counterexample for n = 5, d = 2). **The expectations E N_m are universal** (Theorem A), equivalently the expected numbers of m-sets. Only exchangeability and (GP) are assumed; no parity condition is needed, and the m = n/2 case is handled by counting ordered I.
* **k = n < d+2:** points in general position are affinely independent, so there are no Radon partitions and N_m ≡ 0. This is consistent with T = 0 when r ≤ 0. The only meaningful variant is to project to ℝ^{n−2}: if πX is exchangeable and in general position, Theorem 1.4 applies in dimension n−2 unchanged.

---

## 6. Edge cases
* **d = 1.** Every configuration has the same order type, so N_m = C(n, m) − 2 surely and the law is trivially universal. The counterexample needs d ≥ 2.
* **d = 2.** n = 4: Theorem 1.4. n = 5: the Lean counterexample for the law; E N_1 = 5/6 and E N_2 = 25/6 are universal.
* **d = 3.** n = 5: Theorem 1.4. n = 6: E N_m = (1/4, 3, 11/2, 3, 1/4) by the r = 2 formula. A counterexample to the law is expected but not computed.
* **Degenerate walks.** (GP) cannot be dropped: [SR] gives a trapezoid example with ties, and collinear walks make τ undefined. Exchangeability is used twice, for the averaging and for transferring (GP) to all permuted walks, which is what yields Lemma 4.3 and §4.4. Stationary non-exchangeable increments are open ([SR] §7, item 3).
* **Does Gale duality preserve the hypotheses?** Yes. (GP) ⇔ every r Gale vectors are independent. For walks, after exchangeability, this is equivalent to (GP) of all permuted walks, which gives full difference-genericity (§4.4).
* **Position-dependent events.** Theorem 2.26 of [RP] (with Wendel's formula under symmetry) handles events such as {S_n ∈ conv(others)}. Such events are not universal without symmetry: for d = 1 with positive increments, P(S_n extreme) = 1. Only statistics symmetric in the positions are universal. The cyclic averaging exploits exactly that symmetry.

---

## 7. Lean formalization status and outline
**Done.**
* `SylvesterRadon/Counterexample.lean`: exact certificates for membership in convex hulls (barycentric weights) and non-membership (separating functionals); soundness lemmas over ℝ×ℝ; general position via determinants; the exchangeable urn model as a `PMF`; the counterexample; the interior counts.
* `SylvesterRadon/WalkGale.lean`: the general-n circular representation.

**Outline for Theorem A.**
1. Definitions: `RadonPartition`, `N_m`, `GeneralPosition` (the `AffineIndependent` families of size d+1), `cdes` on `ZMod n`-indexed words, `M_m`.
2. Lemma M (the involution φ): pure combinatorics, feasible.
3. Gale duality (G1)–(G2): linear algebra over `Matrix.ker`. Mathlib has no Gale transform, so it must be built.
4. Topes and the Euler-characteristic identity: Mathlib has no hyperplane arrangements, face posets or Zaslavsky's theorem. This is the main missing infrastructure. For r = 2 one can avoid it and use the rotation argument of §4.7 with explicit angular orderings.
5. The exchangeable averaging (Step 3 of [SR]) with `MeasureTheory` and permutation invariance of the law.

A likely route is `import Mathlib`, with `Mathlib.Analysis.Convex.*`, `Mathlib.LinearAlgebra.AffineSpace.Independent`, `Mathlib.Probability.*` and `Mathlib.Combinatorics.Enumerative.*` as the relevant parts.

---

## 8. Open questions
1. Is there a closed form or generating function for M_m(λ), and hence for T_{n,r}? For r ≤ 2 it reduces to Eulerian numbers.
2. What is the range of the law of the order type for n = d+3 over exchangeable walks satisfying (GP)? For example, what are the extreme values of P(convex position) for d = 2, n = 5 (30/120 … 40/120 observed)?
3. Are higher *symmetric* moments universal (e.g. E[N_m(N_m − 1)])? For n = 5, d = 2 the answer is no, since the law is not universal while the mean is. What is the largest class of universal statistics?
4. Is there an analogue of Theorem A for the Gaussian mixtures S = XA of [SR] Theorem 1.3, where the Gale polygon has a Gaussian law?
5. Can the Euler-characteristic step be replaced by a direct generalization of [RP] Theorem 2.17 in which Q is replaced by the family of polygons?
