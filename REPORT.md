# Conic and Tverberg-type extensions of Barysheva's Theorem 1.4: literature-first report

This report continues the earlier investigation (`GENERALIZATIONS.md`, the Lean files in
`RequestProject/`). **No new Lean code was written at this stage.** Everything new below is a
handwritten proof, an exact finite computation (rational arithmetic, exhaustive enumeration of the
symmetry orbit of a fixed increment list), or a numerical linear-programming check. The scripts are
in `experiments/` (see §12).

## Labels used throughout

| label | meaning |
|---|---|
| **[KNOWN]** | stated and proved in the cited literature (reference, theorem number given) |
| **[KNOWN-implicit]** | follows from cited results by a short, standard argument written out here; not stated there in this form |
| **[PROVED]** | proved in this investigation (handwritten proof given here) |
| **[PROVED-sketch]** | proved here; every step is given, but routine measure-theoretic or genericity details are only indicated |
| **[COND]** | conditionally proved (the condition is stated) |
| **[CONJ]** | conjectural (supported by exact computations, which are listed) |
| **[HEUR]** | heuristic |
| **[FALSE]** | false; the counterexample is given |
| **[NU]** | novelty unresolved: no source found in the search described, but the search cannot be called exhaustive |

"Exact computation" means: an exchangeable (resp. sign-exchangeable) law is realised by putting a fixed
integer list of increments in uniformly random order (resp. uniformly random order and signs). All
probabilities are then exact rationals, computed by enumerating the whole group orbit with integer
determinants. Linear-programming checks (used only for Tverberg-type existence questions) are
floating-point and are labelled as numerical.

## Standing notation

* \(X_1,\dots,X_N\in\mathbb R^d\) increments, \(S_i=X_1+\dots+X_i\).
* **(Ex)** exchangeable: \((X_{\sigma(1)},\dots,X_{\sigma(N)})\overset d=(X_1,\dots,X_N)\).
* **(±Ex)** sign-exchangeable (= "symmetrically exchangeable" in Kabluchko–Vysotsky–Zaporozhets):
  \((\varepsilon_1X_{\sigma(1)},\dots,\varepsilon_NX_{\sigma(N)})\overset d=(X_1,\dots,X_N)\) for all \(\sigma\), all signs \(\varepsilon\).
* **(GP\(_{\rm lin}\))** general linear position: every \(d\) of \(S_1,\dots,S_N\) are linearly independent a.s.
* \(S\) also denotes the \(d\times N\) matrix with columns \(S_i\); \(\ker S\subset\mathbb R^N\) is the
  dependency space (the linear Gale dual), of dimension \(N-d\) under (GP\(_{\rm lin}\)), \(N\ge d\).
* \(\mathrm{pos}(A)\) positive (conic) hull, \(\mathrm{conv}(A)\) convex hull.
* Type-B Eulerian numbers \(B(n,k)\): number of signed permutations \(w\in B_n\) with
  \(k\) descents in \((0,w_1,\dots,w_n)\); \(\sum_k B(n,k)t^k\) has rows \(1,1\); \(1,6,1\); \(1,23,23,1\); \(1,76,230,76,1\); \(1,237,1682,1682,237,1\).
  (OEIS A060187. Recurrence \(B(n,k)=(2k+1)B(n-1,k)+(2n-2k+1)B(n-1,k-1)\);
  \(\sum_{j\ge0}(2j+1)^n t^j=\sum_kB(n,k)t^k/(1-t)^{n+1}\).) In Kabluchko–Panzo the same numbers are
  written \(B\langle n,k\rangle\); they were identified by the defining generating function, not the symbol.
* \(B[n,k]\): coefficients of \((t+1)(t+3)\cdots(t+2n-1)=\sum_kB[n,k]t^k\) (type-B Stirling numbers of the first kind;
  written \(B(n,k)\) in KVZ 2016/2017 — note the clash of notation with the Eulerian numbers, resolved here by the generating functions).

---

## 1. Literature map

### 1.1 Primary sources checked in full text (original arXiv versions; journal data recorded)

| # | reference | what it proves (exact location) | assumptions | relation to this project |
|---|---|---|---|---|
| L1 | E. Barysheva, *Sylvester and Radon problems for random walks* (uploaded `sylvester_radon.pdf`) | Thm 1.4: affine Radon partition of \(S_1,\dots,S_{d+2}\); \(\mathbb P(\text{smaller part}=k)\) via Eulerian numbers; proof by 1-dim Gale dual, Abel summation, cyclic averaging (Lemmas 4.3–4.4) | (Ex), affine GP | the starting point |
| L2 | Z. Kabluchko, H. Panzo, *Sylvester's problem for random walks and bridges* (arXiv 2501.16166v2; Discrete Comput. Geom. 2026) | **Thm 3.17** = Barysheva's Thm 1.4 (affine types of \(\mathrm{conv}(S_0,\dots,S_{d+1})\)) and its bridge version; **Thm 4.1** (spherical version: probabilities of combinatorial types of \(\mathrm{pos}(X_1,\dots,X_{d+2})\cap\mathbb S^d\) expressed through expected \(f\)-vectors by triangular inversion); **Thm 4.5**: for a (±Ex) walk in \(\mathbb R^{d+1}\) with \(d+2\) steps, \(\mathbb P(\text{type }T^d_m)=\eta_{d,m}B\langle d+2,m+1\rangle/(2^{d+2}(d+2)!)\), \(\eta_{d,m}=2\) unless \(m=d/2\), where it is 1; bridge version with Eulerian numbers | (±Ex)+(GP) for walks, (Ex)+bridge+(GP′) for bridges | **contains the full law of \(\tau_{\rm lin}\) (Theorem C)**; dictionary in §2 |
| L3 | T. Godland, Z. Kabluchko, *Positive hulls of random walks and bridges* (arXiv 2104.05542v2; Stoch. Proc. Appl. 147 (2022) 327–362) | (1.4)–(1.5): \(\mathbb P(\mathrm{pos}(S_1..S_n)=\mathbb R^d)=\frac{2}{2^nn!}\sum_{r\ge0}B[n,d+1+2r]\); **Cor. 2.12**: expected face numbers of the positive hull; **Cor. 4.5**: probability that \(\mathrm{pos}(S_{i_1},\dots,S_{i_k})\) is a face, as explicit function of the index gaps; Thm 4.1 (= KVZ Adv. Math. Thm 2.1, joint absorption for several walks and bridges with product B/A symmetry) | (±Ex) (block versions allowed), (GP) | face probabilities determine the labelled law of Theorem C by Möbius inversion (§2.3) |
| L4 | Z. Kabluchko, V. Vysotsky, D. Zaporozhets, *Convex hulls of random walks, hyperplane arrangements, and Weyl chambers* (arXiv 1510.04073; GAFA 27 (2017) 880–918) | **Thm 2.1** absorption probability for bridges (Stirling numbers of the first kind); **Thm 2.3** absorption for (±Ex) walks; reduction to "number of Weyl chambers of type \(A_{n-1}\)/\(B_n\) met by a generic subspace" (Zaslavsky, Whitney) | (Ex)/(±Ex) + GP | supplies the boundary values \(Z_0,Z_N\) in our main recursion (§5) |
| L5 | Z. Kabluchko, V. Vysotsky, D. Zaporozhets, *Convex hulls of random walks: expected number of faces and face probabilities* (arXiv 1612.00249; Adv. Math. 320 (2017) 595–629) | **Thm 1.2** \(\mathbb E f_k(\mathrm{conv}(S_0..S_n))\), only (Ex); **Thm 1.6** labelled face probabilities, needs (±Ex) (Example 1.10 shows symmetry is essential); **Thm 1.11** bridges; **Thm 1.14** averages over cyclic shifts; **Thm 2.1** joint absorption, several walks + bridges | as stated | affine Theorems A/B of the earlier report are implicit here (§2.4) |
| L6 | Z. Kabluchko, V. Vysotsky, D. Zaporozhets, *A multidimensional analogue of the arcsine law for the number of positive terms in a random walk* (arXiv 1610.02861; Bernoulli 25 (2019) 521–548) | **Thm 1.2**: \(\mathbb E\#\{k\text{-subsets }C:0\notin\mathrm{conv}(S_C)\}=\binom nk\cdot 2\frac{B[k,d-1]+B[k,d-3]+\dots}{2^kk!}\); geometric form: expected number of \(k\)-faces of a uniform B-chamber not met by a generic codim-\(d\) subspace; §3.1 block-reshuffling trick; for \(d=1\) equivalent to the binomial moments of the Sparre Andersen arcsine law | i.i.d. symmetric in the abstract; the proof uses (±Ex)+GP | closest relative of our main new result (§5.3, Candidate 1); our result implies Thm 1.2 but not conversely as far as we can see |
| L7 | Z. Kabluchko, A. Tarasov (arXiv 2608.16752, 2026) | wall-crossing method: number of signed permutations with a property is invariant under deformation through walls; combinatorial Sparre Andersen (Thm 3), Thm 9, recurrences (Thm 17) | deterministic | an alternative route to deterministic orbit-sum identities (§8) |
| L8 | `Gpt.pdf` (uploaded) | permutation–cycle approach: chamber–cycle identity, positive-hull identity (Thm 3.1), non-absorption via independent cycle sums (Thm 1.1), Wendel sign counting (Lemma 6.1) | arbitrary / (±Ex) | method source (§8) |
| L9 | `random_permutations_lectures_1-4.pdf` (uploaded; Zaporozhets' lectures) | Thm 2.13 (for any \(x_1..x_n\in\mathbb R^d\), \(y\): \(\sum_\sigma 1_{C_\sigma}(y)=\sum_\sigma1_{D_\sigma}(y)\), cones of rearranged paths vs cones of cycle sums); Thm 2.16 (convex-hull/zonotope version); Thm 2.17 (any convex \(Q\subset\mathbb R^n\) meets as many Weyl chambers \(K_\sigma\) as subspaces \(F_\sigma\) counted with multiplicity; "layered cake" lemma); Thm 2.24 (absorption generating function for an arbitrary walk via independent copies); Thm 2.25 (Wendel); Thm 2.26 | none / as stated | method source (§8) |
| L10 | `rw_notes.pdf` (uploaded; Zaporozhets, *Random walks and Lévy processes*) | Thm 1.2 (Sparre Andersen), Thm 1.10 (\(\mathbb E f_1\) planar), Thm 2.2/2.4 + Lemma 2.5 (bijection: number of positive partial sums ↔ position of the maximum), Spitzer/Baxter (§3, §5–6), Thm 7.3/Cor 7.4 (face probabilities), Thm 8.1 + Lemma 8.6 (absorption via B-chambers missed by a generic subspace), §9 Zaslavsky | (Ex)/(±Ex) | method source (§8) |
| L11 | Z. Kabluchko, *Gale coupling for i.i.d. uniform cones* (arXiv 2602.08581) | Gale duality couples random cones of i.i.d. symmetric vectors | i.i.d. | shows Gale duality is used for *independent* samples; not for walks |
| L12 | J. A. De Loera, T. Hogan, *Stochastic Tverberg theorems with applications in multiclass logistic regression, separability, and centerpoints of data* (arXiv 1907.09698; SIAM J. Discrete Math. 34 (2020)) | probability that a random partition of random (i.i.d.) points is a Tverberg partition; Sarkaria-type lifting | i.i.d. points | i.i.d. analogue of our random-partition questions (§6) |
| L13 | M. White, *Radon partitions of random Gaussian polytopes* (arXiv 2507.05449) | Radon partitions of i.i.d. Gaussian samples | Gaussian i.i.d. | i.i.d. analogue |
| L14 | J. Randon-Furling, D. Zaporozhets (arXiv 2007.02768) | convex hulls of several planar Gaussian random walks | independent Gaussian walks | several-walk results (§9) |
| L15 | A. Iksanov, Z. Kabluchko, A. Marynych, V. Wachtel (arXiv 2403.16448) | \(r\)-versions of Eulerian-type numbers from walks | — | checked as a possible source of an \(r>2\) Eulerian analogue; not the same objects |
| L16 | B. Bukh, P.-S. Loh, G. Nivasch, *Classifying unavoidable Tverberg partitions* (arXiv 1611.01078; J. Comput. Geom. 8 (2017) 174–205) | which order-types of Tverberg partitions ("Tverberg types") occur in every long point sequence; families with exactly \((r-1)!^d\) Tverberg partitions | deterministic, ordered point sequences | temporal patterns of Tverberg partitions (§6) |
| L17 | P. Soberón, *An elementary proof of Sierksma's conjecture for seven points in the plane* (arXiv 2604.18485, 2026); earlier S. Hell (topological) | any 7 points in general position in \(\mathbb R^2\) have at least 4 Tverberg 3-partitions | deterministic | lower bound observed in our walk computations (§6) |
| L18 | I. Bárány, P. Soberón, *Tverberg's theorem is 50 years old: a survey* (arXiv 1712.06119; Bull. AMS 55 (2018)) | survey: Sarkaria's tensor proof, Sierksma's conjecture, colourful/topological Tverberg, counting Tverberg partitions | — | background for §6–7 |
| L19 | J.-P. Roudneff, *Partitions of points into simplices with k-dimensional intersection. Part I: the conic Tverberg's theorem*, European J. Combin. 22 (2001) 733–743 | a "conic Tverberg theorem" (title/abstract only; **full statement not accessible** in this environment) | — | possible prior source for §7.4; status of our deterministic conic statement therefore [NU] |
| L20 | W. Hansen, V. Klee, Proc. AMS 22 (1969) 450–457 | Radon-type theorems for positive (conic) sets | — | background for conic Radon |
| L21 | T. M. Cover (1965), L. Schläfli; J. G. Wendel (1962) | number of orthants met by a generic \(k\)-dim subspace of \(\mathbb R^N\): \(2\sum_{i<k}\binom{N-1}i\); Wendel's absorption probability for independent symmetric vectors | generic / independent symmetric | used in §5.1 |

Other items consulted (abstract or partial text): Panzo 2409.07927; Chan–Kalai et al. 2507.01353;
Godland–Kabluchko 2004.10466 (tessellations by \(Y_i\pm Y_j\)); Götze–Kabluchko–Zaporozhets 1911.04184.
None of them contains the statements of §5–7 below. Searches were run on arXiv (full-text API) and OpenAlex
(forward citations of L2–L6), with the terms listed in the task (linear/conic Radon, positive hulls of
random walks, absorption, positive spanning, Weyl chambers, conic intrinsic volumes, Grassmann angles,
conic Tverberg, linear Tverberg, positive Tverberg, intersections of positive hulls, Sarkaria, Sierksma,
k-sets of random walks, level sets of arrangements, multidimensional arcsine law). General web search
was not available, so MathSciNet-only or paywalled items (in particular Roudneff 2001) could not be read
in full. **All novelty statements below are therefore [NU] unless a source is cited.**

### 1.2 Equivalence dictionary (conic, \(n=d+1\) vectors in \(\mathbb R^d\), GP\(_{\rm lin}\))

| this report | Kabluchko–Panzo (L2) | Godland–Kabluchko (L3) | oriented matroids |
|---|---|---|---|
| unique dependence \(g\), \(\sum g_iS_i=0\) | Gale dual of \(d+2\) vectors in \(\mathbb R^{d+1}\) (their \(d\) shifted by one) | — | the unique signed circuit |
| \(\tau_{\rm lin}=0\) (all \(g_i\) one sign) | type \(T_{-1}\): \(\mathrm{pos}=\) whole space | absorption \(C_n^B=\mathbb R^d\) | totally cyclic / acyclic dual |
| \(\tau_{\rm lin}=k\ge1\) | type \(T_{k-1}\) | — | circuit with \(\min(|C^+|,|C^-|)=k\) |
| \(\mathrm{pos}(S_{[n]\setminus\{i,j\}})\) is a facet | facet | face event of Cor. 4.5 | \(g_ig_j<0\) |
| \(\mathrm{pos}(S_F)\) is a face, \(F\neq\emptyset\) | face | Cor. 4.5 | \(g\) not of constant sign on \(F^c\) |

Number of facets of \(\mathrm{pos}(S_1..S_n)\) is \(\tau(n-\tau)\): a facet has complement \(\{i,j\}\), and it is a facet iff \(S_i,S_j\) lie on the same side of \(\mathrm{span}(S_{[n]\setminus\{i,j\}})\), i.e. iff \(g_ig_j<0\). Hence type \(T_m\) ↔ \(\tau_{\rm lin}=m+1\), and the combinatorial type of the positive hull is exactly the unordered sign pattern of \(g\).

---

## 2. Status of Theorem C

### 2.1 The event \(\tau_{\rm lin}=0\) — **[KNOWN]**

\(\{\tau_{\rm lin}=0\}=\{\mathrm{pos}(S_1..S_{d+1})=\mathbb R^d\}=\{0\in\mathrm{int\,conv}(S_1..S_{d+1})\}\) (§4.4).
Its probability \(2/(2^nn!)\cdot B[n,n]=1/(2^d(d+1)!)\) (\(n=d+1\)) is the case \(n=d+1\) of the absorption formula
KVZ GAFA (L4) Thm 2.3 / Godland–Kabluchko (L3) eq. (1.5), and the case \(m=-1\) of Kabluchko–Panzo (L2) Thm 4.5.

### 2.2 The full distribution of \(\tau_{\rm lin}\) — **[KNOWN]**

Kabluchko–Panzo (L2), **Theorem 4.5** (walk part), with \(d\mapsto d-1\), \(m=k-1\), is *exactly* Theorem C:
\(\mathbb P(\tau_{\rm lin}=k)=\eta\,B(n,k)/(2^nn!)\), \(\eta=2\) for \(2k<n\), \(\eta=1\) for \(2k=n\).
Assumptions there: (±Ex) and (GP) (every \(d\) of the walk vectors linearly independent a.s.) — the same as ours.
Their proof is different from ours: expected face numbers of positive hulls (Godland–Kabluchko Cor. 2.12)
plus the triangular inversion of Thm 4.1 ("types ↔ expected \(f\)-vectors"). The B-Eulerian numbers arise
there from B-Stirling identities, not from a descent count.

### 2.3 The full labelled linear Radon partition — **[KNOWN-implicit]**; explicit descent form **[PROVED]**, novelty **[NU]**

**Statement (labelled law).** Under (±Ex), (GP\(_{\rm lin}\)), \(n=d+1\): for every sign vector \(s\in\{\pm\}^n\),
\[
\mathbb P\big(\mathrm{sign}(g)\in\{s,-s\}\big)=\frac{\#\{w\in B_n:\ \text{the up/down word of }(w_1,\dots,w_n,0)\in\{s,-s\}\}}{2^nn!},
\]
where the up/down word of \((a_1,\dots,a_{n+1})\) is \((\mathrm{sign}(a_i-a_{i+1}))_{i=1}^n\).

*Why it is implicitly known.* For \(\emptyset\ne F\subsetneq[n]\), \(\mathrm{pos}(S_F)\) is a face iff \(g\) is not of
constant sign on \(F^c\) (the vectors \(S_{F^c}\) modulo \(\mathrm{span}(S_F)\) have the unique dependence \(g_{F^c}\); they span a pointed cone iff that dependence is not one-signed).
Put \(f(K)=\mathbb P(g \text{ constant sign on }K)\) and \(h(A)=\mathbb P(\{\mathrm{sign}\,g\}=\{1_A-1_{A^c},\,-(1_A-1_{A^c})\})\) (so \(h(A)=h(A^c)\)).
Then for \(K\ne\emptyset\): \(f(K)=\sum_{A\supseteq K}h(A)\) (sum over all subsets \(A\)), so by Möbius inversion
\(h(A)=\sum_{K\supseteq A}(-1)^{|K|-|A|}f(K)\) for \(A\neq\emptyset\). The \(f(K)\) are \(1-\mathbb P(\mathrm{pos}(S_{K^c})\text{ is a face})\) for \(|K|\ge2\), given explicitly by Godland–Kabluchko (L3) **Cor. 4.5**; \(f(\{i\})=1\); and \(f([n])\) is the absorption probability. Hence L3 determines the labelled law. We checked numerically-exactly that the descent formula above reproduces L3 Cor. 4.5 for all faces for \(d=2,3,4\), and the labelled law itself by exhaustive orbit enumeration for \(d=2,3\) (three increment lists each; `e1.py`, `e1b.py`).

The explicit descent-set description and its proof by Gale duality/Abel summation (§4) were not found in the literature: **[PROVED]**, **[NU]**.

### 2.4 The proof method — **[PROVED]** here; the method itself is the conic transcription of Barysheva's

Gale duality + Abel summation + averaging over \(B_n\) (§4). Not found for the conic problem in L2–L6 (they use
Weyl-chamber counting / face numbers); Barysheva (L1) uses it for the affine problem with cyclic averaging. **[NU]** as a published proof, but it is a routine adaptation.

Similarly, the affine Theorems A (rotation classes, (Ex)) and B (labelled affine Radon partition, (±Ex)) of
`GENERALIZATIONS.md` are **[KNOWN-implicit]**: the labelled affine law is determined by the labelled face
probabilities of KVZ (L5) Thm 1.6 by the same Möbius inversion, and rotation-class sums by the cyclic-shift averages of L5 Thm 1.14.

### 2.5 Assumptions and strengthenings

* The no-ties conditions (\(G_i\ne0\), \(|G_i|\ne|G_j|\)) are **not** extra assumptions: they follow from (GP\(_{\rm lin}\)) + (±Ex) (§4.2). **[PROVED]**
* (±Ex) cannot be weakened to (Ex): for \(d=1\), \(n=2\), positive increments give \(\tau_{\rm lin}=1\) a.s., while the formula gives \(\mathbb P(\tau_{\rm lin}=0)=1/4\). **[FALSE without sign symmetry]**
* Block versions: the same proof works if the law is invariant only under a subgroup acting transitively enough — but the conclusion then changes; we did not pursue this. L3 Cor. 4.5 already allows block symmetry for face events.

---

## 3. Strongest surviving version of Theorem C (publication-style)

**Theorem C′.** Let \(X_1,\dots,X_n\) be random vectors in \(\mathbb R^{n-1}\) whose joint law is invariant
under the hyperoctahedral group \(B_n\) acting by \((X_i)\mapsto(\varepsilon_iX_{\sigma(i)})\), and assume that
any \(n-1\) of the partial sums \(S_1,\dots,S_n\) are linearly independent a.s. Let \(g\) span the
(one-dimensional) space of linear dependences of \(S_1,\dots,S_n\). Then a.s. every \(g_i\neq0\), and for every
set \(\mathcal D\subseteq\{\pm\}^n\) closed under global sign change,
\[
\mathbb P\big(\mathrm{sign}(g)\in\mathcal D\big)=\frac{\#\{w\in B_n:\ \mathrm{ud}(w_1,\dots,w_n,0)\in\mathcal D\}}{2^nn!}.
\]
Consequently, with \(\tau_{\rm lin}=\min(\#\{g_i>0\},\#\{g_i<0\})\),
\(\mathbb P(\tau_{\rm lin}=k)=2B(n,k)/(2^nn!)\) for \(2k<n\) and \(B(n,n/2)/(2^nn!)\) for \(2k=n\); and by §4.3–4.4
these events are, respectively, "\(\mathrm{pos}(S_I)\cap\mathrm{pos}(S_J)\ne\{0\}\) for the bipartition \(\{I,J\}\) with \(\min(|I|,|J|)=k\)" and, for \(k=0\), "\(0\in\mathrm{int\,conv}(S_1..S_n)\)".

Status: the \(\tau_{\rm lin}\) part is **[KNOWN]** (L2 Thm 4.5); the labelled part **[KNOWN-implicit]** (L3 Cor. 4.5 + Möbius); the explicit descent form and this proof **[PROVED]**, **[NU]**.
The Lean development of the earlier stage (`Conic.lean`) proves the deterministic counting core and the \(\tau_{\rm lin}\) statement with the no-ties conditions as hypotheses; §4.2 removes those hypotheses on paper.

---

## 4. Proof audit of Theorem C′ — **[PROVED]**

### 4.1 The steps and where each hypothesis enters

1. **One-dimensional Gale dual.** By (GP\(_{\rm lin}\)) the \(d\times n\) matrix \(S\) (\(n=d+1\)) has rank \(d\), so \(\ker S\) is a line \(\mathbb Rg\). Every \(g_i\ne0\): if \(g_i=0\), the remaining \(d\) vectors would be dependent.
2. **Abel summation.** \(\sum_ig_iS_i=\sum_ig_i\sum_{m\le i}X_m=\sum_mG_mX_m\) with \(G_m=\sum_{i\ge m}g_i\). Thus \(G=(G_1..G_n)\) spans \(\ker X\) (the dependence space of the increments; \(X=SU^{-1}\) with \(U\) unitriangular, so \(\dim\ker X=1\)), and conversely \(g_i=G_i-G_{i+1}\) with \(G_{n+1}:=0\).
   *Difference from the affine case:* there the row of ones forces \(\sum g_i=0\), i.e. \(G_1=0\), and the sequence closes into a circle \((0,G_2,\dots,G_{d+2})\); here nothing forces \(G_1=0\), the sequence \((G_1,\dots,G_n,0)\) is a *line* ending at \(0\), and cyclic averaging must be replaced by averaging over signed permutations (sign changes move values across the anchor 0).
3. **Covariance.** For \((\sigma,\varepsilon)\in B_n\) let \(X'_m=\varepsilon_mX_{\sigma(m)}\). Then \(G'_m=\varepsilon_mG_{\sigma(m)}\) spans \(\ker X'\). The sign vector of the new \(g'\) is the up/down word of \((\varepsilon_1G_{\sigma(1)},\dots,\varepsilon_nG_{\sigma(n)},0)\), defined up to a global sign because \(G\) is defined up to a scalar.
4. **No ties ⇒ reduction to \(B_n\).** If \(G_i\ne0\) and \(|G_i|\ne|G_j|\) (\(i\ne j\)), the \(2n+1\) numbers \(0,\pm G_i\) are distinct; replacing \(|G_i|\) by its rank gives a signed permutation \(w_0\), and \((\sigma,\varepsilon)\mapsto w=(\sigma,\varepsilon)\cdot w_0\) is a bijection \(B_n\to B_n\) under which the up/down word of step 3 equals \(\mathrm{ud}(w_1..w_n,0)\). Therefore, for every \(\omega\) outside a null set,
\[\#\{(\sigma,\varepsilon):\mathrm{sign}(g')\in\mathcal D\}=\#\{w\in B_n:\mathrm{ud}(w,0)\in\mathcal D\}.\]
5. **Averaging.** By (±Ex), \(\mathbb P(\mathrm{sign}\,g\in\mathcal D)=\mathbb E\big[\frac1{2^nn!}\sum_{(\sigma,\varepsilon)}1\{\mathrm{sign}\,g'\in\mathcal D\}\big]\), and step 4 makes the integrand constant.
6. **Type-B ascent statistic.** \(\#\{w:\ \mathrm{ud}(w_1..w_n,0)\text{ has }k\text{ descents}\}=B(n,k)\): reverse \(w\) (descents of \((w,0)\) become ascents of \((0,w_n,\dots,w_1)\)), then negate all entries (ascents become descents), a bijection of \(B_n\). \(\tau_{\rm lin}=\min(\mathrm{des},n-\mathrm{des})\) and \(B(n,k)=B(n,n-k)\) give the stated formula.

### 4.2 Which no-ties statements follow from what — **[PROVED]**

Let \(F\) be the event that some transformed walk \(X'\) (\((\sigma,\varepsilon)\in B_n\)) violates (GP\(_{\rm lin}\)). By (±Ex) each \(X'\) satisfies (GP\(_{\rm lin}\)) a.s., so \(\mathbb P(F)=0\). Off \(F\):

* **\(G_m\ne0\)** (uses (Ex) + GP only). \(G_m=0\) means \(\{X_j\}_{j\ne m}\) is dependent. Take the ordering \(\sigma\) that puts \(X_m\) last: \(\mathrm{span}(X'_1..X'_{n-1})=\mathrm{span}(S'_1..S'_{n-1})\), which is \(d\)-dimensional by GP of \(X'\). Contradiction.
* **\(G_i\ne G_j\)** (uses (Ex) + GP only). Then \(\sum_{m\ne i,j}G_mX_m+G_i(X_i+X_j)=0\), so the \(d\) vectors \(\{X_i+X_j\}\cup\{X_m\}_{m\ne i,j}\) are dependent. Order the increments as \(X_i,X_j,\) rest: these \(d\) vectors are a unitriangular transform of \(S'_2,\dots,S'_n\), independent by GP of \(X'\). Contradiction. (This is Barysheva's Lemma 4.3 argument.)
* **\(G_i\ne-G_j\)** (**needs the sign symmetry**). Flip the sign of \(X_j\): then \(G'_j=-G_j\), \(G'_m=G_m\) otherwise, and \(G_i=-G_j\) becomes \(G'_i=G'_j\) for the walk \(X'\), excluded by the previous item applied to \(X'\).

Under (Ex) alone, \(G_i=-G_j\) can have positive probability while GP holds, but this is irrelevant there because sign changes are not used. (GP\(_{\rm lin}\)) also gives \(g_i\neq0\) directly (step 1), which is the special case \(G_i\ne G_{i+1}\).

### 4.3 Two positive cones — **[PROVED]** (elementary; implicit in the oriented-matroid literature)

**Lemma 4.3.** Let \(S_1..S_N\in\mathbb R^d\) satisfy (GP\(_{\rm lin}\)), \(N\ge d+1\), and let \([N]=I\sqcup J\) with \(I,J\ne\emptyset\). TFAE:
(a) \(\mathrm{pos}(S_I)\cap\mathrm{pos}(S_J)\ne\{0\}\);
(b) \(\ker S\) meets the open orthant \(O_{I,J}=\{g:g_I>0,\ g_J<0\}\);
(c) \(\mathrm{pos}(S_I\cup(-S_J))=\mathbb R^d\);
(d) \(\mathrm{relint\,pos}(S_I)\cap\mathrm{relint\,pos}(S_J)\neq\emptyset\).
For \(N=d+1\), (b) says: the unique dependence has one strict sign on \(I\) and the opposite strict sign on \(J\).

*Proof.* (b)⇒(a): \(g\mapsto y(g)=\sum_Ig_iS_i\) is linear on \(\ker S\) and \(\ker S\cap O_{I,J}\) is relatively open in \(\ker S\). If \(y\equiv0\) there, then \(y\equiv0\) on \(\ker S\), so \(\ker S=\ker S_I\oplus\ker S_J\), whence \(\mathrm{rk}S_I+\mathrm{rk}S_J=d\). But GP gives \(\mathrm{rk}S_I=\min(|I|,d)\), and \(|I|+|J|\ge d+1\) forces \(\min(|I|,d)+\min(|J|,d)\ge d+1\). So some \(g\in\ker S\cap O_{I,J}\) has \(y(g)=\sum_Ig_iS_i=\sum_J(-g_j)S_j\neq0\), which lies in both cones. (The same \(g\) gives (d).)
(a)⇒(b): suppose \(\ker S\cap O_{I,J}=\emptyset\). Separating the subspace \(\ker S\) from the open convex cone \(O_{I,J}\) (Gordan–Stiemke alternative) gives \(0\ne c\in(\ker S)^\perp=\mathrm{row}(S)\) with \(c_I\ge0\ge c_J\); write \(c_i=\langle u,S_i\rangle\), \(u\ne0\). If \(0\ne y=\sum_I\lambda_iS_i=\sum_J\mu_jS_j\) with \(\lambda,\mu\ge0\), then \(0\le\langle u,y\rangle\le0\), so \(\lambda_i\langle u,S_i\rangle=0=\mu_j\langle u,S_j\rangle\) for all \(i,j\). Hence \(\lambda,\mu\) are supported on \(Z=\{i:\langle u,S_i\rangle=0\}\), and \(|Z|\le d-1\) by GP. Then \((\lambda,-\mu)\) is a nonzero dependence among at most \(d-1\) vectors (nonzero since \(y\ne0\)), contradicting GP.
(b)⇔(c): (c) holds iff \([S_I,-S_J]\) has a strictly positive dependence and spans \(\mathbb R^d\) (standard); the dependence is \((g_I,-g_J)\). (d)⇒(a) is trivial. ∎

Thus the number of conic Radon bipartitions is a count of open orthants met by \(\ker S\) (§5).

### 4.4 The all-one-sign case — **[PROVED]**

For \(N=d+1\) and GP: \(g>0\) ⇔ \(0\in\mathrm{int\,conv}(S_1..S_{d+1})\) ⇔ \(\mathrm{pos}(S_1..S_{d+1})=\mathbb R^d\) ⇔ \(\mathrm{pos}(S_I)\cap\mathrm{pos}(S_J)=\{0\}\) for every bipartition with \(I,J\neq\emptyset\).
*Proof.* (⇒) Let \(g>0\), normalised by \(\sum g_i=1\). An affine dependence \(a\) (\(\sum a_iS_i=0\), \(\sum a_i=0\)) is a linear dependence, so \(a=cg\), and \(0=\sum a_i=c\); hence the \(S_i\) are affinely independent, \(\mathrm{conv}(S)\) is a \(d\)-simplex, and \(0=\sum g_iS_i\) has all barycentric coordinates positive, so \(0\) is interior. (⇐) If \(0\in\mathrm{int\,conv}(S)\), the \(d+1\) points affinely span \(\mathbb R^d\), so they are affinely independent and \(\mathrm{conv}(S)\) is a simplex; the barycentric coordinates \(\lambda\) of the interior point \(0\) are all positive and \(\sum\lambda_iS_i=0\), so \(\lambda\) is a positive multiple of \(\pm g\). The equivalence with positive spanning is Lemma 4.3(c) with \(J=\emptyset\) read as "strictly positive dependence + spanning"; and if \(g>0\) no bipartition has opposite strict signs, so all cone intersections are trivial by Lemma 4.3. ∎

---

## 5. Results for \(N>d+1\) walk vectors

Throughout this section: \(S_1..S_N\in\mathbb R^d\), \(N\ge d+1\), (GP\(_{\rm lin}\)). For \(0\le q\le N\) let
\[
Z_q=\#\{I\subseteq[N]:|I|=q,\ \ker S\cap O_{I,I^c}\neq\emptyset\},\qquad Y_q=\binom Nq-Z_q .
\]
For \(1\le q\le N-1\), \(Z_q\) counts conic Radon bipartitions with \(|I|=q\) (Lemma 4.3), and \(Y_q\) counts \(q\)-sets \(I\) that are *linearly separable*: some \(u\) has \(\langle u,S_i\rangle>0\) on \(I\) and \(<0\) off \(I\). Equivalently \(Y_q\) is the number of regions of the central arrangement \(\{S_i^\perp\}\) on whose positive side lie exactly \(q\) of the vectors. \(Z_0=Z_N=1\{0\in\mathrm{int\,conv}(S)\}\).

### 5.1 Deterministic totals — **[KNOWN]** (Cover/Schläfli, Wendel; L21)

Under (GP\(_{\rm lin}\)), \(\ker S\) is in general position w.r.t. the coordinate hyperplanes (\(\dim\ker S\cap\{g_F=0\}=\dim\ker S_{F^c}=(N-d-|F|)^+\)). Hence
\(\sum_qZ_q=2\sum_{i=0}^{N-d-1}\binom{N-1}i\) and \(\sum_qY_q=2\sum_{i=0}^{d-1}\binom{N-1}i\) (number of regions). So the *total* number of conic Radon bipartitions, \(\sum_{q=1}^{N-1}Z_q=2\sum_{i<N-d}\binom{N-1}i-2\cdot1\{0\in\mathrm{int\,conv}S\}\), is deterministic up to the absorption indicator. **[PROVED]** (this consequence); its expectation follows from L3/L4.

For *independent* symmetric vectors (Wendel's setting), sign invariance makes every orthant equally likely, so \(\mathbb EZ_q=\binom Nq\,2^{1-N}\sum_{i<N-d}\binom{N-1}i\). **[PROVED]**, elementary. For walks this fails (table in §5.3).

### 5.2 Fixed and random bipartitions

* **Fixed bipartition: not universal.** **[FALSE]** as a universality claim. \(d=2\), \(N=4\), (±Ex): \(\mathbb P(\mathrm{pos}(S_{\{1\}})\cap\mathrm{pos}(S_{\{2,3,4\}})\neq\{0\})\) equals \(5/16\) for one increment list and \(31/96\) for another (exact orbit enumeration, `e2.py`). It depends on the increment law and on the temporal position of the indices. (At \(N=d+1\) it *is* universal: Theorem C′.)
* **Random bipartition with prescribed size \(q\): universal in expectation** — this is \(\mathbb EZ_q/\binom Nq\), see Theorem 5.3. **[PROVED-sketch]**, **[NU]**.
* **Uniform random bipartition (all \(2^N\) subsets):** \(\mathbb P=2^{-N}\mathbb E\sum_qZ_q\), universal by §5.1 and L3/L4. **[PROVED]** (consequence of known results).

### 5.3 Main new result: the expected level counts are distribution-free

**Theorem 5.3.** Let \(\mathcal K\) be the class of random configurations consisting of finitely many random *bridges* and finitely many random *walks* in \(\mathbb R^m\) (the vectors are all partial sums of all components, excluding the zero endpoints of bridges), whose joint increment law is invariant under the product of the symmetric groups (bridges) and hyperoctahedral groups (walks) acting within components, and which are in general linear position a.s. (any \(m\) of the vectors independent). Then for every \(q\), \(\mathbb EZ_q\) and \(\mathbb EY_q\) depend only on \(m\), \(q\), and the component lengths. In particular, for a single (±Ex) walk \(S_1..S_N\in\mathbb R^d\), \(\mathbb EZ_q=z(N,d,q)\) is distribution-free, and it is computed by the recursion below. Moreover, the statement is deterministic in orbit form: for every list \(x_1..x_N\) such that all walks \(\big(\sum_{j\le i}\varepsilon_jx_{\sigma(j)}\big)_i\) are in general position (plus the analogous condition for the walks with merged increments used in the recursion), \(\sum_{(\sigma,\varepsilon)\in B_N}Z_q(\text{walk}(\sigma,\varepsilon))=2^NN!\,z(N,d,q)\).

Status: **[PROVED-sketch]**; **[NU]** (not in L2–L7; the closest known statements are L6 Thm 1.2, which our result implies, see below, and the totals of §5.1).

**Proof.** *(i) Deterministic contraction–deletion identity.* For a configuration \(T\) of \(M\) vectors in GP in \(\mathbb R^m\), let \(T\setminus i\) be the deletion and \(T/i\) the contraction (project the others along \(T_i\) to \(\mathbb R^m/\mathbb RT_i\)). Then \(\ker(T\setminus i)=\ker T\cap\{g_i=0\}\) and \(\ker(T/i)\) is the coordinate projection of \(\ker T\) forgetting \(i\). A region of \(\ker T\setminus\bigcup_{j\ne i}\{g_j=0\}\) is either a region of \(\ker T\) or is cut by \(\{g_i=0\}\) into two; the cut ones are exactly the regions of \(\ker(T\setminus i)\). Counting with the number \(q\) of plus signs and summing over \(i\):
\[
(M-q)Z_q(T)+(q+1)Z_{q+1}(T)=\sum_{i=1}^M Z_q(T/i)+\sum_{i=1}^MZ_q(T\setminus i).\tag{5.1}
\]
(Verified on 200 random configurations, `e5.py`.) Read downwards in \(q\), (5.1) determines \(Z_{M-1},\dots,Z_0\) from \(Z_M\) and the two sums.
*(ii) The class \(\mathcal K\) is closed under the operations, in law.* Contracting at a point of a walk component splits it into a bridge (the part before the point, since \(S_i\equiv0\) in the quotient) and a walk (the part after); contracting at a point of a bridge splits it into two bridges. The product symmetry is inherited (the projection direction is invariant under the permutations within the new pieces). Deletion of a uniformly random point of a component of length \(\ell\) yields, by the block-reshuffling argument of L6 §3.1, a component of length \(\ell-1\) of the same type (merging two consecutive increments of an exchangeable sequence at a uniformly random place gives an exchangeable sequence; with signs, a sign-exchangeable one). Since (5.1) involves only the *sums* over \(i\), only the uniformly-random-deletion law matters.
*(iii) Boundary values.* \(\mathbb EZ_M=\mathbb P(0\in\mathrm{int\,conv}(T))\) is distribution-free on \(\mathcal K\) by the joint absorption theorem KVZ Adv. Math. (L5) Thm 2.1 (= L3 Thm 4.1).
*(iv) Base \(m=1\).* In \(\mathbb R^1\), \(Z_q=\binom Mq-1\{P=q\}-1\{P=M-q\}\) with \(P\) the number of positive points. Conditionally on the orbit, the positive counts of different components are independent; a bridge of length \(b\) has its count uniform on \(\{0..b-1\}\) (cycle lemma), a walk of length \(w\) has the Sparre Andersen arcsine law (L10 Thm 2.2, L9 Thm 2.2). Both are distribution-free.
*(v) Induction* on \((m,M)\) using (5.1), (ii)–(iv). The orbit form follows because each step is itself an orbit identity. ∎

**Exact checks (all agree).** The recursion (`experiments/rec.py`, `multi.py`) reproduces every brute-force orbit enumeration:

| \(d\) | \(N\) | \(\mathbb EZ_q\), \(q=0..N\) | \(\mathbb EY_q\) |
|---|---|---|---|
| 2 | 3 | 1/24, 23/24, 23/24, 1/24 (Theorem C) | 23/24, 49/24, 49/24, 23/24 |
| 2 | 4 | 1/12, 2, 23/6, 2, 1/12 | 11/12, 2, 13/6, 2, 11/12 |
| 2 | 5 | 77/640, 5867/1920, 7511/960, … | 563/640, 3733/1920, 2089/960, … |
| 2 | 6 | 293/1920, 3947/960, 24667/1920, 8533/480, … | 1627/1920, 1813/960, 4133/1920, 1067/480, … |
| 3 | 5 | 5/384, 385/384, 255/64, … | 379/384, 1535/384, 385/64, … |
| 3 | 6 | 253/11520, 9973/5760, 93619/11520, 35251/2880, … | |
| 4 | 6 | 1/640, 119/320, 1919/640, 841/160, … | |

(Rows are palindromic.) Brute force: \(d=2\), \(N=4,5,6\) and \(d=3\), \(N=5,6\), three increment lists each (\(N=6\): all \(2^66!=46080\) signed orderings per list). Integer normalisations \(Z^*_q=\mathbb EZ_q\cdot2^NN!/2\): e.g. \(d=2\): \(N=4\): 16, 384, 736, 384, 16; \(N=5\): 231, 5867, 15022, …; \(d=3\), \(N=5\): 25, 1925, 7650, …; at \(N=d+1\) they are the B-Eulerian numbers.
**Several independent symmetric walks** (new check this stage): \(d=2\), walk lengths \((2,2)\): \(\mathbb EZ=(1/4,2,7/2,2,1/4)\); \((2,1)\): \((1/8,7/8,7/8,1/8)\); \((3,2)\): \((21/64,611/192,719/96,\dots)\); \(d=3\), \((2,2,1)\): \((9/64,85/64,113/32,\dots)\) — each identical for three random increment lists and equal to the recursion's prediction.

**Interpretation.** For \(d=1\), \(\frac12\mathbb EY_q=\mathbb P(\#\{i:S_i>0\}=q)\), the Sparre Andersen arcsine law. So \(\mathbb EY_q\) is a \(d\)-dimensional analogue of the arcsine *distribution* (not just of its binomial moments): the expected number of regions of the hyperplane arrangement \(\{S_i^\perp\}\) having exactly \(q\) walk vectors on their positive side. KVZ (L6) obtained the binomial-moment analogue; we checked that their Thm 1.2 follows from our \(\mathbb EY_q(\cdot)\) via the Euler-characteristic relation \(M_{N,k}=\sum_{|H|\le d-1}(-1)^{|H|}\sum_q\binom qkY_q(S/H)\) (`chk_kvz.py`, all cases \(d\le4\), \(N\le7\) true). We do not know whether L6 conversely determines \(\mathbb EY_q\) for \(d\ge2\).

**What is not universal** (exact, **[FALSE]** as universality claims): the *distribution* of the vector \((Z_q)_q\) (\(d=2\), \(N=5\) and \(d=2,3\), \(N=6\): different lists give different laws, `out_e3_*`); \(\mathbb EZ_q\) under (Ex) alone (\(d=2\), \(N=4\): \(\mathbb EZ_N\in\{7/24,1/8,0\}\) for three lists).

**Generating-function form** **[PROVED]**: writing \(\sum_qZ_q(T)x^q=\sum_ka_k(T)(1+x)^{M-k}(1-x)^k\), identity (5.1) decouples into \(2(M-k)a_k(T)=\sum_ia_k(T/i)+\sum_ia_k(T\setminus i)\), and only even \(k\) occur (palindromy). A closed formula for \(z(N,d,q)\) is **open**.

### 5.4 Signed circuits

* **Subset-average principle** **[KNOWN-implicit]** (L6 §3.1): for a uniformly random \((d+1)\)-subset \(C\), \(S_C\) is again a (±Ex) walk, so \(\sum_{|C|=d+1}\mathbb P(\text{circuit on }C\text{ has labelled pattern }s)=\binom N{d+1}\cdot\mathbb P_{B}(s)\) with \(\mathbb P_B\) the Theorem C′ law. In particular, \(\mathbb E\#\{\text{positive circuits}\}=\binom N{d+1}/(2^d(d+1)!)\) — this is L6 Thm 1.2 with \(k=d+1\) (complement form). Checked: \(1/6\) (\(d=2,N=4\)), \(5/12\) (\(d=2,N=5\)).
* The expected number of circuits with \(\min(|C^+|,|C^-|)=k\) is \(\binom N{d+1}\eta B(d+1,k)/(2^{d+1}(d+1)!)\). **[PROVED]** (same principle + Theorem C), **[NU]** but immediate.
* Per-support laws (a fixed \(C\)) are **not universal** **[FALSE]** (`e4.py`), and the temporal sign pattern of a fixed circuit depends on index gaps (as in L3 Cor. 4.5).
* The number of circuits is deterministic (\(\binom N{d+1}\) under GP).

### 5.5 Absorption, positive spanning, refinements

\(\mathbb P(0\in\mathrm{conv}(S_1..S_N))\) and \(\mathbb P(\mathrm{pos}=\mathbb R^d)\) **[KNOWN]**: L4 Thm 2.3, L3 (1.4)–(1.5), L10 Thm 8.1. Refinements obtained here: by level (Theorem 5.3), by circuit sign type (§5.4). The kernel–orthant refinement "number of orthants met, by number of plus signs" is exactly \((Z_q)\).

### 5.6 Kernel geometry

\(\ker S\) with the coordinate hyperplanes: chamber count deterministic (§5.1) **[KNOWN]**; chamber counts by level have universal expectations (Theorem 5.3) **[PROVED-sketch]**; the full oriented matroid is not universal (\(N=d+3\) counterexample of `Counterexamples.lean`; Z-distribution above). Conic intrinsic volumes / Grassmann angles of the chambers of \(\ker S\) are metric quantities and depend on the law (even for Gaussian walks they are explicit only in special cases); we found no distribution-free statement for them. **[HEUR]**: only combinatorial (counting) functionals averaged over a group orbit can be universal by these methods.

---

## 6. Ordinary affine Tverberg partitions of walk points

### 6.1 The affine Radon case \(r=2\), general \(N\)

**Theorem 6.1.** Let \(S_0=0,S_1..S_n\in\mathbb R^d\) have (Ex) increments and be in general affine position a.s. (homogenised vectors \((S_i,1)\) in GP\(_{\rm lin}\) in \(\mathbb R^{d+1}\)). Then the expected number of Radon bipartitions \(\{S_i\}=A\sqcup B\) with \(|A|=q\) (\(\mathrm{conv}A\cap\mathrm{conv}B\neq\emptyset\)), equivalently the expected number of \(q\)-sets (subsets cut off by a hyperplane) of \(\{S_0..S_n\}\), is distribution-free. **[PROVED-sketch]**, **[NU]**.
*Proof idea.* Homogenise; a contraction at a point \((S_i,1)\) yields a vector bridge configuration (A-type) after a cyclic shift: a uniformly random cyclic shift of \((X_1..X_n,-S_n)\) is an exchangeable bridge whose point set is a translate of \(\{S_0..S_n\}\); then (5.1) with A-type components only, and the base/boundary values from L4 Thm 2.1 and the cycle lemma. No sign symmetry is needed.
Exact checks (`recaff.py` vs brute force): \(d=2\): 5 points \((0,5/6,25/6,25/6,5/6,0)\); 6 points \((0,43/30,124/15,63/5,\dots)\); \(d=3\): 6 points \((0,1/4,3,11/2,\dots)\); 7 points \((0,22/45,377/60,2741/180,\dots)\). \(q=1\): \(n+1-\mathbb Ef_0\), consistent with L5 Thm 1.2. The *distribution* is not universal **[FALSE]** (orbit enumeration; and `fivePoints_not_universal` in `Counterexamples.lean`). For **several** walks the affine statement fails already at \(N=d+2\) (`twoWalks_not_universal`: \(4/24\) vs \(16/24\)) **[FALSE]**.

### 6.2 \(r=3\), the critical number \(N=(r-1)(d+1)+1\)

At \(N=T(d,r)=(r-1)(d+1)+1\) a Tverberg partition exists for every point set (Tverberg) **[KNOWN]**. General position does **not** imply uniqueness of the partition; Sierksma's conjecture says there are at least \(((r-1)!)^d\) Tverberg partitions; for \(d=2,r=3\) (7 points) this lower bound 4 is a theorem (Hell; Soberón L17) **[KNOWN]**.

Exact enumeration, \(d=2\), \(r=3\), 7 points \(S_0..S_6\) of an (Ex) walk (all \(720\) orderings, all 301 three-block partitions, LP feasibility per partition — numerical LP):

| increment list | distribution of #Tverberg partitions | \(\mathbb E\#\) | \(\mathbb E\#\) profile (1,3,3) | profile (2,2,3) |
|---|---|---|---|---|
| \((-4,11),(-5,6),(-9,-2),(-12,-12),(-12,8),(5,-12)\) | 4:478, 5:216, 6:22, 7:4 | 197/45 | 53/60 | 629/180 |
| \((-11,6),(9,-7),(1,8),(0,11),(4,-1),(5,2)\) | 4:466, 5:204, 6:46, 7:4 | 797/180 | 31/36 | 107/30 |
| \((36,-1),(13,3),(35,4),(31,2),(10,-1),(10,4)\) (drifted) | 4:484, 5:206, 6:28, 7:2 | 787/180 | 157/180 | 7/2 |

Conclusions: minimum always 4 (consistent with Sierksma/Hell); **the expected number of Tverberg 3-partitions is not universal under (Ex)** **[FALSE]** as a universality claim (\(788/180\ne797/180\ne787/180\)); only profiles \((1,3,3)\) and \((2,2,3)\) occur (a block of size 1 must be a point in both other hulls; profile \((1,2,4)\) would need a segment through a point, excluded by GP). Labelled partition probabilities differ across lists. Whether (±Ex) restores a universal expectation for \(r=3\) was **not tested** (the orbit is 64 times larger) — open.

### 6.3 Structural facts (labels per item)

* Uniqueness of the common point for a fixed Tverberg partition at \(N=T(d,r)\): if every block has at most \(d+1\) points, the expected dimension of \(\bigcap_a\mathrm{aff}(S_{I_a})\) is \(\sum_a(|I_a|-1)-(r-1)d=N-r-(r-1)d=0\), so for *generic* points (e.g. a.s. for walks with absolutely continuous joint increment law) the affine hulls meet in exactly one point and the Tverberg point of that partition is unique **[PROVED]** (dimension count). As in the conic case (§7.3), the weak general-position assumption "no \(d+1\) points on a hyperplane" does not by itself force the affine hulls to meet generically **[HEUR]**, by analogy with the explicit conic counterexample; we did not construct an affine one. Uniqueness of coefficients for a fixed partition holds iff each block is affinely independent, which GP gives only if each block has \(\le d+1\) points.
* Temporal structure: Bukh–Loh–Nivasch (L16) classify Tverberg *types* (order patterns) unavoidable in long sequences; walks are ordered sequences, so their deterministic results apply to walk points as to any ordered point sequence in general position. **[KNOWN]** (we did not derive walk-specific probabilities of Tverberg types).
* **Sarkaria lift** (affine): \((S_i,1)\otimes u_a\in\mathbb R^{(d+1)(r-1)}\), \(u_1..u_r\) centred simplex. A partition is Tverberg iff \(0\in\mathrm{conv}\{(S_i,1)\otimes u_{a(i)}\}\) (Sarkaria; L18). The lifted family is a "walk" only within colour classes: the increments of the lifted points within a colour class are \((X_j,0)\otimes u_a\) after inserting the other colours' indices, so exchangeability survives only for *colour-preserving* permutations, and the Gale dual has dimension \(N-(d+1)(r-1)\) (= 1 exactly at \(N=T(d,r)\)!). At \(N=T(d,r)\) the lifted configuration for a fixed colouring has a 1-dim dependence space, and the Barysheva mechanism would apply **if** the symmetry group acting on the lift were large enough to make the dual sequence's order pattern uniform. It is not: permutations mixing colour classes change the lifted configuration, not just its order. This is why no Eulerian-type universal law appears (consistent with the non-universality found above). **[HEUR]** explanation; the non-universality itself is **[FALSE]**-certified by the table.
* An \(r>2\) Eulerian analogue (coloured permutations, wreath products \(\mathbb Z_r\wr S_n\), multiset descents): searched in L15, L18 and the walk papers L2–L6, nothing found. The non-universality in the table above makes any universal formula for \(\mathbb E\#\) (hence for the law) impossible under (Ex). **[FALSE]** as "a universal \(r=3\) law exists under (Ex)"; under (±Ex) **open**.

---

## 7. Multi-part conic Tverberg partitions

Call \([N]=I_1\sqcup\dots\sqcup I_r\) (all \(I_a\ne\emptyset\)) a **conic Tverberg partition** if \(\bigcap_a\mathrm{pos}(S_{I_a})\ne\{0\}\).

### 7.1 Tensor formulation — **[PROVED]** (standard Sarkaria argument, written out)

Let \(u_1..u_r\in\mathbb R^{r-1}\) with \(\sum u_a=0\) and any \(r-1\) of them independent. For \(y_1..y_r\in\mathbb R^d\): \(\sum_ay_a\otimes u_a=0\iff y_1=\dots=y_r\) (the only linear relation among the \(u_a\) is \(\sum u_a=0\)). Hence, with \(y_a=\sum_{i\in I_a}\lambda_iS_i\):
\[
\sum_i\lambda_i\,S_i\otimes u_{a(i)}=0,\ \lambda\ge0\iff y_1=\dots=y_r=:y,\ y\in\bigcap_a\mathrm{pos}(S_{I_a}).
\]
So conic Tverberg ⇔ the lifted vectors \(S_i\otimes u_{a(i)}\in\mathbb R^{d(r-1)}\) have a nonnegative dependence **with \(y\ne0\)**. A nonnegative dependence with \(y=0\) exists iff some block has \(0\in\mathrm{conv}(S_{I_a})\) — under GP\(_{\rm lin}\) this needs \(|I_a|\ge d+1\). Thus: if all \(|I_a|\le d\), then "nonnegative nonzero lifted dependence" ⇔ "conic Tverberg", and \(y\ne0\) forces every block to be used nontrivially.

### 7.2 Dimension count — **[PROVED]**

Unknowns \((\lambda,y)\in\mathbb R^N\times\mathbb R^d\), equations \(rd\). Generic solution space dimension \(N+d-rd\); a unique ray requires \(N=(r-1)d+1=:N_{\rm conic}\), equivalently \(N\) vectors in \(\mathbb R^{d(r-1)}\) with a 1-dimensional dependence space. ✓ Precisely, if every block is in GP within \(\mathbb R^d\):
\[
\dim\{(\lambda,y)\}=\dim W+\sum_a(|I_a|-d)^+,\qquad W=\bigcap_a\mathrm{span}(S_{I_a}).
\]

### 7.3 Uniqueness at \(N=N_{\rm conic}\)

* **GP\(_{\rm lin}\) does not give a unique coefficient ray.** **[FALSE]** with counterexample: \(d=4\), \(r=3\), \(N=9\), blocks of size 3 spanning three hyperplanes \(H_1,H_2,H_3\) that share a common 2-plane. Every 4 of the 9 vectors can still be independent (numerical check: min \(|\det|\) over all 4-subsets \(\approx1.2\cdot10^{-3}\ne0\)), but \(\dim W=2\) and the solution space has dimension 2 (generic configuration: 1). (`w_check.py`.)
* If \(\dim W=1\) and all \(|I_a|\le d\), the coefficient ray is unique, and the common ray is unique (if \(y\) and \(-y\) were both in a block cone, that block would have a positive dependence among \(\le d\) independent vectors). **[PROVED]**
* If some \(|I_a|>d\), coefficients are never unique (extra \(\sum(|I_a|-d)^+\) dimensions), although the common ray may be.
* Uniqueness of coefficients for a fixed partition says nothing about uniqueness of the partition: \(d=2\), \(r=3\), \(N=5\) walk configurations have 0, 1, or several conic Tverberg 3-partitions (below).

### 7.4 Deterministic conic Tverberg number — **[PROVED]**, novelty **[NU]** (possibly in Roudneff 2001, L19)

**Theorem 7.4.** (a) Any \(N\ge(r-1)(d+1)+1\) vectors in \(\mathbb R^d\) in general linear position admit a conic Tverberg \(r\)-partition. (b) For all \(d,r\ge2\) there are \((r-1)(d+1)\) vectors in GP\(_{\rm lin}\) with none. Hence the deterministic threshold is \(N_{\rm aff}=(r-1)(d+1)+1\), **not** \(N_{\rm conic}=(r-1)d+1\).

*Proof.* (a) By affine Tverberg there are a partition and \(p\in\bigcap_a\mathrm{conv}(S_{I_a})\subseteq\bigcap_a\mathrm{pos}(S_{I_a})\). If \(p\ne0\) we are done. If \(p=0\), each block has \(0\in\mathrm{conv}(S_{I_a})\), which under GP\(_{\rm lin}\) needs \(|I_a|\ge d+1\); so \(N\ge r(d+1)>(r-1)(d+1)+1\) — contradiction for \(N=(r-1)(d+1)+1\); for larger \(N\) apply this to the first \((r-1)(d+1)+1\) vectors and add the rest to any block.
(b) Let \(v_0..v_d\) be the vertices of a centred simplex (\(\sum v_k=0\), any \(d\) independent). Take \(r-1\) copies of each \(v_k\) and perturb slightly to reach GP\(_{\rm lin}\). Suppose conic Tverberg partitions with unit common vectors \(y_\varepsilon\) existed for perturbations \(\varepsilon\to0\). Pass to a subsequence with a fixed partition (blocks \(I_a\) with label multisets \(D_a\subseteq\{0..d\}\)) and \(y_\varepsilon\to y\), \(|y|=1\). If \(D_a\ne\{0..d\}\), the vectors \(v_{D_a}\) are linearly independent, so the coefficients stay bounded and \(y\in\mathrm{pos}(v_{D_a})\); if \(D_a=\{0..d\}\), \(y\in\mathrm{pos}(v_{D_a})=\mathbb R^d\) trivially. Write \(y=\sum_kc_kv_k\) with \(c\ge0\) and minimal support \(J\) (all nonnegative representations are \(c+t\mathbf 1\), \(t\ge0\)); \(\emptyset\ne J\ne\{0..d\}\). For \(D_a\neq\{0..d\}\), \(y\in\mathrm{pos}(v_{D_a})\) iff \(J\subseteq D_a\); also \(J\subseteq D_a\) trivially if \(D_a=\{0..d\}\). So every label in \(J\) occurs in all \(r\) blocks — but each label has only \(r-1\) copies. Contradiction. ∎
Numerical confirmation \(d=2,r=3\): six perturbed copies (two near each of three directions at \(120°\)) have no conic Tverberg 3-partition (LP over all 90 partitions, 6 random perturbations; `conic_lb.py`). Also, 15 of 200 Gaussian 6-tuples in \(\mathbb R^2\) have none.
At \(N_{\rm conic}\) deterministic existence fails: \(r=2\): \(d+1\) positively spanning vectors have only trivial intersections; \(d=2,r=3\): a regular pentagon of directions has no conic 3-partition. **[PROVED]** for \(r=2\); the pentagon by numerical LP over all 25 three-block partitions (`pent.py`).

### 7.5 Random walks at \(N_{\rm conic}\) — not universal

\(d=2,r=3,N=5\), (±Ex), exact orbit enumeration with exact cross-product tests: \(\mathbb P(\exists\text{ conic 3-partition})=19/20,\ 913/960,\ 911/960\); \(\mathbb E\#=1171/640,\ 703/384,\ 3511/1920\) for three lists. **[FALSE]** as universality claims. Only profile \((1,2,2)\) occurs (a block of size 3 forces two singleton blocks to share a ray). For \(r=2\), \(N=d+1\) this is Theorem C′ (universal) — so universality at the conic critical size is special to \(r=2\).

---

## 8. Methods: what each computes and whether it transfers

| method (source) | computes | symmetry needed | walk points? | combines with Gale duality? | new statement it gave / could give | obstruction |
|---|---|---|---|---|---|---|
| 1-dim Gale dual + Abel summation + group averaging (L1; §4) | full labelled law of the unique dependence | (Ex) for affine/rotation classes, (±Ex) for conic/labelled | yes | it *is* Gale duality | Theorem C′ (explicit descent form) | needs \(\dim\ker=1\): \(N=d+1\) (conic), \(d+2\) (affine), or the Sarkaria lift at \(N=T(d,r)\) — but there the group is too small (§6.3) |
| Weyl chambers met by a generic subspace; Zaslavsky/characteristic polynomial (L4, L10 §8–9) | absorption probabilities, \(\mathbb Ef_k\) | (Ex)/(±Ex) | yes | yes: \(\ker X\) is the subspace; orthants of \(g\) ↔ descent-class cones of \(G\) | boundary values in Thm 5.3 | counts single chambers; descent classes are unions of chambers, not deterministic individually |
| expected \(f\)-vectors + triangular inversion (L2 Thm 4.1) | type probabilities when the type is determined by face numbers | as for \(f\)-vectors | yes | — | reproves Theorem C | only works when types ↔ \(f\)-vectors bijectively (\(d+2\) vectors) |
| face probabilities + Möbius inversion (L3 Cor. 4.5; §2.3) | labelled laws | (±Ex) | yes | yes | labelled Theorem C′ implicit | for \(N>d+1\) faces no longer determine the oriented matroid; full OM not universal |
| block reshuffling / subset averaging (L6 §3.1) | sums over subsets of universal per-subset quantities | (Ex)/(±Ex) | yes | yes | circuit counts (§5.4); deletion step of Thm 5.3 | gives only sums over subsets, never per-subset laws |
| contraction–deletion + induction over a closed class (new here) | expected counts of regions by level | product A/B symmetry | yes (bridges+walks) | yes: contraction = Gale-dual projection | Theorem 5.3, Theorem 6.1 | needs boundary values (absorption) and a 1-d base; gives expectations only |
| cycle lemma / cyclic shifts (L1, L5 Thm 1.14; L10 Lemma 2.5) | rotation-invariant statistics; bridge ↔ walk | (Ex) | yes | yes | affine Thm 6.1 (cyclic shift to a bridge) | breaks for several walks (different translations) |
| permutation–cycle identities (L9 Thms 2.13, 2.16, 2.17, 2.24; L8) | \(\sum_\sigma1[y\in C_\sigma]=\sum_\sigma1[y\in D_\sigma]\): replaces dependent partial sums by independent cycle sums | none (deterministic) | yes | partially: absorption = point-in-cone; our \(Z_q\) is not a point-in-cone event | possible direct proof of Thm 5.3 if \(Z_q\) can be written as \(\sum\) of indicator functions of convex sets in \(\mathbb R^N\) (layered-cake Thm 2.17) | the level sets \(\{g:\#\{g_i>0\}=q\}\cap\ker\) are not convex |
| Wendel sign counting (L9 Thm 2.25; L8 Lemma 6.1) | orthants met by a generic subspace | independence + symmetry | **no** (needs independent coordinates' signs) | yes | §5.1 totals | for walks only orbit sums over \(B_N\), not over \(\{\pm\}^N\), are available |
| wall-crossing (L7) | invariance of signed-permutation counts under deformation | deterministic | yes | yes | alternative proof of orbit-form Thm 5.3: show \(\sum_{w}Z_q(w\cdot x)\) is constant across walls | requires analysing all wall types (ties \(G_i=\pm G_j\), \(G_i=0\), and higher-dimensional degeneracies of \(\ker\)) |
| conic intrinsic volumes, Crofton, polarity (L4, L2 §4, L11) | angle sums, \(\mathbb P(L\cap C\neq\{0\})\) for *uniform* \(L\) | rotation invariance of \(L\) (Gaussian/i.i.d.) | only for Gaussian walks via explicit angles | weakly | Gaussian-specific formulas (not pursued) | walk subspaces \(\ker X\) are not Haar-distributed; metric quantities are not universal |
| Sarkaria tensor lift (L18; §6.3, §7.1) | Tverberg ⇔ positive dependence in a lifted space | — | lift destroys walk structure across colours | yes at \(N=T(d,r)\) (1-dim dual) | Theorem 7.4 tensor form; dimension counts | colour-mixing permutations are not symmetries of the lift |
| Spitzer/Baxter, Wiener–Hopf (L10 §3–6) | 1-d fluctuation laws | i.i.d. (or exchangeable via combinatorial lemma) | yes | only through the \(m=1\) base case | base case of Thm 5.3 | genuinely one-dimensional |

---

## 9. Candidate theorems

### Candidate 1 — level counts of a sign-exchangeable walk (Theorem 5.3)
* **Hypotheses/conclusion:** as in §5.3; \(\mathbb EZ_q\), \(\mathbb EY_q\) distribution-free on \(\mathcal K\); orbit-sum version deterministic.
* **Literature check:** L2–L7 read in full for statements about \(k\)-sets, levels of arrangements, conic Radon partitions of walks, arcsine laws; arXiv searches "k-sets" ∧ "random walk", "arrangement" ∧ "level" ∧ "random walk", "multidimensional arcsine"; forward citations of L6 (OpenAlex). Nothing equivalent found. L6 Thm 1.2 is weaker (implied).
* **Novelty:** **[NU]**.
* **Method:** §5.3. **Completed:** identity (5.1) (proved, tested); closure of \(\mathcal K\); base case; boundary values (known); induction; exact checks (14 cases incl. several walks).
* **Missing lemma:** a fully written measure-theoretic version of the reshuffling step for mixed classes (routine); and a closed formula.
* **Obstructions:** none known for the expectation; the distribution is provably not universal.
* **Tests:** \(d=2,N=7\); \(d=3,N=7\) brute force (\(2^77!\approx6.5\cdot10^5\) orderings); several bridges + walks in \(d=3\).

### Candidate 2 — closed formula for \(z(N,d,q)\)
* **Statement (conjectural shape):** \(\sum_qz(N,d,q)x^q\) is an explicit combination of \((1+x)^{N-2j}(1-x)^{2j}\) with B-Stirling-type coefficients, specialising to \(\sum_kB(n,k)x^k\cdot2/(2^nn!)\) (folded) at \(N=d+1\) and to the arcsine generating function at \(d=1\).
* **Literature check:** not found in L2–L7. The integer tables \(Z^*\) (e.g. 16, 384, 736; 231, 5867, 15022; 25, 1925, 7650) could not be looked up in OEIS from this environment — this should be done first. **[NU]**; that a product-type formula exists is **[CONJ]** (weakly supported only by the decoupling of §5.3).
* **Method:** solve the decoupled recursion \(2(M-k)a_k=\sum a_k(T/i)+\sum a_k(T\setminus i)\) on \(\mathcal K\) with generating functions in the component lengths (exponential generating functions per component, as in Spitzer-type formulas).
* **Missing step:** guessing the per-component generating function; **tests:** the tables in `experiments/cf.py` output (\(d\le4\), \(N\le8\)).

### Candidate 3 — affine level counts (Theorem 6.1), and its \(k\)-set reading
* Expected number of \(q\)-sets of \(\{S_0..S_n\}\) for (Ex) walks is distribution-free. **Literature:** \(q=1\) is \(\mathbb Ef_0\) (L5 Thm 1.2); no general-\(q\) statement found. **[PROVED-sketch]**, **[NU]**. **Obstruction:** fails for several walks (§6.1). **Tests:** \(d=2\), 7–8 points.

### Candidate 4 — deterministic conic Tverberg number \((r-1)(d+1)+1\) (Theorem 7.4)
* **Literature:** Roudneff 2001 (L19) title "the conic Tverberg's theorem" strongly suggests a closely related or identical statement (possibly in oriented-matroid generality); full text not accessible. **[PROVED]**, **[NU]** (likely known).
* **Tests:** done for \(d=2,r=3\) numerically.

### Candidate 5 — labelled law of Theorem C in descent form
* **[PROVED]**; implicit in L3 Cor. 4.5 (**[KNOWN-implicit]**); explicit form **[NU]**.

### Candidate 6 — (±Ex) universality of \(\mathbb E\#\)Tverberg partitions for \(r=3\)
* Under (Ex) it is false (§6.2). Under (±Ex) there is no evidence either way, so it is **open** (not even conjectured). **Literature:** De Loera–Hogan (L12) treat i.i.d. points only. **Test:** \(d=2\), 7 points, full signed orbit (\(46080\) orderings × 301 LPs).

### Candidate 7 — circuit-type counts
* \(\mathbb E\#\{\text{circuits with }\min(|C^\pm|)=k\}=\binom N{d+1}\eta B(d+1,k)/(2^{d+1}(d+1)!)\). **[PROVED]**, immediate from known results; **[NU]** as a stated formula.

---

## 10. Counterexamples (all exact unless marked numerical)

1. Fixed conic bipartition probability not universal: \(d=2\), \(N=4\), \(I=\{1\}\): \(5/16\) vs \(31/96\).
2. Distribution of \((Z_q)\) not universal (\(d=2\), \(N=5,6\); \(d=3\), \(N=5,6\)).
3. \(\mathbb EZ_q\) not universal under (Ex) only (\(d=2,N=4\): \(\mathbb EZ_4\in\{7/24,1/8,0\}\)).
4. Per-support circuit laws not universal (\(d=2\), \(N=4,5\)).
5. Theorem C without sign symmetry: \(d=1\), positive increments.
6. Affine several-walk Radon law not universal (Lean, `twoWalks_not_universal`); full affine type at \(N=d+3\) not universal (Lean, `fivePoints_not_universal`).
7. Affine Tverberg \(r=3\), \(d=2\), 7 points: \(\mathbb E\#\) partitions \(197/45\), \(797/180\), \(787/180\) under (Ex) (numerical LP per partition, exact counting).
8. Conic Tverberg \(r=3\), \(d=2\), \(N=5\), (±Ex): existence probability \(19/20\), \(913/960\), \(911/960\).
9. GP\(_{\rm lin}\) does not give a unique coefficient ray at \(N_{\rm conic}\) (\(d=4,r=3\), numerical rank).
10. No deterministic conic Tverberg theorem at \(N_{\rm conic}\) (positively spanning simplex; pentagon), nor at \((r-1)(d+1)\) (Theorem 7.4(b)).
11. Stationary ergodic non-exchangeable increments break Theorem 1.4 (earlier report, prose).

---

## 11. Ranking of directions and plans

1. **Closed form and full proof write-up of Theorem 5.3 (level counts / \(d\)-dimensional arcsine law).** Plan: (a) write the reshuffling lemma for the class \(\mathcal K\) in full; (b) solve the decoupled recursion with exponential generating functions in the component lengths, using the known absorption generating functions (L4/L5) as boundary data; (c) compare with L6 to see whether Thm 1.2 there is equivalent for \(d\ge2\); (d) asymptotics \(N\to\infty\) (a \(d\)-dimensional arcsine density for the normalised level). Tests: \(d=2,3\), \(N\le8\) tables (already available).
2. **A direct (bijective or wall-crossing) proof of the orbit identity \(\sum_{w\in B_N}Z_q(w\cdot x)=\mathrm{const}\).** Plan: use the Kabluchko–Tarasov wall-crossing method (L7) or the layered-cake identity (L9 Thm 2.17) on descent-class cones \(\{G:\mathrm{Des}(G,0)=D\}\), which are convex; show that wall crossings change the per-\(D\) counts only by transfers between classes with the same \(|D|\). This would also explain *which* refinements are universal (it predicts: any statistic constant on \(\{D:|D|=q\}\)-sums).
3. **Sign-symmetric affine/conic Tverberg for \(r=3\).** Plan: run the \((\pm\)Ex) orbit test for \(d=2\), 7 points (affine) and \(d=2\), 5 vectors (conic: already non-universal, so focus on the affine case), and examine whether averaging additionally over random colourings (Candidate "random partition with prescribed sizes") restores universality — the natural analogue of the subset-average principle. If it does, attack it via the Sarkaria lift at \(N=T(d,r)\) (1-dim dual) with averaging over colour-preserving signed permutations.

---

## 12. Files

* `experiments/` — scripts used for the exact computations: `core.py` (exact determinants, orbits, topes), `e1.py`, `e1b.py` (labelled conic law), `e2.py` (fixed bipartitions), `e3.py` (distribution and expectation of \(Z\)), `e4.py` (circuits), `e5.py` (identity (5.1)), `rec.py`, `multi.py`, `recaff.py` (recursions), `chk_kvz.py` (comparison with KVZ Bernoulli Thm 1.2), `cf.py` (integer tables), `tv.py`, `tv_run.py`, `tv_exact2.py` (Tverberg enumerations), `conic_lb.py`, `w_check.py` (§7), and the output files `out_*.txt`.
* Earlier stage: `GENERALIZATIONS.md`, `RequestProject/*.lean` (unchanged).
