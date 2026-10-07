# Expected level counts of random walks: theorems and complete proofs

This is the publication-style theorem–proof document of the present stage. It supersedes the
sketches of `REPORT.md` §5–§7 wherever they differ; every difference is listed in `VALIDATION.md`.
Literature comparisons are in `LITERATURE.md`, the Lean formalization is described in
`FORMALIZATION.md`, and the exact computations are in `certificates/` (see `certificates/README.md`).

Labels: **[KNOWN]** (with reference), **[KNOWN-implicit]**, **[PROVED]** (complete proof below),
**[PROVED, NU]** (complete proof; novelty unresolved), **[COND]** (proved modulo a cited published theorem,
named explicitly), **[LEAN]** (kernel-checked, see `FORMALIZATION.md`), **[OBS]** (observed in exact
computations, not proved), **[FALSE]**.

---

## 0. Conventions

* \(V\) is a real vector space of dimension \(m\ge 0\). A **configuration** is a finite family
  \(T=(T_1,\dots,T_M)\) of vectors of \(V\), indexed by \([M]=\{1,\dots,M\}\); repetitions are allowed.
* \(L(T)=\ker T=\{g\in\mathbb R^M:\ \sum_i g_iT_i=0\}\), the space of linear dependences.
* A **sign vector** is \(s\in\{+,-\}^M\); \(s^+=\{i:s_i=+\}\). Its **open orthant** is
  \(O_s=\{g\in\mathbb R^M: g_i>0\ (i\in s^+),\ g_i<0\ (i\notin s^+)\}\). For \(I\subseteq[M]\) write \(O_I\) for
  \(O_s\) with \(s^+=I\). For \(M=0\), \(\mathbb R^0=\{()\}\), there is exactly one sign vector and \(O=\{()\}\).
* \(s\) is a **tope** of \(T\) if \(L(T)\cap O_s\neq\varnothing\).
* **Level counts:** for \(0\le q\le M\),
  \[
  Z_q(T)=\#\{I\subseteq[M]:\ |I|=q,\ L(T)\cap O_I\neq\varnothing\},\qquad Y_q(T)=\binom Mq-Z_q(T),
  \]
  and \(Z_q=0\) for \(q<0\) or \(q>M\). The subsets \(I\) are *labelled* and *ordered*: \(I\) and its complement
  are counted separately (once in \(Z_q\), once in \(Z_{M-q}\)).
* **Pointwise palindromy.** \(L(T)=-L(T)\) and \(-O_I=O_{I^c}\), so \(Z_q(T)=Z_{M-q}(T)\) for every \(T\).
  Hence the number of *unordered* bipartitions \(\{I,I^c\}\) with \(\{|I|,|I^c|\}=\{q,M-q\}\) and
  \(L\cap O_I\ne\varnothing\) equals \(Z_q\) if \(2q\ne M\) and \(Z_q/2\) if \(2q=M\).
* \(\mathrm{pos}(A)\) is the set of nonnegative combinations of \(A\) (\(\mathrm{pos}(\varnothing)=\{0\}\));
  \(\mathrm{conv}(\varnothing)=\varnothing\).
* **(GP)** \(T\) is in *general linear position* in \(V\) if every subfamily of at most \(m\) of the vectors is
  linearly independent (for \(M\ge m\): any \(m\) of them form a basis). Repeated vectors are excluded when \(m\ge2\).
* **Deletion and contraction.** \(T\setminus i=(T_j)_{j\ne i}\) in \(V\);
  \(T/i=(\bar T_j)_{j\ne i}\) in \(V/\mathbb RT_i\), where the bar is the quotient map. (If \(T_i=0\), \(T/i\)
  is just the image in \(V\).) Both are indexed by \([M]\setminus\{i\}\cong[M-1]\).
* \(i\) is a **coloop** of \(T\) if \(T_i\notin\mathrm{span}(T_j:j\ne i)\); equivalently \(g_i=0\) for every \(g\in L(T)\).
* **Symmetry hypotheses for a random sequence \(X=(X_1,\dots,X_N)\in V^N\).**
  (Ex) the law is invariant under \(X\mapsto(X_{\sigma(1)},\dots,X_{\sigma(N)})\), \(\sigma\in\mathfrak S_N\);
  (±Ex) the law is invariant under the hyperoctahedral group \(B_N\), \((\sigma,\varepsilon)\cdot X=(\varepsilon_1X_{\sigma(1)},\dots,\varepsilon_NX_{\sigma(N)})\).
  The walk is \(S_i=X_1+\dots+X_i\). Measurability: \(X\) is a random element of \(V^N\) with its Borel
  \(\sigma\)-algebra; all statistics below are bounded Borel functions on the relevant event (Remark 4.3).

---

## 1. Deterministic geometry

**Lemma 1.1 (Stiemke's alternative) [KNOWN; LEAN].** For \(v_1,\dots,v_M\in V\) exactly one of the
following holds: (i) there is \(y\in\mathbb R^M\) with all \(y_i>0\) and \(\sum y_iv_i=0\); (ii) there is a linear
functional \(u\) on \(V\) with \(u(v_i)\ge0\) for all \(i\) and \(u(v_j)>0\) for some \(j\).

*Proof.* Both cannot hold: \(0=u(\sum y_iv_i)=\sum y_iu(v_i)>0\). Suppose (i) fails. Then the subspace
\(L=\ker(y\mapsto\sum y_iv_i)\) and the open convex cone \(P=(0,\infty)^M\) are disjoint. By the Hahn–Banach
separation theorem there are a linear \(\varphi\) on \(\mathbb R^M\) and \(c\in\mathbb R\) with \(\varphi<c\) on \(P\) and
\(\varphi\ge c\) on \(L\). Since \(L\) is a subspace, \(\varphi|_L=0\) and \(c\le0\); since \(P\) is a cone, \(\varphi\le0\) on \(P\), so
\(\varphi=-\sum c_ie_i^*\) with \(c_i\ge0\), and \(\varphi\ne0\) because \(\varphi<c\le0\) on \(P\). A functional vanishing on the
kernel of the linear map \(A:y\mapsto\sum y_iv_i\) factors through \(A\): \(\varphi=-u\circ A\) for a linear \(u\) on \(V\)
(define it on \(\mathrm{im}A\) and extend). Then \(u(v_i)=-\varphi(e_i)=c_i\ge0\), not all zero. ∎

**Lemma 1.2 (strictification) [PROVED; LEAN].** Let \(T\) satisfy (GP) and let \(\varepsilon\in\{\pm1\}^M\). If a
functional \(u\) satisfies \(\varepsilon_iu(T_i)\ge0\) for all \(i\), and \(u\ne0\), then there is \(u'\) with
\(\varepsilon_iu'(T_i)>0\) for all \(i\).

*Proof.* Let \(Z=\{i:u(T_i)=0\}\). The vectors \((T_i)_{i\in Z}\) lie in the hyperplane \(\ker u\) of dimension
\(m-1\); if \(|Z|\ge m\), any \(m\) of them would be independent by (GP), impossible. So \(|Z|\le m-1\) and
\((T_i)_{i\in Z}\) is independent; choose \(w\) with \(w(\varepsilon_iT_i)=1\) for \(i\in Z\). For \(t>0\) smaller than
\(\min_{i\notin Z}\varepsilon_iu(T_i)/|w(T_i)|\) (over \(i\) with \(w(T_i)\neq 0\)), \(u'=u+tw\) works. ∎

*Where (GP) enters.* Only to bound \(|Z|\le m-1\) and make \((T_i)_{i\in Z}\) independent.

**Theorem 1.3 (separation form) [PROVED; LEAN].** Let \(T\) satisfy (GP) and \(M\ge1\). For every
\(I\subseteq[M]\):
\[
L(T)\cap O_I\neq\varnothing\iff\text{there is no functional }u\text{ with }u(T_i)>0\ (i\in I),\ u(T_j)<0\ (j\notin I).
\]
Hence \(Y_q(T)\) is the number of \(q\)-sets \(I\) that are *strictly separated* from their complement by a
linear hyperplane, i.e. the number of regions of the central arrangement \(\{T_i^\perp\}\) in \(V^*\) having exactly
\(q\) of the vectors on their positive side.

*Proof.* Put \(v_i=\varepsilon_iT_i\) with \(\varepsilon_i=+1\) on \(I\), \(-1\) off \(I\); \(L\cap O_I\ne\varnothing\) is (i) of Lemma
1.1 for the \(v_i\). (⇒) A strict separator would be (ii) (here \(M\ge1\) is used). (⇐) If (i) fails, (ii) gives
\(u\ne0\) with \(u(v_i)\ge0\), and Lemma 1.2 makes it strict. ∎

Without (GP) the implication (⇐) fails: `certificates/out_counterexamples.txt`, CE7.

**Theorem 1.4 (cone–orthant equivalence) [PROVED; LEAN].** Let \(T\) satisfy (GP), \(m\ge1\), and
\(\varnothing\ne I\subsetneq[M]\). Then
\[
\mathrm{pos}(T_I)\cap\mathrm{pos}(T_{I^c})\neq\{0\}\iff L(T)\cap O_I\neq\varnothing .
\]

*Proof.* (⇒) Let \(0\ne y=\sum_{I}a_iT_i=\sum_{I^c}b_jT_j\) with \(a,b\ge0\). The dependence \(g=(a,-b)\) has
the right signs only weakly (coordinates may vanish). Suppose \(L\cap O_I=\varnothing\). By Theorem 1.3 there is
\(u\) with \(u(T_i)>0\) on \(I\) and \(u(T_j)<0\) on \(I^c\). Then \(u(y)=\sum a_iu(T_i)\ge0\) and \(u(y)=\sum b_ju(T_j)\le0\), so
\(u(y)=0\), whence all \(a_i=0\) and \(y=0\): contradiction. *This is the only place where a weakly signed dependence
is upgraded to a strict one, and it uses (GP) through Lemma 1.2.*

(⇐) Let \(g\in L\cap O_I\) and \(y=\sum_Ig_iT_i=-\sum_{I^c}g_jT_j\in\mathrm{pos}(T_I)\cap\mathrm{pos}(T_{I^c})\). If \(y\ne0\)
we are done. If \(y=0\), then \((T_i)_{i\in I}\) is linearly dependent, so \(|I|\ge m+1\) by (GP), so (GP again, \(m\ge1\))
\(T_I\) spans \(V\); likewise \(T_{I^c}\) spans \(V\). Pick \(w\ne0\) and \(h\in\mathbb R^M\) with \(\sum_Ih_iT_i=w\),
\(\sum_{I^c}h_jT_j=-w\); then \(h\in L\), \(g+th\in L\cap O_I\) for small \(t>0\) (the orthant is open), and the
corresponding common vector is \(tw\ne0\). ∎

*Remarks.* (a) The hypothesis \(I\ne\varnothing,[M]\) is necessary: \(\mathrm{pos}(\varnothing)=\{0\}\), whereas
\(L\cap O_{[M]}\neq\varnothing\) is possible. The boundary levels are therefore *defined* by the orthant
condition (Proposition 1.5). (b) \(m\ge1\) is necessary (for \(m=0\) all \(T_i=0\)). (c) Without (GP) both
directions fail (CE7: \(T=((1,0),(1,0),(0,1))\) for (⇒), \(T=((1,0),(-1,0),(0,1),(0,-1))\) for (⇐)).

**Proposition 1.5 (boundary levels) [PROVED; LEAN for (a)].** Let \(T\) satisfy (GP), \(m\ge1\), \(M\ge1\).
(a) \(Z_q(T)=Z_{M-q}(T)\). (b) \(Z_M(T)=Z_0(T)=\mathbf 1\{0\in\mathrm{int\,conv}(T_1,\dots,T_M)\}=\mathbf 1\{\mathrm{pos}(T)=V\}=\mathbf 1\{0\in\mathrm{conv}(T)\}\).
(c) If \(M\le m\), then \(Z_q(T)=0\) for all \(q\).

*Proof.* (a) was shown in §0. (c) \(T\) is independent, so \(L=\{0\}\), and \(0\notin O_I\) as \(M\ge1\).
(b) By Theorem 1.3, \(Z_M=1\) iff no \(u\) is positive on all \(T_i\). If \(M\le m-1\) both sides vanish
(\(\mathrm{pos}(T)\) lies in a hyperplane). If \(M\ge m\), the \(T_i\) span \(V\), so a nonzero \(u\ge0\) on \(T\) is positive
somewhere and Lemma 1.2 makes it strictly positive; hence \(Z_M=1\) iff no nonzero \(u\) is \(\ge0\) on \(\mathrm{pos}(T)\),
iff \(\mathrm{pos}(T)=V\) (a finitely generated cone is closed; Farkas), iff \(0\in\mathrm{int\,conv}(T)\). Finally if
\(0\in\mathrm{conv}(T)\setminus\mathrm{int\,conv}(T)\), a supporting hyperplane \(H\ni0\) of \(\mathrm{conv}(T)\) gives
\(0\in\mathrm{conv}(T\cap H)\); the vectors in the linear hyperplane \(H\) are at most \(m-1\) and independent by (GP),
so \(0\) is not in their convex hull: contradiction. ∎

**Proposition 1.6 (heredity and totals) [PROVED; LEAN for (b)].** Let \(T\) satisfy (GP) in \(V\), \(\dim V=m\ge1\).
(a) \(T\setminus i\) satisfies (GP) in \(V\), and \(T/i\) satisfies (GP) in \(V/\mathbb RT_i\).
(b) If \(M\ge m+1\), \(T\) has no coloops; if \(1\le M\le m\), every \(i\) is a coloop.
(c) [KNOWN: Schläfli, Cover–Efron, Wendel] If \(M\ge m+1\), \(\sum_qZ_q(T)=2\sum_{j=0}^{M-m-1}\binom{M-1}{j}\)
and \(\sum_qY_q(T)=2\sum_{j=0}^{m-1}\binom{M-1}{j}\).

*Proof.* (a) Deletion: subfamilies of \(T\setminus i\) are subfamilies of \(T\). Contraction: \(T_i\ne0\) by (GP);
for \(J\not\ni i\) with \(|J|\le m-1\), \((\bar T_j)_{j\in J}\) is independent in \(V/\mathbb RT_i\) iff \((T_j)_{j\in J\cup\{i\}}\) is
independent in \(V\), which holds by (GP). (b) If \(M\ge m+1\), any \(m\) of the \(T_j\), \(j\ne i\), span \(V\ni T_i\). If
\(M\le m\), \(T\) is independent. (c) \(Y\)-total = number of regions of a generic central arrangement of \(M\)
hyperplanes in \(\mathbb R^m\) (Schläfli/Cover–Efron), and \(\sum_q(Y_q+Z_q)=2^M\). ∎

---

## 2. The contraction–deletion identity

**Lemma 2.1 (kernels) [PROVED; LEAN].** Let \(p_i:\mathbb R^M\to\mathbb R^{M-1}\) forget coordinate \(i\) and
\(\iota_i:\mathbb R^{M-1}\to\mathbb R^M\) insert a zero at position \(i\). Then
\(L(T\setminus i)=\iota_i^{-1}(L(T))=L(T)\cap\{g_i=0\}\) (read in \(\mathbb R^{M-1}\)) and \(L(T/i)=p_i(L(T))\).

*Proof.* The first is immediate. For the second: \(g'\in L(T/i)\iff\sum_{j\ne i}g'_jT_j\in\mathbb RT_i\iff\exists c:\
\sum_{j\ne i}g'_jT_j-cT_i=0\iff\exists g\in L(T)\) with \(p_i(g)=g'\). ∎

**Lemma 2.2 (region correspondence) [PROVED; LEAN].** Let \(L\subseteq\mathbb R^M\) be a linear subspace and
\(i\) a coordinate such that \(g_i\ne0\) for some \(g\in L\). For \(s'\in\{\pm\}^{[M]\setminus i}\) let \(s'^{\pm}\) be its two
extensions with \(s_i=\pm\). Then
\[
\text{(a)}\ \ p_i(L)\cap O_{s'}\ne\varnothing\iff L\cap O_{s'^+}\ne\varnothing\ \text{or}\ L\cap O_{s'^-}\ne\varnothing;\qquad
\text{(b)}\ \ \iota_i^{-1}(L)\cap O_{s'}\ne\varnothing\iff L\cap O_{s'^+}\ne\varnothing\ \text{and}\ L\cap O_{s'^-}\ne\varnothing .
\]

*Proof.* Fix \(v\in L\) with \(v_i\ne0\).
(a, ⇐) \(p_i\) maps \(O_{s'^\pm}\) into \(O_{s'}\). (a, ⇒) Let \(g\in L\), \(p_i(g)\in O_{s'}\). If \(g_i\ne0\), \(g\in O_{s'^{\mathrm{sign}\,g_i}}\).
If \(g_i=0\), then for \(|t|\) small \(p_i(g+tv)\in O_{s'}\) (open) and \((g+tv)_i=tv_i\neq0\).
(b, ⇒) If \(g\in L\), \(g_i=0\), \(p_i(g)\in O_{s'}\), then \(g\pm tv\) for small \(t>0\) lie in \(O_{s'^+}\) and \(O_{s'^-}\) (in some order).
(b, ⇐) If \(g^+\in L\cap O_{s'^+}\), \(g^-\in L\cap O_{s'^-}\), put \(\lambda=g^+_i/(g^+_i-g^-_i)\in(0,1)\); then
\(h=(1-\lambda)g^++\lambda g^-\in L\) has \(h_i=0\) and, for \(j\ne i\), \(h_j\) is a convex combination of two numbers of
sign \(s'_j\), so \(p_i(h)\in O_{s'}\) and \(h=\iota_i(p_i(h))\). ∎

Geometrically: the regions of the coordinate arrangement in \(p_i(L)\) are the regions of \(L\) with the wall
\(\{g_i=0\}\) forgotten; such a region is either a single region of \(L\) (not cut) or the union of two regions of
\(L\) together with the piece of wall between them (cut); the cut ones are exactly the regions of
\(L\cap\{g_i=0\}\). The hypothesis \(g_i\not\equiv0\) on \(L\) says that \(\{g_i=0\}\) is a genuine hyperplane of \(L\).

**Theorem 2.3 (contraction–deletion identity) [PROVED, NU; LEAN].** Let \(T\) be a configuration of \(M\ge1\)
vectors without coloops (no general position needed). For every integer \(q\),
\[
(M-q)\,Z_q(T)+(q+1)\,Z_{q+1}(T)=\sum_{i=1}^MZ_q(T/i)+\sum_{i=1}^MZ_q(T\setminus i).\tag{2.1}
\]
More precisely, for every single \(i\) that is not a coloop,
\[
Z_q(T/i)+Z_q(T\setminus i)=\#\{s\text{ tope}:\ s_i=-,\ |s^+|=q\}+\#\{s\text{ tope}:\ s_i=+,\ |s^+|=q+1\}.\tag{2.2}
\]
The same holds for any linear subspace \(L\subseteq\mathbb R^M\) on which no coordinate vanishes identically, with
\(T/i\), \(T\setminus i\) replaced by \(p_i(L)\), \(\iota_i^{-1}(L)\).

*Proof.* By Lemma 2.1 and Lemma 2.2, with \(A(s')\), \(B(s')\) the two events "\(s'^+\) is a tope", "\(s'^-\) is a tope",
\[
Z_q(T/i)+Z_q(T\setminus i)=\#\{s':|s'^+|=q,\ A\vee B\}+\#\{s':|s'^+|=q,\ A\wedge B\}=\#\{s':|s'^+|=q,A\}+\#\{s':|s'^+|=q,B\}.
\]
Now \(s'\mapsto s'^+\) is a bijection from \(\{s':|s'^+|=q\}\) onto \(\{s:s_i=+,|s^+|=q+1\}\), and \(s'\mapsto s'^-\) onto
\(\{s:s_i=-,|s^+|=q\}\). This is (2.2). Summing (2.2) over \(i\) and exchanging the order of summation,
\(\sum_i\#\{s\text{ tope}:s_i=+,|s^+|=q+1\}=\sum_{s\text{ tope},|s^+|=q+1}|s^+|=(q+1)Z_{q+1}\) and
\(\sum_i\#\{s\text{ tope}:s_i=-,|s^+|=q\}=(M-q)Z_q\). ∎

*Multiplicities and boundary cases.* Each tope \(s\) with \(|s^+|=q+1\) is counted once for each of its \(q+1\)
plus-coordinates, each tope with \(|s^+|=q\) once for each of its \(M-q\) minus-coordinates. For \(q=M\) both sides
vanish; for \(q=M-1\) (2.1) reads \(Z_{M-1}+MZ_M=\sum_iZ_{M-1}(T/i)+\sum_iZ_{M-1}(T\setminus i)\); for \(q=0\),
\(MZ_0+Z_1=\sum_i(Z_0(T/i)+Z_0(T\setminus i))\); for \(q<0\) everything vanishes. No uniformity (simplicity) of
the oriented matroid is needed: only the absence of coloops. With a coloop (2.1) can fail: \(M=1\), \(T_1\ne0\),
\(q=0\): LHS \(=0\), RHS \(=1+1\). Under (GP) the hypothesis holds iff \(M\ge m+1\) or \(m=0\)
(Proposition 1.6(b)); for \(2\le M\le m\) both sides of (2.1) vanish anyway.

**Corollary 2.4 (diagonal form) [PROVED, NU; LEAN for the consequence below].** Expand \(P_T(x)=\sum_qZ_q(T)x^q=\sum_{k=0}^Ma_k(T)(1+x)^{M-k}(1-x)^k\)
(the polynomials \((1+x)^{M-k}(1-x)^k\) form a basis of polynomials of degree \(\le M\)). Under the hypotheses of
Theorem 2.3, for \(0\le k\le M-1\),
\[
2(M-k)\,a_k(T)=\sum_ia_k(T/i)+\sum_ia_k(T\setminus i),\tag{2.3}
\]
(coefficients of the \((M-1)\)-configurations taken in the degree-\((M-1)\) basis). Moreover \(a_k(T)=0\) for odd
\(k\) (palindromy), \(2^Ma_0(T)=\sum_qZ_q(T)\), and \(2^Ma_M(T)=\sum_q(-1)^qZ_q(T)\).

*Proof.* The left side of (2.1), as a generating function, is \(MP+(1-x)P'\). For \(P=(1+x)^{M-k}(1-x)^k\) one
computes \(MP+(1-x)P'=(M-k)(1+x)^{M-k-1}(1-x)^k[(1+x)+(1-x)]=2(M-k)(1+x)^{M-1-k}(1-x)^k\); compare coefficients.
Palindromy \(x^MP(1/x)=P(x)\) maps the \(k\)-th basis polynomial to \((-1)^k\) times itself. Evaluate at \(x=\pm1\). ∎

In particular (2.3) determines \(a_0,\dots,a_{M-1}\) from the smaller configurations, but not \(a_M\); and
if \(M\) is odd, \(a_M=0\) by palindromy. So **the top level \(Z_M\) is needed as independent input only when
\(M\) is even.**
(Lean: `Zc_eq_of_minors` in `RequestProject/LevelCounts/Solving.lean` — two coloop-free configurations whose minor
sums agree have the same level vector if their top levels agree or their size is odd; the proof uses the closed form
\(d_{M-j}=(-1)^j\binom Mjd_M\) of the homogeneous recursion instead of the basis expansion.)

---
## 3. Walk and bridge configurations

**Definition 3.1.** A *component type* is either \(\mathsf W_w\) (a walk with \(w\ge1\) points) or \(\mathsf B_b\) (a bridge
with \(b\ge1\) points). Data for \(\mathsf W_w\): increments \(x=(x_1,\dots,x_w)\in V^w\); points \(x_1+\dots+x_k\),
\(1\le k\le w\); symmetry group \(B_w\). Data for \(\mathsf B_b\): increments \(y=(y_1,\dots,y_{b+1})\in V^{b+1}\) with
\(\sum y_j=0\); points \(y_1+\dots+y_k\), \(1\le k\le b\) (the endpoint \(0\) is excluded); symmetry group
\(\mathfrak S_{b+1}\). A *type* \(\tau\) is a finite list of component types; \(M(\tau)\) is the total number of points;
\(G_\tau\) is the product of the component groups, acting componentwise on data \(\xi\); \(T_\tau(\xi)\) is the
configuration of all points of all components (the empty type has \(M=0\), \(G=\{1\}\)).
For the single walk \(\tau=(\mathsf W_N)\) this is \(S_1,\dots,S_N\) with group \(B_N\).

**Lemma 3.2 (contraction splits components) [PROVED].** Let \(P\) be the \(k\)-th point of a component \(c\) of
\(T=T_\tau(\xi)\), \(\pi:V\to V'=V/\mathbb RP\).
(a) If \(c=\mathsf W_w\) with increments \(x\), then \(T/P\cong T_{\tau'}(\xi')\) where \(c\) is replaced by
\(\mathsf B_{k-1}\) with increments \((\pi x_1,\dots,\pi x_k)\) and \(\mathsf W_{w-k}\) with increments \((\pi x_{k+1},\dots,\pi x_w)\),
all other components being projected by \(\pi\) (components with \(0\) points are dropped).
(b) If \(c=\mathsf B_b\) with increments \(y\), then \(c\) is replaced by \(\mathsf B_{k-1}\) with increments
\((\pi y_1,\dots,\pi y_k)\) and \(\mathsf B_{b-k}\) with increments \((\pi y_{k+1},\dots,\pi y_{b+1})\).
Here "\(\cong\)" means equality of indexed families after a fixed relabelling of the index set; \(Z_q\) is unchanged.

*Proof.* (a) For \(j<k\), \(\pi(x_1+\dots+x_j)\) are the points of the sequence \(\pi x_1,\dots,\pi x_k\), whose total
\(\pi P\) is \(0\): a bridge with \(k-1\) points. For \(j>k\), \(\pi(x_1+\dots+x_j)=\pi(x_{k+1}+\dots+x_j)\): a walk.
(b) Same, using \(\pi(y_{k+1}+\dots+y_{b+1})=\pi(-P)=0\). ∎

*Quotient maps and dependence.* The new components share the single quotient map \(\pi\), which depends on the
data (on \(P\)); the components of \(\xi'\) are *not* independent in any probabilistic sense, and no independence
is ever used: only invariance of the orbit sum (proof of Theorem 4.1, step 2).

**Lemma 3.3 (block reshuffling) [PROVED].** For a list \(x=(x_1,\dots,x_w)\), \(w\ge2\), and \(1\le k\le w\), let
\(\mu_k(x)\in V^{w-1}\) be the increments of the walk \(\mathsf W_w(x)\setminus k\):
\(\mu_k(x)=(x_1,\dots,x_{k-1},x_k+x_{k+1},x_{k+2},\dots,x_w)\) for \(k<w\) and \(\mu_w(x)=(x_1,\dots,x_{w-1})\).
For \(\alpha<\beta\) and \(\rho=\pm1\) let \(y^{\alpha\beta\rho}\in V^{w-1}\) be \(x\) with \(x_\alpha,x_\beta\) replaced by the single entry
\(x_\alpha+\rho x_\beta\), and \(y^\gamma\) be \(x\) with \(x_\gamma\) removed. Then for every function \(f\) on \(V^{w-1}\),
\[
\sum_{g\in B_w}\sum_{k=1}^wf\big(\mu_k(g x)\big)=2\sum_{\alpha<\beta,\ \rho=\pm1}\ \sum_{h\in B_{w-1}}f(h\,y^{\alpha\beta\rho})+2\sum_{\gamma=1}^w\sum_{h\in B_{w-1}}f(h\,y^\gamma).\tag{3.1}
\]
For a bridge, \(\mathsf B_b(y)\setminus k\) has increments \(\nu_k(y)=(y_1,\dots,y_k+y_{k+1},\dots,y_{b+1})\) (\(1\le k\le b\); both
end points are merges, never drops), and with \(y^{\alpha\beta}\) = \(y\) with \(y_\alpha,y_\beta\) merged into \(y_\alpha+y_\beta\),
\[
\sum_{\sigma\in\mathfrak S_{b+1}}\sum_{k=1}^bf\big(\nu_k(\sigma y)\big)=2\sum_{\alpha<\beta}\ \sum_{h\in\mathfrak S_b}f(h\,y^{\alpha\beta}).\tag{3.2}
\]

*Proof.* (3.1), merge terms \(k<w\). Write \(gx=(\varepsilon_1x_{\sigma(1)},\dots,\varepsilon_wx_{\sigma(w)})\). Then \(\mu_k(gx)\) is a list of
\(w-1\) *blocks*: signed singletons and, at position \(k\), the block \(\varepsilon_kx_{\sigma(k)}+\varepsilon_{k+1}x_{\sigma(k+1)}\). Let
\(\{\alpha<\beta\}=\{\sigma(k),\sigma(k+1)\}\), \(\rho=\varepsilon_k\varepsilon_{k+1}\), and let \(\eta\) be the sign carried by \(x_\alpha\). The block equals
\(\eta(x_\alpha+\rho x_\beta)\), so \(\mu_k(gx)=h\,y^{\alpha\beta\rho}\) for a unique \(h\in B_{w-1}\) (which permutes the blocks and
assigns their signs). Conversely, \((h,\alpha,\beta,\rho)\) together with the choice of which of \(\alpha,\beta\) comes first inside the
merged block determines \((g,k)\) uniquely. Hence \((g,k)\mapsto(h,\alpha,\beta,\rho)\) is exactly 2-to-1; the counts agree:
\((w-1)\,2^ww!=2\cdot\binom w2\cdot2\cdot2^{w-1}(w-1)!\).
Drop term \(k=w\): \(\mu_w(gx)=h\,y^{\gamma}\) with \(\gamma=\sigma(w)\), and \(g\mapsto(h,\gamma,\varepsilon_w)\) is a bijection
\(B_w\to B_{w-1}\times[w]\times\{\pm1\}\), giving the factor 2.
(3.2): \(\nu_k(\sigma y)\) has the merged block \(y_{\sigma(k)}+y_{\sigma(k+1)}\) at position \(k\in[b]\) among \(b\) blocks; every
position \(1..b\) of the merged block among the \(b\) blocks occurs, and \((\sigma,k)\mapsto(h,\{\sigma(k),\sigma(k+1)\})\) is 2-to-1:
\(b\,(b+1)!=2\binom{b+1}2b!\). ∎

*Probabilistic reading.* If \(X\) is (±Ex) in \(V^w\) and \(K\) is uniform on \([w]\), independent of \(X\), then
\(\mu_K(X)\) is (±Ex) in \(V^{w-1}\): by (3.1) the law of \(\mu_K(X)\) is \(\frac1{w}\mathbb E\) of the uniform measure on the
\(B_w\times[w]\) image, which is a mixture of uniform \(B_{w-1}\)-orbit measures. *Deleting the first point
\(S_1\)* corresponds to merging \(x_1+x_2\) (it is a merge, not a drop: the walk starts at the origin, which is
not a point of the configuration); *deleting the last point \(S_w\)* corresponds to dropping \(x_w\). For a fixed
\(k\), \(\mu_k(X)\) is in general *not* (±Ex) (merged and unmerged increments have different laws); only the sum over
\(k\) is invariant, and (2.1) involves only that sum.

**Lemma 3.4 (genericity is hereditary) [PROVED].** Call data \(\xi\) of type \(\tau\) in \(V\) *generic* if
\(T_\tau(g\xi)\) satisfies (GP) for every \(g\in G_\tau\). If \(\xi\) is generic, then (a) for every point \(P\) and every
\(g\), the contracted data \((g\xi)'\) of Lemma 3.2 are generic for \(\tau'\) in \(V/\mathbb RP\); (b) every base list
\(y^{\alpha\beta\rho}\), \(y^\gamma\), \(y^{\alpha\beta}\) of Lemma 3.3 (with the other components unchanged) is generic for the type with
one point fewer.

*Proof.* (a) Let \(H\subseteq G_\tau\) be the subgroup acting on the first \(k\) increments of \(c\) by permutations only
(\(\mathfrak S_k\)), on the remaining increments of \(c\) by \(B_{w-k}\) (resp. \(\mathfrak S_{b+1-k}\)), and on the other
components by their full groups. Every \(h\in H\) fixes \(P\): \(P(h g\xi)=P(g\xi)\). The \(G_{\tau'}\)-orbit of \((g\xi)'\) is
\(\{T_\tau(hg\xi)/P:h\in H\}\) (as \(H\cong G_{\tau'}\) compatibly with Lemma 3.2), and each of these satisfies (GP) by
Proposition 1.6(a). (b) Every element of the \(B_{w-1}\)-orbit of a base list equals some \(\mu_k(g x)\) (surjectivity in
the proof of Lemma 3.3), so its configuration is \(T_\tau(g\xi)\setminus P\), which satisfies (GP). ∎

---

## 4. The orbit theorem and the probabilistic theorem

**Absorption input (A).** For every type \(\tau\), every \(m\ge1\) and every generic \(\xi\) of type \(\tau\) in a space
of dimension \(m\),
\[
\sum_{g\in G_\tau}\mathbf 1\{0\in\mathrm{conv}\,T_\tau(g\xi)\}=|G_\tau|\,a_\tau(m)
\]
with \(a_\tau(m)\) depending only on \(\tau\) and \(m\). **Status [KNOWN].** Kabluchko–Vysotsky–Zaporozhets, *Adv. Math.*
320 (2017), Theorem 2.1 (= Godland–Kabluchko, SPA 2022, Theorem 4.1) computes
\(\mathbb P(0\in\mathrm{conv})\) for \(s\) walks of lengths \(n_1..n_s\) and \(r\) bridges with \(m_1..m_r\ge2\) increments
whose joint increment law is invariant under \(\prod B_{n_i}\times\prod\mathfrak S_{m_j}\) and which are a.s. in general
position ("any \(d\) of the vectors linearly independent"): \(\mathbb P[0\in\mathrm{conv}]=2(c_{d+1}+c_{d+3}+\dots)/(\prod2^{n_i}n_i!\prod m_j!)\)
where \(\sum_kc_kt^k=\prod_i(t+1)(t+3)\cdots(t+2n_i-1)\prod_j(t+1)(t+2)\cdots(t+m_j-1)\). Applied to the *uniform law on the
orbit* \(\{g\xi\}\) (which is \(G_\tau\)-invariant, and a.s. in general position exactly when \(\xi\) is generic), it is (A).
Our bridge \(\mathsf B_b\) has \(m_j=b+1\ge2\) increments. By Proposition 1.5(b), \(\mathbf 1\{0\in\mathrm{conv}\,T\}=Z_M(T)\) for
generic data.

**Theorem 4.1 (orbit theorem) [COND on (A) for even \(M\); PROVED, NU].** For every type \(\tau\) and \(m\ge0\) there
are numbers \(z_\tau(m,q)\) such that for every \(V\) of dimension \(m\) and every generic \(\xi\) of type \(\tau\) in \(V\),
\[
\sum_{g\in G_\tau}Z_q\big(T_\tau(g\xi)\big)=|G_\tau|\,z_\tau(m,q)\qquad(0\le q\le M(\tau)).
\]
The numbers are determined by: \(z_\tau(m,q)=\binom Mq\) if \(m=0\); \(z_\tau(m,q)=0\) if \(1\le M\le m\);
\(z_\varnothing(m,0)=1\); \(z_\tau(m,M)=a_\tau(m)\) if \(M\ge m+1\), \(M\) even; and for \(M\ge m+1\ge2\), \(0\le q\le M-1\),
\[
(M-q)z_\tau(m,q)+(q+1)z_\tau(m,q+1)=\sum_{(c,k)}z_{\tau/(c,k)}(m-1,q)+\sum_{c}\mathrm{len}(c)\,z_{\tau-c}(m,q),\tag{4.1}
\]
where \((c,k)\) runs over all points (component \(c\), index \(k\)), \(\tau/(c,k)\) is the type of Lemma 3.2,
\(\mathrm{len}(c)\) is the number of points of \(c\), and \(\tau-c\) is \(\tau\) with \(c\) shortened by one point (removed if it had
one point). For odd \(M\ge m+1\) the top value is forced by palindromy (Corollary 2.4) and (A) is not used.

*Proof.* Induction on \(M\). The cases \(M=0\), \(m=0\) (\(L=\mathbb R^M\)) and \(1\le M\le m\) (Proposition 1.5(c)) are
immediate. Let \(M\ge m+1\), \(m\ge1\), \(\xi\) generic. Every \(T_\tau(g\xi)\) satisfies (GP), hence has no coloops
(Proposition 1.6(b)); apply (2.1) to it and sum over \(g\in G_\tau\).

*Step 1 (deletion terms).* Fix a component \(c\) with \(\ell\) points; the other components are carried along
unchanged. If \(c=\mathsf W_\ell\), Lemma 3.3 (3.1) applied to the function
\(f(\cdot)=\sum_{g'\in G_{\text{other}}}Z_q(\cdots)\) expresses \(\sum_g\sum_kZ_q(T_\tau(g\xi)\setminus(c,k))\) as \(2\binom\ell2\cdot2+2\ell=2\ell^2\)
orbit sums of type \(\tau-c\), each of generic data (Lemma 3.4(b)), hence by induction equal to
\(2\ell^2|B_{\ell-1}||G_{\text{other}}|z_{\tau-c}(m,q)=\ell|G_\tau|z_{\tau-c}(m,q)\). For \(c=\mathsf B_\ell\), (3.2) gives
\(2\binom{\ell+1}2\) orbit sums, i.e. \(\ell(\ell+1)\,\ell!\,|G_{\text{other}}|z=\ell|G_\tau|z_{\tau-c}\). If \(\ell=1\), deleting the point removes
\(c\); its group (\(B_1\) or \(\mathfrak S_2\), order 2) acts trivially on the remaining configuration, giving \(|G_\tau|z_{\tau-c}\).

*Step 2 (contraction terms).* Fix a point \((c,k)\) and let \(H\) be the subgroup of Lemma 3.4(a). For any function
\(F\) on \(G_\tau\), \(\sum_gF(g)=\frac1{|H|}\sum_g\sum_{h\in H}F(hg)\). With \(F(g)=Z_q(T_\tau(g\xi)/(c,k))\): since
\(P(hg\xi)=P(g\xi)\), the inner sum is the \(G_{\tau'}\)-orbit sum of the generic data \((g\xi)'\) in \(V/\mathbb RP(g\xi)\), which
equals \(|G_{\tau'}|z_{\tau'}(m-1,q)\) by induction. As \(|H|=|G_{\tau'}|\), the total is \(|G_\tau|z_{\tau/(c,k)}(m-1,q)\).
(Note that \(H\) uses only *permutations* of the first \(k\) increments: sign changes there would move \(P\). This is
exactly why the piece before \(P\) becomes a bridge, with symmetric group \(\mathfrak S_k\).)

*Step 3 (top level and solving).* By Steps 1–2, the right side of (2.1), summed over \(g\), equals \(|G_\tau|\) times the
right side of (4.1). For even \(M\), (A) gives \(\sum_gZ_M=|G_\tau|a_\tau(m)\); for odd \(M\), Corollary 2.4 applied to
\(\sum_gP_{T_\tau(g\xi)}\) shows that its \(a_M\)-coefficient vanishes while \(a_0..a_{M-1}\) are \(|G_\tau|\) times universal
numbers by (2.3). In both cases solving (2.1) downwards from \(q=M-1\) to \(q=0\) shows that each
\(\sum_gZ_q(T_\tau(g\xi))\) is \(|G_\tau|\) times a number depending only on \(\tau,m,q\). ∎

*Uniqueness.* (4.1) with the stated boundary data is a triangular system (in \(M\), then downward in \(q\)), so it
determines \(z_\tau(m,q)\) uniquely; `certificates/levelrec.py` implements it with exact rationals.

**Theorem 4.2 (expected conic level counts) [COND on (A); PROVED, NU].** Let \(X_1,\dots,X_N\) be random vectors in
\(\mathbb R^d\) satisfying (±Ex), and assume that \(S_1,\dots,S_N\) are a.s. in general linear position. Then for
\(0\le q\le N\),
\[
\mathbb E\,Z_q(S_1,\dots,S_N)=z(N,d,q):=z_{(\mathsf W_N)}(d,q),\qquad \mathbb E\,Y_q=\binom Nq-z(N,d,q),
\]
independent of the law of the increments. More generally, for a random configuration of type \(\tau\) whose data
law is \(G_\tau\)-invariant and a.s. in general position, \(\mathbb EZ_q=z_\tau(d,q)\). For \(\varnothing\ne I\subsetneq[N]\) the
event counted is "\(\mathrm{pos}(S_I)\cap\mathrm{pos}(S_{I^c})\ne\{0\}\)" (Theorem 1.4); the complementary count \(Y_q\)
is the number of \(q\)-sets strictly linearly separable from their complement (Theorem 1.3).

*Proof.* Let \(F\) be the event that some \(g\cdot X\) violates (GP); by invariance and the a.s. hypothesis,
\(\mathbb P(F)=0\). By invariance, \(\mathbb EZ_q(X)=\mathbb E\big[\frac1{|B_N|}\sum_gZ_q(gX)\big]\); off \(F\), the data \(X(\omega)\) are
generic and the bracket equals \(z(N,d,q)\) by Theorem 4.1. ∎

**Remark 4.3 (measurability).** On the open dense set of data in general position, \(Y_q=\sum_{|I|=q}\mathbf 1_{U_I}\)
with \(U_I=\{\xi:\exists u,\ \pm u(S_i(\xi))>0\}\) a union of open sets (Theorem 1.3); so \(Y_q\) and \(Z_q\) are Borel
there, and the expectations are well defined.

**Remark 4.4 (weaker symmetry).** (±Ex) cannot be replaced by (Ex): CE3 (`certificates/out_counterexamples.txt`):
for \(d=2,N=4\), three exchangeable laws give \(\mathbb EZ_4=1/4,\ 0,\ 1/12\). It is instructive to see where the
proof breaks. The class of *(Ex)-walks* and bridges is closed under the operations: contraction at a walk point
gives a bridge and an (Ex)-walk (with \(H=\mathfrak S_k\times\mathfrak S_{w-k}\times\cdots\)), and the unsigned version of
(3.1) (\(\rho=+1\) only, \((\sigma,k)\mapsto(h,\alpha,\beta)\) 2-to-1 for merges, \(\sigma\mapsto(h,\gamma)\) bijective for the drop)
holds. Hence Steps 1–2 survive, and the **only** failure is the absorption input (A), which is false for
(Ex)-walks (positive increments are never absorbed). Consequently, under (Ex) alone the orbit sums of all
\(Z_q\) are determined by the orbit sums of the absorption indicators of the even-size derived configurations.

**Recursion data and values [PROVED; exact].** For \(\tau=(\mathsf W_N)\) the recursion (4.1) involves the types
\((\mathsf B_{a_1},\dots,\mathsf B_{a_r},\mathsf W_w)\) (at most one walk, which is always the *last* piece). Table of
\(\mathbb EZ_q\) (\(q=0..N\), palindromic): \(d=2,N=4\): \(1/12,\,2,\,23/6,\,2,\,1/12\);
\(d=2,N=5\): \(77/640,\,5867/1920,\,7511/960,\dots\); \(d=3,N=5\): \(5/384,\,385/384,\,255/64,\dots\) (`certificates/out_check_universality.txt`,
14 cases including several walks and bridges and the cut-set version, each matched by exhaustive orbit enumeration of
three integer increment lists). For \(N=d+1\) the kernel is a line, the topes are \(\pm\mathrm{sign}(g)\), and
\(z(d+1,d,q)=2B(d+1,q)/(2^{d+1}(d+1)!)\) for all \(q\) (with the type-B Eulerian numbers \(B(n,k)\), using
\(B(n,k)=B(n,n-k)\)); this is Theorem C (§8), e.g. \(d=2\): \(1/24,\,23/24,\,23/24,\,1/24\).

**Corollary 4.5 (d=1) [KNOWN: Sparre Andersen].** For \(d=1\) and data in general position (\(S_i\ne0\)), the only
separating functionals are \(u>0\) and \(u<0\), so \(Y_q=\mathbf 1\{N_+=q\}+\mathbf 1\{N_+=N-q\}\) with
\(N_+=\#\{i:S_i>0\}\). By the symmetry \(X\mapsto-X\), \(\mathbb EY_q=2\,\mathbb P(N_+=q)\), so Theorem 4.2 re-derives the
distribution-freeness of \(N_+\) (Sparre Andersen); the recursion reproduces
\(\mathbb P(N_+=q)=\binom{2q}q\binom{2N-2q}{N-q}4^{-N}\) for \(N\le8\) (`certificates/levelrec.py`). The one-dimensional base is
*not* needed in the induction (the bases are \(m=0\) and \(M\le m\)); in \(d=1\)
the input (A) is itself the case \(q\in\{0,N\}\) of Sparre Andersen's theorem, so this is a consistency check, not an
independent proof.

---
## 5. Subset averaging and circuit corollaries

**Lemma 5.1 (subset averaging) [PROVED].** Let \(X\) be (±Ex) in \(V^N\), \(1\le u\le N\), and let \(U\) be a uniformly
random \(u\)-subset of \([N]\), independent of \(X\). Write \(U=\{u_1<\dots<u_u\}\) and
\(Y^U=(S_{u_1},\,S_{u_2}-S_{u_1},\dots,S_{u_u}-S_{u_{u-1}})\) (block sums; the increments after \(u_u\) are discarded). Then
\(Y^U\) is (±Ex) in \(V^u\), its walk is \((S_i)_{i\in U}\), and it is a.s. in general position if \(S\) is.
Consequently, for every bounded Borel \(f\),
\(\ \mathbb E\sum_{|U|=u}f\big((S_i)_{i\in U}\big)=\binom Nu\,\mathbb Ef(\text{walk of }Y^U)\).

*Proof.* Signs: changing the signs of all increments in block \(a\) changes the sign of \(Y^U_a\) only, and leaves the
law of \((X,U)\) invariant. Permutations: \(U\) is determined by its block sizes \((b_1,\dots,b_u)\) (positive) and the
discarded tail \(b_{u+1}\ge0\); for \(\pi\in\mathfrak S_u\) let \(U^\pi\) have block sizes \((b_{\pi(1)},\dots,b_{\pi(u)})\) and the same
tail, and let \(\rho\) be the permutation of \([N]\) moving the blocks accordingly. Then
\((Y^U_{\pi(1)},\dots,Y^U_{\pi(u)})=Y^{U^\pi}(\rho X)\), and \((\rho X,U^\pi)\overset d=(X,U)\) because \(U\mapsto U^\pi\) is a bijection of the
\(u\)-subsets and \(\rho X\overset d= X\) conditionally on \(U\). General position is inherited by subfamilies. ∎

(A deterministic orbit version follows by iterating Lemma 3.3: deleting the \(N-u\) points outside \(U\) in all orders.)

**Theorem 5.2 (cut-set level counts) [COND on (A); PROVED, NU].** Under the hypotheses of Theorem 4.2, for
\(1\le u\le N\) and \(0\le q\le u\): \(\ \mathbb E\sum_{|U|=u}Z_q(S_U)=\binom Nu\,z(u,d,q)\).

*Proof.* Lemma 5.1 and Theorem 4.2 applied to the law of \(Y^U\). ∎

**Corollary 5.3 (Kabluchko–Vysotsky–Zaporozhets' arcsine law) [KNOWN].** With \(q=u=k\),
\(Z_k(S_U)=\mathbf 1\{0\in\mathrm{conv}\,S_U\}\) (Proposition 1.5), so
\(\mathbb E\#\{U:|U|=k,\ 0\notin\mathrm{conv}\,S_U\}=\binom Nk(1-a_{(\mathsf W_k)}(d))=\binom Nk\frac{2(B(k,d-1)+B(k,d-3)+\cdots)}{2^kk!}\),
which is KVZ, *Bernoulli* 25 (2019), Theorem 1.2 (their \(M^{(d)}_{n,k}\)). This is exactly their "second proof"
(their §3.1: absorption + averaging); we include it to fix the dictionary, not as a new result.

**Corollary 5.4 (expected circuit types) [PROVED via KNOWN Theorem C; NU as a stated formula].** Let \(N\ge d+1\), \(S\) as
in Theorem 4.2. Every \((d+1)\)-subset \(C\subseteq[N]\) supports a unique (up to scale) dependence \(g^C\) of
\((S_i)_{i\in C}\) with all coordinates nonzero (Proposition 1.6 / GP). Let \(C_k\) be the number of \(C\) for which
\(\min(\#\{g^C_i>0\},\#\{g^C_i<0\})=k\). Then (the *deterministic* number of circuit supports is \(\binom N{d+1}\)) and
\[
\mathbb E\,C_k=\binom N{d+1}\frac{\eta_k\,B(d+1,k)}{2^{d+1}(d+1)!},\qquad \eta_k=2\ (2k<d+1),\quad\eta_k=1\ (2k=d+1).
\]
In particular the expected number of *positive circuits* (\(0\in\mathrm{int\,conv}\,S_C\)) is
\(\mathbb EC_0=\binom N{d+1}\frac{2}{2^{d+1}(d+1)!}\).

*Proof.* Lemma 5.1 with \(u=d+1\) and \(f=\mathbf 1\{\tau_{\rm lin}=k\}\), and Theorem C (Kabluchko–Panzo, Theorem 4.5; §8)
for the (±Ex) walk \(Y^U\) of \(d+1\) steps. \(B(n,0)=1\). ∎

*What survives averaging and what does not.* (a) *Temporal sign patterns survive:* for a sign word
\(w\in\{\pm\}^{d+1}\) (read in increasing time order along \(C\)),
\(\mathbb E\#\{C:\mathrm{sign}(g^C)\in\{w,-w\}\}=\binom N{d+1}\,\#\{v\in B_{d+1}:\mathrm{ud}(v_1,\dots,v_{d+1},0)\in\{w,-w\}\}/(2^{d+1}(d+1)!)\), by
Lemma 5.1 and the labelled form of Theorem C (`Conic.lean`, `card_radonPat_signedWalk` in `Generalizations.lean`).
(b) *The probability for a fixed support is not distribution-free* (CE4: support \(\{1,2,4\}\), \(d=2,N=4\): positive-circuit
probability \(1/24\) vs \(1/16\)). (c) *The law of the number of circuits of a given type is not distribution-free*
(CE8: \(d=2,N=5\), positive circuits: \(\mathbb P(C_0=3,4,5)=270/3840,170/3840,22/3840\) vs \(278/3840,154/3840,30/3840\),
both with mean \(5/12\)). (d) Since \(Z_k(S_C)\in\{0,1,2\}\) is a function of the type, Corollary 5.4 is also the case
\(u=d+1\) of Theorem 5.2.

---

## 6. Affine level counts

Let \(S_0=0,S_1,\dots,S_n\in\mathbb R^d\), \(S_i=x_1+\dots+x_i\), and put \(\widehat S_i=(S_i,1)\in\mathbb R^{d+1}\). **(GP\(_{\rm aff}\))**: any
\(d+1\) of the \(n+1\) points are affinely independent \(\iff\) \(\widehat S\) satisfies (GP) in \(\mathbb R^{d+1}\).
For \(I\subseteq\{0,\dots,n\}\), \(|I|=q\), define
\(R_q=\#\{I:|I|=q,\ \mathrm{conv}(S_I)\cap\mathrm{conv}(S_{I^c})\ne\varnothing\}\) with \(\mathrm{conv}(\varnothing)=\varnothing\) (so \(R_0=R_{n+1}=0\)),
ordered labelled subsets as in §0.

**Lemma 6.1 (homogenization) [PROVED; LEAN: `Rc_eq_Zc_hom`, `Rc_eq_card_not_affSep`].** Under (GP\(_{\rm aff}\)), \(R_q=Z_q(\widehat S)\) for all
\(q\), and \(\binom{n+1}q-R_q\) is the number of \(q\)-sets strictly separated from their complement by an affine
hyperplane.

*Proof.* For \(\varnothing\ne I\subsetneq\{0..n\}\): \(\mathrm{conv}(S_I)\cap\mathrm{conv}(S_{I^c})\ne\varnothing\iff\mathrm{pos}(\widehat S_I)\cap\mathrm{pos}(\widehat S_{I^c})\ne\{0\}\)
(a nonzero common vector has positive last coordinate; divide by it), and Theorem 1.4 applies (\(m=d+1\ge1\)). For
\(I=\varnothing\) or all: \(\ker\widehat S\) lies in \(\{\sum g_i=0\}\), which misses \(O_\varnothing\) and \(O_{\rm all}\). Separation: Theorem 1.3, a
linear functional on \(\mathbb R^{d+1}\) being an affine functional on \(\mathbb R^d\). ∎

**Lemma 6.2 (cyclic-shift bridge) [PROVED].** Let \(z=(x_1,\dots,x_n,-S_n)\in(\mathbb R^d)^{n+1}\) (sum \(0\)). For
\(0\le j\le n\), the contraction \(\widehat S/j\) is linearly isomorphic to the bridge configuration \(\mathsf B_n\) with
increments \(\mathrm{rot}^j z=(z_{j+1},\dots,z_{n+1},z_1,\dots,z_j)\); explicitly, under
\(\mathbb R^{d+1}/\mathbb R\widehat S_j\cong\mathbb R^d\), \((v,t)\mapsto v-tS_j\), the points are \(S_i-S_j\) (\(i\ne j\)). Moreover
\((\sigma,j)\mapsto\mathrm{rot}^j(\sigma x,-S_n)\) is a bijection \(\mathfrak S_n\times\{0..n\}\to\mathfrak S_{n+1}\cdot z\) (as arrangements of the
\(n+1\) entries of \(z\)).

*Proof.* The map has kernel \(\mathbb R\widehat S_j\) and is onto, so it induces the isomorphism; \(\widehat S_i\mapsto S_i-S_j\). The
partial sums of \(\mathrm{rot}^jz\) are \(S_{j+t}-S_j\) (\(t\le n-j\)), then \(-S_j=S_0-S_j\), then \(S_t-S_j\) (\(t<j\)), ending at
\(0\): exactly \(\{S_i-S_j:i\ne j\}\) in cyclic order. For the bijection: the position of \(-S_n\) in the arrangement
determines \(j\) and the order of the other entries determines \(\sigma\). Linear isomorphisms preserve kernels, hence
\(Z_q\). ∎

**Lemma 6.3 (affine deletion) [PROVED].** Deleting \(\widehat S_0\) gives (after the translation \(v\mapsto v-S_1\), a linear
automorphism \((v,t)\mapsto(v-tS_1,t)\) of \(\mathbb R^{d+1}\)) the affine walk with increments \((x_2,\dots,x_n)\); deleting
\(\widehat S_n\) gives increments \((x_1,\dots,x_{n-1})\); deleting \(\widehat S_j\), \(0<j<n\), merges \(x_j+x_{j+1}\). Summed over \(\mathfrak S_n\):
\[
\sum_{\sigma}\sum_{j=0}^nf\big(\widehat S(\sigma x)\setminus j\big)=2\sum_{\gamma=1}^n\sum_{h\in\mathfrak S_{n-1}}f(\widehat S(hy^\gamma))+2\sum_{\alpha<\beta}\sum_{h\in\mathfrak S_{n-1}}f(\widehat S(hy^{\alpha\beta})).
\]

*Proof.* As in Lemma 3.3 (unsigned): the head drop \(j=0\) and the tail drop \(j=n\) each give a bijection
\(\mathfrak S_n\to\mathfrak S_{n-1}\times[n]\); the merges give a 2-to-1 map. Count: \((n+1)n!=2n(n-1)!+2\binom n2(n-1)!\). ∎

**Theorem 6.4 (expected affine level counts) [COND on bridge absorption; PROVED, NU].** Let \(X_1,\dots,X_n\) be (Ex)
in \(\mathbb R^d\) with \(S_0=0,S_1,\dots,S_n\) a.s. in (GP\(_{\rm aff}\)). Then \(\mathbb ER_q=r(n,d,q)\) depends only on \(n,d,q\);
deterministically, \(\sum_{\sigma\in\mathfrak S_n}R_q(S(\sigma x))=n!\,r(n,d,q)\) whenever all \(S(\sigma x)\) are in (GP\(_{\rm aff}\)). The
numbers satisfy \(r=0\) if \(n\le d\), \(r(n,d,0)=r(n,d,n+1)=0\), and for \(n\ge d+1\), \(0\le q\le n\),
\[
(n+1-q)\,r(n,d,q)+(q+1)\,r(n,d,q+1)=(n+1)\,z_{(\mathsf B_n)}(d,q)+(n+1)\,r(n-1,d,q).\tag{6.1}
\]

*Proof.* Apply (2.1) to \(T=\widehat S(\sigma x)\) (\(M=n+1\ge m+1=d+2\), so no coloops) and sum over \(\sigma\). Contractions:
by Lemma 6.2 the sum is \(\sum_{\pi\in\mathfrak S_{n+1}}Z_q(\mathsf B_n(\pi z))=(n+1)!\,z_{(\mathsf B_n)}(d,q)\) by Theorem 4.1 for one bridge (all its
orbit members are contractions of members of the walk orbit, hence in (GP) by Proposition 1.6(a)). Deletions: by
Lemma 6.3, \((n+1)n!\,r(n-1,d,q)\) by induction on \(n\) (genericity of the base lists as in Lemma 3.4(b)). Top level:
\(Z_{n+1}(\widehat S)=0\). Solve downward. The probabilistic statement follows as in Theorem 4.2. ∎

*Inputs.* The bridge values \(z_{(\mathsf B_n)}(d,q)\) need (A) only for configurations of bridges (type A); these are
KVZ GAFA 2017, Theorem 2.1 (one bridge) and KVZ Adv. Math. 2017, Theorem 2.1 (several bridges, as contraction of a
bridge produces two bridges). No sign symmetry is needed anywhere. Exact agreement with orbit enumeration:
`certificates/out_affine_check.txt`.

**Variants.** (a) *Affine bridge* (\(S_0=S_{n+1}=0\), points \(S_0,\dots,S_n\), (Ex) increments \(y_1..y_{n+1}\) with sum \(0\)):
contraction at any point is a cyclic shift of the same bridge, deletion is a cyclic merge; the same proof gives a
distribution-free \(\mathbb ER_q\) [PROVED, NU]. (b) *Several affine walks from a common origin*: **[FALSE]** (CE5: walk
lengths \((3,2)\), \(\mathbb ER_1=3/2\) vs \(1\); without the origin, lengths \((2,2)\): \(\mathbb ER_1=1/2\) vs \(1/4\)). The
proof breaks because contracting at a point of one walk translates the other walk to a walk started at
\(-S^{(1)}_j\), which is not a configuration of the class.

**Relation to known results.** \(\binom{n+1}{q}-R_q\) counts the \(q\)-sets of the \(n+1\) walk points cut off by an
affine hyperplane ("\(q\)-sets" in the sense of discrete geometry, here for an exchangeable walk). For \(n=d+1\),
\(R_q\) is the affine Radon type, and Theorem 6.4 reduces to Barysheva's Theorem 1.4 / Kabluchko–Panzo Theorem 3.17
(expectation level). For general \(n\), the top nontrivial information \(\sum_q\) is the deterministic count of
separable sets (Harding / Cover: \(2\sum_{j\le d}\binom{n}{j}\)). We did not find the full \(q\)-level expectation in the
literature (§7 and `LITERATURE.md`). The argument of §7 (Proposition 7.2 applied to \(\widehat S\), whose contractions are
bridges by Lemma 6.2) indicates that it is also implied by the known absorption theorems for several bridges; we
have written out and checked that second route only for the conic walk theorem, so for the affine theorem this
remark is a sketch.

---
## 7. Relation to the multidimensional arcsine law; explicit formula

**Known theorem (KVZ, *Bernoulli* 25 (2019) 3, Theorem 1.2).** For a (±Ex) walk in \(\mathbb R^d\) in general position,
\(n\ge d+1\), \(1\le k\le n\): \(\mathbb EM^{(d)}_{n,k}=\binom nk\frac{B(k,d-1)+B(k,d-3)+\cdots}{2^{k-1}k!}\), where
\(M^{(d)}_{n,k}=\#\{J:|J|=k,\ 0\notin\mathrm{conv}(S_j:j\in J)\}\) and \(\sum_jB(k,j)t^j=(t+1)(t+3)\cdots(t+2k-1)\). For \(d=1\),
\(M_{n,k}=\binom{N_+}k+\binom{N_-}k\), so these are factorial moments of the arcsine law.

**Lemma 7.1 (Euler identity in a cone) [PROVED].** Let \(T\) be in (GP) in \(V\), \(\dim V=m\ge1\), \(M\ge m\), and
\(\varnothing\ne J\subseteq[M]\). Let \(C_J=\{u\in V^*:u(T_j)>0\ (j\in J)\}\). Then
\[
\mathbf 1\{C_J\ne\varnothing\}=\sum_{F}(-1)^{|H_F|},
\]
the sum over the nonzero relatively open faces \(F\) of the arrangement \(\{T_i^\perp\}\) contained in \(C_J\), where
\(H_F=\{i:u(T_i)=0\text{ on }F\}\).

*Proof.* As \(M\ge m\) and the \(T_i\) span \(V\), every face is a pointed cone, so \(F\cap\mathbb S\) (unit sphere of any norm) is
an open cell of dimension \(\dim F-1=m-|H_F|-1\) (GP: \((T_h)_{h\in H_F}\) independent). If \(C_J\ne\varnothing\), it is an
open convex cone containing no line, so \(C_J\cap\mathbb S\) is homeomorphic to an open \((m-1)\)-ball, with compactly
supported Euler characteristic \((-1)^{m-1}\); it is the disjoint union of the cells \(F\cap\mathbb S\), \(F\subseteq C_J\)
(the sign conditions defining \(C_J\) are unions of faces). Additivity of \(\chi_c\) over this finite partition gives
\((-1)^{m-1}=\sum_F(-1)^{m-|H_F|-1}\). If \(C_J=\varnothing\) both sides vanish. ∎

**Proposition 7.2 (binomial moments of the level vector) [PROVED, NU; exact check].** Let \(S\) be in (GP) in
\(V\), \(\dim V=d\ge1\), \(N\ge d\). For every \(k\ge1\),
\[
\sum_{q}\binom qk\,Y_q(S)=\sum_{h=0}^{d-1}\ \sum_{|H|=h}M_k(S/H),\qquad M_k(T):=\#\{J:|J|=k,\ 0\notin\mathrm{conv}(T_J)\},\tag{7.1}
\]
\(H\) ranging over subsets of \([N]\), \(J\) over subsets of \([N]\setminus H\), and \(S/H\) the contraction by \(\mathrm{span}(S_H)\).
Equivalently: *the number of regions of \(\{S_i^\perp\}\) inside the open cone \(C_J\) equals the number of flats
\(W_H=\{u:u(S_h)=0,\ h\in H\}\), \(|H|\le d-1\), meeting \(C_J\)* (Zaslavsky's count restricted to a convex cone).

*Proof.* \(\sum_q\binom qkY_q=\sum_{R}\binom{|P(R)|}k=\#\{(R,J):J\subseteq P(R)\}\) over regions \(R\) with positive set \(P(R)\)
(Theorem 1.3). Lemma 7.1 summed over \(J\), with faces grouped by \(H_F=H\) (the faces with zero set \(H\) are the regions
of \(S/H\), Lemma 2.1–2.2 iterated) gives \(M_k(S)=\sum_{|H|\le d-1}(-1)^{|H|}\sum_q\binom qkY_q(S/H)\), because
\(0\notin\mathrm{conv}(S_J)\iff C_J\ne\varnothing\). Apply this to every \(S/H\) (again in (GP), Proposition 1.6) and sum over
\(|H|=h\): \(m_k(h)=\sum_{h'\ge h}(-1)^{h'-h}\binom{h'}{h}w_k(h')\) with \(m_k(h)=\sum_{|H|=h}M_k(S/H)\),
\(w_k(h)=\sum_{|H|=h}\sum_q\binom qkY_q(S/H)\) (a set \(K\) of size \(h'\) arises from \(\binom{h'}h\) pairs \(H\subseteq K\)). Binomial
inversion gives \(w_k(h)=\sum_{h'\ge h}\binom{h'}hm_k(h')\); take \(h=0\). The equivalent form is the same count for a fixed
\(J\). ∎ Exact check: `certificates/out_zaslavsky_identity.txt` (all \(k\), \(d\le4\), \(N\le6\), 148 configurations).

**Theorem 7.3 (second proof and explicit formula) [COND on (A); PROVED, NU; exact check].** Under the hypotheses of
Theorem 4.2 with \(N\ge d\ge1\), for \(k\ge1\),
\[
\mathbb E\sum_q\binom qkY_q(S)=\sum_{h=0}^{d-1}\binom N{k+h}\gamma(k,h,d),\qquad
\gamma(k,h,d)=\binom{k+h}h-2\sum_{i\ge0}\,[t^{\,d-h+1+2i}\,x^k]\;\frac{\big((1-x)^{-t}-1\big)^h}{(tx)^h\,(1-x)^{(t+1)/2}},\tag{7.2}
\]
and \(\mathbb EY_q=\sum_{k\ge q}(-1)^{k-q}\binom kq\,\mathbb E\sum_{q'}\binom{q'}kY_{q'}\), with the \(k=0\) moment
\(2\sum_{j<d}\binom{N-1}j\). (Here \(\big((1-x)^{-t}-1\big)/t=\sum_{j\ge1}t^{j-1}(-\log(1-x))^j/j!\) is a power series in \(t,x\).)

*Proof.* Take expectations in (7.1). For \(|H|=h\), \(|J|=k\), \((S/H)_J=(S_{H\cup J})/H\). Fix the *pattern* \(w\in\{H,J\}^{h+k}\)
(the relative order of the elements of \(H\) and \(J\)); there are \(\binom N{h+k}\) pairs \((H,J)\) with a given pattern
(choose \(U=H\cup J\)). By Lemma 5.1 (with \(u=h+k\)), \(\mathbb E\sum_{(H,J)\text{ of pattern }w}\mathbf 1\{0\notin\mathrm{conv}((S_U)/H)\}
=\binom N{h+k}\mathbb P(0\notin\mathrm{conv}(S'/H_w))\) for a (±Ex) walk \(S'\) of \(h+k\) steps, \(H_w\) the \(H\)-positions of \(w\). By
Lemma 3.2 iterated, \(S'/H_w\) is a configuration of bridges with \(k_1,\dots,k_h\) points (the \(J\)'s before the first,
between consecutive \(H\)'s) and a walk with \(k_w\) points (after the last \(H\)), in dimension \(d-h\), and averaging
over the subgroup fixing the points of \(H_w\) (Step 2 of Theorem 4.1) makes its law invariant under the product group.
By (A), \(\mathbb P(0\in\mathrm{conv})=2\sum_{i\ge0}[t^{d-h+1+2i}]\prod_c\frac{(t+1)\cdots(t+k_c)}{(k_c+1)!}\cdot\frac{(t+1)(t+3)\cdots(t+2k_w-1)}{2^{k_w}k_w!}\).
Summing over the \(\binom{k+h}h\) compositions \((k_1,\dots,k_h,k_w)\) of \(k\) and using
\(\sum_n\frac{(t+1)\cdots(t+n)}{(n+1)!}x^n=\frac{(1-x)^{-t}-1}{tx}\), \(\sum_n\frac{(t+1)(t+3)\cdots(t+2n-1)}{2^nn!}x^n=(1-x)^{-(t+1)/2}\) gives (7.2). ∎

Exact check against the recursion of Theorem 4.1: `certificates/out_zaslavsky_formula.txt` (\(d\le4\), \(N\le7\), all
agree, both in the \((H,J)\)-sum form and in the compact form (7.2)). Sample values: \(\gamma(k,0,d)=1-a_{(\mathsf W_k)}(d)\);
\(d=2\): \(\gamma(\cdot,1,2)=2,\,23/12,\,11/6,\,563/320,\dots\)

**Consequences for the comparison with KVZ (question G).**

1. *KVZ ⇒ ?* Theorem 1.2 of KVZ (walks only) does **not** pointwise determine the level vector: in \(d=3\) there are
   configurations in general position with identical counts \(M_{N,k}\) for all \(k\) but different \((Z_q)\)
   (`certificates/out_kvz_pointwise.txt`: \(N=5\), \(Z=(0,1,4,4,1,0)\) vs \((0,0,5,5,0,0)\)). But by (7.1) the level vector
   **is** pointwise a linear function of the subset-absorption counts of all contractions \(S/H\), \(|H|\le d-1\)
   (consistently, no counterexample exists for those: `certificates/out_kvz_contractions.txt`). The expectations of
   the latter are given by the *joint* absorption theorem for bridges and walks (KVZ Adv. Math. 2017, Thm 2.1)
   and averaging. **Hence Theorem 4.2 is implied by KVZ Adv. Math. Theorem 2.1 via the elementary identity (7.1) and
   the averaging Lemmas 3.2, 5.1**; it is *not* implied by KVZ Bernoulli Theorem 1.2 alone in any pointwise-linear way.
2. *? ⇒ KVZ.* KVZ Theorem 1.2 is the top level \(q=u=k\) of Theorem 5.2 (Corollary 5.3). From Theorem 4.2 for the walk
   alone one gets only the \(h=0\) part of (7.1) mixed with contraction terms; the clean implication uses the cut-set
   version.
3. *Verdict.* Theorem 4.2 (and its mixed and cut-set versions) is **equivalent, modulo elementary identities, to the
   joint absorption theorem for walks and bridges**: (A) for all mixed types ⇒ all expected level counts (by (7.1)
   and averaging, or by the recursion of §4); conversely the top level of the mixed level-count theorem is (A).
   It is genuinely stronger than KVZ Bernoulli Theorem 1.2 for walks only (which is one linear functional of it).
   The statement in terms of level counts / sign-imbalanced topes, the recursion (4.1), and the explicit formula
   (7.2) were not found in the literature (`LITERATURE.md`), but the result should be presented as a consequence
   of, and a reformulation organised around, the KVZ absorption theorem — not as an independent universality
   phenomenon.

**Structure of the generating function [OBS / PROVED parts].** With \(\sum_q\mathbb EZ_qx^q=\sum_k\alpha_k(1+x)^{N-k}(1-x)^k\):
\(\alpha_k=0\) for odd \(k\) (PROVED, palindromy); \(2^N\alpha_0=2\sum_{j\le N-d-1}\binom{N-1}j\) (PROVED, Proposition 1.6);
\(2^N\alpha_k(N,d)=\sum_{c}\binom N{k+c}\beta(k,c,d)\) with \(N\)-independent \(\beta\) (OBS: `certificates/out_structure_check.txt`,
\(d\le4\), \(N\le11\); the analogous structure for the binomial moments, \(\sum_h\binom N{k+h}\gamma(k,h,d)\), is PROVED in (7.2));
\(\beta(k,c,d)=0\) for \(c\equiv d\pmod 2\) (OBS).
No closed product formula was found; the integer arrays \(2^NN!\,\mathbb EZ_q/2\) (e.g. \(16,384,736\); \(231,5867,15022\);
\(25,1925,7650\)) have no OEIS match (searched 2026-10). The coefficients are *not* type-A/B Stirling or Eulerian
numbers except at \(N=d+1\) (type-B Eulerian, Theorem C) and at the top level (the KVZ coefficients \(B(k,j)\), which are
the coefficients of the characteristic polynomial of the type-B arrangement, i.e. type-B Stirling-type numbers).

---
## 8. Theorem C (the baseline) — status and the no-ties audit

**Theorem C.** \(X_1,\dots,X_n\) (±Ex) in \(\mathbb R^{n-1}\) (\(n=d+1\)), \(S_1,\dots,S_n\) a.s. in (GP). Let \(g\) span \(\ker S\) and
\(\tau_{\rm lin}=\min(\#\{g_i>0\},\#\{g_i<0\})\). Then a.s. all \(g_i\ne0\), and
\(\mathbb P(\tau_{\rm lin}=k)=\eta_kB(n,k)/(2^nn!)\) (\(\eta_k=2\) for \(2k<n\), \(1\) for \(2k=n\)); more precisely, for any set \(\mathcal D\) of sign
vectors closed under global negation, \(\mathbb P(\mathrm{sign}\,g\in\mathcal D)=\#\{w\in B_n:\mathrm{ud}(w_1,\dots,w_n,0)\in\mathcal D\}/(2^nn!)\),
where \(\mathrm{ud}(a)_i=\mathrm{sign}(a_i-a_{i+1})\).

**Status (re-verified).**

| item | status | source / dictionary |
|---|---|---|
| \(\mathbb P(\tau_{\rm lin}=0)\) | KNOWN | \(=\mathbb P(0\in\mathrm{int\,conv}\,S)\) (Prop. 1.5) \(=1/(2^d(d+1)!)\): KVZ GAFA 2017 Thm 2.3 / Godland–Kabluchko (1.5) with \(n=d+1\) |
| law of \(\tau_{\rm lin}\) | KNOWN | Kabluchko–Panzo (DCG 2026, arXiv 2501.16166v2) **Thm 4.5**: walk in \(\mathbb R^{d'+1}\) with \(d'+2\) steps, type \(T^{d'}_m\) \(\leftrightarrow\) \(\tau_{\rm lin}=m+1\), \(d'=d-1\); same hypotheses |
| full labelled sign pattern of \(g\) (up to global sign) | KNOWN-implicit | Godland–Kabluchko SPA 2022 **Cor. 4.5** (face probabilities of \(\mathrm{pos}(S_F)\)) + Möbius inversion over \(\{K: g\ \text{constant on}\ K\}\) (REPORT.md §2.3; checked exactly for \(d\le4\)) |
| probability of a fixed labelled bipartition | KNOWN-implicit | same (it is one value of the labelled law) |
| descent description via a uniform signed permutation | not found in the literature | `Conic.lean`, `Generalizations.lean` (Lean, earlier stage) |
| proof by 1-dim Gale duality + Abel summation + \(B_n\)-averaging | not found for the conic problem | Barysheva's affine proof, transcribed; Kabluchko–Panzo prove Thm 4.5 by face numbers |
| weaker symmetry | (Ex) alone is **false** | \(d=1,n=2\), positive increments: \(\tau_{\rm lin}=1\) a.s. vs formula \(\mathbb P(\tau=0)=1/4\) |

So the distributional content of Theorem C is known; only the explicit signed-descent representation and the
Gale/Abel/averaging proof may be new, and the latter is a routine transcription of Barysheva's method.

**No-ties audit [PROVED].** Write \(G_m=\sum_{i\ge m}g_i\) (so \(\sum_mG_mX_m=0\) spans \(\ker X\)). Let \(F\) be the null event that
some \(w\cdot X\) violates (GP). Off \(F\):
* \(G_m\ne0\) needs only (Ex)+(GP): if \(G_m=0\), the \(d\) increments \(\{X_j\}_{j\ne m}\) are dependent; in the ordering putting
  \(X_m\) last they span \(\mathrm{span}(S'_1,\dots,S'_d)\), which is \(d\)-dimensional by (GP). Contradiction.
* \(G_i\ne G_j\) (\(i\ne j\)) needs only (Ex)+(GP): \(G_i=G_j\) makes \(\{X_i+X_j\}\cup\{X_m\}_{m\ne i,j}\) dependent; order the increments
  with \(X_i,X_j\) last: these \(d\) vectors span \(\mathrm{span}(S'_1,\dots,S'_{n-2},S'_n)\), \(d\)-dimensional by (GP).
* \(G_i\ne-G_j\) needs a sign change: \(G_i=-G_j\) makes \(\{X_i-X_j\}\cup\{X_m\}\) dependent; apply the previous argument to the
  ordering with \(X_j\) replaced by \(-X_j\), which requires (±Ex). **Sharpness:** under (Ex)+(GP) alone the tie
  \(G_i=-G_j\) can occur a.s.: \(d=1\), \(n=2\), \(X_1=X_2=1\): \(S=(1,2)\) satisfies (GP), \(g=(2,-1)\), \(G=(1,-1)\).

The earlier report's claim is confirmed.

---

## 9. Exact counterexamples (limits of universality)

All data are integer increment lists; an exchangeable (resp. sign-exchangeable) law is the uniform law on the
\(\mathfrak S_N\)- (resp. \(B_N\)-) orbit; every orbit member is checked to be in general position with exact
determinants; topes are decided exactly by the oriented-matroid orthogonality test (cocircuit signs from integer
determinants), cross-checked against an independent region enumeration (Theorem 1.3 / Gordan). Script:
`certificates/counterexamples.py`, output `certificates/out_counterexamples.txt`. Those marked **[LEAN]** are also
kernel-checked (`RequestProject/LevelCounts/Counterexamples.lean`, see `FORMALIZATION.md`).

* **CE1 (fixed bipartition, \(N>d+1\)) [LEAN].** \(d=2,N=4\), (±Ex). Event \(\mathrm{pos}(S_1)\cap\mathrm{pos}(S_2,S_3,S_4)\ne\{0\}\).
  Increments \((-5,9),(-7,-1),(-6,6),(5,6)\): probability \(1/3\); increments \((-2,5),(6,8),(-2,2),(-2,-2)\): \(5/16\).
* **CE2 (law of \((Z_q)_q\)).** \(d=3,N=5\), (±Ex): the joint laws of \((Z_0,\dots,Z_5)\) for the two lists in
  `counterexamples.py` (`LISTS_3_5`) differ (e.g. the frequency of one level vector is \(794\) vs \(834\) out of \(3840\)),
  although all expectations agree (Theorem 4.2).
* **CE3 (sign symmetry needed) [LEAN].** \(d=2,N=4\), (Ex) only: \(\mathbb EZ_4=\mathbb P(0\in\mathrm{int\,conv})=1/4,\ 0,\ 1/12\) for three lists;
  under (±Ex) all give \(1/12\).
* **CE4 (fixed-support circuits) [LEAN].** \(d=2,N=4\), (±Ex), support \(\{1,2,4\}\): \(\mathbb P(\text{positive circuit})=1/24\)
  vs \(1/16\) (sums over the four supports agree: \(4\cdot1/24\), Corollary 5.4).
* **CE5 (several affine walks).** Planar, (Ex) within each walk: lengths \((3,2)\) with common origin, \(\mathbb ER_1=3/2\) vs \(1\);
  lengths \((2,2)\) without origin, \(\mathbb ER_1=1/2\) vs \(1/4\). (Earlier Lean: `RequestProject/Counterexamples.lean`,
  `twoWalks_not_universal`, for a related affine statistic.)
* **CE6 (full combinatorial type beyond the 1-dim Gale dual).** \(d=2,N=4\) (Gale dual of dimension 2): the labelled tope
  set of \(\ker S\) has 21 resp. 18 distinct values over the two orbits, and one tope set has probability \(1/48\) vs \(5/96\).
* **CE7 (general position needed in Theorems 1.3–1.4).** \(T=((1,0),(1,0),(0,1))\) and \(T=((1,0),(-1,0),(0,1),(0,-1))\).
* **CE8 (law of the number of positive circuits).** \(d=2,N=5\), (±Ex): \(\mathbb P(C_0=3,4,5)\cdot3840=270,170,22\) vs
  \(278,154,30\), same mean \(5/12\).
* **CE9 (level vector not determined by KVZ counts).** `out_kvz_pointwise.txt` (§7).
* **Tverberg-type (§10):** the expected number of conic 3-partitions of \(S_1..S_5\) in \(\mathbb R^2\) ((±Ex)) is \(1171/640\) vs
  \(3517/1920\); of affine 3-partitions of \(S_0..S_6\) ((Ex)) \(197/45\) vs \(797/180\) — exact, by exact rational
  feasibility of the defining linear systems (`certificates/out_tverberg_exact.txt`).

The pattern: what is universal is exactly what can be written as an orbit sum of a quantity satisfying a
closed recursion with universal boundary data (level counts, cut-set level counts, circuit-type counts summed over
supports); fixed labelled events, full laws, and multi-part Tverberg counts are not.

---

## 10. Conic Tverberg partitions and Roudneff's theorem

**Roudneff's Theorem 2.1 (dictionary; Roudneff, *European J. Combin.* 22 (2001) 733–743, read in full).** For an
affine flat \(L\) and a finite set \(X\) (not both empty), Roudneff's \([L,X)\) is the set of barycentres
\(\sum_{z\in L\cup X}\alpha_zz\) with \(\sum\alpha_z=1\) and \(\alpha_x\ge0\) for \(x\in X\) only — coefficients on points of \(L\) are
**unrestricted**. In modern notation, for \(L\ne\varnothing\): \([L,X)=L+\mathrm{pos}(X-a)\) for any \(a\in L\) (if \(1-\sum_x\alpha_x\ne0\) the
\(L\)-part is a point of \(L\) scaled by it; if it is \(0\), the \(L\)-part is a direction vector of \(L\)). Special cases:
\([\varnothing,X)=\mathrm{conv}X\); \([L,\varnothing)=L\); \([\{a\},\{b\})\) is the half-line from \(a\) through \(b\); \([\{a\},X)=a+\mathrm{pos}(X-a)\),
the cone with apex \(a\); for a linear subspace \(L\), \([L,X)=L+\mathrm{pos}(X)\). Flats are *in general position at infinity*
if every subfamily that meets at infinity also meets in \(\mathbb R^d\). **Theorem 2.1:** if \(L_1..L_m\) are in general position at
infinity and \(|X|+\sum_i(1+\dim L_i)\ge(m-1)(d+1)+1\) (\(\dim\varnothing=-1\)), some partition has \(\bigcap_i[L_i,X_i)\ne\varnothing\).
*Specializations.* \(L_i=\varnothing\): Tverberg's theorem. \(L_i=\{0\}\) for all \(i\) (points are trivially in general position at
infinity): \([\{0\},X_i)=\mathrm{pos}(X_i)\), the threshold becomes \(|X|\ge(m-1)d\), and the conclusion
\(\bigcap\mathrm{pos}(X_i)\ne\varnothing\) is **vacuous** (every positive hull contains \(0\)); it says nothing about a nonzero common
vector. Linear subspaces \(L_i\): \(\bigcap(L_i+\mathrm{pos}X_i)\ne\varnothing\), again trivially containing \(0\). Nontrivial affine flats
(\(0\notin L_i\)) give "Tverberg with cones whose apex sets are flats", a genuinely affine statement.
**Neither Theorem 2.1, nor Lemmas 3.1/3.3, Theorems 4.1, 5.1, 5.3 of Part I, nor any citing work found
(`literature/cites_roudneff_kvz.txt`: 18 citing items of Part I, 6 of Part II, titles/abstracts screened; Perles–Sigron and
Bárány–Soberón read where accessible) asserts \(\bigcap_a\mathrm{pos}(S_{I_a})\ne\{0\}\) as such.** The closest consequences are:
(i) *Roudneff Part I, Theorem 4.1* (Reay/Tverberg): every set of \(2(m-1)d+2\) points of \(\mathbb R^d\) is \((m,1)\)-divisible, i.e.
some partition has \(\dim\bigcap_i\mathrm{conv}X_i\ge1\). A segment contains a nonzero point, which lies in every \(\mathrm{pos}(X_i)\). Hence
**any \(N\ge2(r-1)d+2\) distinct vectors admit a conic Tverberg \(r\)-partition, with no general-position hypothesis**; for \(d=1\)
this is sharp (\(r-1\) positive numbers, \(r-1\) negative numbers and \(0\)). (ii) *Theorem 5.1* (\(m=3,4\)): \((m-1)(d+1)+2\) points in
affine general position are \((m,1)\)-divisible, giving a conic partition at one more than the threshold of Theorem 10.1 and
under a different (affine) general-position hypothesis. A projective change of the hyperplane at infinity (as in
Roudneff's proof) converts nonzero rays into points only for *pointed* configurations (all vectors in an open
half-space), see (c) below.

**Theorem 10.1 (deterministic conic Tverberg number) [PROVED; elementary consequence of Tverberg; NU (likely
folklore)].** Let \(d\ge1\), \(r\ge1\).
(a) If \(N\ge(r-1)(d+1)+1\) and \(S_1,\dots,S_N\in\mathbb R^d\) are in (GP), there is a partition \([N]=I_1\sqcup\dots\sqcup I_r\) with
\(\bigcap_a\mathrm{pos}(S_{I_a})\ne\{0\}\).
(b) There are \((r-1)(d+1)\) vectors in (GP) with no such partition.
(c) If moreover all \(S_i\) lie in an open half-space, the threshold is \((r-1)d+1\) (exact).

*Proof.* (a) Let \(N_0=(r-1)(d+1)+1\). Tverberg's theorem for \(S_1,\dots,S_{N_0}\) gives a partition into \(r\) parts with a common
point \(p\in\bigcap\mathrm{conv}(S_{I_a})\subseteq\bigcap\mathrm{pos}(S_{I_a})\). If \(p=0\), then \(0\in\mathrm{conv}(S_{I_a})\) for each \(a\); a convex combination of at most
\(d\) vectors that are linearly independent (GP) is nonzero, so \(|I_a|\ge d+1\) for all \(a\) and \(N_0\ge r(d+1)\): contradiction.
So \(p\ne0\); put the remaining \(N-N_0\) vectors into any parts (cones only grow).
(b) Let \(v_0,\dots,v_d\) be the vertices of a simplex with centroid \(0\) (any \(d\) of them a basis, \(\sum v_i=0\)), and let \(A\) consist
of \(r-1\) copies of each \(v_i\). *No partition of \(A\) works:* the cones \(\mathrm{pos}(v_D)\), \(D\subsetneq\{0..d\}\), form a complete simplicial
fan, so a nonzero \(y\) lies in the relative interior of \(\mathrm{pos}(v_{D(y)})\) for a unique nonempty proper \(D(y)\), and \(y\in\mathrm{pos}(v_D)\)
iff \(D\supseteq D(y)\) (also when \(D\) is everything). If \(y\ne0\) lies in every \(\mathrm{pos}(I_a)\), each block contains a copy of each
\(v_i\), \(i\in D(y)\ne\varnothing\): \(r\) copies, but only \(r-1\) exist. *Persistence:* suppose perturbations \(A^{(\varepsilon)}\to A\) admit
partitions with unit common vectors \(y_\varepsilon\). Passing to a subsequence, the partition is fixed and \(y_\varepsilon\to y\), \(|y|=1\).
Write \(y_\varepsilon=\sum_{j\in I_a}\lambda^{(\varepsilon)}_jw^{(\varepsilon)}_j\), \(\lambda\ge0\). If \(I_a\) contains copies of all \(d+1\) directions,
\(\mathrm{pos}(I_a)=\mathbb R^d\ni y\) in the limit configuration. Otherwise its limit directions are linearly independent, so the
\(\lambda^{(\varepsilon)}\) stay bounded (else normalizing by \(\max\lambda\) gives a nontrivial nonnegative combination of independent
directions equal to \(0\)), and a further subsequence gives \(y\in\mathrm{pos}(I_a)\) for the limit configuration. Thus \(y\ne0\) is
common to all blocks of a partition of \(A\): contradiction. Hence all sufficiently small perturbations have no
partition, and since (GP) is open and dense, some small perturbation is in (GP).
(c) Let \(u(S_i)>0\) for all \(i\); central projection \(S_i\mapsto S_i/u(S_i)\) onto \(\{u=1\}\cong\mathbb R^{d-1}\) maps nonzero vectors of
\(\mathrm{pos}(S_I)\) to points of \(\mathrm{conv}\) of the projections and conversely; (GP) in \(\mathbb R^d\) is affine GP of the projections.
Tverberg's number in \(\mathbb R^{d-1}\) is \((r-1)d+1\), and it is tight for points in general position. ∎

*Relation to literature.* (a)–(c) are not Roudneff's Theorem 2.1 (whose \(L_i=\{0\}\) case is vacuous, see above). (a) is a
two-line corollary of Tverberg's theorem (= Roudneff 2.1 with all \(L_i=\varnothing\)) plus the zero-exclusion step; without (GP),
Roudneff's Theorem 4.1 gives the weaker threshold \(2(r-1)d+2\). (b) is the standard multiplicity construction. We found no
explicit statement of (a)–(c), so the result should be presented as a remark ("folklore-level"), not as a main theorem.
**Lean:** the zero-exclusion step (`card_gt_of_zero_mem`), (a) conditional on Tverberg's theorem as an explicit hypothesis
(`conic_tverberg_of_tverberg`), and (a) for \(r=2\) unconditionally via Mathlib's Radon theorem (`conic_radon`) are
kernel-checked in `RequestProject/LevelCounts/ConicTverberg.lean`; (b) and (c) are not formalized.

**Proposition 10.2 (Sarkaria lift) [PROVED; LEAN].** Fix a colouring \(a:[N]\to[r]\) with classes \(I_1..I_r\), and
\(u_1,\dots,u_r\in\mathbb R^{r-1}\) whose only linear relation is \(\sum u_a=0\). For \(\lambda\in\mathbb R^N\):
\[
\sum_i\lambda_i\,S_i\otimes u_{a(i)}=0\iff y_1=\dots=y_r,\qquad y_a:=\sum_{i\in I_a}\lambda_iS_i .
\]
*Proof.* \(\sum_i\lambda_iS_i\otimes u_{a(i)}=\sum_ay_a\otimes u_a=\sum_{a<r}(y_a-y_r)\otimes u_a\), and \(u_1,\dots,u_{r-1}\) are a basis, so the
tensor vanishes iff \(y_a=y_r\) for all \(a\). ∎ (Lean: `sarkaria_lift`, with \(u_a=e_a\) for \(a<r\) and \(u_r=-\sum e_a\), the lifted
vector \(S_i\otimes u_{a(i)}\) being represented as an element of \(V^{r-1}\cong V\otimes\mathbb R^{r-1}\); the degenerate alternative (ii)
below is `sarkaria_zero_case`.)

*Distinctions.* A nonnegative nonzero lifted dependence \(\lambda\) gives either (i) a genuine common nonzero vector
\(y\in\bigcap\mathrm{pos}(S_{I_a})\), or (ii) \(y=0\): each class with \(\lambda|_{I_a}\ne0\) is then positively dependent, so under (GP) has at least
\(d+1\) elements. *Algebraic threshold* \(N_{\rm alg}=(r-1)d+1\): the lifted vectors live in \(\mathbb R^{d(r-1)}\), so for
\(N\ge N_{\rm alg}\) the dependence space is at least one-dimensional; this says nothing about positivity. *Existence
threshold* \(N_{\rm exist}=(r-1)(d+1)+1\) (Theorem 10.1). *Uniqueness* must be separated into: uniqueness of the coefficient
ray \(\lambda\) for a fixed colouring; uniqueness of the common geometric ray \(\mathbb Ry\); uniqueness of the colouring. Exact
example (`certificates/out_tverberg_exact.txt`, item 6): \(d=4,r=3,N=9=N_{\rm alg}\), nine integer vectors in (GP); for one colouring the
dependence space of the lifted vectors has dimension 2 and contains two strictly positive solutions with
non-proportional common vectors \(y=(40,52,0,0)\) and \((30,41,0,0)\) — so for \(N=N_{\rm alg}\) neither the coefficient ray nor the
common ray need be unique even under (GP) of the \(S_i\) (the lift itself is not in general position).

**Probabilistic Tverberg questions [exact; negative].** The expected number of conic Tverberg 3-partitions of
\(S_1..S_5\in\mathbb R^2\) under (±Ex) and of affine 3-partitions of \(S_0..S_6\in\mathbb R^2\) under (Ex) are not distribution-free (§9).
We did not find a universal averaged Tverberg statistic; per the protocol no further Tverberg theorem is proposed.
