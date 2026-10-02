# Conjecture 3 (the cyclic-collision formula): statement, corrections and proof

**Where the statement comes from.** The file `wtf.pdf` cited in the request was not among the
uploaded files. Conjecture 3 is therefore taken from §2.3 of `RESEARCH_MAP.md` and from the
definitions in the request; those two sources agree. "Theorem 2.17" means Theorem 2.17 of
`random_permutations_lectures_1-4.pdf`. "Theorem 1.4", "Lemma 4.2", "Lemma 4.3" and
"Lemma 4.4" refer to `sylvester_radon.pdf`.

**Verdict in one paragraph.** Every identity in Conjecture 3 is **true**. Four things needed
correcting:

- **Genericity.** The right assumption is that *every reordering* of the steps puts the walk
  points in general position. I call this (G); §2 restates it in three equivalent ways.
  General position of one ordering, even together with "no ties in the Gale diagram", is
  **not** enough for the counting statements (smallest counterexample: Example 4.4,
  $N=5$, $d=2$). For exchangeable steps, general position of the given ordering almost
  surely already implies (G), so no extra probabilistic hypothesis is needed.
- **The "interior" form needs no genericity at all.** If $N_1$ is replaced by the number of
  walk points lying in the *interior* of the hull of the other points, the pointwise identity
  and the counting formulas hold for every spanning closed walk.
- **Conditioning.** "Conditioning on $P$" must be replaced by conditioning on the
  permutation-invariant $\sigma$-field $\mathcal I$, or on any intermediate $\sigma$-field.
  This needs no regular conditional distributions, and repeated steps or symmetries cause no
  trouble.
- **The role of Theorem 2.17.** Applied to an affine slice $Q_u$ of the dependency space,
  Theorem 2.17 gives $\#\{\pi:K_\pi\cap Q_u\ne\emptyset\}=\sum_{k\ge d+2}{N\brack k}$. That
  number is **not** half the number of chambers (already false for $N=4$, $d=1$: $2\cdot7=14$
  but $|\Omega|=12$). The correct relation is the recursion of Lemma 7.3, and it does give
  $|\Omega|=2\sum_{j\ge0}{N\brack d+2+2j}$.

For $N=d+3$ the identity $T_2(P)=2s(P)$ holds exactly as conjectured, with $s(P)$ the number
of unordered strongly separable splits. The factor $2$ comes from the two half-periods of the
circular sequence, which are exchanged by reversal. One side remark: for $N=4$ (that is,
$d=1$) every generic $P$ has $s(P)=3$ (Corollary 9.1). So a bound $s\le 2$, as in
Conjecture 4, cannot hold for 4-point Gale diagrams. Conjecture 4 itself is not treated here.

**Machine-checked part.** `RequestProject/CyclicCollision.lean` builds with no `sorry` and uses
only the standard axioms. It contains:
- the orbit-counting core of §5 for an *arbitrary* set $\Omega\subseteq\mathrm{Sym}(N)$
  (`sum_rotCount`, `sum_rotCount_sq`, `sum_fun_rotCount_eq`, `sum_rotCount_stab`,
  `sum_rotCount_choose_two_stab`);
- the converse half of the Gale–polygon lemma (`gale_converse`,
  `eq_const_of_cyclic_diff_zero`); the forward half is `ChamberEulerian.gale_identity`, from
  the earlier session;
- the "signed dependence $\Rightarrow$ convex combination" step of §4
  (`mem_convexHull_of_signed_dependence`).

Everything else is proved below in prose.

---

## 1. Corrected theorem statement

Throughout, $N\ge d+2$ and $d\ge1$. Here $a=(a_1,\dots,a_N)\in(\mathbb R^d)^N$ with
$\sum_i a_i=0$, and the $a_i$ span $\mathbb R^d$. For a permutation $\pi\in\mathrm{Sym}(N)$,
the reordered closed walk has the points

$$s^\pi_k=a_{\pi(1)}+\dots+a_{\pi(k)},\qquad k=1,\dots,N,\qquad s^\pi_N=0 .$$

The remaining notation ($\widetilde L$, $P$, $\Omega$, $\rho$, $\mathcal C_N$, $q_P$,
$\kappa$, $T_r$, (G), $s(P)$) is defined in §2.

**Theorem A (deterministic).**

1. *(Nonvertex lemma; no genericity.)* For every $\pi$ and every $i\in\mathbb Z/N$,
   $$s^\pi_i\in\operatorname{int}\operatorname{conv}\{s^\pi_j:j\ne i\}\iff \pi\circ\rho^{\,i}\in\Omega(P).$$
   So, for every circular class $c$,
   $N_1^{\rm int}(c)=q_P(c)$, where $N_1^{\rm int}(c)$ is the number of points of the walk of
   $c$ that are interior to the hull of the other points.
2. *(Interior versus nonvertex.)* If the points of the walk of $c$ are in general affine
   position, then $N_1(c)=N_1^{\rm int}(c)=q_P(c)$. Without general position this can fail.
3. *(Circular-word counting; no genericity for $N_1^{\rm int}$, (G) for $N_1$.)*
   $$\frac1{(N-1)!}\sum_{c\in\mathcal C_N}\binom{N_1^{\rm int}(c)}{r}=\frac{T_r(P)}{(N-1)!},\qquad
   \frac{\#\{c:N_1^{\rm int}(c)=0\}}{(N-1)!}=1-\frac{\kappa(P)}{(N-1)!}.$$
   The same holds with $N_1$ in place of $N_1^{\rm int}$ under (G).
4. *(Stirling layer; under (G).)* $T_1(P)=|\Omega(P)|=2\sum_{j\ge0}{N\brack d+2+2j}$.
5. *(Rank two; under (G) and $N=d+3$.)* $T_2(P)=2s(P)$, $T_r(P)=0$ for $r\ge3$, and
   $\kappa(P)=N(N-1)-2s(P)$.

**Theorem B (exchangeable walks and bridges).** Let $X=(X_1,\dots,X_N)$ be either

- an *exchangeable bridge* ($X\circ\sigma\overset d=X$ for all $\sigma\in\mathrm{Sym}(N)$ and
  $\sum X_i=0$ a.s.), or
- an *ordinary walk*: $X=(Y_1,\dots,Y_{N-1},-\sum_iY_i)$ with $(Y_i)$ exchangeable, whose
  points are $S_0=0,S_1,\dots,S_{N-1}$.

Assume that the $N$ points are almost surely in general affine position. Let $\mathcal I$ be
the $\sigma$-field of events $\{X\in B\}$ with $B$ a Borel set invariant under the relevant
group $G$: $G=\mathrm{Sym}(N)$ for bridges, and $G=\mathrm{Stab}(N)$, the permutations fixing
the closing position, for walks. Then, almost surely,

$$\mathbb E\Bigl[\tbinom{N_1}{r}\Bigm|\mathcal I\Bigr]=\frac{T_r(P)}{(N-1)!},\qquad
\mathbb P(N_1=0\mid\mathcal I)=1-\frac{\kappa(P)}{(N-1)!},$$

and hence $\mathbb E\binom{N_1}{r}=\mathbb E T_r(P)/(N-1)!$ and
$\mathbb P(\text{convex position})=1-\mathbb E\kappa(P)/(N-1)!$. In particular
$\mathbb E N_1=2\sum_{j\ge0}{N\brack d+2+2j}/(N-1)!$ is distribution-free.

For $N=d+3$:

$$\mathbb P(N_1=2)=\frac{2\,\mathbb E s(P)}{(N-1)!},\qquad
\mathbb P(N_1=1)=\frac{N}{(N-2)!}-\frac{4\,\mathbb E s(P)}{(N-1)!},\qquad
\mathbb P(N_1=0)=1-\frac{N}{(N-2)!}+\frac{2\,\mathbb E s(P)}{(N-1)!}.$$

---

## 2. Precise assumptions and definitions

**Dependency space and Gale diagram.** Let
$\widetilde L=\{t\in\mathbb R^N:\sum_it_ia_i=0\}$. The map $t\mapsto\sum t_ia_i$ is onto
$\mathbb R^d$ because the $a_i$ span, so $\dim\widetilde L=N-d$. Also
$\mathbf 1\in\widetilde L$ because $\sum a_i=0$. Put $m=N-d-1$.

An **affine Gale diagram** is a tuple $P=(p_1,\dots,p_N)$ in $\mathbb R^m$ such that

$$\widetilde L=\{(\langle u,p_i\rangle+c)_{i=1}^N:\ u\in\mathbb R^m,\ c\in\mathbb R\}.$$

One exists: choose a basis $\mathbf 1,v^1,\dots,v^m$ of $\widetilde L$ and put
$p_i=(v^1_i,\dots,v^m_i)$. In that case $(u,c)\mapsto t$ is a linear bijection. Any two
Gale diagrams differ by an invertible affine map of $\mathbb R^m$.

**Projection orders.**

$$\Omega(P)=\{\pi\in\mathrm{Sym}(N):\exists u,\ \langle u,p_{\pi(1)}\rangle>\dots>\langle u,p_{\pi(N)}\rangle\}
=\{\pi:\ C_\pi\cap\widetilde L\neq\emptyset\},$$

where $C_\pi=\{t:t_{\pi(1)}>\dots>t_{\pi(N)}\}$ is the open Weyl chamber. The two
descriptions agree because adding $c\mathbf 1$ does not change the order. So
$\Omega=\Omega(\widetilde L)$ is intrinsic: it does not depend on the choice of $P$. An order
and its reverse are counted separately.

**Circular classes.** Let $\rho\in\mathrm{Sym}(N)$ be $\rho(k)=k+1$ (mod $N$), so that
$(\pi\circ\rho^i)(k)=\pi(k+i)$. As a word, $\pi\circ\rho^i$ is $\pi$ cut after position $i$:
$$\pi\circ\rho^i=\bigl(\pi(i+1),\dots,\pi(N),\pi(1),\dots,\pi(i)\bigr).$$
$\mathcal C_N$ is the set of left cosets $c=\pi\langle\rho\rangle$. Right multiplication by
$\langle\rho\rangle$ is free, so each class has exactly $N$ elements and
$|\mathcal C_N|=(N-1)!$. Define
$$q_P(c)=|c\cap\Omega|,\qquad\kappa(P)=\#\{c:q_P(c)>0\},\qquad T_r(P)=\sum_{c\in\mathcal C_N}\binom{q_P(c)}{r}.$$

**The walk of a circular class.** For $\pi\in c$ and $0\le i<N$, using $\sum a=0$,

$$s^{\pi\circ\rho^i}_k=s^\pi_{i+k}-s^\pi_i\qquad(\text{indices mod }N,\ s^\pi_0:=s^\pi_N=0). \tag{2.1}$$

Check: for $i+k\le N$ both sides equal $a_{\pi(i+1)}+\dots+a_{\pi(i+k)}$. For $i+k>N$ the
left side is $(-s^\pi_i)+s^\pi_{i+k-N}$, because $a_{\pi(i+1)}+\dots+a_{\pi(N)}=-s^\pi_i$.
So rotating the word translates the point configuration by $-s^\pi_i$ and shifts the indices.
Hence every translation-invariant statistic depends only on $c$: $N_1(c)$,
$N_1^{\rm int}(c)$, convex position, and general position.

**Vertices.** For a finite indexed family $(s_j)$, the point $s_i$ is a *vertex* if
$s_i\notin\operatorname{conv}\{s_j:j\neq i\}$. $N_1$ counts the indices that are not vertices,
and $N_1^{\rm int}$ counts the indices with
$s_i\in\operatorname{int}\operatorname{conv}\{s_j:j\ne i\}$. Clearly $N_1^{\rm int}\le N_1$.

**Genericity conditions.** All of them are listed separately here, and the text never
silently identifies them.

- **(GP$_\pi$)** The points $s^\pi_1,\dots,s^\pi_N$ are in general affine position: any $d+1$
  of them are affinely independent.
- **(NT)** The Gale points $p_1,\dots,p_N$ are pairwise distinct ("no ties in generic
  projections").
- **(G)** (GP$_\pi$) holds for **every** $\pi\in\mathrm{Sym}(N)$.
- **(Simple)** (only for $m=2$) No three $p_i$ are collinear and no two connecting lines
  $p_ip_j$, $p_kp_l$ (with $\{i,j\}\ne\{k,l\}$) are parallel. Equivalently, the
  Goodman–Pollack circular sequence of $P$ is *simple*: every move swaps exactly two
  elements, and moves occur at distinct times.

For a set partition $B$ of $[N]$ write $V_B=\{t:t\text{ constant on blocks of }B\}$
($\dim V_B=\#B$) and $a_\beta=\sum_{i\in\beta}a_i$.

**Lemma 2.1 (equivalent forms of (G)).** The following are equivalent:

- (a) (G);
- (b) for every partition $B$ of $[N]$ into exactly $d+1$ blocks, the block sums
  $(a_\beta)_{\beta\in B}$ span $\mathbb R^d$;
- (c) $\dim(V_B\cap\widetilde L)=\max(\#B-d,1)$ for every set partition $B$.

Moreover (G) implies (NT), and if $m=2$ (that is, $N=d+3$) then (G) $\iff$ (Simple). If
$N=d+2$ then (G) $\iff$ (NT).

*Proof.* (a)$\Rightarrow$(b). List the blocks $\beta_1,\dots,\beta_{d+1}$ consecutively in a
word $\pi$, and let $k_j=|\beta_1|+\dots+|\beta_j|$. By (GP$_\pi$) the $d+1$ points
$0=s^\pi_N,s^\pi_{k_1},\dots,s^\pi_{k_d}$ are affinely independent. So the vectors
$s^\pi_{k_j}=a_{\beta_1}+\dots+a_{\beta_j}$, $j\le d$, are linearly independent. By
unitriangularity, so are $a_{\beta_1},\dots,a_{\beta_d}$.

(b)$\Rightarrow$(a). Take $d+1$ points of the walk of $\pi$. By (2.1) we may rotate so that
one of them is $s_N=0$ and the others are $s_{k_1},\dots,s_{k_d}$ with $0<k_1<\dots<k_d<N$.
Their affine independence is the linear independence of the cumulative sums of the
consecutive blocks $\beta_j=\{\pi(k_{j-1}+1),\dots,\pi(k_j)\}$, $j\le d$ (with $k_0=0$). It
is therefore equivalent to the independence of $a_{\beta_1},\dots,a_{\beta_d}$. Together with
$\beta_{d+1}$, the rest of the word, these blocks form a partition into $d+1$ blocks. The
$d+1$ block sums add up to $0$ and span $\mathbb R^d$, so their only linear relation is the
all-ones relation, and any $d$ of them form a basis.

(b)$\iff$(c). We have $V_B\cap\widetilde L=\{(t_\beta):\sum_\beta t_\beta a_\beta=0\}$, of
dimension $\#B-\operatorname{rank}(a_\beta)$, and $\operatorname{rank}\le\min(d,\#B-1)$ since
$\sum_\beta a_\beta=0$. So (c) says that the rank is $\min(d,\#B-1)$ for all $B$, and (b) is
the case $\#B=d+1$. Conversely, assume (b). If $\#B\ge d+1$, coarsen $B$ to $d+1$ blocks; the
span only shrinks under coarsening, so the rank is $d$. If $\#B\le d+1$, refine $B$ to
$d+1$ blocks (possible since $N\ge d+1$). The $d+1$ fine block sums have the all-ones vector
as their only relation, so the $\#B$ coarse sums (sums over groups) have only the all-ones
relation, and the rank is $\#B-1$.

(G)$\Rightarrow$(NT). Let $B$ merge only $\{i,j\}$, so $\#B=N-1$. By (c),
$\dim(V_B\cap\widetilde L)=N-1-d<\dim\widetilde L$. So $\widetilde L\not\subseteq\{t_i=t_j\}$,
that is, $p_i\ne p_j$.

For $N=d+3$, (b) concerns partitions into $d+1=N-2$ blocks. Those are either one 3-block
$\{i,j,k\}$ or two 2-blocks $\{i,j\},\{k,l\}$. By (c) the condition reads
$V_B\cap\widetilde L=\mathbb R\mathbf 1$. In Gale terms this says: no $u\ne0$ has
$\langle u,p_i\rangle=\langle u,p_j\rangle=\langle u,p_k\rangle$, i.e. no collinear triple;
and no $u\neq0$ is orthogonal to both $p_i-p_j$ and $p_k-p_l$, i.e. no parallel connecting
lines. Together with (NT) this is (Simple). For $N=d+2$ the partitions into $d+1$ blocks merge
one pair, and the same computation gives (NT). $\square$

**Remark 2.2.** (G) is strictly stronger than (GP$_{\rm id}$)+(NT). See Example 4.4: there
$N=5$, $d=2$, the given ordering is in general position, the $p_i$ are distinct, three of
them are collinear, and $|\Omega|=16\neq20$. For $N=d+2$, Barysheva's trapezoid (§4.2 of
`sylvester_radon.pdf`) shows that (GP$_{\rm id}$) alone does not give (NT).

---

## 3. The Gale–polygon lemma

Let $D:\mathbb R^N\to\mathbb R^N$, $(Dt)_i=t_i-t_{i+1}$, indices mod $N$. Let
$\mathrm{Dep}=\{\lambda\in\mathbb R^N:\sum\lambda_i=0,\ \sum\lambda_is_i=0\}$ be the space of
affine dependences of $s_1,\dots,s_N$ (here $s=s^{\rm id}$).

**Lemma 3.1.**

- (i) For **every** $t\in\mathbb R^N$: $\sum_i(Dt)_i=0$ and
  $\sum_i(Dt)_i\,s_i=\sum_it_ia_i$.
- (ii) $\ker D=\mathbb R\mathbf 1$ and $\operatorname{im}D=\{\lambda:\sum\lambda_i=0\}$.
- (iii) $D$ maps $\widetilde L$ onto $\mathrm{Dep}$, with kernel $\mathbb R\mathbf 1$. In
  Gale coordinates, $u\mapsto\lambda^u$ with $\lambda^u_i=\langle u,p_i-p_{i+1}\rangle$ is a
  linear isomorphism $\mathbb R^m\to\mathrm{Dep}$ (when $P$ comes from a basis as in §2).

*Proof.* (i) The first sum telescopes. For the second,
$$\sum_i(t_i-t_{i+1})s_i=\sum_it_is_i-\sum_jt_js_{j-1}=\sum_jt_j(s_j-s_{j-1})=\sum_jt_ja_j,$$
using $s_0:=s_N$. Indeed $s_j-s_{j-1}=a_j$ for $j\ge2$, and $s_1-s_N=a_1-0$.

(ii) $Dt=0$ means $t_i=t_{i+1}$ for all $i$, so $t$ is constant. Given $\lambda$ with
$\sum\lambda=0$, set $t_1=0$ and $t_{i+1}=t_i-\lambda_i$ for $i<N$. Then
$t_N-t_1=-\sum_{i<N}\lambda_i=\lambda_N$, so $Dt=\lambda$. (Lean: `gale_converse`,
`eq_const_of_cyclic_diff_zero`.)

(iii) By (i), $D\widetilde L\subseteq\mathrm{Dep}$. Conversely, if $\lambda\in\mathrm{Dep}$,
write $\lambda=Dt$ by (ii); then $\sum t_ia_i=\sum\lambda_is_i=0$ by (i), so
$t\in\widetilde L$. The kernel is $\ker D\cap\widetilde L=\mathbb R\mathbf 1$. Finally,
$t\in\widetilde L$ is $t_i=\langle u,p_i\rangle+c$, and $Dt=\lambda^u$. If $\lambda^u=0$ then
$(\langle u,p_i\rangle)_i$ is constant, hence a multiple of $\mathbf 1$; since
$\mathbf 1,v^1,\dots,v^m$ are independent, $u=0$. $\square$

As a dimension check, $\dim\mathrm{Dep}=N-1-d=m$, because $s_1,\dots,s_N$ affinely span
$\mathbb R^d$: their consecutive differences are the $a_i$. The lemma uses only
$\sum a_i=0$; spanning is used only for the dimension count. Applied to $\pi$, the affine
dependences of $s^\pi_1,\dots,s^\pi_N$ are exactly
$\lambda_k=\langle u,p_{\pi(k)}-p_{\pi(k+1)}\rangle$, because the Gale diagram of
$(a_{\pi(k)})_k$ is $(p_{\pi(k)})_k$.

For $N=d+2$, $m=1$, this is Lemma 4.2 of `sylvester_radon.pdf`: there $G$ is our $t$,
normalised by a zero at the slot of the closing step; see §8.

---

## 4. The nonvertex / projection-order equivalence

**Lemma 4.1 (signed dependences).** Let $s_1,\dots,s_N$ affinely span $\mathbb R^d$ and fix
$i$. The following are equivalent:

- (a) $s_i\in\operatorname{int}\operatorname{conv}\{s_j:j\ne i\}$;
- (b) there is an affine dependence $\lambda$ with $\lambda_i>0$ and $\lambda_j<0$ for all
  $j\ne i$.

*Proof.* (b)$\Rightarrow$(a). We have
$s_i=\sum_{j\ne i}\mu_js_j$ with $\mu_j=-\lambda_j/\lambda_i>0$ and $\sum_{j\neq i}\mu_j=1$
(Lean: `mem_convexHull_of_signed_dependence`). If the points $s_j$, $j\ne i$, lay in an affine
hyperplane $H$, then so would $s_i$, contradicting spanning. So they affinely span
$\mathbb R^d$. A convex combination with all weights positive then lies in the relative
interior of their hull, which here is the interior.

(a)$\Rightarrow$(b). Let $b=\frac1{N-1}\sum_{j\ne i}s_j$. Since $s_i$ is interior,
$y=s_i+\varepsilon(s_i-b)$ lies in the hull for small $\varepsilon>0$, say
$y=\sum_{j\neq i}\nu_js_j$ with $\nu_j\ge0$. Then
$s_i=\frac1{1+\varepsilon}y+\frac{\varepsilon}{1+\varepsilon}b$ is a convex combination of
the $s_j$, $j\ne i$, with all weights at least $\frac{\varepsilon}{(1+\varepsilon)(N-1)}>0$.
Put $\lambda_i=1$ and $\lambda_j=-(\text{weight of }s_j)$. $\square$

**Lemma 4.2 (nonvertex $=$ interior under general position).** If $s_1,\dots,s_N$
($N\ge d+2$) are in general affine position, then
$s_i\in\operatorname{conv}\{s_j:j\ne i\}$ implies
$s_i\in\operatorname{int}\operatorname{conv}\{s_j:j\ne i\}$.

*Proof.* The $N-1\ge d+1$ other points affinely span $\mathbb R^d$, so their hull $K$ is a
full-dimensional polytope. If $s_i\in\partial K$, then $s_i$ lies in a facet $F$ with affine
hull a hyperplane $H$, and $F=\operatorname{conv}(F\cap\{s_j\})$. By Carathéodory in $H$
(dimension $d-1$), $s_i$ is in the convex hull of at most $d$ points $s_j\in H$. Those points
together with $s_i$ form at most $d+1$ affinely dependent points, since $s_i$ lies in their
affine hull and is distinct from them. This contradicts general position. $\square$

**Example 4.3 (Lemma 4.2 fails without general position).** Take $d=2$, $N=4$ and steps
$(1,0),(1,0),(-1,1),(-1,-1)$. The points are $s=(1,0),(2,0),(1,1),(0,0)$. Here $s_1$ is the
midpoint of $s_4s_2$, which is an edge of $\operatorname{conv}\{s_2,s_3,s_4\}$. So $s_1$ is
not a vertex, but it is not interior either: $N_1=1\ne0=N_1^{\rm int}$. By Theorem 4.5 below,
$q_P(c)=0$ for this class. So $N_1(c)=q_P(c)$ fails without general position, while
$N_1^{\rm int}(c)=q_P(c)$ still holds.

**Theorem 4.5 (cut lemma).** Let $\sum a=0$ with the $a_i$ spanning. For every $\pi$ and
every $i\in\{1,\dots,N\}$,

$$s^\pi_i\in\operatorname{int}\operatorname{conv}\{s^\pi_j:j\ne i\}\iff\pi\circ\rho^{\,i}=(\pi(i+1),\dots,\pi(N),\pi(1),\dots,\pi(i))\in\Omega(P).$$

If (GP$_\pi$) holds, the left side is equivalent to "$s^\pi_i$ is not a vertex".

*Proof.* By Lemma 3.1 applied to $\pi$, the affine dependences are
$\lambda_k=h_k-h_{k+1}$ with $h_k=\langle u,p_{\pi(k)}\rangle$, $u\in\mathbb R^m$. The sign
pattern of Lemma 4.1(b) asks for $h_k<h_{k+1}$ for all $k\ne i$ (indices mod $N$), and for
$h_i>h_{i+1}$. The $N-1$ inequalities $h_k<h_{k+1}$, $k=i+1,\dots,i-1$, form the chain
$$h_{i+1}<h_{i+2}<\dots<h_N<h_1<\dots<h_i,$$
which already implies $h_i>h_{i+1}$. With $u'=-u$ the chain says
$\langle u',p_{\pi(i+1)}\rangle>\dots>\langle u',p_{\pi(i)}\rangle$, that is,
$\pi\circ\rho^i\in\Omega$. The steps are reversible. Combine with Lemma 4.1, and with
Lemma 4.2 for the last sentence (the points of a walk always affinely span, since their
differences are the $a_i$). $\square$

The case $i=N$ says that the base point $s^\pi_N=0$ is interior iff $\pi\in\Omega$. This is
the event counted in Theorem 2.26 of the lecture notes.

**Corollary 4.6 (pointwise identity).** For every $c$:

- $N_1^{\rm int}(c)=q_P(c)$, with no genericity;
- if the walk of $c$ is in general position, $N_1(c)=q_P(c)$.

*Proof.* Fix $\pi\in c$. The map $i\mapsto\pi\circ\rho^i$, $i\in\mathbb Z/N$, is a bijection
onto $c$. Apply Theorem 4.5 and sum over $i$. $\square$

**Example 4.4 (general position of one ordering plus (NT) is not enough).** Take the planar
Gale points $p_1=(0,0)$, $p_2=(1,0)$, $p_3=(0,1)$, $p_4=(3,0)$, $p_5=(2,5)$, so $N=5$,
$d=2$, $m=2$. Here $p_1,p_2,p_4$ are collinear. Solving
$\widetilde L^{\perp}=\{z:\sum z=0,\ \sum x_iz_i=0,\ \sum y_iz_i=0\}$ gives the basis
$(2,-3,0,1,0)$, $(6,-2,-5,0,1)$, hence the steps
$$a_1=(2,6),\ a_2=(-3,-2),\ a_3=(0,-5),\ a_4=(1,0),\ a_5=(0,1),\qquad\textstyle\sum a_i=0.$$
The walk points are $(2,6),(-1,4),(-1,-1),(0,-1),(0,0)$. All ten $3\times3$ orientation
determinants are nonzero; in the order of the triples
$123,124,125,134,135,145,234,235,245,345$ they are $15,17,14,7,4,-2,5,5,1,1$. So
(GP$_{\rm id}$) holds, and the $p_i$ are distinct, so (NT) holds.

The pairs $\{1,2\},\{1,4\},\{2,4\}$ share one critical direction. The other seven
directions, $(0,1)$, $(2,5)$, $(1,-1)$, $(1,5)$, $(3,-1)$, $(1,2)$, $(1,-5)$, are pairwise
non-parallel and differ from $(1,0)$. So there are $8$ critical directions, $16$ open arcs and
$|\Omega|=16$. By §5, the average of $N_1^{\rm int}$ over all $120$ orderings is
$16/24\ne20/24$. This does not contradict Theorem B: a uniformly random ordering of these steps
is exchangeable, but it is *not* almost surely in general position (orderings in which
$1,2,4$ are cyclically consecutive are degenerate).

---

## 5. Deterministic circular-word counting

**Theorem 5.1.** For every spanning closed walk $a$ and every $r\ge0$,
$$\sum_{c\in\mathcal C_N}\binom{N_1^{\rm int}(c)}r=T_r(P),\qquad\#\{c:N_1^{\rm int}(c)=0\}=(N-1)!-\kappa(P).$$
Under (G), the same holds with $N_1$.

*Proof.* Use Corollary 4.6 termwise. For the second identity, $N_1^{\rm int}(c)=0$ iff
$q_P(c)=0$. Under (G) every class is in general position, so $N_1=N_1^{\rm int}$. Dividing by
$(N-1)!$ gives the two displayed formulas of the request. $\square$

**Multiplicity versus support.**

- $T_1(P)=\sum_cq_P(c)=|\Omega(P)|$ counts projection orders with multiplicity. It is the
  number of open chambers met by $\widetilde L$.
- $\kappa(P)$ counts only the circular classes that contain at least one projection order.
- Since $1_{q>0}=\sum_{r\ge1}(-1)^{r+1}\binom qr$,
  $$\kappa=T_1-T_2+T_3-\cdots,\qquad T_r=0\ \text{for } r>N-d-1. \tag{5.1}$$
  The vanishing holds because a full-dimensional hull has at least $d+1$ vertices, so
  $N_1^{\rm int}\le N_1\le N-d-1$.
- So the deficiency $T_1-\kappa$ is the inclusion–exclusion of the *collisions*: several
  projection orders falling into one circular class. As shown in §6 and §7, $T_1$ is
  universal and $T_2$ is not.

**Group-averaged form.** For $x=(x_1,\dots,x_N)$ write $x\circ\sigma=(x_{\sigma(1)},\dots,x_{\sigma(N)})$.

- *Relabelling.* $\widetilde L(x\circ\sigma)=\{t\circ\sigma:t\in\widetilde L(x)\}$, hence
  $\Omega(x\circ\sigma)=\sigma^{-1}\Omega(x)$. Left multiplication by $\sigma^{-1}$ permutes
  the left cosets, $q_{x\circ\sigma}(c)=q_x(\sigma c)$, and therefore $T_r$ and $\kappa$ are
  invariant: $T_r(x\circ\sigma)=T_r(x)$ and $\kappa(x\circ\sigma)=\kappa(x)$.
- The walk of $x\circ\sigma$ is the walk of the class $\sigma\langle\rho\rangle$ of $x$.
- Each class has $N$ elements, so
  $$\frac1{N!}\sum_{\sigma\in\mathrm{Sym}(N)}f\bigl(N_1^{\rm int}(x\circ\sigma)\bigr)=\frac1{(N-1)!}\sum_{c}f\bigl(q_x(c)\bigr). \tag{5.2}$$

**Lemma 5.2 (transversal).** Each class $c=\pi\langle\rho\rangle$ contains exactly one
$\sigma$ with $\sigma(N)=N$. Hence $\sigma\mapsto\sigma\langle\rho\rangle$ is a bijection
$\mathrm{Stab}(N)\to\mathcal C_N$, and
$$\frac1{(N-1)!}\sum_{\sigma\in\mathrm{Stab}(N)}f\bigl(N_1^{\rm int}(x\circ\sigma)\bigr)=\frac1{(N-1)!}\sum_cf\bigl(q_x(c)\bigr). \tag{5.3}$$

*Proof.* $(\pi\circ\rho^i)(N)=\pi(i)$, and exactly one $i\in\mathbb Z/N$ has $\pi(i)=N$. So
the representative is the rotation of the word that puts the label $N$ (the closing step) in
the last position. $\square$

Lean (`CyclicCollision.lean`, for an arbitrary set $\Omega$):

- `sum_fun_rotCount_eq`: $\sum_{\pi}f(q(\pi))=N\sum_{\pi(p)=p}f(q(\pi))$;
- `sum_rotCount`: $\sum_\pi q(\pi)=N|\Omega|$;
- `sum_rotCount_sq`: $\sum_\pi q(\pi)^2=N\sum_{\alpha\in\Omega}q(\alpha)$;
- `sum_rotCount_stab`: $\sum_{\pi(p)=p}q(\pi)=|\Omega|$;
- `sum_rotCount_choose_two_stab`:
  $2\sum_{\pi(p)=p}\binom{q(\pi)}2+|\Omega|=\sum_{\alpha\in\Omega}q(\alpha)$.

The right side of the last identity, minus $|\Omega|$, counts ordered pairs of distinct
same-class projection orders; this is $2T_2$.

---

## 6. Exchangeable walk and bridge corollaries

All sets involved are Borel. The set $\{(y,z_1,\dots,z_k):y\in\operatorname{int}\operatorname{conv}(z)\}$
is open, since an interior point stays inside a small simplex whose vertices depend
continuously on $z$. The functions $T_r$ and $\kappa$ are then Borel by Theorem 5.1. Write
$F(x)=N_1^{\rm int}(\text{walk of }x)$.

**Lemma 6.1 (conditional expectation as a group average).** Let $G$ be a finite group acting
on $(\mathbb R^d)^N$ by $x\mapsto x\circ\sigma$, and suppose $X\circ\sigma\overset d=X$ for
all $\sigma\in G$. Let $\mathcal I=\{\{X\in B\}:B\text{ Borel},\ B\circ\sigma=B\ \forall\sigma\in G\}$.
For bounded Borel $f$,
$$\mathbb E[f(X)\mid\mathcal I]=\frac1{|G|}\sum_{\sigma\in G}f(X\circ\sigma)\quad\text{a.s.}$$

*Proof.* The right side $g(X)$ is $\mathcal I$-measurable, because $g$ is $G$-invariant. For
invariant $B$ we have $\mathbb E[f(X)1_B(X)]=\mathbb E[f(X\circ\sigma)1_B(X\circ\sigma)]=\mathbb E[f(X\circ\sigma)1_B(X)]$
for each $\sigma$. Averaging over $\sigma$ gives $\mathbb E[g(X)1_B(X)]$. $\square$

This is the correct form of "the labels are uniform given the unlabeled data". It averages
over *group elements*, so it needs no regular conditional distribution, and repeated steps or
nontrivial stabilisers cause no difficulty. If $\mathcal J$ is any $\sigma$-field with
$\sigma(T_r(X))\subseteq\mathcal J\subseteq\mathcal I$, for instance the $\sigma$-field
generated by any invariant encoding of the unlabeled Gale diagram, the tower property gives
the same formulas conditionally on $\mathcal J$. Conditioning on the *labeled* $P$ is
meaningless, since $P$ determines $N_1$.

**Bridges.** Take $G=\mathrm{Sym}(N)$. By Lemma 6.1 and (5.2), almost surely
$$\mathbb E\bigl[\tbinom{F(X)}r\bigm|\mathcal I\bigr]=\frac{T_r(X)}{(N-1)!},\qquad\mathbb P(F(X)=0\mid\mathcal I)=1-\frac{\kappa(X)}{(N-1)!}.$$
The $N!$ linear orders of the steps fall into the $(N-1)!$ circular classes, each of size
$N$, and within a class the point sets are translates (2.1).

**Ordinary walks.** Let $Y_1,\dots,Y_{N-1}$ be exchangeable and append the closing step
$X_N=-\sum Y_i$. The points of the closed walk are $S_1,\dots,S_{N-1},S_N=0=S_0$, which is the
point set $\{S_0,\dots,S_{N-1}\}$. For $\sigma\in\mathrm{Stab}(N)$,
$X\circ\sigma=(Y\circ\sigma',X_N)\overset d=X$. Take $G=\mathrm{Stab}(N)$, apply Lemma 6.1 and
(5.3): the same two formulas hold, with $|G|=(N-1)!$. Lemma 5.2 is the precise orbit-counting
statement: rotating each circular word so that the closing step comes last is a bijection
between $\mathrm{Stab}(N)$ and $\mathcal C_N$. Walks and bridges therefore have the same
formula *as functions of the step configuration*. They differ only through the law of
$T_r(X)$ and $\kappa(X)$.

**From $N_1^{\rm int}$ to $N_1$.** Assume the $N$ points are a.s. in general position. Then
$N_1=F(X)$ a.s. (Lemma 4.2). Moreover (G) holds a.s.: each $X\circ\sigma$, $\sigma\in G$, has
the law of $X$ and so is a.s. in general position; every $\pi\in\mathrm{Sym}(N)$ is a rotation
of some $\sigma\in\mathrm{Stab}(N)$; and rotation preserves general position by (2.1). This
gives Theorem B. For the normalisation of Theorem 1.4 (points $S_1,\dots,S_{d+2}$), translate
by $-S_1$: this gives a walk from $0$ with the $d+1$ exchangeable increments
$X_2,\dots,X_{d+2}$ (compare Remark 4.5 of `sylvester_radon.pdf`).

**Cyclic shifts preserve $N_1$ and convex position.** This is (2.1): rotation is a
translation of the point set together with a cyclic relabelling of the indices.

---

## 7. The exact role of Theorem 2.17

**What Theorem 2.17 says.** For *any* convex $Q\subseteq\mathbb R^N$,
$\#\{\sigma:K_\sigma\cap Q\ne\emptyset\}=\#\{\sigma:F_\sigma\cap Q\ne\emptyset\}$. Here
$K_\sigma$ are the *closed* chambers and $F_\sigma=V_{\mathrm{cyc}(\sigma)}$. It knows nothing
about $\widetilde L$ being a subspace or about open chambers. We work under (G), in the form
(c) of Lemma 2.1. Put $L_0=\widetilde L\cap\mathbf 1^\perp$ ($\dim L_0=m$), choose
$u\in L_0$, and let
$$Q_u=\{t\in L_0:\langle u,t\rangle=1\}\qquad(\text{convex}).$$

Say that a subspace $L\ni\mathbf 1$ of dimension $N-c$ is *generic* if
$\dim(V_B\cap L)=\max(\#B-c,1)$ for all $B$. So (G) says that $\widetilde L$ is generic with
$c=d$.

**Lemma 7.1 (closed versus open).** Let $L$ be generic. If $t\in K_\pi\cap L$ and
$t\notin\mathbb R\mathbf 1$, then every neighbourhood of $t$ meets $C_\pi\cap L$.

*Proof.* Let $B$ be the partition of $[N]$ into the level sets of $t$. Since $t\in K_\pi$,
the blocks are consecutive in the word $\pi$, with strict decrease between blocks. Since
$t\in V_B\cap L\setminus\mathbb R\mathbf 1$, $\dim(V_B\cap L)\ge2$, so it equals $\#B-c$.
Then $\dim(V_B+L)=\#B+(N-c)-(\#B-c)=N$, so $V_B+L=\mathbb R^N$. Pick $z\in C_\pi$ and write
$z=v+l$ with $v\in V_B$, $l\in L$. Inside each block, $t-\varepsilon v$ is constant, so
$t+\varepsilon l=t-\varepsilon v+\varepsilon z$ is strictly ordered according to $\pi$ within
blocks. For small $\varepsilon$ the strict gaps between blocks survive. So
$t+\varepsilon l\in C_\pi\cap L$. $\square$

Now let $\Omega_u^{\pm}=\{\pi:C_\pi\cap L_0\cap\{\pm\langle u,\cdot\rangle>0\}\ne\emptyset\}$.

**Lemma 7.2 (one-sided count from Theorem 2.17).** Under (G), for $u\in L_0$ outside a finite
union of proper subspaces,
$$|\Omega_u^+|=\#\{\pi:K_\pi\cap Q_u\neq\emptyset\}=\#\{\sigma:F_\sigma\cap Q_u\neq\emptyset\}=\sum_{k\ge d+2}{N\brack k}.$$

*Proof.* First equality. "$\le$" is clear after rescaling. For "$\ge$": a point
$t\in K_\pi\cap Q_u$ is not in $\mathbb R\mathbf 1$, since $Q_u\subseteq\mathbf 1^\perp$ and
$0\notin Q_u$. By Lemma 7.1 there is a nearby $t'\in C_\pi\cap\widetilde L$. Subtracting its
mean keeps it in $C_\pi$ and puts it in $L_0$, with $\langle u,t'\rangle$ close to $1$. Rescale.

Second equality: this is Theorem 2.17 with $Q=Q_u$.

Third equality. $F_\sigma\cap Q_u\ne\emptyset$ iff $F_\sigma\cap L_0\not\subseteq u^\perp$.
For $u$ outside the subspaces $(F_\sigma\cap L_0)^\perp\cap L_0$ (taken over $\sigma$ with
$F_\sigma\cap L_0\ne0$), this is iff $F_\sigma\cap L_0\ne0$. By (c),
$\dim(F_\sigma\cap L_0)=\max(\mathrm{cyc}(\sigma)-d,1)-1$, which is positive iff
$\mathrm{cyc}(\sigma)\ge d+2$. Finally $\#\{\sigma:\mathrm{cyc}(\sigma)=k\}={N\brack k}$. $\square$

**Lemma 7.3 (central versus affine: the missing ingredient).** Under the hypotheses of
Lemma 7.2, let $L'=(L_0\cap u^\perp)+\mathbb R\mathbf 1$. Then
$$|\Omega(\widetilde L)|=2|\Omega_u^+|-|\Omega(L')|,$$
and $L'$ is generic with $c=d+1$ for $u$ outside a further finite union of proper subspaces.

*Proof.* Let $\pi\in\Omega$ and $t\in C_\pi\cap\widetilde L$. Subtracting the mean puts $t$ in
$C_\pi\cap L_0$, which is relatively open in $L_0$. A small perturbation makes
$\langle u,t\rangle\ne0$, so $\Omega=\Omega^+_u\cup\Omega^-_u$. The map $t\mapsto-t$ sends
$C_\pi$ to $C_{\pi w_0}$ (the reversed word), so $|\Omega_u^-|=|\Omega_u^+|$.

The intersection $\Omega^+_u\cap\Omega^-_u$ consists of the $\pi$ for which the convex set
$C_\pi\cap L_0$ meets both open half-spaces. By convexity, and since $C_\pi\cap L_0$ is
relatively open, this happens iff it meets $u^\perp$, i.e. iff $C_\pi\cap L'\ne\emptyset$.
Inclusion–exclusion gives the formula.

For genericity, $V_B\cap L'=\mathbb R\mathbf 1\oplus(V_B\cap L_0\cap u^\perp)$. For $u$ off
$(V_B\cap L_0)^\perp$, the dimension drops by one whenever $V_B\cap L_0\ne0$. This gives
$\dim(V_B\cap L')=1+\max(\#B-d-2,0)=\max(\#B-(d+1),1)$. $\square$

**Proposition 7.4.** Under (G), $T_1(P)=|\Omega(P)|=2\sum_{j\ge0}{N\brack d+2+2j}$.

*Proof.* Lemmas 7.1–7.3 use only property (c) of $\widetilde L$, so they hold verbatim
for every generic $L\ni\mathbf 1$ with parameter $c$ in place of $d$ (for $c\le N-2$, so
that $L_0\ne0$). We show by downward induction on $c$ that $|\Omega(L)|$ takes a common
value $r(c)$ on all generic $L$ with parameter $c$. By Lemmas 7.2 and 7.3,
$$r(c)=2\sum_{k\ge c+2}{N\brack k}-r(c+1).$$
At $c=N-1$ we have $L=\mathbb R\mathbf 1$, which meets no open chamber, so $r(N-1)=0$.
Unwinding,
$$r(d)=2\sum_{i\ge0}(-1)^i\sum_{k\ge d+2+i}{N\brack k}=2\sum_{j\ge0}{N\brack d+2+2j}. \qquad\square$$

*Alternative proof (Zaslavsky).* By (c), the intersection poset of the restricted arrangement
$\{t_i=t_j\}\cap L_0$ is the rank-truncation of the partition lattice to the flats of rank
$<m$, plus the top element $\{0\}$. Zaslavsky's theorem (T. Zaslavsky, *Facing up to
arrangements*, Mem. AMS 1 (1975), no. 154) together with Rota's sign theorem gives
$$\#\text{regions}=\sum_{k<m}w_k+\sum_{k<m}(-1)^{m-1-k}w_k,\qquad w_k={N\brack N-k},$$
and this is the same number. The same count, under the same kind of genericity, is in
Kabluchko–Vysotsky–Zaporozhets, *Convex hulls of random walks, hyperplane arrangements, and
Weyl chambers*, GAFA 27 (2017) 880–918 (reference [13] of the lecture notes).

**"Half the chambers" is false.** By Lemma 7.3,
$2|\Omega^+_u|=|\Omega|+|\Omega(L')|>|\Omega|$ unless $N=d+2$ (where $L'=\mathbb R\mathbf 1$).
For $N=d+3$: $|\Omega^+_u|=1+\binom N2$, but $|\Omega|=N(N-1)$. The smallest case is $N=4$,
$d=1$: $2\cdot7=14\ne12$.

**Checks.**

- $N=d+2$: $2{N\brack N}=2$. Directly: $P\subset\mathbb R$ has distinct points by (NT), so
  $\Omega=\{\text{decreasing},\text{increasing}\}$.
- $N=d+3$: $2{N\brack N-1}=N(N-1)$. Directly: by (Simple) there are $2\binom N2$ distinct
  critical angles, hence $N(N-1)$ arcs with pairwise distinct orders (§8.1).
- $d=1$: four or more distinct points on a line always have $N_1=N-2$. Indeed, using
  $\sum_{k\text{ odd}}{N\brack k}=N!/2$,
  $2\sum_{j}{N\brack3+2j}/(N-1)!=(N!-2(N-1)!)/(N-1)!=N-2$.

**The $r=1$ consequence.** $\mathbb E N_1=T_1/(N-1)!=2\sum_j{N\brack d+2+2j}/(N-1)!$, and
equivalently
$$\mathbb E f_0=N-\mathbb E N_1=\frac{2}{(N-1)!}\sum_{j\ge0}{N\brack d-2j}$$
(using $\sum_k(-1)^k{N\brack k}=0$). For a walk with $n=N-1$ steps this is the known
distribution-free expected number of vertices: the $k=0$ case of the
Kabluchko–Vysotsky–Zaporozhets face formula, Adv. Math. 320 (2017).

**Why Theorem 2.17 stops at $r=1$.** $T_1=\sum_\pi1[C_\pi\cap\widetilde L\ne\emptyset]$ is
*linear* in chamber indicators, and Theorem 2.17 counts exactly such sums for one convex set.
By contrast,
$$T_2=\tfrac12\sum_\pi\sum_{i=1}^{N-1}1[\pi\in\Omega]\,1[\pi\rho^i\in\Omega]$$
is *quadratic*. It pairs the chamber $K_\pi$ with the chamber $K_{\pi\rho^i}$, i.e. it acts on
positions rather than on coordinates. There is no single convex set whose chamber count is
this sum. And $T_2$ is **not** universal: the two Lean-checked step sets of
`FivePointBridge.lean` ($N=5$, $d=2$, general position for every ordering) have $20$
and $10$ orderings out of $120$ with $N_1=2$. By Theorem 5.1 these counts are
$120\cdot T_2/24$, so $T_2=4$ and $T_2=2$, while both have $T_1=20$.

---

## 8. Rank two: proof of $T_2(P)=2s(P)$

Assume $N=d+3\ge4$, so $m=2$, and assume (G), equivalently (Simple) (Lemma 2.1). Write
$u_\theta=(\cos\theta,\sin\theta)$ and $M=\binom N2$.

### 8.1 The circular sequence

The critical angles of a pair $\{x,y\}$ are the two angles with $u_\theta\perp p_x-p_y$; they
differ by $\pi$. By (Simple) the $2M$ critical angles are distinct. Sort them as
$\varphi_0<\dots<\varphi_{2M-1}$ (cyclically). The set of critical angles is invariant under
$+\pi$, and every half-open interval of length $\pi$ contains exactly one critical angle of
each pair. Hence $\varphi_{k+M}=\varphi_k+\pi$.

Let $\omega_k$ be the projection order (by decreasing $\langle u_\theta,p\rangle$) on the open
arc $(\varphi_k,\varphi_{k+1})$. It is constant there, because there are no ties. Indices are
mod $2M$.

**Lemma 8.1.**

- (i) $\omega_{k+1}$ is obtained from $\omega_k$ by swapping one *adjacent* pair, namely the
  pair whose critical angle is $\varphi_{k+1}$.
- (ii) For $0\le l\le M$, the set $D(\omega_k,\omega_{k+l})$ of pairs ordered differently is
  the set of pairs crossed at $\varphi_{k+1},\dots,\varphi_{k+l}$, and has exactly $l$
  elements. Also $\omega_{k+M}=\mathrm{rev}(\omega_k)$.
- (iii) $|D(\omega_k,\omega_{k'})|=\min(l,2M-l)$ where $l\equiv k'-k$ (mod $2M$). In
  particular the $\omega_k$ are pairwise distinct, and $\Omega(P)=\{\omega_0,\dots,\omega_{2M-1}\}$
  with $|\Omega|=N(N-1)$.

*Proof.* (i) At $\varphi_{k+1}$ only $\{x,y\}$ ties. All other relative orders persist, by
continuity. If some $z$ lay between $x$ and $y$, its relations to both would persist, so
$x,y$ could not swap.

(ii) The interval $(\varphi_k,\varphi_{k+l}]$ is half-open of length at most $\pi$, so it
contains at most one critical angle of each pair. Each pair crossed is therefore crossed
exactly once, and it is inverted. For $l=M$ every pair is inverted.

(iii) For $l>M$, $\omega_{k+l}=\mathrm{rev}(\omega_{k+l-M})$, so $D$ is the complement of a
set of size $l-M$. Every $\pi\in\Omega$ is realised on an open cone of directions, and that
cone contains a noncritical angle. $\square$

### 8.2 Block-transposition events

**Definition.** A *block-transposition event* (BTE) is a pair $(k,i)$ with
$k\in\mathbb Z/2M$ and $1\le i\le N-1$ such that, writing $\omega_k=AB$ ($A$ the first $i$
letters, $B$ the remaining $N-i$),
$$\omega_{k+|A||B|}=BA,\quad\text{i.e. }\omega_{k+i(N-i)}=\omega_k\circ\rho^i.$$
By Lemma 8.1(ii) this holds iff the $|A||B|$ moves right after arc $k$ are exactly the
cross-block swaps $\{a,b\}$ with $a\in A$, $b\in B$. Those moves are then consecutive, they
turn $AB$ into $BA$, and they leave the internal orders of $A$ and $B$ unchanged.

Let $\mathcal E$ be the set of BTEs, with $k$ ranging over the **full** period of $2M$ arcs.
Every unordered split $\{A,B\}$ is considered with both orientations, and $\mathcal E$ is not
quotiented by reversal.

Note that $|A||B|\le\lfloor N^2/4\rfloor<M$ for $N\ge3$.

**Proposition 8.2.** The map
$\Phi:\mathcal E\to\{\{\alpha,\beta\}\subseteq\Omega:\alpha\ne\beta,\ \alpha\langle\rho\rangle=\beta\langle\rho\rangle\}$,
$(k,i)\mapsto\{\omega_k,\omega_k\circ\rho^i\}$, is a bijection. Hence $|\mathcal E|=T_2(P)$.

*Proof.* Two distinct elements of one class are $\alpha=AB$ and $\beta=\alpha\rho^i=BA$, with
$1\le i\le N-1$. This is step 1 of the request: a nontrivial cyclic block rotation. Here
$D(\alpha,\beta)$ is the set of cross pairs, of size $i(N-i)\in[1,M)$.

Let $\alpha=\omega_k$, $\beta=\omega_{k'}$ and $l\equiv k'-k$. By Lemma 8.1(iii),
$\min(l,2M-l)=i(N-i)<M$, so exactly one of $l$ and $2M-l$ equals $i(N-i)$:

- if $l=i(N-i)$, then $(k,i)\in\mathcal E$;
- if $2M-l=i(N-i)$, then $(k',N-i)\in\mathcal E$, since $\omega_{k'}=BA$ has first block $B$
  and $\omega_{k'+|A||B|}=\omega_k=AB$.

So $\Phi$ is onto. For injectivity, suppose $(k,i)$ and $(k',i')$ have the same image. If
$\omega_k=\omega_{k'}$, then $k=k'$ (Lemma 8.1(iii)) and $\rho^i=\rho^{i'}$, so $i=i'$.
Otherwise $\omega_{k'}=\omega_k\rho^i$ and $\omega_k=\omega_{k'}\rho^{i'}$. Then the
forward distances $k\to k'$ and $k'\to k$ would both be $<M$, but they add up to $2M$, a
contradiction. $\square$

This settles steps 2 and 3 of the request: a same-class pair occurs exactly when all cross
inversions are performed consecutively, and every BTE yields such a pair.

### 8.3 The factor 2

The map $\iota(k,i)=(k+M,N-i)$ is a fixed-point-free involution of $\mathcal E$. Indeed, if
$\omega_k=AB$ and $\omega_{k+l}=BA$, then
$\omega_{k+M}=\mathrm{rev}(B)\,\mathrm{rev}(A)$ and
$\omega_{k+M+l}=\mathrm{rev}(A)\,\mathrm{rev}(B)$. So $(k+M,N-i)$ is again an event, with the
roles of $A$ and $B$ exchanged as sets.

**Definition of $s(P)$.** Set $s(P)=|\mathcal E|/2$. This is the number of $\iota$-orbits, and
it equals the number of BTEs whose start $k$ lies in any fixed window of $M$ consecutive arcs
(one half-period). Proposition 8.4 identifies these orbits with unordered splits.

**Theorem 8.3.** Under (G) and $N=d+3$: $T_2(P)=2s(P)$, $T_r(P)=0$ for $r\ge3$, and
$\kappa(P)=N(N-1)-2s(P)$.

*Proof.* Proposition 8.2 and the definition of $s(P)$ give the first identity. The second is
$q\le N-d-1=2$, from (5.1). Then $\kappa=T_1-T_2$ by (5.1), with $T_1=N(N-1)$. $\square$

**Why exactly 2 (step 4 of the request).** $T_2$ counts *unordered* same-class pairs, and
each such pair is one BTE (Proposition 8.2); no orientation of the pair is chosen. The events
come in reversal pairs $\{(k,i),(k+M,N-i)\}$, one in each half-period. So the factor is
$2=$ (number of half-periods). It is *not* the factor that orients a pair $\{\alpha,\beta\}$:
that would give $4$ in the ordered count $\sum_{\alpha\in\Omega}(q(\alpha)-1)=2T_2=4s$.

### 8.4 Geometric translation: strongly separable splits

For an unordered split $\{A,B\}$ of $P$ with both parts nonempty, let
$I=\{\theta:\langle u_\theta,a\rangle>\langle u_\theta,b\rangle\ \forall a\in A,b\in B\}$. Call
$\{A,B\}$ *strongly separable* if

- it is strictly linearly separable ($I\ne\emptyset$), and
- for every pair $x,y$ lying on the same side, some line *parallel to $xy$* strictly separates
  $A$ from $B$.

**Proposition 8.4.** Under (Simple), $s(P)$ is the number of strongly separable unordered
splits of $P$. More precisely, $(k,i)\mapsto$ (the set of the first $i$ letters of
$\omega_k$, the set of the rest) is a bijection from $\mathcal E$ onto the *oriented* strongly
separable splits.

*Proof.* Fix an oriented split $(A,B)$.

*Shape of $I$.* $I$ is an intersection of open half-circles, so it is an open arc
$(\alpha,\beta)$ when nonempty. Its length is $<\pi$, because there are two non-parallel
cross differences when $N\ge3$. Its endpoints are critical angles of cross pairs, and
$-I=I+\pi$ is the arc on which $B$ lies above $A$. Let $J=[\beta,\alpha+\pi]$, an arc of
length $<\pi$. Each cross pair changes sign on $J$, so it has exactly one critical angle in
$J$. The endpoints of $J$ are cross critical angles, and by (Simple) internal critical angles
never coincide with them.

*Event $\Rightarrow$ strongly separable.* Let $(k,i)$ be an event for $(A,B)$. Then
$\omega_k=AB$, so arc $k$ lies in $I$. The move right after arc $k$ is a cross swap, which
leaves $I$, so arc $k$ is the *last* arc of $I$ and $\varphi_{k+1}=\beta$. The moves at
$\varphi_{k+1},\dots$ run through $J$. The first $|A||B|$ of them are cross swaps, which are
all the cross swaps in $J$. If $J$ contained an internal critical angle, it would come after
all of them, but the last critical angle of $J$ is the cross angle $\alpha+\pi$. So $J$
contains no internal critical angle, and neither does $J+\pi$.

Thus every internal critical angle lies in $I\cup(-I)$. That is, for each same-side pair
$\{x,y\}$, projection onto $u\perp(x-y)$ strictly separates $A$ from $B$. Equivalently some
line parallel to $xy$ strictly separates $A$ from $B$.

*Strongly separable $\Rightarrow$ event.* Conversely, if $\{A,B\}$ is strongly separable, let
$k$ be the last arc of $I$. The critical angles in $J$ are exactly the $|A||B|$ cross ones, so
$\omega_{k+|A||B|}$ is the first arc of $-I$. By Lemma 8.1(ii) it differs from $\omega_k=AB$
exactly in the cross pairs, so it equals $BA$.

*Uniqueness.* The event of an oriented split is unique, because $k$ must be the last arc of
$I$. Exchanging the orientation gives the partner $\iota(k,i)$. $\square$

### 8.5 Status of the geometric phrase

The geometric characterisation in `RESEARCH_MAP.md` ("every line through two points on the same
side is parallel to some separating line") is correct under (Simple), with "separating" read
as *strictly* separating. For a singleton side $A=\{a\}$, the condition concerns only pairs
in $B$, and separability means that $a$ is a vertex of $\operatorname{conv}P$.

---

## 9. The $d+2$ and $d+3$ cases, and all factors for $N=4,5$

### 9.1 $N=d+2$: collapse to Theorem 1.4

Here $m=1$ and $P=(p_1,\dots,p_N)\subset\mathbb R$. (G) is equivalent to (NT), i.e. the $p_i$
are distinct (Lemma 2.1). Under exchangeability with general position this holds a.s.; this
is Barysheva's Lemma 4.3, of which Lemma 2.1 and §6 are the general-$N$ version.

By Lemma 3.1 the affine dependence of the walk of $\pi$ is unique up to scale:
$\lambda_k=p_{\pi(k)}-p_{\pi(k+1)}$. The Radon partition is (cyclic descents, cyclic ascents)
of the cyclic sequence $(p_{\pi(1)},\dots,p_{\pi(N)})$, and
$\tau=\min(\mathrm{cdes},\mathrm{casc})$.

To identify with Lemma 4.2 of `sylvester_radon.pdf`: normalise $t$ to vanish at the slot of
the closing step. Then $(0,t_1,\dots,t_{N-1})$ is Barysheva's $(G_1=0,G_2,\dots,G_{d+2})$,
her $X_1$ plays no role (translation by $-S_1$), and her average over $\sigma(1)=1$ is our
$\mathrm{Stab}(N)$ (Lemma 5.2).

By Lemma 4.4 of `sylvester_radon.pdf` (rotate so that the minimum comes first), exactly
$A(N-1,k-1)$ circular classes have $k$ cyclic ascents. This gives Theorem 1.4. In our language:

- $\Omega=\{\uparrow,\downarrow\}$, and these two words are never rotations of each other
  for $N\ge3$;
- so $q_P(c)\in\{0,1\}$, $T_1=\kappa=2$ and $T_r=0$ for $r\ge2$;
- $q_P(c)=1$ iff $\mathrm{casc}(c)\in\{1,N-1\}$, giving $\mathbb P(\tau=1)=2A(d+1,0)/(d+1)!=2/(d+1)!$
  and $\mathbb P(\text{convex})=1-2/(d+1)!$.

The cyclic-collision formula is therefore the $k=1$ part of Theorem 1.4. It is a higher-rank
analogue of that part, not of the full Eulerian law: for $N\ge d+3$ a single cyclic-ascent
statistic no longer exists.

### 9.2 $N=d+3$

By Theorem 8.3, $N_1\le2$ and $\binom{N_1}2=1[N_1=2]$, so
$$\mathbb P(N_1=2)=\frac{\mathbb ET_2}{(N-1)!}=\frac{2\,\mathbb Es(P)}{(N-1)!}.$$
For $N_1\in\{0,1,2\}$, $1[N_1=0]=1-N_1+\binom{N_1}2$. Hence
$$\mathbb P(N_1=0)=1-\mathbb EN_1+\mathbb E\tbinom{N_1}2=1-\frac{N}{(N-2)!}+\frac{2\,\mathbb Es(P)}{(N-1)!},$$
and $\mathbb P(N_1=1)=\mathbb EN_1-2\,\mathbb P(N_1=2)$. No bound on $s$ is used or claimed
here.

### 9.3 All factors for $N=4$ and $N=5$

- **$N=4$, $d=2$ ($N=d+2$).**
  - $T_1=2{4\brack4}=2$, $T_2=0$, $\kappa=2$, $(N-1)!=6$.
  - $\mathbb EN_1=\mathbb P(\tau=1)=2/6=1/3$, $\mathbb P(\text{convex})=2/3$.
  - Theorem 1.4 agrees: $\mathbb P(\tau=1)=2A(3,0)/3!=1/3$ and $\mathbb P(\tau=2)=A(3,1)/3!=2/3$.
- **$N=4$, $d=1$ ($N=d+3$, $P$ planar with 4 points).**
  - $T_1=2{4\brack3}=12=N(N-1)$.
  - Four distinct collinear points always have $N_1=2$. So every one of the $6$ classes has
    $q=2$, $T_2=6$, and $\kappa=6=12-6$.
  - $\mathbb P(N_1=2)=6/6=1$ and $\mathbb P(\text{convex})=1-12/6+6/6=0$.
  - **Corollary 9.1.** Every simple 4-point planar configuration $P$ (no three collinear, no
    parallel connecting lines) has $s(P)=3$. *Proof.* Every such $P$ is the Gale diagram of a
    closed walk on the line (the steps are a basis of $\widetilde L^\perp$, as in
    Example 4.4), and that walk satisfies (G) by Lemma 2.1. Hence $2s=T_2=6$. $\square$
  - So "$s\le2$" cannot hold for 4-point configurations; the bound of Conjecture 4 can at most
    concern $N\ge5$. This fact is recorded only because it bears on how Conjecture 4 is
    stated; Conjecture 4 was not worked on here.
- **$N=5$, $d=2$ ($N=d+3$).**
  - $T_1=2{5\brack4}=20$, $(N-1)!=24$, $\mathbb EN_1=5/6$.
  - $\mathbb P(N_1=2)=\mathbb Es/12$, $\mathbb P(N_1=1)=5/6-\mathbb Es/6$,
    $\mathbb P(\text{convex})=1/6+\mathbb Es/12$.
  - For the two Lean-checked step sets: convex-position counts $40/120$ and $30/120$, and
    two-interior counts $20/120$ and $10/120$ (`FivePointBridge.lean`). Theorem 5.1 gives
    $T_2=4,2$, hence $s=2,1$. Then $1/6+2/12=1/3$ and $1/6+1/12=1/4$ match the checked counts.
- **$N=5$, $d=3$ ($N=d+2$).**
  - $T_1=2$, $\mathbb P(\text{convex})=1-2/24=11/12$.
  - Theorem 1.4: $\mathbb P(\tau=1)=2/4!$.
- **$N=5$, $d=1$.**
  - $T_1=2({5\brack3}+{5\brack5})=2(35+1)=72$, so $\mathbb EN_1=72/24=3=N-2$, as it must be.

---

## 10. Status table

| Part | Statement | Status |
|---|---|---|
| §3 | Gale–polygon identity $\lambda=Dt$ and its converse modulo constants | **proved** (Lean: `gale_identity`, `gale_converse`, `eq_const_of_cyclic_diff_zero`) |
| §4 | Cut lemma: $s^\pi_i$ interior $\iff\pi\rho^i\in\Omega$ | **proved**, no genericity beyond spanning (signed-dependence step in Lean) |
| §4 | "not a vertex" $\iff$ "interior of hull of the rest" | **proved under general position** of that ordering; **false** without it (Example 4.3, $N=4$, $d=2$) |
| §4 | $N_1(c)=q_P(c)$ | **proved under (GP$_c$)**; $N_1^{\rm int}(c)=q_P(c)$ always |
| §5 | $\sum_c\binom{N_1}{r}=T_r$; $\#\{N_1=0\}=(N-1)!-\kappa$ | **proved** for $N_1^{\rm int}$ always, for $N_1$ under (G) (Lean: orbit-counting core) |
| §6 | Conditional formulas given $\mathcal I$; unconditional formulas; walks and bridges | **proved** under exchangeability and a.s. general position (which implies (G) a.s.). "Given $P$" is **ill-posed** and is replaced by $\mathcal I$ |
| §6 | (GP of one ordering)+(NT) suffices deterministically | **false** (Example 4.4: $N=5$, $d=2$, $|\Omega|=16$) |
| §7 | $T_1=2\sum_j{N\brack d+2+2j}$ | **proved under (G)**: Theorem 2.17 plus Lemmas 7.1 and 7.3 (or via Zaslavsky) |
| §7 | "affine slice counts half the chambers" | **false** (smallest: $N=4$, $d=1$, $14\neq12$); correct relation is Lemma 7.3 |
| §7 | $T_2$ universal / given by Theorem 2.17 | **false** (Lean-checked counts: $T_2=4$ vs $2$ at $N=5$, $d=2$) |
| §8 | $T_2=2s$ at $N=d+3$, block-transposition bijection, factor $2$ | **proved under (G)** $\iff$ (Simple) |
| §8 | Geometric "strongly separable splits" characterisation | **proved under (Simple)**, with strict separation |
| §9 | $N=d+2$ reduces to the $k=1$ part of Theorem 1.4 | **proved** |
| §9 | $\mathbb P(N_1=2)=2\mathbb Es/(N-1)!$, $\mathbb P(N_1=0)=1-\mathbb EN_1+\mathbb E\binom{N_1}2$ at $N=d+3$ | **proved** |
| — | Bounds on $s(P)$ (Conjecture 4) | **not addressed**. Side remark: $s=3$ for every simple 4-point $P$ (Corollary 9.1) |
| — | A block-type description of $T_2$ for $N\ge d+4$ (Gale dimension $\ge3$) | **unresolved**; Theorem A(1)–(4) hold there, but §8 uses planarity |
