# A Lean library for BGW trees: proposed scope and roadmap

Review date: 29 October 2026.

**Status:** final review complete; ready to freeze as a planning baseline. Three agents reviewed mathematical statements, source alignment, and scope; identified issues were corrected and rechecked.

**Recommendation.** Build a reusable library alongside the paper formalizations. The strongest common foundation in this collection is **ordered trees, product weights, Łukasiewicz coding, cyclic shifts, and conditioned random walks**. A first release proving exact identities in this foundation would already be useful. Full scaling limits and condensation theorems should be later applications, with their substantial analytic prerequisites made explicit.

**Review scope.** Three agents reviewed three main manuscripts each, using the local TeX sources, theorem statements, prerequisite sections, and selected proofs; their findings were synthesized and key recommendations cross-checked. The nine primary manuscripts are listed below. Old versions, referee reports, illustrations, and the reference PDFs under `15.Max degree/Biblio` were not treated as additional target manuscripts or exhaustively reviewed. This is a dependency and design review, not a verification of every proof. Source labels and line numbers refer to the current local files, and may differ from published versions.

At review time, this folder contains no Lean project, pinned Mathlib dependency, or Git repository. This document proposes work; it does not report completed Lean formalizations. The existing papers have not been modified.

**Literature follow-up, 29 October 2026.** Three agents also checked external primary texts against this roadmap. The additions are deliberately small: additive fringe-sum recursion, finite-depth cylinder probabilities, and prescribed degree-profile enumeration. Two existing targets are made more precise: leaf-grafting counts and finite-depth size bias. Sources and exact locators appear beside the statements below. These fit existing components and do not add a release milestone. The larger topics in this document are dependencies to revisit when needed, not an instruction to implement them now.

## 1. What the papers have in common

The references in this table link to public manuscripts. Subsequent references such as **P2, `prop:K`, lines 544–562** identify a precise place in the locally reviewed TeX source; line numbers may differ between versions. Local manuscript copies are not redistributed in this repository.

| ID | Manuscript | Regime and main endpoint | Most useful material to extract |
| --- | --- | --- | --- |
| P1 | [A simple proof of Duquesne's theorem on contour processes of conditioned Galton-Watson trees][P1], Igor Kortchemski | Critical, aperiodic offspring; stable index in $(1,2]$; fixed total progeny; height and contour limits | Tree/path coding, Kemperman identity, finite-prefix changes of measure, height/contour comparison |
| P2 | [Invariance principles for Galton-Watson trees conditioned on the number of leaves][P2], Igor Kortchemski | Critical stable offspring; leaf conditioning and extensions to degree-set counts | Ordered forests, marked cycle lemma, joint size/leaf distribution, leaf-to-size comparison |
| P3 | [Limit theorems for conditioned non-generic Galton–Watson trees][P3], Igor Kortchemski | Subcritical mean $0<m<1$; local tail $\mu(k)=L(k)k^{-1-\theta}$ with $\theta>1$; condensation and logarithmic height | Forest decomposition at the maximal vertex, infinite-degree limit trees, total variation transfer |
| P4 | [Sub-exponential tail bounds for conditioned stable Bienaymé–Galton–Watson trees][P4], Igor Kortchemski | Critical stable offspring of index in $(1,2]$; uniform width, height and degree bounds | BFS and reverse DFS coding, queue bounds, cyclically invariant observables, size bias and spines |
| P5 | [Condensation in critical Cauchy Bienaymé–Galton–Watson trees][P5], Igor Kortchemski and Loïc Richier | Critical mean $1$; Cauchy attraction; different results under exact-size and at-least-size conditioning | Survival recursion, first-passage and ladder identities, Cauchy centering, largest-jump approximation |
| P6 | [Large deviation Local Limit Theorems and limits of biconditioned Trees and Maps][P6], Igor Kortchemski and Cyril Marzouk | Product-weight trees with both size and leaf count fixed; several scaling regimes | Arbitrary nonnegative weights, tilting, bridges with marks, split-and-shuffle representation |
| P7 | [Critical trees are neither too short nor too fat][P7], Louigi Addario-Berry, Serte Donderwinkel and Igor Kortchemski | Universal critical height/width results; sharper asymptotics under a local Cauchy assumption | Degree multiset law, BFS bounds, conditioned concentration, bridge to labelled trees |
| P8 | [Condensation in subcritical Cauchy Bienaymé trees][P8], Igor Kortchemski and Leonard Vetter | Subcritical mean; local Cauchy tail; condensation, maximal-vertex depth and logarithmic height | Exact-size tilt invariance, reuse of condensation transfer arguments, survival-to-height transfer |
| P9 | [Rare subtree patterns in size-conditioned Bienaymé trees: Poisson approximation and declumping][P9], Igor Kortchemski and Leonard Vetter | Critical stable offspring of index in $(1,2]$; microscopic rare marks with non-clustering hypotheses | Fringe coding, marked counts, uniform-vertex fringe formula, grafting, root-mark recurrences |

The overlap is substantial enough to justify a library rather than nine isolated developments. P8 explicitly reuses the approach of P3 once a different random-walk estimate is established. P9 uses the same cyclic-shift machinery as the earlier conditioning papers. P6 also shows that the common combinatorial probability layer should accommodate **weights that are not initially probability distributions**.

## 2. Representation choices to settle first

### Ordered trees, with a route to infinite degree

Use rooted **plane trees** as the primary objects: vertices have addresses given by finite words of child indices, ancestry is the prefix relation, and children form an initial segment. Child order is essential for DFS, BFS, reverse DFS, cyclic coding, and the first vertex attaining a maximal degree. An abstract graph modulo isomorphism would obscure these operations.

For Lean, addresses based on `List ℕ` with children numbered from zero are a reasonable implementation choice, provided the correspondence with the papers' positive child indices is explicit. This is a proposal, not a requirement imposed by the sources. Prototype subtree restriction and DFS reconstruction before fixing the representation permanently.

For the first implementation, finite sets of addresses with the tree axioms are a plausible choice. A recursive ordered-tree datatype is another option, but should have a proved address representation if used. Avoid maintaining two unrelated notions of tree.

There must eventually be a general tree space whose children may be finite or infinite. **P3 explicitly permits infinite outdegree** in its definition, lines 357–379, and its local limit has an infinite-degree vertex (`thm:local`, lines 739–751). A type that permanently builds local finiteness into every tree cannot express this theorem. Keep the finite address representation compatible with a later set-of-addresses extension, but implement that extension only when a selected theorem needs it. The first finite combinatorial proofs need not construct the infinite-tree probability space.

For later local convergence, choose a topology that can express condensation limits, for example through finite address-membership observations. Stabilization of entire finite-radius balls is unsuitable when the limiting root has infinitely many children.

### Separate a tree from its traversal and its encoding

Keep the tree, its DFS or BFS enumeration, the vector of integer increments, and the partial-sum path as distinct objects connected by theorems. Increment vectors should use integers: subtracting one from a natural-number outdegree must not use truncated natural subtraction.

For a tree with $n$ vertices, there are $n$ increments and $n+1$ path values. Set the root depth to zero and the singleton height to zero. State explicitly how the height process is extended at its terminal index and how a contour is extended beyond its natural length $2(n-1)$.

Use an ordered list of trees for a finite forest. Distinguish a forest's number of components from its total number of vertices. When maxima are involved, specify whether the forest is nonempty.

### Keep hypotheses separate

Do not bundle criticality, aperiodicity, finite variance, or stable attraction into the basic tree or offspring-law definitions. The reusable finite identities usually need none of them.

In particular:

- Critical and subcritical Cauchy offspring laws in these papers have **finite mean**. The stable limit's index $1$ does not imply infinite offspring mean.
- A local assumption such as $\mu(k)\sim L(k)/k^2$ is stronger than the corresponding tail/domain-of-attraction assumption. P5 uses the distinction between exact-size and at-least-size conditioning; P7 and P8 require local regularity for their sharper Cauchy results.
- Every conditioned law must record positivity of its normalizing constant. State results for admissible sizes before adding optional aperiodicity hypotheses.
- Leaf counts can have additional lattice constraints. Aperiodicity of the original offspring law does not automatically remove them; P2 discusses this near `thm:ltn`, lines 864–883.
- Exact-size conditioning, at-least-size conditioning, leaf conditioning, and joint conditioning are different constructions with different transfer theorems.

## 3. Reusable definitions and theorems, in priority order

Here, **first** means suitable for the initial library; **next** means useful once that foundation works; **later** means a substantial further development. These are relative priorities, not calendar estimates.

| Component | Definitions and theorem targets | Priority | Main users |
| --- | --- | --- | --- |
| Finite trees and forests | Root, parent, ancestry, children, depth, subtree, grafting, size and component count | First | All papers |
| Tree statistics | Generation sizes, height, width, maximal degree, leaves, counts of degrees in a set | First | All papers |
| Product weights | Tree weights, positive partition functions, fixed-statistic normalized laws, tilting | First | P3, P6, P8; useful throughout |
| Łukasiewicz coding | DFS enumeration, valid excursions, reconstruction, forest concatenation, height from records | First | All papers |
| Cyclic combinatorics | Rotations, good rotation indices, cycle lemma, discrete Vervaat transform | First | All papers |
| Finite probabilistic identities | Rotation-invariant product laws, marked Kemperman/Dwass, conditioned bridges | First, after coding | All papers |
| BGW law and branching | Offspring law, full tree law, root decomposition, finite-tree mass formula, extinction | Next; develop alongside the finite core | All probabilistic applications |
| Fringe and marked counts | Fringe decoding, count as a cyclic sum, uniform-vertex identities, one-hole grafting | Next | P9; useful in P3, P5, P8 |
| BFS and contour | Queue/width bounds, mirror traversal, discrete contour and height comparison | Next | P1, P2, P4, P7 |
| PGFs and survival | Generation recursion, survival recursion, elementary height bounds, forest maxima | Next | P3, P5, P7, P8, P9 |
| Conditioning tools | Prefix density ratios, bridge splitting, leaf shuffling, degree multiset laws | Next | P1, P2, P6, P7, P9 |
| Size bias and spines | Pointed trees, size-biased offspring, truncation and expectation identities | Next/later | P4 and local-limit arguments |
| Probability transfers | Total variation under maps, coupling/error bounds, independent forest approximation | Next/later | P3, P5, P7, P8, P9 |
| Heavy-tail analysis | Regular variation, local limits, large deviations, Cauchy normalizations | Later, driven by a chosen theorem | Most asymptotic results |
| Continuous limits | Stable processes, bridges, excursions, height processes, Skorokhod convergence | Later | P1, P2, P3, P5, P6 |
| Specialized applications | Foata–Fuchs, Poisson declumping, looptrees, maps and metric scaling limits | Later, separate modules | P5, P6, P7, P9 |

### A. Elementary identities worth proving immediately

Throughout, $\mathbb N=\{0,1,2,\ldots\}$. For a nonempty finite tree $T$, write $k_T(v)$ for outdegree, $Z_h(T)$ for generation size, $H(T)$ for height, $\operatorname{Width}(T)$ for width, and $\Delta(T)$ for maximal outdegree. Prove:

$$
\sum_{v\in T} k_T(v)=|T|-1,
\qquad
\sum_{h=0}^{H(T)} Z_h(T)=|T|.
$$

$$
|T|\leq 1+H(T)\operatorname{Width}(T),
\qquad
\Delta(T)\leq\operatorname{Width}(T).
$$

Define degree-set counts once:

$$
N_A(T)=\#\{v\in T:k_T(v)\in A\}.
$$

Leaves are $N_{\{0\}}(T)$ and total size is $N_{\mathbb N}(T)$. Add identities under subtree restriction, forest concatenation and grafting. Start grafting with just a tree $C$, a specified leaf $x$, and a tree $S$ inserted there. No separate context datatype is needed initially. The original leaf is identified with the inserted root, giving

$$
N_A(C[S]_x)+\mathbf 1_{\{0\in A\}}=N_A(C)+N_A(S).
$$

This addition form avoids natural-number subtraction. Source: [Abraham–Delmas, *Local limits of conditioned Galton–Watson trees I*, §5.1, p. 12](https://arxiv.org/pdf/1304.4035v4#page=12). It makes the existing grafting target precise for P2/P6 degree counts and P9 surgery arguments.

**Small literature addition: additive fringe sums.** For a real-valued function $f$ on finite trees, define

$$
F_f(T)=\sum_{v\in T}f(T_v).
$$

If $T_1,\ldots,T_d$ are the root-child subtrees, prove

$$
F_f(T)=f(T)+\sum_{i=1}^{d}F_f(T_i).
$$

Indicators give fringe counts; a function of the root degree gives degree-set counts. There are no probability or moment assumptions. This is the elementary part of [Janson, *Asymptotic normality of fringe subtrees and additive functionals in conditioned Galton–Watson trees*, §1, equations (1.3) and (1.6), p. 2](https://arxiv.org/pdf/1312.1211v1#page=2). Add the finite-sum definition and recursion in the tree module; the paper's central limit theorems are outside the present scope. Do not extend the preceding leaf-grafting formula to arbitrary $f$: grafting also changes the fringe trees of ancestors.

These identities are recommended infrastructure, including facts the papers use without separate statements. Sources include P2's forest and coding sections, P4's height/width argument near line 318, and P9's cut-and-graft development near lines 2497–2512.

### B. Finite weights and conditioning

For nonnegative finite weights $w_k$, define

$$
\operatorname{weight}_w(T)=\prod_{v\in T}w_{k_T(v)}.
$$

Prove that the family of plane trees with $n$ vertices is finite, then define the weighted law on any specified subfamily with positive total weight. Start with fixed size; extend to fixed size and degree-set counts. Finiteness of a size class does not require the weight sequence itself to have finite support.

This construction supports simply generated trees directly and later agrees with BGW conditioning when $w=\mu$. It is useful before constructing the full unconditioned BGW law. Sources: P6, lines 1202–1226; P8, `prop:tilting`, lines 208–210.

### C. Łukasiewicz coding and geometry

For vertices $u_0,\ldots,u_{n-1}$ in DFS order, define

$$
W_0=0,
\qquad
W_{i+1}=W_i+k_T(u_i)-1.
$$

Prove the tree/excursion equivalence: $W_i\geq0$ for $i<n$, $W_n=-1$, and every such integer path with increments at least $-1$ reconstructs a unique finite plane tree. Prove both inverse identities, not only existence of a decoder.

For an ordered forest of $r\geq1$ trees, concatenate increment vectors. The resulting path first hits $-r$ at its terminal time; successive first hits of $-1,\ldots,-r$ recover the component boundaries.

The ancestor-count formula is especially valuable:

$$
H_i=\#\left\{j:0\leq j<i,\ W_j=\min_{j\leq k\leq i}W_k\right\}.
$$

It converts height into a path-prefix statistic. Source: P2, `eq:Hmes`, lines 515–516. For maximal degrees, prove $\Delta(T)=1+\max_{i<n}(W_{i+1}-W_i)$, with a declared tie-breaking rule when identifying the first maximal vertex.

Add BFS after DFS. With the actual exploration queue $Q_i=W_i^{\mathrm{bfs}}+1$, a useful bound is

$$
\operatorname{Width}(T)\leq\max_{0\leq i<n}Q_i\leq2\operatorname{Width}(T).
$$

P4 proves this form in `eq:bfs`, lines 705–709. Contour interpolation and the identity $b_i=2i-H_i$ belong in a later deterministic module; P1 uses them at lines 878–884.

### D. Cycle lemma and conditioned bridges

For $1\leq r\leq n$ and integer increments $x_i\geq-1$ summing to $-r$, prove that exactly $r$ cyclic-shift **indices** yield a path first hitting $-r$ at time $n$. Count indices rather than distinct rotated vectors: periodic vectors can have repeated rotations in the forest case. Sources: P2, lines 518–542; P4, lines 534–542.

For $r=1$, define the discrete Vervaat transform by the first minimum among $W_1,\ldots,W_n$, with an explicit endpoint convention: a minimum attained first at the terminal index induces the zero rotation modulo $n$. Keep this finite construction separate from the much harder continuous Vervaat transform.

Then prove a weighted rotation identity for cyclically invariant nonnegative real-valued observables $F$. For $1\leq r\leq n$, IID integer-valued increments $X_i\geq-1$, partial sums $S_n$ starting at $S_0=0$, and first hitting time $\tau_{-r}$,

$$
\mathbb E\left[F(X_1,\ldots,X_n)\mathbf 1_{\{\tau_{-r}=n\}}\right]
=\frac rn\,
\mathbb E\left[F(X_1,\ldots,X_n)\mathbf 1_{\{S_n=-r\}}\right].
$$

An integrable real-valued version can follow. With $F=1$, obtain Kemperman's identity; with the tree/forest correspondence, obtain Dwass's formula. With marked increments, obtain leaf and degree-count identities. With positive-probability conditioning, obtain the Vervaat representation of conditioned BGW trees.

This stronger observable-level theorem is more reusable than separate proofs for size, leaves and maximal degree. Source: P4, `lem:shifts`, lines 526–556.

### E. BGW construction and branching

Use an offspring probability law $\mu$ on $\mathbb N$, connected to Mathlib's measure-theoretic probability interface. Write $m=\sum_{k\geq0}k\mu(k)$ when finite mean is assumed. A candidate full construction assigns independent offspring variables to the countable address space and determines which addresses belong to the tree through their ancestors. Prove measurability and the branching property rather than treating them as implicit.

**Small literature addition: finite-depth probabilities.** First construct the tree through a fixed generation $h$. If $r_h$ retains generations $0,\ldots,h$ and $t$ is a finite tree with $H(t)\leq h$, prove

$$
p_h(t):=\mathbb P(r_h(\mathcal T)=t)
=\prod_{\substack{u\in t\\ |u|<h}}\mu(k_t(u)).
$$

Vertices at level $h$ contribute no factor: their offspring are unobserved. This needs no criticality, mean or extinction assumption. A depth-$h$ realization is finite, but the set of possible realizations is generally countably infinite, unlike a fixed-size class. Source: [Abraham–Delmas, *An introduction to Bienaymé–Galton–Watson trees and their local limits*, §2.2.1, equation (10), p. 6, version 3](https://arxiv.org/pdf/1506.05571v3#page=6). This supplies a concrete interface for branching and truncation; first state further-generation independence through finite cylinder events, without developing general conditional kernels or stopping lines.

Prove the finite-tree formula

$$
\mathbb P_\mu(\mathcal T=T)=\prod_{v\in T}\mu(k_T(v)).
$$

Then identify the normalized finite weighted law with the conditional BGW law. For general offspring laws, finite-tree weights need not sum to one: in the supercritical case they account only for extinction. Even at mean one, the deterministic one-child law must be excluded from almost-sure finiteness statements. Prove the required extinction/normalization result before packaging a law on finite trees as an unconditional probability law.

Standard foundational targets include the generation recursion, $\mathbb E[Z_h]=m^h$ under finite mean, the PGF composition law, extinction as the least fixed point of the offspring PGF in $[0,1]$, and almost-sure extinction for mean at most one with $\mu(1)\neq1$. These are recommended supporting theorems, not new results of the reviewed papers.

For height survival probabilities, the papers directly use

$$
Q_h=\mathbb P(Z_h(\mathcal T)>0),\qquad
Q_0=1,\qquad
Q_{h+1}=1-f_\mu(1-Q_h),
$$

where $f_\mu(s)=\sum_{k\geq0}\mu(k)s^k$ for $s\in[0,1]$. For finite trees, $Q_h=\mathbb P(H(\mathcal T)\geq h)$; the generation-event definition also works before an infinite-tree height is defined. Sources: P5, `eqn:recurrence`, lines 426–431; P8, lines 462–465. Derive $Q_h\leq m^h$ for subcritical finite mean. For $r\geq1$ independent almost-surely finite BGW trees with this offspring law, prove

$$
\mathbb P\left(\max_{1\leq i\leq r}H(\mathcal T_i)<h\right)=(1-Q_h)^r.
$$

Keep root leaf-height separate from tree height. Its different recursion, useful in P9, is $x_0=1$ and $x_{h+1}=f_\mu(x_h)-\mu(0)$, where $x_h$ is the probability that the nearest descendant leaf is at distance at least $h$ from the root.

### F. Exact identities that connect directly to these papers

**Joint total size and leaf count.** For $r$ independent BGW trees, total size $p$ and total leaf count $\ell$, prove P2's `prop:K`, lines 544–562:

$$
\mathbb P_\mu^{(r)}(|\mathcal F|=p,\ N_{\{0\}}(\mathcal F)=\ell)
=\frac rp\,
\mathbb P(B_p=\ell)\,
\mathbb P(S'_{p-\ell}=\ell-r),
$$

where $B_p$ is binomial with parameter $\mu(0)$ and $S'$ has nonnegative increments with law $\mu(j+1)/(1-\mu(0))$. Record $p\geq r\geq1$, $0\leq\ell\leq p$, and $\mu(0)<1$; handle degenerate cases separately. Its proof combines the marked cycle lemma with a finite decomposition according to which increments equal $-1$.

**Biconditioned split-and-shuffle.** Formalize P6's `lem:separation_sauts`, lines 1269–1280. Fix $1\leq K\leq n$ and nonnegative real tree weights $\theta$ with $\theta(0)>0$. A corresponding bridge with $n$ steps and $K$ negative steps can be constructed by independently sampling a nondecreasing bridge of length $n-K$ ending at $K-1$, with increment weights $p(j)=\theta(j+1)$ for $j\geq0$, and uniformly choosing the $K$ negative-step positions. If $L_j$ counts those positions up to $j$,

$$
W_j=S_{j-L_j}-L_j.
$$

The result is finite and exact; it requires positive normalizers for the sampled laws. Together with $\theta(0)>0$, these ensure that the target law is defined. It is a good first distinctive application of the shared library.

**Fringe decoding and counts.** Prove that the DFS increments beginning at a vertex, stopped at their first cumulative sum of $-1$, encode precisely that vertex's fringe subtree. Source: P9, `eq:fringe`, lines 693–695. Then express a marked fringe count as a sum of cyclic indicators and transfer its law to an IID bridge (`def:indicators` and `lem:RW`, lines 742–764).

The useful probabilistic endpoint is P9's `cor:cyclicshift`, lines 777–824. Let $\xi_i$ be IID with offspring law $\mu$, set $R_0=0$ and $R_m=\sum_{i=1}^{m}(\xi_i-1)$, and define $\Psi_m(a)=\mathbb P(R_m=a)$. Set $\Psi_m(a)=0$ for negative $m$, and sample a uniform vertex by an independent uniform DFS index. For a Boolean mark $G$,

$$
\mathbb P\bigl(G(\mathcal T^n_{U_n})=1\bigr)
=\frac{\mathbb E\left[\mathbf 1_{\{G(\mathcal T)=1\}}\Psi_{n-|\mathcal T|}(0)\right]}{\Psi_n(-1)}.
$$

Use an almost-surely finite unconditioned tree law here, or first state the equivalent finite sum over tree sizes at most $n$. Require $\Psi_n(-1)>0$. For a fixed finite tree $t$ with $m\leq n$ vertices, this yields the particularly concrete formula

$$
\mathbb E\left[\#\{v\in\mathcal T^n:\mathcal T^n_v=t\}\right]
=n\,\mathbb P(\mathcal T=t)\frac{\Psi_{n-m}(0)}{\Psi_n(-1)}.
$$

This is an attractive early library demonstration: it combines trees, coding, conditioning, and a meaningful statistic without any stable-limit machinery.

**Conditional degree multiset.** Prove that the outdegree multiset of $\mathcal T^n$ has the law of $n$ IID offspring values conditioned on their sum being $n-1$. This concerns the multiset, not the ordered DFS sequence. Source: P7, `rk:degrees`, lines 572–575. Use it as the common interface for degree extremes and concentration.

**Small literature addition: counting a prescribed degree profile.** Let $1\leq r\leq n$, with finitely supported counts $a_j\in\mathbb N$ satisfying $\sum_j a_j=n$ and $\sum_j j a_j=n-r$. For the set $\mathcal F_{r,a}$ of ordered plane forests with $r$ components and these outdegree counts, prove

$$
\#\mathcal F_{r,a}=\frac rn\frac{n!}{\prod_j a_j!}.
$$

Source: [Pitman, *Combinatorial Stochastic Processes*, §6.2, Exercise 6.2.1, equations (6.18)–(6.19), p. 129](https://www.stat.berkeley.edu/~aldous/206-Exch/Papers/pitman_CSP.pdf#page=130). For Lean, first prove the division-free identity $n\,\#\mathcal F_{r,a}=r\,\operatorname{multinomial}(a)$. The tree case is $r=1$. As an immediate consequence, a product-weight law conditioned on a positive-weight profile is uniform on that profile: all its forests have the same product weight. This is a corollary of the already planned cycle lemma, useful for P4 forests and P7 degree conditioning; it needs no separate allocation model or counting framework.

## 4. A concrete first release

**First complete theorem: exponential-tilt invariance at fixed size.** This is P8's `prop:tilting`, and has a weighted analogue in P6. If

$$
\mu(k)=a\lambda^k\nu(k),\qquad a>0,\quad\lambda>0,
$$

then every tree $T$ of size $n$ satisfies

$$
\operatorname{weight}_\mu(T)
=a^n\lambda^{n-1}\operatorname{weight}_\nu(T).
$$

The degree-sum identity supplies the exponent $n-1$, and the common factor cancels when the fixed-size weights are normalized. Start with this weighted statement; later derive equality of the conditional BGW laws. No stable attraction, finite variance, or infinite-tree construction is needed for the weighted theorem. Under fixed size and fixed leaf count, also prove invariance under a separate positive multiplier on the leaf weight.

The proposed first release can proceed through these independently reviewable milestones:

1. **Finite tree foundation:** ordered trees and forests, subtrees, degree-set counts, degree sum, grafting identities, and finiteness of each size class.
2. **First probability interface:** positive weighted normalizers and tilt invariance, with singleton, path, and star examples.
3. **Encoding:** DFS/excursion equivalence, forest decomposition and the ancestor-count formula.
4. **Cyclic probability:** cycle lemma, weighted rotation identity, Vervaat, and a finite weighted version of Dwass/Kemperman.
5. **BGW interpretation:** full branching construction or a justified finite-law construction under extinction assumptions; prove agreement with the earlier weights and the stopped walk.
6. **Two useful applications:** the joint size/leaf-count identity and the exact fringe-count expectation. The split-and-shuffle identity is a natural next addition.

Milestones 1–4 can make progress without first formalizing an infinite random tree. Milestone 5 must resolve normalization and semantics before the finite constructions are advertised as a full unconditioned BGW library. There is no need to finish a paper's main asymptotic theorem to make this release mathematically valuable.

## 5. How the full papers would build on that release

The following are routes through the papers, not claims that the listed prerequisites are already formalized.

**P1: contour-process invariance.** After coding, prove the exact-versus-at-least-size absolute-continuity relation (`lem:AC`, lines 579–592) and deterministic contour/height comparison. The complete endpoint additionally needs a stable local limit theorem, regular variation, and the Duquesne–Le Gall invariance theorem used in `thm:cvW`, lines 745–750. A proof conditional on that theorem would be an intermediate result, not a complete formalization of the paper.

**P2: leaf conditioning.** First target `prop:K`, then degree-set counts, leaf-to-size concentration, and the appropriate lattice arithmetic. Later targets are leaf-count asymptotics (`thm:ltn`), coding-process convergence (`thm:cvG` and the full-interval Łukasiewicz theorem `thm:cvW3`, lines 1986–1994), and maximal degree (`thm:max`). The general degree-set extension (`thm:general`, lines 2494–2508) has additional restrictions, including a finite or cofinite degree set in the infinite-variance case; preserve them.

**P3: subcritical condensation.** Extract the deterministic cut at the maximal jump (`prop:links`, lines 684–691), then a generic theorem transferring a bridge approximation into an approximately independent descendant forest (`prop:tilde` and `cor:indep`, lines 696–713). Use these in the maximal-degree and logarithmic-height arguments. The geometric-depth proof additionally uses generalized local convergence and tightness of the first maximal vertex's DFS index (lines 760–769). That local convergence requires the infinite-degree tree space. Stable fluctuations and metric non-tightness need additional analytic and geometric machinery.

**P4: uniform tail bounds.** BFS geometry and the cyclic-observable identity are the best initial targets. The main width, height and degree bounds (`thm:width`, `thm:height`, `thm:degree`) then need uniform walk deviations, conditioned-bridge estimates, and, for the height argument, size-biased/spine tools. The generic size-biased offspring law uses normalization by a positive finite mean; immortal-spine and subcritical condensation constructions should not be conflated.

When this proof needs size bias, start at finite depth. For $0<m<\infty$, use offspring law $k\mu(k)/m$ along a marked ancestral line, choose its continuing child uniformly, and use ordinary offspring law $\mu$ elsewhere. For a finite tree $t$ with $H(t)=h$ and $v\in t$ at depth $h$, the pointed truncation mass satisfies

$$
p_h^*(t,v)=m^{-h}p_h(t),
\qquad
\sum_{\substack{v\in t\\ |v|=h}}p_h^*(t,v)=\frac{Z_h(t)}{m^h}p_h(t).
$$

This is [Lyons–Pemantle–Peres, *Conceptual proofs of L log L criteria for mean behavior of branching processes*, §2, equations (2.1)–(2.2), p. 4](https://arxiv.org/pdf/math/0404083v1#page=4). It sharpens the existing spine target without requiring an infinite spine or martingale-limit theory first. Implement it when P4 needs it, not as another first-release requirement.

**P5: critical Cauchy condensation.** Separate the tail-assumption/at-least-size branch from the local-assumption/exact-size branch. Reusable targets include finite-path time reversal and the last weak ladder-time identity (`lem:In`, lines 503–515), ladder-time decompositions, survival recursion, and total variation approximations (`prop:dTV1`, `thm:dTVLoc`). The main looptree, depth and ranked-degree limits (`thm:loop-local`, `thm:height-local`, `thm:degrees-local`) require Cauchy renewal estimates, continuous processes, and in places Poisson random measures and metric geometry.

**P6: biconditioning.** The finite bridge tilting lemma (`lem:tilting`, lines 755–773), marked Vervaat lemma (`lem:vervaat`, lines 1240–1254), and split-and-shuffle lemma provide a substantial exact foundation. The local limit and bridge convergence theorems have distinct bulk, small-endpoint, large-endpoint and stable regimes. Preserve those hypotheses rather than packaging them as one unspecified limit theorem. Planar-map applications, starting near line 1606, belong beyond the initial BGW library.

**P7: universal critical geometry.** The degree multiset identity and BFS queue bounds are immediate beneficiaries of the common library. Medium-stage targets include the subexponential cost of conditioning (`lem:probtree`, line 981), negligible high-degree mass (`lem:nomasshighdegrees`, line 1024), and bridge concentration (`prop:width_bound`, line 1061). The general height result uses a separate labelled-tree representation and the Foata–Fuchs bijection; first prove the link from randomly labelled plane trees (`prop:planetrees`, line 1175). Keep the general critical theorem separate from the sharper Cauchy theorem under `eq:hypmu`.

**P8: subcritical Cauchy condensation.** This is a useful test of reuse: supply the new Cauchy one-large-jump estimate to the P3 transfer layer, then derive condensation and height results. The source is short, but its external local large-deviation and survival-asymptotic prerequisites are substantial. The main theorem distinguishes logarithmic height convergence from tightness of the centered height, the latter holding precisely under the extra condition $\sum_k k\log(k)\mu(k)<\infty$ (`thm:main`, lines 149–163). Do not silently inherit stronger height conclusions from another regime.

**P9: rare patterns.** Start with fringe decoding, the exact count formula, root-mark propagation, and cut-and-graft bounds. For a mark of probability $\pi$, the branching property gives the root-event identity

$$
\widehat\pi
=\mathbb E\left[\mathbf 1_{\{D\in B\}}\bigl(1-(1-\pi)^D\bigr)\right],
$$

where $D$ is the root degree and the event is that $D\in B$ and some child subtree is marked (P9, `eq:parent_formula`, line 2220). This is reusable independently of Poisson approximation. The full `thm:PoissonApproximation` needs microscopicity `(M)`, pair non-clustering `(C)`, Chen–Stein bounds and bridge-removal estimates. With $\pi_n$ the unconditioned mark probability, bounded $n\pi_n$ gives approximation by a Poisson law of mean $n\pi_n$ in total variation, while $n\pi_n\to\infty$ gives a law of large numbers. Structural condition `(S)` is a sufficient route to `(M)`, not a universal property of marks. Declumped counts provide witnesses for some maximum events; the paper explicitly warns that they need not be deterministically equivalent to those events (lines 829–834).

## 6. Shared analytical work to plan separately

**Regular variation.** Prioritize Potter bounds, uniform convergence on compact multiplicative intervals, sums and integrals, truncated moments, tail equivalences, and inverse normalizing scales. P1, P2, P3 and P4 already isolate parts of this toolkit. Prove only the portion required by the first chosen asymptotic theorem before attempting a comprehensive theory.

**Local limits and large deviations.** Track lattice span, admissible endpoints, uniformity ranges, centering, and normalization in the statement. Central local limits, large-deviation local estimates, and one-large-jump estimates are distinct inputs. A lemma with an explicit local-limit hypothesis can be useful, but does not establish that hypothesis for a particular offspring law.

**Cauchy centering.** The truncated-mean centering

$$
b_n=n\,\mathbb E\left[X\mathbf 1_{\{|X|\leq a_n\}}\right],
\qquad n\mathbb P(X\geq a_n)\longrightarrow1
$$

cannot generally be replaced at fluctuation scale by $n\mathbb E[X]$. P8 explicitly discusses this near line 281. P7 also notes that its sign convention for $b_n$ is opposite to that in P5. Give the shared definitions one convention and prove the translation lemmas.

**Probability transfers.** Total variation decreases under measurable maps, errors transfer to event probabilities, and agreement on events of probability tending to one transfers limiting statements. Package these generic arguments once, including for vectors whose dimensions depend on $n$. The shared condensation layer should accept a precisely formulated largest-jump/forest approximation theorem, while separate modules establish it for each tail regime.

**Continuous objects and topology.** Full invariance principles require laws on path spaces, tightness, weak convergence, stable Lévy processes, bridges and excursions, and continuous height processes. Metric-space applications add Gromov–Hausdorff or Gromov–Hausdorff–Prokhorov convergence. These are major dependencies even when a paper cites their existence in a single sentence.

## 7. Mathlib reuse and verification status

This folder has no pinned Mathlib checkout, so **no theorem-level availability audit or compilation check has been performed**. A small check of the official online documentation confirms relevant starting interfaces:

- [Probability mass functions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/ProbabilityMassFunction/Basic.html): `PMF`, normalization, and conversion to measures.
- [Conditional probability](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/ConditionalProbability.html): event conditioning and the hypotheses under which it is a probability measure.
- [Independence](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Basic.html): independent families and random variables.
- [Strong law of large numbers](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/StrongLaw.html): an existing general result to reuse when an argument needs it.

These are entry points, not evidence that a particular BGW proof will compile without additional infrastructure. No absence claim is made for BGW constructions, regular variation, local limit theorems, stable processes, Chen–Stein bounds, or relevant tree combinatorics. Before implementation, pin Lean and Mathlib, inspect that revision for the required objects, and record which components can be reused, adapted, or must be developed.

General-purpose list/rotation lemmas, probability identities, regular-variation results, and convergence tools may be suitable Mathlib contributions. Tree-specific interfaces and the paper developments can remain in the BGW repository. Upstreaming should follow working proofs rather than block the first coherent release.

## 8. Minimal organization and completion criteria

Keep one repository. Begin with `BGW/Tree.lean` and `BGW/Weighted.lean` for the first target. As the subsequent milestones require them, a small layout could become:

```text
BGW/
  Tree.lean          # Finite trees, forests, statistics, subtree operations
  Weighted.lean      # Fixed-size weights and tilting
  Coding.lean        # DFS paths and reconstruction
  Cyclic.lean        # Rotations and the cycle lemma
  Law.lean           # Offspring, finite-depth laws and BGW interpretation
  Conditioning.lean  # Exact identities using the preceding components
Applications/        # Add a Lean application when its proof begins
```

This is a proposed organization, not a scaffold to create in advance. Split files only when their actual contents justify it. The deterministic modules should not import probability analysis or paper modules. Keep paper-specific assumptions in application files. Use `Applications/` for Lean files and retain `papers/` for the manuscripts, avoiding a case-only folder-name distinction.

**Scope after the literature check.** Add the three small ingredients and two refinements above inside existing milestones. Do not create separate frameworks for random allocations, arbitrary marks, generic branching models, or additive-functional limits. Janson's [*Simply generated trees, conditioned Galton–Watson trees, random allocations and condensation*](https://arxiv.org/abs/1112.0510) is a useful reference for the existing weighted/cyclic core, not a mandate to implement its entire classification. Root-degree formulas can be added as consequences of branching and forest Dwass when an application needs them.

Also defer Rizzolo's additional degree-set tree transformation: [*Scaling limits of Markov branching trees and Galton–Watson trees conditioned on the number of vertices with out-degree in a given set*, §3.1, Theorem 6](https://arxiv.org/pdf/1105.2528v2) constructs a related offspring law to study degree-set counts. The marked cycle identity already serves the immediate joint size/count targets here. Keep infinite-tree topology, stopping-line branching, multitype processes and analytic limit theories tied to a specific later paper theorem.

For each milestone, record the mathematical statement, source label, exact hypotheses, Lean declaration, and remaining imported dependencies. Distinguish a completed theorem from a theorem conditional on an unproved analytic assumption. A finished paper claim should have no remaining `sorry` or newly introduced unproved axiom in its dependency chain, beyond Lean's standard foundational axioms.

Before enlarging the scope, check the public definitions on singleton trees, stars, paths, binary trees, forests with several components, repeated cyclic rotations, and an offspring law with periodic admissible sizes. These examples target genuine boundary and convention risks rather than duplicate the main proofs.

## 9. Source conventions and apparent inconsistencies to resolve

These observations concern the local manuscripts. They are reasons to reconstruct exact finite statements from definitions and consult the final published version when implementing; they are not a claim that the papers' asymptotic conclusions fail.

| Source location | Observation | Formalization consequence |
| --- | --- | --- |
| P4, `eq:D`, line 282, and the convergence near line 292 | Height is multiplied by $n/B_n$, whereas its own tail threshold is $un/B_n$ and P1's theorem, lines 866–870, uses multiplier $B_n/n$ | Check the version and use a single consistent height normalization |
| P7, `eq:width`, line 401 | With $W_0=0$ and increments $k-1$, the displayed bound $\operatorname{Width}(T)\leq\max W$ fails for a singleton and a star | Use the queue $Q=W+1$; P4's `eq:bfs` includes the offset |
| P7, `eq:boundH`, around lines 681–688 | The displayed upper bound omits a root-to-child edge when descendant trees are rooted at children of the maximal vertex; a star exposes the discrepancy | Derive the bound from exact grafting-height equations, retaining the $+1$ |
| P3, prose at line 877 versus `prop:lp`, lines 879–880 | The prose gives $\log(1/m)$ for the limit of $H(T_n)/\log n$, while the height theorem and moment formula give its reciprocal | Preserve the consistent constant $1/\log(1/m)$ after checking the source version |
| P5, line 433 versus line 482 | The same tail-sum ratio $\ell^*/L$ is said to tend to zero and later to infinity | Resolve the conflicting statements before importing the scale-separation argument |

**Recommended next implementation task.** Prototype finite plane trees, prove the outdegree-sum identity, define positive fixed-size weighted laws, and prove exponential-tilt invariance. Then use the tree/excursion equivalence and cycle lemma to reach the joint leaf-count and exact fringe-count formulas. This would establish a small, coherent library that directly serves the manuscripts already in this folder.

[P1]: https://arxiv.org/abs/1109.4138v3
[P2]: https://arxiv.org/abs/1110.2163v4
[P3]: https://arxiv.org/abs/1205.3145v4
[P4]: https://arxiv.org/abs/1504.04358
[P5]: https://arxiv.org/abs/1804.10183v3
[P6]: https://arxiv.org/abs/2101.01682v3
[P7]: https://arxiv.org/abs/2311.06163v2
[P8]: https://arxiv.org/abs/2503.07530v2
[P9]: https://arxiv.org/abs/2607.22291v1
