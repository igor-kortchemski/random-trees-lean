# BGW formalization roadmap — extract for arXiv-2607.22291v1

Extraction date: 29 October 2026.

**Source:** [BGW_FORMALIZATION_ROADMAP.md](BGW_FORMALIZATION_ROADMAP.md). This document retains the parts of that roadmap needed for **P9**, with shared entries narrowed to this manuscript. It preserves the original level of detail and leaves the full roadmap unchanged.

**Target manuscript:** [Rare subtree patterns in size-conditioned Bienaymé trees: Poisson approximation and declumping][P9], Igor Kortchemski and Leonard Vetter, arXiv:2607.22291v1. Source labels and line numbers refer to the locally reviewed TeX source, which is not redistributed in this repository.

The setting is critical offspring in the domain of attraction of a stable law of index $\alpha\in(1,2]$. The relevant foundation is **finite ordered trees, BGW branching, DFS coding, cyclic shifts, conditioned random walks, fringe counts and grafting**. The asymptotic work adds regular variation, local limits and Poisson approximation.

This is a planning document; it does not report completed Lean formalizations.

## 1. Finite trees and representation conventions

Use rooted **plane trees** as the primary objects: vertices have addresses given by finite words of child indices, ancestry is the prefix relation, and children form an initial segment. Child order is essential for DFS and cyclic coding.

For Lean, addresses based on `List ℕ` with children numbered from zero are a reasonable implementation choice, provided the correspondence with the paper's positive child indices is explicit. Prototype subtree restriction and DFS reconstruction before fixing the representation permanently. Finite sets of addresses with tree axioms or a recursive ordered-tree datatype are possible choices; avoid maintaining two unrelated notions of tree.

Keep the tree, its DFS enumeration, its vector of integer increments and its partial-sum path as distinct objects connected by theorems. Subtracting one from an outdegree must use integer subtraction. A tree with $n$ vertices has $n$ increments and $n+1$ path values.

Retain the root, parent, ancestry, children, depth, fringe subtree, leaves, generation sizes, size and grafting operations. Set root depth to zero. Use an ordered list of trees for a finite forest and distinguish its component count from its total size.

Throughout, $\mathbb N=\{0,1,2,\ldots\}$. With $k_T(v)$ the outdegree of $v$, prove the degree-sum identity:

$$
\sum_{v\in T}k_T(v)=|T|-1.
$$

Prove finiteness of the family of plane trees of each fixed size. Start grafting with a tree $C$, a specified leaf $x$, and a tree $S$ inserted there, identifying the original leaf with the inserted root. No separate context datatype is needed initially. Retain the subtree and grafting identities needed by P9's cut-and-graft arguments.

A mark can be a Boolean function $G$ on finite trees. Its count is the finite sum of its indicators over fringe subtrees. A separate framework for arbitrary marks or additive-functional limit theorems is unnecessary.

## 2. DFS coding, rotations and forests

For vertices $u_0,\ldots,u_{n-1}$ in DFS order, define

$$
W_0=0,
\qquad
W_{i+1}=W_i+k_T(u_i)-1.
$$

Prove the tree/excursion equivalence: $W_i\geq0$ for $i<n$, $W_n=-1$, and every such integer path with increments at least $-1$ reconstructs a unique finite plane tree. Prove both inverse identities.

For an ordered forest of $r\geq1$ trees, concatenate increment vectors. The resulting path first hits $-r$ at its terminal time; successive first hits of $-1,\ldots,-r$ recover the component boundaries.

For $1\leq r\leq n$ and integer increments $x_i\geq-1$ summing to $-r$, prove that exactly $r$ cyclic-shift **indices** yield a path first hitting $-r$ at time $n$. Count indices rather than distinct rotated vectors, since periodic vectors can have repeated rotations.

Retain the rotation identity for cyclically invariant nonnegative real-valued observables $F$. For IID integer-valued increments $X_i\geq-1$, partial sums $S_n$ starting at zero, and first hitting time $\tau_{-r}$:

$$
\mathbb E\left[F(X_1,\ldots,X_n)\mathbf 1_{\{\tau_{-r}=n\}}\right]
=\frac rn\,
\mathbb E\left[F(X_1,\ldots,X_n)\mathbf 1_{\{S_n=-r\}}\right].
$$

With $F=1$, obtain Kemperman's identity; with the tree/forest correspondence, obtain Dwass's formula. With positive-probability conditioning, obtain the cyclic representation of conditioned BGW trees by IID bridges.

## 3. BGW law, branching and conditioning

Use an offspring probability law $\mu$ on $\mathbb N$, connected to Mathlib's measure-theoretic probability interface. Keep criticality, aperiodicity, finite variance and stable attraction separate from the basic definitions.

Prove the root branching property and the finite-generation branching facts needed by the paper. Establish the finite-tree mass formula:

$$
\mathbb P_\mu(\mathcal T=T)=\prod_{v\in T}\mu(k_T(v)).
$$

Define fixed-size conditioning only when its normalizing constant is positive, and identify its law with normalized finite-tree weights. State results for admissible sizes.

For the unconditioned finite-tree law, prove the required extinction and normalization result. Here $\mu$ is critical and $\mu(1)\neq1$. Even at mean one, the deterministic one-child law must be excluded from almost-sure finiteness statements. A finite-law construction under these extinction assumptions is sufficient if its branching semantics and agreement with the stopped walk are proved.

Retain prefix conditioning density ratios and bridge splitting. These connect exact finite identities to P9's bridge-removal estimates.

Keep **root leaf-height** separate from ordinary tree height. For $f_\mu(s)=\sum_{k\geq0}\mu(k)s^k$, its recursion is

$$
x_0=1,
\qquad
x_{h+1}=f_\mu(x_h)-\mu(0),
$$

where $x_h$ is the probability that the nearest descendant leaf is at distance at least $h$ from the root.

## 4. Fringe decoding and exact count identities

Prove that the DFS increments beginning at a vertex, stopped at their first cumulative sum of $-1$, encode precisely that vertex's fringe subtree. Source: P9, `eq:fringe`, lines 693–695. Then express a marked fringe count as a sum of cyclic indicators and transfer its law to an IID bridge (`def:indicators` and `lem:RW`, lines 742–764).

The useful probabilistic endpoint is P9's `cor:cyclicshift`, lines 777–824. Let $\xi_i$ be IID with offspring law $\mu$, set $R_0=0$ and $R_m=\sum_{i=1}^{m}(\xi_i-1)$, and define $\Psi_m(a)=\mathbb P(R_m=a)$. Set $\Psi_m(a)=0$ for negative $m$, and sample a uniform vertex by an independent uniform DFS index. For a Boolean mark $G$:

$$
\mathbb P\bigl(G(\mathcal T^n_{U_n})=1\bigr)
=\frac{\mathbb E\left[\mathbf 1_{\{G(\mathcal T)=1\}}\Psi_{n-|\mathcal T|}(0)\right]}{\Psi_n(-1)}.
$$

Use an almost-surely finite unconditioned tree law here, or first state the equivalent finite sum over tree sizes at most $n$. Require $\Psi_n(-1)>0$.

For a fixed finite tree $t$ with $m\leq n$ vertices, this yields

$$
\mathbb E\left[\#\{v\in\mathcal T^n:\mathcal T^n_v=t\}\right]
=n\,\mathbb P(\mathcal T=t)\frac{\Psi_{n-m}(0)}{\Psi_n(-1)}.
$$

This is the natural first probabilistic endpoint for this extract: it combines trees, coding, conditioning and a meaningful statistic without stable-limit machinery.

## 5. Rare patterns and declumping

Retain fringe decoding, the exact count formula, root-mark propagation and cut-and-graft bounds. For a mark of probability $\pi$, the branching property gives the root-event identity

$$
\widehat\pi
=\mathbb E\left[\mathbf 1_{\{D\in B\}}\bigl(1-(1-\pi)^D\bigr)\right],
$$

where $D$ is the root degree and the event is that $D\in B$ and some child subtree is marked (P9, `eq:parent_formula`, line 2220). This is reusable independently of Poisson approximation.

The full `thm:PoissonApproximation` needs microscopicity `(M)`, pair non-clustering `(C)`, Chen–Stein bounds and bridge-removal estimates. With $\pi_n$ the unconditioned mark probability, bounded $n\pi_n$ gives approximation by a Poisson law of mean $n\pi_n$ in total variation, while $n\pi_n\to\infty$ gives a law of large numbers.

Structural condition `(S)` is a sufficient route to `(M)`, not a universal property of marks. Declumped counts provide witnesses for some maximum events; the paper explicitly warns that they need not be deterministically equivalent to those events (lines 829–834).

## 6. Analytical prerequisites retained from the roadmap

- **Regular variation:** Potter bounds, uniform convergence on compact multiplicative intervals, and the sum/integral estimates used by P9. Develop only the portion required by its walk and forest estimates.
- **Local limits:** retain the stable central local-limit input, tracking lattice span, admissible endpoints, uniformity ranges and normalization. A lemma with an explicit local-limit hypothesis does not establish that hypothesis for an offspring law.
- **Random-walk tightness:** retain the scaled-walk estimates needed to control short blocks; develop only the consequences used by P9.
- **Probability transfers:** total variation under measurable maps, coupling/error bounds, transfer to event probabilities, and transfer of limiting statements when random objects agree with probability tending to one.
- **Poisson approximation:** Chen–Stein bounds and the conditioned-bridge estimates already identified in §5.

These are substantial prerequisites. A theorem proved conditionally on an unproved analytic input is an intermediate result.

## 7. Implementation order and completion criteria

The applicable milestones from the original roadmap are:

1. **Finite tree foundation:** ordered trees and forests, subtrees, relevant statistics, degree sum, grafting and finiteness of each size class.
2. **Encoding:** DFS/excursion equivalence and forest decomposition.
3. **Cyclic probability:** cycle lemma, rotation identity and Dwass/Kemperman.
4. **BGW interpretation:** branching and a justified finite-tree law, agreeing with the product formula and stopped walk.
5. **Exact fringe counts:** cyclic indicators, the uniform-vertex formula and its count-expectation consequence.
6. **P9's asymptotic development:** the retained analytic inputs, microscopicity/non-clustering, Poisson approximation and declumping, together with root-mark and grafting arguments.

At the original review date, the folder had no Lean project or pinned Mathlib checkout, so no theorem-level availability audit or compilation check had been performed. Relevant starting interfaces retained from that review are [probability mass functions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/ProbabilityMassFunction/Basic.html), [conditional probability](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/ConditionalProbability.html) and [independence](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Basic.html). Before implementation, pin Lean and Mathlib and inspect that revision for the required results.

Keep one repository. The relevant prospective files from the original layout are `BGW/Tree.lean`, `BGW/Coding.lean`, `BGW/Cyclic.lean`, `BGW/Law.lean` and `BGW/Conditioning.lean`, with the paper development under `Applications/`. Create and split files only when their contents justify it. Keep deterministic modules independent of probability analysis and paper modules.

For each milestone, record the mathematical statement, source label, exact hypotheses, Lean declaration and remaining imported dependencies. A finished paper claim should have no remaining `sorry` or newly introduced unproved axiom in its dependency chain, beyond Lean's standard foundational axioms.

Check conventions on singleton trees, stars, paths, binary trees, forests with several components, repeated cyclic rotations and an offspring law with periodic admissible sizes.

## 8. Essential rules for reuse, Mathlib and Palomar

Implementation guidance added 29 October 2026. Recheck submission policies when preparing a contribution.

- **Reusable interfaces:** use Mathlib's probability objects and convergence notions. Review the tree, subtree and BGW-law definitions before building long proofs; document conventions and provide basic rewrite lemmas. Keep deterministic combinatorics, probability and applications separate. Generalize only for concrete needs.
- **Explicit assumptions and complete proofs:** attach criticality, extinction, stable attraction and conditioning positivity only where needed. State unproved analytic inputs as hypotheses. Finished results must have no `sorry` or custom axioms in their dependencies; avoid `native_decide` in proofs intended for Palomar, whose permitted axioms are restricted. [Palomar proof requirements](https://palomar-registry.org/how-to-submit)
- **Reproducible use:** pin compatible Lean/Mathlib versions, commit `lake-manifest.json`, use Lean's module system with deliberate public exports, and run clean builds in CI. Document sources and authorship; prefer Apache-2.0 for the Lean code to align with Mathlib's licensing convention. [Mathlib style guidance](https://leanprover-community.github.io/contribute/style.html)
- **Future Mathlib contributions:** follow its naming and documentation conventions, seek early review of foundational definitions, and contribute small reusable pieces. Contributors must understand AI-assisted code and disclose its use; GitHub/Zulip comments must be human-written under the current policy. [Contribution guidance](https://leanprover-community.github.io/contribute/index.html)
- **Palomar packaging:** `Solution.lean` may import this library at a pinned public GitHub commit and reuse its proofs. `Challenge.lean` must state the result independently using only permitted imports; it cannot simply import arbitrary BGW modules. Its 1,000-line/100-KiB limit concerns the statement and required definitions, not the whole library. Add Comparator configuration and accurate `formalization.yaml` metadata when preparing a submission. [Submission standard](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)

Build the ordinary reusable library first. Keep definitions auditable now; prepare the Palomar presentation once a substantial result is proved.

[P9]: https://arxiv.org/abs/2607.22291v1
