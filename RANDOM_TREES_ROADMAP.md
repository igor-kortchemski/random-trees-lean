# Random Trees in Lean — development roadmap

Scope baseline v1, reviewed 31 October 2026. The intended home is one evolving GitHub
repository, eventually named `random-trees`, with four mathematical areas:
**BGW trees, metric-measure geometry, continuum random trees, and stable trees**.
Develop and review useful pieces here; prepare bounded Tau Ceti proposals when
their statements and dependencies are stable. The whole programme need not be
finished before contributing a first piece.

This document sets the shared priorities. The earlier BGW roadmaps and the three
local Tau Ceti drafts remain detailed references; their original scopes are not
silently enlarged. In particular, the stable-tree programme below is new.
This roadmap does not rename the repository or move existing Lean files.

## 1. One project, four areas

| Area | Responsibility | Dependencies within this library |
| --- | --- | --- |
| `BGW` | Finite plane trees, branching laws, conditioning, walks, fringe subtrees, discrete height and contour | None of the other three areas |
| `MetricMeasure` | Compact probability metric spaces, unrooted and rooted GHP, comparison and convergence tools | No tree-specific dependency |
| `ContinuumTrees` | Real-tree geometry, continuous coding, discrete-to-continuous comparison, Brownian CRT | `MetricMeasure`; `BGW` only for discrete comparison |
| `StableTrees` | Stable random-walk tools, finite Marchal trees, stable height excursions and stable-tree limits | BGW and the shared continuum foundations, as needed by each module |

These are module boundaries, not four packages. Keep the existing `BGW`
namespace and public imports. Add other directories when there is actual code;
do not first rename every declaration or design a universal tree interface.
Stable scalar analysis and finite Marchal algorithms should not import the
continuous stable-tree construction.

## 2. What can actually be reused

Three agents inspected sibling projects, reading theorem statements, proof
bodies and relevant dependency boundaries. The table describes candidate
source proofs, **not code already integrated into this repository**. This was
a source audit, not a new compilation or certification of those projects.
Paths below start at the named project root; filenames without a directory
share the preceding file's directory.

| Source | Concrete reusable material | Boundary to preserve |
| --- | --- | --- |
| **This repository** | `BGW/Tree/`, `BGW/LocallyFinite/`, `BGW/MetricMeasure/`, `BGW/ContinuumTrees/`, `BGW/StableTrees/` | The discrete BGW law, extinction, full generation-history transitions, cycle/forest identities, conditioning, tilting, geometric uniform laws and exact fringe expectations are integrated. G1–G3, C1–C2, and S1 are implemented, including rooted GHP completeness and the C2 transfer in distribution under stated hypotheses. See the implementation table and report for the precise remaining work. Keep the list-of-children API over the current `WType` implementation. |
| **`freezing1`**, also adapted in **`height-paper-full`** | `Freezing1/PlaneBienaymeLaw.lean`, `PlaneBienaymeBranching.lean`, `PlaneGeometricBienayme.lean`: constructed iid-offspring law, branching and `exists_unique_bienaymeLaw` for an arbitrary offspring probability | The carrier contains possibly infinite, locally finite plane trees. Child addresses start at 1; finite BGW addresses start at 0. The deterministic bridge, the topology, pruning and the constructed law with its root-degree law are now proved here; the branching property, uniqueness, the finite-atom formula, the least-fixed-point characterization of extinction and normalization for mean at most one are proved here too; the geometric/uniform-plane-tree specialization is now proved here using Mathlib geometric measures. These are related implementations, not two independent foundations to import. |
| **`freezing2`** | `Freezing2/Geometry/GHPTriangle.lean`, `GHPSeparation.lean`, `GHPCompleteness.lean`, `GHPCompactness.lean`: unrooted GHP metric quotient, Polishness and compact inverse images under forgetting to GH; `Freezing2/Probability/GHPTightness.lean` transports tightness | Whole compact carriers with Borel probability measures; no full-support assumption. The unrooted core and rooted metric, Polishness, scaling and comparison bounds have been integrated here. |
| **`freezing2`** | `Freezing2/Geometry/RealTree.lean`, `GHRealTree.lean`: four-point condition plus completeness and midpoints gives a real tree; GH stability tools | Reuse the geometric proofs. They do not yet construct a tree from a continuous excursion or a Brownian CRT law. |
| **`freezing2`**, with small helpers from **`freezing1`** | `Freezing2/Probability/ProkhorovBounds.lean`, `WeakPerturbation.lean`, `SampledDistanceContinuity.lean`, `SampleDensity.lean`; `Freezing1/FiniteMultisetSampling.lean` | Perturbation of weak limits, continuity of sampled distance laws, empirical measures retaining multiplicities. Density of iid samples requires full support. Extract only the helpers used by a named target. |
| **`arXiv-2607.22291v1 ` / `PoissonDeclumping`** | `PoissonDeclumping/Lukasiewicz/BridgeLaw.lean` (`map_shift_conditioned`), `PoissonDeclumping/Cyclic/UniformVertex.lean` (`uniformFringeLaw_real_eq`): cyclic conditioning and exact uniform-fringe laws | Statements work for arbitrary offspring PMFs using finite-tree weights. Require positive conditioning probability to obtain a probability law; their totalized zero-event definitions are not such a law. Adapt to the existing BGW encoding rather than keep duplicate finite-tree theories. |
| **The same project: stable analysis** | `PoissonDeclumping/Stable/LocalLimit.lean` (`localLimit`, `walkProb_eq_zero_of_not_dvd`), `DensityLaw.lean`, `Normalization.lean`, `FiniteVariance.lean`, `MaximalTightness.lean`, the required `PoissonDeclumping/RegularVariation/` modules, and `PoissonDeclumping/Bridge/ForestEstimates.lean` | A substantial scalar stable toolkit is proved, including the lattice LLT, density identification, regular variation of the normalizer, required Potter/Karamata estimates, tightness of the walk maximum and uniform forest-size bounds. Size lower bounds retain admissibility. See the exact hypothesis boundary below. |
| **`Parking-bis`** | `ParkingThreshold/TotalVariation.lean`, `Pinsker.lean`, `FiniteLaw.lean`, `BorelEstimates.lean`: finite total variation/Pinsker, contraction under kernels, quantitative Borel-weight estimates | A small reserve for concrete applications, not a new mandatory information-theory programme. Some files import parking-specific modules: extract generic statements and proofs, not their whole import graph. |

The stable hypothesis in `PoissonDeclumping/Statements/Defs.lean` is especially
important. `StableDomain μ α a` assumes criticality, nondegeneracy,
$1<\alpha\le2$, a monotone normalizer with $a_n>0$ for $n\ge1$, and scalar weak convergence
$S_n/a_n\Rightarrow Y_\alpha$ to a probability law satisfying
$\mathbb E[e^{-\lambda Y_\alpha}]=e^{\lambda^\alpha}$ for $\lambda>0$.
**The LLT is a theorem derived from this hypothesis, not one of its fields.**
It retains the lattice condition and the lattice-span factor.

`stableDomain_of_finiteVariance` constructs an actual instance at $\alpha=2$,
with $a_n=\sigma\sqrt{n}/\sqrt{2}$. However, the general characterization from
truncated second moments is unfinished. `DomainCharacterization.lean`
constructs a limit from explicit characteristic-function asymptotics; it does
not yet derive those asymptotics in full generality. Functional $J_1$
convergence, a stable Lévy process and its height process are also not supplied
by this scalar toolkit. The available Potter/Karamata bounds concern positive
monotone sequences in their stated exponent ranges; they should not be
advertised as a complete general theory of regular variation.

Other inspected projects are useful as application tests, without expanding
the initial core: `height-paper` / `height-paper-full`, `Parking` /
`Parking-paper`, the Cauchy project `arXiv-2503.07530v2`, and the growth project
`arXiv-2505.16571v2`. Reuse their isolated tilting, concentration or generating
function arguments only when a target needs them. The growth-profile exponent
is not a stable-law index. `CRT-formalization` currently supplies a roadmap,
`GHP-formalization` is empty, and `arXiv-2402.04098v3/LevyMaps.lean` supplies no
implemented Lévy theory.

### Source snapshots and extraction

- Current BGW baseline: commit `d818312f05742621cf0c5b76fca124c93ff1572e` in
  [Bienayme-Galton-Watson-Trees](https://github.com/igor-kortchemski/Bienayme-Galton-Watson-Trees/tree/d818312f05742621cf0c5b76fca124c93ff1572e).
- GHP source: commit `8bace72d36cdf7d250414f3d98acfaa415de23d9` in
  [uniform-attachment-freezing-scaling-limits](https://github.com/igor-kortchemski/uniform-attachment-freezing-scaling-limits/tree/8bace72d36cdf7d250414f3d98acfaa415de23d9), Apache-2.0.
- Cyclic and stable-toolkit source: commit `4b5e36d25347ee548108439235d6fefe8fddf718`
  in [rare-subtree-patterns](https://github.com/igor-kortchemski/rare-subtree-patterns/tree/4b5e36d25347ee548108439235d6fefe8fddf718), Apache-2.0.
- Stable scalar extraction on 1 November uses the later source commit
  `fc5ef722392b1af41e8b9d5fc45d5a521b7823dd`; the inspection snapshot above remains historical.
- Other local sources need an identified snapshot and attribution when ported;
  local source paths alone are not reproducible public dependencies.

For scale: the inspected GHP completeness/compactness closures each contain
21 generic local modules; general BGW existence/uniqueness in `freezing1`
uses 11. In contrast, importing `FinitePlaneUniformLaw` brings in 143 local
modules, and `SampledReconstruction` brings in model-specific freezing code.
Extract their useful generic lemmas instead. Preserve Lean 4.35.0 and the
current Mathlib pin during the first ports, then compile and inspect the
actual exported dependency closures. Do not rebuild mathematics merely to
remove a source project's name from its provenance.

### Implementation checkpoint — 2 November 2026

This table records implementation, without changing the reviewed v1 mathematical scope.
The [formalization report](FORMALIZATION_REPORT.md) contains theorem correspondence and checks.

| Stage | Implemented | Still needed |
| --- | --- | --- |
| B1 | General BGW law, finite bridge, branching/uniqueness, atoms, extinction/classification, PGFs/means and full finite-history transitions | New consequences only when required by consumers |
| B2 | Size and finite degree-count conditioning, marked cyclic identities, bridge/forest identities, tilting and geometric uniform laws | Further consequences as required by consumers |
| B3 | Exact fringe expectations/blocks, height from Łukasiewicz record minima, contours in heights/addresses, exact first visits, continuous interpolation, LCA and vertex graph metric | Further observable consequences when required by consumers |
| G1 | Unrooted Polish GHP quotient, GH projection, compactness and tightness transfer | No further G1 extraction planned |
| G2–G3 | Rooted metric quotient, completeness, separability and Polishness; 1-Lipschitz forgetting, common-source bounds, jointly continuous positive scaling, weak perturbation and continuity of finite iid distance laws | Delivered; add further tools when required by tree limits |
| C1 | Real-tree criterion, compact real-tree coding, root/Lebesgue mass, 6-Lipschitz rooted GHP coding and measured deterministic rerooting | Delivered; random tree laws belong to later stages |
| C2 | Uniform finite-vertex bundles, exact contour embedding and density, uniform vertex sampler, metric/mass comparison, deterministic contour-to-rooted-GHP transfer, and transfer in distribution for random sizes under explicit measurability and size/scale hypotheses | Delivered; conditioned-tree contour invariance principles and their probabilistic inputs remain |
| C3 | Constructed continuous Brownian bridge law, Gaussian residual independence and grid invariance; minimum is negative almost surely; minima on $[0,b]$ and $[c,d]$ are almost surely unequal when $b<c\le d<1$; measurable first-minimum/Vervaat transform and actual law of its coded tree | Uniqueness of the continuous minimum, strict positivity of the Vervaat transform, and identification with the standard excursion/CRT laws |
| S1 | Scalar LLT/density, normalizer regular variation, Potter/Karamata, maximal tightness, finite-variance supplier, walk/forest bridge and uniform local/tail/weighted forest bounds | General attraction characterization when a concrete family requires it |
| S2 | Selection weights and PMF for Marchal selection on a provided finite graph | State-chain construction, exact finite-tree law and Rémy identification |
| S3–S4 | — | Stable height excursion, functional convergence and conditioned tree limits |

## 3. BGW: complete the reusable discrete foundation

| Milestone | Deliverable | Starting point |
| --- | --- | --- |
| **B1 — laws and the finite-tree bridge** | Connect the constructed locally finite BGW tree to finite `BGW.PlaneTree`; prove finite atom weights, generation branching, PGF iteration and extinction. The total mass of finite-tree weights is the extinction probability $q$, not automatically 1. | Current finite API plus the general construction in `freezing1` / `height-paper-full`. |
| **B2 — conditioning and cyclic walks** | Weighted cycle lemma, Dwass/Kemperman for forests, conditional cyclic-bridge law and exponential tilting. Include finitely many degree-count marks and the fixed-size geometric/uniform-plane-tree specialization. | Extract the existing cyclic proofs from `PoissonDeclumping`; retain admissible sizes and multiplicities of rotation indices. |
| **B3 — observables and geometry** | Exact fringe expectations and basic additive recursions; ancestors/LCA, graph distance, discrete height and contour, first-visit and Łukasiewicz-to-height identities. | Current addresses/fringe/DFS, existing exact fringe laws, then the missing height/contour development. |

Specify conditioning events with positive probability. Keep extinction results
valid in their stated mean regime, including the exceptional deterministic
one-child law. Marked conditioning initially includes finite total size; it
does not promise every theorem about conditioning solely on a degree count.
See [Abraham–Delmas](https://arxiv.org/abs/1506.05571) for BGW foundations and
[Kortchemski](https://arxiv.org/abs/1110.2163) for the relevance of marked
conditioning to scaling limits.

## 4. MetricMeasure: extract GHP, then add the rooted interface

| Milestone | Deliverable |
| --- | --- |
| **G1 — existing unrooted core** | Port compact measured spaces, GHP distance, separation, metric quotient, completeness and separability. Port compactness/tightness under forgetting to GH. |
| **G2 — rooted spaces and comparisons** | Construct the rooted counterpart, the forgetful map, correspondence/coupling bounds and joint continuity of positive distance scaling. |
| **G3 — tools used by tree limits** | Perturbation of weak convergence and continuity of finite sampled distance laws. Add empirical-sampling or reconstruction lemmas when a named tree theorem uses them. |

Fix one convention: nonempty compact metric spaces with Borel probability
measures, modulo surjective measure-preserving isometries of the **whole
carrier**. Use ambient cost $d_H+d_P$, and $d(\rho,\rho')+d_H+d_P$ for rooted
spaces. Full support is an additional hypothesis only where needed, not part
of the carrier definition. Scaling changes distances, not total mass; do not
assume exact homogeneity of the Prokhorov term. This follows the compact GHP
framework of [Abraham–Delmas–Hoscheit](https://arxiv.org/abs/1202.5464).

## 5. ContinuumTrees: shared coding, then the Brownian CRT

| Milestone | Deliverable |
| --- | --- |
| **C1 — real trees and continuous coding** | Port the real-tree geometry. For continuous $g:[0,1]\to[0,\infty)$ with zero endpoints, construct the compact tree coded by $d_g(s,t)=g(s)+g(t)-2\min_{[s\wedge t,s\vee t]}g$, its root and the pushforward of Lebesgue probability. Prove coding continuity in rooted GHP and deterministic rerooting. |
| **C2 — transfer from finite trees** | Embed discrete vertices in the contour-coded tree and compare uniform vertex mass with contour mass. Transfer convergence of scaled continuous contours to rooted GHP convergence, including random total size under explicit size/scale assumptions. |
| **C3 — Brownian bridge and Vervaat laws** | Constructed bridge, Gaussian residual independence and grid invariance; almost-sure negativity and unequal minima on $[0,b]$ and $[c,d]$ when $b<c\le d<1$; measurable first-minimum/Vervaat transform and coded-tree law. Still prove continuous-minimum uniqueness and strict Vervaat positivity, then identify the law with the standard excursion and Brownian CRT under convention $T_{2e}$. |

For C2 with random vertex counts $N_k$ and deterministic distance divisors
$b_k>0$, retain $b_k\to\infty$ and $b_k/N_k\to0$ in probability. Require
convergence in distribution in $C([0,1],\mathbb R)$ with the uniform norm of
the contours rescaled to duration 1 and divided by $b_k$. The discrete measures
are uniform on all vertices; the limit carries the excursion's Lebesgue
pushforward.

The geometric and coding stages do not depend on Brownian existence. A theorem
assuming contour convergence is a useful transfer theorem; it does not prove
the conditioned invariance principle. Keep that probability obligation visible
before claiming an unconditional BGW-to-CRT limit. Likewise, a predicate
describing Brownian paths is not a supplier of an existing Brownian law.
Use [Le Gall](https://arxiv.org/abs/math/0511515) for coding and Brownian CRT
conventions, and [Kortchemski](https://arxiv.org/abs/1109.4138) for the connection
with conditioned trees.

## 6. StableTrees: a real fourth direction, developed in stages

Start with $1<\alpha\le2$ and the normalization
$\mathbb E[e^{-\lambda X_t}]=e^{t\lambda^\alpha}$, $\lambda\ge0$.
The Cauchy boundary $\alpha=1$ has different issues and is not included by
silently extending this parameter range.

| Milestone | Deliverable and completion boundary |
| --- | --- |
| **S1 — stable scalar toolkit** | Extract the `PoissonDeclumping` LLT, density and normalizer results, and the resulting uniform forest-size bounds, with their actual attraction hypotheses and periodicity. Keep the finite-variance instance as a concrete example. Complete the missing domain-of-attraction characterization when needed for the first new offspring family. This stage provides no path-space limit theorem. |
| **S2 — finite stable growth models** | Selection weights and the resulting PMF are proved for a provided finite graph. Still define the finite leaf-labelled Marchal state chain, establish its transition probability kernels and exact finite-tree law, and identify the $\alpha=2$ specialization with Rémy after forgetting plane order. This bounded target is not a construction of the continuum stable tree. |
| **S3 — stable height excursion and tree law** | Construct the spectrally positive stable Lévy process and the normalized continuous height excursion $H_\alpha$, including the law and measurability needed to code $T_{H_\alpha}$. Reuse C1 for its rooted measured real-tree realization. An assumed excursion with desired properties does not complete this stage. |
| **S4 — conditioned BGW scaling limit** | Prove the required functional convergence and conditioned height/contour invariance principle. Combine B2, C2 and S3 to obtain the rooted GHP limit of size-conditioned critical BGW trees in the stable domain. Use graph-distance factor $a_n/n$ and uniform mass on all vertices; take limits along admissible sizes. |

For the remaining S2 work, use finite non-plane trees without degree-two vertices, modulo
leaf-label-preserving graph isomorphism. At step $n\ge1$, their leaves are
exactly $A_0,\ldots,A_n$, with $A_0$ the distinguished root. Start with the
edge joining $A_0$ and $A_1$. Edges have weight
$\alpha-1$, vertices of degree $d\ge3$ have weight $d-1-\alpha$, and the total
is $n\alpha-1$. At $\alpha=2$, only the reachable binary shapes have positive
mass. A plane-tree implementation must explicitly forget plane order when
identifying this law. [Curien–Haas, §§1.1 and 1.3](https://arxiv.org/abs/1207.5418v1)
specifies the state space, algorithm and exact law.

The recommended first continuous route is **Lévy/height coding**, because it
serves conditioned BGW limits and uses the scalar work already present. S3–S4
are substantial later milestones. Do not simultaneously undertake a second
construction from the almost-sure Marchal limit; that route and its measured
identification can be added when an application needs them. Primary sources
for the height route are [Duquesne–Le Gall](https://arxiv.org/abs/math/0509558)
and [Kortchemski](https://arxiv.org/abs/1109.4138).

Check the Brownian endpoint explicitly: the scalar $\alpha=2$ convention is
variance 2, whereas C3 uses the CRT coded by twice a *standard* Brownian
excursion. Prove the deterministic rescaling between the two tree conventions;
do not identify them by name. For more general conditioning, separate the law
of the total size from the choice of mass measure: uniform mass on selected
degrees or leaves needs its own comparison with uniform mass on all vertices.

## 7. Practical order and scope control

1. **First integrations (completed):** B1 and G1 were integrated independently.
   The general BGW construction with its finite-tree bridge, and generic GHP
   foundations, are available in this library.
2. **First reusable applications:** B2–B3 and S1 recover conditioning, fringe
   formulas and stable LLTs in the common library. Use one existing paper as
   a downstream consumer to test that the extracted interfaces suffice.
3. **Connect discrete and continuous trees (G2 and C1–C2 delivered):** use the
   rooted GHP and contour-transfer foundations for later invariance principles.
   Develop finite Marchal laws in parallel only if they are the next desired result.
4. **Construct the random continuum objects:** C3, then S3–S4 as their
   probability prerequisites become available. Record missing inputs rather
   than hiding them in an all-powerful assumption structure.

Keep rare-pattern Poisson/declumping, parking, freezing dynamics and specific
height bounds in their paper projects. Their needs guide this library, but
their full models need not become library dependencies. Cut trees,
fragmentations, looptrees, infinite spines and a second stable-tree
construction are not commitments of the first development cycle.

For reuse and eventual Mathlib/Tau Ceti/Palomar work: prefer existing Mathlib
objects, small mathematical imports, explicit hypotheses and documented
normalizations. Keep provenance and licences when porting. Completed exports
must have no proof holes or custom axioms in their dependency closure. Pin
public dependency commits, build affected consumers, and distinguish a proved
conditional theorem from discharged prerequisites. Keep one evolving roadmap
and the existing formalization report; do not add a submission framework now.
When a coherent result is ready, review that destination's current requirements
and prepare its bounded submission separately.

The v1 scope passed a final cross-review by three agents on 31 October 2026.
This records a review of the roadmap and source claims, not fresh Lean verification.
Implementation details and the source inventory can evolve; add later scope
extensions explicitly, with their concrete theorem targets and dependencies.
