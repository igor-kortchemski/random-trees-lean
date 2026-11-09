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

**Execution plan added 5 November 2026:** [Section 8](#8-classical-probability-campaign)
sets out the classical-probability campaign specified by `CLASSICAL_THEORY_INPUTS.md`,
for subsequent execution with Claude as coordinator. It extends S3–S4 and the
Brownian work above. Preparing this plan did not start formalization or refresh
the verification checkpoint.

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

### External public libraries — checked 6 November 2026

Two public Lean libraries were inspected read-only for the classical-probability
campaign (§8). Neither is a dependency of this repository.

| Library | Snapshot inspected | Content and fit | Decision |
| --- | --- | --- | --- |
| [LeanLevy](https://github.com/slink/LeanLevy) | `7e73fd9b23ad52956ec2756a815889a783131ce4`, MIT | Lean 4.32.0, Mathlib `1f165a51` (13 July 2026), no module system; 35 files, about 24,000 lines, no proof holes. Lévy–Khintchine representation, converse and uniqueness; Poisson random measures with σ-finite intensity; pure-jump Lévy processes with càdlàg paths; Kolmogorov extension. | Not needed through CT5. The stable law is in `BGW/StableTrees/Scalar`; Lévy's continuity theorem (`ProbabilityMeasure.tendsto_iff_tendsto_charFun`) and the càdlàg predicate are in the pinned Mathlib; Kolmogorov extension is vendored; route R-F does not use the Lévy–Itô construction, which needs 29 of its 35 files. Possible use in CT7 only: the Poisson random measure slice (`PoissonPointFamily`, `PoissonRandomMeasure` and three supporting files, about 3,000 lines). |
| [MarkovProcess](https://github.com/scottnarmstrong/MarkovProcess) | `2486404169c10c774164626503aba4ed7c1f0da5`, Apache-2.0 | Lean 4.35.0 and the Mathlib commit pinned here, module system, Mathlib as its only dependency, no proof holes in the library. Continuous-path Feller processes: existence and uniqueness from a Kolmogorov moment bound, strong Markov properties, generators, killing, Brownian motion. | No current target. Stable processes have jumps, and Brownian motion is supplied by `vendor/brownian-motion`. If a target needs one of its kernel or strong-Markov results, add it as a Git dependency pinned to a full commit. |

Choose the form of reuse by what the target needs:

- **Direct dependency** when the library matches the pinned Lean and Mathlib,
  uses the module system and its interface fits: a Git `[[require]]` pinned to a
  full commit, imported narrowly through one module of this library.
- **Source port** when the proofs are long and difficult and the interface fits,
  such as LeanLevy's Lévy–Khintchine proof. Keep the upstream licence notice and
  record the snapshot.
- **New formalization with the external proof as a reference** when the
  mathematics is standard and the version gap and interface mismatch would
  require rewriting most of a slice anyway. The Poisson random measure is such a
  case: prefer a Mathlib-style predicate for a Poisson random measure with given
  intensity and an existence theorem to LeanLevy's piece-indexed construction.
  Tau Ceti (checked at `385ec2ddd8ddf8cc779b78c176308cb9c6b55499`) has no
  Poisson random measure either. Credit the reference in the module
  documentation. This is not a rebuild to remove provenance, which the rule
  above still excludes.

Decide the CT7 case when its route for CT.C21–C22 is fixed. Itô's excursion
theorem mainly needs the strong Markov property and a characterization of
Poisson point processes; LeanLevy's results concern its own constructed
measure and do not appear to supply that characterization. External library
declarations must never appear in a Palomar Challenge, whose imports are
limited to Mathlib, Tau Ceti and CSLib. A Tau Ceti contribution can only use
what Tau Ceti or Mathlib contains: contact the authors and check the intentions
registry before proposing material derived from these libraries there.

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

## 8. Classical probability campaign

Prepared **5 November 2026**, at the owner's request: “prepare a roadmap and then
I will execute using Claude orchestrator”. This is the operational plan for that
future execution. The present work changes documentation only. It neither starts
workers on Lean proofs nor authorizes publication, dependency upgrades or edits
to a companion project.

### 8.1 Objective, source and completion boundary

Formalize the classical results specified in
[CLASSICAL_THEORY_INPUTS.md](CLASSICAL_THEORY_INPUTS.md), with genuine constructions
and proofs in this general library, so that the article arXiv:1110.2163v4 can
import them. Preserve all 39 numbered items in the coverage inventory. Results
marked optional in the specification are scheduled after the main application
path; they are not silently removed from the requested full scope. Alternative
proof methods need not all be implemented, but an independently stated theorem
remains an obligation even if another method bypasses its use.

Here **CT.C1–CT.C39** denote the specification's C1–C39. They are different from
this roadmap's existing ContinuumTrees milestones C1–C3. Campaign phases are
**CT0–CT10**. Neither kind of label denotes proof status.

The specification snapshot has SHA-256
`a72b7467be88117460bd288052fbf982b8e0d9eb8943f3a709680dee69e91a7e`.
The copy in `/Users/igor/LeanFormalization/arXiv-1110.2163v4-BGW-leaves`
was identical when this plan was prepared. Its references to “this project”,
`CLAUDE.md`, `cor_Lambda`, `BGWLeaves.vervaat`, `pDens`, and local survey/source
files refer to that **article project**, unless an exact BGW declaration is
separately identified. Do not assume those declarations already live in BGW.

The source specification is a research brief, with uncompiled sketches and
explicitly unverified references. It is not an approved Lean interface or a
proof certificate. Its [read], [std], [D] and [num] tags retain their stated
meaning; numerical checks do not discharge analytic identities. CT0 verifies
the sources needed by the first phase; later source checks are done before their
own interfaces are adopted, rather than blocking all work on every book citation.

The current reproducible verification procedure is `python3 scripts/check.py`.
The last recorded successful checkpoint, **2 November 2026**, covers 170
maintained library/supplier modules and 3,175 constants. This roadmap did not
rerun it. The current checkout contains extensive local changes and untracked
sources; preserve them. Lean remains `leanprover/lean4:v4.35.0`, and Mathlib
remains `56a005855ea17e0b0958f73ec801ae140b0a1679`.

Two completion claims are deliberately distinct:

- **Article-input core complete:** every required classical input has a proved
  supplier, including the excursion/height identifications, and the generic
  adapters suffice for the stated application. Optional results can remain open,
  listed explicitly. This does not certify the article's own proofs.
- **All CT.C1–CT.C39 complete:** every stated result, including deferred optional
  results and strengthened subclaims, has a proved export or an exact checked
  specialization of existing work. No cited input or unproved characterization
  remains in its dependency closure.

Conditional theorems are legitimate intermediate results with their actual
hypotheses. They do not complete a source theorem or construct a limit law.
Defining a `Prop` that states an external theorem does not prove it. Defining an
excursion as a Vervaat image does not prove its agreement with the normalized
Itô excursion.

### 8.2 Library boundaries and mathematical decisions

The general library must remain independent of `BGWLeaves`. The article's
current `CLAUDE.md`, read on 5 November, says that the functional results remain
NOT STATED until the owner requests work there; it also explicitly defers a
cited-input layer. This campaign must not start that layer or modify the article.
Read-only inspection of the relevant mathematical sources and candidate reusable
proofs can inform the library work. Any source port must preserve provenance,
licensing and the repository's mathematical interfaces.

Use these design defaults, subject to independently reviewed mathematical
contracts rather than speculative framework work:

| Decision | Default and obligation |
| --- | --- |
| Path carrier | `D T E` on `Set.Icc 0 T`, using Mathlib's càdlàg predicate. Prove the real-valued theory first; retain generic deterministic lemmas where they cost little. Settle positive-horizon and zero-horizon conventions before dependent interfaces. |
| J1 topology | Keep Billingsley's ordinary time-change metric as the public metric. It is not complete. CT.C3 supplies a compatible complete metric and `PolishSpace` later; never infer `CompleteSpace` for the ordinary metric. |
| Joint paths | Use `D T ℝ × C([0,T],ℝ)^k` internally. Prove the common-time-change comparison with vector-valued J1 when matching the source's joint statement. Coordinatewise J1 convergence alone is insufficient in general. |
| Algebra and measurability | No artificial normed-group structure on J1 paths. Give the carrier its Borel measurable structure once; prove evaluation and cylinder results. Preserve existing finite-tree measurable conventions and explicit observable hypotheses. |
| Valid parameters | Existence-backed stable/process laws require $1<\theta\le2$ and positive horizons. Any totalized definition outside this range must have clearly restricted characterization theorems. Do not copy the unchecked sketches' missing binders or side conditions. |
| Weak convergence | State convergence in `ProbabilityMeasure` or an established distribution API with the actual weak topology. Do not copy sketches that put a bare `Measure.map` into an unspecified neighborhood filter. Support varying sample spaces and prove the measurability needed by actual pushforwards. |
| Stable normalization | $\mathbb E[e^{-\lambda X_t}]=e^{t\lambda^\theta}$, so $X=\sqrt{2}B$ at $\theta=2$. Use corrected admissible normings, retaining lattice/admissibility hypotheses. |
| Excursion normalization | Local time is $-I$; fix $N(\zeta>t)=t^{-1/\theta}/\Gamma(1-1/\theta)$. Construct unit-duration excursions by scaling/disintegration, never by ordinary conditioning on the null event $\{\zeta=1\}$. |
| Height | Construct the height process and its continuous version, including prefix measurability and compatibility under the excursion law. At $\theta=2$, $H=X-I$ under the process law; its excursion version agrees with $X$ under the appropriate excursion law. |
| Tree normalization | Preserve BGW's standard Brownian CRT convention $T_{2e}$ and prove the scaling comparison with $T_{\sqrt{2}e}$. Preserve whole carriers, the existing GHP cost, and uniform vertex mass unless an explicit leaf-mass transfer is proved. |
| Arbitrarily long time | Compact horizons suffice for the article interface. Fluctuation theory and excursion construction require compatible laws for all horizons plus justified localization, or a local càdlàg path carrier. Decide this before CT6; a single law on $[0,1]$ cannot supply unbounded first-passage/excursion constructions. |

Candidate module homes are `BGW/Skorokhod/`, `BGW/Probability/` for genuinely
generic weak-convergence tools, and subdirectories of `BGW/StableTrees/` for the
process, bridge, excursions, height and invariance principles. Keep existing
Brownian work under `BGW/ContinuumTrees/`. These are suggested homes, not a
request to scaffold empty modules or move working declarations. Generic tools
must not import the stable process or the article; use narrow imports and add
public reexports only for checked results.

R-A and R-B are **candidate proof reductions**, not free completed inputs:

- **R-A, CT.C29:** prefer the exact-size argument from CT.C24 and CT.C28 if its
  discrete LLT/absolute-continuity/tail estimates can be proved or extracted
  generically into BGW. Verify admissible-size quantifiers and the actual
  contour/height conclusion. Never import an article theorem back into BGW.
- **R-B, CT.C35:** it requires two limits of the same concrete sequence: excursion
  prefix convergence obtained without CT.C35, and Vervaat-bridge convergence
  also obtained without CT.C35. Then prove equality using CT.C12 and endpoint
  continuity. To deliver CT.C35 in BGW, both routes and their shared witness must
  be available inside BGW. An article-only identification cannot discharge a BGW
  export. Investigate this at CT0/CT7; use a direct excursion/bridge proof if a
  self-contained reduction would require importing the paper's probability
  development. Include the full identification with Itô's law, even when a
  source first identifies a conditioned-positive bridge.

### 8.3 Corrections and source checks before dependent proofs

Resolve the following in the corresponding statement review. They are concrete
planning issues, not newly approved replacements for the specification.

| Issue | Required resolution |
| --- | --- |
| CT.C16/CT.C17 apparent construction cycle | First prove tightness and identification of subsequential finite-dimensional laws. Use a genuine attraction witness to construct the process law, prove uniqueness, then export the FCLT for every qualifying walk. Strong Markov and spectral properties are additional obligations. |
| CT.C22/CT.C26 cycle | Separate the Lévy excursion law and its scaling from the pair involving height. Construct height under the process/excursion measures, then normalize it and prove the joint mixture. |
| CT.C24 scheduled before height | Prove the identity for tests of the Lévy path first. Upgrade to joint path/height tests only after the adapted measurable height functional and compatible versions are proved. |
| CT.C24 continuity argument | The sketch's passage from almost every lifetime to lifetime one needs a justified test class and domination. Establish it for an appropriate continuous/determining class, then extend to bounded measurable tests. Do not assert continuity for arbitrary bounded measurable tests merely from scaling. |
| Brownian pilot | Existing Brownian bridge and Vervaat image laws do not supply continuous-minimum uniqueness, prefix density, Donsker or Itô identification automatically. Track each separately. |
| CT.C33 endpoint claim | Fact (a).3 needs an endpoint case split or a corrected premise. For $f(t)=t$ when $t<1$ and $f(1)=2$, the first minimizing time is $g=0$ and $f$ is continuous there. The displayed map has $V(f)=f$, so $V(f)(1-)=1\ne2=V(f)(1)$. Check the intended interior-minimum version and preserve the discrete terminal-jump convention. This is a direct mathematical witness, not a Lean-checked counterexample. |
| CT.C34 | Independently check the càdlàg continuity proof, including the minimum attained as a value or left limit, continuity at the minimizer, the wrap point and the terminal endpoint. The continuous-path theorem alone does not establish it. |
| CT.C8/CT.C13 | Verify exact Mathlib hypotheses and compactness/tightness directions, including endpoint conventions in oscillation moduli. Schedule CT.C3 earlier if the chosen construction needs Polishness or standard Borel tools. |
| CT.C17 generality | The prose states real-valued iid increments, while the sketch uses integer-valued steps and the existing witnesses concern offspring walks. Deliver the advertised generality or clearly record the intermediate specialization; “no harder” is not a proof. |
| CT.C37 constants | Existing rooted measured constant 6 does not prove the stated GH constant 2. Audit the exact exports, forgetful maps and metric conventions before marking every subclaim reused. |
| Cited inputs and ownership | The specification's assertion that all cited inputs are never about trees conflicts with `CitedDLGTail` itself. Classify it as a classical tree invariance principle, not a path-law existence axiom. Do not create a cited-input layer in the article under its present instructions. |
| Article lattice issue Q10 | Keep the general conditioning claim for arbitrary degree sets as an article-side open issue. This roadmap cannot certify Theorem 8.1(II) merely by supplying the classical theory. |
| N1–N15 and [std] references | Check source scope, theorem numbering, signs, normalization and joint versus marginal conclusions. Keep proposed errata distinct from accepted author rulings. Do not edit the article's erratum ledger during this library campaign. |

### 8.4 Phases and acceptance targets

Phases are dependency milestones, not time boxes. Work may overlap only when the
shared interfaces and required inputs are ready. Each acceptance target also
requires the evidence in §8.7. “Reuse” means an exact checked specialization,
not matching a declaration name in a search result.

#### CT0 — Establish the execution baseline and first contracts

Read `AGENTS.md`, `README.md`, `FORMALIZATION_REPORT.md`, `HANDOVER_CLAUDE.md`, this
section and the specification. Read the Claude orchestration references in §8.8
and the applicable proof/audit skills. Check for other active builds and preserve
the dirty checkout. Run the existing repository check once the build slot is
available; record pre-existing failures separately from campaign changes.

Audit the exact reusable results in the pinned Mathlib, BGW and its suppliers.
Resolve the first path-space contracts, their sources, horizon conventions and
the candidate CT.C33 correction. Record source locators and route decisions in
the existing report/handover; do not create another theorem database. Inventory
the classical sources locally before fetching missing primary texts.

**Acceptance:** current baseline evidence; exact first interfaces independently
reviewed and, where the Claude profile requires it, presented for the owner's
approval; the first worker brief names a feasible target and disjoint owned files.
The roadmap's signatures are sketches and are not that approval.

#### CT1 — Deterministic path space

Implement CT.C1, CT.C5–CT.C7 and CT.C36, with the elementary approximation lemmas
needed for CT.C2/CT.C4. Prove the actual J1 metric, separation, boundedness, the
time-change convergence characterization and the continuous-path embedding.
Prove restrictions, extension/stopping and their precise continuity domains;
time-space scaling must support different spatial factors on different
coordinates. Prove the largest-positive-jump bound, including jumps at the
terminal time.

**Acceptance:** useful ordinary-import examples for a continuous path and a
finite step path; verified endpoint behavior; the deterministic scaling result
needed by Lemma 5.7; no probability assumptions hidden in deterministic lemmas.
After the carrier is reviewed, scaling/continuous-path proofs and jump-functional
proofs can have separate owners.

#### CT2 — Measurable path space and weak-convergence tools

Complete CT.C2 and CT.C4: separability for J1, Borel evaluations and joint
evaluation, and the cylinder characterization with the terminal time retained.
Implement CT.C9–CT.C12, reusing the existing BGW perturbation theorem for CT.C10.
Verify CT.C13's already available directions and obtain the needed subsequence
tools under their actual hypotheses. CT.C9's generic portion can start in
parallel with CT1 because it does not depend on the path carrier.

**Acceptance:** extended CMT, Slutsky on varying probability spaces, approximation
by stopped prefixes, equality of laws from prefixes and from finite-dimensional
distributions, and the countability of fixed jump times. Compose these into a
generic corrected Lemma 5.7 mechanism with a concrete measurable step-path
application inside BGW. This is the first substantial usable milestone; it does
not assert a stable FCLT or any conditioned tree limit.

#### CT3 — Vervaat calculus and the Brownian pilot

Implement CT.C33–CT.C34 after correcting/reviewing their contracts. Include
measurability, endpoint cases, the finite-word correspondence and a comparison
with BGW's existing continuous-loop transform. State the finite-word lemma in
BGW's own walk language; the article can later prove its wrapper agrees.

Use CT.C19 to instantiate the new path API with the existing Brownian process
and bridge. A promising first missing Brownian proof is continuous-minimum
uniqueness: combine the proved strict negativity with the proved inequality of
minima on separated intervals, over countably many rational interval endpoints.
Then prove strict positivity of the Vervaat path. Prove the Gaussian bridge's
prefix-density formula separately and connect it to the new bridge interface.

**Acceptance:** the Brownian process/bridge instances, unique interior minimum,
applicable Vervaat continuity, and prefix density have their own checked exports.
The pilot is not a claim of a Brownian conditioned-tree limit. Donsker waits for
CT5; Itô excursion and classical CRT identification wait for CT8. This phase may
run beside the scalar part of CT4 when ownership is disjoint.

#### CT4 — Stable scalar suppliers and path-law compactness

Complete CT.C15: an unconditional stable scalar law for each valid index, the
semigroup densities, required derivative/kernel estimates, and the Gamma kernel
properties. If relying on a witness proved in the article, re-establish or port
it with its complete generic dependency closure; do not silently assume
existence for each index. Retain explicit checks of the variance-two endpoint.

Prove the sufficiency parts of CT.C8 needed for walk tightness. Prefer a route
that reuses independent-block factorization and existing maximum estimates;
compare Aldous and a direct oscillation-modulus argument before choosing one.
Maximum tightness alone is insufficient. Prove only the needed criterion first,
keeping the remaining advertised criterion/directions on the CT10 inventory.
Advance CT.C3 here if it unblocks the chosen law construction.

**Acceptance:** genuine stable probability suppliers and the convolution law;
an established path-space tightness criterion and its verified walk application;
the compactness/subsequence extraction needed for CT5, without assuming its
limit process exists.

#### CT5 — Stable process and functional limit theorem

Implement the non-circular R-F route: tightness and finite-dimensional limits;
construction of a process law from one qualifying witness; uniqueness; then
convergence of every qualifying walk to that law. Establish consistency for
positive horizons, scaling, no fixed discontinuities and no negative jumps.
Prove the advertised real-increment FCLT, while reusing integer/offspring
specializations where useful. Retain a separate measurable step-path map and
the correct value at the final time.

Prove the simple Markov property needed by the bridge. Schedule the strong
Markov and unbounded-horizon interface explicitly with CT6; the finite-dimensional
characterization does not itself discharge their Lean proofs.

**Acceptance:** CT.C16's constructed law and CT.C17's FCLT, with each outstanding
CT.C16 property identified until proved. The finite-variance specialization now
gives a genuine Donsker result under the chosen normalization. No excursion law
is assumed in this construction.

#### CT6 — Fluctuation theory and stable bridge

Settle the compatible-horizon/local path framework needed for stopping times,
first passage and the later Poisson excursion construction. Prove the strong
Markov property, then CT.C18: regularity, creeping/first passage, the inverse
local-time subordinator, Kendall's identity, duality and continuous unique
minimum. Preserve the sign change from spectrally negative references.

Construct CT.C31 as an actual law on the closed interval. Choose either a
projective bridge construction with a proved terminal limit or a tightness/LLT
construction from discrete bridges; choose the route after inspecting its exact
dependencies. Consistent prefix densities alone do not give the terminal
property. Prove reversal with left limits and the no-fixed-jump property. Combine
the reviewed fluctuation results with prefix absolute continuity to prove CT.C32.

**Acceptance:** strong Markov/fluctuation exports; a bridge law with prefix
density and $X_{1-}=X_1=0$ almost surely; its unique continuously attained interior
minimum; almost-sure continuity of Vervaat. The bridge construction can progress
while independent fluctuation lemmas are proved; its minimum theorem waits for
the relevant CT.C18 inputs.

#### CT7 — Excursions, height and the Gamma identity

Use the following order to remove the specification's circular phase boundary:

1. **CT7a, Lévy excursions:** CT.C20–CT.C23 for the reflected process alone.
   Construct local time, the Poisson excursion law and sigma-finite measure,
   its lifetime normalization, scaled unit excursion, path-only mixture and
   Markov property. Define the excursion carrier, stopped-zero continuation and
   start/end conventions explicitly. Prove CT.C22 E1–E2 at this level.
2. **CT7b, path-only Gamma identity:** prove CT.C24 for tests of the Lévy path
   using Kendall, the excursion Markov property and the lifetime disintegration.
   Supply the test-class/continuity argument recorded in §8.3.
3. **CT7c, height:** implement CT.C26's approximation/exploration construction,
   continuous versions under the process and excursion measures, adapted
   measurable path functional, joint scaling and normalized height excursion.
   State and prove the necessary version compatibility rather than relying on
   an unnamed almost-sure choice.
4. **CT7d, joint laws:** prove CT.C22 E4 for the pair and extend CT.C24 to joint
   tests. Establish positivity, endpoints and all required no-fixed-jump facts
   under the actual constructed laws.

**Acceptance:** constructed normalized and tail excursion laws, the continuous
height supplier, and the full joint Gamma identity, with no `Cited...` premise.
CT7a–b already yield reusable results if the height construction takes longer.
Keep the exploration-process support theory scoped to these targets and CT8.

#### CT8 — Forest and conditioned-tree limits; identifications

Prove CT.C27 on every positive horizon, first for the joint walk/height process
and then the advertised contour component. Prove finite-dimensional convergence, the required height
tightness and the passage between the source's space/time scales and the
project's normings. Prove CT.C28 by excursion extraction: the first long tree
has the right conditional law; random extraction endpoints approximate correctly;
no excursion has the boundary lifetime; localization covers its random end.
Deliver CT.C28 on every positive horizon too, using the stopped-zero excursion
continuation and the corresponding scaled mixture. The unit-horizon statement
is the early consumer target, not the entire stated result.

Deliver CT.C29 by the accepted R-A route or a direct proof, including the joint
height/contour conclusion and its periodic extension along admissible sizes.
Deliver CT.C35 through the self-contained R-B route or a direct bridge/excursion
argument chosen under §8.2. Neither identity may be used
to prove a prerequisite of its own reduction. Finish CT.C30 and CT.C26's
Brownian identification, including the deterministic CRT scaling comparison.

**Acceptance:** the all-positive-horizon forest and size-tail theorems, the
joint exact-size height/contour invariance principle including periodic laws,
Vervaat/Itô law identity and Brownian specialization have unconditional
exports. Keep marginal and joint source claims distinct: a cited theorem about
height/contour does not certify a joint walk/height/contour theorem.

#### CT9 — Geometry, mass measures and the library handoff

Audit/reuse CT.C37–CT.C38 as soon as useful; do not rebuild the existing GHP
theory. Supply missing exact constants or forgetful maps. Prove the general
time-padding/random-size adapters needed to pass from the article's contour
convention to BGW's verified transfer. Preserve the divisor, size-ratio and
measurability hypotheses.

For CT.C39, prove a reusable deterministic coupling/Prokhorov estimate between
vertex and leaf measures and its convergence consequence under explicit leaf
index discrepancy and height-modulus hypotheses. Specify the discrete quantile
convention at zero and one. The article's `cor_Lambda` supplies a later
specialization; it is not a dependency that BGW may import. An application in
BGW can discharge those hypotheses for an actual available model, without
claiming the article's leaf-conditioned theorem.

The final application in CT.C39 is a further full-scope obligation: check the
specialization under the actual leaf-conditioning assumptions, including the
suppliers of the discrepancy estimate and height convergence. A different-model
example does not complete it. At CT0, distinguish the generic library theorem
from that article application. If the necessary suppliers can be proved as
reusable BGW results, include them here; if completing the specialization needs
the article's own functional layer, retain it as an explicit downstream open
obligation until a separately authorized article execution supplies and checks
it. This permits the narrower article-input-core claim, never an unqualified
claim that all CT.C1–CT.C39 and their applications are complete.

**Acceptance:** exact geometry and measure-transfer exports and an ordinary
consumer example showing the library's actual inputs and conclusions. The
article-input core can be reported complete only after the CT8 suppliers and
all required parts of CT9 pass their checks. Give the article maintainer a
precise import/declaration map and remaining article-side obligations; editing
or building that companion is separate work under its own instructions.

#### CT10 — Deferred full-scope results and final reconciliation

Complete CT.C3 if not already needed, CT.C14's general representation theorem
under independently verified hypotheses, and CT.C25's straddling-excursion
construction including its height counterpart. Finish optional subclaims that
the application route bypassed: the other CT.C8 criterion and required converse
directions and CT.C13's converse specialization after Polishness; CT.C15
positivity/negativity-probability and remaining analytic claims; CT.C22 E3;
CT.C32 uniformity of the minimum time; and the vector-valued
formulation of CT.C5 if not already delivered.

Treat the named alternative excursion characterizations in CT.C30 as proof-route
choices unless an equivalence is itself claimed by the selected export. Every
identification actually used by the source-facing results remains mandatory.
Reconcile the entire specification, including unnumbered subclaims and corrected
statements, against exact exports. Explain bypassed source arguments and any
remaining source ambiguity rather than declaring completion from the phase list.

**Acceptance:** all CT.C1–CT.C39 entries and their stated subclaims are accounted
for, including the actual CT.C39 specialization, the full verification passes,
and independent source/proof review supports the precise completion claim.
Publication remains a separate task.

### 8.5 Complete item allocation

This is a static allocation table. Record evolving proof status and evidence in
`FORMALIZATION_REPORT.md`, not in a second parallel checklist. Existing work
remains subject to an exact interface check before its row is marked complete.

| Specification item | Delivery phase | Required boundary |
| --- | --- | --- |
| CT.C1 | CT1 | Actual J1 metric and time-change characterization. |
| CT.C2 | CT2 | J1 separability and needed second countability. |
| CT.C3 | CT4 if needed; otherwise CT10 | Compatible complete metric, Polishness and valid instance arrangement. |
| CT.C4 | CT2 | Evaluations, cylinder sigma-field and joint measurability. |
| CT.C5 | CT1; vector completion by CT10 | Continuous embedding, uniform convergence at continuous limits, joint comparison. |
| CT.C6 | CT1 | Precise continuity sets and coordinatewise rescaling factors. |
| CT.C7 | CT1 | Stopped-prefix approximation at continuous terminal endpoints. |
| CT.C8 | CT4; remaining directions CT10 | Genuine path compactness/tightness, including every advertised criterion. |
| CT.C9 | CT2 | Extended CMT with actual measurability and topology hypotheses. |
| CT.C10 | CT2 | Reuse perturbation; varying-space metric Slutsky. |
| CT.C11 | CT2 | Approximation theorem and prefix-plus-terminal control. |
| CT.C12 | CT2 | F.d.d./prefix determination and countably many fixed jump times. |
| CT.C13 | CT2/CT4; full directions after CT.C3 | Exact Mathlib reuse and specialization. |
| CT.C14 | CT10 | Common-space representation theorem; bypassing it does not prove it. |
| CT.C15 | CT4; remaining subclaims CT10 | Unconditional scalar law, semigroup, kernels and analytic properties. |
| CT.C16 | CT5–CT6 | Constructed process, compatible horizons, scaling, spectrum and Markov properties. |
| CT.C17 | CT5 | Functional convergence with stated increment generality. |
| CT.C18 | CT6 | Every fluctuation fact F1–F6, with correct sign and passage conventions. |
| CT.C19 | CT3; excursion identification CT8 | Brownian instances and prefix density; classical identification separately proved. |
| CT.C20 | CT7a | Reflected process and normalized local time. |
| CT.C21 | CT7a | Actual Poisson excursion theorem and sigma-finite measure. |
| CT.C22 | CT7a/CT7d; E3 by CT10 | Path excursion first, joint height mixture later, all advertised properties. |
| CT.C23 | CT7a | Excursion Markov property with usable integrated form. |
| CT.C24 | CT7b/CT7d | Path-only identity then the full joint Gamma identity. |
| CT.C25 | CT10 | Straddling-excursion path construction and height comparison. |
| CT.C26 | CT7c/CT8 | Constructed continuous height, measurable dependence, scaling, excursions and Brownian case. |
| CT.C27 | CT8 | Actual joint forest invariance principle on every positive horizon, including contour. |
| CT.C28 | CT8 | Size-tail tree theorem on every positive horizon with proved random excursion extraction. |
| CT.C29 | CT8 | Joint exact-size height/contour theorem including periodic laws along admissible sizes, via an acyclic library proof. |
| CT.C30 | CT8 | Classical Brownian excursion/height and tree-normalization identities. |
| CT.C31 | CT6 | Full bridge law including continuous terminal pinning. |
| CT.C32 | CT6; uniformity by CT10 | Unique interior continuously attained minimum; advertised uniform law retained. |
| CT.C33 | CT3 | Corrected general map, measurability, endpoint cases and discrete correspondence. |
| CT.C34 | CT3, applied in CT6 | Càdlàg J1 continuity under independently checked hypotheses. |
| CT.C35 | CT8 | Vervaat image equals the constructed normalized Itô excursion. |
| CT.C36 | CT1 | Largest positive and absolute jump bounds as stated. |
| CT.C37 | Audit early; finish CT9 | Existing coding plus exact GH/GHP constants and forgetful comparisons. |
| CT.C38 | Audit early; finish CT9 | Verified contour transfer and generic convention adapters. |
| CT.C39 | CT9; application handoff if needed | Generic vertex/leaf coupling and transfer; full completion also needs the checked actual leaf-conditioned specialization, with ownership resolved at CT0. |

### 8.6 Dependency order and parallel work

```text
CT0 -> CT1 -> CT2
CT2 -> CT3
CT2 -> CT4 -> CT5 -> CT6
CT6 -> CT7a -> CT7b
CT7a -> CT7c
CT7b + CT7c -> CT7d -> CT8 -> CT9

CT.C9 generic work can overlap CT1.
CT.C15 scalar work can overlap CT1–CT3.
CT.C37–CT.C38 reuse checks can happen early.
CT3's deterministic core can overlap CT2; its full measurability uses CT2.
CT7b and CT7c share CT7a; CT7d requires both.
CT8's C35 also requires CT3 and CT6, through the chosen acyclic route.
CT.C3 moves earlier if required; CT10 closes the deferred full scope.
```

The graph is an overview; the item table and the selected reviewed proof route
determine actual dependencies. In particular, CT8 must not consume CT.C35 through
a theorem used to prove CT.C35. Build constraints can make writing more agents
counterproductive even when the mathematics is independent.

Recommended initial assignment after CT0:

- One owner for the path carrier/J1 metric and shared definitions.
- One independent worker for generic extended CMT or the scalar semigroup work,
  whichever has a reviewed dependency-ready contract.
- One reviewer for the exact source-facing contracts and their semantic
  definitions. Review remains independent of authorship; a repairer cannot
  provide that repaired result's independent review.

Add further workers only when there are independent, sufficiently large tasks
and the single compilation slot is not already the bottleneck. Keep all existing
project/client/profile caps; this recommendation is not a new concurrency limit.
Only the coordinator launches workers. Workers request a reassignment or help
rather than starting another agent.

Use a short worker brief with the following fields; this is a template, not a
request for another tracking system:

```text
Target: exact declaration(s), phase and source locator.
Interface: approved/reviewed statement and relevant semantic definitions.
Inputs: proved reusable lemmas and any explicit interim hypotheses.
Ownership: exact files; shared definitions and aggregates owned by coordinator.
Route: proposed argument, known obstacles and previous failed approaches.
Checks: proposed focused command and affected consumers; coordinator executes.
Constraints: no holes/new axioms, unchanged pins, no child workers, one build.
Return: changed files, reusable progress, check output reference, open obligations.
Stop/handoff: structural blocker or two materially different failed approaches.
```

### 8.7 Proof acceptance and evidence

The development checkout supplies the `lean-workflow` and `lean-statement-audit`
procedures used at the named interfaces. See the [public evidence](docs/evidence/README.md)
for the verification records associated with this library.

1. **Before substantial dependent work:** a reviewer who did not author the
   interface reconstructs the source statement and checks the exact elaborated
   types, semantic definitions, quantifiers, normalizations, endpoint cases and
   necessary identifications. Reuse unaffected reviews. Apply the selected
   Claude profile's key-statement approval rule as described in §8.8.
2. **During proof work:** the coordinator runs focused dependency-aware builds,
   such as `lake build BGW.Skorokhod.Basic` once that module actually exists.
   Only one Lean/Lake validation runs at a time, including auditor probes. Keep
   its source/dependency inputs stable. Workers continue reading or editing
   unrelated files. A bare `lake env lean` does not refresh stale imports.
3. **At integration:** review the diff, compile the actual exports and affected
   consumers, and inspect their axiom closure. No `sorry`, `admit`, custom axioms,
   `native_decide`, `bv_decide` or `unsafe` in maintained Lean. Only `propext`,
   `Classical.choice` and `Quot.sound` are permitted in the checked closure.
4. **At a coherent milestone:** run `python3 scripts/check.py`. It discovers
   current BGW modules, exercises public consumer files, audits private/generated
   declarations and checks documentation. Add only useful examples for new public
   interfaces, without creating a separate test framework. Do not rerun the full
   check after every helper.
5. **Before claiming the milestone:** independently review the substantive proof
   route and source correspondence, distinguishing corrected claims and
   alternative arguments. Update `FORMALIZATION_REPORT.md` with exact exports,
   results, review evidence and remaining obligations. Update README scope only
   when delivered scope changes.

No implementation test or source audit was run for this roadmap. Its review is
about coverage, ordering and operational compatibility. A future whole-scope
claim also requires a fresh omission scan against the specification and the
selected primary sources. Comparator/publication checks belong to a later
requested publication task; do not introduce Challenge holes or a submission
framework during this campaign.

### 8.8 Claude orchestration and project compatibility

The owner has selected **Claude as the future coordinator** for this campaign.
This is a campaign-specific execution choice; it does not rewrite the installed
Codex skill profile or enlarge external-provider authorizations. Use the local
`lean-orchestrator` skill and its Claude profile from the development checkout
at startup, alongside this repository's instructions. The reviewed profile
snapshot has SHA-256
`f41c01572019ca7cdce5d499bc6653e573e0f9e8461eacf92ecfa62e24253476`;
check subsequent changes before relying on its settings. Do not replace the
project's `.agents` skills or install new configuration merely to execute this plan.

The profile currently selects an Opus coordinator at `xhigh`, native Sonnet
reviews, and Codex proof workers, with Sol for hard obligations. Apply its actual
supported controls when the campaign starts and report unavailable settings.
This roadmap does not launch those processes or claim a model/effort change.
Read the profile's worker guide before using external workers; keep their briefs
bounded and their ownership disjoint.

Project-specific precedence and adaptations:

- **One build, including probes.** The repository's coordinator-only Lean/Lake
  rule is stricter than the Claude profile's parallel targeted-build allowance
  and the article project's build cap. Use one compile slot across the entire
  campaign; the article's higher limit does not apply here.
- **No frozen proof holes.** The profile's freeze phase allows registered
  `sorry` bodies only “as the project's draft policy allows”. BGW allows none.
  Record approved exact statement text in the existing plan/report and use
  permitted hole-free elaboration probes or explicit parameterized interfaces.
  Add a maintained theorem only with its proof. Do not introduce a new axiom,
  Challenge hole or registered `sorry` to scaffold this campaign. Preserve any
  existing approved interface without creating a second sealing system.
- **Exact key-statement approval.** The profile's “Campaign phases”, step 3,
  says: “Present the exact declarations to the user for approval.” If executing
  under that profile, batch the concrete reviewed key declarations and obtain
  that approval before assigning their dependent proofs. This requirement comes
  from the linked profile; the roadmap and its sketches are not such approval.
  Ordinary helpers and completed milestone transitions do not acquire an extra
  approval gate. If the owner explicitly changes this rule for the campaign,
  record and follow that instruction while retaining independent fidelity review.
- **Provider scope.** The profile's Open Math OS default is conditional on
  authorization for that provider and project material. This roadmap supplies
  none; use its existing authorized fallback when that condition is unmet.
  Do not transfer the article project's special quota exceptions or provider
  permissions to BGW. Existing project authorization for Anthropic reviews and
  the owner's future launch instructions retain their exact scope.
- **Resources and quotas.** Read the selected profile's actual applicable limits
  at startup and before new waves. Retain user budgets and existing reserve
  rules. Missing readings are unknown, not zero usage or renewed quota. Do not
  invent a new budget or install a polling/controller service.
- **Escalation.** After two materially different failed approaches, hand the
  exact obstruction, reusable work and evidence to the coordinator. Diagnose
  mathematics, representation or elaboration before changing effort. Follow
  the selected profile's bounded escalation and human-arbitration rules;
  continue independent branches while a genuine blocker is unresolved.

**Owner rulings for execution, 6 November 2026.** The owner started the campaign
asking for minimal human intervention and answered two setup questions:

- **Approval gate replaced by audits.** Key statements no longer wait for the
  owner's approval. Each passes an independent Sonnet statement audit; the main
  shared interfaces also get one read-only GPT‑Sol audit and a blind read-back.
  The verdicts are recorded in `FORMALIZATION_REPORT.md`. The coordinator still
  asks on a genuine source ambiguity or when a frozen statement turns out wrong.
- **Local checkpoint commits.** Work happens on the local branch
  `campaign/random-trees`, committed at the baseline and at each verified
  milestone. Nothing is pushed; the coordinator alone commits.

Compilation follows `AGENTS.md`: a worker runs only the compilations its brief
pre-grants. The one-build rule is kept by a lock: every Lean/Lake command of the
campaign, the coordinator's, workers' and auditors' alike, runs through
`python3 .orchestration/bin/lake_gate.py <lake arguments>`, which runs one at a time.
Approved statement texts live in `.orchestration/contracts/` as `sorry` probes
outside the library; a maintained file reproduces them verbatim with proofs,
and sealing compares the two before `freeze_check.py` records the sealed
declarations.

At each handoff, use `HANDOVER_CLAUDE.md` for the active phase, owned files,
accepted contracts, validation output references, failed approaches, pending
reviews and the next bounded target. Keep proof coverage in
`FORMALIZATION_REPORT.md`. Use §8.9 below as the single place for this campaign's
operational recommendations; do not create a duplicate recommendations file.

### 8.9 Estimates and operational recommendations

The specification's core totals are approximately **26.5–51.5 thousand Lean
lines**, before optional work, integration and corrections. These are planning
estimates, not measured time/token budgets. Its “0 lines via R-B” does not include
the identification argument and the work needed to make that reduction
self-contained. Excursion/exploration theory and height tightness are the major
uncertainties. Re-estimate after CT2, CT5 and the first complete CT7 slice using
actual validated work; do not promise a completion date from line counts.

| Observation | Suggested adjustment | Scope and limitation |
| --- | --- | --- |
| The path carrier is shared by almost every later phase; the repository serializes compilation. | Start with two independent writing tasks and one reviewer, as in §8.6; keep one shared-interface owner. | Planning recommendation, not a measured optimum or an override of profile caps. |
| Excursion/height and process/FCLT dependencies must be split before delegation. | Assign CT7a before CT7d and the common tightness/f.d.d. kernel before CT.C17's final export. | Based on the specification's own dependency list and the read-only planning review. |
| Existing Brownian interval-minimum results offer a bounded pilot before general fluctuation theory. | Try the countable rational-interval argument for continuous-minimum uniqueness. | Candidate route; no proof or performance result is claimed here. |

At future milestones, replace or refine these suggestions with evidence from
actual worker handoffs, validation costs, repairs and available usage. Record
actual models/efforts and missing usage honestly. Do not run extra benchmarks
solely to populate this table.

### 8.10 Launch prompt for the owner

Start Claude in `/Users/igor/LeanFormalization/BGW-formalization` with the
intended orchestrator available, then use the following prompt. Supplying it is
the later execution step; preparing this document did not execute it.

```text
Use the Claude lean-orchestrator to execute section 8 of RANDOM_TREES_ROADMAP.md
for CLASSICAL_THEORY_INPUTS.md, with full proved coverage of CT.C1–CT.C39 as the
eventual objective. Start with CT0 and the first dependency-ready CT1/CT2 work.

Read AGENTS.md, README.md, FORMALIZATION_REPORT.md, HANDOVER_CLAUDE.md and the
roadmap before starting. Read the local Claude orchestration skill and profile
linked in section 8.8; apply their settings subject to this repository's rules.
Preserve all existing local changes and dependency pins. Only the coordinator
runs Lean/Lake, with one validation at a time, including audit probes. No proof
holes or new axioms are allowed, including for frozen declarations.

Follow the phase acceptance targets and independent statement/proof reviews.
Present concrete reviewed key declarations as required by the selected profile;
do not treat this roadmap as approval of unchecked Lean signatures. Continue
dependency-ready work through the planned phases within the applicable limits;
milestones are verification points, not automatic requests for fresh permission.

Keep BGW independent of the article project. Do not edit that project, start its
cited-input layer, publish, push, upgrade dependencies or activate a new external
provider under this instruction. Preserve R-A/R-B only when their actual proof
dependencies are acyclic and available in the library. Track conditional helpers
and missing identifications honestly until their suppliers are proved.

Maintain proof status in FORMALIZATION_REPORT.md, active handoff state in
HANDOVER_CLAUDE.md and operational advice in roadmap section 8.9. At a required
stop, preserve the exact validated state, useful unvalidated work and the next
bounded task. Do not claim full completion while any in-scope obligation remains.
```
