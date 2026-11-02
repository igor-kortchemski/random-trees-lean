# Random Trees in Lean

A Lean 4 library for finite and locally finite BGW trees, compact metric-measure
geometry, continuum-tree coding and scalar stable-law tools. It is in development;
the API may change, so downstream projects should pin a published commit.

Start with this finite-tree consumer example:

```lean
module

import BGW

open BGW.PlaneTree

example : (node [leaf, leaf]).size = 3 := by
  simp
```

The public aggregate imports the four areas. For smaller dependencies, start with:

| Area | Useful starting imports |
| --- | --- |
| BGW trees | `BGW.Tree`, `BGW.LocallyFinite.Law`, `BGW.LocallyFinite.SizeConditioning` |
| Metric-measure geometry | `BGW.MetricMeasure` |
| Continuum trees | `BGW.ContinuumTrees.CodingMeasure`, `BGW.ContinuumTrees.ContourLawConvergence` |
| Stable trees | `BGW.StableTrees` |

These are module entry points rather than separate packages. See the [formalization
report](FORMALIZATION_REPORT.md) for the verified scope and the detailed module table below.
Checked public-consumer examples are in [BGWTest/Examples.lean](BGWTest/Examples.lean)
and [BGWTest/Measurability.lean](BGWTest/Measurability.lean).

## Conventions

| Topic | Convention |
| --- | --- |
| Finite-tree addresses | Zero-based child indices; root address `[]` |
| Locally finite tree addresses | Positive child indices, converted explicitly from finite trees |
| Size and uniform vertex | Size counts vertices; uniform mass samples all vertices, including the root |
| Contour coding | Contours are rescaled to the unit interval |
| GHP carrier and cost | Whole carrier retained even without full measure support; GHP costs use sums |
| Extinction and size conditioning | Condition on positive-mass sizes; extinction is certain for mean at most one except the deterministic one-child law (`μ {1} = 1`) |
| Brownian CRT normalization | The target convention is $T_{2e}$ for normalized excursion $e$ |
| Stable index two | The finite-variance specialization uses variance $2$ |

## Use from a sibling checkout

For a local consumer beside this repository, add the valid path dependency below to
its `lakefile.toml`. Use the same `lean-toolchain` and Mathlib revision as this library:

```toml
[[require]]
name = "bgw"
path = "../random-trees-lean"
```

The repository is [random-trees-lean](https://github.com/igor-kortchemski/random-trees-lean).
For a Git dependency, use this repository URL and pin the complete commit SHA you
intend to use. The Lake package remains `bgw` and Lean imports remain `BGW`.

This initial snapshot continues the development previously hosted in
[Bienayme-Galton-Watson-Trees](https://github.com/igor-kortchemski/Bienayme-Galton-Watson-Trees),
based on commit `d818312f05742621cf0c5b76fca124c93ff1572e`, with the subsequent
locally verified additions described in the formalization report.

## Contributing

Keep Lean and Mathlib pins in sync with `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json`; add imports at the narrowest useful module boundary. Document
mathematical conventions and state clearly which results remain open. The common
repository check is `python3 scripts/check.py`. Do not use `sorry` or introduce new
axioms to close a proof. The [random-trees roadmap](RANDOM_TREES_ROADMAP.md) records
shared priorities; the [formalization report](FORMALIZATION_REPORT.md) records results.

## Available foundations

- Finite rooted ordered trees with a list-of-children interface, structural
  induction and executable recursion.
- Zero-based vertex addresses, DFS enumeration, fringe subtrees, cut and graft
  operations, and finiteness of fixed-size tree classes.
- DFS degree words and Łukasiewicz increments, with the tree/excursion
  correspondence and executable reconstruction proved in both directions.
- Ordered forests, concatenated encodings and first passage at component
  boundaries.
- Canonical locally finite plane trees and a proved equivalence between their
  finite part and the existing finite-tree type.
- A Polish and Borel structure on these trees, canonical pruning of offspring
  fields, and the law of a Bienaymé–Galton–Watson tree for an arbitrary offspring
  probability measure, with the law of the root degree.
- The branching property of that law (conditionally on the root degree, the children
  are independent copies), uniqueness among probability measures with this property,
  and the probability of a finite tree as the product of the offspring masses of its
  outdegrees. The total mass of the finite trees is bounded by one, not assumed to be one.
- Extinction by a finite depth, the iteration of the offspring generating function and the
  identification of the probability that the tree is finite with the smallest fixed point of
  that function in `[0, 1]`, for every offspring law; and normalization to one (almost sure
  finiteness, finite-tree weights summing to one) when the mean is at most one and `μ {1} ≠ 1`;
  conversely the extinction probability is `< 1` when the mean exceeds one (infinite mean
  included), so it equals one exactly when the mean is at most one and `μ {1} ≠ 1`.
- Finite generations on possibly infinite locally finite trees, preserving the generation sizes
  of finite trees. Their sizes are measurable; given a root degree of positive probability,
  the child generation sizes are iid. The generation generating function is the iterated
  offspring generating function and its extended mean is `m ^ n`, with infinite means allowed.
  Given an entire finite generation history, the next size is a sum of independent offspring
  counts; the conditional version requires positive history mass.
- Conditioning on the number of vertices: the size event, its mass as a sum of finite-tree
  weights, admissible sizes, and the atoms of the conditioned law, for every offspring law.
- Walk weights of Łukasiewicz words (the weight of a tree is the walk weight of its increments),
  the deterministic cycle lemma for bridge words, and the Kemperman–Dwass identity in weight
  form: `n` times the total weight of the trees with `n` vertices is the total walk weight of the
  bridge words of length `n`; and its probabilistic form `n * P(|T| = n) = P(S_n = -1)` for the
  Łukasiewicz walk of independent offspring counts, for every offspring law.
- Exact coding of ordered forests with `ℓ ≥ 1` components by forest codes (through an artificial
  root), the generalized cycle lemma (exactly `ℓ` good rotation indices, counted with
  multiplicity) and Kemperman's identity for forests `n P(|F| = n) = ℓ P(S_n = -ℓ)`.

- Exponential tilting preserves size-conditioned laws; geometric offspring gives uniform plane
  trees at each positive size. Exact fringe-block decoding and uniform-fringe expectations
  are stated through finite-tree atoms. Discrete contours have unit steps and duration twice
  the number of edges. LCA gives the graph metric on present vertices. Conditioning may
  prescribe finitely many outdegree counts as well as total size. Contours in addresses
  have exact first-visit times and a continuous interpolation with the correct nodal heights.
- Compact metric probability spaces modulo whole-carrier measured isometry, with the GHP
  metric, completeness, separability/Polishness and compactness/tightness transfer to GH.
  Measures need not have full support. Rooted GHP is also complete, separable and Polish;
  positive spatial scaling is jointly continuous. Finite iid sampled-distance laws are
  GHP-continuous, with repeated samples retained; errors vanishing in probability preserve
  weak convergence.
- The deterministic real-tree criterion from completeness, four points and midpoints, and
  the compact real tree coded by any continuous real function on the unit interval, rooted
  at time zero with Lebesgue pushforward mass. The coding map is 6-Lipschitz in rooted GHP.
- A constructed Brownian bridge with Gaussian residual independence and grid-invariance;
  its minimum is negative almost surely, and minima on $[0,b]$ and $[c,d]$ are
  almost surely unequal when $b<c\le d<1$. Continuous-minimum uniqueness, strict positivity of the Vervaat
  transform, and identification with the standard Brownian CRT remain open.
- Scalar stable local limits with their lattice factor, density identification, regular
  variation and Potter/Karamata estimates, walk maximum tightness, and a constructed
  finite-variance instance with index two. Uniform local/tail/weighted forest estimates
  and two-sided size bounds retain admissibility where needed. Scalar attraction is explicit; these results
  do not construct a stable process or a continuum tree law.

Trees reuse Mathlib's `WType` internally in [BGW/Tree.lean](BGW/Tree.lean).
The public interface exposes ordered lists of children: `induction` and `cases`
produce a single `node ts` case, and `PlaneTree.fold` defines bottom-up recursion.
The root address is `[]`, child indices start at zero, size counts vertices, and
a fringe subtree is re-rooted at its selected vertex.

The separate `BGW.LocallyFinite.Tree` carrier uses positive child indices, as in
the source BGW-law construction. `PlaneTree.toLocallyFinite` shifts addresses
explicitly, and `PlaneTree.equivFiniteVertices` identifies exactly its finite
part. `Present` distinguishes a leaf from an absent address even though both
have zero offspring. The carrier is Polish with its Borel σ-algebra; `prune` turns an
i.i.d. field of potential offspring counts into a tree, and `bienaymeLaw μ` is its law.
`IsBienayme` expresses the branching property, `exists_unique_bienaymeLaw` shows that the
constructed law is the unique probability measure having it, and
`bienaymeLaw_toLocallyFinite` gives the atom of a finite tree. The finite-tree bridge is
still an `Equiv` (`PlaneTree` carries no measurable structure), and the value of the extinction
probability is classified by the mean (one exactly when the mean is at most one and `μ {1} ≠ 1`,
below one otherwise); its value in the supercritical case is not computed.

Everything is available through `import BGW`:

```lean
module

import BGW

open BGW.PlaneTree

example : (node [leaf, leaf]).increments = [1, -1, -1] := by
  simp [leaf]

example : (ofIncrements? [1, -1, -1]).map size = some 3 := by
  decide
```

## Building

Install [Elan](https://github.com/leanprover/elan). From the repository root,
`python3 scripts/check.py` runs the complete repository check; `lake build` is useful
for the regular build during iteration. The check completed on 2 November 2026 with
3,641 Lake jobs, 170 library modules and 3,175 constants; `docBlame` reported no
missing documentation, and both public-consumer files passed. Its axiom audit found
only Lean's standard axioms in the checked library declarations. This reports the
checked library scope and is not a certification of all of Mathlib.

```sh
lake build
```

Keep Lean and Mathlib at the repository's pinned versions; do not upgrade dependencies
as part of an unrelated change. For focused iteration, check one file with:

```sh
lake env lean BGW.lean
```

For interactive editing, open the repository in VS Code with the Lean 4 extension.

The pinned environment is Lean **4.35.0** and Mathlib **v4.35.0**, at commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Keep
[lean-toolchain](lean-toolchain), [lakefile.toml](lakefile.toml) and
[lake-manifest.json](lake-manifest.json) together to reproduce these versions.
[GitHub Actions](.github/workflows/lean.yml) runs the build on pushes and pull
requests, using the Mathlib cache.

The Brownian construction uses two small source extractions under `vendor/`, with pinned
upstream commits, licences and compatibility edits documented in their
[BrownianMotion](vendor/brownian-motion/README.md) and
[KolmogorovExtension4](vendor/kolmogorov-extension4/README.md) provenance notes.
They use the same Lean and Mathlib versions as the library.

## Library and documentation

| File | Contents |
| --- | --- |
| [BGW.lean](BGW.lean) | Public entry point |
| [Tree](BGW/Tree.lean) | Plane trees, list interface and basic operations |
| [Vertices](BGW/Tree/Vertices.lean) | Vertex addresses and DFS enumeration |
| [Fringe](BGW/Tree/Fringe.lean) | Fringe subtrees, replacement, cutting and grafting |
| [Finite](BGW/Tree/Finite.lean) | Finiteness of bounded-size and fixed-size classes |
| [DFS](BGW/Tree/DFS.lean) | Degree words and tree/forest increments |
| [Decode](BGW/Tree/Decode.lean) | Executable degree-word reconstruction |
| [Excursion](BGW/Tree/Excursion.lean) | Łukasiewicz excursion characterization and inverse identities |
| [Forest](BGW/Tree/Forest.lean) | First passage at forest component boundaries |
| [Locally finite trees](BGW/LocallyFinite/Basic.lean) | Canonical offspring fields and vertex membership |
| [Topology](BGW/LocallyFinite/Topology.lean) | Polish topology and Borel structure of the canonical fields |
| [Pruning](BGW/LocallyFinite/Prune.lean) | Canonical pruning of an offspring field and its measurability |
| [Law](BGW/LocallyFinite/Law.lean) | The BGW law for an arbitrary offspring law; probability and root degree |
| [Groups](BGW/LocallyFinite/Groups.lean) | Independent groups of offspring coordinates |
| [Branching](BGW/LocallyFinite/Branching.lean) | The branching property `IsBienayme` and its proof for the constructed law |
| [Cylinders](BGW/LocallyFinite/Cylinders.lean) | Finite offspring cylinders and their root decomposition |
| [Unique](BGW/LocallyFinite/Unique.lean) | Uniqueness of the branching law, `exists_unique_bienaymeLaw` |
| [Weight](BGW/Tree/Weight.lean) | Degree-product weights of finite trees |
| [Atoms](BGW/LocallyFinite/Atoms.lean) | Probability of a finite tree, measurability of the finite part, transport of the law |
| [Generating function](BGW/GeneratingFunction.lean) | The offspring generating function in `[0, ∞]` |
| [Extinction](BGW/LocallyFinite/Extinction.lean) | Extinction by finite depth, iteration, least fixed point |
| [Normalization](BGW/LocallyFinite/Normalization.lean) | Extinction probability one for mean at most one with `μ {1} ≠ 1` |
| [Supercritical](BGW/LocallyFinite/Supercritical.lean) | Extinction probability below one for mean greater than one; classification by the mean |
| [Size conditioning](BGW/LocallyFinite/SizeConditioning.lean) | Size event, admissible sizes, conditioned law on finite trees |
| [Walk weight](BGW/Tree/WalkWeight.lean) | Walk weights of Łukasiewicz words and the mass of a size class |
| [Cycle lemma](BGW/Tree/CycleLemma.lean) | Cycle lemma for bridges, shift bijection, weighted Kemperman–Dwass identity |
| [Walk law](BGW/LocallyFinite/WalkLaw.lean) | Kemperman identity `n P(|T| = n) = P(S_n = -1)` for trees |
| [Forest cycle](BGW/Tree/ForestCycle.lean) | Forest codes, generalized cycle lemma, weighted Kemperman identity for forests |
| [Forest walk law](BGW/LocallyFinite/ForestWalkLaw.lean) | Kemperman identity `n P(|F| = n) = ℓ P(S_n = -ℓ)` for forests |
| [First passage](BGW/Tree/FirstPassage.lean) | Splitting a forest bridge word at its first passage time; weight factorization |
| [First-passage law](BGW/LocallyFinite/FirstPassageLaw.lean) | Convolution `P(S_N = -ℓ) = ∑_{q ≤ N} P(|F| = q) P(S_{N-q} = 0)` |
| [Excursion law](BGW/LocallyFinite/ExcursionLaw.lean) | Excursion event `ζ = n` with mass `P(\|T\| = n)`; the code of the conditioned tree has the excursion law (atoms and expectations) |
| [Bridge law](BGW/LocallyFinite/BridgeLaw.lean) | Conditional bridge law; uniform cyclic shift of the conditioned tree (atoms and expectations) |
| [Finite-tree bridge](BGW/Tree/LocallyFinite.lean) | Address conversion, injectivity and exact finite-part equivalence |
| [Generation process](BGW/LocallyFinite/GenerationProcess.lean) | Full finite-history transitions and absorption at zero |
| [Tilting](BGW/LocallyFinite/Tilting.lean) | Equality of size-conditioned laws under exponential tilting |
| [Geometric laws](BGW/LocallyFinite/Geometric.lean) | Uniform plane trees from geometric offspring |
| [Fringe law](BGW/LocallyFinite/FringeLaw.lean) | Exact uniform-vertex fringe expectation |
| [Degree conditioning](BGW/LocallyFinite/DegreeConditioning.lean) | Size with finitely many outdegree counts |
| [Vertex geometry](BGW/Tree/Geometry.lean) | LCA and graph metric on present vertices |
| [Contour](BGW/Tree/Contour.lean) | Executable discrete contour, duration and unit-step properties |
| [Height](BGW/Tree/Height.lean) | Ancestors, fringe blocks and the Łukasiewicz-to-height identity |
| [MetricMeasure](BGW/MetricMeasure.lean) | GHP quotients, unrooted Polishness, rooted separability/scaling, weak perturbation and sampled laws |
| [ContinuumTrees](BGW/ContinuumTrees.lean) | Measured coding/rerooting, contour transfer, Brownian bridge and Vervaat-image laws |
| [StableTrees](BGW/StableTrees.lean) | Scalar stable toolkit, finite-variance instance and forest/walk bridge |
| [Formalization report](FORMALIZATION_REPORT.md) | Current coverage and verification record |
| [Random Trees roadmap](RANDOM_TREES_ROADMAP.md) | Shared development plan for BGW, GHP, continuum and stable trees, with reusable sources |
| [Claude handover](HANDOVER_CLAUDE.md) | Verified starting point and the next bounded implementation step |
| [Targeted roadmap](BGW_ROADMAP_2607_22291.md) | Plan for rare subtree patterns and Poisson approximation |
| [Broader roadmap](BGW_FORMALIZATION_ROADMAP.md) | Proposed scope across several BGW topics |

The roadmaps describe planned work; the report identifies what is implemented.
References link to public manuscripts. Local copies of papers and development
tools are excluded from the repository.

This independent project is intended to support a possible future integration
into [Tau Ceti](https://github.com/TauCetiProject/TauCeti), subject to its roadmap
and review process.

## License

Licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE).
