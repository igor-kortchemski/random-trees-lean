# Random Trees in Lean

**[Browse the API documentation](https://igor-kortchemski.github.io/random-trees-lean/)**

A Lean 4 library on random trees and the classical probability behind their scaling limits:
finite and locally finite Bienaymé–Galton–Watson (BGW) trees, the Skorokhod space and
weak-convergence tools, the spectrally positive stable Lévy process with its excursion theory
and height process, the Duquesne–Le Gall scaling limits of BGW trees and forests,
Gromov–Hausdorff–Prokhorov (GHP) geometry and continuum trees coded by continuous functions.
Every proof is checked by Lean's kernel with only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`; the library sources contain no `sorry`.

The library is in development (version `0.1.1`): names and module boundaries may still
change, so downstream projects should pin a commit.

**Where to find a result.** [CLASSICAL_THEORY_COVERAGE.md](CLASSICAL_THEORY_COVERAGE.md)
maps every item C1–C39 of the classical-theory specification
([CLASSICAL_THEORY_INPUTS.md](CLASSICAL_THEORY_INPUTS.md)) to the exact Lean declarations and
the module to import, says whether each statement is exact, equivalent, corrected or left to a
consumer, and ends with an import map for the article *Invariance principles for
Galton–Watson trees conditioned on the number of leaves*. The
[formalization report](FORMALIZATION_REPORT.md) records the scope and verification.

A first example:

```lean
module

import BGW

open BGW.PlaneTree

example : (node [leaf, leaf]).size = 3 := by
  simp
```

`import BGW` loads everything. For smaller dependencies, start with:

| Area | Useful starting imports |
| --- | --- |
| BGW trees | `BGW.Tree`, `BGW.LocallyFinite.Law`, `BGW.LocallyFinite.SizeConditioning` |
| Probability tools | `BGW.Probability` (weak convergence, Skorokhod representation, convergence in measure) |
| Skorokhod space | `BGW.Skorokhod.Basic`, `BGW.Skorokhod.Measurable`, `BGW.Skorokhod.Tightness`, or `BGW.Skorokhod` |
| Stable process, excursions, height, tree limits | the module named in the coverage index for each result, or `BGW.StableTrees` |
| Metric-measure geometry | `BGW.MetricMeasure` |
| Continuum trees | `BGW.ContinuumTrees.CodingMeasure`, `BGW.ContinuumTrees.ContourLawConvergence` |

These are module entry points of one package. Compiled consumer examples are in
[BGWTest/](BGWTest/).

## Conventions

| Topic | Convention |
| --- | --- |
| Finite-tree addresses | Zero-based child indices; root address `[]` |
| Locally finite tree addresses | Positive child indices, converted explicitly from finite trees |
| Size and uniform vertex | Size counts vertices; uniform mass samples all vertices, including the root |
| Contour coding | Contours are rescaled to the unit interval |
| GHP carrier and cost | Whole carrier retained even without full measure support; GHP costs use sums |
| Extinction and size conditioning | Condition on positive-mass sizes; extinction is certain for mean at most one except the deterministic one-child law (`μ {1} = 1`) |
| Path spaces | `D T E`: càdlàg paths on `[0, T]` with the J1 metric; Billingsley's complete metric lives on the type synonym `DComplete T E` (same topology); `DLoc`: real càdlàg paths on `[0, ∞)` with the evaluation σ-algebra |
| Stable index and normalization | `1 < θ ≤ 2`, spectrally positive, Laplace exponent `λ ^ θ` (`E e^{-λ X_t} = e^{t λ^θ}`); outside this range the stable laws are documented junk values |
| Stable index two | `X = √2 B` (variance `2t`); the finite-variance specialization uses variance `2` |
| Brownian CRT normalization | Aldous's CRT is coded by `2e`; the θ = 2 tree limit is coded by `√2 e` |
| Tree scaling limits | C27–C29 hold for any admissible norming (the `…_of_attracted` theorems); the original exports take `StableDomain μ θ B`, a monotone positive norming |

## Getting the library

Install [Elan](https://github.com/leanprover/elan), then clone and build release `v0.1.1`:

```sh
git clone --branch v0.1.1 https://github.com/igor-kortchemski/random-trees-lean.git
cd random-trees-lean
lake exe cache get
lake build
```

To run the build, consumer examples, axiom audit and documentation lint together, use
`python3 scripts/check.py`.

To use the library from another Lake project, use the same `lean-toolchain` and add one of
these to its `lakefile.toml`, then run `lake update` and `lake exe cache get`:

```toml
# a local checkout beside your project
[[require]]
name = "bgw"
path = "../random-trees-lean"

# or a published tag
[[require]]
name = "bgw"
git = "https://github.com/igor-kortchemski/random-trees-lean.git"
rev = "v0.1.1"
```

Lake resolves Mathlib and the vendored packages from the library's pinned configuration.
The [verification notes](docs/evidence/README.md) describe the separate consumer build.
The examples use Lean's module system and start with `module`.

## Main results

### Discrete trees and BGW laws

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
- Scalar stable local limits with their lattice factor, density identification, regular
  variation and Potter/Karamata estimates, walk maximum tightness, uniform local, tail and
  weighted forest estimates, two-sided size bounds at admissible sizes, and the Marchal
  growth chain with its finite law.

### Skorokhod space and weak convergence (C1–C14)

- `D T E` with the J1 metric, separability, Billingsley's complete metric and Polishness, Borel
  σ-field equal to the cylinder σ-field, the continuous paths as a subspace with uniform
  convergence to continuous limits, and continuity of evaluation, restriction, stopping,
  suprema, infima and time–space scaling.
- Relative compactness and tightness (the modulus `w'`, Billingsley's Theorem 13.2, Aldous's
  criterion), the continuous mapping theorem for almost everywhere continuous maps, converging
  together and Slutsky on varying spaces, Billingsley's approximation theorem, determining
  classes, Prokhorov's theorem and the Skorokhod representation.

### Stable processes and excursion theory (C15–C25)

- The θ-stable law, its density and transition kernels; the stable Lévy process as a law on
  `D T ℝ` and on `DLoc`, characterized by its increments; the functional limit theorem for
  walks in the stable domain of attraction, with Donsker's theorem for finite variance.
- Regularity of `0`, first passage and Kendall's identity, the unique minimum, and the
  θ = 2 instance `X = √2 B`.
- The reflected process `X − I` with local time `−I` and its strong Markov property (for the
  canonical filtration and its usual augmentation); Itô's excursion theorem with the excursion
  measure `N`; the normalized excursion and `N(· | ζ > 1)`; the Markov property under `N`;
  the `Γ_a` identity; Chaumont's path construction of the normalized excursion.

### Height process and scaling limits of BGW trees (C26–C30)

- The height process, its continuous modification and the excursion height `H^exc`.
- The Duquesne–Le Gall forest theorem (joint convergence of the rescaled Łukasiewicz path,
  height process and contour), the limit of trees with at least `n` vertices, and Duquesne's
  theorem for trees with exactly `n` vertices (along admissible sizes), as functional limits
  in law, for any admissible norming sequence (`BGW.StableTrees.NonmonotoneNorming`).
- At θ = 2: `H^exc = X^exc = √2 e`, with `e` the Vervaat transform of the Brownian bridge,
  and Aldous's normalization of the Brownian CRT.

### Bridges, Vervaat transform and jumps (C31–C36)

- The stable bridge on `D 1 ℝ`, its unique minimum attained continuously, the càdlàg Vervaat
  map with its continuity at bridge-like paths and its discrete counterpart, and Chaumont's
  identity `V(X^br) = X^exc` in law.
- The largest-jump functional, 2-Lipschitz for J1; the normalized excursion has a positive jump
  almost surely for θ < 2 and is continuous at θ = 2.

### Metric-measure geometry and continuum trees (C37–C39)

- Compact metric probability spaces modulo whole-carrier measured isometry, with the GHP
  metric, completeness, separability/Polishness and compactness/tightness transfer to GH.
  Measures need not have full support. Rooted GHP is also complete, separable and Polish;
  positive spatial scaling is jointly continuous. Finite iid sampled-distance laws are
  GHP-continuous, with repeated samples retained; errors vanishing in probability preserve
  weak convergence.
- The deterministic real-tree criterion from completeness, four points and midpoints, and
  the compact real tree coded by any continuous real function on the unit interval, rooted
  at time zero with Lebesgue pushforward mass, with Lipschitz bounds for GH and rooted GHP.
- Transfer of contour convergence to convergence in law of rooted measured trees. The
  uniform leaf measure has the same limit as the uniform vertex measure under the size ratio
  and leaf distribution hypotheses in the coverage index.

### Outside this library

Six subclaims of the specification belong to the article that consumes the library (its
leaf-conditioned specializations and a random time change); the coverage index lists them.
Of the 35 labelled results of the rare-subtree paper arXiv:2607.22291, two are proved here
in atomic form; that paper is a consumer, not a target of this library.

## Tree interface

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

## Building and checking

`lake build` builds the library; `python3 scripts/check.py` runs the complete check. It builds
every library and vendored module, compiles the consumer examples in `BGWTest/` with warnings
as errors, audits every library and vendor constant (including private and generated ones) for
the three allowed axioms, and runs `docBlame`. The published check audited 12,925 constants
across 871 library and 30 vendored modules and reported zero `docBlame` errors.
See the [verification notes](docs/evidence/README.md) for the build and independent kernel checks.

`python3 scripts/lint_report.py` runs Mathlib's default environment linters (`#lint`) over the
library; since 8 November 2026 it reports no finding (three definitions keep a documented
`nolint`, see the changelog). A non-blocking CI job also builds with Mathlib's standard linter set.
API documentation can be generated with doc-gen4 from [docs/build/](docs/build/README.md).

For focused iteration, check one file with:

```sh
lake env lean BGW.lean
```

For interactive editing, open the repository in VS Code with the Lean 4 extension.

The pinned environment is Lean **4.35.0** and Mathlib **v4.35.0**, at commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Keep
[lean-toolchain](lean-toolchain), [lakefile.toml](lakefile.toml) and
[lake-manifest.json](lake-manifest.json) together to reproduce these versions.
[GitHub Actions](.github/workflows/lean.yml) runs the complete check on pushes and pull
requests, using the Mathlib cache.

The Brownian construction and the projective limit behind `DLoc` use two small source
extractions under `vendor/`, with pinned upstream commits, licences and compatibility edits
documented in their [BrownianMotion](vendor/brownian-motion/README.md) and
[KolmogorovExtension4](vendor/kolmogorov-extension4/README.md) provenance notes. They use the
same Lean and Mathlib versions as the library.

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
| [Probability](BGW/Probability.lean) | Weak convergence, Skorokhod representation, convergence in measure, tail and integral limits |
| [Skorokhod](BGW/Skorokhod.lean) | `D T E`, J1 and Billingsley metrics, measurability, tightness, Vervaat map, jumps, `DLoc` |
| [MetricMeasure](BGW/MetricMeasure.lean) | GHP quotients, unrooted Polishness, rooted separability/scaling, weak perturbation and sampled laws |
| [ContinuumTrees](BGW/ContinuumTrees.lean) | Real trees, measured coding and rerooting, contour transfer, Brownian bridge and Vervaat-image laws, leaf measure |
| [StableTrees](BGW/StableTrees.lean) | Stable laws and processes, excursion theory, height process, forest and conditioned-tree limits, stable bridge, Marchal chain |
| [Classical-theory coverage](CLASSICAL_THEORY_COVERAGE.md) | C1–C39 mapped to exact declarations, with the article import map |
| [Classical-theory specification](CLASSICAL_THEORY_INPUTS.md) | The informal statements C1–C39 and their corrections |
| [Formalization report](FORMALIZATION_REPORT.md) | Coverage and verification record |
| [Changelog](CHANGELOG.md) | Notable changes and renamed declarations |
| [Verification](docs/evidence/README.md) | Build, axiom audit, and independent kernel replay |
| [API documentation](docs/build/README.md) | How to generate the HTML documentation with doc-gen4 |

## Maintenance and releases

- **Maintainer:** Igor Kortchemski. Questions and reports go through
  [GitHub issues](https://github.com/igor-kortchemski/random-trees-lean/issues).
- **Citation:** Cite the library using [CITATION.cff](CITATION.cff) and include the commit or
  release you used.
- **Versions:** releases are tagged commits. See [CHANGELOG.md](CHANGELOG.md) for changes.
- **Pins:** Lean and Mathlib are pinned exactly. An upgrade is its own commit that changes
  `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` together and reruns the check.
- **Breaking changes:** before `1.0` declarations may be renamed or moved; the changelog
  lists renamed and moved declarations with their new names.

## Contributing

Keep Lean and Mathlib pins in sync with `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json`; add imports at the narrowest useful module boundary. Document
mathematical conventions and state clearly which results remain open. The common
repository check is `python3 scripts/check.py`. Do not use `sorry` or introduce new
axioms to close a proof. Keep the coverage index and formalization report in sync with
changes to public declarations. The public tree contains the Lean library, examples, build
and verification tools, licenses, and documentation for readers. Keep planning notes,
review drafts, and campaign records in the development checkout.

Most of the code was written with AI assistance under the author's direction.

## License

Licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE).
