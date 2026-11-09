# Changelog

The library is pre-release (`0.1.0`); names and module paths may change before `1.0`. This file
records notable changes, and every renamed or moved public declaration.

## Unreleased

### Publication preparation

- Document installation from a published commit in `random-trees-lean` and add citation metadata.
- Update the verification checkpoint, the C27–C29 export notes and the public freeze index.
- Allow 90 minutes for the main CI job to accommodate an uncached library build.

### 9 November 2026 — independent kernel replay

- The compiled library passes `leanchecker` (all 870 modules), and its full export (416,202
  declarations, with the Mathlib closure) is accepted by `leanchecker-paranoid`, `con-leche`, `con-ron`
  and `lean4lean`; `nanoda` ran out of memory on this machine. The export declares `sorryAx` (Lean core)
  but no declaration uses it. Details: [docs/evidence/KERNEL_REPLAY.md](docs/evidence/KERNEL_REPLAY.md).

### 9 November 2026 — freeze records in format 4

- All 104 active freeze records are now in format 4 (skills v2.0.0), which also freezes the Lake
  configuration, the dependencies' sources and the compiled dependency files. Each of the 94 former
  format-3 records was recorded again at its own commit (56), or, when it had been recorded from
  uncommitted work, at the first later commit containing its modules (38); in every case the
  declaration hashes are identical to the predecessor's, and the new record passes on the current
  tree. The predecessors are kept unchanged and linked (see [docs/evidence/](docs/evidence/README.md)).

### 8 November 2026 — generic lemmas leave the `BGW.StableTrees` namespace (`a30839d`)

- The 120 public declarations of 25 generic files now live in the namespace of their folder, with no
  compatibility aliases: 23 files of `BGW/Probability/` move from `BGW.StableTrees`,
  `BGW.StableTrees.PathTail` and `BGW.StableTrees.DiscreteHeightApprox` to `BGW.Probability`
  (Doob's L² maximal inequalities, the Poisson-process characterization, convergence in measure,
  tail bounds, measurable reconstruction, independent partial sums, integral limits, the Skorokhod
  representation lift); `BGW/Skorokhod/PathRegularity` and `PathWindowInf` move to `BGW.Skorokhod`.
  The exact map is [docs/renames/2026-11-08-namespaces.tsv](docs/renames/2026-11-08-namespaces.tsv).
- The article consumer (`arXiv-1110.2163v4-BGW-leaves`) was rebuilt in a scratch copy against this
  commit and builds unchanged: its import closure contains none of the changed modules.
- Deferred: `BGW/ContinuumTrees/ExcursionCarrier.lean` keeps the namespace `BGW.StableTrees`. Its
  carrier (`IsExcursionTag`, `Excursion`) is generic, with no stable-law parameter, but 31 freeze
  records and many uses depend on it; its namespace and its folder will be reorganized later.

### 8 November 2026 — unused hypotheses of frozen statements (approved by the maintainer)

- Removed from theorems (frozen statements; each becomes stronger):
  `Skorokhod.tendsto_map_splitProdWithCont` (`[SeparableSpace E]`),
  `Skorokhod.CompatiblePaths.measure_ext` (`[IsFiniteMeasure Q']`),
  `Skorokhod.isTightMeasureSet_of_cadlagModulus` and `…_eventually` (`[OpensMeasurableSpace (D T E)]`),
  `StableTrees.tendsto_integral_abs_sub_of_massOne` and `tendsto_integral_mul_of_massOne`
  (`[IsProbabilityMeasure P]`), `Skorokhod.DLoc.measure_ext_of_restrict` (`[IsFiniteMeasure Q]`),
  and, not frozen, `MetricMeasure.ghpDistance_self`, `rootedGHPDistance_self`,
  `ghpDistance_eq_zero_of_measured_isometry`, `rootedGHPDistance_eq_zero_of_measured_isometry`
  (`[IsProbabilityMeasure μ]`).
- Kept, with `@[nolint unusedArguments]` and a docstring explaining the domain they fix:
  `LocallyFinite.offspringFieldLaw` (`[IsProbabilityMeasure μ]`: `Measure.infinitePi` is `0` otherwise),
  `MetricMeasure.ghpCosts` and `rootedGHPCosts` (compactness and Borel assumptions; `ghpDistance` and
  `rootedGHPDistance` keep them too). The earlier removal of these assumptions from `ghpCosts`,
  `ghpDistance` and their lemmas is undone: with nonempty carriers, compactness keeps the Hausdorff
  term finite (Mathlib's real `hausdorffDist` is `0` when infinite), and the Borel assumptions make
  the embeddings measurable so that the pushforward measures are meaningful.
- Freeze records whose statements changed received linked successor records (see
  [docs/evidence/](docs/evidence/README.md)); the earlier records are kept unchanged.

### 8 November 2026 — audit plan, phases 2 and 3 (non-breaking parts)

- **New theorems:** C27, C28 and C29 for any admissible norming sequence (module
  `BGW.StableTrees.NonmonotoneNorming`): `ForestTriple.tendsto_forestTripleLaw_of_attracted`,
  `ForestTriple.tendsto_forestTripleVecLaw_of_attracted`, `TailPair.tendsto_tailPairLaw_of_attracted`,
  `ExactContour.tendsto_exactHeightContourLaw_of_attracted`,
  `ExactContour.tendsto_exactHeightLibContourLaw_of_attracted` (in `BGW.StableTrees`), under
  `IsRealStableAttracted (realOffspringStepLaw μ) θ B` instead of the monotone `StableDomain μ θ B`.
- **New API:** postcomposition of càdlàg paths `BGW.Skorokhod.D.postcomp` with `postcomp_apply`,
  `postcomp_id`, `postcomp_comp`, `continuous_postcomp`, `measurable_postcomp` and
  `D.lipschitzWith_postcomp` (constant `max K 1`: the time part of the J1 cost does not shrink);
  real-factor time–space scaling `timeSpaceScaleSMul`, `timeSpaceScaleSMulC` for normed spaces
  (module `BGW.Skorokhod.ScalingSMul`); scaling on the unrooted GHP quotient `MeasuredGHSpace.scale` with
  its Lipschitz, continuity and measurability lemmas (module `BGW.MetricMeasure.MeasuredScaling`).
- **Moved, full names unchanged:** the basic `DLoc` API (carrier, evaluation σ-algebra, restriction,
  shift, filtrations, passage times) to `BGW.Skorokhod.DLocBasic`, which does not depend on the vendored
  packages (`BGW.Skorokhod.DLoc` re-exports it and keeps the projective-family part);
  `Coding.forgetToGH`, `continuous_forgetToGH`, `tendsto_map_forgetToGH` to
  `BGW.MetricMeasure.RootedUnderlyingGH`; `maxJump_eq_zero_of_continuous` and
  `maxJump_eq_zero_iff_continuous_of_leftLim_le` to `BGW.Skorokhod.Jump`.
- **Mathlib default linters:** from 47 findings to 6 (the remaining 6 are in frozen statements).
  Unused instance arguments were removed from theorems (this only strengthens them), e.g.
  `exists_joint_tendstoInMeasure_of_fiber_limits`, `Scalar.integral_conv_int` and four `Attraction`
  lemmas; the GHP part of this clean-up was revised the same day (next entry). The simp lemmas
  `Coding.circularProjection_zero/one`, `Coding.reroot_zero/one`, `Vervaat.rotate_zero/one` and
  `Vervaat.vervaat_zero/one` are restated in simp normal form; `@[simp]` was removed from
  `BrownianBridge.path_zero/one`, `FiniteTree.mass_singleton`, `PlaneTree.fringe?_node_cons` and three
  `Marchal.graftGraph_*` lemmas. Local instances renamed `instMeasurableSpaceListNat`,
  `instMeasurableSpaceListInt`; the unused binder of `bridgePrefix_family` is now `_hb` (same type).
- **`set_option`:** from 46 uses to 5 (proof changes only).
- **Tooling:** `scripts/lint_report.py`; a non-blocking CI job running Mathlib's standard linter set and
  `#lint`; `BGWTest/ApiExamples.lean` in the check; a doc-gen4 project in
  [docs/build/](docs/build/README.md).

### 8 November 2026 — documentation and evidence

- README, entry-point docstrings and the report header describe the current library; an
  installation route, a maintenance section, this changelog and the statement evidence
  ([docs/evidence/](docs/evidence/README.md)) were added.
- New compiled consumer examples: the README tree snippets in `BGWTest/Examples.lean`, and
  stable excursions and Donsker's theorem in `BGWTest/ScalingLimits.lean`.
- [LEAN_LIBRARY_AUDIT.md](LEAN_LIBRARY_AUDIT.md): audit for reuse, Mathlib and Tau Ceti.

### 8 November 2026 — second cleanup (`87d240c`)

- Moved to the namespace `BGW.Probability`, module `BGW.Probability.Stieltjes`:
  `stieltjes_restrict_Ioc_congr`, `stieltjes_min_restrict_le`, `stieltjes_min_initial_cdf`,
  `stieltjes_min_total`, `stieltjes_translate_window` (previously in `BGW.StableTrees`).
- `BGW.ContinuumTrees.FiniteTree.exists_vertex_ratio_bound_on_compact` moved from
  `LeafLawConvergenceDeterministic` to `ContourLawConvergence` (same full name).
- New public declarations replacing private copies: `BGW.Skorokhod.integral_freeze_shiftAt`,
  `measurable_lifetimeDensity`, `measurable_lifetimePos`, the leaf-rank lemmas of
  `BGW.ContinuumTrees.LeafMeasure`, `exists_uniform_oscillation_of_isCompact`, the Lipschitz lemmas
  of the path operations of `BGW.Skorokhod.OptionalGaps`, and the general modules
  `BGW.Probability.Completion` and `BGW.Probability.Rounding`.

### 8 November 2026 — first cleanup (`7334c52`)

- One public `BGW.Probability.exists_nnrat_btwn` replaces five private copies.
- `prodWithCont` and `continuous_prodWithCont` moved into `BGW.Skorokhod.ProductPaths`
  (`ProductPathsVector` re-exports them).
- Removed: the module `BGW.StableTrees.TailPairIntegralComparison` with
  `BGW.StableTrees.TailPair.eventually_abs_integral_sub_le_of_reconstruction` (use the a.e. form
  `BGW.StableTrees.PathTail.eventually_abs_integral_sub_le_of_reconstruction_ae`), and the
  aliases `TailPair.firstLongIndex_realForestIncrements` and `TailPair.ladderTime_realForestIncrements`
  (use the now public
  `BGW.StableTrees.PathTail.firstLongIndex_eq` and `BGW.StableTrees.PathTail.ladderTime_eq`).
- Generic helpers moved, with unchanged full names, to `BGW/Probability/` and
  `BGW/Skorokhod/` (`ConvergenceInMeasure`, `TailBounds`, `MeasurableReconstruction`,
  `IntegralLimits`, `SkorokhodRepresentationLift`, `IndependentPartialSums`, `NNReal`,
  `PathRegularity`, `PathWindowInf`).

### 6–8 November 2026 — classical-probability layer

- The Skorokhod space and weak-convergence tools, the stable law and Lévy process, excursion
  theory, the height process, the scaling limits of BGW trees and forests, stable bridges and
  the Vervaat transform, and the transfer to continuum trees: items C1–C39 of
  [CLASSICAL_THEORY_COVERAGE.md](CLASSICAL_THEORY_COVERAGE.md).

### 29 October – 2 November 2026 — foundations

- Finite plane trees, locally finite trees and the BGW law with its branching property,
  extinction, conditioning and Kemperman identities; the GHP metric; real trees coded by
  continuous functions; scalar stable tools (see the
  [formalization report](FORMALIZATION_REPORT.md)).
