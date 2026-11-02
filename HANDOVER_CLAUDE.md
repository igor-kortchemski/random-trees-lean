# Claude handover — Random Trees bootstrap

> Publication snapshot for `igor-kortchemski/random-trees-lean`.
> Historical local paths, uncommitted-state descriptions and temporary log references
> below document the development before this initial export. They are not dependencies
> of the published library. Reproduce current checks with `python3 scripts/check.py`.

Updated 2 November 2026. **Current handover: the quality roadmap has been implemented.**
The user authorized the bounded maintenance work in `AUDIT_QUALITE_MATHLIB_UX.md`,
including repair of the existing minimum proof. The older pause snapshot below is historical.
This checkpoint does not claim that the whole Random Trees mathematical roadmap is complete.

Read the current [formalization report](FORMALIZATION_REPORT.md#quality-and-integration-checkpoint--2-november-2026)
and [README](README.md) first. Preserve all local changes; no commit, push, dependency update
or publication has been performed.

### Current reproducible check

```sh
python3 scripts/check.py
```

It passed on this checkout: **3641 Lake jobs**, both public-consumer files, **3175 constants
from all 170 maintained BGW/supplier modules**, and **zero `docBlame` errors**. Only the
three standard permitted axioms occur. The check regenerates its own temporary audit;
no old probe in `/tmp` is needed. The same command is wired into GitHub Actions, whose
remote execution has not been observed here. Lean 4.35.0 and the Mathlib pin are unchanged.

### Changes since the pause

- Minimum compiles with its approved statement, following parser/API/preimage fixes and
  the local `let` preferred by the linter. Marchal weights compile without unused-instance
  warnings. Grid, Minimum and Marchal weights are now reexported by their sector entries.
- Rooted completeness/Polishness and C2 transfer in law with random sizes are integrated
  and currently verified, rather than remaining unchecked scoped additions.
- Definition docstrings and headers are complete for the reported gaps. `PlaneTree.ext`
  supports equality by children; generic scaling no longer imports the rooted quotient.
- Ordinary-import examples cover the API and a local discrete measurable structure on
  finite trees supplying the measurability hypotheses of C2. There is no global instance.
- Explicit model settings used: Luna low (headers/inventory), Luna medium (documentation),
  Sol low (Marchal), Sol medium (API/docstrings/checks), Sol high (Minimum), Astra high
  (independent sensitive/final reviews). Only the root coordinator ran Lean/Lake.

The next mathematical work, if requested, remains continuous-minimum uniqueness, excursion/CRT
identification, actual finite Marchal growth laws, and stable process/height and functional
limits. The selection PMF is not the chain; the Vervaat image law is not an already proved
classical CRT identification. Keep these boundaries explicit.

## Historical handover — 1 November 2026, superseded by the checkpoint above

Updated 1 November 2026. **PAUSED at the user's explicit request:**
“I have no more tokens left. Stop and prepare a handover.”
The previous instruction to continue without stopping is superseded. All proof workers
were interrupted; the last running build had already finished. Do not resume formalization
until the user authorizes resumption or gives this handover to a successor to continue.

Working checkout: `/Users/igor/LeanFormalization/BGW-formalization`.
No commit, push, publication, rename or dependency-pin upgrade has been performed.
Preserve all local changes, including the many untracked Lean files and `vendor/`.

## Resume snapshot — read this before the historical details

The project is not complete. B1–B3, unrooted GHP, deterministic coding/rerooting and
scalar S1 are substantially implemented. Since the last combined verification checkpoint,
C2 transfer in distribution and rooted GHP completeness have also compiled. Brownian
minimum proofs and the first finite Marchal ingredients are in progress.

### Exact verification boundary

- Last **full build plus combined axiom audit**: full `lake build`, **3599 jobs**,
  no warnings; **3067 constants from 163 selected project and Brownian-supplier modules**,
  including private/generated declarations. Only `propext`, `Classical.choice` and
  `Quot.sound`. Logs: `/tmp/random-trees-full-milestone.log` and
  `/tmp/random-trees-current-review.log`; probe: `/tmp/random-trees-current-review.lean`.
- These figures are a historical coherent checkpoint. **They do not certify the entire
  current source tree.** New successful scoped builds and unfinished files follow below.
- Lean remains **4.35.0**; Mathlib remains
  **56a005855ea17e0b0958f73ec801ae140b0a1679**. Existing manifest dependency revisions were
  compared with `/tmp/bgw-before-brownian-lake-manifest.json` and unchanged.
- The four main Markdown documents passed local-link/math-format checks and
  `git diff --check` at that checkpoint. A comment/string-aware scan found no forbidden
  constructs in 163 then-maintained source files; refresh it for later files.

### New successful scoped builds, after that checkpoint

| File | Actual result and meaning | Current integration/review boundary |
| --- | --- | --- |
| `BGW/ContinuumTrees/ContourLawConvergence.lean` | Compiled without warning, 16s; log `/tmp/random-trees-increments-contour-law-build.log`. `FiniteTree.tendsto_rooted_laws_of_contour` transfers weak contour convergence with random sizes on varying probability spaces. | Publicly imported by `ContinuumTrees.lean`; exact contracts and complete proof bodies independently reviewed PASS. Full consumer build/combined axiom audit still to refresh. |
| `BGW/MetricMeasure/RootedGHPCompleteness.lean` | Compiled without warning at the **standard heartbeat budget**, 7.1s; log `/tmp/random-trees-marchal-regression-build.log`. CompleteSpace and PolishSpace for the existing rooted metric. | Publicly imported by `MetricMeasure.lean`; contract and complete mathematical proof independently reviewed PASS. The same log also has unrelated Marchal/regression failures from earlier source versions. |
| `BGW/ContinuumTrees/BrownianBridgeIncrements.lean` | Compiled without warning, 8.4s; log `/tmp/random-trees-rooted-increments-build.log`. Gaussian differences, mean zero, variance $d(1-d)$ and zero atom masses for $0<d<1$. | Imported through Regression; final independent review PASS. The other target in that log failed in an older rooted-completeness version, since corrected. |
| `BGW/ContinuumTrees/BrownianBridgeRegression.lean` | Latest version, including independence of the **whole continuous residual path** and increment, compiled without warning, 7.4s. | Public import already added. Latest log `/tmp/random-trees-grid-regression-build-3.log` is fully successful. First covariance group had final independent review PASS; the independence addition has an approved independent contract but still needs final independent body review and fresh axiom audit. |
| `BGW/ContinuumTrees/BrownianBridgeGrid.lean` | Compiled without warning, 9.5s, in the same latest successful log (**3386 jobs**). Centered cyclic grid invariance is derived from Gaussian means/covariances; distinct grid values, unique grid minimum, positivity probability $1/(n+1)$, and strictly negative continuous bridge minimum a.s. | **Not yet imported by the public entry point.** Exact contracts passed independent review; final corrected bodies/exports still need final source review and combined audit. It does not prove uniqueness of the continuous minimum. |

C2 retains deterministic divisors $b_n>0$, $b_n\to\infty$, and
$b_n/N_n\to0$ in probability; contours have duration one and spatial factor $1/b_n$.
The theorem assumes measurability of the actual contour/rooted-space observables explicitly.
There is no global measurable-space instance on `PlaneTree` or all addresses. GHP error
convergence is **proved** from tightness and compact oscillation, not assumed. The size-ratio
condition uses strict real outer-measure tails; ordinary measurable tree inputs give the
usual probability interpretation.

Rooted completeness uses the actual rooted costs in one complete ambient realization.
The root limit belongs to the entire Hausdorff-limit carrier, even outside measure support.
A former elaboration timeout was fixed by explicitly typing the ambient `Z` in the
continuous infDist map; the temporary enlarged heartbeat budget was removed.

### Files awaiting their next check

- **`BGW/StableTrees/MarchalWeights.lean`**: exact total selection weight
  $n\alpha-1$, nonnegative weights, positive normalizer, normalized PMF on
  `G.edgeSet ⊕ {v // 3 ≤ G.degree v}` for an existing finite `SimpleGraph` tree.
  Leaf labels are an injection from `Fin (n+1)` whose image is exactly degree-one vertices;
  every other degree is at least three. Contracts and full bodies independently reviewed
  PASS by `conditioning_patterns`. The first build failed only on two Nat-to-Nat cast
  simplifications and an unused `[DecidableEq V]` warning. `stable_trees` applied
  `Nat.cast_id` and a local `omit`; **this corrected version has not been compiled**.
  Log of the earlier failures: `/tmp/random-trees-marchal-regression-build.log`.
  Not publicly imported yet. This is a selection PMF, not the Marchal growth chain.
- **`BGW/ContinuumTrees/BrownianBridgeMinimum.lean`**: written and frozen, **never compiled
  or finally reviewed**. First approved target only:
  `measure_prefixMin_eq_intervalMin (b c d : I) (b<c) (c≤d) (d<1)` says equality of
  minima on `[0,b]` and `[c,d]` has zero bridge-law mass. Uses genuine regression
  independence, atom-free increment, singleton sections and Fubini. Continuous global
  uniqueness and Vervaat strict positivity are **not yet included as proved results**.
- **`BGW/StableTrees/MarchalTree.lean`**: does **not exist** at pause. Work was only
  exploring a direct state carrier: finite numbered SimpleGraph, exhaustive leaf labels,
  no degree two, quotient by graph isomorphisms preserving every label. No contract for
  this carrier was yet approved for implementation. A clade/laminar-family representation
  was considered but not adopted: do not build both representations or a general framework.

### Next authorized continuation

1. Preserve the checkout. Compile the corrected Marchal weights and the new minimum file,
   review final corrected grid/regression proofs independently, then add only checked exports.
2. Run a fresh full build and a refreshed combined consumer/axiom probe. The current probe
   imports the old checkpoint closure; explicitly add the new modules and audit their
   private/generated constants too. Logs are temporary files and may disappear; rerun if
   absent rather than treating prose as kernel evidence.
3. Update the existing report/roadmap/README at that coherent checkpoint. Those documents
   currently lag the newly compiled C2-in-law, rooted completeness and grid results; their
   last full/audit checkpoint is still accurate. Do not create another ledger.
4. Continue Brownian minimum uniqueness, then strict positivity of the Vervaat path and the
   required identification with the standard excursion/CRT. Continue finite Marchal laws
   with a small faithful graph state and actual growth transitions, then S3–S4 as planned.

Useful first commands **when resumption is authorized**:

```sh
lake build BGW.StableTrees.MarchalWeights BGW.ContinuumTrees.BrownianBridgeMinimum
lake build
```

Only one coordinator runs Lean/Lake. Workers may read/write disjoint files but must not
start overlapping builds. No `sorry`, `admit`, custom axioms, `native_decide`, `bv_decide`
or `unsafe` in maintained Lean code. Use the existing Lean skills for early statement
review, final proof/source review, affected builds and axiom checks. Markdown math uses
`$...$` and standalone `$$` delimiters.

### Brownian source and identification cautions

The actual supplier is vendored under local Lake path dependencies:
`RemyDegenne/brownian-motion` **497e5e2a60450796f75ab920e6c33addae4d644d** and
`RemyDegenne/kolmogorov_extension4` **c20f168ed693537c78111ffeabc2ab5f384e35d6**.
Only the construction closure is included (26 Brownian + three Kolmogorov modules and one
Mathlib compatibility module). Eight generic lemmas were backported; one API call and one
import were adapted. The upstream unfinished reflection file is excluded. Original clones
are in `/tmp/bgw-brownian-497e5e2` and `/tmp/bgw-kolmogorov-c20f168`; maintained sources
are in the repo's `vendor/`, with licences/provenance. Do not change pins to fix proofs.

The bridge is genuinely constructed from `gaussianLimit`/`brownian`, anchored at both
endpoints for every outcome. `VervaatBridge.treeLaw` is the genuine image of the bridge
under the measurable first-minimum Vervaat map and coding by twice the path. **This alone
is not yet the proved classical Brownian CRT identification.**

The regression route for uniqueness follows Kim–Pollard, *Cube Root Asymptotics*,
Lemma 2.6, specialized to two intervals, not a new general Gaussian-extrema theory.
[Primary text](https://www.stat.yale.edu/~pollard/Papers/KimPollard90AS.pdf).
For later excursion identification, the occupation/conditioning argument in
[Chaumont–Uribe Bravo, arXiv:1405.1335v1](https://arxiv.org/pdf/1405.1335v1)
was investigated but **not approved**: selecting uniformly near a minimum versus conditioning
an independent rotation can introduce occupation bias. Recheck the exact theorem and
hypotheses before using that route; no implemented proof depends on it.

For Marchal, preserve the original edge incident to A0 as an ordinary selectable edge.
At $\alpha=2$, internal vertex weights vanish on binary states, **not on every admissible
state**; the binary support is a theorem about the chain started from A0—A1. Primary
source: [Curien–Haas, §§1.1 and 1.3](https://arxiv.org/pdf/1207.5418v1).

### Suggested successor prompt

> Reprends le projet dans `/Users/igor/LeanFormalization/BGW-formalization` à partir de
> `HANDOVER_CLAUDE.md`, en lisant d'abord son « Resume snapshot ». Je t'autorise à reprendre
> la formalisation. Préserve tous les changements locaux, Lean 4.35.0 et le pin Mathlib.
> Vérifie d'abord les fichiers en attente, puis poursuis `RANDOM_TREES_ROADMAP.md` sans
> suringénierie. Utilise les skills Lean et les revues indépendantes appropriés, avec un seul
> coordinateur de compilation. Ne publie, ne pousse et ne renomme rien. N'annonce pas le
> projet terminé tant que les obligations mathématiques de la roadmap restent ouvertes.

## Start here

Read [RANDOM_TREES_ROADMAP.md](RANDOM_TREES_ROADMAP.md) for the reviewed v1 scope
and [FORMALIZATION_REPORT.md](FORMALIZATION_REPORT.md) for implemented coverage.
The user wants one reusable library with four areas and minimal infrastructure.
Paper-specific results stay in their companion projects. The generation-history transition,
tilting/geometric laws, exact fringe expectations, unrooted Polish GHP core, real-tree
criterion and scalar stable toolkit are now compiled and reviewed. Uniform forest bounds,
finite degree-count conditioning, LCA/vertex graph geometry and continuous-function coding
as compact real trees are also compiled. Measured rerooting, positive scaling, rooted
separability, exact contour mass comparison and deterministic convergence transfer are now
proved. The Brownian bridge, measurable Vervaat transform and actual image tree law are
constructed. The resume snapshot above records newer compiled transfer/completeness results
and the remaining Brownian/stable probability obligations. Have source-facing contracts reviewed
before substantial proofs.
Do not introduce a general framework merely to package the next lemma.

Keep Lean **4.35.0** and Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Keep the current folder, Lake package
and `BGW` namespace while developing. No rename, publication or push is part of
this handover. The base Git revision is `d818312f05742621cf0c5b76fca124c93ff1572e`;
the roadmap, the bootstrap modules, all modules added since (topology, pruning, law, branching,
uniqueness, weights, atoms, generating function, extinction, normalization, size conditioning, walk weights, cycle lemma, walk law, forest cycle,
forest walk law, first passage, bridge/excursion laws, supercritical classification and generation
sizes) and their documentation are local, uncommitted work. Inspect
`git status` and preserve all existing changes before continuing.

The local `lean-autoformalization-skills/skills/` collection contains
`lean-workflow`, `lean-project-architecture` and `lean-statement-audit`.
Use the existing workflow: one writer/build coordinator, independent review of
new source-facing interfaces, focused builds, then affected consumers. Do not
add a second progress ledger or a submission framework. Mathematical Markdown
uses `$...$` and standalone `$$` delimiters, compatible with MacDown/QLMarkdown.

## What is now proved

Modules on the carrier, all exported by `import BGW`:

- [BGW/LocallyFinite/Basic.lean](BGW/LocallyFinite/Basic.lean): `BGW.LocallyFinite.Tree`
  is the subtype of canonical offspring fields `List ℕ → ℕ`. It may have
  infinite height. `degree`, `child`, `Present` and `FiniteVertices` preserve
  the deterministic meanings used in `freezing1`.
- [BGW/Tree/LocallyFinite.lean](BGW/Tree/LocallyFinite.lean): the existing finite
  `BGW.PlaneTree` embeds by `toLocallyFinite`. Its degrees, existing children
  and vertices are preserved; the embedding is injective and its image is
  exactly the trees with finitely many present vertices.
- [Topology](BGW/LocallyFinite/Topology.lean): `isClosed_canonical`,
  `instance : PolishSpace Tree`, `continuous_offspring`, `continuous_degree`,
  `continuous_child`. The topology is the subtype topology of the product of discrete
  `ℕ`: a sequence converges iff every coordinate is eventually constant.
- [Prune](BGW/LocallyFinite/Prune.lean): `pruneRaw`, `prune`, `degree_prune`,
  `child_prune`, `prune_val`, `prune_val_of_present`, `measurable_prune`.
- [Law](BGW/LocallyFinite/Law.lean): for every `μ : Measure ℕ` with
  `IsProbabilityMeasure μ`, `offspringFieldLaw μ` (`Measure.infinitePi`),
  `bienaymeLaw μ := (offspringFieldLaw μ).map prune`, both probability instances,
  `bienaymeLaw_apply`, `measurePreserving_prune`, `bienaymeLaw_map_degree` (root degree has
  law `μ`) and `bienaymeLaw_leaf`. No mean, support or criticality hypothesis.
- [Groups](BGW/LocallyFinite/Groups.lean), [Branching](BGW/LocallyFinite/Branching.lean):
  `iid_branch_groups`; `childrenEvent`; `IsBienayme μ ρ` (root degree has law `ρ`; when
  `μ {degree = k} ≠ 0`, the conditional law of `(child T 1, …, child T k)` is
  `Measure.pi (fun _ => μ)`); `bienaymeLaw_childrenEvent` (mass `μ {k} * ∏ bienaymeLaw μ (E i)`);
  `isBienayme_bienaymeLaw`.
- [Cylinders](BGW/LocallyFinite/Cylinders.lean), [Unique](BGW/LocallyFinite/Unique.lean):
  `IsBienayme.unique`, `IsBienayme.eq_bienaymeLaw`, `exists_unique_bienaymeLaw`: the constructed
  law is the only probability measure on `Tree` with the branching property for `ρ`.
- [Tree/Weight](BGW/Tree/Weight.lean): `PlaneTree.weight p t = (t.degrees.map p).prod` with
  `weight_node`, `weight_leaf`, `weight_eq_zero_iff`, `weight_ne_zero_iff`.
- [Atoms](BGW/LocallyFinite/Atoms.lean): `bienaymeLaw_toLocallyFinite`
  (`bienaymeLaw μ {t.toLocallyFinite} = weight (fun d => μ {d}) t`), `measurableEmbedding_toLocallyFinite`
  (for the discrete σ-algebra written explicitly), `measurableSet_finiteVertices`,
  `bienaymeLaw_finiteVertices` (`P(finite) = ∑' t, weight …`), `tsum_weight_le_one`,
  `bienaymeLaw_restrict_finiteVertices` (restriction to the finite part is
  `Measure.sum (fun t => weight … t • Measure.dirac t.toLocallyFinite)`).

- [GeneratingFunction](BGW/GeneratingFunction.lean): `BGW.offspringGF μ s = ∑' k, μ {k} * s ^ k`
  in `ℝ≥0∞`, with `offspringGF_zero` (`= μ {0}`), `offspringGF_one` (`= 1`, probability measure) and
  `offspringGF_mono` (no hypothesis on `μ`).
- [Extinction](BGW/LocallyFinite/Extinction.lean): with `extinctBy n = {T | ∀ u, Present T u → u.length < n}`
  (so `extinctBy_zero : extinctBy 0 = ∅`, `extinctBy_one : extinctBy 1 = {leaf}`; the source's
  `heightLE h` is `extinctBy (h + 1)`): `monotone_extinctBy`, `measurableSet_extinctBy`,
  `extinctBy_succ_eq` (`E_{n+1} = ⋃ k, childrenEvent k (fun _ => E_n)`),
  `finiteVertices_iff_children` (finite iff all existing children are), `iUnion_extinctBy`
  (`⋃ n, E_n = {FiniteVertices}`), then for every offspring probability measure `μ`:
  `bienaymeLaw_extinctBy_succ`, `bienaymeLaw_extinctBy` (`P(E_n) = f^[n] 0`),
  `bienaymeLaw_finiteVertices_eq_iSup`, `tendsto_iterate_offspringGF`,
  `offspringGF_bienaymeLaw_finiteVertices` (`f q = q`),
  `bienaymeLaw_finiteVertices_le_of_fixedPoint` (every fixed point `s`, no bound `s ≤ 1`, is `≥ q`),
  `isLeast_bienaymeLaw_finiteVertices` (`q` is the least element of `{s ≤ 1 | f s = s}`) and
  `isLeast_tsum_weight` (same for the total weight of finite plane trees).

- [Normalization](BGW/LocallyFinite/Normalization.lean) and the end of
  [GeneratingFunction](BGW/GeneratingFunction.lean): `tsum_measure_singleton`,
  `eq_one_of_offspringGF_eq` (for `∑' k, k * μ {k} ≤ 1` and `μ {1} ≠ 1`, `1` is the only fixed point
  of `offspringGF μ` in `[0, 1]`; strict Bernoulli at some `j ≥ 2` when the mean is one, strictness
  from the mean when it is below one), then, with the mean written `∫⁻ k : ℕ, (k : ℝ≥0∞) ∂μ ≤ 1`
  (Mathlib's expectation): `bienaymeLaw_finiteVertices_eq_one`, `tsum_weight_eq_one`,
  `ae_finiteVertices_bienaymeLaw`.
- [Supercritical](BGW/LocallyFinite/Supercritical.lean) and `exists_lt_one_offspringGF_le` in
  [GeneratingFunction](BGW/GeneratingFunction.lean): for mean `> 1` (infinite allowed) a point
  `s < 1` with `offspringGF μ s ≤ s`, hence `bienaymeLaw_finiteVertices_lt_one`; with
  `bienaymeLaw_finiteVertices_eq_zero_of_singleton_one`, the classification
  `bienaymeLaw_finiteVertices_eq_one_iff` (`q = 1` iff mean `≤ 1` and `μ {1} ≠ 1`).

- [SizeConditioning](BGW/LocallyFinite/SizeConditioning.lean):
  `sizeEvent n = {T | FiniteVertices T ∧ {u | Present T u}.ncard = n}` (the `FiniteVertices` conjunct
  is essential at `n = 0`: `Set.ncard` of an infinite set is `0`, so without it `sizeEvent 0` would be
  the infinite trees), `ncard_present_toLocallyFinite`
  (`{u | Present t.toLocallyFinite u}.ncard = t.size`), `toLocallyFinite_mem_sizeEvent_iff`,
  `sizeEvent_eq_image`, `measurableSet_sizeEvent`, `sizeEvent_zero : sizeEvent 0 = ∅`,
  `bienaymeLaw_sizeEvent` (mass `= ∑' t, if t.size = n then weight … t else 0`),
  `bienaymeLaw_sizeEvent_ne_zero_iff` (admissible iff some tree of size `n` has positive weight),
  `isProbabilityMeasure_cond_sizeEvent` (admissible sizes), `cond_sizeEvent_self` (mass one on the
  event), `cond_sizeEvent_eq_zero` (inadmissible:
  the conditioned measure is `0`), `cond_sizeEvent_singleton` (atom `weight / mass` at a tree of size
  `n`, `0` otherwise). Conditioning uses Mathlib's `ProbabilityTheory.cond`, notation `μ[|s]`.

- [Tree/WalkWeight](BGW/Tree/WalkWeight.lean): `walkWeight p xs = (xs.map fun a => p (a + 1).toNat).prod`,
  `PlaneTree.walkWeight_increments` (`walkWeight p t.increments = weight p t`),
  `PlaneTree.tsum_weight_size_eq_tsum_excursions`; in `SizeConditioning`:
  `bienaymeLaw_sizeEvent_eq_tsum_excursions`, `bienaymeLaw_sizeEvent_ne_zero_iff_excursion`.
  Excursions are the library's `IsTreeExcursion` words (prefix sums), not the source's first passage.
- [Tree/CycleLemma](BGW/Tree/CycleLemma.lean): `bridgeWords n` (length `n`, entries `≥ -1`, sum `-1`);
  private `isTreeExcursion_rotate_iff` (rotation by `i < n` is an excursion iff `i` is the first
  minimizer of the prefix sums on `[0, n)`); `exists_unique_rotate_isTreeExcursion` (the cycle lemma,
  `∃! i, i < n ∧ IsTreeExcursion (x.rotate i)`); `PlaneTree.shiftEquiv n :
  {t // t.size = n} × Fin n ≃ bridgeWords n`, `(t, i) ↦ t.increments.rotate i`; `walkWeight_rotate`;
  `PlaneTree.natCast_mul_tsum_weight_size` (`n * ∑' t, (if t.size = n then weight p t else 0) =
  ∑' x, indicator (bridgeWords n) (walkWeight p) x`); in `SizeConditioning`:
  `natCast_mul_bienaymeLaw_sizeEvent` (`n * P(size = n) = ∑' x, indicator (bridgeWords n) …`).

- [LocallyFinite/WalkLaw](BGW/LocallyFinite/WalkLaw.lean): `countBridges n = {ω : Fin n → ℕ | ∑ i, ω i + 1 = n}`,
  `stepWord ω = List.ofFn fun i => (ω i : ℤ) - 1` (injective, into `bridgeWords n` exactly on
  `countBridges n`, `walkWeight_stepWord : walkWeight p (stepWord ω) = ∏ i, p (ω i)`,
  `exists_stepWord_eq`), `tsum_bridgeWords_walkWeight`, `pi_countBridges`, and the main
  `LocallyFinite.natCast_mul_bienaymeLaw_sizeEvent_eq_pi`:
  `n * bienaymeLaw μ (sizeEvent n) = Measure.pi (fun _ : Fin n => μ) (countBridges n)`
  (Kemperman: `n P(|T| = n) = P(S_n = -1)`, every `μ`, both sides zero at `n = 0`).

- [Tree/ForestCycle](BGW/Tree/ForestCycle.lean): `IsForestCode ℓ xs` (steps `≥ -1`, sum `-ℓ`, every
  proper prefix sum, empty prefix included, `> -ℓ`); `isForestCode_iff_isTreeExcursion_cons` (artificial
  root `ℓ - 1`, needs `1 ≤ ℓ`); `PlaneForest.increments_injective`;
  `PlaneForest.isForestCode_iff_existsUnique` (forest codes are exactly the codes of the unique forests
  with `ℓ` components); `PlaneForest.walkWeight_increments` (component weights only, no root factor);
  `forestBridgeWords ℓ n` (`forestBridgeWords 1 n = bridgeWords n`); `exists_first_sum_take_eq`;
  `isForestCode_rotate_iff`; `ncard_rotate_isForestCode`
  (`{i | i < x.length ∧ IsForestCode ℓ (x.rotate i)}.ncard = ℓ`, indices counted with multiplicity);
  `forestWeight p ℓ n`; `forestWeight_eq_tsum_codes`; `natCast_mul_forestWeight`
  (`n * forestWeight p ℓ n = ℓ * ∑' x, indicator (forestBridgeWords ℓ n) (walkWeight p) x`);
  `PlaneForest.length_le_size`, `forestWeight_eq_zero_of_lt`. `sum_take_rotate` (CycleLemma) is public.
- [LocallyFinite/ForestWalkLaw](BGW/LocallyFinite/ForestWalkLaw.lean): `countForestBridges ℓ n =
  {ω | ∑ i, ω i + ℓ = n}` (`countForestBridges 1 n = countBridges n`, empty for `n < ℓ`),
  `stepWord_mem_forestBridgeWords_iff`, `tsum_forestBridgeWords_walkWeight`, `pi_eq_tsum_indicator`
  and the main `natCast_mul_forestWeight_eq_pi`:
  `n * forestWeight (fun d => μ {d}) ℓ n = ℓ * Measure.pi (fun _ : Fin n => μ) (countForestBridges ℓ n)`
  for `IsProbabilityMeasure μ`, `1 ≤ ℓ`, every `n`; `forestWeight_one`,
  `LocallyFinite.forestWeight_one_eq_bienaymeLaw_sizeEvent` (`ℓ = 1` is the tree identity).
  `exists_stepWord_eq_of_entries` (WalkLaw) is the generalized helper.
- [Tree/FirstPassage](BGW/Tree/FirstPassage.lean): `walkWeight_append`;
  `length_eq_of_isForestCode_take` (uniqueness of the first passage time to `-ℓ`);
  `firstPassageWords ℓ N q = {x ∈ forestBridgeWords ℓ N | q ≤ N ∧ IsForestCode ℓ (x.take q)}`;
  `mem_firstPassageWords_iff` (for `q ≤ N`: a forest code of length `q` followed by a word of
  `forestBridgeWords 0 (N - q)`); `sum_indicator_firstPassageWords` (partition over `q ≤ N`, periodic
  words included); `tsum_firstPassageWords_walkWeight` (factorization through
  `forestWeight_eq_tsum_codes`); and the word-level convolution `tsum_forestBridgeWords_eq_sum`
  (`1 ≤ ℓ`, arbitrary `p`).
- [LocallyFinite/FirstPassageLaw](BGW/LocallyFinite/FirstPassageLaw.lean): `countForestBridges_zero`
  (`countForestBridges 0 m = {ω | ∑ i, ω i = m}`, `rfl`) and the main
  `pi_countForestBridges_eq_sum`:
  `Measure.pi (fun _ : Fin N => μ) (countForestBridges ℓ N) =
  ∑ q ∈ Finset.range (N + 1), forestWeight (fun d => μ {d}) ℓ q *
  Measure.pi (fun _ : Fin (N - q) => μ) (countForestBridges 0 (N - q))`
  for `IsProbabilityMeasure μ`, `1 ≤ ℓ`, every `N` (`P(S_N = -ℓ) = ∑_{q ≤ N} P(|𝒢_ℓ| = q)
  P(S_{N-q} = 0)`); `pi_countBridges_eq_sum` is `ℓ = 1`, with `bienaymeLaw μ (sizeEvent q)`.
- [LocallyFinite/BridgeLaw](BGW/LocallyFinite/BridgeLaw.lean): `countsOfWord n x` (left inverse of
  `stepWord`: `countsOfWord_stepWord`, `stepWord_countsOfWord`), `tsum_bridgeWords_walkWeight_mul`,
  `tsum_shift_weight_mul` (pairs `(t, i)` ↔ bridge words by `shiftEquiv`);
  `pi_countBridges_ne_zero_iff` (`P(S_n = -1) ≠ 0 ↔ n ≠ 0 ∧ bienaymeLaw μ (sizeEvent n) ≠ 0`);
  `isProbabilityMeasure_cond_pi_countBridges` (admissible, `n ≠ 0`); `cond_pi_countBridges_singleton`
  (atoms of `cond (Measure.pi (fun _ : Fin n => μ)) (countBridges n)`); and the uniform cyclic shift
  without a measure on finite trees: `cond_pi_countBridges_singleton_shift` (atom of the count vector
  of a rotation of the code of `t` is `n⁻¹ *` the atom of `t.toLocallyFinite` in
  `(bienaymeLaw μ)[|sizeEvent n]`) and `cond_pi_countBridges_apply_eq_tsum` (for every set `A`, the
  conditional bridge mass is `∑' (t, i), n⁻¹ * cond atom t * indicator A 1 (countsOfWord n
  ((t.increments).rotate i))`, no hypothesis: both sides vanish at inadmissible sizes and `n = 0`).
- [LocallyFinite/ExcursionLaw](BGW/LocallyFinite/ExcursionLaw.lean): `countExcursions n` (count
  vectors whose `stepWord` is an `IsTreeExcursion`, the event `{ζ(X) = n}`), `stepWord_mem_excursions_iff`,
  `tsum_excursions_walkWeight`, `pi_countExcursions` (`P(ζ(X) = n) = P(|T| = n)`),
  `pi_countExcursions_ne_zero_iff` (admissible size), `isProbabilityMeasure_cond_pi_countExcursions`,
  `cond_pi_countExcursions_eq_zero`, `cond_pi_countExcursions_singleton` (atoms), `stepWord_countsOfWord_increments`, and the law of the
  code of the size-conditioned tree without a measure on finite trees:
  `cond_pi_countExcursions_singleton_code` (the atom at the count vector of the code of `t` is the
  atom of `t.toLocallyFinite` in `(bienaymeLaw μ)[|sizeEvent n]`) and
  `cond_pi_countExcursions_apply_eq_tsum` (for every set `A`, the excursion mass is
  `∑' t : {t // t.size = n}, cond atom t * indicator A 1 (countsOfWord n t.increments)`, no
  hypothesis beyond `IsProbabilityMeasure μ`).

- [LocallyFinite/Generation](BGW/LocallyFinite/Generation.lean): `generation T n` is the finite set
  of present addresses of length `n`; `generationSize T n` is its cardinality. Root size is one,
  generation one is the root degree, and the next size is the sum of the child generation sizes.
  `generationSize_eq_zero_iff` identifies zero size with `extinctBy n`;
  `PlaneTree.generation_toLocallyFinite` and `generationSize_toLocallyFinite` preserve the existing
  finite-tree observable, with the explicit positive-address shift.
- [LocallyFinite/GenerationLaw](BGW/LocallyFinite/GenerationLaw.lean): `measurable_generationSize`,
  `cond_map_children_generationSize` (root degree `k`, guarded by `μ {k} ≠ 0`),
  `lintegral_children_of_degree` (also handles null degree classes),
  `lintegral_pow_generationSize_succ` and `lintegral_pow_generationSize`
  (`∫⁻ T, s ^ Z_n(T) ∂bienaymeLaw μ = (offspringGF μ)^[n] s`, every `s : ℝ≥0∞`, including `0, ∞`),
  `lintegral_generationSize_succ` and `lintegral_generationSize`
  (`∫⁻ T, Z_n(T) ∂bienaymeLaw μ = (∫⁻ k, k ∂μ)^n`, infinite mean allowed).
  No measurable instance, moment assumption or new probability-process framework is added.

The finite bridge interface is unchanged:

```lean
BGW.PlaneTree.positiveAddress                 -- List.map Nat.succ
BGW.PlaneTree.offspringAt_positiveAddress
BGW.PlaneTree.child_toLocallyFinite
BGW.PlaneTree.present_toLocallyFinite
BGW.PlaneTree.toLocallyFinite_injective
BGW.LocallyFinite.exists_toLocallyFinite_iff
BGW.PlaneTree.equivFiniteVertices
```

The last definition has type
`BGW.PlaneTree ≃ {T : BGW.LocallyFinite.Tree // BGW.LocallyFinite.FiniteVertices T}`.
Its surjectivity is proved by a finite height bound and `LocallyFinite.truncate`.
The original eight finite-tree modules and their declarations were left intact.

## Decisions that need to survive the handover

1. **Two address conventions, one explicit bridge.** Finite trees keep child
   indices starting at 0. The locally finite carrier keeps the source's positive
   indices, avoiding a reindexing of the whole probability development. Root is
   `[]` in both. Use `positiveAddress`; applying `Nat.pred` blindly would merge
   indices 0 and 1.
2. **Membership is `Present`.** A zero offspring coordinate can be a present
   leaf or an absent address. `child T j` is the leaf when `j` is absent;
   `child_toLocallyFinite` therefore has an explicit child-existence premise.
   Finiteness of the support of an offspring field does not count leaf vertices.
   `prune` keeps a count only at present addresses (`prune_val_of_present` with
   `not_present_offspring_zero`); a retained zero is a present leaf.
3. **Instances, checked.** The only instance added for the carrier is
   `PolishSpace Tree`. `MeasurableSpace Tree` is Mathlib's `Subtype.instMeasurableSpace`
   (induced by `MeasurableSpace.pi` on `Offspring`), and `BorelSpace Tree` is found by
   inference through `Subtype.borelSpace` and `Pi.borelSpace`; it equals `borel Tree`.
   **Do not** copy the `freezing1` instances `MeasurableSpace Tree := borel Tree`
   (a second, competing instance) or `MeasurableSpace Address := ⊤` (a global
   instance on `List ℕ`; nothing needs it, since the product σ-algebra only uses the
   values' space). Sets of addresses and finite products need no σ-algebra on `Address`.
   The branching, uniqueness, weight and atom modules add no instance, and `open scoped Classical`
   is confined to the statement of one theorem (`IsBienayme.cylinder_degree_measure`).
4. **Law instances are not the content.** `IsProbabilityMeasure (Measure.map f μ)` holds
   in Mathlib for every `f` (totalized `map`). The real statements are `measurable_prune`,
   `bienaymeLaw_apply`, `measurePreserving_prune` and `bienaymeLaw_map_degree`; use them
   rather than the instance when a proof needs the actual pushforward.
5. **Topology scope.** Trees have finite degrees, so a vertex of infinite degree
   (condensation, mentioned in `BGW_FORMALIZATION_ROADMAP.md`) is not a point of
   this carrier. The topology is the local topology of locally finite trees.
6. **No measurable structure on `PlaneTree`.** `equivFiniteVertices` is an ordinary `Equiv`;
   do not call it a `MeasurableEquiv`. `PlaneTree` is countable and deliberately has no
   `MeasurableSpace` instance (it would be a global instance on a core type). Everything the
   transport needs is stated in `Tree`: measurable singletons, `measurableSet_finiteVertices`,
   and `measurableEmbedding_toLocallyFinite` with `⊤` written explicitly. Keep it that way
   unless a consumer needs a `Measure PlaneTree`.
7. **The total finite mass is not 1.** `bienaymeLaw_finiteVertices` is the probability `q` that the
   tree is finite; it is `≤ 1` for every `μ`, is the least fixed point of `offspringGF μ` in `[0, 1]`
   (`isLeast_bienaymeLaw_finiteVertices`, no hypothesis beyond `IsProbabilityMeasure μ`), and can be
   `0` (`dirac 1`: `f s = s`, so `q = 0` despite mean one) or `1` (`dirac 0`: `f ≡ 1`), both checked in
   temporary probes and not library theorems. Its value is a statement about the mean of `μ`: it is
   `1` for mean `≤ 1` with `μ {1} ≠ 1` (`bienaymeLaw_finiteVertices_eq_one`), where the hypothesis
   `μ {1} ≠ 1` is necessary (`dirac 1`) and so is the mean bound (for `1/4 δ₀ + 3/4 δ₂`,
   `q ≤ 1/3`, probe only). For mean above one, including infinite mean,
   `bienaymeLaw_finiteVertices_lt_one` proves `q < 1`; its numerical value is not computed. State such hypotheses explicitly in the lemma that
   needs them. The indexing is fixed: `E_0 = ∅`, `E_1 = {leaf}`, `P(E_n) = f^[n] 0`.
8. **The finite API stays abstract.** Use `node`, `children`, `fold` and the
   proved bridge; the `WType` implementation is confined to `BGW/Tree.lean`.
9. **Walk weights need a support guard.** `walkWeight p x` uses `(a + 1).toNat`, so an
   entry below `-1` would contribute `p 0`. It is a step-law mass only on words with
   all entries at least `-1`. Existing excursions, bridge words and `stepWord` ensure this;
   preserve that condition in the forest extension rather than redesigning the weight API.
10. **Level-zero bridges are `forestBridgeWords 0`, not a new set.** The suffix after the first
   passage to `-ℓ` is a word of steps `≥ -1` and sum `0`, which is `forestBridgeWords 0 (N - q)`
   (`-((0 : ℕ) : ℤ)` is `0`), and at the count level `countForestBridges 0 m` (`rfl` to
   `{ω | ∑ i, ω i = m}`). The convolution keeps `1 ≤ ℓ` because `forestWeight_eq_tsum_codes` does;
   the empty forest `ℓ = 0` is outside the statements. The walk is cut at the first passage time, a
   deterministic first-passage fact about the word; no stopping time or Markov property on the
   measure is used.

## Supercritical classification and excursion law (proved), and what remains

`LocallyFinite/Supercritical` proves, for every offspring probability measure and in `ℝ≥0∞`
(infinite mean allowed): `bienaymeLaw_finiteVertices_lt_one` (mean `∫⁻ k, k ∂μ > 1` gives
`q < 1`), `bienaymeLaw_finiteVertices_eq_zero_of_singleton_one` (`μ {1} = 1` gives `q = 0`) and
`bienaymeLaw_finiteVertices_eq_one_iff` (`q = 1` iff mean at most one and `μ {1} ≠ 1`). The route
is `exists_lt_one_offspringGF_le` in `GeneratingFunction`: truncate the mean to
`M = ∑_{k<N} k μ{k} > 1`, take `x ^ N = 1/M`, and use `k x ^ N (1 - x) ≤ 1 - x ^ k` for `k ≤ N` to
get `f x ≤ x`; a sub-fixed point bounds `q` by monotone iteration. This avoids convexity and
derivatives, and `q` is not computed for mean above one (it is the least fixed point,
`isLeast_bienaymeLaw_finiteVertices`).

`LocallyFinite/ExcursionLaw` proves the excursion law, the counterpart of `map_dfsSeq_conditioned`
in `PoissonDeclumping`, in atom and expectation form (see the proved list). It follows the same
pattern as the cyclic shift: the excursion words are reindexed by count vectors through `stepWord`
(`tsum_excursions_walkWeight`), and the trees of size `n` are paired with the excursion vectors by
`increments_injective`, `countsOfWord_stepWord` and `isTreeExcursion_iff_existsUnique`. No measure
on `PlaneTree` and no map of measures is used.

## Current additions beyond the earlier proved list

- `GenerationField` and `GenerationProcess`: measurable finite histories, offspring-field
  independence across a generation and the complete next-size transition. Joint event masses
  cover null histories; conditional transitions retain the nonzero-history guard.
- `Tree/Tilting`, `LocallyFinite/Tilting`, `Geometric`: weight transformation, equality of
  conditioned laws for finite nonzero tilt factors, and geometric/uniform plane trees.
- `Tree/FringeWalk`, `FringeWeight`, `LocallyFinite/FringeLaw`: exact fringe blocks, weighted
  fringe convolution and the uniform-vertex formula in atomic form. This closes P9
  `cor:cyclicshift`; `Scalar/ForestBounds` also closes `lem:forest_estimates` in atomic form.
  The other 33 labeled P9 results remain open in this library.
- `Tree/Contour`, `ContourVertices`, `ContourInterpolation`: heights and addresses along the
  contour, endpoints, duration, unit graph steps, exact first DFS visits at `2*i-depth`,
  continuous polygonal interpolation and its nodal values. `Tree/Height` proves the
  Łukasiewicz record-minimum formula and exact ancestral/fringe intervals. `Tree/Geometry` gives LCA and
  the graph metric. `DegreeCount` and `DegreeConditioning` implement finite degree marks.
- `MetricMeasure`: 23 generic GHP source modules plus a local tightness transfer. The quotient
  uses whole compact nonempty carriers with Borel probability measures and Hausdorff plus
  Lévy–Prokhorov cost. It is complete/separable/Polish; forgetting to GH is nonexpansive,
  has compact inverse images of compact sets and preserves/reflects tightness of measure sets.
- `ContinuumTrees/RealTree`: complete four-point spaces with midpoints are real trees.
  Reuses Mathlib's `Metric.gromovProduct`. `Coding`, `CodingQuotient` and `CodingRealTree`
  now construct a compact real tree from a continuous real function, proving four points
  and actual midpoints. `CodingMeasure` supplies the root and genuine Lebesgue pushforward;
  `CodingStability` proves the 6-Lipschitz rooted coding map (4 unrooted). `CodingReroot`
  gives measured deterministic rerooting; `CodingScaling` identifies spatial scaling.
  Finite-tree embedding/density, the exact uniform sampler and metric/mass comparison give
  `FiniteTree.tendsto_rooted_scale_of_contour` in `ContourConvergence.lean`.
  BrownianBridge, Vervaat and VervaatBridge construct actual path/tree laws; the standard
  excursion/CRT identification is still open. Rooted GHP has separability, jointly
  continuous scaling, common-source bounds and G3 weak/sampled-law tools.
- `StableTrees`: scalar attraction definitions, lattice LLT/density, normalizer regular
  variation, Potter/Karamata, scalar and actual walk-maximum tightness, finite-variance
  supplier and the bridge from product-walk sums to the existing forest Kemperman law.
  `Scalar/ForestBounds` derives local/tail/weighted forest estimates, forest normalization
  for critical nondegenerate laws and two-sided size bounds on admissible sizes.

## Next bounded work and mathematical boundaries

Use the current resume snapshot at the top of this file. The following historical
foundation details remain useful, but the explicit pause and newer verification boundaries
above take precedence. Do not restart already compiled contour transfer or rooted completeness.

`StableDomain` contains scalar weak attraction with the normalized stable Laplace transform;
its LLT is derived. Finite variance supplies index two with limit variance two and normalizer
`σ * sqrt n / sqrt 2`. There is no stable process or height supplier yet. Only positive
indices require a positive normalizer.

Preserve GHP's source pseudometric/topology when upgrading to a metric, whole carriers
including zero-mass points, sum convention and no full-support premise. `GHSpace` has no
global measurable instance; the projection/tightness statements use a local Borel structure.

Source snapshots: GHP/real trees `8bace72d36cdf7d250414f3d98acfaa415de23d9` in `freezing2`;
stable scalar extraction `fc5ef722392b1af41e8b9d5fc45d5a521b7823dd` in
`arXiv-2607.22291v1 ` (the directory has a trailing space). Both are Apache-2.0. The earlier
roadmap inspection used an older stable-source snapshot; do not conflate them. Brownian
construction snapshots and the minimal compatibility port are documented under `vendor/`;
all existing Lean/Mathlib pins are unchanged.

## Latest verification checkpoint

On 1 November 2026, full `lake build` passed with **3599 jobs**, no warnings and unchanged
existing pins. The clean scratch consumer/axiom probe `/tmp/random-trees-current-review.lean`
and its `.log` checked **3067 constants from all 163 selected project and supplier modules**,
including private/generated constants. Only `propext`, `Classical.choice` and `Quot.sound`
occur. It includes all preceding checks plus unary/binary/singleton height conventions,
rooted second countability, actual uniform vertex sampling, Brownian endpoints, Vervaat
nonnegativity and the genuine coded-tree probability law. Full build log:
`/tmp/random-trees-full-milestone.log`. Rooted completeness and random-size convergence in
law are under development and excluded from this checkpoint. No permanent test framework
was introduced.

Independent interface and final source/proof reviews passed for these additions. Historical
evidence remains in [FORMALIZATION_REPORT.md](FORMALIZATION_REPORT.md). New files still being
developed must be compiled and audited before adding them to this checkpoint. Source scans
must ignore comments: a valid GHP docstring uses the English verb “admit”.

Commands from this checkout:

```sh
lake build
lake env lean /tmp/random-trees-current-review.lean
```

One coordinator runs shared builds; proof workers do not launch Lean/Lake concurrently.
No Comparator or Palomar submission verification, commit, push, rename or publication has
been performed. Work is paused. On authorized resumption, follow the current snapshot above;
make no claim of whole-project completion while any required direction remains open.
