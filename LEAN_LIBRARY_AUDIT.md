# Lean library audit for public reuse

Audit of this repository against the brief `lean_library_audit_agent.md` (version 1.0, 8 November 2026), for three
destinations: an independent library, Mathlib, and Tau Ceti. Audited snapshot: commit `a6879ba` on branch
`campaign/random-trees`, 8 November 2026.

**Method.** The audit was read-only: no source file, theorem statement, definition or dependency pin was changed.
Five independent reviewers ran Kimi K3.1 Pro through Open Math OS, three on this machine and two on the Open Math OS
team VM. Each owned one area:
- statement fidelity of the Skorokhod/probability layer, of the stable process and excursions, and of trees/GHP;
- API and interoperability;
- documentation, packaging and a clean-environment build.

Claude (Opus 5.5) coordinated them. It verified each substantive finding against the source, ran the external
consumer test and Mathlib's default linters, and checked the current Mathlib and Tau Ceti contribution policies.
Working notes and logs are in the local, untracked folder `.orchestration/audit/`. The evidence that matters is
quoted below.

**Assurance.** Kernel checking, the transitive axiom audit and the clean build cover the whole library. The
fidelity review read statements and the definitions they use. For the central results it was exhaustive over the
coverage index, but it did not re-review proof bodies. The API review sampled six central objects.

## A. Executive assessment

**Independent library.** The mathematics is in good condition, but the library is not yet adoptable by others.
- No statement-fidelity defect of P0 or P1 severity was found. The reviewers covered every corrected, bypassed or
  equivalent row of `CLASSICAL_THEORY_COVERAGE.md`, all main exact rows of C1–C39, and the original BGW results.
- Proofs are kernel-checked with only `propext`, `Classical.choice` and `Quot.sound`.
- The complete repository check reproduces from scratch in a clean environment.
- An external project can use the snapshot through a path dependency (Appendix C).

Three things block adoption:
- **Not published.** The audited code exists only on an unpushed local branch; GitHub `main` is the older
  plane-tree library (`d818312`).
- **Stale documentation.** The README and the top-level module docstrings describe the 2 November library and call
  delivered results open.
- **No install route.** No tested installation procedure is documented for a fresh user.

None of these needs a change to the mathematics.

**Mathlib.** Several vendor-free components are plausible candidates:
- the compact-horizon Skorokhod space `D T E` with J1, Billingsley's metric d°, measurability and tightness;
- Lévy–Prokhorov tools and the measured, rooted GHP spaces;
- real trees and continuous coding;
- generic weak-convergence and convergence-in-measure tools;
- after discussion with maintainers, `PlaneTree`.

Each would be a new theory for Mathlib, so its policy calls for a Zulip discussion first. Contributions should be
small PRs by a human contributor who understands the code, with AI use disclosed and the `LLM-generated` label.

The obstacles are concrete:
- The basic local-path layer `DLoc` imports the vendored KolmogorovExtension4, and the Brownian layer imports the
  vendored BrownianMotion; neither is Mathlib (P1-3).
- The stable law's construction pulls in 64 BGW modules (P2-4).
- Mathlib's default linters report 25 problems in the general layer (P2-2).
- 26 generic files use the application namespace `BGW.StableTrees` (P3).

**Tau Ceti.** There is a close technical fit with the three local roadmap drafts in `tauceti-roadmaps/`
(Bienaymé–Galton–Watson trees, GHP topology, continuum random trees), whose milestones map onto vendor-free
modules. Those drafts were never submitted, and Tau Ceti admits new mathematics only through human-curated
roadmaps. A port must also meet Tau Ceti's rules:
- track Mathlib `master` rather than the v4.35.0 pin;
- contain no `set_option` at all (BGW has 46, almost all in `StableTrees`; the GHP, CRT and discrete BGW layers have
  one between them);
- keep no compatibility layer, with one topic per PR;
- follow the roadmap's specification rather than this repository's.

The stable-process and excursion layer has no Tau Ceti roadmap. The local drafts list stable trees as a scope
boundary, so that layer belongs to the independent library unless a new roadmap is proposed.

## B. Baseline and coverage

| Item | Value |
| --- | --- |
| Repository | `github.com/igor-kortchemski/Bienayme-Galton-Watson-Trees` (origin); audited branch `campaign/random-trees`, commit `a6879ba`, **not pushed** (origin `main` = `d818312`) |
| Working tree | Tracked Lean, Lake and docs are exactly `a6879ba`. Uncommitted `.agents/`, `AGENTS.md` (skills upgrade to v2.0.0) are out of scope. Ignored and untracked: `.orchestration/`, `papers/`, `tauceti-roadmaps/`. |
| Toolchain | `leanprover/lean4:v4.35.0` |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` (v4.35.0), Lake `rev` pinned to that commit |
| Other dependencies | Vendored path packages `vendor/brownian-motion` and `vendor/kolmogorov-extension4`, Apache-2.0, upstream revisions and adaptations recorded in their READMEs. Mathlib's transitive packages (batteries `66e4691`, aesop `4a174c4`, Qq `dce0ad7`, proofwidgets `df72b02`, importGraph `a41f0e9`, LeanSearchClient `d6b4c7b`, plausible `dfa4f38`, Cli `c24fe60`). No Tau Ceti dependency. |
| Size | 865 BGW Lean files (151,812 lines in the seven source directories) and 30 vendored modules. `StableTrees` alone has 613 files. |
| Build configuration | `lakefile.toml`: default target `BGW`, `globs = ["BGW.*"]`, `requiresModuleSystem = true`. Options: `autoImplicit = false`, `warningAsError = true`, style linters `header`, `native`, `maxHeartbeats`, `longFile = 1500`. `BGWTest/` is outside the default target; `scripts/check.py` and CI compile it. |
| Quality checks | `scripts/check.py`: builds `BGW` plus every vendored module, compiles both `BGWTest` files with warnings as errors, then generates an `import all` audit that checks every constant (private and generated included) for the three standard axioms and runs `#lint only docBlame in BGW`. CI (`.github/workflows/lean.yml`) runs exactly this script, with the Mathlib cache. |
| Informal sources | `CLASSICAL_THEORY_INPUTS.md` (C1–C39 with corrections (a)–(m)), `CLASSICAL_THEORY_COVERAGE.md` (231 rows), `FORMALIZATION_REPORT.md`, the published arXiv sources under `papers/` (ignored, local), audited contracts under `.orchestration/contracts/` (local). |

**Coverage.** "Exhaustive", "sampled" and "not performed" are as stated.

| Check | What ran | Outcome |
| --- | --- | --- |
| Clean-environment build | `python3 scripts/check.py` on the Open Math OS VM from an archive of the tracked tree at `a6879ba`. The VM's preinstalled Lean 4.35.0 and `/opt/mathlib` matched the pins, and each package `HEAD` was checked against the manifest. 864 BGW and 30 vendored modules were compiled, none replayed. | **PASS**: 4,420 jobs, 7.5 min. Agrees with the local fresh-worktree check at `87d240c`, which has the same Lean sources. |
| Transitive axiom audit | Generated `import all` audit over all 895 project and vendored modules | **PASS**: 12,803 constants, only `propext`, `Classical.choice`, `Quot.sound` |
| Documentation lint | `#lint only docBlame in BGW` | **PASS**: 0 errors in 7,578 declarations |
| Mathlib default linters | Coordinator probe: `#lint in BGW` with all of `BGW/{Probability,Skorokhod,MetricMeasure,Tree,LocallyFinite}` and `BGW.GeneratingFunction` imported (15 linters) | **25 errors in 1,969 declarations**: 9 `simpNF`, 16 `unusedArguments` (P2-2). `StableTrees` was not linted. |
| Trust scan | Exhaustive regex scans of the assigned areas for `sorry`, `admit`, `axiom`, `native_decide`, `opaque`, `implemented_by`, `@[extern]`, heartbeat raises | No escape hatch. 7 local `maxHeartbeats` raises, each with a comment. |
| Fidelity: C1–C14, C31–C36 | All 33 corrected, bypassed or equivalent rows; every row of C1, C3, C4, C8–C11, C13–C14, C31–C36; 6 sampled exact rows; central definitions of `D`, `DLoc`, J1, d°, the measurable structure, weak convergence and tightness; one elaborated-type probe | No finding |
| Fidelity: C15–C25 | Every non-article-side row read with the definitions it uses (stable law, kernels, process laws, filtrations, reflected process, excursion measure, unit and tail laws, Markov property under N, Γ_a, Chaumont); no elaborated-type probe | No finding |
| Fidelity: C26–C30, C37–C39 | 56/56 rows; height/contour, forest, Łukasiewicz, coding, GH/GHP, Lévy–Prokhorov and leaf-measure definitions | One P2 (P2-1) |
| Fidelity: original BGW | Main results of the generating-function, branching, extinction, size and degree conditioning, walk/forest/excursion laws, tilting, fringe and generation modules, with degenerate offspring laws checked; some helpers sampled (listed in L2 notes) | No finding |
| API and interoperability | 6 central objects (`D`/`DLoc`, rooted and unrooted GHP, real/coded trees, plane and locally finite trees, tagged excursions, stable law/process); exhaustive import-graph, namespace, instance, simp, notation, `set_option` and file-size scans; reuse search in pinned Mathlib and the vendored packages | Findings P1-3, P2-3 to P2-6, P3 |
| External consumer | Separate Lake project, `require bgw` by local path to a fresh clone at `a6879ba`, two examples with five declarations (Appendix C) | **Compiles**; friction recorded in P2-7 |
| Policies | Mathlib contribution and AI pages; Tau Ceti `README`, `AGENTS.md`, roadmap `CONTRIBUTING.md`, review rubric `_common.md`, read 8 November 2026 | Used in A and D |
| Not performed | Network installation (`git clone` plus `lake exe cache get`; both builds used the pinned packages already present); a hosted CI run of this snapshot (it is not pushed); comparison with Mathlib `master` (no counterpart claims beyond the pin); doc-gen4 generation (not configured); semantic re-review of proof bodies; `#lint` on `StableTrees`; performance benchmarking | See remediation |

## C. Prioritized findings

No P0 finding: no advertised result was found materially misrepresented, and the trust model is as claimed.

### P1-1 — The audited library is unpublished and has no tested installation route

- **Goal:** independent library.
- **Location:** repository state; `README.md:47-61, 174-202`; `.github/workflows/lean.yml`.
- **Evidence:**
  - The campaign branch is local only; origin `main` is `d818312`, which has none of the classical-theory layer.
  - The README's consumer recipe is a sibling `path = "../BGW-formalization"` dependency and states that no complete
    published commit is claimed.
  - There is no clone step, no `lake exe cache get`, and no Git-pinned `require` snippet.
  - Only CI configures the Mathlib cache.
- **Consequence:**
  - Nobody else can obtain the audited code.
  - Once published, a new user still has no tested path from clone to cached build, and a cold build compiles
    Mathlib.
- **Remedy:**
  1. Decide on publication. That is the owner's decision and outside the audit.
  2. Then document clone, elan, `lake exe cache get`, `lake build` and `python3 scripts/check.py`.
  3. Give a `[[require]]` snippet pinned to a published full commit.
  4. Let CI run on the published branch.
- **Verification:** in an empty directory, with no reused `.lake`, follow only the README over the network, then
  build an external consumer pinned by `rev`.
- **Confidence:** confirmed.

### P1-2 — The front-door documentation contradicts the delivered library

- **Goal:** independent library; Mathlib and Tau Ceti scoping.
- **Location:** `README.md:72-137, 174-182`; `BGW.lean:58-100`; `BGW/StableTrees.lean:117-120`;
  `FORMALIZATION_REPORT.md:5` and its older "open" sections.
- **Evidence:**
  - `README.md:129-137` says Vervaat strict positivity and identification with the Brownian CRT "remain open".
  - The same lines say the scalar results "do not construct a stable process or a continuum tree law".
  - The report and the coverage index record all of these as delivered (C19, C26–C30, C33–C35, C37–C39).
  - The README's figures are the 2 November ones (170 modules, 3,175 constants); the current figures are 865 + 30
    modules and 12,803 constants.
  - `BGW/StableTrees.lean` imports the stable-process modules while its docstring says they are not constructed.
  - The README does not link `CLASSICAL_THEORY_COVERAGE.md`, the best index of the library's results.
- **Consequence:** a new user is steered away from the main results and cannot see the current scope and
  limitations. These are understatements, not false claims of proof.
- **Remedy:** rewrite the README scope, figures and limitations from the 8 November checkpoint, and link the
  coverage index and its import map. Mark older report sections as historical, and update the docstrings of
  `BGW.lean` and `BGW/StableTrees.lean`.
- **Verification:** check every "open" or "remaining" claim against the coverage index; `python3 scripts/check.py`.
- **Confidence:** confirmed (coordinator read the cited lines).

### P1-3 — Vendored non-Mathlib packages sit inside foundational layers

- **Goals:** Mathlib, Tau Ceti. For the independent library the vendoring itself is acceptable.
- **Location:**
  - `BGW/Skorokhod/PathLawFamily.lean:13` (`public import KolmogorovExtension4.KolmogorovExtension`), publicly
    imported by `BGW/Skorokhod/DLoc.lean:8`;
  - `BGW/ContinuumTrees/BrownianBridge.lean:8`;
  - `BGW/StableTrees/HeightContinuityHolder.lean:9-10`, `HeightContinuityKolmogorov.lean:11-12`.
- **Evidence:**
  - Import-closure scan: 5 of 80 `BGW.Skorokhod*` modules, 10 of 35 `BGW.ContinuumTrees*` and 482 of 614
    `BGW.StableTrees*` depend on a vendored package.
  - So the carrier, evaluation σ-algebra, restriction and shift of `DLoc` cannot be imported without
    KolmogorovExtension4.
  - The Brownian layer uses the vendor's global `brownian`/`gaussianLimit` (`BrownianBridge.lean:51-83`).
- **Consequence:** basic local paths, the local stable law and the Brownian CRT layer cannot be extracted to Mathlib
  or Tau Ceti as packaged. By contrast, the compact `D T E`, all of `MetricMeasure` and the deterministic coding are
  vendor-free.
- **Remedy:**
  - Split `DLoc.lean` into (a) carrier, σ-algebra, restriction, shift and filtration, and (b) the projective-law
    construction, with only (b) importing KolmogorovExtension4.
  - Parameterize the Brownian bridge and CRT modules over a Wiener-process supplier.
  - Both change import paths, so they are design decisions.
- **Verification:** recompute import closures; a file importing only the basic `DLoc` module has no vendored
  dependency.
- **Confidence:** confirmed.

### P2-1 — C27–C29 require a monotone norming while the coverage index calls them exact

- **Goal:** independent library (downstream article use); interface for extraction.
- **Location:** `BGW/StableTrees/Defs.lean:56-68` (`StableDomain`, field `monotone : Monotone a`); main statements
  `ForestTriple.lean:101`, `ForestTripleVector.lean:90`, `TailPair.lean:175`, `ExactContourJoint.lean:35, 95`;
  `CLASSICAL_THEORY_COVERAGE.md:416, 430, 445, 603`.
- **Evidence:**
  - All three exports take `StableDomain μ θ B`, which bundles a monotone, positive `B`.
  - The specification allows any admissible positive norming and calls monotonicity "never essential".
  - The coverage index lists C27 and C28 main rows as exact and mentions the restriction only as a "residual wording
    point, none a gap".
  - `IsRealStableAttracted` already supports non-monotone normings for the walk FCLT, but no forest, tail or
    exact-contour wrapper uses it.
- **Consequence:** the theorems are correct and non-vacuous; every domain admits a monotone norming. However, a user
  holding a given non-monotone norming cannot apply them directly, and the "exact" label overstates the interface.
- **Remedy:**
  - Add wrapper theorems under the non-monotone attraction predicate. One route: compare with a monotone admissible
    norming through `IsRealStableAttracted.tendsto_norming_ratio`, then transfer by Slutsky. This adds API without
    changing frozen statements, and the route is likely to work but untested.
  - Or relabel the rows "equivalent (monotone norming)".
- **Verification:** a consumer example with an oscillating, asymptotically equivalent norming that derives C27, C28
  and C29.
- **Confidence:** confirmed for the interface gap.

### P2-2 — Mathlib's default linters report 25 problems; the standard linter set is not configured

- **Goals:** Mathlib, Tau Ceti; maintenance.
- **Location:** `lakefile.toml:7-13`; `scripts/check.py:65`; `.orchestration/audit/lint/lint.log` (local).
- **Evidence:** `#lint in BGW` over the general layer and the original BGW modules gave "Found 25 errors in 1969
  declarations … with 15 linters".
  - **`simpNF` (9):** these simp lemmas are not in simp normal form: `Coding.circularProjection_{zero,one}`,
    `Coding.reroot_{zero,one}`, `Vervaat.rotate_{zero,one}`, `Vervaat.vervaat_{zero,one}`,
    `PlaneTree.fringe?_node_cons`.
  - **`unusedArguments` (16):** for example `[OpensMeasurableSpace (D T E)]` in
    `Skorokhod.isTightMeasureSet_of_cadlagModulus`, plus arguments of `ghpCosts`, `ghpDistance_self`,
    `rootedGHPCosts`, `rootedGHPDistance_self`, `Skorokhod.tendsto_map_splitProdWithCont`,
    `CompatiblePaths.measure_ext`, `LocallyFinite.offspringFieldLaw` and 6 private helpers.
  - **Configuration:** `check.py` runs only `docBlame`. `weak.linter.mathlibStandardSet` and
    `linter.style.longLine` are not enabled, and 39 lines in 25 files exceed 100 characters.
- **Consequence:** Mathlib and Tau Ceti CI would reject these declarations as they stand. The simp lemmas can also
  make `simp` loop or miss in downstream proofs.
- **Remedy:**
  - Fix the `simpNF` lemmas: restate them, or drop `@[simp]`.
  - Remove the unused arguments.
  - Add a non-blocking CI job running `#lint` and the Mathlib standard set, then make it blocking.
- **Design decision:** some unused arguments are in frozen statements (`isTightMeasureSet_of_cadlagModulus` in
  `CT4_Tightness`, `tendsto_map_splitProdWithCont` in `CT10_G3`, `offspringFieldLaw` reachable from several CT8
  records). Removing them changes public statements and needs new freeze records.
- **Verification:** `#lint in BGW` with 0 errors over the full library, `StableTrees` included.
- **Confidence:** confirmed.

### P2-3 — 46 `set_option` uses, concentrated in `StableTrees`

- **Goals:** Tau Ceti (forbidden outright), Mathlib (justification needed); Lean upgrades.
- **Location:** 29 `StableTrees` files and `Probability/PoissonCharacterizationBasic.lean:38`.
- **Evidence:** `rg '^\s*set_option' BGW` gives:
  - 36 `backward.isDefEq.respectTransparency false`;
  - 7 `maxHeartbeats` (400000 three times, 500000 twice, 800000 twice, each local with a comment);
  - 2 `warn.classDefReducibility false`;
  - 1 `linter.unusedVariables`.

  `Skorokhod`, `MetricMeasure`, `ContinuumTrees`, `Tree` and `LocallyFinite` have none.
- **Consequence:**
  - These modules cannot enter Tau Ceti unchanged.
  - The `backward.*` options are transition flags that a later Lean release may remove, which would break 36 proofs
    at once.
- **Remedy:** replace each `respectTransparency` use by an explicit `unfold`, `show` or `erw`, or by a
  definitional lemma; reduce heartbeat needs by splitting proofs. Track the count in CI.
- **Verification:** `rg '^\s*set_option' BGW` count goes down; build without the options.
- **Confidence:** confirmed.

### P2-4 — The stable law's construction is coupled to the BGW attraction development

- **Goal:** Mathlib; modular reuse.
- **Location:** `BGW/StableTrees/StableLaw.lean:36-65`.
- **Evidence:**
  - `stableLaw` is defined analytically, but its probability proof obtains `exists_stableDomain`.
  - That result is built from a critical offspring law with a Pareto tail.
  - The import closure is 64 BGW modules below `StableLaw` and 112 below `StableProcessLaw`.
- **Consequence:** the θ-stable distribution cannot be proposed as a focused Mathlib module.
- **Remedy:** give `stableLaw` an analytic existence route, and keep `exists_stableDomain` as an application
  theorem. This changes proofs and imports only, not statements.
- **Verification:** the closure of `StableLaw` no longer contains BGW attraction modules.
- **Confidence:** confirmed for the dependency. No shorter construction in the repository is claimed.

### P2-5 — Path-space generality gaps

- **Goals:** independent library, Mathlib.
- **Location and evidence:**
  - **`DLoc` is real-valued only, with no topology.** `BGW/Skorokhod/DLoc.lean:42` defines
    `DLoc := {f : ℝ≥0 → ℝ // IsCadlag f}`, with only an evaluation σ-algebra and no topology or metric in `BGW/`.
  - **No postcomposition on `D`.** There is no generic map `D T E → D T F` by a continuous function, although pinned
    Mathlib has `IsCadlag.continuous_comp` (`Mathlib/Topology/Order/Cadlag.lean:119`).
  - **Scaling needs a ring.** Time–space scaling requires `[NormedRing E]` where `[NormedSpace ℝ E]` with a real
    factor suffices (`Skorokhod/Scaling.lean:28`, `ScalingContinuous.lean:27`, `ScalingMultiplication.lean:22`).
- **Consequence:**
  - Vector-valued local paths cannot be represented.
  - Local weak convergence cannot be stated natively.
  - Continuous-mapping applications to coordinates and norms need bespoke code.
- **Remedy:** add `D.postcomp` with simp and Lipschitz lemmas, a `NormedSpace` scaling variant and `DLoc E`. These
  are additive; changing `DLoc` itself is a design decision.
- **Verification:** examples with `Fin d → ℝ` paths and a coordinate projection.
- **Confidence:** confirmed. How far a local J1 topology is in scope is the owner's call.

### P2-6 — GHP quotient operations are asymmetric; a generic bridge sits in the CRT layer

- **Goals:** Tau Ceti (GHP draft, milestone 6), Mathlib.
- **Location:** `BGW/MetricMeasure/RootedScaling.lean:83, 93, 270-318`;
  `BGW/ContinuumTrees/CodingGHCompat.lean:39-60`.
- **Evidence:**
  - Quotient-level scaling exists only on `RootedMeasuredGHSpace`; there is no `MeasuredGHSpace.scale`.
  - The forgetful map from rooted measured to plain GH spaces (`forgetToGH`), with its continuity and law
    transport, is defined in `ContinuumTrees`.
- **Remedy:** add the unrooted quotient `scale`, and move `forgetToGH` to `MetricMeasure`. The move changes a module
  path.
- **Verification:** both quotients have `scale_one`, inverse and continuity lemmas, and `ContinuumTrees` imports
  rather than owns the bridge.
- **Confidence:** confirmed.

### P2-7 — Examples and discoverability for users

- **Goal:** independent library.
- **Evidence:**
  - **README snippets.** Two README snippets (`increments`, `ofIncrements?`) are not compiled anywhere.
  - **Test coverage.** `BGWTest` has no stable-process, excursion, height or forest-limit example.
  - **Lake warnings.** The external consumer (Appendix C) compiled, but Lake warns on every import from a non-module
    file: "designed for use with the module system; consider adding `module`".
  - **`wienerD` namespace.** The library's Donsker theorem lives in `BGW.StableTrees` but states its limit with
    `wienerD`, which is in `BGW.ContinuumTrees.BrownianD`, a namespace the user must find and open.
  - **`maxJump` lemma placement.** The basic lemma `maxJump_eq_zero_of_continuous` (C36.a4) is in
    `BGW.Skorokhod.OptionalGaps`, not `BGW.Skorokhod.Jump`.
- **Remedy:**
  - Compile the README snippets and the Appendix C examples in `BGWTest`.
  - Say in the README how a non-module consumer is treated.
  - Move the basic `maxJump` facts into `Jump.lean` (a module move; the name is unchanged).
- **Verification:** `scripts/check.py` compiles the new examples; a README fence diff.
- **Confidence:** confirmed (the consumer build logs are in `.orchestration/audit/consumer/`).

### P2-8 — No generated API documentation

- **Location:** no doc-gen4 configuration or workflow.
- **Consequence:** 895 modules are navigable only through source and long Markdown files.
- **Remedy:** a pinned doc-gen4 setup and a reproducible generation command; publishing is optional.
- **Confidence:** confirmed.

### P2-9 — Release, migration and maintenance ownership are implicit

- **Location:** `lakefile.toml:2` (`version = "0.1.0"`); `README.md:3-5, 58-70`.
- **Evidence:** there is no changelog, release or deprecation policy, contribution guide beyond a short section, or
  named maintainer contact.
- **Remedy:** a short maintenance section covering owner, pin policy, changelog and upgrade approach.
- **Confidence:** confirmed for the tracked tree.

### P2-10 — Provenance and review evidence are outside the repository

- **Location:** `FORMALIZATION_REPORT.md:374-376, 450-454`; `.gitignore:13`.
- **Evidence:**
  - The report says the `freezing1` sources behind core `LocallyFinite` modules have no identified committed
    snapshot.
  - The audited contracts (`.orchestration/contracts/`, 211 files), the freeze records
    (`~/LeanFormalization/BGW-campaign-records/`) and the milestone logs are local and ignored.
- **Consequence:** build and axiom claims can be rerun from the repository, but statement-freeze and review evidence
  cannot be inspected from it.
- **Remedy:**
  - Record the `freezing1` origin and revision.
  - Publish a minimal, non-operational evidence package: contracts and freeze-record hashes.
- **Confidence:** confirmed.

### P3 — Aggregated polish

- **Generic code in the application namespace.** 26 generic files outside `StableTrees` declare `BGW.StableTrees*`
  namespaces (23 in `Probability`, e.g. `ConvergenceInMeasure.lean:25`). Rename them by topic before any upstream
  move; this changes names and is a design decision.
- **Agent-operational files.** `HANDOVER_CLAUDE.md`, `AGENTS.md`, `CLAUDE.md` and the large roadmaps are tracked.
  Six absolute `/Users/igor/...` links appear in `RANDOM_TREES_ROADMAP.md` and `HANDOVER_CLAUDE.md`, two of them
  broken. Label these files as internal or move them before publication.
- **Vendored headers.** 14 of 26 vendored Brownian files lack per-file headers, while
  `vendor/brownian-motion/README.md:6` says notices are preserved in each file. Compare with upstream; do not invent
  authors.
- **Long files.** 8 files exceed 800 lines (largest `KaramataTransforms.lean`, 932). No split is needed except where
  P1-3 asks for one.

## D. Ordered remediation plan

**1. Adoption blockers.** No change to statements or names.
1. Owner's decision on publishing `campaign/random-trees`, and how.
2. README, `BGW.lean` and `StableTrees.lean` docstrings rewritten from the current checkpoint, with links to the
   coverage index and import map (P1-2).
3. A tested installation route and a Git-pinned consumer snippet (P1-1).
4. Compiled README snippets and the Appendix C examples in `BGWTest` (P2-7).
5. Maintenance and release section (P2-9); `freezing1` provenance and a minimal evidence package (P2-10).

**2. Quality gates.** Mostly no API change.
1. Fix the 9 `simpNF` lemmas and the non-frozen unused arguments.
2. Enable `longLine` and the Mathlib standard linter set in CI, first non-blocking.
3. Run `#lint` on `StableTrees`.
4. Reduce the 46 `set_option` uses, starting with `backward.isDefEq.respectTransparency` (P2-2, P2-3).
5. doc-gen4 (P2-8).

**3. Structure and API.** These need explicit design decisions because they change public statements, names, imports
or dependencies.
- Unused arguments in frozen statements (new freeze records needed).
- `DLoc` split and the Brownian supplier interface (P1-3; import paths).
- Analytic construction route for `stableLaw` (P2-4; imports).
- Topic namespaces for the 26 generic files (P3; names, with no compatibility aliases if the destination is Tau
  Ceti).
- `D.postcomp`, a `NormedSpace` scaling variant, `DLoc E` (P2-5; additive except `DLoc E`).
- Unrooted GHP `scale` and the `forgetToGH` move (P2-6; one module path).
- Non-monotone wrappers for C27–C29, or relabelled coverage rows (P2-1; additive).

**4. Upstream routes.** Separate from each other and from the independent library.

*Tau Ceti:*
1. Update the three local roadmap drafts, written to be implementable fresh with this repository as a cited source.
2. Submit them as human-reviewed roadmap PRs with AI attribution. The CRT draft first needs its Brownian supplier
   reconciled with the StochasticCalculus proposal.
3. Port only vendor-free modules (GHP; deterministic CRT; discrete BGW), against Mathlib `master`, with no
   `set_option` and one topic per PR.
4. The stable and excursion layer has no roadmap: keep it in the independent library or propose a new roadmap.

*Mathlib:*
1. Start a Zulip discussion of `D T E` with J1 and d°, and of measured GHP, as new theories.
2. Then send small PRs from a human contributor who understands each, with AI disclosure and the `LLM-generated`
   label. Generic probability lemmas first, after a case-by-case check against current Mathlib.
3. Resolve the vendored dependencies first for anything touching `DLoc` or Brownian motion.

**Strengths to preserve:**
- The J1 metric and Billingsley's d° live on distinct types joined by an identity homeomorphism (`DComplete`), so
  the ordinary J1 topology is never silently replaced.
- Totalized operations are visible and fenced. Junk values outside `1 < θ ≤ 2` are documented; finite-stopping-time
  hypotheses block `⊤` junk; integrability accompanies signed Γ identities; null conditioning events are explicit.
- Hard conclusions are theorems, not structure fields: `IsStableLevyLaw` holds only the start and increments, and N
  is built from the passage-jump point process.
- Degenerate cases are genuine:
  - extinction is classified for arbitrary offspring laws, with infinite means and `μ{1} = 1` included;
  - C29 runs along every unbounded admissible sequence, periodic laws included;
  - tail conditioning is shown to be non-null.
- No upward imports: nothing in `Probability`, `Skorokhod`, `MetricMeasure`, `Tree` or `LocallyFinite` imports
  `StableTrees` or `ContinuumTrees`. Global instances are restrained (72, all on BGW types) and there is no notation.
- `CLASSICAL_THEORY_COVERAGE.md` maps 231 subclaims to exact declarations and modules.
- One maintained command, which CI also runs, covers the build, consumer files, transitive axioms and docBlame.

## Appendix A — Status of `AUDIT_QUALITE_MATHLIB_UX.md` (2 November 2026)

| Earlier recommendation | Status at `a6879ba` |
| --- | --- |
| §4 P1: repair Minimum/Marchal; verify every delivered module | Resolved: the glob covers all sources, and `check.py` and CI build every module. |
| §4 P1: synchronize README, report and roadmap | Partly: the earlier fixes hold, but new drift appeared (P1-2). |
| §4 P1: reproducible source set | Resolved for the source package, which builds from a clean archive. Publication is open (P1-1). |
| §4 P2: durable consumers, axiom audit, CI | Resolved: `BGWTest`, a generated transitive audit, CI. |
| §4 P2: enable relevant Mathlib linters | Partly: four style linters; standard set and `longLine` absent; 25 default-lint errors (P2-2). |
| §4 P2: clear docBlame findings | Resolved: 0 errors in 7,578 declarations. |
| §4 P2 / §7 C: headers, authors, style | Partly: all 865 files have headers; 39 long lines remain. |
| §5.1: compiled first README example | Resolved (`README.md:7-18`, `BGWTest/Examples.lean:19-20`). |
| §5.2: real URL and commit-pinned consumer | Partly: URL present, no pinned-`rev` recipe (P1-1). |
| §5.3: BGW probability, GHP, coding and scalar examples | Partly: present; newest APIs uncovered (P2-7). |
| §5.4: conventions table | Resolved (`README.md:34-45`). |
| §5.5: contribution section | Resolved at a basic level; maintenance and release open (P2-9). |
| §5 API: children extensionality; C2 measurability example | Resolved (`BGW/Tree.lean:51`, `BGWTest/Measurability.lean`). |
| §6: lighten rooted-scaling imports | Resolved (`RootedScalingBase.lean:8-9`). |
| §6: search upstream equivalents, prepare small candidates | Search done by this audit: no central duplication found at the pin (section D, step 4). Preparation open. |
| §6: isolate Brownian dependencies for Mathlib | Open (P1-3). |
| §6: human understanding and AI disclosure for submissions | Not yet applicable (no PR); the policy is restated in section D. |
| §7: preserve pins; avoid wholesale re-encoding | Resolved: original pins kept; `WType` stays internal. |
| §7: defer a documentation portal | Obsolete at the current size: reconsider (P2-8). |
| §9 figures (3,641 jobs, 170 modules) | Obsolete: current figures are in section B. |

## Appendix B — Commands and outcomes

- **Clean build on the VM:** `python3 scripts/check.py` → `Build completed successfully (4420 jobs)`; `Axiom audit
  passed: 12803 constants from 895 modules.`; `Found 0 errors in 7578 declarations … All linting checks passed!`
- **Default linters:** `python3 .orchestration/bin/lake_gate.py env lean .orchestration/audit/lint/LintGeneral.lean`
  → `Found 25 errors in 1969 declarations (plus 1435 automatically generated ones) in BGW with 15 linters`.
- **Consumer:** `lake update` in `.orchestration/audit/consumer/app` resolved `bgw` by path and the 11 inherited
  packages at the pinned revisions. It warned that the vendored packages have no `lake-manifest.json`; this is
  harmless, since they inherit the root pins.
- **Consumer build:** `lake build` → `Build completed successfully (3922 jobs)`. The snapshot's build artifacts were
  copied from an identical-source build, so this tests resolution, packaging and the API, not compilation from
  scratch (the VM run covers that).
- **Snapshot state:** `git rev-parse HEAD` = `a6879ba…`; `git status` lists only `.agents/` and `AGENTS.md`.
- **Mechanical scans:** `rg '^\s*set_option' BGW | …` gives 46 uses in 30 files; a Python scan finds 39 lines over
  100 characters in 25 files.

## Appendix C — External consumer examples

A separate Lake project with `[[require]] name = "bgw", path = "../bgw"` (a fresh clone at `a6879ba`). These are
narrow imports with no `module` header. All five declarations compile.

```lean
import BGW.StableTrees.ExcursionJump
import BGW.StableTrees.StableProcessBrownian
import BGW.Skorokhod.Jump
import BGW.Skorokhod.OptionalGaps
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory Filter Topology
open BGW.Skorokhod BGW.StableTrees BGW.ContinuumTrees BGW.ContinuumTrees.BrownianD

-- 1. Construct normalized stable excursions and apply C22.
example : ∀ᵐ x ∂(levyExcLaw (3 / 2) : Measure (D 1 ℝ)), 0 < maxJump x :=
  ae_maxJump_pos_levyExcLaw (by norm_num) (by norm_num)

example : levyExcLaw (3 / 2) ≠ levyExcLaw 2 := by
  intro h
  have h1 := ae_maxJump_pos_levyExcLaw (θ := 3 / 2) (by norm_num) (by norm_num)
  have h2 := ae_maxJump_eq_zero_levyExcLaw_two
  rw [h] at h1
  have : ∀ᵐ x ∂(levyExcLaw 2 : Measure (D 1 ℝ)), False := by
    filter_upwards [h1, h2] with x hx1 hx2
    linarith [hx2.1]
  simpa using (ae_iff.1 this)

-- 2. A new consequence: the largest rescaled jump of a critical finite-variance
--    Lukasiewicz path converges in law to 0 (library Donsker + library Lipschitz
--    bound on the largest jump + Mathlib's continuous mapping theorem).
theorem tendsto_maxJump_stepPathLaw {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hfinite : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n => (stepPathLaw (realOffspringStepLaw μ) T
        (fun n : ℕ => (Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ) / Real.sqrt 2) *
          Real.sqrt n) n).map maxJump) atTop
      (𝓝 ((wienerD (NNReal.sqrt 2) T).map maxJump)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_stepPathLaw_wienerD_of_finiteVariance hc hne hfinite hT)
    lipschitzWith_two_maxJump.continuous

theorem map_maxJump_wienerD (c : NNReal) (T : ℝ) :
    ((wienerD c T).map maxJump : Measure ℝ) = Measure.dirac 0 := by
  have h : ∀ᵐ f ∂(wienerD c T : Measure (D T ℝ)), maxJump f = 0 := by
    filter_upwards [ae_mem_range_ofContinuous_wienerD c T] with f hf
    obtain ⟨g, rfl⟩ := hf
    exact maxJump_eq_zero_of_continuous g.continuous
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_congr h, Measure.map_const]
  simp

example {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hfinite : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n => ((stepPathLaw (realOffspringStepLaw μ) T
        (fun n : ℕ => (Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ) / Real.sqrt 2) *
          Real.sqrt n) n).map maxJump : ProbabilityMeasure ℝ)) atTop
      (𝓝 ⟨Measure.dirac 0, inferInstance⟩) := by
  convert tendsto_maxJump_stepPathLaw hc hne hfinite hT using 2
  congr 1
  apply ProbabilityMeasure.toMeasure_injective
  rw [map_maxJump_wienerD]
  rfl
```

It took four attempts to compile. Every failure was about discoverability, none about a missing lemma: the
`BrownianD` namespace, the `OptionalGaps` import, and two proof-term details.

## Appendix D — Remediation status (8 November 2026, after the audit)

The audit body above describes the snapshot `a6879ba`. This table records what was done since, all on
the local branch `campaign/random-trees` (nothing published).

| Finding | Status | Commits |
| --- | --- | --- |
| P1-1 unpublished, no install route | Install route documented and tested from a fresh clone; publication is the owner's decision (open) | `b550f39`, `c75273a` |
| P1-2 stale front-door documentation | Resolved: README, entry docstrings, report header | `b550f39` |
| P1-3 vendored packages in foundational layers | Partly: the basic `DLoc` API is in the vendor-free `Skorokhod/DLocBasic`; the Brownian supplier interface is open | `231ab51` |
| P2-1 C27–C29 need a monotone norming | Resolved: `…_of_attracted` theorems for any admissible norming (audited contract, sealing audit) | `231ab51` |
| P2-2 Mathlib default linters (25 errors) | Resolved: 0 findings over the whole library; three definitions keep a documented `nolint`; non-blocking CI job with the standard linter set | `231ab51`, `945651a` |
| P2-3 46 `set_option` uses | 5 left, each documented | `231ab51` |
| P2-4 stable law coupled to the BGW attraction proof | Open | — |
| P2-5 path-space generality | Partly: `D.postcomp`, real-factor scaling for normed spaces; `DLoc E` and a local J1 topology open | `231ab51` |
| P2-6 GHP quotient asymmetry | Resolved: unrooted `MeasuredGHSpace.scale`; `forgetToGH` moved to `MetricMeasure` | `231ab51` |
| P2-7 examples and discoverability | Mostly: README snippets and new examples compiled, module-system note, largest-jump lemmas moved to `Jump`; the `wienerD` namespace is unchanged | `b550f39`, `231ab51` |
| P2-8 API documentation | Resolved: doc-gen4 project in `docs/build/`, generation tested | `231ab51` and later |
| P2-9 release and maintenance policy | Resolved: README section and `CHANGELOG.md` | `b550f39` |
| P2-10 provenance and evidence | Resolved: `freezing1` provenance, `docs/evidence/` (contracts, freeze-record hashes, linked successor records) | `b550f39`, `7c0f1d6` |
| P3 generic code in `BGW.StableTrees` | Resolved for 25 files (120 names, exact map in `docs/renames/`); `ExcursionCarrier` deferred | `a30839d` |
| P3 tracked internal files, absolute links, vendored headers | Open | — |

Statement changes approved by the maintainer: unused hypotheses removed from seven frozen theorems,
with linked successor freeze records; the domain assumptions of `offspringFieldLaw`, `ghpCosts`,
`rootedGHPCosts` (and the two GHP distances) are kept and documented.
