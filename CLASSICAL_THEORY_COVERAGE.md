# Coverage of the classical-theory specification (C1–C39)

The tables map the [classical theory inputs](CLASSICAL_THEORY_INPUTS.md) to Lean
declarations. The Module column gives the import for each result. The remaining
article-specific obligations are listed below the tables.

Status vocabulary.

- DELIVERED (exact): an export states the subclaim as specified.
- DELIVERED (equivalent/stronger form): an export states an equivalent or stronger form; the Notes say how it differs (for example general metric space `E` instead of $\mathbb R$, filter instead of sequence, a carrier on $[0,\infty)$).
- CORRECTED (letter): the audited statement differs from the specification because the specified statement was false or vacuous; the letter is the entry (a)–(m) in the section "Statement corrections" of [FORMALIZATION_REPORT.md](FORMALIZATION_REPORT.md). Corrections (g)–(m) concern contracts and proof routes (C28.b, C26, C27) and are not subclaim rows.
- BYPASSED: an alternative proof route does not use the specified argument; the Notes quote why the item does not require it. Bypassing does not remove a stated theorem: where a subclaim is itself an independent theorem its row is delivered.
- ARTICLE-SIDE: the subclaim belongs to the article's own layer; BGW supplies the stated ingredients (section "Remaining obligations").

Counts below are rows of the per-item tables (one row per subclaim, including unnumbered and corrected ones); a row is counted by the first word of its status. Mixed rows C30.a3 and C33.5 (delivered, with an article-side half) are counted as delivered and listed under "Remaining obligations".

| Status | Rows |
| --- | ---: |
| DELIVERED (exact) | 158 |
| DELIVERED (equivalent/stronger) | 50 |
| CORRECTED | 7 |
| BYPASSED | 10 |
| ARTICLE-SIDE | 6 |
| IN PROGRESS | 0 |
| OPEN | 0 |
| Total | 231 |

## Summary by item

"Overall" is the status of the item, with article-side obligations identified separately. "Corr." lists the audit corrections (a)–(m) that touch the item.

| Item | Overall | Rows | Corr. | Main modules |
| --- | --- | --- | --- | --- |
| [C1](#c1) Skorokhod space $D([0,T],\mathbb R)$ and the $J_1$ metric | DELIVERED | 7 exact, 3 equiv. |  | `BGW.Skorokhod.Basic`, `BGW.Skorokhod.StepApprox`, `BGW.Skorokhod.TimeChange` |
| [C2](#c2) Separability of $D$ | DELIVERED | 4 equiv. |  | `BGW.Skorokhod.Separable`, `BGW.Skorokhod.Basic` |
| [C3](#c3) Billingsley's metric $d^\circ$, completeness, Polishness | DELIVERED | 4 exact | (c) | `BGW.Skorokhod.CompleteMetricCompleteness`, `BGW.Skorokhod.CompleteMetricTimeChange`, `BGW.Skorokhod.CompleteMetricCore` |
| [C4](#c4) Borel $\sigma$-field of $D$ equals the cylinder $\sigma$-field; measurable evaluations | DELIVERED | 6 exact |  | `BGW.Skorokhod.Measurable`, `BGW.Skorokhod.MeasurableCylinders`, `BGW.Skorokhod.MeasurableExtrema` |
| [C5](#c5) $C\subset D$; $J_1$ convergence to a continuous limit is uniform; $D\times C$ versus $D(\mathbb R^2)$ | DELIVERED | 4 exact, 1 equiv. |  | `BGW.Skorokhod.Continuous`, `BGW.Skorokhod.ContinuousEmbedding`, `BGW.Skorokhod.ProductPaths` |
| [C6](#c6) Continuity facts (evaluation, restriction, stopping, sup/inf, time-space scaling) | DELIVERED | 8 exact, 1 equiv. |  | `BGW.Skorokhod.Restrict`, `BGW.Skorokhod.RestrictContinuity`, `BGW.Skorokhod.Scaling` |
| [C7](#c7) Stopped-path approximation at a continuity endpoint | DELIVERED | 2 exact, 1 equiv. |  | `BGW.Skorokhod.Restrict`, `BGW.Skorokhod.OptionalGaps` |
| [C8](#c8) Relative compactness and tightness in $D$ ($w'$, Billingsley 13.2, Aldous) | DELIVERED | 1 exact, 2 equiv., 4 corrected | (b), (f) | `BGW.Skorokhod.Tightness`, `BGW.Skorokhod.PolishTightness`, `BGW.Skorokhod.AldousCriterionBasic` |
| [C9](#c9) Continuous mapping theorem for a.e.-continuous maps | DELIVERED | 1 exact, 2 equiv. |  | `BGW.Probability.WeakConvergence` |
| [C10](#c10) Converging-together lemma; metric Slutsky on varying spaces | DELIVERED | 1 exact, 1 equiv. |  | `BGW.MetricMeasure.WeakPerturbation`, `BGW.Probability.WeakConvergence` |
| [C11](#c11) Billingsley's approximation theorem 3.2; prefix and terminal control | DELIVERED | 1 exact, 3 equiv. |  | `BGW.Skorokhod.Prefix`, `BGW.Probability.WeakConvergence`, `BGW.Skorokhod.ProductPaths` |
| [C12](#c12) Determining classes | DELIVERED | 1 exact, 1 equiv., 1 corrected | (e) | `BGW.Skorokhod.MeasurableLaws`, `BGW.Skorokhod.Prefix`, `BGW.Skorokhod.MeasurableJumps` |
| [C13](#c13) Prokhorov | DELIVERED | 1 exact |  | `BGW.Skorokhod.PolishTightness` |
| [C14](#c14) Skorokhod representation | DELIVERED | 1 corrected | (a) | `BGW.Probability.SkorokhodRepresentation`, `BGW.Probability.SeparableRepresentation`, `BGW.Skorokhod.PolishTightness` |
| [C15](#c15) Stable law $\mu_\theta$, density $p_1$, $p_t$, kernels $q_s$, $\Gamma_a$ | DELIVERED except ARTICLE-SIDE: C15.3c | 12 exact, 3 equiv., 1 article-side |  | `BGW.StableTrees.StableLaw`, `BGW.StableTrees.Scalar.Density`, `BGW.StableTrees.KendallAdapter` |
| [C16](#c16) The $\theta$-stable spectrally positive Lévy process as a law on $D([0,T])$ | DELIVERED | 9 exact, 2 equiv. |  | `BGW.StableTrees.StableLevyLaw`, `BGW.StableTrees.StableProcessLaw`, `BGW.StableTrees.StableProcessMarkov` |
| [C17](#c17) Functional limit theorem for walks in the stable domain | DELIVERED except ARTICLE-SIDE: C17.iii | 4 exact, 1 equiv., 1 article-side |  | `BGW.StableTrees.StableProcessLaw`, `BGW.StableTrees.RealAttraction`, `BGW.StableTrees.StableProcessBrownian` |
| [C18](#c18) Fluctuation basics (regularity of 0, first passage, Kendall, unique minimum) | DELIVERED | 9 exact, 1 equiv. |  | `BGW.StableTrees.StableFirstPassage`, `BGW.StableTrees.StablePassageSubordinator`, `BGW.StableTrees.StableFirstPassagePath` |
| [C19](#c19) $\theta=2$ instance, $X=\sqrt2 B$ | DELIVERED | 5 exact |  | `BGW.ContinuumTrees.BrownianD`, `BGW.StableTrees.StableProcessBrownian`, `BGW.ContinuumTrees.BrownianBridge` |
| [C20](#c20) Reflected process $X-I$, local time $-I$ | DELIVERED | 2 exact, 2 equiv. |  | `BGW.StableTrees.ExcursionGapsStrongMarkov`, `BGW.StableTrees.ReflectedRestart`, `BGW.StableTrees.StableRegularity` |
| [C21](#c21) Itô excursion theorem for $X-I$, excursion measure $N$ | DELIVERED | 4 exact, 1 equiv. |  | `BGW.StableTrees.ExcursionMeasureBasic`, `BGW.StableTrees.MarkedExcursionsBasic`, `BGW.StableTrees.ExcursionMeasureCounts` |
| [C22](#c22) Itô description of $N$, normalized excursion $X^{\mathrm{exc}}$, $N(\cdot\mid\zeta>1)$ | DELIVERED | 10 exact |  | `BGW.StableTrees.UnitExcursionLawBasic`, `BGW.StableTrees.ExcursionGapsIto`, `BGW.ContinuumTrees.ExcursionCarrier` |
| [C23](#c23) Markov property under $N$ | DELIVERED | 2 exact |  | `BGW.StableTrees.ExcursionMarkovConsequences`, `BGW.StableTrees.ExcursionMarkovProof`, `BGW.Skorokhod.DLoc` |
| [C24](#c24) Proposition 5.3 ($\Gamma_a$ identity) | DELIVERED | 5 exact |  | `BGW.StableTrees.GammaIdentity`, `BGW.StableTrees.JointExcursion`, `BGW.StableTrees.KendallAdapter` |
| [C25](#c25) Chaumont's path construction of $X^{\mathrm{exc}}$ (optional) | DELIVERED | 1 exact, 1 equiv. |  | `BGW.StableTrees.StraddlingExcursionBasic`, `BGW.StableTrees.ExcursionGaps`, `BGW.StableTrees.StraddlingExcursionLaw` |
| [C26](#c26) Height process $H$, continuity, $H^{\mathrm{exc}}$ | DELIVERED | 10 exact | (i), (j), (k) | `BGW.StableTrees.JointExcursion`, `BGW.StableTrees.HeightProcessBasic`, `BGW.StableTrees.HeightContinuityBasic` |
| [C27](#c27) Duquesne--Le Gall forest theorem (unconditioned joint $(W,H,C)$) | DELIVERED | 3 exact, 2 equiv., 2 bypassed | (h), (l), (m) | `BGW.StableTrees.ForestTriple`, `BGW.StableTrees.ForestTripleVector`, `BGW.Skorokhod.ProductPaths` |
| [C28](#c28) Theorem 5.1 (trees with $\zeta\ge n$) | DELIVERED | 3 exact, 2 equiv., 2 bypassed | (g) | `BGW.StableTrees.TailPair`, `BGW.StableTrees.TailPairBasic`, `BGW.StableTrees.DiscreteForestTreeLaws` |
| [C29](#c29) Theorem 4.1 (Duquesne, trees with $\zeta=n$) | DELIVERED | 1 exact, 4 equiv., 1 bypassed |  | `BGW.StableTrees.ExactContourJoint`, `BGW.StableTrees.ExactContourTerminal`, `BGW.StableTrees.ExactContourGlobal` |
| [C30](#c30) $\theta=2$: $H^{\mathrm{exc}}=X^{\mathrm{exc}}=\sqrt2 e$; Aldous's normalization | DELIVERED; leaf-conditioned form of C30.a3 ARTICLE-SIDE | 5 exact, 2 equiv., 1 bypassed |  | `BGW.StableTrees.BrownianExcursion`, `BGW.StableTrees.FiniteVarianceContour`, `BGW.StableTrees.BrownianIdentification` |
| [C31](#c31) Stable bridge $X^{\mathrm{br}}$ on $D([0,1])$ | DELIVERED | 7 exact, 4 equiv. |  | `BGW.StableTrees.StableBridgeClosed`, `BGW.StableTrees.BridgeProjective`, `BGW.StableTrees.BridgePrefix` |
| [C32](#c32) Unique minimum of $X^{\mathrm{br}}$, attained continuously | DELIVERED | 4 exact, 1 bypassed |  | `BGW.StableTrees.StableBridgeMinimum`, `BGW.Skorokhod.Vervaat`, `BGW.StableTrees.StableBridgeUniformMinimum` |
| [C33](#c33) Càdlàg Vervaat map $V$ and its discrete correspondence | DELIVERED; C33.5 glue to `BGWLeaves.vervaat` ARTICLE-SIDE | 5 exact, 2 equiv., 1 corrected | (d) | `BGW.Skorokhod.VervaatRotate`, `BGW.Skorokhod.VervaatContinuity`, `BGW.Skorokhod.Vervaat` |
| [C34](#c34) Continuity of $V$ at bridge-like paths | DELIVERED | 3 exact, 1 equiv., 1 bypassed |  | `BGW.Skorokhod.VervaatContinuity`, `BGW.StableTrees.StableBridgeMinimum`, `BGW.Skorokhod.VervaatMinimumContinuity` |
| [C35](#c35) $V(X^{\mathrm{br}})=X^{\mathrm{exc}}$ in law (Chaumont) | DELIVERED | 1 exact, 1 bypassed |  | `BGW.StableTrees.VervaatIto` |
| [C36](#c36) Largest-jump functional $\bar\Delta$ | DELIVERED except ARTICLE-SIDE: C36.N14 | 5 exact, 1 article-side |  | `BGW.Skorokhod.Jump`, `BGW.Skorokhod.OptionalGaps`, `BGW.StableTrees.ExcursionJump` |
| [C37](#c37) Real tree coded by $g\in C$; GH and GHP Lipschitz bounds | DELIVERED | 4 exact, 1 equiv. |  | `BGW.ContinuumTrees.CodingGH`, `BGW.ContinuumTrees.CodingRealTree`, `BGW.ContinuumTrees.CodingMeasure` |
| [C38](#c38) Contour to rooted measured GHP transfer | DELIVERED | 5 exact |  | `BGW.ContinuumTrees.ContourAdapters`, `BGW.ContinuumTrees.ContourLawConvergence`, `BGW.ContinuumTrees.ContourPaperTransfer` |
| [C39](#c39) Uniform leaf measure versus uniform vertex measure | DELIVERED except ARTICLE-SIDE: C39.c, C39.c', C39.app | 2 exact, 2 equiv., 1 bypassed, 3 article-side |  | `BGW.ContinuumTrees.LeafMeasure`, `BGW.ContinuumTrees.ContourEmbedding`, `BGW.ContinuumTrees.UniformVertexSampling` |

## Per-item coverage

Columns: subclaim, short claim, status, fully qualified Lean declarations, module(s) to import, notes. The notation `E` is a separable metric space (the real case and the products $\mathbb R\times\mathbb R$, `Fin d → ℝ` are instances); `hθ` abbreviates `1 < θ ∧ θ ≤ 2`.

### C1

Skorokhod space $D([0,T],\mathbb R)$ and the $J_1$ metric.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C1.def-D | `D_T(E)`: càdlàg paths on `[0,T]` (right-continuous, left limits, `f(0-):=f(0)`) | DELIVERED (exact) | `BGW.Skorokhod.D` (structure over `Set.Icc 0 T`, field `isCadlag' : IsCadlag toFun`), `BGW.Skorokhod.isCadlag` | `BGW.Skorokhod.Basic` | Exactly the spec's Lean sketch; `IsCadlag` on `Icc` gives the `f(0-)=f(0)` convention. |
| C1.def-Lambda | `Λ_T` = increasing homeomorphisms = order isos of `[0,T]` | DELIVERED (exact) | `BGW.Skorokhod.TimeChange` (`abbrev := Icc 0 T ≃o Icc 0 T`), `BGW.Skorokhod.TimeChange.apply_zero`, `BGW.Skorokhod.TimeChange.apply_top`, `BGW.Skorokhod.TimeChange.abs_sub_le` | `BGW.Skorokhod.TimeChange` | Fixing of 0 and T proved (`BGW.Skorokhod.TimeChange.apply_zero`, `BGW.Skorokhod.TimeChange.apply_top`, hypothesis `0 ≤ T`). |
| C1.def-d | `d_T(f,g)=inf_λ max(sup\|λt−t\|, sup ρ(f t, g(λ t)))` | DELIVERED (exact) | `BGW.Skorokhod.j1Dist`, `BGW.Skorokhod.dist_eq_j1Dist` | `BGW.Skorokhod.Basic` | `⨅ σ, max (⨆ t, \|σ t − t\|) (⨆ t, dist (f t) (g (σ t)))`. |
| C1.1a | every `f∈D` has bounded (relatively compact for `ℝ^d`) range | DELIVERED (equivalent/stronger form) | `BGW.Skorokhod.isBounded_range` | `BGW.Skorokhod.Basic` | States `Bornology.IsBounded (range f)` for any pseudo-metric `E`; relative compactness for `ℝ^d` follows from `ProperSpace` (Mathlib). |
| C1.1b | at most countably many jumps | DELIVERED (exact) | `BGW.Skorokhod.countable_setOf_jump_ne` | `BGW.Skorokhod.StepApprox` | `{t \| leftLim f t ≠ f t}.Countable`. |
| C1.1c | for `ε>0` only finitely many jumps of size `>ε` | DELIVERED (exact) | `BGW.Skorokhod.finite_setOf_jump_gt` | `BGW.Skorokhod.StepApprox` | `{t \| ε < dist (leftLim f t) (f t)}.Finite`. |
| C1.2 | `d_T` is a metric (separation uses right-continuity) | DELIVERED (exact) | `BGW.Skorokhod.instMetricSpace` (`noncomputable instance`, `dist := j1Dist`) | `BGW.Skorokhod.Basic` | Includes `eq_of_dist_eq_zero`; no `CompleteSpace` instance rests on `d` (spec pitfall respected: completeness is on the synonym `DComplete`). The J1 topology is the metric topology of this instance by construction. |
| C1.3 | `d_T(f,g) ≤ sup_t ρ(f t, g t)` | DELIVERED (exact) | `BGW.Skorokhod.dist_le_iSup_dist` | `BGW.Skorokhod.Basic` |  |
| C1.4 | `d(f_n,f)→0` iff time changes `λ_n` with `‖λ_n−id‖→0` and `sup ρ(f_n(λ_n t), f t)→0` | DELIVERED (equivalent/stronger form) | `BGW.Skorokhod.tendsto_iff_exists_timeChange` | `BGW.Skorokhod.Basic` | Stated for an arbitrary filter `l` on an index type (spec: sequences). Time changes compose as `u i (σ i t)` vs `f t`, matching the spec. |
| C1.(d) | minimal: `E=ℝ`, `T=1` and prefixes `T=a`; `d` only | DELIVERED (equivalent/stronger form) | same as C1 rows | — | Delivered for general metric `E` and every real `T` (empty `Icc` when `T<0`, harmless). `d°` is separate (C3). |

### C2

Separability of $D$.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C2.1 | `(D_T, d_T)` is separable (for separable `E`) | DELIVERED (equivalent/stronger form) | `BGW.Skorokhod.instSeparableSpace` | `BGW.Skorokhod.Separable` | Instance for separable metric `E` (spec: `E=ℝ`); proved via `BGW.Skorokhod.exists_uniform_step_approximation` (step approximations with values `f(u n)`, not rational data; the density claim is delivered in this equivalent form). |
| C2.2 | `SecondCountableTopology (D T ℝ)` | DELIVERED (equivalent/stronger form) | consequence of `BGW.Skorokhod.instSeparableSpace` + `BGW.Skorokhod.instMetricSpace` via Mathlib instances | `BGW.Skorokhod.Separable`, `BGW.Skorokhod.Basic` | No BGW-named theorem; instance inference checked by a Lean probe (`inferInstance` for `SecondCountableTopology (D T ℝ)`, 8 Nov 2026). |
| C2.3 | `ProbabilityMeasure (D T ℝ)` metrizable | DELIVERED (equivalent/stronger form) | same as C2.2 (Mathlib instance for separable pseudo-metrizable spaces) | — | No BGW-named theorem; `MetrizableSpace (ProbabilityMeasure (D T ℝ))` by `inferInstance` (Lean probe, 8 Nov 2026). |
| C2.4 | `Borel(D×S) = Borel(D)⊗Borel(S)` for second-countable `S` | DELIVERED (equivalent/stronger form) | consequence of C2.2 via Mathlib `Prod.borelSpace` | — | No BGW-named theorem; `BorelSpace (D T ℝ × D T ℝ)` by `inferInstance` (Lean probe, 8 Nov 2026). |

### C3

Billingsley's metric $d^\circ$, completeness, Polishness.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C3.1 | `‖λ‖°=sup_{s<t}\|log((λt−λs)/(t−s))\|`, `d°(f,g)=inf_λ max(‖λ‖°, sup ρ)` | DELIVERED (exact) | `BGW.Skorokhod.TimeChange.logSlope` (in `ℝ≥0∞`), `BGW.Skorokhod.j1CompleteDist`, `BGW.Skorokhod.DComplete` (type synonym with `BGW.Skorokhod.instMetricSpaceDComplete`) | `BGW.Skorokhod.CompleteMetricTimeChange`, `BGW.Skorokhod.CompleteMetricCore`, `BGW.Skorokhod.CompleteMetricSpace` | Uses `edist` and `toReal` to absorb infinite slope; equal to the spec. |
| C3.2 | `d` and `d°` give the same topology | DELIVERED (exact) | `S.toDComplete : D T E ≃ₜ DComplete T E`, `BGW.Skorokhod.dist_toDComplete`, `BGW.Skorokhod.dist_le_exp_j1CompleteDist_sub_one` | `BGW.Skorokhod.CompleteMetricTopology`, `BGW.Skorokhod.CompleteMetricComparison` | CORRECTED side-statement: Billingsley (12.17) `d ≤ e^{d°}−1` holds on `[0,1]` only; delivered `d ≤ max 1 T (e^{d°}−1)` (report, "Statement corrections" (c)). The spec itself only asked for equivalence of topologies, which is the homeomorphism. |
| C3.3 | `D` complete for `d°` | DELIVERED (exact) | `BGW.Skorokhod.instCompleteSpaceDComplete` (complete `E`) | `BGW.Skorokhod.CompleteMetricCompleteness` |  |
| C3.4 | `D` is Polish | DELIVERED (exact) | `BGW.Skorokhod.instIsCompletelyMetrizableSpace`, `BGW.Skorokhod.polishSpace_D`, `BGW.Skorokhod.standardBorelSpace_D` | `BGW.Skorokhod.CompleteMetricCompleteness`, `BGW.Skorokhod.PolishTightness` | `BGW.Skorokhod.polishSpace_D` is `infer_instance` from complete metrizability + separability. Optional item delivered; matches the spec pitfall (`MetricSpace` instance stays `d`). |

### C4

Borel $\sigma$-field of $D$ equals the cylinder $\sigma$-field; measurable evaluations.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C4.1 | each `π_t` is Borel | DELIVERED (exact) | `BGW.Skorokhod.measurable_eval` (also `BGW.Skorokhod.measurable_eval_top`, `BGW.Skorokhod.measurable_eval_zero`) | `BGW.Skorokhod.Measurable` | The name `measurable_eval` also exists in `DLoc.lean` and `StableTrees/BridgeProjectiveOpen.lean` (different spaces); the cited one is `BGW.Skorokhod.measurable_eval` in `Measurable.lean`. |
| C4.2 | `Borel(D_T)=σ(π_t : t∈S)` for `S` dense with `T∈S` | DELIVERED (exact) | `BGW.Skorokhod.measurableSpace_eq_iSup_comap_eval` (with `BGW.Skorokhod.eq_of_eval_eq_on_dense`) | `BGW.Skorokhod.MeasurableCylinders` | Needs `E` separable (stated for separable metric `E`); matches spec `E=ℝ`. Uses `hT0 : 0 ≤ T`, `⟨T,_,_⟩ ∈ S`. |
| C4.3 | `(f,t) ↦ f(t)` jointly measurable on `D_T × [0,T]` | DELIVERED (exact) | `BGW.Skorokhod.measurable_eval₂` | `BGW.Skorokhod.Measurable` | Proved through dyadic right-time approximations (`BGW.Skorokhod.measurable_dyadicRightTime`, `BGW.Skorokhod.tendsto_dyadicRightTime` in `BGW.Skorokhod.StepApprox`). |
| C4.4a | `f ↦ f(t−)` Borel | DELIVERED (exact) | `BGW.Skorokhod.measurable_leftLim_eval` | `BGW.Skorokhod.Measurable` |  |
| C4.4b | `f ↦ sup_{s∈J} f(s)` and `inf_{s∈J}` Borel, `J` an interval | DELIVERED (exact) | `BGW.Skorokhod.measurable_iSup_eval`, `BGW.Skorokhod.measurable_iInf_eval` (hypothesis `J.OrdConnected`) | `BGW.Skorokhod.MeasurableExtrema` | Real-valued paths; `⨆ s : J`. |
| C4.(d) | library needed, consumer layer avoidable | DELIVERED (exact) | all of the above | — | Delivered although the spec calls the consumer layer avoidable; companion a.e.-measurability by `BGW.Probability.aemeasurable_of_ae_continuousAt` is C9.1. |

### C5

$C\subset D$; $J_1$ convergence to a continuous limit is uniform; $D\times C$ versus $D(\mathbb R^2)$.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C5.1 | `d_T(f,g) ≤ ‖f−g‖_∞` for continuous `f,g` | DELIVERED (exact) | `BGW.Skorokhod.ofContinuous`, `BGW.Skorokhod.lipschitzWith_one_ofContinuous` | `BGW.Skorokhod.Continuous` | 1-Lipschitz for the sup metric on `C(Icc 0 T, E)`. |
| C5.2 | `d_T(f_n,f)→0`, `f` continuous ⇒ `‖f_n−f‖_∞→0` | DELIVERED (exact) | `BGW.Skorokhod.tendsto_iSup_dist_of_tendsto_ofContinuous` | `BGW.Skorokhod.Continuous` | Filter version; hypothesis `Tendsto u l (𝓝 (ofContinuous f))`. |
| C5.3 | `C ⊂ D` homeomorphism onto a closed subset; J1 = uniform on `C` | DELIVERED (exact) | `BGW.Skorokhod.isClosedEmbedding_ofContinuous` (with `BGW.Skorokhod.lipschitzWith_one_ofContinuous`) | `BGW.Skorokhod.ContinuousEmbedding`, `BGW.Skorokhod.Continuous` | `Topology.IsClosedEmbedding (ofContinuous)`; the sup topology on `C(Icc,E)` coincides with compact-open, so J1 = uniform on `C` follows. |
| C5.4 | `f_n→f` in `D(ℝ)`, `g_n→g` uniformly, `g∈C` ⇒ `(f_n,g_n)→(f,g)` in `D(ℝ²)` | DELIVERED (equivalent/stronger form) | `BGW.Skorokhod.prodCont`, `BGW.Skorokhod.continuous_prodCont`, `BGW.Skorokhod.tendsto_prodCont`; general `BGW.Skorokhod.prodWithCont`, `BGW.Skorokhod.continuous_prodWithCont` | `BGW.Skorokhod.ProductPaths` | Joint continuity on `D×C` (stronger than the sequence statement); general `E×F` covers `ℝ^{1+k}`. Optional per spec (d); first delivered at CT10 C5.4 and CT8 K13b. Law-level consequence ("convergence in law in `D×C^k` ⇒ in `D(ℝ^{1+k})`") is the continuous mapping theorem applied to `BGW.Skorokhod.continuous_prodWithCont` (consumer: `StableTrees/ForestTripleVector`). |
| C5.4-converse | convergence in law in `D(ℝ^{1+k})` with continuous coordinates ⇒ in `D×C^k` ("holds always (coordinates)") | DELIVERED (exact) | `BGW.Skorokhod.tendsto_map_splitProdWithCont`, `BGW.Skorokhod.splitProdWithCont`, `BGW.Skorokhod.prodWithCont_splitProdWithCont` | `BGW.Skorokhod.OptionalGaps` | Law-level converse: convergence in law in `D_T(E×F)` to a limit whose second coordinate is a.s. continuous, along laws whose second coordinate is a.s. continuous, implies convergence in law of the images under `BGW.Skorokhod.splitProdWithCont` in `D_T(E)×C([0,T],F)`. `BGW.Skorokhod.prodWithCont_splitProdWithCont` shows that splitting inverts `BGW.Skorokhod.prodWithCont` on paths with continuous second coordinate. Commit `e7d9564`. |

### C6

Continuity facts (evaluation, restriction, stopping, sup/inf, time-space scaling).

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C6.1a | `π_0`, `π_T` 1-Lipschitz | DELIVERED (exact) | `BGW.Skorokhod.lipschitzWith_one_eval_zero`, `BGW.Skorokhod.lipschitzWith_one_eval_right` (hypothesis `0 ≤ T`) | `BGW.Skorokhod.Restrict` |  |
| C6.1b | `π_t` continuous at `f` if `f` is continuous at `t` | DELIVERED (exact) | `BGW.Skorokhod.continuousAt_eval` | `BGW.Skorokhod.Restrict` | Any `t` in `Icc 0 T`. |
| C6.2a | restriction `r_a : D_T→D_a` continuous at `f` continuous at `a` | DELIVERED (exact) | `BGW.Skorokhod.restrict`, `BGW.Skorokhod.continuousAt_restrict` | `BGW.Skorokhod.Restrict`, `BGW.Skorokhod.RestrictContinuity` | Also `BGW.Skorokhod.measurable_restrict_of_nonneg` / `BGW.Skorokhod.measurable_restrict` (`BGW.Skorokhod.Prefix`, `BGW.Skorokhod.MeasurableMaps`), used by C11/C12. |
| C6.2b | extension `ι_a(g)(t)=g(t∧a)` is 1-Lipschitz | DELIVERED (exact) | `BGW.Skorokhod.extendConst`, `BGW.Skorokhod.lipschitzWith_one_extendConst` | `BGW.Skorokhod.Restrict` |  |
| C6.2c | stopping `φ_a=ι_a∘r_a` continuous at `f` continuous at `a` | DELIVERED (exact) | `BGW.Skorokhod.stop`, `BGW.Skorokhod.stop_eq_extendConst_restrict`, `BGW.Skorokhod.continuousAt_stop` | `BGW.Skorokhod.Restrict`, `BGW.Skorokhod.RestrictContinuity` |  |
| C6.3a | `inf`, `sup` over `[0,T]` are 1-Lipschitz | DELIVERED (exact) | `BGW.Skorokhod.lipschitzWith_one_iInf`, `BGW.Skorokhod.lipschitzWith_one_iSup` | `BGW.Skorokhod.Restrict` | `D T ℝ`. |
| C6.3b | `f ↦ sup_{s∈[c,T]}\|f(s)−f(c)\|` continuous at `f` continuous at `c` | DELIVERED (exact) | `BGW.Skorokhod.continuousAt_oscillationFrom` | `BGW.Skorokhod.RestrictContinuity` | `⨆ s : {s // c ≤ s}, \|g s − g c\|`; any `c`. |
| C6.4 | `Ψ(g,k,s)=(t↦k⊙g(min(st,T)))\|[0,a]` continuous at `(f,1,1)`, `f` continuous at `a`; `d≥1`, distinct factors per coordinate | DELIVERED (equivalent/stronger form) | `BGW.Skorokhod.timeSpaceScale`, `BGW.Skorokhod.continuousAt_timeSpaceScale` | `BGW.Skorokhod.Scaling` | `E` is any `NormedRing`, spatial factor `k : E` (not only positive), time factor `s ∈ Ioi 0`; `⊙` is the ring product, so `E = Fin d → ℝ` gives coordinatewise factors (docstring says so). Hypotheses `0<a<T`, continuity of `f` at `a`. Measurability for fixed parameters: `BGW.Skorokhod.measurable_timeSpaceScale_fixed`. |
| C6.4-C | in the product form `D×C`, the C-coordinate map `(h,k,s) ↦ k·h(min(s·,T))\|[0,a]` is continuous everywhere | DELIVERED (exact) | `BGW.Skorokhod.timeSpaceScaleC`, `BGW.Skorokhod.continuous_timeSpaceScaleC` | `BGW.Skorokhod.ScalingContinuous` |  |

### C7

Stopped-path approximation at a continuity endpoint.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C7.1 | `d_T(φ_{T−δ}f, f) ≤ sup_{s∈[T−δ,T]}\|f s − f(T−δ)\|` | DELIVERED (exact) | `BGW.Skorokhod.dist_stop_le` | `BGW.Skorokhod.Restrict` | `dist (stop a f) f ≤ ⨆ s : {s // a ≤ s}, dist (f s) (f a)`, for any `0 ≤ a ≤ T`. |
| C7.2 | if `f` continuous at `T`, the RHS `→0` as `δ↓0` (consequence `φ_{T−δ}f → f`) | DELIVERED (equivalent/stronger form) | `BGW.Skorokhod.tendsto_stop_nhdsLT` | `BGW.Skorokhod.Restrict` | Exports the consequence `stop a f → f` as `a↑T`; the RHS-vanishing itself is not a named lemma (it is the oscillation hypothesis of the consumers, e.g. in `BGW.Skorokhod.tendsto_of_tendsto_restrict_of_oscillation`). |
| C7.C | the same bound in `C_T` with the uniform norm | DELIVERED (exact) | `BGW.Skorokhod.dist_stopContinuous_le`, `BGW.Skorokhod.stopContinuous` | `BGW.Skorokhod.OptionalGaps` | `dist (stopContinuous a f) f ≤ ⨆ s ≥ a, dist (f s) (f a)` for `f` in `C(Icc 0 T, E)` with the uniform metric, `0 ≤ a ≤ T`. Commit `e7d9564`. |

### C8

Relative compactness and tightness in $D$ ($w'$, Billingsley 13.2, Aldous).

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C8.mod | modulus `w'_f(δ)` and `w'_f(δ)→0` for every `f∈D` | CORRECTED (b) (exact) | `BGW.Skorokhod.cadlagModulus`, `BGW.Skorokhod.tendsto_cadlagModulus` | `BGW.Skorokhod.Tightness` | CORRECTED: convention `w'=0` for `δ≥T` makes the criteria vacuous; the criteria carry `δ<T` (report correction (b)). Also `BGW.Skorokhod.cadlagModulus_mono`, `BGW.Skorokhod.exists_partition_of_cadlagModulus_lt`. |
| C8.cpt-suff | `sup‖f‖<∞` and `w'→0` uniformly ⇒ relatively compact (Arzelà-Ascoli analogue) | CORRECTED (b) (exact) | `BGW.Skorokhod.isCompact_closure_of_cadlagModulus` | `BGW.Skorokhod.Tightness` | `ProperSpace E`; correction (b) (`δ<T`). |
| C8.cpt-nec | relatively compact ⇒ bounded and uniform modulus (the iff) | DELIVERED (equivalent/stronger form) | `BGW.Skorokhod.bounded_and_modulus_of_isCompact_closure`, `BGW.Skorokhod.isCompact_closure_iff_bounded_and_modulus`, `BGW.Skorokhod.exists_uniform_cadlagModulus_of_isCompact`, `BGW.Skorokhod.exists_isBounded_values_of_isCompact` | `BGW.Skorokhod.PolishTightness`, `BGW.Skorokhod.Tightness` | Spec (d) says only the sufficiency direction is needed; the necessity (which needs `d°`, C3) is delivered. Requires `0<T`. |
| C8.tight-suff | (i) bounded values and (ii) vanishing modulus in probability ⇒ tight | CORRECTED (b) (exact) | `BGW.Skorokhod.isTightMeasureSet_of_cadlagModulus`, `BGW.Skorokhod.isTightMeasureSet_of_cadlagModulus_eventually` | `BGW.Skorokhod.Tightness` | The "eventual" form (tail of the sequence) takes tightness of each `P n` as an input (automatic on Polish `D`, by C3/C13). Correction (b). |
| C8.tight-nec | tight ⇒ (i) and (ii) with `limsup` (Billingsley Thm 13.2 iff) | DELIVERED (equivalent/stronger form) | `BGW.Skorokhod.isTightMeasureSet_range_iff_limsup`, `BGW.Skorokhod.isTightMeasureSet_iff_isCompact_closure_D` | `BGW.Skorokhod.PolishTightness` | Spec says necessity needs C3 and is not required; delivered. `BGW.Skorokhod.isTightMeasureSet_range_iff_limsup` is an iff for sequences of probability measures, `ProperSpace E`, `0<T`, limsup form with `δ<T`. |
| C8.Aldous | Aldous's criterion (sufficient): (i) tight sup plus `Y(τ+h)−Y(τ)→0` in probability at bounded stopping times ⇒ tight | CORRECTED (f) (exact) | `BGW.Skorokhod.IsStopTime`, `BGW.Skorokhod.isTightMeasureSet_of_aldous`; variant `BGW.Skorokhod.isTightMeasureSet_of_aldous_fixedTimes` | `BGW.Skorokhod.AldousCriterionBasic`, `BGW.Skorokhod.AldousCriterion` | Varying probability spaces `Ω n` with filtrations indexed by `Icc 0 T`; stopping times valued in `[0,T]`, `h n ≥ 0`, `h n→0`, shifts clipped at `T` by `projIcc`. CORRECTED: an `_initial` variant (tightness at time 0 only) was false (counterexample `n·1_{U≤t}`), replaced by the fixed-time variant (report correction (f)). `E=ℝ` only (spec: real-valued processes). |
| C8.(d)/(e) | Mathlib `isCompact_closure_of_isTightMeasureSet` | DELIVERED (exact) | Mathlib `MeasureTheory.isCompact_closure_of_isTightMeasureSet` (checked present in the pinned Mathlib) | `Mathlib.MeasureTheory.Measure.Prokhorov` | Used by the tight ⇒ compact steps; see C13. |

### C9

Continuous mapping theorem for a.e.-continuous maps.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C9.main | `P_n→P`, `h` a.e.-continuous under `P` and a.e.-measurable ⇒ `P_n.map h → P.map h` | DELIVERED (equivalent/stronger form) | `BGW.Probability.tendsto_map_of_ae_continuousAt` | `BGW.Probability.WeakConvergence` | Index type and filter arbitrary (countably generated); only `AEMeasurable h (P i)` is assumed, the one for the limit being derived (C9.1) so the statement has no separate `hQ`. `S,S'` pseudo-metric with Borel structure. |
| C9.1 | `∀ᵐ x ∂P, ContinuousAt h x ⇒ AEMeasurable h P` (continuity set `G_δ`) | DELIVERED (exact) | `BGW.Probability.aemeasurable_of_ae_continuousAt` | `BGW.Probability.WeakConvergence` | Target a pseudo-metric Borel space (no separability assumed). |
| C9.2 | at most countably many atoms; all but countably many cut-offs `{1/α<y<α}`, `{\|y\|<α}` have `P`-null boundary (N11) | DELIVERED (equivalent/stronger form) | `BGW.Probability.countable_setOf_measure_frontier_ne_zero` | `BGW.Probability.WeakConvergence` | General form: for a family of sets with pairwise disjoint frontiers, only countably many frontiers have positive measure (finite measure). Both cut-off families satisfy the disjointness; the atoms statement on `ℝ` is the Mathlib countability of atoms. No dedicated cut-off wrapper lemma. |

### C10

Converging-together lemma; metric Slutsky on varying spaces.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C10.1 | converging together: `law(G_n)→ν`, `P_n(d(F_n,G_n)>ε)→0` ⇒ `law(F_n)→ν` | DELIVERED (exact) | `BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability` | `BGW.MetricMeasure.WeakPerturbation` | Pre-existing; statement read: pseudo-metric Borel second countable `E`, varying `Ω n`, `real`-measure error tends to 0. |
| C10.2 | `law(X_n)→P`, `P_n(d(Y_n,c)>ε)→0` ⇒ `law(X_n,Y_n)→P⊗δ_c` (separable `S,S'`) | DELIVERED (equivalent/stronger form) | `BGW.Probability.tendsto_map_prodMk_of_tendsto_of_error` | `BGW.Probability.WeakConvergence` | The limit is written `P.map (x ↦ (x,c))`, which is `P⊗δ_c`. Second countable `S,S'`, varying `Ω n`. |

### C11

Billingsley's approximation theorem 3.2; prefix and terminal control.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C11.1 | Billingsley Thm 3.2 (approximation theorem) | DELIVERED (exact) | `BGW.Probability.tendsto_of_tendsto_approx` | `BGW.Probability.WeakConvergence` | Varying `Ω n`; `lim_u limsup_n P(ε ≤ d(X_{u,n},Y_n)) = 0` for every `ε`; second countable `S`. |
| C11.2-D | prefix convergence + a.s. continuity at `T` + terminal oscillation ⇒ `Y^n ⇒ Y` in `D_T` | DELIVERED (equivalent/stronger form) | `BGW.Skorokhod.tendsto_of_tendsto_restrict_of_oscillation` | `BGW.Skorokhod.Prefix` | The set `A` with `sup A=T` is replaced by a sequence `a k ↑ T` (`a k<T`); `limsup` then `k→∞` of the oscillation after `a k`. Equivalent for the use (a countable cofinal subset of `A`). Supporting: `BGW.Skorokhod.measurable_restrict_of_nonneg`, `BGW.Skorokhod.measurable_stop_of_nonneg`, `BGW.Skorokhod.tendsto_map_stop`, `BGW.Skorokhod.map_extendConst_restrict`. |
| C11.2-DC | the same in `D_T × C_T^k` (i.e. `D(E×F)`) | DELIVERED (equivalent/stronger form) | `BGW.Skorokhod.tendsto_of_tendsto_restrict_of_oscillation` with `E := ℝ × F` via `BGW.Skorokhod.prodWithCont` | `BGW.Skorokhod.Prefix`, `BGW.Skorokhod.ProductPaths` | Delivered for `D T E`, `E` any separable metric space (so `ℝ^{1+k}`); the product-of-spaces form is by `BGW.Skorokhod.prodWithCont` and the CMT. Consumers: K13b, K16. |
| C11.2-C | the same in `C_T` | DELIVERED (equivalent/stronger form) | `BGW.Skorokhod.tendsto_continuous_of_tendsto_restrict_of_oscillation`, `BGW.Skorokhod.restrictContinuous` | `BGW.Skorokhod.OptionalGaps` | Same hypotheses as C11.2-D (sequence `a k ↑ T`, `a k < T`, limsup-then-`k→∞` control of the oscillation after `a k`) for `Y n` valued in `C(Icc 0 T, E)`, `E` separable, `0 < T`. Commit `e7d9564`. |

### C12

Determining classes.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C12.1 | laws on `D_T` with equal fdd on finite subsets of a dense `S∋T` are equal | DELIVERED (exact) | `BGW.Skorokhod.ext_of_finiteDimensional` | `BGW.Skorokhod.MeasurableLaws` | Separable `E`, `hT0 : 0≤T`. |
| C12.2 | laws a.s. continuous at `T` with equal prefix laws `P∘r_a⁻¹` for `a→T` are equal (no C4 needed) | DELIVERED (equivalent/stronger form) | `BGW.Skorokhod.ext_of_restrict` | `BGW.Skorokhod.Prefix` | Hypotheses `a k<T`, `a k→T`, `P`, `Q` a.s. continuous at `T`, `P.map (restrict ·) = Q.map (restrict ·)` for all `k` (no continuity-at-`a` side condition needed; weaker hypotheses than the spec, so stronger). The unrelated `BGW.Skorokhod.DLoc.ext_of_restrict` is a path-level lemma. |
| C12.3 | `{t : P(f(t−)≠f(t))>0}` countable for every law `P` on `D_T` | CORRECTED (e) (exact) | `BGW.Skorokhod.countable_setOf_measure_jump_ne_zero` | `BGW.Skorokhod.MeasurableJumps` | CORRECTED hypothesis: needs `E` separable (report correction (e)); the spec's `E=ℝ` case is covered. |

### C13

Prokhorov.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C13 | Prokhorov: tight ⇒ relatively compact (and converse on Polish), `IsTightMeasureSet.prodMk`, metrizability | DELIVERED (exact) | Mathlib `MeasureTheory.isCompact_closure_of_isTightMeasureSet`, `isTightMeasureSet_of_isCompact_closure`, `IsTightMeasureSet.prodMk` (all present in the pinned Mathlib); BGW converse on `D`: `BGW.Skorokhod.isTightMeasureSet_iff_isCompact_closure_D` | `Mathlib.MeasureTheory.Measure.Prokhorov`, `Mathlib.MeasureTheory.Measure.Tight`, `BGW.Skorokhod.PolishTightness` | Status-only item ("nothing new needed"); BGW additionally gives the iff on `D` for complete separable `E`. |

### C14

Skorokhod representation.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C14 | Skorokhod representation (spec: not needed, avoided) | CORRECTED (a) (equivalent/stronger form) | `BGW.Probability.exists_tendsto_ae_of_tendsto` (Polish, on `unitInterval`); `BGW.Probability.exists_probabilitySpace_tendsto_ae_of_tendsto` and `BGW.Probability.exists_probabilitySpace_tendsto_ae_of_tendsto_metric` (separable, some probability space); `BGW.Skorokhod.exists_tendsto_ae_of_tendsto_D` (on `D`) | `BGW.Probability.SkorokhodRepresentation`, `BGW.Probability.SeparableRepresentation`, `BGW.Skorokhod.PolishTightness` | Delivered although the spec says to avoid it (scheduled-optional, not removed). CORRECTED: the `[0,1]` version is false for non-Polish separable spaces (Bernstein set), hence Polish-only on `[0,1]` plus the general-probability-space version (Dudley) (report correction (a)). Nothing in C1-C14 depends on it. |

### C15

Stable law $\mu_\theta$, density $p_1$, $p_t$, kernels $q_s$, $\Gamma_a$.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C15.1a | `μ_θ = p_1 dx` probability measure; unconditional (no `BGW.StableTrees.StableDomain` witness) | DELIVERED (equivalent/stronger form) | `BGW.StableTrees.stableLaw` (def, `ProbabilityMeasure ℝ`), `BGW.StableTrees.stableLaw_eq_withDensity`, `BGW.StableTrees.integral_stableDensity`, `BGW.StableTrees.stableDensity_nonneg`, `BGW.StableTrees.exists_stableDomain`, (underlying: `BGW.StableTrees.Scalar.limitLaw_eq_withDensity`) | `BGW.StableTrees.StableLaw`, `BGW.StableTrees.Scalar.DensityLaw` | Unconditional for `1<θ≤2`; witness is an explicit Pareto-tail offspring law (`exists_stableDomain`, from `BGW.StableTrees.existsStableDomain_pareto`), as the spec's "bridge". `BGW.StableTrees.stableLaw` is junk outside `1<θ≤2` |
| C15.1b | Laplace transform `∫ e^{-λx} μ_θ(dx)=e^{λ^θ}`, λ≥0 | DELIVERED (exact) | `BGW.StableTrees.integral_exp_neg_mul_stableLaw` (sketch name `stableLaw_laplace`), uniqueness `BGW.StableTrees.eq_stableLaw_of_laplace` | `BGW.StableTrees.StableLaw` | Stated for `0 ≤ lam`; uniqueness is for `lam>0` |
| C15.1c | characteristic function `exp((−iu)^θ)` | DELIVERED (exact) | `BGW.StableTrees.charFun_stableLaw` (= `Scalar.stableCF θ t := cexp ((-(t*I))^(θ:ℂ))`), `BGW.StableTrees.Scalar.charFun_withDensity_stableDensity` | `BGW.StableTrees.StableLaw`, `BGW.StableTrees.Scalar.DensityLaw` | principal power |
| C15.2a | `p_1` continuous, Lipschitz | DELIVERED (exact) | `BGW.StableTrees.Scalar.continuous_stableDensity`, `BGW.StableTrees.Scalar.lipschitzWith_stableDensity` | `BGW.StableTrees.Scalar.Density` | explicit Lipschitz constant |
| C15.2b | `p_1` bounded | DELIVERED (exact) | `BGW.StableTrees.Scalar.exists_stableDensity_le` | `BGW.StableTrees.Scalar.Density` |  |
| C15.2c | `p_1(0)=Γ(1+1/θ)sin(π/θ)/π>0` | DELIVERED (exact) | `BGW.StableTrees.Scalar.stableDensity_zero`, `BGW.StableTrees.Scalar.stableDensity_zero_pos`; alt. form `BGW.StableTrees.stableDensity_zero_eq_inv_theta_gamma` (= `(1/θ)/Γ(1−1/θ)`) | `BGW.StableTrees.Scalar.Density`, `BGW.StableTrees.ExcursionLifetime` |  |
| C15.3a | `sup_x \|x p_1(x)\| < ∞` | DELIVERED (exact) | `BGW.StableTrees.exists_abs_mul_stableDensity_le` (+ `BGW.StableTrees.differentiable_stableDensity`) | `BGW.StableTrees.Scalar.StableDensityBounds` |  |
| C15.3b | `sup_x \|x p_1'(x)\| < ∞` | DELIVERED (exact) | `BGW.StableTrees.exists_abs_mul_deriv_stableDensity_le` | `BGW.StableTrees.Scalar.StableDensityBounds` |  |
| C15.3c | "tranche 1" consequences `qKernel_one_lipschitzOn`, `sizeTailKernel_lipschitz` | ARTICLE-SIDE | not in `BGW/` | — | Spec (d): "item 3 is already in tranche 1" (project side); not required of the library |
| C15.4a | semigroup `p_s * p_t = p_{s+t}` (density form) | DELIVERED (exact) | `BGW.StableTrees.stableDensityAt` (def, `t^{-1/θ}p_1(t^{-1/θ}x)`), `BGW.StableTrees.integral_stableDensityAt_mul` (sketch name `pDens_conv`) | `BGW.StableTrees.StableLaw` | `∫ y, p_s y * p_t (x−y) = p_{s+t} x` for `s,t>0`, all x; exactly the spec form |
| C15.4b | semigroup, measure form; `p_t` is the density of `stableLawAt θ t` | DELIVERED (equivalent/stronger form) | `BGW.StableTrees.stableLawAt` (def), `BGW.StableTrees.stableLawAt_eq_withDensity`, `BGW.StableTrees.stableLawAt_conv` (`∗`), `BGW.StableTrees.integral_exp_neg_mul_stableLawAt` | `BGW.StableTrees.StableLaw` | extra |
| C15.5 | `∫ p_1(−u)1_{u>0}du = P(X_1<0)=1/θ` | DELIVERED (exact) | `BGW.StableTrees.integral_stableDensity_neg_Ioi`, `BGW.StableTrees.stableLaw_Iio_zero`, `BGW.StableTrees.stableLaw_Ioi_zero`, `BGW.StableTrees.stableLaw_singleton_zero`, `BGW.StableTrees.stableLawAt_Iio_zero` | `BGW.StableTrees.StablePositivity` |  |
| C15.6 | `p_1>0` on ℝ (optional) | DELIVERED (exact) | `BGW.StableTrees.stableDensity_pos` | `BGW.StableTrees.Scalar.StableDensityPos` | declaration is stated as `0 < Scalar.stableDensity θ x`, all x, `1<θ≤2` (file `Scalar/StableDensityPos.lean`, namespace `BGW.StableTrees`) |
| C15.7a | `BGW.StableTrees.gammaA` definition `θ q_{1−a}(x)/G_{1−a}(x)`; `BGW.StableTrees.qKernel`, `BGW.StableTrees.sizeTailKernel` | DELIVERED (exact) | `BGW.StableTrees.qKernel`, `BGW.StableTrees.sizeTailKernel`, `BGW.StableTrees.sizeTailKernelENN`, `BGW.StableTrees.gammaA`, `BGW.StableTrees.gammaA_mul_sizeTail`, `BGW.StableTrees.qKernel_eq_kendallKernel` | `BGW.StableTrees.KendallAdapter` |  |
| C15.7b | `Γ_a` continuous | DELIVERED (equivalent/stronger form) | `BGW.StableTrees.continuousOn_gammaA`, `BGW.StableTrees.measurable_gammaA` | `BGW.StableTrees.KendallAdapter` | Joint continuity on `{(a,x) : a<1, 0<x}`; stronger than continuity in x on (0,∞) |
| C15.7c | `Γ_a` positive (and nonneg.) | DELIVERED (exact) | `BGW.StableTrees.gammaA_pos` (`a<1`, `0<x`), `BGW.StableTrees.gammaA_nonneg`, `BGW.StableTrees.sizeTailKernel_pos` | `BGW.StableTrees.Scalar.StableDensityPos`, `BGW.StableTrees.KendallAdapter` |  |

### C16

The $\theta$-stable spectrally positive Lévy process as a law on $D([0,T])$.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C16.a1 | f.d.d. characterization `BGW.StableTrees.IsStableLevyLaw` (start at 0 a.s.; independent stable increments along `0=t_0<…`) | DELIVERED (exact) | `BGW.StableTrees.IsStableLevyLaw` (structure with `start`, `increments`), `BGW.StableTrees.IsStableLevyLaw.map_increments` | `BGW.StableTrees.StableLevyLaw` | increments law `Measure.pi (stableLawAt θ (t_i−t_{i−1}))` |
| C16.a2 | uniqueness of `P^X_T` | DELIVERED (exact) | `BGW.StableTrees.IsStableLevyLaw.unique` (`0<T`, `1<θ≤2`) | `BGW.StableTrees.StableLevyLaw` | via f.d.d. determining class |
| C16.a3 | existence of `P^X_T` on `D_T` | DELIVERED (exact) | `BGW.StableTrees.exists_isStableLevyLaw`, `BGW.StableTrees.existsUnique_isStableLevyLaw`, `BGW.StableTrees.stableProcessLaw` (def), `BGW.StableTrees.isStableLevyLaw_stableProcessLaw`, `BGW.StableTrees.eq_stableProcessLaw_iff`, `BGW.StableTrees.map_eval_stableProcessLaw`, `BGW.StableTrees.ae_eval_zero_stableProcessLaw` | `BGW.StableTrees.StableProcessLaw` | route R-F (FCLT + tightness + Prokhorov) |
| C16.P1 | consistency under restriction | DELIVERED (exact) | `BGW.StableTrees.IsStableLevyLaw.map_restrict`, `BGW.StableTrees.map_restrict_stableProcessLaw` | `BGW.StableTrees.StableLevyLaw`, `BGW.StableTrees.StableProcessLaw` |  |
| C16.P2 | scaling `c^{-1/θ}X_{ct}` | DELIVERED (exact) | `BGW.StableTrees.IsStableLevyLaw.map_timeSpaceScale`, `BGW.StableTrees.stableProcessLaw_scaling` | `BGW.StableTrees.StableLevyLaw`, `BGW.StableTrees.StableProcessMarkov` | via `BGW.Skorokhod.timeSpaceScale` |
| C16.P3 | no fixed discontinuities | DELIVERED (exact) | `BGW.StableTrees.IsStableLevyLaw.ae_continuousAt`, `BGW.StableTrees.ae_continuousAt_stableProcessLaw` | `BGW.StableTrees.StableLevyLaw`, `BGW.StableTrees.StableProcessLaw` | for every `t ∈ [0,T]` |
| C16.P4 | a.s. no negative jumps `X_t ≥ X_{t−}` | DELIVERED (exact) | `BGW.StableTrees.ae_leftLim_le_stableProcessLaw` (`leftLim f t ≤ f t`, all t), `BGW.StableTrees.ae_leftLim_le_stableLocalLaw` | `BGW.StableTrees.StableProcessNoNegativeJumps`, `BGW.StableTrees.StableLocalLaw` |  |
| C16.P5a | simple Markov property at fixed `s≤T` | DELIVERED (exact) | `BGW.StableTrees.stableProcessLaw_simpleMarkov` (indep. of `BGW.Skorokhod.restrict`, law `stableProcessLaw θ (T−s)` of `BGW.Skorokhod.shiftIncrement`); on `[0,∞)`: `BGW.StableTrees.map_shift_stableLocalLaw`, `BGW.StableTrees.indep_filtration_shift_stableLocalLaw`, `BGW.StableTrees.condExp_shift_stableLocalLaw` | `BGW.StableTrees.StableProcessMarkov`, `BGW.Skorokhod.Restrict`, `BGW.Skorokhod.ShiftIncrement`, `BGW.StableTrees.StableLocalMarkov` | past = natural past σ-algebra. Reweighting identity needed for C31: `BGW.StableTrees.bridgePrefix_consistent`, `BGW.StableTrees.bridgePrefix_mass_one` (`BGW.StableTrees.BridgePrefix`) |
| C16.P5b | strong Markov at stopping times | DELIVERED (equivalent/stronger form) | `BGW.StableTrees.map_shiftAt_restrict_stableLocalLaw`, `BGW.StableTrees.integral_shiftAt_mul_past`, `BGW.StableTrees.condExp_shiftAt_of_ae_lt_top` | `BGW.StableTrees.StableStrongMarkov` | On the carrier `DLoc` (paths on `[0,∞)`), stopping times of `DLoc.filtration` (right-continuous), not on `D_T`; needed only for Parts F/B (spec (d)) |
| C16.P6 | θ=2: `P^X_T` = law of `√2 B` | DELIVERED (exact) | `BGW.StableTrees.stableProcessLaw_two`, `BGW.StableTrees.coe_stableProcessLaw_two` (`= wienerD (NNReal.sqrt 2) T`) | `BGW.StableTrees.StableProcessBrownian` |  |
| C16.ext | law on `[0,∞)` (`DLoc`) used by Parts F/B | DELIVERED (equivalent/stronger form) (extra) | `BGW.StableTrees.stableLocalLaw`, `BGW.StableTrees.eq_stableLocalLaw_iff`, `BGW.StableTrees.map_restrict_stableLocalLaw`, `BGW.StableTrees.map_eval_stableLocalLaw` | `BGW.StableTrees.StableLocalLaw` |  |

### C17

Functional limit theorem for walks in the stable domain.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C17.main | FCLT `S_{⌊nt⌋}/B_n ⇒ P^X_T` in `D_T`, all `T>0` | DELIVERED (equivalent/stronger form) | `BGW.StableTrees.IsRealStableAttracted.tendsto_stepPathLaw` (sketch name `fclt_stable`), `BGW.StableTrees.IsRealStableAttracted` (structure) | `BGW.StableTrees.StableProcessLaw`, `BGW.StableTrees.RealAttraction` | Real iid steps, `B` only eventually positive, no centering/monotonicity (stronger than the spec). Also `…tendsto_map_realStepPath_iid` (any iid realization). Hypothesis is `scaledSumLaw ν B n → stableLaw θ`, i.e. spec's `BGW.StableTrees.StableDomain`/`IsStableAttracted ν θ 0 B` |
| C17.main-int | integer-step and offspring forms | DELIVERED (exact) | `BGW.StableTrees.Attraction.IsStableAttracted.tendsto_stepPathLaw`, `BGW.StableTrees.StableDomain.tendsto_stepPathLaw` | `BGW.StableTrees.StableProcessLaw` |  |
| C17.main-Donsker | θ=2 finite-variance instance | DELIVERED (exact) (extra) | `BGW.StableTrees.tendsto_stepPathLaw_wienerD_of_finiteVariance` | `BGW.StableTrees.StableProcessBrownian` |  |
| C17.i | same along any subsequence | DELIVERED (exact) | `BGW.StableTrees.IsRealStableAttracted.tendsto_stepPathLaw_subseq` | `BGW.StableTrees.StableProcessLaw` |  |
| C17.ii | `B_{⌊nt⌋}/B_n → t^{1/θ}` | DELIVERED (exact) | `BGW.StableTrees.IsRealStableAttracted.tendsto_norming_floor_ratio`, general `BGW.StableTrees.IsRealStableAttracted.tendsto_norming_ratio` | `BGW.StableTrees.StableProcessCompactness`, `BGW.StableTrees.RealAttraction` | `m_j/q_j → c>0 ⇒ B(m_j)/B(q_j) → c^{1/θ}` |
| C17.iii | random time change + Lemma 6.2(i) ⇒ Lemma 6.2(ii) | ARTICLE-SIDE | none (deterministic ingredients only: `BGW.Skorokhod.timeSpaceScale`, continuity of scaling maps) | `BGW.Skorokhod.Scaling` | The random scalar time and space perturbation belongs to the proof of the article's Lemma 6.2(ii). |

### C18

Fluctuation basics (regularity of 0, first passage, Kendall, unique minimum).

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C18.F1a | `I` continuous, nonincreasing, `I_t→−∞` | DELIVERED (exact) | `BGW.StableTrees.ae_runningInf_continuous_antitone_tendsto` (`BGW.StableTrees.runningInfLoc`) | `BGW.StableTrees.StableFirstPassage`, `BGW.StableTrees.StableFirstPassagePath` | on `DLoc` |
| C18.F1b | `X_{T_x}=−x` (creeping down), all x>0 simultaneously | DELIVERED (exact) | `BGW.StableTrees.ae_creeping_down_stableLocalLaw`, `BGW.StableTrees.ae_strictPassageBelow_ne_top` | `BGW.StableTrees.StableFirstPassage` |  |
| C18.F2 | 0 regular for `(−∞,0)` and `(0,∞)` | DELIVERED (exact) | `BGW.StableTrees.ae_regular_both_stableLocalLaw` (`DLoc.RegularBelowAtZero ∧ RegularAboveAtZero`), also after stopping times: `BGW.StableTrees.ae_regular_both_shiftAt_stableLocalLaw` | `BGW.StableTrees.StableRegularity` | via Blumenthal 0-1 (`BGW.StableTrees.measure_zeroOne_filtration_zero`, `BGW.StableTrees.StableLocalMarkov`) |
| C18.F3a | `(T_x)` subordinator: monotone càdlàg from 0, →∞ | DELIVERED (exact) | `BGW.StableTrees.ae_isCadlag_monotone_passage`, `BGW.StableTrees.ae_tendsto_passageTime_atTop`, `BGW.StableTrees.passageTime`, `BGW.StableTrees.passageLaw` | `BGW.StableTrees.StablePassageSubordinator` |  |
| C18.F3b | independent stationary increments | DELIVERED (equivalent/stronger form) | `BGW.StableTrees.measure_inter_passageIncrement` (independence of `F_{T_x}` and `T_{x+y}−T_x`, with law `passageLaw θ y`), `BGW.StableTrees.map_passageIncrement`, `BGW.StableTrees.firstPassage_map_increments` | `BGW.StableTrees.StablePassageSubordinator`, `BGW.StableTrees.StablePassageSubordinatorIncrements` | independence stated against the stopped σ-algebra |
| C18.F3c | `E e^{−λT_x}=e^{−xλ^{1/θ}}` | DELIVERED (exact) | `BGW.StableTrees.integral_exp_neg_strictPassageBelow`, `BGW.StableTrees.lintegral_exp_neg_firstPassageBelow`, `BGW.StableTrees.integral_exp_neg_passageLaw`, uniqueness `BGW.StableTrees.eq_passageLaw_of_integral_exp_neg` | `BGW.StableTrees.StableFirstPassage`, `BGW.StableTrees.StablePassageSubordinator` |  |
| C18.F4 | Kendall `P(T_x∈ds)=(x/s)p_s(−x)ds` | DELIVERED (exact) | `BGW.StableTrees.kendall` (`passageLaw θ x = withDensity (x/s * stableDensityAt θ s (−x))` on `Ioi 0`), `BGW.StableTrees.integral_passageLaw_eq_kendall`, `BGW.StableTrees.lintegral_kendallKernel`, `BGW.StableTrees.qKernel_eq_kendallKernel`, `BGW.StableTrees.passageLaw_eq_qKernel` | `BGW.StableTrees.StableKendall`, `BGW.StableTrees.KendallAdapter` | for every `x>0` |
| C18.F5 | duality (time reversal of increments) | DELIVERED (exact) | `BGW.Skorokhod.reverseIncrements` (`u ↦ f T − f((T−u)−)`), `BGW.StableTrees.map_reverseIncrements_stableProcessLaw` | `BGW.Skorokhod.ReverseIncrements`, `BGW.StableTrees.StableProcessReversal` | on `D_T`, `T>0` |
| C18.F6a | unique minimizer (value or left limit) on fixed `[0,t]` | DELIVERED (exact) | `BGW.StableTrees.stableProcessLaw_ae_existsUnique_generalizedMinimizer`, `BGW.StableTrees.IsStableLevyLaw.ae_existsUnique_generalizedMinimizer`, `BGW.StableTrees.IsStableLevyLaw.ae_existsUnique_windowMinimizer`, transfer to absolutely continuous laws | `BGW.StableTrees.StableUniqueMinimum` |  |
| C18.F6b | minimizer interior, X continuous there | DELIVERED (exact) | `BGW.StableTrees.stableProcessLaw_ae_unique_continuous_minimum`, `BGW.StableTrees.IsStableLevyLaw.ae_unique_continuous_minimum`, `BGW.StableTrees.IsStableLevyLaw.ae_regular_after_jumps` | `BGW.StableTrees.StableContinuousMinimum` | `0<g<T`, `ContinuousAt f g`, `min (leftLim f g) (f g) = ⨅ f`, uniqueness |

### C19

$\theta=2$ instance, $X=\sqrt2 B$.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C19.1 | `P^X_T` = image of Wiener measure under `√2·` and `C→D` | DELIVERED (exact) | `BGW.ContinuumTrees.BrownianD.wienerD`, `BGW.StableTrees.stableProcessLaw_two`, `BGW.StableTrees.coe_stableProcessLaw_two` | `BGW.ContinuumTrees.BrownianD`, `BGW.StableTrees.StableProcessBrownian` |  |
| C19.2 | `X^br = √2·BrownianBridge.law` | DELIVERED (exact) | `BGW.ContinuumTrees.BrownianD.bridgeD` (def via `BGW.ContinuumTrees.BrownianBridge.law`), `stableBridgeLaw_two : stableBridgeLaw 2 = bridgeD (NNReal.sqrt 2)` | `BGW.ContinuumTrees.BrownianD`, `BGW.ContinuumTrees.BrownianBridge` | also `BGW.ContinuumTrees.BrownianD.map_eval_bridgeD` (marginals) |
| C19.3 | bridge prefix density `p_{1−a}(−X_a)/p_1(0)` (Gaussian, variance 2t) | DELIVERED (exact) | `BGW.ContinuumTrees.BrownianD.map_restrict_bridgeD_eq_withDensity`, `BGW.ContinuumTrees.BrownianD.map_restrict_bridgeD_absolutelyContinuous`, `BGW.StableTrees.BrownianIdentification.bridgePrefixWeight_two`, `BGW.StableTrees.BrownianIdentification.stableDensity_two` | `BGW.ContinuumTrees.BrownianD`, `BGW.StableTrees.BrownianIdentification` |  |
| C19.4 | `X^exc = √2·VervaatBridge.law` | DELIVERED (exact) | `BGW.StableTrees.BrownianIdentification.levyExcLaw_two` | `BGW.StableTrees.BrownianExcursion` | this is the C35-at-θ=2 identification (CT8 K08, K18b); no longer open |
| C19.5 | `H=X−I`; under N, `H^exc=X^exc` | DELIVERED (exact) | `BGW.StableTrees.ae_heightLoc_two` (`heightLoc = X−I` all times), `BGW.StableTrees.ae_height_two`, `BGW.StableTrees.BrownianIdentification.excLaw_two`, `BGW.StableTrees.BrownianIdentification.excLaw_two_map_diag`, `BGW.StableTrees.excLaw_height_eq_path_two` | `BGW.StableTrees.BrownianHeight`, `BGW.StableTrees.HeightProcessTwo`, `BGW.StableTrees.BrownianPair`, `BGW.StableTrees.JointExcursion` |  |

### C20

Reflected process $X-I$, local time $-I$.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C20.1 | `X−I` is strong Markov for `(F_t)` | DELIVERED (equivalent/stronger form) | `BGW.StableTrees.condExp_reflectedFutureAt`, `BGW.StableTrees.reflectedFutureAt`, `BGW.StableTrees.reflectedStateAt`, `BGW.StableTrees.reflectedFutureAt_apply`; ingredients `BGW.StableTrees.reflectedFrom`, `BGW.StableTrees.reflectedFrom_restart`, `BGW.StableTrees.reflectedFrom_restart_shiftAt` | `BGW.StableTrees.ExcursionGapsStrongMarkov`, `BGW.StableTrees.ReflectedRestart` | For the right-continuous canonical filtration `DLoc.filtration`: for an a.s. finite stopping time `τ` and bounded measurable `G`, the conditional expectation given `F_τ` of `G` of the post-`τ` reflected path is the integral of `G ∘ reflectedFrom (reflectedStateAt τ f)` against `stableLocalLaw θ`. Commit `e1dcb5c`. The augmented-filtration form (spec wording) is C20.1-aug. |
| C20.1-aug | `X−I` strong Markov for the augmented filtration | DELIVERED (exact) | `BGW.StableTrees.condExp_reflectedFutureAt_augmented`, `BGW.StableTrees.stableAugmentedFiltration`, `BGW.StableTrees.StableCompletedSpace` | `BGW.StableTrees.AugmentedStrongMarkov` | Node G1b, commit `6581280`: stopping times of the usual augmentation (null sets joined, right-regularized) on the completed space; conditional expectation under the completed law. |
| C20.2 | 0 regular for itself (for `X−I`) | DELIVERED (equivalent/stronger form) | `BGW.StableTrees.ae_regular_both_stableLocalLaw`, `BGW.StableTrees.ae_regular_both_shiftAt_stableLocalLaw`, `BGW.StableTrees.ae_strictPassage_zero_stableLocalLaw` | `BGW.StableTrees.StableRegularity` | regularity of `X−I` at 0 follows from regularity of `(−∞,0)` for X; not stated verbatim in that form |
| C20.3 | `−I` local time of `X−I` at 0, right-continuous inverse `x ↦ T_x` | DELIVERED (exact) | `BGW.StableTrees.localTime` (`= −runningInfLoc`), `BGW.StableTrees.ae_localTime_spec`, `BGW.StableTrees.firstPassageBelow_eq_inverseLocalTime`, `BGW.StableTrees.ae_runningInf_const_off_zeroSet`, `BGW.StableTrees.ae_localTime_passageTime` | `BGW.StableTrees.StablePassageSubordinator`, `BGW.StableTrees.StablePassageSubordinatorStieltjes` |  |

### C21

Itô excursion theorem for $X-I$, excursion measure $N$.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C21.1 | `Σ δ_{(−I_{g_i},ω^i)}` Poisson point measure, intensity `dt⊗N` | DELIVERED (equivalent/stronger form) | `BGW.StableTrees.excursionPointMeasure` (def), `BGW.StableTrees.excursionMeasure`, `BGW.StableTrees.excursionCounts_poisson_independent`, `BGW.StableTrees.excursionCounts_poisson_independent_pointMeasure`, `BGW.StableTrees.lintegral_pointMeasure_eq_prod` (`E ξ(B)=(lebNN ⊗ N)(B)`), `BGW.StableTrees.isTimeSimpleLevy_of_ae_eq_excursionPointMeasure`, `BGW.StableTrees.lintegral_windowMark_eq`, `BGW.StableTrees.ae_excursionPointMeasure_counting`, `BGW.StableTrees.exists_measurable_modification_excursionPointMeasure` | `BGW.StableTrees.MarkedExcursionsBasic`, `BGW.StableTrees.ExcursionMeasureBasic`, `BGW.StableTrees.ExcursionMeasureCounts`, `BGW.StableTrees.ExcursionMeasureIntensity`, `BGW.StableTrees.MarkedExcursionsMarkov`, `BGW.StableTrees.ExcursionMeasureWindow`, `BGW.StableTrees.MarkedExcursionsMeasurable` | Poisson statement is the counts form (independent Poisson counts of boxes with `N(A_i)<∞`, mean `(t−s)N(A)`) with intensity identification; `N` is *defined* as the intensity `N A = E ξ((0,1]×A)`, so the theorem identifies it with the law of excursions. Excursion windows: `BGW.StableTrees.ae_isExcursionInterval_iff`, `BGW.StableTrees.ae_pos_set_eq_iUnion_jump_intervals` (`BGW.StableTrees.StableExcursionSupport`) |
| C21.2 | `ℰ`, `ζ`; `N` σ-finite | DELIVERED (exact) | `BGW.StableTrees.Excursion` (tagged carrier, `BGW.StableTrees.Excursion.lifetime`, `BGW.StableTrees.Excursion.lifetime_pos`), `BGW.StableTrees.sigmaFinite_excursionMeasure`, `BGW.StableTrees.excursionMeasure_lifetime_slab_lt_top` | `BGW.ContinuumTrees.ExcursionCarrier`, `BGW.StableTrees.ExcursionMeasureBasic` | carrier uses a positive tag `ζ` with `ζ = sSup{ω>0}` proved a.e. (next row) |
| C21.3 | `N(ζ>t)=t^{−1/θ}/Γ(1−1/θ)` | DELIVERED (exact) | `BGW.StableTrees.excursionMeasure_lifetime_tail`, `BGW.StableTrees.excursionMeasure_lifetime_tail_scale`, `BGW.StableTrees.excursionMeasure_lifetime_density` | `BGW.StableTrees.ExcursionLifetimeTail`, `BGW.StableTrees.ExcursionLifetimeDensity` |  |
| C21.4 | `N(1−e^{−λζ})=λ^{1/θ}` | DELIVERED (exact) | `BGW.StableTrees.lintegral_one_sub_exp_lifetime` (`q≥0`) | `BGW.StableTrees.ExcursionLifetimeLaplace` |  |
| C21.5 | N-a.e. `ω(s)>0` on `(0,ζ)`, ends continuously (no negative jump) | DELIVERED (exact) | `BGW.StableTrees.ae_excursionMeasure_support` (positivity on `(0,ζ)`, `ζ=sSup{ω>0}`, `ω(0)=0`, continuity at 0, `ω(t)→0` as `t↑ζ`), `BGW.StableTrees.ae_excursionMeasure_of_ae_jumpExcursion` | `BGW.StableTrees.ExcursionMeasureSupport`, `BGW.StableTrees.ExcursionMeasureSupportTransfer` |  |

### C22

Itô description of $N$, normalized excursion $X^{\mathrm{exc}}$, $N(\cdot\mid\zeta>1)$.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C22.Ito-a | family `N_{(a)}` with `N_{(a)}(ζ=a)=1` and scaling `S^{(λ)}_*N_{(a)}=N_{(λa)}` | DELIVERED (exact) | `BGW.StableTrees.measure_lifetime_excursionAt`, `BGW.StableTrees.excursionAt_scaling`, `BGW.StableTrees.unitExcursionLaw`, `BGW.StableTrees.excursionAt`, `BGW.StableTrees.ae_lifetime_unitExcursionLaw`, `BGW.StableTrees.isProbabilityMeasure_unitExcursionMeasure`, `BGW.StableTrees.excursionScale` | `BGW.StableTrees.ExcursionGapsIto`, `BGW.StableTrees.UnitExcursionLawBasic`, `BGW.ContinuumTrees.ExcursionCarrier` | `N_(a)(ζ = a) = 1` for every `a > 0` (`BGW.StableTrees.measure_lifetime_excursionAt`) and `S^(λ)_*N_(a) = N_(λa)` (`BGW.StableTrees.excursionAt_scaling`); `excursionAt θ u` is the image of `BGW.StableTrees.unitExcursionLaw` under the scaling `S_u`. Commit `e1dcb5c` (modules `BGW.StableTrees.ExcursionGapsIto`, `BGW.StableTrees.UnitExcursionLawBasic`). |
| C22.Ito-b | `N=∫N_{(a)} p_1(0)a^{−1−1/θ}da` | DELIVERED (exact) | `BGW.StableTrees.excursionMeasure_eq_lifetime_mixture`, `BGW.StableTrees.lintegral_excursionMeasure_eq_mixture`, `BGW.StableTrees.setLIntegral_excursionMeasure_eq_mixture`, `BGW.StableTrees.lifetimeDensity` | `BGW.StableTrees.UnitExcursionLawMixture`, `BGW.StableTrees.UnitExcursionLawBasic` | density `(1/θ)/Γ(1−1/θ)·u^{−1−1/θ}` = `p_1(0)u^{−1−1/θ}` via `BGW.StableTrees.stableDensity_zero_eq_inv_theta_gamma` |
| C22.Ito-c | uniqueness of the family | DELIVERED (exact) | `BGW.StableTrees.excursionAt_unique`, `BGW.StableTrees.excursionMeasure_unique_of_scaling`, `BGW.StableTrees.map_excursionScale_excursionMeasure` | `BGW.StableTrees.ExcursionGapsIto`, `BGW.StableTrees.UnitExcursionLawJoint`, `BGW.StableTrees.ExcursionLifetimeScaling` | `BGW.StableTrees.excursionAt_unique`: a measurable family of probability measures with exact lifetime support, the scaling law and the lifetime mixture of `N` equals `excursionAt θ`, so the family is unique. Commit `e1dcb5c`. `BGW.StableTrees.excursionMeasure_unique_of_scaling` is the uniqueness of `N`. |
| C22.def | `N(·\|ζ=1):=N_{(1)}`; agrees with normalization of `N(·\|ζ>t)`, independent of t | DELIVERED (exact) | `BGW.StableTrees.unitExcursionLaw`, `BGW.StableTrees.levyExcLaw`, `BGW.StableTrees.normalize_tail_independent_of_threshold`, `BGW.StableTrees.normalizeExc`, `BGW.StableTrees.tailExcursionLaw` | `BGW.StableTrees.UnitExcursionLawBasic`, `BGW.StableTrees.UnitExcursionLawJoint`, `BGW.ContinuumTrees.ExcursionCarrier` |  |
| C22.E1 | `X^exc_0=0`, `X^exc_1=X^exc_{1−}=0`, `X^exc_s>0` on `(0,1)` | DELIVERED (exact) | `BGW.StableTrees.levyExcLaw_endpoints_pos`, `BGW.StableTrees.ae_unitExcursionLaw_positive` | `BGW.StableTrees.UnitExcursionLaw`, `BGW.StableTrees.UnitExcursionLawSupport` |  |
| C22.E2 | no fixed discontinuities | DELIVERED (exact) | `BGW.StableTrees.levyExcLaw_noFixedJump` (`t∈(0,1)`, `BGW.StableTrees.NoFixedJumpUnit`), `BGW.StableTrees.N_noFixedJump` (under `N`) | `BGW.StableTrees.UnitExcursionDensity`, `BGW.StableTrees.UnitExcursionDensityGoodTimes`, `BGW.StableTrees.ExcursionMarkovConsequences` | endpoints covered by E1 |
| C22.E3 | θ<2 jump, `Δ̄>0`; θ=2 continuous | DELIVERED (exact) | `BGW.StableTrees.ae_maxJump_pos_levyExcLaw`, `BGW.StableTrees.ae_maxJump_eq_zero_levyExcLaw_two`, `BGW.StableTrees.ae_maxJump_pos_iff_levyExcLaw`; input `BGW.StableTrees.ae_forall_exists_pos_jump` | `BGW.StableTrees.ExcursionJump`, `BGW.StableTrees.StablePositiveJumps` | optional item, delivered in CT10 |
| C22.E4a | Itô mixture: `N(·\|ζ>1)` on `[0,1]` = U-mixture of scaled `(X^exc,H^exc)`, `U` density `(1/θ)u^{−1−1/θ}` on `(1,∞)`, path `U^{1/θ}`, height `U^{1−1/θ}` | DELIVERED (exact) | `BGW.StableTrees.tailExcLaw` (def, horizon `T`), `BGW.StableTrees.tailExcLaw_eq_mixture` (joint pair), `BGW.StableTrees.pairStretch`, `BGW.StableTrees.tailExcursionLaw_eq_mixture`, `BGW.StableTrees.tailLevyExcLaw_eq_mixture` | `BGW.StableTrees.JointExcursion`, `BGW.StableTrees.UnitExcursionLawMixture` | `tailExcLaw θ T` carries a horizon `T` (spec sketch: `tailExcLaw θ` on [0,1]); `T=1` is the spec object. Mixture proved for every `T>0` |
| C22.E4b | under `N(·\|ζ>1)`: no fixed discontinuity on [0,1], `X_t>0` on `(0,1]` | DELIVERED (exact) | `BGW.StableTrees.N_noFixedJump`, `BGW.StableTrees.ae_excursionMeasure_support`, `BGW.StableTrees.ae_tailExcursionLaw_support` | `BGW.StableTrees.ExcursionMarkovConsequences`, `BGW.StableTrees.ExcursionMeasureSupport`, `BGW.StableTrees.UnitExcursionLawSupport` | `BGW.StableTrees.ae_tailExcursionLaw_support`: `1<ζ`, positive on `(0,ζ)`, left limit 0 at ζ |
| C22.R-H | `BGW.StableTrees.excLaw` on `D 1 ℝ × C(I,ℝ)` | DELIVERED (exact) | `BGW.StableTrees.excLaw`, `BGW.StableTrees.excLaw_map_fst`, `BGW.StableTrees.tailExcLaw_map_fst`, `BGW.StableTrees.tailExcLaw_map_restrictPair`, `BGW.StableTrees.excLaw_height_endpoints_pos` | `BGW.StableTrees.JointExcursion` |  |

### C23

Markov property under $N$.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C23.a | `N(F·G(X_{t+·})1{ζ>t})=N(F·E_{X_t}[G(X_{·∧T_0})]1{ζ>t})` | DELIVERED (exact) | `BGW.StableTrees.excursion_markov_lintegral` (nonneg., `F` on prefix `D t ℝ`, `G` on `BGW.Skorokhod.DLoc`), `BGW.StableTrees.excursion_markov_integral` (signed bounded), `BGW.StableTrees.killedStableKernel` (`BGW.StableTrees.isMarkovKernel_killedStableKernel`, `BGW.StableTrees.killedStableKernel_apply`, `BGW.StableTrees.killedStableKernel_zero`), `BGW.StableTrees.futureFrom`, `BGW.StableTrees.killedPath` | `BGW.StableTrees.ExcursionMarkovProof`, `BGW.Skorokhod.DLoc`, `BGW.StableTrees.ExcursionMarkovConsequences`, `BGW.StableTrees.ExcursionMarkovKernel` | `F` is a function of the natural prefix `r_t e` (spec: `F_t`-measurable); the kernel is the law of `y+X` killed at first passage below `−y` |
| C23.d | integrated form with `G` of the hitting time `ζ=t+T_0∘θ_t` | DELIVERED (exact) | `BGW.StableTrees.excursion_remainingLifetime_lintegral` (`passageLaw θ (e(t))`) | `BGW.StableTrees.ExcursionMarkovConsequences` |  |

### C24

Proposition 5.3 ($\Gamma_a$ identity).

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C24.main | `E[F(r_aX^exc,r_aH^exc)]=E[F(r_aX̃,r_aH̃)Γ_a(X̃_a)]`, `F` bounded measurable on `D_a×C_a` | DELIVERED (exact) | `BGW.StableTrees.gamma_identity` (signed bounded tests, with both integrability conclusions), `BGW.StableTrees.lintegral_gamma_identity` (nonneg. tests) | `BGW.StableTrees.JointExcursion` | LHS `excLaw θ`, RHS `tailExcLaw θ 1`; `0<a<1`. Spec sketch `gamma_identity (ha) (F) (hF) (hFb)` matches in content |
| C24.path | X-only form (path tests) | DELIVERED (exact) | `BGW.StableTrees.gamma_identity_path`, `BGW.StableTrees.lintegral_gamma_identity_path`, `BGW.StableTrees.levyExcLaw_prefix_eq_withDensity_tail` | `BGW.StableTrees.GammaIdentity` | the spec reduction "H on [0,a] is a functional of X on [0,a]" is realized by `BGW.StableTrees.heightPrefixAE` (`BGW.StableTrees.ae_heightPrefixAE_eq_heightPrefix`, `BGW.StableTrees.ae_heightPrefixAE_excursionRestrict`, `BGW.StableTrees.map_restrictPair_excLaw`) |
| C24.pos | `X_a>0` `N(·\|ζ>1)`-a.s. so `Γ_a(X_a)` defined | DELIVERED (exact) | `BGW.StableTrees.ae_evalEnd_pos_tailPrefix` (`BGW.StableTrees.evalEnd`) | `BGW.StableTrees.GammaIdentity` |  |
| C24.F=1 | `N(Γ_a(X_a)\|ζ>1)=1` | DELIVERED (exact) | `BGW.StableTrees.integral_gammaA_tail_eq_one` | `BGW.StableTrees.GammaIdentity` | also integrable |
| C24.steps | steps 1–5 (Kendall + Itô + continuity in u), size tail | DELIVERED (exact) | `BGW.StableTrees.excursionTail_size_tail`, `BGW.StableTrees.gammaA_mul_sizeTail`, `BGW.StableTrees.lintegral_unitPrefix_eq`, `BGW.StableTrees.levyExcLaw_prefix_density`, `BGW.StableTrees.exists_goodTimes_unit`, `BGW.StableTrees.excursionTail_density_continuousAt_one` | `BGW.StableTrees.GammaIdentity`, `BGW.StableTrees.KendallAdapter`, `BGW.StableTrees.UnitExcursionDensity`, `BGW.StableTrees.UnitExcursionDensityGoodTimes`, `BGW.StableTrees.UnitExcursionDensityTailContinuity` | proof route, not subclaims |

### C25

Chaumont's path construction of $X^{\mathrm{exc}}$ (optional).

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C25.X | `(ζ_1^{−1/θ}(X_{g_1+ζ_1 s}−X_{g_1}))` has the law of `X^exc` | DELIVERED (exact) | `BGW.StableTrees.straddlingExcursion`, `BGW.StableTrees.straddleStart`, `BGW.StableTrees.straddleEnd`, `BGW.StableTrees.straddleLife`, `BGW.StableTrees.ae_straddleStart_eq_sSup`, `BGW.StableTrees.ae_straddleEnd_eq_sInf`, `BGW.StableTrees.map_straddling_restrict_eq_levyExcLaw`, `BGW.StableTrees.map_normalize_straddling_eq_unitExcursionLaw`, `BGW.StableTrees.straddleLaw`, `BGW.StableTrees.isProbabilityMeasure_straddleLaw`, `BGW.StableTrees.indepFun_straddle_age_shape` | `BGW.StableTrees.StraddlingExcursionBasic`, `BGW.StableTrees.ExcursionGaps`, `BGW.StableTrees.StraddlingExcursionLaw` | For every `t > 0` (`t = 1` included). The endpoints are defined as the passage times `T_{L_t−}`, `T_{L_t}`; a.s. they equal `sup{s ≤ t : X_s = I_s}` and `inf{s > t : X_s = I_s}` (`BGW.StableTrees.ae_straddleStart_eq_sSup`, `BGW.StableTrees.ae_straddleEnd_eq_sInf`, commit `e1dcb5c`), the spec description. |
| C25.H | `H^exc=(ζ_1^{1/θ−1}H_{g_1+ζ_1 s})`, jointly with path | DELIVERED (equivalent/stronger form) | `BGW.StableTrees.straddleHeightPath`, `BGW.StableTrees.ae_heightLoc_straddling`, `BGW.StableTrees.ae_heightLoc_straddle_endpoints`, `BGW.StableTrees.map_straddleHeight_eq_excLaw`, `BGW.StableTrees.map_straddleHeightData_eq_prod` | `BGW.StableTrees.StraddlingHeight` | joint law with age/lifetime independent |

### C26

Height process $H$, continuity, $H^{\mathrm{exc}}$.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C26.H1-P | `H_t=lim ε^{−1}∫1{X_s<I^s_t+ε}ds` in P-probability (θ∈(1,2)) | DELIVERED (exact) | `BGW.StableTrees.heightApprox` (def), `BGW.StableTrees.height` (def, via reversal + `BGW.StableTrees.supLocalTime`), `BGW.StableTrees.heightApprox_tendstoInMeasure` (`𝓝[>] 0`, all `t`), `BGW.StableTrees.ae_tendsto_heightApprox_supEps`, `BGW.StableTrees.ae_heightRaw_eq` | `BGW.StableTrees.HeightProcessBasic`, `BGW.StableTrees.SupremumLocalTimeIdentBasic`, `BGW.StableTrees.HeightProcessIdentification` | full `ε↓0` limit in measure, plus a.s. along `BGW.StableTrees.supEps`; holds for `1<θ≤2` |
| C26.H1-N | same in N-measure on `{t<ζ}` | DELIVERED (exact) | `BGW.StableTrees.heightApprox_tendstoInMeasure_excursionHeight` (limit `excursionHeight θ e t`), `BGW.StableTrees.exists_heightApprox_tendstoInMeasure_excursion`, `BGW.StableTrees.exists_heightApprox_tendstoInMeasure_unit` | `BGW.StableTrees.ExcursionHeightIdentification`, `BGW.StableTrees.HeightBridgesExcursionLimit` |  |
| C26.H1-2 | θ=2: `H_t=X_t−I_t` | DELIVERED (exact) | `BGW.StableTrees.ae_height_two`, `BGW.StableTrees.ae_height_zero_iff`, `BGW.StableTrees.ae_heightLoc_two` | `BGW.StableTrees.HeightProcessTwo`, `BGW.StableTrees.HeightProcessConcentration`, `BGW.StableTrees.BrownianHeight` |  |
| C26.H2-P | continuous modification under P | DELIVERED (exact) | `BGW.StableTrees.heightLoc` (def, `BGW.StableTrees.continuous_heightLoc`, everywhere), `BGW.StableTrees.ae_exists_continuous_height`, `BGW.StableTrees.ae_heightLoc_eq_height` (modification), `BGW.StableTrees.ae_heightLoc_locallyHolder`, `BGW.StableTrees.height_increment_moment_bound` | `BGW.StableTrees.HeightContinuityBasic`, `BGW.StableTrees.HeightContinuityKolmogorov`, `BGW.StableTrees.HeightContinuityHolder`, `BGW.StableTrees.HeightContinuityMoments` | local Hölder of every order `<1−1/θ`; uses own Kolmogorov–Chentsov |
| C26.H2-N | continuous modification under N | DELIVERED (exact) | `BGW.StableTrees.excursionHeight` (def), `BGW.StableTrees.IsExcursionHeightVersion`, `BGW.StableTrees.ae_exists_isExcursionHeightVersion`, `BGW.StableTrees.ae_heightLoc_jumpExcursion`, `BGW.StableTrees.excursionHeight_nonneg` | `BGW.StableTrees.ExcursionHeightBasic`, `BGW.StableTrees.ExcursionHeightExcursionMeasure`, `BGW.StableTrees.ExcursionHeightLocality` | see correction (k): excursion height is reconstructed from the height at Lebesgue-a.e. age (`BGW.StableTrees.ae_heightLoc_eq_heightUniv_ae`) |
| C26.H3 | `(H_s)_{s≤t}` measurable functional of `(X_s)_{s≤t}` | DELIVERED (exact) | `BGW.StableTrees.measurable_height_prefix` (prefix σ-algebra `comap restrict`), `BGW.StableTrees.heightPrefix` (measurable: `BGW.StableTrees.measurable_heightPrefix`), `BGW.StableTrees.ae_heightPrefix_restrict_all`, `BGW.StableTrees.ae_heightPrefix_eval`, `BGW.StableTrees.map_heightPrefix_pair` | `BGW.StableTrees.HeightProcessBasic`, `BGW.StableTrees.HeightContinuityBasic`, `BGW.StableTrees.HeightContinuityMeasurable`, `BGW.StableTrees.HeightContinuity` | the a.s. identity `H=H(X)` as in spec pitfall; fixed-time version exact, path version a.s. on one event for all horizons |
| C26.H4 | joint scaling; H defined under `N(·\|ζ>t)` and `N(·\|ζ=1)` | DELIVERED (exact) | `BGW.StableTrees.ae_excursionHeight_scale`, `BGW.StableTrees.ae_excursionHeight_scale_unit`, `BGW.StableTrees.ae_excursionHeight_normalize`, `BGW.StableTrees.ae_prod_excursionHeight_scale`, `BGW.StableTrees.excursionPair`, `BGW.StableTrees.pairStretch` | `BGW.StableTrees.ExcursionHeightScaling`, `BGW.StableTrees.ExcursionHeightUnitScaling`, `BGW.StableTrees.ExcursionHeightNormalization`, `BGW.StableTrees.JointExcursion` | height scales by `c^{1−1/θ}` |
| C26.H5 | `H^exc` continuous, `H^exc_0=H^exc_1=0`, `>0` on `(0,1)` | DELIVERED (exact) | `BGW.StableTrees.excLaw_height_endpoints_pos` (second coordinate lies in `C(I,ℝ)` by construction), `BGW.StableTrees.ae_excursionHeight_pos`, `BGW.StableTrees.ae_excursionHeight_pos_unit`, `BGW.StableTrees.excursionHeight_zero`, `BGW.StableTrees.excursionHeight_eq_zero_of_lifetime_le` | `BGW.StableTrees.JointExcursion`, `BGW.StableTrees.ExcursionHeightPositivity`, `BGW.StableTrees.ExcursionHeightBasic` |  |
| C26.H6 | θ=2: `H^exc=X^exc=√2 e` | DELIVERED (exact) | `BGW.StableTrees.excLaw_height_eq_path_two`, `ae_excursionHeight_two(_unit)`, `BGW.StableTrees.BrownianIdentification.excLaw_two`, `BGW.StableTrees.BrownianIdentification.excLaw_two_map_diag`, `BGW.StableTrees.BrownianIdentification.excLaw_two_map_snd`, `BGW.StableTrees.BrownianIdentification.levyExcLaw_two` | `BGW.StableTrees.JointExcursion`, `BGW.StableTrees.BrownianPair`, `BGW.StableTrees.BrownianExcursion` |  |
| C26.d-law | existence of the law `BGW.StableTrees.excLaw` (and `BGW.StableTrees.tailExcLaw`) | DELIVERED (exact) | `BGW.StableTrees.excLaw`, `BGW.StableTrees.tailExcLaw`, `BGW.StableTrees.excLaw_map_fst`, `BGW.StableTrees.tailExcLaw_map_fst` | `BGW.StableTrees.JointExcursion` | marginals are the normalized/tail excursion laws |

### C27

Duquesne--Le Gall forest theorem (unconditioned joint $(W,H,C)$).

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C27.a1 | Forest `(V_{⌊nt⌋}/B_n, (B_n/n)H^f_{⌊nt⌋}, (B_n/n)C^f_{2nt}) ⇒ (X,H,H)` in `D_T×C_T×C_T`, every `T>0` | DELIVERED (exact; product-of-paths form) | `BGW.StableTrees.ForestTriple.tendsto_forestTripleLaw`; for any admissible norming `BGW.StableTrees.ForestTriple.tendsto_forestTripleLaw_of_attracted` (module `BGW.StableTrees.NonmonotoneNorming`) (laws `BGW.StableTrees.ForestTriple.forestTripleLaw`, `BGW.StableTrees.ForestTriple.forestTriplePath`, `BGW.StableTrees.ForestTriple.forestTripleLimit`) | `BGW.StableTrees.ForestTriple`, `BGW.StableTrees.NonmonotoneNorming` | The original export uses `StableDomain μ θ B`. The `_of_attracted` export covers arbitrary admissible normings under criticality and nondegeneracy. The law is over `offspringSeqLaw μ`, with linearly interpolated height and the padded contour (tree `r` occupies `[2Lr,2L(r+1)]`). |
| C27.a2 | Same as one path in `D_T(ℝ³)` (Cor. 2.5.1 form) | DELIVERED (exact) | `BGW.StableTrees.ForestTriple.tendsto_forestTripleVecLaw` (any admissible norming: `BGW.StableTrees.ForestTriple.tendsto_forestTripleVecLaw_of_attracted`), `BGW.StableTrees.ForestTriple.forestTripleVecLimit_eq`, `BGW.StableTrees.ForestTriple.continuous_tripleVec`, `BGW.Skorokhod.continuous_prodWithCont` | `BGW.StableTrees.ForestTripleVector`, `BGW.Skorokhod.ProductPaths` | K13b. Limit identified as image of `stableProcessLaw θ T` under `g ↦ (g, H g, H g)`. |
| C27.a3 | Identification of the limit with the stable process and its height in both C-coordinates | DELIVERED (exact) | `BGW.StableTrees.ForestTriple.forestTripleLimit_eq_map_stableProcessLaw`, `BGW.StableTrees.ForestTriple.forestTripleLaw_map_pair`, `BGW.StableTrees.ForestTriple.forestTripleVecLimit_eq` | `BGW.StableTrees.ForestTriple`, `BGW.StableTrees.ForestTripleVector` | `heightPrefix θ T` (H03) is the continuous height. |
| C27.d | Needed variant: `(V,H)` pair for every `T`; C not needed | DELIVERED (stronger) | `BGW.StableTrees.ForestTriple.tendsto_forestTripleLaw`, `BGW.StableTrees.ForestTriple.forestTripleLaw_map_pair` | `BGW.StableTrees.ForestTriple` | Pair marginal agrees with the sealed K11 forest pair law; C28 consumes the pair. |
| C27.g1 | DLG index theorems by space scale `p`; conversion to "all n with `B_n`" | BYPASSED | none (not an export) | — | Spec (g) pitfall, not a claim. Proof goes through the project's own walk/height limit (C17, C26) plus a Slutsky step (`BGW.StableTrees.ForestContour.dist_forestContourPath_forestHeightPath`), so no `p(n) ≈ B_n` conversion is needed. |
| C27.g2 | Step height `H_{⌊nt⌋}` (DLG) versus interpolated height (paper) are equivalent | BYPASSED | none | — | Only the interpolated form is exported (the paper's form). The step form is not needed by C28. |
| C27.opt | Unpadded contour clock (optional) | DELIVERED (equivalent, comparison only) | `BGW.StableTrees.ForestContour.forestContourUnpadded`, `BGW.StableTrees.ForestContour.unpadded_contour_error_tendstoInMeasure`, `BGW.StableTrees.ForestContour.ae_tendsto_unpaddedStart` | `BGW.StableTrees.UnpaddedContourClock`, `BGW.StableTrees.UnpaddedContour` | Convergence in measure of padded minus unpadded error; no joint-triple statement with the unpadded contour is exported. Not required by spec (a). |

### C28

Theorem 5.1 (trees with $\zeta\ge n$).

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C28.a1 | `(W_{⌊nt⌋}(τ_n)/B_n, (B_n/n)H_{nt}(τ_n)) ⇒ N(·∣ζ>1)` pair in `D_1×C_1`, `τ_n ~ P_μ(·∣ζ≥n)`, any admissible `B_n`, no aperiodicity | DELIVERED (stronger: every `T>0`) | `BGW.StableTrees.TailPair.tendsto_tailPairLaw`; for any admissible norming `BGW.StableTrees.TailPair.tendsto_tailPairLaw_of_attracted` (laws `BGW.StableTrees.TailPair.tailPairLaw`, `BGW.StableTrees.DiscreteForest.tailTreeLaw`, `BGW.StableTrees.TailPair.treePairPath`, `BGW.StableTrees.PathTail.treePrefixPath`, `BGW.StableTrees.TailPair.treeHeightPath`) | `BGW.StableTrees.TailPair`, `BGW.StableTrees.TailPairBasic`, `BGW.StableTrees.DiscreteForestTreeLaws`, `BGW.StableTrees.PathTailDefs` | Target `tailExcLaw θ T` = image of `N(·\|ζ>1)` under the pair map (`BGW.StableTrees.tailExcursionLaw`). `T = 1` is the horizon of (a) and (d). The original export assumes `StableDomain μ θ B` and `0<T`. The `_of_attracted` export in `BGW.StableTrees.NonmonotoneNorming` covers arbitrary admissible normings under criticality and nondegeneracy. |
| C28.a2 | "The same holds on any `[0,T]`" | DELIVERED (exact) | `BGW.StableTrees.TailPair.tendsto_tailPairLaw` | `BGW.StableTrees.TailPair` | Same theorem (explicit `T`). |
| C28.a3 | Equivalent form `⇒ tailExcLaw θ` | DELIVERED (exact) | `BGW.StableTrees.TailPair.tendsto_tailPairLaw`, `BGW.StableTrees.TailPair.tailPairLaw_map_fst` | `BGW.StableTrees.TailPair`, `BGW.StableTrees.TailPairBasic` | `tailExcLaw θ T` is exactly the limit of the theorem. |
| C28.pitfall | W and H extended by 0 after ζ (§1.6) | DELIVERED (equivalent) | `BGW.StableTrees.TailPair.treeHeightPath_eq_zero`, `BGW.StableTrees.TailPair.abs_extractedHeight_sub_le`, `BGW.StableTrees.TailPair.treeHeightPath_blockLF` | `BGW.StableTrees.TailPairBasic` | Height vanishes from time `ζ/n`, as in the paper. The walk path uses increments padded by 0 (`BGW.StableTrees.PathTail.treeIncrementSeq`, `getD i 0`), so it stays at `−1/B_n` after ζ, not at 0; the discrepancy is `≤ 1/B_n` (`BGW.StableTrees.PathTail.dist_treePrefixPath_closed_le`), vanishing in the limit. Wording difference only. |
| C28.d | Needed variant: on `[0,1]` | DELIVERED (exact) | `BGW.StableTrees.TailPair.tendsto_tailPairLaw` with `T = 1` | `BGW.StableTrees.TailPair` | Restrictions to `[0,a]`, `a<1`, follow by continuity of `restrict`. |
| C28.f | `CitedDLGTail` Option-A Prop | BYPASSED | none | — | Placeholder superseded by the proved theorem; no `CitedDLGTail` def exists in `BGW/` (rg on `CitedDLG` returns nothing). |
| C28.b | Derivation [D] from C27 by first long tree extraction | BYPASSED | `BGW.StableTrees.TailPair.map_offspringSeqLaw_firstLongTree`, `BGW.StableTrees.TailPair.map_firstLongMark_excursionPair`, `BGW.StableTrees.TailPair.ae_excursionHeight_firstLongMark` | `BGW.StableTrees.TailPairBasic` | Proof route (a coupling along the whole sequence with the first long block; no Skorokhod representation). Proof-route remark, not a separate claim. |

### C29

Theorem 4.1 (Duquesne, trees with $\zeta=n$).

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C29.a1 | Contour alone: `(B_n/n)C_{2nt}(τ_n) ⇒ H^exc` in `C([0,1])`, `τ_n ~ P_μ(·∣ζ=n)` | DELIVERED (exact) | `BGW.StableTrees.ExactContour.tendsto_exactContourLaw`; for arbitrary admissible norming, take the second marginal of `BGW.StableTrees.ExactContour.tendsto_exactHeightContourLaw_of_attracted` | `BGW.StableTrees.ExactContourConvergence`, `BGW.StableTrees.NonmonotoneNorming` | The named contour theorem assumes `StableDomain μ θ B` and convergence along admissible sizes. Its target is `(excLaw θ).map Prod.snd`, the law of the excursion height. |
| C29.a2 | Joint `((B_n/n)H_{nt}, (B_n/n)C_{2nt}) ⇒ (H^exc,H^exc)` | DELIVERED (exact; both contour clocks) | `BGW.StableTrees.ExactContour.tendsto_exactHeightContourLaw` (paper clock `2nt`; any admissible norming: `BGW.StableTrees.ExactContour.tendsto_exactHeightContourLaw_of_attracted`, `BGW.StableTrees.ExactContour.tendsto_exactHeightLibContourLaw_of_attracted`), `BGW.StableTrees.ExactContour.tendsto_exactHeightLibContourLaw` (library clock `2(n−1)t`); limit `(excLaw θ).map (fun p => (p.2,p.2))` | `BGW.StableTrees.ExactContourJoint` | Statement is along an unbounded sequence `q` of admissible sizes (`Admissible μ (q k)`: `P(ζ=q k) ≠ 0`), `StableDomain μ θ B`. |
| C29.a3 | Aperiodicity = `(H_θ)(iii)`; periodic μ works along `n ≡ 1 (mod span)` ("not needed") | DELIVERED (stronger) | `BGW.StableTrees.ExactContour.tendsto_exactHeightContourLaw`, `BGW.StableTrees.Admissible`, `BGW.StableTrees.Attraction.sizeProb_pos_iff` | `BGW.StableTrees.ExactContourJoint`, `BGW.StableTrees.ForestLocalLimitDefs`, `BGW.StableTrees.Attraction.Defs` | No aperiodicity hypothesis; admissible-size subsequences cover periodic μ. For aperiodic μ all large `n` are admissible, so the "for n large" form follows with `q = id` shifted. |
| C29.d | Needed variant: contour statement only | DELIVERED (exact) | `BGW.StableTrees.ExactContour.tendsto_exactContourLaw` | `BGW.StableTrees.ExactContourConvergence` | See C29.a1 for arbitrary admissible norming. |
| C29.f | `CitedDuquesne` Prop | BYPASSED | none | — | No such def in `BGW/`; the theorem itself is proved (route R-A style, through K14/K15/K16, no cited black box). |
| C29.g | Pitfall: printed norming of 1.10 must not be used | DELIVERED (by construction) | `BGW.StableTrees.StableDomain` | `BGW.StableTrees.Defs` | Theorems are quantified over admissible `B` (`BGW.StableTrees.StableDomain`), not the printed norming. |

### C30

$\theta=2$: $H^{\mathrm{exc}}=X^{\mathrm{exc}}=\sqrt2 e$; Aldous's normalization.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C30.a1 | `X^exc = √2 e` (θ = 2) | DELIVERED (exact) | `BGW.StableTrees.BrownianIdentification.levyExcLaw_two` | `BGW.StableTrees.BrownianExcursion` | `levyExcLaw 2 = law.map (fun e => ofContinuous (√2 • e))`, `law = VervaatBridge.law`. K18b. |
| C30.a2 | `H^exc = √2 e` (height marginal) and the pair `(X^exc,H^exc) = (√2e,√2e)` | DELIVERED (exact) | `BGW.StableTrees.BrownianIdentification.excLaw_two_map_snd`, `BGW.StableTrees.BrownianIdentification.excLaw_two`, `BGW.StableTrees.BrownianIdentification.excLaw_two_map_diag`, `BGW.StableTrees.BrownianIdentification.measurable_sqrtTwoPair` | `BGW.StableTrees.BrownianPair` | K18c. |
| C30.a3 | Theorem 4.5 becomes `(σ/(2√ζ))C_{2ζt}(τ_n) ⇒ e` with `B_n = σ√(n/2)` | DELIVERED (equivalent: fixed-size form) for the fixed-size statement; ARTICLE-SIDE for the leaf-conditioned random-ζ statement | `BGW.StableTrees.ExactContour.tendsto_exactHeightContour_finiteVariance_stable`, `BGW.StableTrees.ExactContour.tendsto_exactHeightContour_finiteVariance`, `BGW.StableTrees.ExactContour.tendsto_exactContour_finiteVariance`, `BGW.StableTrees.ExactContour.finiteVarianceNorming_eq`, `BGW.StableTrees.ExactContour.finiteVarianceNorming_div`, `BGW.StableTrees.ExactContour.treeContourPath_finiteVariance_paper`, `BGW.StableTrees.ExactContour.heightContourPath_const_mul` | `BGW.StableTrees.FiniteVarianceContour` | Exact-size trees, amplitude `σ/(2√n)`, along admissible sizes; limit `BGW.ContinuumTrees.VervaatBridge.law`. Aldous's theorem is the fixed-size case. The leaf-conditioned analogue (random ζ, Remark 4.6) needs the article's Theorem 4.5 layer; BGW supplies the deterministic identity `σ/(2√z)` for every tree size `z` and the random-size adapters (C38). |
| C30.i | Characterization (i): Itô measure of `B` conditioned on unit length | DELIVERED (equivalent) | `BGW.StableTrees.levyExcLaw` (`BGW.StableTrees.unitExcursionLaw`), `BGW.StableTrees.BrownianIdentification.levyExcLaw_two` | `BGW.StableTrees.UnitExcursionLawBasic`, `BGW.StableTrees.BrownianExcursion` | The library's normalized excursion law at θ = 2, identified with (ii) up to the factor `√2`. There is no separate "Itô measure of standard BM" object; (i) = (ii) is exactly `BGW.StableTrees.BrownianIdentification.levyExcLaw_two`. |
| C30.ii | Characterization (ii): Vervaat transform of the Brownian bridge (`BGW.ContinuumTrees.VervaatBridge.law`) | DELIVERED (exact) | `BGW.ContinuumTrees.VervaatBridge.law`, `BGW.StableTrees.BrownianIdentification.stableBridgeLaw_two`, `BGW.StableTrees.BrownianIdentification.vervaat_smul` | `BGW.ContinuumTrees.VervaatBridge`, `BGW.StableTrees.BrownianIdentification`, `BGW.StableTrees.BrownianExcursion` | `e` of the C30 statements is defined this way. |
| C30.iii | Characterization (iii): Bessel(3) bridge | BYPASSED | none | — | Roadmap CT10: named alternative excursion characterizations are proof-route choices unless an equivalence is itself claimed by the selected export; none of the exports claims it. Spec (d) asks only for `H^exc = √2e` with `e` as in (ii) "plus (i) = (ii) if one wants". |
| C30.(i)=(ii) | Identification (i) = (ii) (C35 at θ = 2) | DELIVERED (exact) | `BGW.StableTrees.BrownianIdentification.levyExcLaw_two`, `BGW.StableTrees.VervaatIto.map_vervaatD_stableBridgeLaw`, `BGW.StableTrees.BrownianIdentification.stableBridgeLaw_two` | `BGW.StableTrees.BrownianExcursion`, `BGW.StableTrees.VervaatIto`, `BGW.StableTrees.BrownianIdentification` | Via C35 route; see C35. |
| C30.pitfall | Aldous's CRT is coded by `2e`; θ=2 tree limit is `T_{√2e}` = `1/√2` times `T_{2e}` | DELIVERED (exact) | `BGW.StableTrees.BrownianIdentification.rootedMeasuredGHSpace_sqrt_two_smul`, `BGW.StableTrees.BrownianIdentification.stableTreeLaw_two` | `BGW.StableTrees.FiniteVarianceContour` | Statement: `(excLaw 2).map (rootedMeasuredGHSpace ∘ snd) = treeLaw.map (scale (1/√2))`. |

### C31

Stable bridge $X^{\mathrm{br}}$ on $D([0,1])$.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C31.a(i) | Prefix identity `E^br[F(X restricted to [0,a])] = E^X[F · p_{1−a}(−X_a)/p_1(0)]`, bounded Borel `F` on `D_a` | DELIVERED (equivalent: measure/integral form) | `BGW.StableTrees.map_restrict_stableBridgeLaw`, `BGW.StableTrees.integral_restrict_stableBridgeLaw`, `BGW.StableTrees.bridgePrefixLaw`, `BGW.StableTrees.bridgePrefixWeight` | `BGW.StableTrees.BridgeProjective`, `BGW.StableTrees.StableBridgeClosed`, `BGW.StableTrees.BridgePrefix` | Weight is `stableDensityAt θ (1−a) (−f a) / Scalar.stableDensity θ 0`, matching the spec's `pDens … / Scalar.stableDensity θ 0`. Stated for `0<a<1`, `hθ`. The spec's `theorem stableBridgeLaw_prefix` has no exact name; two equivalent exports instead. |
| C31.a(i)-mart | Consistency across `a` ("`M_a` a mean-one P-martingale") | DELIVERED (equivalent: consistency and mass one) | `BGW.StableTrees.bridgePrefix_mass_one`, `BGW.StableTrees.bridgePrefix_consistent`, `BGW.StableTrees.bridgePrefix_family`, `BGW.StableTrees.integral_bridgePrefixWeight_stableProcessLaw`, `BGW.StableTrees.bridgePrefixLaw_unique` | `BGW.StableTrees.BridgePrefix`, `BGW.StableTrees.StableBridgeClosed` | The martingale property is exported in its equivalent consistent-family form, not as a named `Martingale` statement. Spec presents it as the reason, not as a subclaim. |
| C31.a(ii) | `P^br(X_1 = 0 ∧ X_{1−} = 0) = 1` | DELIVERED (stronger) | `BGW.StableTrees.stableBridgeLaw_endpoints` | `BGW.StableTrees.BridgeProjective` | A.s. `X_0 = 0 ∧ X_1 = 0 ∧ leftLim X 1 = 0`. Also `BGW.StableTrees.bridgeOpen_ae_terminal_limit`, `BGW.StableTrees.bridgeOpenLaw_ae_terminal_limit`. |
| C31.a(iii) | Time reversal `(−X_{(1−t)−})` has law `P^br` (with `X_{0−} := X_0`) | DELIVERED (exact) | `BGW.StableTrees.map_reverseBridge_stableBridgeLaw`, `BGW.Skorokhod.reverseBridge`, `BGW.Skorokhod.reverseBridgeFun`, `BGW.Skorokhod.reverseBridge_eq_reverseIncrements`, `BGW.Skorokhod.measurable_reverseBridge`, `BGW.StableTrees.ae_reverseBridge_reverseBridge`, `BGW.StableTrees.ae_endpoints_reverseBridge` | `BGW.StableTrees.StableBridgeClosed`, `BGW.Skorokhod.ReverseBridge` | `reverseBridgeFun f s = −leftLim f (1−s)`. |
| C31.a(iv) | No fixed discontinuities | DELIVERED (exact) | `BGW.StableTrees.stableBridgeLaw_ae_continuousAt`, `BGW.StableTrees.stableBridgeLaw_ae_leftLim_eq` | `BGW.StableTrees.StableBridgeClosed` | For each fixed `t ∈ [0,1]` (including 0 and 1); not simultaneous in `t`, as the spec's statement. |
| C31.uniq | Uniqueness from (i), (ii) and C12(b) | DELIVERED (exact) | `BGW.StableTrees.stableBridgeLaw_unique`, `BGW.StableTrees.stableBridgeLaw_unique_of_endpoints`, `BGW.StableTrees.eq_stableBridgeLaw_iff` | `BGW.StableTrees.StableBridgeClosed` | Hypothesis: prefix laws for all `a<1` and `f 1 = leftLim f 1` a.s. (minimal form), or pinned form. |
| C31.N6 | (i) alone does not determine a law on `D_1` | DELIVERED (exact) | `BGW.StableTrees.exists_ne_stableBridgeLaw_same_prefixes` | `BGW.StableTrees.StableBridgeClosed` | Explicit counterexample law (terminal value overwritten). |
| C31.exist | Existence of the bridge law on `D_1(ℝ)` (projective limit, left limit at 1) | DELIVERED (exact) | `BGW.StableTrees.stableBridgeLaw`, `BGW.StableTrees.closeBridge`, `BGW.StableTrees.bridgeOpenLaw`, `BGW.StableTrees.exists_unique_bridgeOpenLaw`, `BGW.StableTrees.bridgePrefixProb_compatible`, `BGW.StableTrees.measurable_closeBridge` | `BGW.StableTrees.BridgeProjectiveClose`, `BGW.StableTrees.BridgeProjectiveOpen` | "Direct" route of the spec. Junk value (Dirac at zero path) outside `hθ`; every theorem takes `hθ`. |
| C31.d | Needed: (i) and (ii); (iii) as tool for C32 | DELIVERED (exact) | see above rows | — |  |
| C31.limit | Alternative: bridge as a weak limit of walk bridges (Liggett / paper 6.1) | DELIVERED (equivalent, optional) | `BGW.StableTrees.VervaatIto.tendsto_walkBridgeLaw` | `BGW.StableTrees.VervaatIto` | Not required by spec (d). |
| C31.θ2 | θ = 2 identification (extra) | DELIVERED (exact; extra) | `BGW.StableTrees.BrownianIdentification.stableBridgeLaw_two`, `BGW.StableTrees.BrownianIdentification.stableDensity_two`, `BGW.StableTrees.BrownianIdentification.bridgePrefixWeight_two` | `BGW.StableTrees.BrownianIdentification` | `stableBridgeLaw 2 = bridgeD √2`. |

### C32

Unique minimum of $X^{\mathrm{br}}$, attained continuously.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C32.a1 | `inf X < 0` a.s. | DELIVERED (exact) | `BGW.StableTrees.stableBridgeLaw_ae_iInf_neg` | `BGW.StableTrees.StableBridgeMinimum` |  |
| C32.a2 | Unique `g ∈ [0,1]` with `min(X_{g−},X_g) = inf X`, and `g ∈ (0,1)` | DELIVERED (exact) | `BGW.StableTrees.stableBridgeLaw_ae_minimum`, `BGW.StableTrees.stableBridgeLaw_ae_existsUnique_continuous_minimizer`, `BGW.Skorokhod.vervaatTime`, `BGW.Skorokhod.min_leftLim_vervaatTime` | `BGW.StableTrees.StableBridgeMinimum`, `BGW.Skorokhod.Vervaat` | Uniqueness stated as `∀ t, min(leftLim f t, f t) = ⨅ f → t = vervaatTime f`, `0 < vervaatTime f < 1`. `leftLim` at 0 equals `f 0` by the subtype convention (`X_{0−} := X_0`). |
| C32.a3 | `X` continuous at `g` | DELIVERED (exact) | same `BGW.StableTrees.stableBridgeLaw_ae_minimum` (clause `ContinuousAt f (vervaatTime f)`) | `BGW.StableTrees.StableBridgeMinimum` | N5 pitfall handled. |
| C32.a4 | `g` uniform on `(0,1)` ("not needed") | DELIVERED (exact; CT10) | `BGW.StableTrees.map_vervaatTime_stableBridgeLaw`, `BGW.StableTrees.stableBridgeLaw_vervaatTime_le`, `BGW.StableTrees.bridge_gridIncr_cyclic` | `BGW.StableTrees.StableBridgeUniformMinimum`, `BGW.StableTrees.StableBridgeUniformMinimumGrid` | Uniform on `[0,1]` (same law as on `(0,1)`). |
| C32.[D] | Proof plan: prefixes `a'_k ↑ 1`, F6, F2 | BYPASSED | `BGW.StableTrees.stableBridgeLaw_ae_prefix_unique_continuous_minimum` (used) | `BGW.StableTrees.StableBridgeMinimum` | Proof route; the plan is followed (prefix lemma, transfer via absolute continuity). Not a separate claim. |

### C33

Càdlàg Vervaat map $V$ and its discrete correspondence.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C33.def | Definition of `g_1` and `V` (formulas, with `ω(0−):=ω(0)`, `−ω(0)` correction on wrap) | DELIVERED (exact) | `BGW.Skorokhod.vervaatTime`, `BGW.Skorokhod.vervaatD`, `BGW.Skorokhod.exists_min_leftLim`, `BGW.Skorokhod.min_leftLim_vervaatTime`, `BGW.Skorokhod.vervaatTime_le` | `BGW.Skorokhod.Vervaat`, `BGW.Skorokhod.VervaatRotate` | `vervaatD f t = f(g+t) − m` if `g+t ≤ 1`, else `f(g+t−1) + f 1 − m − f 0`. `g_1` is the first attainment time (`BGW.Skorokhod.vervaatTime_le`). |
| C33.1 | `V(ω) ∈ D_1(ℝ)` | DELIVERED (exact) | `BGW.Skorokhod.vervaatD` (structure field `isCadlag'`; proved by the private helper `isCadlag_rotate`) | `BGW.Skorokhod.VervaatRotate` | By the type `D 1 ℝ`. |
| C33.2 | `V(ω)(0) = ω(g_1) − m`, zero iff infimum attained as a value at `g_1` | DELIVERED (by definition; named lemma only for the continuity case) | `BGW.Skorokhod.vervaatD`, `BGW.Skorokhod.vervaatD_zero_of_continuousAt` | `BGW.Skorokhod.VervaatRotate`, `BGW.Skorokhod.VervaatContinuity` | No named lemma for the iff in general; the formula is `rfl`-level. The needed case ("continuous at g gives 0") is exported. |
| C33.3a | If ω continuous at `g_1`: `V(ω)(1) = V(ω)(1−) = ω(1) − ω(0)` | CORRECTED (premise `0 < g_1` added; see correction (d) in the report) | `BGW.Skorokhod.vervaatD_one_of_continuousAt` | `BGW.Skorokhod.VervaatContinuity` | Statement: `0 < vervaatTime f` and `ContinuousAt f g` give `vervaatD f 1 = f 1 − f 0` and `ContinuousAt (vervaatD f) 1`. Counterexample in the docstring (`f t = t`, `f 1 = 2`). |
| C33.3b | The only jump of `V(ω)` not coming from a jump of `ω` is at `1 − g_1`, of size `ω(1) − ω(1−)` | DELIVERED (exact) | `BGW.Skorokhod.vervaatD_wrap`, `BGW.Skorokhod.leftLim_vervaatD_wrap`, `BGW.Skorokhod.vervaatD_wrap_sub_leftLim`, `BGW.Skorokhod.vervaatD_jump_of_ne_wrap` (with `BGW.Skorokhod.vervaatWrapTime`) | `BGW.Skorokhod.OptionalGaps` | `vervaatWrapTime f = 1 − g_1`; the signed jump of `vervaatD f` at the wrap time equals `f 1 − leftLim f 1` (premise `0 < 1 − g_1`), and away from the wrap time (`t > 0`) the jump of `vervaatD f` at `t` is the jump of `f` at the rotated time `g_1 + t` modulo 1. The special case `BGW.Skorokhod.continuousAt_vervaatD_wrap` remains. Commit `e7d9564`. |
| C33.4 | `V` is Borel (or a.e. measurable) | DELIVERED (exact; stronger than a.e.) | `BGW.Skorokhod.measurable_vervaatD`, `BGW.Skorokhod.vervaatTime_le_iff_prefix_inf` | `BGW.Skorokhod.VervaatMeasurable` | Borel, via C4 route. |
| C33.5 | Discrete correspondence `V(ω_x) = ω_{𝐕(x)}`, `g_1(ω_x) = i_*/k`, assumption `min_{1≤j≤k} w_j < 0` | DELIVERED (exact) | `BGW.Skorokhod.vervaatD_stepPath`, `BGW.Skorokhod.vervaatTime_stepPath`, `BGW.Skorokhod.stepPath`, `BGW.Skorokhod.vervaatIndex`, `BGW.Skorokhod.isTreeExcursion_rotate_vervaatIndex` | `BGW.Skorokhod.VervaatStep` | Hypothesis `∃ j, 1 ≤ j ≤ length ∧ (take j).sum < 0`. Conclusion: `vervaatD (stepPath x B) = stepPath (x.rotate (vervaatIndex x)) B`. `BGW.Skorokhod.vervaatIndex` is the first `i ∈ [1,k]` minimizing the partial sum (Def. 6.3). The spec's `BGWLeaves.vervaat (Vervaat/Defs.lean)` is in the article companion: identifying `x.rotate (vervaatIndex x)` with the article's `vervaat` is ARTICLE-SIDE glue (BGW has the rotation form). |
| C33.cont | Comparison with continuous loops (extra) | DELIVERED (extra) | `BGW.Skorokhod.vervaatD_ofContinuous`, `BGW.Skorokhod.vervaatTime_ofContinuous` | `BGW.Skorokhod.VervaatComparison` | `vervaatD (ofContinuous g) = ofContinuous (Vervaat.vervaat ⟨g,_⟩)`. |

### C34

Continuity of $V$ at bridge-like paths.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C34.a1 | Continuity of `V` at `f` with `f(0)=0`, continuous at 1, unique interior continuous minimizer | DELIVERED (exact) | `BGW.Skorokhod.continuousAt_vervaatD`, `BGW.Skorokhod.continuousAt_vervaatTime` | `BGW.Skorokhod.VervaatContinuity`, `BGW.Skorokhod.VervaatMinimumContinuity` | Uniqueness encoded as `∀ t, min(leftLim f t, f t) = ⨅ → t = vervaatTime f`, with `0 < g < 1` and `ContinuousAt f g`. Time-change route of the sketch (`BGW.Skorokhod.exists_vervaat_timeChange_bound`, `BGW.Skorokhod.exists_aligned_timeChange`, `BGW.Skorokhod.exists_rotated_timeChange`, `BGW.Skorokhod.exists_local_timeChange`). |
| C34.a2 | `V(f)` continuous at `1 − g` and `V(f)(0) = 0` | DELIVERED (exact) | `BGW.Skorokhod.continuousAt_vervaatD` (conclusion conjuncts 2 and 3), `BGW.Skorokhod.continuousAt_vervaatD_wrap`, `BGW.Skorokhod.vervaatD_zero_of_continuousAt` | `BGW.Skorokhod.VervaatContinuity` |  |
| C34.a3 | If `f(1) = 0` then `V(f)(1) = V(f)(1−) = 0` | DELIVERED (equivalent: composition) | `BGW.Skorokhod.vervaatD_one_of_continuousAt` (with `f 0 = 0`, `f 1 = 0`), `BGW.StableTrees.stableBridgeLaw_ae_vervaat_endpoints` | `BGW.Skorokhod.VervaatContinuity`, `BGW.StableTrees.StableBridgeMinimum` | Not a named export for general `f`; obtained from `BGW.Skorokhod.vervaatD_one_of_continuousAt` (value `f 1 − f 0 = 0`, continuity at 1). For the bridge it is exported a.s. |
| C34.cor | `∀ᵐ f ∂stableBridgeLaw θ, ContinuousAt vervaatD f` | DELIVERED (exact) | `BGW.StableTrees.stableBridgeLaw_ae_continuousAt_vervaatD`, `BGW.StableTrees.stableBridgeLaw_ae_vervaat_endpoints`, `BGW.StableTrees.stableBridgeLaw_ae_vervaatD_pos` | `BGW.StableTrees.StableBridgeMinimum` | Also strict positivity of the Vervaat image on `(0,1)`. |
| C34.[D] | Necessity of the hypotheses (N5) | BYPASSED | none | — | Spec says "necessary in general" as a remark; not a claim for the library. |

### C35

$V(X^{\mathrm{br}})=X^{\mathrm{exc}}$ in law (Chaumont).

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C35.a | Under `P^br`, `V(X)` has the law `N(·∣ζ=1)` (law of `X^exc`) | DELIVERED (exact; direct route, not R-B) | `BGW.StableTrees.VervaatIto.map_vervaatD_stableBridgeLaw`, `BGW.StableTrees.VervaatIto.vervaatImage_eq_levyExcLaw`, `BGW.StableTrees.VervaatIto.tendsto_exactWalkLaw_vervaatImage`, `BGW.StableTrees.VervaatIto.restrictLaw_vervaatImage_eq_unitPrefix`, `BGW.StableTrees.VervaatIto.ae_vervaatImage_terminal_zero`, `BGW.StableTrees.VervaatIto.eq_of_restrict_eq_of_terminal_zero`, `BGW.StableTrees.VervaatIto.exists_discreteWitness` | `BGW.StableTrees.VervaatIto` | Statement: `(stableBridgeLaw θ).map vervaatD = levyExcLaw θ`, for `hθ`. `levyExcLaw θ` is `unitExcursionLaw θ` restricted to `[0,1]`, where `unitExcursionMeasure θ` is the normalized scaled tail restriction (docstring: "not a conditioning on `{ζ = 1}`"); that this equals `N(·\|ζ=1)` is by the library definition of the unit excursion. The proof imports only `BGW.StableTrees.DiscreteBridge`, `BGW.StableTrees.ExactPrefix`, `BGW.StableTrees.UnitExcursionLaw`, `BGW.StableTrees.StableBridgeMinimum`, so it does not use C28 or C29. |
| C35.d | R-B alternative (define `X^exc := V(X^br)`) | BYPASSED | `BGW.StableTrees.VervaatIto.vervaatImage_eq_levyExcLaw` | `BGW.StableTrees.VervaatIto` | Not needed: C35 is delivered directly (by the offspring witness), so the identity of §5.1 with `V(X^br)` is an export. |

### C36

Largest-jump functional $\bar\Delta$.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C36.a1 | `Δ̄(f) = sup_t (f t − f(t−)) ∨ 0` | DELIVERED (exact) | `BGW.Skorokhod.maxJump` | `BGW.Skorokhod.Jump` | `⨆ t, max (f t − leftLim f t) 0`; `t = 0` contributes 0 (`leftLim f 0 = f 0`). |
| C36.a2 | `∣Δ̄(f) − Δ̄(g)∣ ≤ 2 d_T(f,g)` | DELIVERED (exact) | `BGW.Skorokhod.lipschitzWith_two_maxJump`, `BGW.Skorokhod.bddAbove_maxJump` | `BGW.Skorokhod.Jump` | `LipschitzWith 2 (maxJump (T := T))` for every `T` (spec asks `T = 1`; stronger). |
| C36.a3 | Same bound for the largest absolute jump | DELIVERED (exact) | `BGW.Skorokhod.maxAbsJump`, `BGW.Skorokhod.lipschitzWith_two_maxAbsJump`, `BGW.Skorokhod.bddAbove_absJump` | `BGW.Skorokhod.Jump` |  |
| C36.a4 | `Δ̄` attained; `Δ̄ = 0` for continuous `f` | DELIVERED (exact) | `BGW.Skorokhod.exists_eq_maxJump`, `BGW.Skorokhod.maxJump_eq_zero_of_continuous`, `BGW.Skorokhod.maxJump_eq_zero_iff`, `BGW.Skorokhod.maxJump_eq_zero_iff_continuous_of_leftLim_le` | `BGW.Skorokhod.OptionalGaps` | Attainment for `0 ≤ T`; `maxJump = 0` for continuous `f`; `maxJump f = 0 ↔ ∀ t, f t ≤ leftLim f t`. `BGW.Skorokhod.maxJump` sees upward jumps only, so `maxJump f = 0 ↔ Continuous f` holds for paths without downward jumps (`BGW.Skorokhod.maxJump_eq_zero_iff_continuous_of_leftLim_le`), as for `X` spectrally positive. Commit `e7d9564`. |
| C36.N14 | `Δ̄(W(τ)) = Δ(τ) − 1` (fails for the one-vertex tree), `λ = n ≥ 2` | ARTICLE-SIDE | none | — | Involves the article's `Δ(τ)` and `W(τ)`; BGW has no tree-degree link. Roadmap C36 is only the functional. |
| C36.c | Use: Δ̄ is continuous on `D([0,1],ℝ)`; limit 0 when `X^exc` continuous | DELIVERED (exact) | `BGW.Skorokhod.lipschitzWith_two_maxJump`, `BGW.StableTrees.ae_maxJump_eq_zero_levyExcLaw_two`, `BGW.StableTrees.ae_maxJump_pos_levyExcLaw`, `BGW.StableTrees.ae_maxJump_pos_iff_levyExcLaw` | `BGW.Skorokhod.Jump`, `BGW.StableTrees.ExcursionJump` | CT10 C22(E3) provides the dichotomy of the limit's largest jump. |

### C37

Real tree coded by $g\in C$; GH and GHP Lipschitz bounds.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C37.a1 | `T_g` compact real tree, rooted at class of 0, mass = image of Lebesgue | DELIVERED (exact; pre-existing) | `BGW.ContinuumTrees.Coding.isRealTree`, `BGW.ContinuumTrees.Coding.fourPoint`, `BGW.ContinuumTrees.Coding.hasMidpoints`, `BGW.ContinuumTrees.Coding.root`, `BGW.ContinuumTrees.Coding.mass`, `BGW.ContinuumTrees.Coding.rootedCompactMeasuredSpace` | `BGW.ContinuumTrees.CodingRealTree`, `BGW.ContinuumTrees.CodingMeasure` | The specification records BGW as already having it; the compactness instance was not re-audited. |
| C37.a2 | `g ↦ T_g` Lipschitz for rooted measured GHP, constant 6 | DELIVERED (exact; pre-existing) | `BGW.ContinuumTrees.Coding.lipschitzWith_rootedMeasuredGHSpace` (`LipschitzWith 6 rootedMeasuredGHSpace`) | `BGW.ContinuumTrees.CodingStability` |  |
| C37.a3 | `g ↦ T_g` 2-Lipschitz for GH (Le Gall 2005, Lemma 2.4) | DELIVERED (exact) | `BGW.ContinuumTrees.Coding.ghDist_le_two_mul_norm`, `BGW.ContinuumTrees.Coding.lipschitzWith_two_toGHSpace` | `BGW.ContinuumTrees.CodingGH` | `ghDist (Space g) (Space h) ≤ 2 ‖g − h‖`. |
| C37.a4 | θ-stable tree is `T_{H^exc}` | DELIVERED (by definition) | `BGW.StableTrees.BrownianIdentification.stableTreeLaw_two` (shape `(excLaw θ).map (rootedMeasuredGHSpace ∘ Prod.snd)`) | `BGW.StableTrees.FiniteVarianceContour` | No named `stableTreeLaw θ` def; the expression is used literally (definition in Duquesne 2003). |
| C37.d | To add: forgetful map rooted measured GHP → GH is 1-Lipschitz | DELIVERED (exact) | `BGW.MetricMeasure.RootedMeasuredGHSpace.lipschitzWith_underlyingGH_forgetRoot`, `BGW.ContinuumTrees.Coding.forgetToGH`, `BGW.ContinuumTrees.Coding.continuous_forgetToGH`, `BGW.ContinuumTrees.Coding.underlyingGH_forgetRoot_rootedMeasuredGHSpace`, `BGW.ContinuumTrees.Coding.tendsto_map_forgetToGH` | `BGW.ContinuumTrees.CodingGH`, `BGW.ContinuumTrees.CodingGHCompat` | `LipschitzWith 1 (underlyingGH ∘ forgetRoot)`. Law-level `BGW.ContinuumTrees.Coding.tendsto_map_forgetToGH` is the GH claim after 5.10. |

### C38

Contour to rooted measured GHP transfer.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C38.a | BGW `BGW.ContinuumTrees.FiniteTree.tendsto_rooted_laws_of_contour` | DELIVERED (exact; pre-existing) | `BGW.ContinuumTrees.FiniteTree.tendsto_rooted_laws_of_contour` | `BGW.ContinuumTrees.ContourLawConvergence` | Hypotheses as in the spec: varying `Ω n`, `t n`, `b n > 0`, `b n → ∞`, measurability of the two observables, `∀ r>0, P(r < b_n/ζ) → 0`, contour convergence. Measure is the uniform vertex measure `mass`. |
| C38.c1 | Time convention `C_{2(ζ−1)s}` vs `C_{2ζs}` (time change within `1/ζ`) | DELIVERED (exact) | `BGW.PlaneTree.paperTimeChange`, `BGW.PlaneTree.paperContourFunction`, `BGW.PlaneTree.abs_paperTimeChange_sub_le`, `BGW.ContinuumTrees.FiniteTree.tendsto_map_paperContour_of_tendsto_map_contour`, `BGW.ContinuumTrees.FiniteTree.tendsto_map_contour_of_tendsto_map_paperContour` | `BGW.ContinuumTrees.ContourAdapters` | Both directions; hypothesis `∀ R, P(ζ < R) → 0`. |
| C38.c1' | `ζ → ∞` in probability from the ratio condition | DELIVERED (exact) | `BGW.ContinuumTrees.FiniteTree.tendsto_real_size_lt_of_ratio` | `BGW.ContinuumTrees.ContourAdapters` |  |
| C38.c2 | Deterministic divisor `b_n = n/(μ₀^{1−1/θ}B_n)` (Remark 5.10) | DELIVERED (exact) | `BGW.ContinuumTrees.FiniteTree.remarkDivisor`, `BGW.ContinuumTrees.FiniteTree.remarkDivisor_pos`, `BGW.ContinuumTrees.FiniteTree.tendsto_remarkDivisor_atTop` | `BGW.ContinuumTrees.ContourAdapters` |  |
| C38.c3 | Composite: contour (paper convention) with remark divisor ⇒ rooted measured law convergence to `ν.map rootedMeasuredGHSpace` | DELIVERED (exact) | `BGW.ContinuumTrees.FiniteTree.tendsto_rooted_laws_of_paperContour_remarkDivisor` | `BGW.ContinuumTrees.ContourPaperTransfer` | Hypotheses include `hNB : B n / N n → 0` and `hsize : ∀ c ∈ (0,1/μ₀), P(ζ < c N n) → 0` (size lower tail); the consumer (article 5.9, size concentration) must supply `hsize`. With `ν = law(H^exc)` the limit is the stable tree. |

### C39

Uniform leaf measure versus uniform vertex measure.

| Item.subclaim | Claim | Status | Lean declarations | Module (import) | Notes |
| --- | --- | --- | --- | --- | --- |
| C39.g1 | Inequality `d_gr(u(i),u(j)) ≤ H_i + H_j − 2 min_{i≤k≤j} H_k + 2` | BYPASSED (equivalent route) | `BGW.ContinuumTrees.FiniteTree.vertexEmbedding`, `BGW.ContinuumTrees.FiniteTree.isometry_vertexEmbedding`, `BGW.ContinuumTrees.FiniteTree.contourFunction_vertexTime` | `BGW.ContinuumTrees.ContourEmbedding` | Not exported in the height-index form. The finite tree's graph metric is isometrically embedded in the tree coded by its contour function, so the coupling bound is stated for the contour function (with the extra `2‖c‖/(2(n−1))` time-scale term in `BGW.ContinuumTrees.LeafMeasure.levyProkhorovDist_mass_leafMass_le`). Spec (b) marks the inequality as paper-level [D]; no independent theorem. |
| C39.g2 | Coupling via `U ~ unif[0,1)`: `u(⌊ζU⌋) ~ m_V`, leaf `⌈λU⌉` `~ m_L`; quantile convention at 0 and 1 | DELIVERED (equivalent; 0-indexed floor quantile) | `BGW.ContinuumTrees.LeafMeasure.rank`, `BGW.ContinuumTrees.LeafMeasure.idxTime`, `BGW.ContinuumTrees.LeafMeasure.vertexTimeMeasure`, `BGW.ContinuumTrees.LeafMeasure.leafTimeMeasure`, `BGW.ContinuumTrees.LeafMeasure.map_rank_volume`, `BGW.ContinuumTrees.LeafMeasure.map_leafRank_volume`, `BGW.ContinuumTrees.LeafMeasure.abs_idxTime_leaf_sub_vertex_le`, `BGW.ContinuumTrees.FiniteTree.map_sampleVertex_volume`, `BGW.ContinuumTrees.LeafMeasure.leafMass` | `BGW.ContinuumTrees.LeafMeasure`, `BGW.ContinuumTrees.UniformVertexSampling` | `rank n s = min ⌊n s⌋ (n−1)` (so `s = 1` goes to `n−1`, `s = 0` to 0), as `CT9` requires ("specify the discrete quantile convention at zero and one"). Leaf `k` (0-indexed) selected by `⌊N U⌋`. Equal in law to the spec's `⌈λU⌉` convention a.e. |
| C39.g3 | Deterministic bound `d_P^{(c·d_gr)}(m_V,m_L) ≤ c(2ω_H(δ)+2) + δ'` | DELIVERED (equivalent, deterministic generic form; different constants and no random layer) | `BGW.ContinuumTrees.LeafMeasure.levyProkhorovDist_map_projection_le_of_coupling`, `BGW.ContinuumTrees.LeafMeasure.levyProkhorovDist_vertex_leaf_le`, `BGW.ContinuumTrees.LeafMeasure.levyProkhorovDist_mass_leafMass_le` | `BGW.ContinuumTrees.LeafMeasure` | Coded-tree form `≤ 2ω` for the vertex/leaf-time measures with `D` bounding `\|ℓ k/n − k/N\|` and `ω` bounding the oscillation of `g` at scale `D+1/N+1/n`; plane-tree adapter `≤ 2ω` with scale `D + 1/N + 2A + 3/n`. Coupling statement `≤ max δ' (2ω)` has the bad-event mass `δ'`. Distance is the unscaled graph metric: no exported scaled `c·d_gr` form. The `+2` is absorbed (contour isometry). |
| C39.g4 | Convergence consequence under leaf-index discrepancy `D_j → 0` and equicontinuity | DELIVERED (exact, deterministic, generic library theorem) | `BGW.ContinuumTrees.LeafMeasure.tendsto_levyProkhorovDist_vertex_leaf`, `BGW.ContinuumTrees.LeafMeasure.tendsto_levyProkhorovDist_vertex_leaf_of_tendsto` | `BGW.ContinuumTrees.LeafMeasure` | Sequences of coding functions `g j`, `n j`, `N j → ∞`, `ℓ j`; hypotheses are a contour-modulus asymptotic equicontinuity, not a height modulus. A one-shot plane-tree bound exists, but no sequence-of-plane-trees convergence statement. |
| C39.g5 | Law-level transfer of C38 to the leaf measure (BGW perturbation C10(1)): rooted measured trees `(t_n, uniform leaf measure)` converge in law to the same limit | DELIVERED (exact) | `BGW.ContinuumTrees.LeafMeasure.tendsto_rooted_leaf_laws_of_contour`, `BGW.ContinuumTrees.LeafMeasure.tendsto_rooted_leaf_laws_of_contour_of_top`, `BGW.ContinuumTrees.LeafMeasure.leafRootedCompactMeasuredSpace`, `BGW.ContinuumTrees.LeafMeasure.dist_scale_leaf_vertex_le`, `BGW.ContinuumTrees.LeafMeasure.leafIndex_numLeaves_sub_one` | `BGW.ContinuumTrees.LeafLawConvergence`, `BGW.ContinuumTrees.LeafLawConvergenceDeterministic` | Law-level transfer of C38 to the uniform leaf measure: contour laws converge, `b n → ∞`, the ratio `b n / size` tends to 0 in probability and the leaf-index discrepancy (`hleaf`) tends to 0 in probability; the rescaled trees carrying the leaf measure then converge in law in the rooted measured GHP space to `ν.map Coding.rootedMeasuredGHSpace`, as for the vertex measure. The `_of_top` form takes `⊤`-measurable random trees. Commit `e7d9564`. |
| C39.c | Cor. 3.3 (`cor_Lambda`) makes `δ → 0` in probability | ARTICLE-SIDE | none | — | This lemma belongs to the article. |
| C39.c' | Tightness of `(B_ζ/ζ)H_{ζ·}` (5.9(ii)) makes `ω_H(δ) → 0` | ARTICLE-SIDE | none (BGW supplies analogues under `ζ = n` and `ζ ≥ n` only: `BGW.StableTrees.ExactContour.tendsto_exactHeightContourLaw`, `BGW.StableTrees.TailPair.tendsto_tailPairLaw`) | `BGW.StableTrees.ExactContourJoint`, `BGW.StableTrees.TailPair` | The leaf-conditioned tightness is the article's own functional layer (5.9). |
| C39.app | Final application: specialization to the actual leaf-conditioned model of the paper (Intro GHP, N9) | ARTICLE-SIDE | none | — | The article supplies the leaf-conditioned contour limit and the leaf-index discrepancy for its model. |

## Remaining obligations

**IN PROGRESS.** None. G1b (`condExp_reflectedFutureAt_augmented`, the augmented-filtration wording of C20.1) is delivered at commit `6581280`.

**OPEN.** None. Every other subclaim has an export, a documented bypass or an article-side classification below.

**Article-side obligations.** One line each on what BGW supplies and what the article must add.

- **C15.3c (Lipschitz size kernel).** BGW supplies `exists_abs_mul_stableDensity_le`, `exists_abs_mul_deriv_stableDensity_le` (C15.3a, b) and the kernels `qKernel`, `sizeTailKernel` with `continuousOn_qKernel`, `continuousOn_sizeTailKernel`. The article proves `qKernel_one_lipschitzOn` and `sizeTailKernel_lipschitz` (tranche 1).
- **C17.iii (random time change for Lemma 6.2(ii)).** BGW supplies the FCLT `IsRealStableAttracted.tendsto_stepPathLaw`, the norming ratio `tendsto_norming_floor_ratio`, and the deterministic maps `timeSpaceScale`, `continuousAt_timeSpaceScale`. The article adds the random scalar time and space perturbation of Lemma 6.2(ii) (via 5.7 with $S_n=T_{an}/(aN_n)$).
- **C30.a3 (leaf-conditioned $\sigma/(2\sqrt\zeta)$ form).** BGW supplies the fixed-size theorem `tendsto_exactHeightContour_finiteVariance_stable`, the identity `finiteVarianceNorming_div` for every tree size, and the random-size adapters of C38 (`tendsto_real_size_lt_of_ratio`, `tendsto_map_paperContour_of_tendsto_map_contour`). The article adds the leaf-conditioned random-size statement of Remark 4.6 from its Theorem 4.5.
- **C33.5 (link to `BGWLeaves.vervaat`).** BGW supplies `vervaatD_stepPath`, `vervaatTime_stepPath`, `vervaatIndex` and `isTreeExcursion_rotate_vervaatIndex`, with the rotation `x.rotate (vervaatIndex x)`. The article identifies that rotation with its own `BGWLeaves.vervaat`.
- **C36.N14.** BGW supplies the functional `maxJump` and `lipschitzWith_two_maxJump`. The article proves $\bar\Delta(W(\tau))=\Delta(\tau)-1$ (false for the one-vertex tree; $\lambda=n\ge2$).
- **C39.c (`cor_Lambda`).** BGW takes the leaf-index discrepancy as hypothesis `hleaf` of `tendsto_rooted_leaf_laws_of_contour`. The article's Corollary 3.3 (`cor_Lambda`) supplies it; BGW cannot import it.
- **C39.c' (leaf-conditioned height tightness).** BGW takes the contour convergence as hypothesis `hlim` (and tightness follows from it); it supplies the analogues under $\zeta=n$ and $\zeta\ge n$ (`tendsto_exactHeightContourLaw`, `tendsto_tailPairLaw`). The article proves the leaf-conditioned form of 5.9(ii).
- **C39.app (final specialization).** BGW supplies the whole generic chain (`tendsto_rooted_laws_of_contour`, `tendsto_rooted_leaf_laws_of_contour`, `levyProkhorovDist_mass_leafMass_le`). The article checks the specialization to the actual leaf-conditioned model: `hb`, `hratio`, `hleaf`, `hlim`.

**Bypassed rows** (not obligations; the reason is in each row): C27.g1, C27.g2, C28.f, C28.b, C29.f, C30.iii, C32.[D], C34.[D], C35.d, C39.g1.

Residual wording points, none a gap: the original exports of C27, C28 and C29 assume the bundled hypothesis `StableDomain μ θ B` (monotone positive `B`); since 8 November 2026 the `…_of_attracted` forms in `BGW.StableTrees.NonmonotoneNorming` hold for an arbitrary admissible norming (`IsRealStableAttracted (realOffspringStepLaw μ) θ B`, with `IsCritical μ` and `μ 1 ≠ 1`), as the specification (§1.3) allows; the walk coordinate of C28 stays at $-1/B_n$ after $\zeta$ (difference at most $1/B_n$); C29.a1 has a named contour-only export under `StableDomain` and follows for arbitrary admissible normings by taking the second marginal of the general joint statement.

## Import map for the article

For each article result of the usage map (§10 of the specification): the BGW modules to import and the exact declarations that supply each classical input, then the remaining article-side step. All names were verified in the source at commit `e7d9564`. Declarations are cited by their fully qualified names.

**4.1 (contour, $\zeta=n$, $C([0,1])$).** Import: `import BGW.StableTrees.ExactContourJoint`, `import BGW.StableTrees.ExactContourGlobal`, `import BGW.StableTrees.JointExcursion`.
  - C29: contour and height-contour limit along admissible sizes: `BGW.StableTrees.ExactContour.tendsto_exactHeightContourLaw`, `BGW.StableTrees.ExactContour.tendsto_exactHeightLibContourLaw`, `BGW.StableTrees.ExactContour.tendsto_contourHeightError`
  - limit law `excLaw` and its marginal (C22, C26): `BGW.StableTrees.excLaw`, `BGW.StableTrees.excLaw_map_fst`, `BGW.StableTrees.excLaw_height_endpoints_pos`
  - Article-side step: Take the second marginal (`continuous_snd` applied to the joint statement); the route R-A through C28 and C24 is not needed.

**4.2 ($H^{\mathrm{exc}}$ is the height excursion).** Import: `import BGW.StableTrees.JointExcursion`, `import BGW.StableTrees.UnitExcursionLawBasic`, `import BGW.StableTrees.ExcursionHeightBasic`, `import BGW.StableTrees.ExcursionHeightPositivity`.
  - C22 and C26: the objects: `BGW.StableTrees.excLaw`, `BGW.StableTrees.unitExcursionLaw`, `BGW.StableTrees.excursionHeight`, `BGW.StableTrees.excursionHeight_zero`, `BGW.StableTrees.ae_excursionHeight_pos_unit`
  - Article-side step: None (definitional).

**4.5 (contour under $\lambda\ge n$).** Import: `import BGW.StableTrees.ExactContourJoint`, `import BGW.StableTrees.FiniteVarianceContour`.
  - 4.1 inputs (C29): `BGW.StableTrees.ExactContour.tendsto_exactHeightContourLaw`
  - finite-variance form (C30): `BGW.StableTrees.ExactContour.tendsto_exactHeightContour_finiteVariance`, `BGW.StableTrees.ExactContour.tendsto_exactContour_finiteVariance`
  - Article-side step: Proposition 4.4(i)(ii) with $U_n=F(\text{rescaled contour})$ and Mathlib `tendsto_iff_forall_integral_tendsto`; no $D$ is needed.

**4.6 ($\theta=2$, Aldous normalization).** Import: `import BGW.StableTrees.BrownianExcursion`, `import BGW.StableTrees.BrownianPair`, `import BGW.StableTrees.FiniteVarianceContour`.
  - C30: $X^{\mathrm{exc}}=\sqrt2\,e$, $H^{\mathrm{exc}}=\sqrt2\,e$: `BGW.StableTrees.BrownianIdentification.levyExcLaw_two`, `BGW.StableTrees.BrownianIdentification.excLaw_two`, `BGW.StableTrees.BrownianIdentification.excLaw_two_map_snd`, `BGW.StableTrees.BrownianIdentification.excLaw_two_map_diag`
  - normalization $\sigma/(2\sqrt n)$ and tree law: `BGW.StableTrees.ExactContour.tendsto_exactHeightContour_finiteVariance_stable`, `BGW.StableTrees.ExactContour.finiteVarianceNorming_eq`, `BGW.StableTrees.ExactContour.finiteVarianceNorming_div`, `BGW.StableTrees.ExactContour.treeContourPath_finiteVariance_paper`, `BGW.StableTrees.BrownianIdentification.rootedMeasuredGHSpace_sqrt_two_smul`, `BGW.StableTrees.BrownianIdentification.stableTreeLaw_two`
  - Article-side step: C30.a3: the leaf-conditioned form $(\sigma/(2\sqrt\zeta))C_{2\zeta t}(\tau_n)\Rightarrow e$ from the article's Theorem 4.5.

**§5.1 (the objects).** Import: `import BGW.StableTrees.StableProcessLaw`, `import BGW.StableTrees.StableLocalLaw`, `import BGW.StableTrees.StableKendall`, `import BGW.StableTrees.StableFirstPassage`, `import BGW.StableTrees.StableUniqueMinimum`, `import BGW.StableTrees.ReflectedRestart`, `import BGW.StableTrees.StablePassageSubordinator`, `import BGW.StableTrees.ExcursionGapsStrongMarkov`, `import BGW.StableTrees.ExcursionMeasureBasic`, `import BGW.StableTrees.MarkedExcursionsBasic`, `import BGW.StableTrees.UnitExcursionLawBasic`, `import BGW.StableTrees.UnitExcursionLawMixture`, `import BGW.StableTrees.ExcursionMarkovProof`, `import BGW.StableTrees.HeightProcessBasic`, `import BGW.StableTrees.HeightContinuityBasic`, `import BGW.StableTrees.ExcursionHeightBasic`, `import BGW.StableTrees.JointExcursion`.
  - C16: stable process law: `BGW.StableTrees.stableProcessLaw`, `BGW.StableTrees.existsUnique_isStableLevyLaw`, `BGW.StableTrees.stableLocalLaw`
  - C18: first passage, Kendall, unique minimum: `BGW.StableTrees.kendall`, `BGW.StableTrees.ae_runningInf_continuous_antitone_tendsto`, `BGW.StableTrees.stableProcessLaw_ae_existsUnique_generalizedMinimizer`
  - C20: reflected process and local time: `BGW.StableTrees.reflectedFrom`, `BGW.StableTrees.localTime`, `BGW.StableTrees.condExp_reflectedFutureAt`
  - C21, C22, C23: excursion measure, Itô description, Markov property: `BGW.StableTrees.excursionMeasure`, `BGW.StableTrees.excursionPointMeasure`, `BGW.StableTrees.excursionAt`, `BGW.StableTrees.excursionMeasure_eq_lifetime_mixture`, `BGW.StableTrees.excursion_markov_lintegral`
  - C26: height process; encoding R-H: `BGW.StableTrees.height`, `BGW.StableTrees.heightLoc`, `BGW.StableTrees.excursionHeight`, `BGW.StableTrees.excLaw`, `BGW.StableTrees.tailExcLaw`
  - Article-side step: none for the objects.

**5.1 (trees with $\zeta\ge n$).** Import: `import BGW.StableTrees.TailPair`, `import BGW.StableTrees.JointExcursion`, `import BGW.StableTrees.UnitExcursionLawMixture`.
  - C28: `BGW.StableTrees.TailPair.tendsto_tailPairLaw`, `BGW.StableTrees.tailExcLaw`, `BGW.StableTrees.tailExcursionLaw_eq_mixture`
  - Article-side step: None (the statement holds for every horizon $T>0$; $T=1$ gives the article's form).

**5.3 ($\Gamma_a$ identity).** Import: `import BGW.StableTrees.JointExcursion`, `import BGW.StableTrees.GammaIdentity`.
  - C24: `BGW.StableTrees.gamma_identity`, `BGW.StableTrees.lintegral_gamma_identity`, `BGW.StableTrees.gamma_identity_path`, `BGW.StableTrees.integral_gammaA_tail_eq_one`, `BGW.StableTrees.ae_evalEnd_pos_tailPrefix`
  - Article-side step: None.

**5.7 (random scalar and space perturbation).** Import: `import BGW.Probability.WeakConvergence`, `import BGW.Skorokhod.Scaling`, `import BGW.Skorokhod.MeasurableMaps`, `import BGW.Skorokhod.ScalingContinuous`, `import BGW.Skorokhod.ProductPaths`.
  - C10(2): `BGW.Probability.tendsto_map_prodMk_of_tendsto_of_error`
  - C9: `BGW.Probability.tendsto_map_of_ae_continuousAt`, `BGW.Probability.aemeasurable_of_ae_continuousAt`
  - C6(4): scaling map and its continuity: `BGW.Skorokhod.timeSpaceScale`, `BGW.Skorokhod.continuousAt_timeSpaceScale`, `BGW.Skorokhod.measurable_timeSpaceScale_fixed`, `BGW.Skorokhod.timeSpaceScaleC`, `BGW.Skorokhod.continuous_timeSpaceScaleC`
  - C2: products and $D\times C$: `BGW.Skorokhod.prodWithCont`, `BGW.Skorokhod.continuous_prodWithCont`
  - Article-side step: Assemble: $(Z^n,K_n,S_n)\Rightarrow(Z,1,1)$ by C10(2), then C9 with continuity of the scaling map at $(Z,1,1)$.

**5.8.** Import: `import BGW.StableTrees.TailPair`, `import BGW.StableTrees.KendallAdapter`, `import BGW.StableTrees.Scalar.StableDensityPos`, `import BGW.Probability.WeakConvergence`, `import BGW.StableTrees.JointExcursion`, `import BGW.StableTrees.UnitExcursionLaw`, `import BGW.StableTrees.UnitExcursionLawSupport`.
  - C28 (step 1): `BGW.StableTrees.TailPair.tendsto_tailPairLaw`
  - C15 item 7: $\Gamma_a$ continuous and positive: `BGW.StableTrees.continuousOn_gammaA`, `BGW.StableTrees.measurable_gammaA`, `BGW.StableTrees.gammaA_pos`
  - C9 with cut-offs off the atoms (N11): `BGW.Probability.tendsto_map_of_ae_continuousAt`, `BGW.Probability.countable_setOf_measure_frontier_ne_zero`
  - C24 (step 5) and C22 E1 (step 6): `BGW.StableTrees.gamma_identity`, `BGW.StableTrees.levyExcLaw_endpoints_pos`, `BGW.StableTrees.ae_tailExcursionLaw_support`
  - Article-side step: C15.3c (Lipschitz size kernel) where the article uses it; Proposition 5.2, eq:cva and the transfer by Proposition 4.4(ii) are proved in the article.

**5.9(i).** Import: `import BGW.StableTrees.JointExcursion`, `import BGW.StableTrees.TailPair`, `import BGW.Probability.WeakConvergence`, `import BGW.Skorokhod.Scaling`.
  - 5.8 and 5.7 inputs: `BGW.StableTrees.gamma_identity`, `BGW.StableTrees.TailPair.tendsto_tailPairLaw`, `BGW.Probability.tendsto_map_prodMk_of_tendsto_of_error`, `BGW.Skorokhod.continuousAt_timeSpaceScale`
  - Article-side step: Choice $K_n=B_{r_n}/B_\zeta$, $S_n=a\zeta/T_{a\mu_0 r_n}$ from Corollary 3.3 and Lemma 5.6(ii) (article).

**5.9(ii).** Import: `import BGW.Skorokhod.Continuous`, `import BGW.Skorokhod.ContinuousEmbedding`, `import BGW.MetricMeasure.WeakPerturbation`, `import BGW.Skorokhod.Prefix`, `import BGW.Skorokhod.OptionalGaps`, `import BGW.Skorokhod.RestrictContinuity`, `import BGW.StableTrees.JointExcursion`.
  - C5: uniform convergence at a continuous limit: `BGW.Skorokhod.tendsto_iSup_dist_of_tendsto_ofContinuous`, `BGW.Skorokhod.isClosedEmbedding_ofContinuous`
  - C10(1): `BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability`
  - C11b: prefix and terminal control in $D$ and in $C$: `BGW.Skorokhod.tendsto_of_tendsto_restrict_of_oscillation`, `BGW.Skorokhod.tendsto_continuous_of_tendsto_restrict_of_oscillation`, `BGW.Skorokhod.continuousAt_oscillationFrom`
  - C26 H5: $H^{\mathrm{exc}}_0=H^{\mathrm{exc}}_1=0$: `BGW.StableTrees.excLaw_height_endpoints_pos`
  - Article-side step: Terminal control from the reversal invariance of the contour under $P(\cdot\mid\lambda=n)$ (article); eq:cvH from 5.8 and 5.7.

**5.10.** Import: `import BGW.Probability.WeakConvergence`, `import BGW.StableTrees.StableProcessCompactness`, `import BGW.ContinuumTrees.ContourAdapters`.
  - C10(2): `BGW.Probability.tendsto_map_prodMk_of_tendsto_of_error`
  - norming ratios: `BGW.StableTrees.IsRealStableAttracted.tendsto_norming_floor_ratio`, `BGW.ContinuumTrees.FiniteTree.remarkDivisor`, `BGW.ContinuumTrees.FiniteTree.tendsto_remarkDivisor_atTop`
  - Article-side step: The continuous map $(f,c)\mapsto c f$ and the in-probability limits $B_\zeta/B_n\to\mu_0^{-1/\theta}$, $\zeta/n\to1/\mu_0$ (article).

**GH claim after 5.10.** Import: `import BGW.ContinuumTrees.ContourPaperTransfer`, `import BGW.ContinuumTrees.ContourAdapters`, `import BGW.ContinuumTrees.CodingGH`, `import BGW.ContinuumTrees.CodingGHCompat`.
  - C38: `BGW.ContinuumTrees.FiniteTree.tendsto_rooted_laws_of_paperContour_remarkDivisor`, `BGW.ContinuumTrees.FiniteTree.tendsto_real_size_lt_of_ratio`, `BGW.ContinuumTrees.FiniteTree.tendsto_map_paperContour_of_tendsto_map_contour`
  - C37 forgetful map: `BGW.MetricMeasure.RootedMeasuredGHSpace.lipschitzWith_underlyingGH_forgetRoot`, `BGW.ContinuumTrees.Coding.tendsto_map_forgetToGH`, `BGW.ContinuumTrees.Coding.ghDist_le_two_mul_norm`
  - Article-side step: Supply `hsize` (lower tail of the size) and the contour convergence 5.9(ii) with 5.10.

**6.2(ii) (FCLT along $N_n=\lfloor n/\mu_0\rfloor$).** Import: `import BGW.StableTrees.StableProcessLaw`, `import BGW.StableTrees.StableProcessCompactness`, `import BGW.StableTrees.StableProcessMarkov`, `import BGW.Skorokhod.Scaling`.
  - C17: `BGW.StableTrees.IsRealStableAttracted.tendsto_stepPathLaw`, `BGW.StableTrees.StableDomain.tendsto_stepPathLaw`, `BGW.StableTrees.IsRealStableAttracted.tendsto_stepPathLaw_subseq`, `BGW.StableTrees.IsRealStableAttracted.tendsto_norming_floor_ratio`
  - C16 P2: scaling: `BGW.StableTrees.stableProcessLaw_scaling`
  - 5.7 inputs: `BGW.Skorokhod.continuousAt_timeSpaceScale`
  - Article-side step: C17.iii: the random time change with $S_n=T_{an}/(aN_n)$ and Lemma 6.2(i).

**6.6 and 6.7 (Vervaat map).** Import: `import BGW.Skorokhod.Vervaat`, `import BGW.Skorokhod.VervaatRotate`, `import BGW.Skorokhod.VervaatStep`, `import BGW.Skorokhod.VervaatMeasurable`.
  - C33: definition and discrete correspondence: `BGW.Skorokhod.vervaatTime`, `BGW.Skorokhod.vervaatD`, `BGW.Skorokhod.vervaatD_stepPath`, `BGW.Skorokhod.vervaatTime_stepPath`, `BGW.Skorokhod.vervaatIndex`, `BGW.Skorokhod.isTreeExcursion_rotate_vervaatIndex`, `BGW.Skorokhod.measurable_vervaatD`
  - Article-side step: C33.5: identify `x.rotate (vervaatIndex x)` with the article's `BGWLeaves.vervaat`; Proposition 6.5 (article).

**6.9(i).** Import: `import BGW.Skorokhod.VervaatContinuity`, `import BGW.Skorokhod.VervaatMinimumContinuity`, `import BGW.StableTrees.StableBridgeMinimum`, `import BGW.StableTrees.BridgeProjective`, `import BGW.StableTrees.VervaatIto`.
  - C34 continuity: `BGW.Skorokhod.continuousAt_vervaatD`, `BGW.Skorokhod.continuousAt_vervaatTime`, `BGW.StableTrees.stableBridgeLaw_ae_continuousAt_vervaatD`, `BGW.StableTrees.stableBridgeLaw_ae_vervaat_endpoints`
  - C31(ii) and C32: `BGW.StableTrees.stableBridgeLaw_endpoints`, `BGW.StableTrees.stableBridgeLaw_ae_minimum`, `BGW.StableTrees.stableBridgeLaw_ae_existsUnique_continuous_minimizer`
  - C35 law: `BGW.StableTrees.VervaatIto.map_vervaatD_stableBridgeLaw`, `BGW.StableTrees.VervaatIto.vervaatImage_eq_levyExcLaw`
  - Article-side step: None.

**6.9(ii).** Import: `import BGW.StableTrees.BridgeProjective`, `import BGW.StableTrees.StableBridgeClosed`, `import BGW.StableTrees.BridgePrefix`.
  - C31(i): `BGW.StableTrees.map_restrict_stableBridgeLaw`, `BGW.StableTrees.integral_restrict_stableBridgeLaw`, `BGW.StableTrees.bridgePrefixWeight`, `BGW.StableTrees.bridgePrefix_mass_one`
  - Article-side step: None.

**6.1.** Import: `import BGW.Probability.WeakConvergence`, `import BGW.StableTrees.StableBridgeClosed`, `import BGW.Skorokhod.Prefix`, `import BGW.Skorokhod.VervaatContinuity`, `import BGW.StableTrees.VervaatIto`, `import BGW.Skorokhod.VervaatStep`.
  - prefix: 6.2(ii), 6.9(ii), C9 with cut-offs: `BGW.Probability.tendsto_map_of_ae_continuousAt`, `BGW.Probability.countable_setOf_measure_frontier_ne_zero`, `BGW.StableTrees.integral_restrict_stableBridgeLaw`
  - terminal control (C11b, N12): `BGW.Skorokhod.tendsto_of_tendsto_restrict_of_oscillation`
  - Vervaat and identification (C34, C35, 6.7): `BGW.Skorokhod.continuousAt_vervaatD`, `BGW.StableTrees.VervaatIto.map_vervaatD_stableBridgeLaw`, `BGW.Skorokhod.vervaatD_stepPath`
  - Article-side step: Lemmas 6.10, 6.11, Proposition 6.8 and the discrete terminal tension estimate (article); random time and space via 5.7; the C33.5 glue for 6.7.

**7.1(i).** Import: `import BGW.Skorokhod.Jump`, `import BGW.Skorokhod.OptionalGaps`, `import BGW.StableTrees.ExcursionJump`, `import BGW.MetricMeasure.WeakPerturbation`.
  - C36: `BGW.Skorokhod.maxJump`, `BGW.Skorokhod.lipschitzWith_two_maxJump`, `BGW.Skorokhod.maxJump_eq_zero_iff`, `BGW.StableTrees.ae_maxJump_pos_levyExcLaw`, `BGW.StableTrees.ae_maxJump_pos_iff_levyExcLaw`, `BGW.StableTrees.ae_maxJump_eq_zero_levyExcLaw_two`
  - C10(1): `BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability`
  - Article-side step: C36.N14: $\bar\Delta(W(\tau))=\Delta(\tau)-1$ (for $\lambda=n\ge2$), plus 6.1 and 5.10.

**Introduction (II) (joint triple on $[0,1]$).** Import: `import BGW.StableTrees.ForestTriple`, `import BGW.StableTrees.ForestTripleVector`, `import BGW.Skorokhod.ProductPaths`, `import BGW.Skorokhod.OptionalGaps`, `import BGW.Skorokhod.Prefix`, `import BGW.MetricMeasure.WeakPerturbation`, `import BGW.Skorokhod.RestrictContinuity`, `import BGW.Probability.WeakConvergence`, `import BGW.StableTrees.JointExcursion`.
  - C27: forest triple: `BGW.StableTrees.ForestTriple.tendsto_forestTripleLaw`, `BGW.StableTrees.ForestTriple.tendsto_forestTripleVecLaw`, `BGW.StableTrees.ForestTriple.forestTripleLimit_eq_map_stableProcessLaw`
  - C5(4) and C11b in $D\times C^k$: `BGW.Skorokhod.prodWithCont`, `BGW.Skorokhod.continuous_prodWithCont`, `BGW.Skorokhod.tendsto_map_splitProdWithCont`, `BGW.Skorokhod.tendsto_of_tendsto_restrict_of_oscillation`
  - C10(1), C6(3), C9: `BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability`, `BGW.Skorokhod.continuousAt_oscillationFrom`, `BGW.Probability.tendsto_map_of_ae_continuousAt`
  - limit object: `BGW.StableTrees.excLaw`
  - Article-side step: Terminal control for $W$ from 6.1 and for $C$, $H$ from the proof of 5.9(ii); the coupling under $N(\cdot\mid\zeta=1)$.

**Introduction, GHP.** Import: `import BGW.ContinuumTrees.ContourLawConvergence`, `import BGW.ContinuumTrees.ContourPaperTransfer`, `import BGW.ContinuumTrees.LeafLawConvergence`, `import BGW.ContinuumTrees.LeafMeasure`.
  - C38: vertex measure: `BGW.ContinuumTrees.FiniteTree.tendsto_rooted_laws_of_contour`, `BGW.ContinuumTrees.FiniteTree.tendsto_rooted_laws_of_paperContour_remarkDivisor`
  - C39: leaf measure: `BGW.ContinuumTrees.LeafMeasure.tendsto_rooted_leaf_laws_of_contour`, `BGW.ContinuumTrees.LeafMeasure.tendsto_rooted_leaf_laws_of_contour_of_top`, `BGW.ContinuumTrees.LeafMeasure.levyProkhorovDist_mass_leafMass_le`, `BGW.ContinuumTrees.LeafMeasure.tendsto_levyProkhorovDist_vertex_leaf`, `BGW.ContinuumTrees.LeafMeasure.leafMass`, `BGW.ContinuumTrees.LeafMeasure.leafIndex`, `BGW.ContinuumTrees.LeafMeasure.numLeaves`
  - Article-side step: C39.c (`cor_Lambda` gives `hleaf`), C39.c' (leaf-conditioned height tightness gives `hlim`) and C39.app (the specialization).

**8.1(II).** Import: `import BGW.StableTrees.ForestTriple`, `import BGW.StableTrees.TailPair`, `import BGW.StableTrees.JointExcursion`.
  - same classical inputs as Introduction (II): `BGW.StableTrees.ForestTriple.tendsto_forestTripleLaw`, `BGW.StableTrees.TailPair.tendsto_tailPairLaw`, `BGW.StableTrees.gamma_identity`
  - Article-side step: The discrete $A$-analogues of 5.2, 5.4, 5.6, 6.5, 6.10, 6.11 (partly proved in the article), with discrete densities restricted to the admissible residue class when the span exceeds one.
