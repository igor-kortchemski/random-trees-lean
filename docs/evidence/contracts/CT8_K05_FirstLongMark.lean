import BGW.StableTrees.ExcursionLifetime
import BGW.StableTrees.ExcursionMarkovConsequences
import BGW.StableTrees.ExcursionMeasure
import BGW.StableTrees.MarkedExcursions
import BGW.StableTrees.StableExcursionSupport
import BGW.StableTrees.UnitExcursionLaw
import BGW.ContinuumTrees.ExcursionCarrier
import Mathlib.Probability.Distributions.Exponential
import BGW.StableTrees.LongExtractionDefs

/-! Contract probe for CT8 node K05 (R5 blueprint §3, audit findings 1 and 5, "first nodes"
item 2): the FIRST LONG POISSON MARK under `stableLocalLaw θ`, probabilistic support only.  The
convergence statement `tendsto_tailWalkLaw` (K05b) is a separate later contract and is NOT here;
nothing below assumes convergence of the discrete extraction (K04), and K04 imports nothing from
here (its good-path predicate lives in `BGW.StableTrees.LongExtractionDefs`).

REUSE (sealed, not restated).  Lifetime atomlessness at positive lifetimes is the sealed
`excursionMeasure_lifetime_eq_zero` (and `tailExcursionLaw_lifetime_eq_zero`); the `Excursion`
carrier has `lifetime_pos`, which disposes of lifetime zero (`excursionMeasure_lifetime_singleton`
below is the thin unified wrapper).  Mass `N(ζ > 1) = 1/Γ(1-1/θ) = θ p₀` is
`excursionMeasure_lifetime_gt_one`.  The Poisson structure is
`excursionCounts_poisson_independent_pointMeasure`, `lintegral_pointMeasure_eq_prod`,
`exists_measurable_modification_excursionPointMeasure`; a.s. facts are `ae_jumpExcursion_spec`,
`ae_jumpExcursion_support`, `ae_jump_window_inf`, `ae_isExcursionInterval_iff`,
`ae_continuousAt_jumpStart`, `ae_passageJumpSet_countable`, `ae_finite_excursionCount`,
`ae_passageTime_eq_firstPassageBelow`, `ae_creeping_passageTime`,
`ae_runningInf_continuous_antitone_tendsto`; no fixed jump: `N_noFixedJump`; the target law is
`tailExcursionLaw θ` (`coe_tailExcursionLaw`, `tailExcursionMeasure = Γ(1-1/θ) • N ↾ {ζ > 1}`).

TRUTH.  With `r = N(ζ > 1) = 1/Γ(1-1/θ)`, the process of long marks
`{(x, e) : x ∈ J(f), ζ(e) > 1}` is a Poisson point process on `ℝ≥0 × {ζ > 1}` with intensity
`Leb ⊗ N↾{ζ>1}` (finite rate in `x`), so the first label `L` is `Exp(r)`, the first mark has the
normalized law `N(· | ζ > 1) = tailExcursionLaw θ`, and they are independent.  `L < ∞`, the
end `T_L = T_{L-} + ζ` is finite and `P(T_L < M) → 1` as `M → ∞`.  Confusion to avoid: the
excursion STRADDLING time 1 (O01) has a different unnormalized law.

PROOF PLAN.  (1) For `a > 0` apply the sealed lifetime atomlessness on each label window
`(0, K]` with `K ∈ ℕ`: the Poisson count of marks with `ζ = a` in `(0,K] × ·` has mean
`K * N{ζ = a} = 0`, so it is a.s. zero, then take the countable union over `K`
(`ae_jump_lifetime_ne`).  (2) Long labels in `(0, K]` have finite count with finite maximum
(`ae_finite_excursionCount`), so a least long label exists whenever there is one, and there is
one a.s. since the count in `(0,K]` is Poisson with mean `K r → ∞` (`ae_exists_longLabel`).
(3) AE-measurability of `L` and the mark from the measurable modification of the point measure
and `sInf` over countably many windows.  (4) Joint law: first-point-of-Poisson on the long-mark
restriction (`P(L > x) = e^{-r x}`, conditional on `L = x` the mark has law `N↾{ζ>1}/r` by
`lintegral_pointMeasure_eq_prod` and the compensation formula).  (5) The a.s. good path
`ae_goodLongExtractionPath`: items (i)-(ii) sealed, (iii) is `ae_isRegularExcursionLevel`
(brackets from strict monotonicity of `T`; the interior bound on `R` and its LEFT limits from
generalized minima on rational windows, `ae_jump_window_inf`: do not infer it from pointwise
`R > 0`), (iv) from (1) with `a = 1`, (v) from (2) and finiteness of `T_L`.  Localization is
only through `T_L < M`; the cut continuity at `T` is `ae_continuousAt_tailExcursion_path` from
`N_noFixedJump` and `tailExcursionLaw ≪ N`.  Size 900-1500 lines.

BINDER SCOPE (AUDITOR_RULES): no integral or big operator followed by `+`/`-` occurs here. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

-- Extraction definitions: `BGW/StableTrees/LongExtractionDefs.lean`.

/-! ### Rate and law of the first label -/

/-- The rate `r_θ = 1/Γ(1-1/θ) = N(ζ > 1) = θ p₀`. -/
noncomputable def longRate (θ : ℝ) : ℝ := 1 / Real.Gamma (1 - 1 / θ)

/-- The exponential law of rate `r_θ` on `ℝ≥0` (the law of the first long label). -/
noncomputable def firstLongLabelLaw (θ : ℝ) : Measure ℝ≥0 :=
  (expMeasure (longRate θ)).map Real.toNNReal

/-- `N(ζ > 1) = r_θ`, from the sealed lifetime tail. -/
theorem excursionMeasure_longMarks (hθ : 1 < θ ∧ θ ≤ 2) :
    excursionMeasure θ {e : Excursion | 1 < (e.lifetime : ℝ)} =
      ENNReal.ofReal (longRate θ) := by
  exact excursionMeasure_lifetime_gt_one hθ

/-! ### Lifetime atomlessness on the process -/

/-- No lifetime is charged by `N` (unified with lifetime `0`, excluded by the carrier). -/
theorem excursionMeasure_lifetime_singleton (hθ : 1 < θ ∧ θ ≤ 2) (u : ℝ≥0) :
    excursionMeasure θ {e : Excursion | e.lifetime = u} = 0 := by
  by_cases hu : u = 0
  · subst hu
    have : {e : Excursion | e.lifetime = 0} = ∅ := by
      ext e
      simp [e.lifetime_pos.ne']
    rw [this, measure_empty]
  · have h := excursionMeasure_lifetime_eq_zero hθ (u : ℝ) (by positivity)
    convert h using 2
    ext e
    simp [NNReal.coe_inj]

/-- A.s. no excursion mark has a prescribed lifetime `a` (Poisson, localized to `(0, K]`,
countable union over `K`; N-null marks do not occur in the process). -/
theorem ae_jump_lifetime_ne (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f,
      passageTime x f - passageTimeMinus x f ≠ a := by
  sorry

/-! ### Existence, measurability and joint law of the first long mark -/

/-- A.s. there is a long label and a least one. -/
theorem ae_exists_longLabel (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∃ L, IsLeast (longLabelSet f) L := by
  sorry

/-- The first long label is a.e.-measurable (junk off the a.s. event). -/
theorem aemeasurable_firstLongLabel (hθ : 1 < θ ∧ θ ≤ 2) :
    AEMeasurable firstLongLabel (stableLocalLaw θ : Measure DLoc) := by
  sorry

/-- The first long mark is a.e.-measurable. -/
theorem aemeasurable_firstLongMark (hθ : 1 < θ ∧ θ ≤ 2) :
    AEMeasurable firstLongMark (stableLocalLaw θ : Measure DLoc) := by
  sorry

/-- **Exponential/product law**: the first long label is `Exp(r_θ)`, the first long mark has
law `tailExcursionLaw θ`, and they are independent. -/
theorem map_firstLongLabel_firstLongMark (hθ : 1 < θ ∧ θ ≤ 2) :
    (stableLocalLaw θ : Measure DLoc).map (fun f => (firstLongLabel f, firstLongMark f)) =
      (firstLongLabelLaw θ).prod (tailExcursionLaw θ : Measure Excursion) := by
  sorry

/-- Identification of the selected mark with `tailExcursionLaw θ` (a corollary of the product
law; no extraction convergence is assumed). -/
theorem map_firstLongMark (hθ : 1 < θ ∧ θ ≤ 2) :
    (stableLocalLaw θ : Measure DLoc).map firstLongMark =
      (tailExcursionLaw θ : Measure Excursion) := by
  sorry

/-- Marginal of the first label: `Exp(r_θ)`. -/
theorem map_firstLongLabel (hθ : 1 < θ ∧ θ ≤ 2) :
    (stableLocalLaw θ : Measure DLoc).map firstLongLabel = firstLongLabelLaw θ := by
  sorry

/-- **Finite end**: the selected end `T_L` is finite a.s. and `P(T_L < M) → 1` as `M → ∞`. -/
theorem tendsto_measure_firstLongEnd_lt (hθ : 1 < θ ∧ θ ≤ 2) :
    Tendsto (fun M : ℝ≥0 =>
      (stableLocalLaw θ : Measure DLoc) {f | passageTime (firstLongLabel f) f < M})
      atTop (𝓝 1) := by
  sorry

/-! ### The a.s. good path -/

/-- No fixed jump of the selected mark at a positive cutoff. -/
theorem ae_continuousAt_tailExcursion_path (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ e ∂(tailExcursionLaw θ : Measure Excursion), ContinuousAt e.path.1 T := by
  sorry

/-- **A.s. supplier of the geometric facts (iii)**: every jump level is a regular excursion
level (interior bounds for values AND left limits, strict record brackets, zero endpoints). -/
theorem ae_isRegularExcursionLevel (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ∀ x ∈ passageJumpSet f, IsRegularExcursionLevel f x := by
  sorry

/-- **`ae_goodLongExtractionPath`, localized by `d < M`**: a.s., if the first long excursion
ends before `M`, the path is good on `[0, M]`. -/
theorem ae_goodLongExtractionPath (hθ : 1 < θ ∧ θ ≤ 2) (M : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      passageTime (firstLongLabel f) f < M → GoodLongExtractionPath M f := by
  sorry

/-- The cut version, for every positive cutoff `T` (continuity of the selected cut at `T`). -/
theorem ae_goodLongExtractionCutPath (hθ : 1 < θ ∧ θ ≤ 2) (M T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      passageTime (firstLongLabel f) f < M → GoodLongExtractionCutPath M T f := by
  sorry

end BGW.StableTrees
