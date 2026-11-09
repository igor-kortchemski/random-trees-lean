import BGW.StableTrees.ExcursionLifetime
import BGW.StableTrees.ExcursionMeasure
import BGW.StableTrees.StableKendall
import BGW.ContinuumTrees.ExcursionCarrier
import BGW.StableTrees.UnitExcursionLaw
import BGW.StableTrees.ExcursionMarkov
import BGW.StableTrees.KendallAdapter

/-! Contract probe for CT7 node E10 (path-only Gamma identity, source Proposition 2.3 of
`duquesne_revised.tex`, lines 727-760; the target article calls it Proposition 5.3), following
`r3-ct7-blueprint/blueprint.md` E10, its signature block and AUDIT item 7.

CONSTANTS.  `α = 1/θ`, `p0 = d_θ(0) = α/Γ(1-α)`, `N(ζ>1) = 1/Γ(1-α) = θ p0`,
so `tailExcursionMeasure θ = Γ(1-α) • N ↾ {ζ>1}` is a probability measure.  Source (N1):
`N(f q_{1-a}(e a); ζ>a) = p0 N_(1)(f)` (= E09); source (N2): for `F ≥ 0`,
`N(F | ζ>1) = Γ(1-α) N(F(r_a e) G_{1-a}(e a); ζ>a)` with `G_r(x) = ∫_{s>r} q_s(x) ds`
(`sizeTailKernelENN`).  Hence
`N(F Γ_a(e a) | ζ>1) = Γ(1-α) θ N(F q_{1-a}(e a); ζ>a) = Γ(1-α) θ p0 N_(1)(F) = N_(1)(F)`,
the only place the coefficients enter: `Γ(1-α) θ p0 = 1`.  Pitfall (blueprint risk): dropping `θ`
or normalizing by `N(ζ>a)` instead of `N(ζ>1)`.  CONSTANTS CHECKED CONSISTENT: blueprint,
source, E06, E08, E09.

DEFINITIONS.  Copied (verbatim) from E06/E08/E09: `excursionTail`, `unitExcursionMeasure`,
`tailExcursionMeasure`, `toProbOrJunk`, `unitExcursionLaw`, `tailExcursionLaw`, `qKernel`,
`sizeTailKernelENN`, `sizeTailKernel`, `gammaA`, `unitPrefix`.  New: `tailPrefix θ a =
(tailExcursionLaw θ).map (excursionRestrict a)` (law of the prefix of the excursion under
`N(· | ζ>1)`), `evalEnd a x = x(a)` the endpoint coordinate of a path on `D a ℝ`.

CONVENTIONS / JUNK.  `a : ℝ≥0` with `0 < a < 1` (blueprint writes `a : ℝ`; the carrier API
`excursionRestrict` takes `ℝ≥0`).  `gammaA θ a x` is a real quotient `θ q_{1-a}(x)/G_{1-a}(x)`:
its value is unconstrained (and not claimed) where `x ≤ 0`; a zero or non-integrable `G_{1-a}(x)`
forces the junk value `0`.  This is harmless: under `tailPrefix` the endpoint satisfies
`evalEnd x > 0` a.s. (`ae_evalEnd_pos_tailPrefix`, since `a < 1 < ζ`), and there
`G_{1-a}(x) > 0` finite
(E08 `sizeTailKernel_pos`, `sizeTailKernelENN_lt_top`) so `gammaA ≥ 0` (E08 `gammaA_nonneg`).
The measure identity is stated first, with density `ofReal (gammaA ..)`; bounded signed tests
are then integrable although `gammaA` is not claimed bounded.  The source test class
(bounded measurable, valued in `ℝ≥0`) is contained in the bounded real class below.
The joint `(path, height)` form (`gamma_identity`, J01) is NOT part of this contract.

TRUTH.  All theorems bind `hθ : 1 < θ ∧ θ ≤ 2`, `0 < a < 1`.

PROOF PLAN.  (1) E07 Markov + remaining lifetime (`excursion_markov_lintegral`) and E08
(`passageLaw_eq_qKernel`, `sizeTailKernelENN_eq_passageLaw`) give
`N(F(r_a e); ζ>1) = N(F(r_a e) G_{1-a}(e a); ζ>a)` (`excursionTail_size_tail`; `ζ>1` is `ζ-a >
1-a`).  (2) Substitute `F · Γ_a(e a)`, use `Γ_a G_{1-a} = θ q_{1-a}` on `e a > 0` (E08
`gammaA_mul_sizeTail`) and cancel the strictly positive finite survival factor.  (3) E09
(`levyExcLaw_prefix_density`) with `N(ζ>1) = θ p0` (E06 `excursionMeasure_lifetime_gt_one`,
`tailExcursionMeasure`) gives equality of finite measures; E08 `sizeTailKernel_pos`,
`ofReal_sizeTailKernel`, `sizeTailKernelENN_lt_top` control the survival factor; total mass one
gives `integral_gammaA_tail_eq_one` and integrability of bounded tests
(`integral_withDensity_eq_integral_toReal_smul`).
Estimate 200-400 lines. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-! ### Copied declarations (not part of this contract) -/

open scoped Classical in
-- copied from contract CT7_E09_UnitDensity (not part of this contract)
/-- **Law of the unit excursion on `[0,a]`**: `(r_a)_* unitExcursionLaw`. -/
noncomputable def unitPrefix (θ : ℝ) (a : ℝ≥0) : Measure (D (a : ℝ) ℝ) :=
  (unitExcursionLaw θ : Measure Excursion).map (excursionRestrict a)

-- copied from contract CT7_E09_UnitDensity (not part of this contract)
/-- **Density of the unit excursion at prefix times** (E2, source (N1)). -/
theorem levyExcLaw_prefix_density {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    unitPrefix θ a =
      (ENNReal.ofReal (Scalar.stableDensity θ 0))⁻¹ •
        ((excursionTail θ a).withDensity
          (fun e => ENNReal.ofReal (qKernel θ (1 - a) (e.path.1 a)))).map
            (excursionRestrict a) := sorry

/-! ### New definitions -/

/-- **Law of the excursion prefix under `N(· | ζ > 1)`**: `(r_a)_* tailExcursionLaw`, on the
compact path space `D a ℝ` (horizon `(a : ℝ)`). -/
noncomputable def tailPrefix (θ : ℝ) (a : ℝ≥0) : Measure (D (a : ℝ) ℝ) :=
  (tailExcursionLaw θ : Measure Excursion).map (excursionRestrict a)

/-- **Endpoint coordinate** `x ↦ x(a)` of a path on `D a ℝ` (the point `a` of `Icc 0 a`). -/
noncomputable def evalEnd (a : ℝ≥0) (x : D (a : ℝ) ℝ) : ℝ :=
  (x : Set.Icc (0 : ℝ) a → ℝ) ⟨a, a.2, le_rfl⟩

/-! ### Supporting facts -/

/-- The endpoint of the restricted excursion is the value at `a`. -/
theorem evalEnd_excursionRestrict (a : ℝ≥0) (e : Excursion) :
    evalEnd a (excursionRestrict a e) = e.path.1 a := sorry

/-- The endpoint coordinate is measurable on `D a ℝ`. -/
theorem measurable_evalEnd (a : ℝ≥0) : Measurable (evalEnd a) := sorry

/-- **Positive endpoint under the tail prefix**: for `a < 1`, `tailPrefix`-a.s. `x(a) > 0`
(from `ae_tailExcursionLaw_support`: `a < 1 < ζ`).  This is where the junk region `x ≤ 0` of
`gammaA` is excluded. -/
theorem ae_evalEnd_pos_tailPrefix {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    ∀ᵐ x ∂(tailPrefix θ a), 0 < evalEnd a x := sorry

/-- **Size-tail identity** (E07 Markov + remaining lifetime + E08 Kendall tail): for `0 < a < 1`
and measurable `F ≥ 0` on `D a ℝ`,
`N(F(r_a e); ζ>1) = N(F(r_a e) G_{1-a}(e a); ζ>a)`, `G_r(x) = ∫_{s>r} q_s(x) ds`
(source (N2), before the factor `Γ(1-α)`). -/
theorem excursionTail_size_tail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) (F : D (a : ℝ) ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ e, F (excursionRestrict a e) ∂(excursionTail θ 1) =
      ∫⁻ e, F (excursionRestrict a e) *
        sizeTailKernelENN θ (1 - a) (e.path.1 a) ∂(excursionTail θ a) := sorry

/-! ### The Gamma identity -/

/-- **Gamma identity as an equality of finite measures** on `D a ℝ`:
`(r_a)_* N_(1) = gammaA(a, x(a)) · (r_a)_* N(· | ζ>1)`.  Hence both sides have mass one. -/
theorem levyExcLaw_prefix_eq_withDensity_tail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    unitPrefix θ a =
      (tailPrefix θ a).withDensity (fun x => ENNReal.ofReal (gammaA θ a (evalEnd a x))) := sorry

/-- **Nonnegative version** (no boundedness): for measurable `F : D a ℝ → ℝ≥0∞`,
`∫⁻ F d(r_a)_* N_(1) = ∫⁻ F(x) Γ_a(x(a)) d(r_a)_* N(· | ζ>1)`. -/
theorem lintegral_gamma_identity_path {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) (F : D (a : ℝ) ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x ∂(unitPrefix θ a) =
      ∫⁻ x, F x * ENNReal.ofReal (gammaA θ a (evalEnd a x)) ∂(tailPrefix θ a) := sorry

/-- **Total mass**: `∫ Γ_a(x(a)) d(r_a)_* N(· | ζ>1) = 1` (and `Γ_a(x(a))` is integrable). -/
theorem integral_gammaA_tail_eq_one {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    Integrable (fun x => gammaA θ a (evalEnd a x)) (tailPrefix θ a) ∧
      ∫ x, gammaA θ a (evalEnd a x) ∂(tailPrefix θ a) = 1 := sorry

/-- **Path-only Gamma identity** (Proposition 2.3 of the source, path part): for every bounded
measurable `F : D a ℝ → ℝ` and `0 < a < 1`,
`N_(1)(F(r_a ·)) = N(F(r_a ·) Γ_a(e a) | ζ>1)`. -/
theorem gamma_identity_path {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) (F : D (a : ℝ) ℝ → ℝ) (hF : Measurable F)
    (hb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    (∫ x, F x ∂(unitPrefix θ a)) =
      ∫ x, F x * gammaA θ a (evalEnd a x) ∂(tailPrefix θ a) := sorry

end BGW.StableTrees
