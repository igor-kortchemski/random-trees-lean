import BGW.StableTrees.Scalar.DensityLaw
import BGW.StableTrees.Scalar.FiniteVariance
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Group.Convolution

/-! Contract probe for CT.C15 items 1, 2 and 4 (CT4): unconditional θ-stable law,
`1 < θ ≤ 2`, with `E[exp(-λ X)] = exp(λ^θ)`. Maintained file:
`BGW/StableTrees/StableLaw.lean` (module `BGW.StableTrees.StableLaw`). It may import the ported
attraction modules `BGW.StableTrees.Attraction.*`. -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace BGW.StableTrees

/-- For every index `1 < θ ≤ 2`, some critical offspring law lies in the normalized θ-stable
domain of attraction (C15.1; witness by an explicit regularly varying tail). -/
theorem exists_stableDomain {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ (μ : PMF ℕ) (a : ℕ → ℝ), StableDomain μ θ a := sorry

/-- The stable density is nonnegative, unconditionally on `1 < θ ≤ 2` (C15.1). -/
theorem stableDensity_nonneg {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ) :
    0 ≤ Scalar.stableDensity θ x := sorry

/-- The stable density integrates to one (C15.1). -/
theorem integral_stableDensity {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∫ x, Scalar.stableDensity θ x = 1 := sorry

/-- The spectrally positive θ-stable law, normalized by `E[exp(-λ X)] = exp(λ^θ)`, for
`1 < θ ≤ 2`; the Dirac mass at `0` outside this range (a junk value). -/
noncomputable def stableLaw (θ : ℝ) : ProbabilityMeasure ℝ :=
  if hθ : 1 < θ ∧ θ ≤ 2 then
    ⟨volume.withDensity (fun x => ENNReal.ofReal (Scalar.stableDensity θ x)), sorry⟩
  else ⟨Measure.dirac 0, inferInstance⟩

/-- The stable law has density `Scalar.stableDensity θ` (C15.1). -/
theorem stableLaw_eq_withDensity {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (stableLaw θ : Measure ℝ) =
      volume.withDensity (fun x => ENNReal.ofReal (Scalar.stableDensity θ x)) := sorry

/-- Laplace transform of the stable law (C15.1). -/
theorem integral_exp_neg_mul_stableLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫ x, Real.exp (-lam * x) ∂(stableLaw θ : Measure ℝ) = Real.exp (lam ^ θ) := sorry

/-- Characteristic function of the stable law: `exp ((-i t)^θ)` (C15.1). -/
theorem charFun_stableLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ) :
    charFun (stableLaw θ : Measure ℝ) t = Scalar.stableCF θ t := sorry

/-- The stable law is the only probability measure with this Laplace transform (C15.1). -/
theorem eq_stableLaw_of_laplace {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ν : Measure ℝ}
    [IsProbabilityMeasure ν]
    (hL : ∀ lam : ℝ, 0 < lam → ∫ y, Real.exp (-lam * y) ∂ν = Real.exp (lam ^ θ)) :
    ν = (stableLaw θ : Measure ℝ) := sorry

/-- At `θ = 2` the stable law is the centered Gaussian of variance `2` (C15; §1.1). -/
theorem stableLaw_two : (stableLaw 2 : Measure ℝ) = gaussianReal 0 2 := sorry

/-- The density of the stable law at time `t > 0`: `t^{-1/θ} p₁(t^{-1/θ} x)` (C15.4). -/
noncomputable def stableDensityAt (θ t x : ℝ) : ℝ :=
  t ^ (-1 / θ) * Scalar.stableDensity θ (t ^ (-1 / θ) * x)

/-- The stable law at time `t > 0`, image of `stableLaw θ` under `x ↦ t^{1/θ} x` (C15.4). -/
noncomputable def stableLawAt (θ t : ℝ) : ProbabilityMeasure ℝ :=
  (stableLaw θ).map (fun x => t ^ (1 / θ) * x)

/-- `stableLawAt θ t` has density `stableDensityAt θ t` (C15.4). -/
theorem stableLawAt_eq_withDensity {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ} (ht : 0 < t) :
    (stableLawAt θ t : Measure ℝ) =
      volume.withDensity (fun x => ENNReal.ofReal (stableDensityAt θ t x)) := sorry

/-- Laplace transform at time `t`: `E[exp(-λ X_t)] = exp(t λ^θ)` (C15.4). -/
theorem integral_exp_neg_mul_stableLawAt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ} (ht : 0 < t)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫ x, Real.exp (-lam * x) ∂(stableLawAt θ t : Measure ℝ) = Real.exp (t * lam ^ θ) := sorry

/-- Semigroup property of the stable laws (C15.4). -/
theorem stableLawAt_conv {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (stableLawAt θ s : Measure ℝ) ∗ (stableLawAt θ t : Measure ℝ) =
      (stableLawAt θ (s + t) : Measure ℝ) := sorry

/-- Semigroup property of the stable densities: `p_s * p_t = p_{s+t}` (C15.4). -/
theorem integral_stableDensityAt_mul {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) (x : ℝ) :
    ∫ y, stableDensityAt θ s y * stableDensityAt θ t (x - y) = stableDensityAt θ (s + t) x :=
  sorry

end BGW.StableTrees
