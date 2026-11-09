import BGW.StableTrees.StableLaw
import BGW.StableTrees.StableDensityAPI

/-! Contract probe for CT.C15 items 5-6 (CT10): positivity and negativity probabilities of the
spectrally positive stable law `stableLaw θ`, `∫ exp(-λx) d(stableLaw θ) = exp(λ^θ)`, `θ ∈ (1,2]`.

TRUTH. Zolotarev positivity parameter for spectrally positive `θ`-stable: `ρ = P(X > 0) = 1 - 1/θ`,
so `P(X < 0) = 1/θ` (Bertoin 1996, VIII.1, for the spectrally negative mirror `P(X>0)=1/θ`;
Zolotarev 1986 I.4). Checks: `θ = 2` gives `1/2` (the law is `N(0,2)`); `θ ↓ 1` gives `P(X<0) → 1`
(`e^{λ^θ} → e^λ`: the law tends to the point mass at `-1`; the mean stays `0` through a
thin heavy positive tail).
Independent Gil-Pelaez check: `charFun = exp((-iu)^θ)`, for `u>0` equal to `exp(u^θ e^{-iπθ/2})`,
`P(X>0) = 1/2 + (1/π) ∫_0^∞ Im φ(u)/u du = 1/2 + (1/(πθ)) ∫_0^∞ Im e^{-zs}/s ds`, with
`z = e^{iπ(1-θ/2)}`, `Re z > 0`, and `∫_0^∞ Im e^{-zs}/s ds = -arctan(Im z/Re z) = -π(1-θ/2)`;
total `1/2 - (1/θ)(1 - θ/2) = 1 - 1/θ`. Both routes agree.
Scale invariance extends the result to every `stableLawAt θ t`, `t > 0`.
No atom at `0` (the law has a density).

PROOF PLAN. (1) `stableLaw_singleton_zero` from `stableLaw_eq_withDensity`. (2) Either Gil-Pelaez
(needs the inversion formula for `P(X>0)`, not in Mathlib; heavy), or Laplace route:
`E[e^{-λX}; X<0]` and `E[e^{-λX}; X>0]` via analytic continuation of `λ ↦ e^{λ^θ}` to
`Re λ > 0` and the Stieltjes/Frullani identity; or Kendall/first-passage route using the
project's `StableFirstPassage` (`P(T_x < ∞) = 1` for spectrally positive does not directly give
it). Recommended: Fourier route via the density `p_1(x) = (1/2π) ∫ e^{-iux} φ(u) du` and
`∫_0^∞ p_1(x)e^{-εx}dx` with `ε ↓ 0` (Abel), computing `∫_0^∞ φ(u)/(ε + iu) du` by contour
rotation, `φ` analytic in `{Re(-iu)^θ ≤ 0}`. Size estimate 300-600 lines. -/

open MeasureTheory
open scoped ENNReal

namespace BGW.StableTrees

/-- No atom at `0`. -/
theorem stableLaw_singleton_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (stableLaw θ : Measure ℝ) {0} = 0 := sorry

/-- CT.C15.5: `P(X_1 > 0) = 1 - 1/θ` for the spectrally positive stable law. -/
theorem stableLaw_Ioi_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (stableLaw θ : Measure ℝ) (Set.Ioi 0) = ENNReal.ofReal (1 - 1 / θ) := sorry

/-- CT.C15.5: `P(X_1 < 0) = 1/θ`. -/
theorem stableLaw_Iio_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (stableLaw θ : Measure ℝ) (Set.Iio 0) = ENNReal.ofReal (1 / θ) := sorry

/-- Density form: `∫_{u>0} p_1(-u) du = 1/θ`. -/
theorem integral_stableDensity_neg_Ioi {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∫ u in Set.Ioi (0 : ℝ), Scalar.stableDensity θ (-u) = 1 / θ := sorry

/-- Every time marginal has the same sign probabilities (scaling). -/
theorem stableLawAt_Iio_zero {θ t : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ht : 0 < t) :
    (stableLawAt θ t : Measure ℝ) (Set.Iio 0) = ENNReal.ofReal (1 / θ) := sorry

end BGW.StableTrees
