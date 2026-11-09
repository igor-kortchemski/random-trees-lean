import BGW.StableTrees.MarkedExcursions
import BGW.StableTrees.ExcursionMeasure
import BGW.StableTrees.Scalar.Density


/-! Contract probe for CT7 node E05 (lifetime law, normalization and scaling of the excursion
measure `N`), following `r3-ct7-blueprint/blueprint.md` E05.

CONSTANTS (checked).  Write `α = 1/θ`.  From N09, `E e^{-q T_x} = e^{-x q^α}`; from E03/E04, a.s.
`T_1 = ∑_{x ≤ 1} ζ(e_x)` (no drift) and the Laplace functional of the Poisson point measure with
intensity `Leb ⊗ N` give `E e^{-q T_1} = exp(-∫ (1 - e^{-qζ}) dN)`.  Hence
`∫ (1 - e^{-qζ}) dN = q^α` (`lintegral_one_sub_exp_lifetime`).  This is the Lévy–Khintchine
exponent of the driftless subordinator with Lévy measure `Π = ζ_* N`, and by the identity
`∫_0^∞ (1 - e^{-qt}) α t^{-1-α} dt / Γ(1-α) = q^α` (integration by parts and
`∫ e^{-qt} t^{-α} dt = Γ(1-α) q^{α-1}`) one gets
`Π(dt) = α/Γ(1-α) t^{-1-α} dt`, `N(ζ > t) = t^{-α} / Γ(1-α)`.
(Note `1 - 1/θ ∈ (0, 1/2]`, so `Γ(1-1/θ) > 0`.)  The coefficient `α/Γ(1-α)` equals
`d_θ(0) = Γ(1+1/θ) sin(π/θ)/π` by `Γ(α)Γ(1-α) = π/sin(πα)` and `Γ(1+α) = αΓ(α)`.

SCALING (checked).  With `scaleLoc θ c f t = c^{1/θ} f(t/c)` the label of an excursion of the
scaled path is `c^{1/θ}` times the original label (E03 `ae_excursionPointMeasure_scaleLoc`), and
`stableLocalLaw θ` is invariant under `scaleLoc θ c`; taking expectations of the window `(0,1]`:
`N(A) = c^{-1/θ} N(S_c^{-1} A)`, i.e. `(S_c)_* N = c^{1/θ} • N`.  Consistency with the tail:
`N(cζ > t) = c^{1/θ} N(ζ > t)`.  Lifetimes are positive so `{0 < ζ}` is everything.

Imports `BGW.StableTrees.Scalar.Density` for `Scalar.stableDensity`.  Estimate 650-1200 lines. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees


/-! ### Lifetime law of `N` -/

/-- **Laplace exponent of the lifetime**: `∫ (1 - e^{-q ζ}) dN = q^{1/θ}` for `q ≥ 0`
(integrand in `ℝ≥0∞`; `1 - e^{-qζ} ∈ [0,1]`). -/
theorem lintegral_one_sub_exp_lifetime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 ≤ q) :
    ∫⁻ e, ENNReal.ofReal (1 - Real.exp (-q * (e.lifetime : ℝ))) ∂(excursionMeasure θ) =
      ENNReal.ofReal (q ^ (1 / θ)) := sorry

/-- **Lifetime tail**: `N(ζ > t) = t^{-1/θ} / Γ(1 - 1/θ)` for `t > 0`. -/
theorem excursionMeasure_lifetime_tail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ) (ht : 0 < t) :
    excursionMeasure θ {e : Excursion | t < (e.lifetime : ℝ)} =
      ENNReal.ofReal (t ^ (-(1 / θ)) / Real.Gamma (1 - 1 / θ)) := sorry

/-- **Lifetime density**: the image of `N` under the lifetime is
`(1/θ)/Γ(1-1/θ) · t^{-1-1/θ} dt` on `(0,∞)` (Lévy measure of the passage subordinator). -/
theorem excursionMeasure_lifetime_density {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (excursionMeasure θ).map Excursion.lifetime =
      lebNN.withDensity (fun t : ℝ≥0 =>
        ENNReal.ofReal ((1 / θ) / Real.Gamma (1 - 1 / θ) * (t : ℝ) ^ (-1 - 1 / θ))) := sorry

/-- **Normalization bridge**: `d_θ(0) = 1 / (θ Γ(1 - 1/θ))` (the coefficient `α/Γ(1-α)`
of the Lévy density equals the stable density at `0`). -/
theorem stableDensity_zero_eq_inv_theta_gamma {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    Scalar.stableDensity θ 0 = 1 / (θ * Real.Gamma (1 - 1 / θ)) := sorry

/-! ### Scaling of `N` -/

/-- **Scaling of `N`** (E01 convention `S_c`: path `c^{1/θ} e(t/c)`, lifetime `c ζ`):
`(S_c)_* N = c^{1/θ} • N` for every `c > 0`. -/
theorem map_excursionScale_excursionMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (c : Set.Ioi (0 : ℝ)) :
    (excursionMeasure θ).map (excursionScale θ c) =
      ENNReal.ofReal ((c : ℝ) ^ (1 / θ)) • excursionMeasure θ := sorry

end BGW.StableTrees
