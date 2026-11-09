import BGW.StableTrees.StableLaw
import BGW.StableTrees.Scalar.Density

/-! Contract probe for CT.C15 item 3 (CT10): `sup_x |x p_1(x)| < ∞` and `sup_x |x p_1'(x)| < ∞`,
`p_1 = Scalar.stableDensity θ`, `θ ∈ (1,2]`. Classification: NEW (no hit in `BGW/`; the
statement of the spec says tranche 1 avoided it, `qKernel_one_lipschitzOn` is not in `BGW/`).

PROOF PLAN. `φ(u) = stableCF θ u = exp((-iu)^θ)`, `p_1(x) = (1/2π) Re ∫ φ(u) e^{-iux} du`.
`φ` is `C^1` on `ℝ` (θ>1 so `|u|^θ` is `C^1` at `0`), `φ' = θ (-iu)^{θ-1}(-i) φ`, and
`‖φ(u)‖ = exp(-c|u|^θ)` (`c = cos(πθ/2)·(-1) > 0` for `θ<2`, `c=1` for `θ=2`); so `φ`, `φ'`,
`uφ'`, `φ''`-type terms are integrable. `x e^{-iux} = i ∂_u e^{-iux}`; integrate by parts
(`integral_mul_deriv_eq_deriv_mul` on `ℝ`, vanishing at `±∞`) to get
`x p_1(x) = (1/2π) Re (i ∫ φ'(u) e^{-iux} du)`, bounded by `(1/2π) ∫‖φ'‖`. The derivative statement needs `HasDerivAt` of
`p_1` (differentiation under the integral, dominated by `|u| ‖φ‖`) and a second integration by
parts with `(uφ)'` integrable. Size 200-450 lines; the second theorem is the harder one. -/

open Real

namespace BGW.StableTrees

/-- `sup_x |x p_1(x)| < ∞`. -/
theorem exists_abs_mul_stableDensity_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ C : ℝ, ∀ x : ℝ, |x * Scalar.stableDensity θ x| ≤ C := sorry

/-- `p_1` is differentiable. -/
theorem differentiable_stableDensity {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    Differentiable ℝ (Scalar.stableDensity θ) := sorry

/-- `sup_x |x p_1'(x)| < ∞`. -/
theorem exists_abs_mul_deriv_stableDensity_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ C : ℝ, ∀ x : ℝ, |x * deriv (Scalar.stableDensity θ) x| ≤ C := sorry

end BGW.StableTrees
