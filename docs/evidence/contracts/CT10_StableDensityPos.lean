import BGW.StableTrees.StableLaw
import BGW.StableTrees.KendallAdapter

/-! Contract probe for CT.C15 items 6-7 (CT10): strict positivity of `p_1` on `ℝ` and of `Γ_a`.
`p_1 = Scalar.stableDensity θ`, `θ ∈ (1,2]`.

AMBIGUITY in the spec (C15.7): "`Γ_a` continuous and positive" is justified only for the
denominator `sizeTailKernel` (`p_1(0) > 0` and continuity). Strict positivity of the numerator
`q_{1-a}(x) = x/(1-a) · p_{1-a}(-x)` needs `p_1 > 0` on `(-∞,0)`, i.e. the (spec-"optional") C15.6.
In the library, only `gammaA_nonneg` exists. So the strict positivity of `gammaA` is NOT free.

ROUTE (elementary, no Zolotarev). `p_1(0) > 0` and continuity give `r > 0` with `p_1 > 0` on
`(-r,r)`; scaling gives `p_t > 0` on `(-r t^{1/θ}, r t^{1/θ})`. `p_t * p_s = p_{t+s}`
(`integral_stableDensityAt_mul`) with continuous nonneg integrands: if `f > 0` on `(-a,a)`,
`g > 0` on `(-b,b)` then `f*g > 0` on `(-(a+b), a+b)`. By induction `p_{1}`
is the `n`-fold convolution of `p_{1/n}`, positive on `(-r n^{1-1/θ}, r n^{1-1/θ})`, and
`n^{1-1/θ} → ∞` since `θ > 1`. Size 150-300 lines (the convolution-positivity lemma is the bulk). -/

namespace BGW.StableTrees

/-- CT.C15.6: `p_1 > 0` on all of `ℝ`. -/
theorem stableDensity_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ) :
    0 < Scalar.stableDensity θ x := sorry

/-- CT.C15.7 (strict positivity): `Γ_a(x) > 0` for `a < 1`, `x > 0`; with
`continuousOn_gammaA` (sealed) and `gammaA_nonneg` (sealed) this completes the item. -/
theorem gammaA_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {a x : ℝ} (ha : a < 1) (hx : 0 < x) :
    0 < gammaA θ a x := sorry

end BGW.StableTrees
