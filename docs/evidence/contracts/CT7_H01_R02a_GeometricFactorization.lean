import BGW.StableTrees.SupremumLocalTime
import BGW.StableTrees.StableLocalLaw
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.Basic

/-! Contract probe for H01 node R02a (blueprint R02, AUDIT items 1 and 8): independence of the
supremum and the drawdown at an independent exponential time, WITHOUT ladders.
Imports the FINAL (unsealed) `BGW.StableTrees.SupremumLocalTime`; `supRunning`, `supReflected` are
NOT redefined.

Encoding of the clock (the blueprint's recommended form, `P ⊗ Exp(q)`).  The probability space
is `DLoc × ℝ` with `expClockLaw θ q = stableLocalLaw θ ⊗ ProbabilityTheory.expMeasure q`; the
second coordinate `e` is the clock `e_q` (rate `q`, mean `1/q`), read as a time through
`e.toNNReal` (junk-free a.s., since `expMeasure q` is carried by `[0, ∞)`).  `S_{e_q}` is
`supRunning p.1 p.2.toNNReal`, `R_{e_q} = S_{e_q} - X_{e_q}` is `supReflected p.1 p.2.toNNReal`.

CONCLUSION ONLY.  No walk, ladder, excursion, or grid object occurs in any statement.
Proof route (docstring note, either supplier may prove it):
 * ROUTE A (blueprint R02, geometric walk): split the walk `X_{kΔ}`, `k ≤ N`, at its LAST maximum
   (empty blocks included; weak/strict inequalities complementary, so ties/atoms cost nothing;
   geometric weight `(1-r) r^j r^k`, `r = e^{-qΔ}`, `N = ⌊e_q/Δ⌋`); the two finite block measures
   have masses multiplying to one; mesh `2^{-n}`; càdlàg grid extrema converge at continuity
   times, exponential time avoids jumps by Fubini; pass bounded continuous product tests to the
   limit.
 * ROUTE B (AUDIT item 8, via the SEALED infimum excursion measure E04): with `Y = X - I`,
   `E[F(-I_{e_q}) G(Y_{e_q})] = (∫ e^{-aΦ} F(a) da) · N[∫_0^ζ q e^{-qs} G(e_s) ds]`, so
   `(-I_{e_q}, Y_{e_q})` are independent; fixed-time reversal integrated over the clock swaps
   this pair into `(R_{e_q}, S_{e_q})`.  Needs `ae_zeroSet_volume_zero`, joint cut/evaluation
   identities and compensation of the predictable factor `e^{-q T_{a-}}`.  Replaces R02 only.
Mere reversal of single excursions or of finite prefixes is NOT enough (AUDIT item 8).
TRUTH.  `S` and `R` are measurable and a.s. `≥ 0` (`f 0 = 0` a.s.), so the real-valued
statements below have no junk; the factors need NOT be probability-normalised separately in
route A, but the stated product law is a genuine independence of the two marginals.  The
explicit transforms (`R_{e_q} ~ Exp(q^{1/θ})`, `E e^{-λ S_{e_q}} = F_q(λ)`) are in contract R03.
Estimate 900-1600 lines (route A) or ~600-1000 (route B, if E04 interfaces fit). -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **Path law times an independent `Exp(q)` clock** on `DLoc × ℝ`. -/
noncomputable def expClockLaw (θ q : ℝ) : Measure (DLoc × ℝ) :=
  (stableLocalLaw θ : Measure DLoc).prod (expMeasure q)

/-- The clock model is a probability space for `q > 0`. -/
theorem isProbabilityMeasure_expClockLaw (θ : ℝ) {q : ℝ} (hq : 0 < q) :
    IsProbabilityMeasure (expClockLaw θ q) := sorry

/-- The clock is a.s. nonnegative, so `toNNReal` reads it without junk. -/
theorem ae_clock_nonneg_expClockLaw (θ : ℝ) {q : ℝ} (hq : 0 < q) :
    ∀ᵐ p ∂expClockLaw θ q, 0 ≤ p.2 := sorry

/-- `p ↦ S_{e_q}` is measurable. -/
theorem measurable_supRunning_expTime :
    Measurable (fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal) := sorry

/-- `p ↦ R_{e_q} = S_{e_q} - X_{e_q}` is measurable. -/
theorem measurable_supReflected_expTime :
    Measurable (fun p : DLoc × ℝ => supReflected p.1 p.2.toNNReal) := sorry

/-- Both `S_{e_q}` and `R_{e_q}` are a.s. nonnegative (`f 0 = 0` a.s.; `R ≥ 0` always). -/
theorem ae_nonneg_supRunning_supReflected_expTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ}
    (hq : 0 < q) :
    ∀ᵐ p ∂expClockLaw θ q, 0 ≤ supRunning p.1 p.2.toNNReal ∧ 0 ≤ supReflected p.1 p.2.toNNReal :=
  sorry

/-- **Independence of the supremum and the drawdown at an independent exponential time.**
`S_{e_q}` and `S_{e_q} - X_{e_q}` are independent under `P ⊗ Exp(q)`, for every `q > 0`. -/
theorem indepFun_supRunning_supReflected_expTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ}
    (hq : 0 < q) :
    IndepFun (fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal)
      (fun p : DLoc × ℝ => supReflected p.1 p.2.toNNReal) (expClockLaw θ q) := sorry

/-- **Product form** in `ℝ≥0∞` (no integrability needed): for Borel `F G : ℝ → ℝ≥0∞`,
`E[F(S_{e_q}) G(R_{e_q})] = E[F(S_{e_q})] · E[G(R_{e_q})]`. -/
theorem lintegral_mul_supRunning_supReflected_expTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ}
    (hq : 0 < q) {F G : ℝ → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G) :
    ∫⁻ p, F (supRunning p.1 p.2.toNNReal) * G (supReflected p.1 p.2.toNNReal) ∂expClockLaw θ q =
      (∫⁻ p, F (supRunning p.1 p.2.toNNReal) ∂expClockLaw θ q) *
        ∫⁻ p, G (supReflected p.1 p.2.toNNReal) ∂expClockLaw θ q := sorry

/-- **Resolvent form** (same statement without the clock space): with `q e^{-qt} dt` weights on
`[0, ∞)`, `∫ q e^{-qt} E[F(S_t) G(R_t)] dt` factors.  Derived from the product form by Tonelli. -/
theorem lintegral_resolvent_mul_supRunning_supReflected {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ}
    (hq : 0 < q) {F G : ℝ → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G) :
    ∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (q * Real.exp (-q * t)) *
        ∫⁻ f, F (supRunning f t.toNNReal) * G (supReflected f t.toNNReal)
          ∂(stableLocalLaw θ : Measure DLoc) =
      (∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (q * Real.exp (-q * t)) *
          ∫⁻ f, F (supRunning f t.toNNReal) ∂(stableLocalLaw θ : Measure DLoc)) *
        ∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (q * Real.exp (-q * t)) *
          ∫⁻ f, G (supReflected f t.toNNReal) ∂(stableLocalLaw θ : Measure DLoc) := sorry

end BGW.StableTrees
