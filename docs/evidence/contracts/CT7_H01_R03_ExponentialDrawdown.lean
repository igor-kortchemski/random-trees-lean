import BGW.StableTrees.SupremumLocalTime
import BGW.StableTrees.StableLocalLaw
import BGW.StableTrees.StablePassageSubordinator
import Mathlib.Probability.Distributions.Exponential

/-! Contract probe for H01 node R03 (blueprint R03, AUDIT item 2): exponential drawdown and the
scalar supremum transform at an independent exponential time.  Depends on R02a.
`supRunning`, `supReflected` (from the FINAL unsealed `BGW.StableTrees.SupremumLocalTime`) are NOT
redefined.

Constants (all CHECKED against the library and the blueprint; no inconsistency found).
`Φ = q^{1/θ}`.  The process is spectrally POSITIVE with `E e^{-λ X_t} = e^{t λ^θ}` for `λ ≥ 0`
(`integral_exp_neg_mul_stableLawAt`), hence `E e^{-λ X_{e_q}} = q/(q - λ^θ)` for `0 ≤ λ < Φ`.
It creeps DOWNWARD (first passage below `-x`, `T_x`, has `E e^{-qT_x} = e^{-xΦ}`, sealed
`integral_exp_neg_passageLaw`), and reaches new suprema by JUMPS.  By reversal
`R_{e_q} = S_{e_q} - X_{e_q} ~ -I_{e_q}` and `P(-I_{e_q} > y) = P(T_y < e_q) = e^{-yΦ}`:
 * `R_{e_q} ~ Exp(Φ)` exactly (`expMeasure (q^{1/θ})`), so `E e^{λ R} = Φ/(Φ-λ)`.
 * With R02a independence, `E e^{-λ X} = E e^{-λ S} · E e^{λ R}` gives
   `F_q(λ) := E e^{-λ S_{e_q}} = q(Φ-λ) / (Φ (q-λ^θ))`, `0 ≤ λ < Φ`; by analytic continuation
   the same formula holds for all `λ ≥ 0`, `λ ≠ Φ`, and `F_q(Φ) = 1/θ` (removable singularity).
Checks: `F_q(0) = 1`; `F_q(∞) = 0` (no atom of `S` at `0`); `θ = 2` gives `Φ/(Φ+λ)`, i.e.
`S_{e_q} ~ Exp(√q)` there.
**FLAG (request wording, not a blueprint/library inconsistency).**  `S_{e_q}` is NOT exponential
for `θ < 2`: `Exp(Φ)` would give `F_q(Φ) = 1/2`, but `F_q(Φ) = 1/θ`.  It is the DRAWDOWN
`R_{e_q}` that is `Exp(q^{1/θ})` for every `θ ∈ (1,2]`; `S_{e_q}` is exponential only at `θ = 2`
(`Φ = √q`).  Both facts are stated below, plus the `θ < 2` non-exponentiality as a guard against
a wrong later reading.
Proof route: (i) fixed-time reversal (`map_reverseIncrements_stableProcessLaw`) and passage
transform give the `R` law; (ii) R02a plus `E e^{-λ X_{e_q}}` for `λ < Φ` gives `F_q` on `[0,Φ)`;
(iii) analytic continuation (both sides analytic in `Re λ > 0` off `Φ`; boundedness of
`e^{-λS}` for `λ ≥ 0` gives analyticity of the left side).  Estimate 500-900 lines. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-! ### copied from contract CT7_H01_R02a_GeometricFactorization (not part of this contract) -/

/-- (copied) Path law times an independent `Exp(q)` clock on `DLoc × ℝ`. -/
noncomputable def expClockLaw (θ q : ℝ) : Measure (DLoc × ℝ) :=
  (stableLocalLaw θ : Measure DLoc).prod (expMeasure q)

/-- (copied) The clock model is a probability space for `q > 0`. -/
theorem isProbabilityMeasure_expClockLaw (θ : ℝ) {q : ℝ} (hq : 0 < q) :
    IsProbabilityMeasure (expClockLaw θ q) := sorry

/-- (copied) Independence of `S_{e_q}` and `R_{e_q}`. -/
theorem indepFun_supRunning_supReflected_expTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ}
    (hq : 0 < q) :
    IndepFun (fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal)
      (fun p : DLoc × ℝ => supReflected p.1 p.2.toNNReal) (expClockLaw θ q) := sorry

/-! ### R03 proper -/

/-- **Exponential drawdown.** `S_{e_q} - X_{e_q} ~ Exp(q^{1/θ})`. -/
theorem law_supReflected_expTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    (expClockLaw θ q).map (fun p : DLoc × ℝ => supReflected p.1 p.2.toNNReal) =
      expMeasure (q ^ (1 / θ)) := sorry

/-- Tail form: `P ⊗ Exp(q) (R_{e_q} > y) = e^{-y q^{1/θ}}` for `y ≥ 0`. -/
theorem expClockLaw_supReflected_gt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q)
    {y : ℝ} (hy : 0 ≤ y) :
    expClockLaw θ q {p | y < supReflected p.1 p.2.toNNReal} =
      ENNReal.ofReal (Real.exp (-(y * q ^ (1 / θ)))) := sorry

/-- Input for the division step: `E e^{-λ X_{e_q}} = q/(q-λ^θ)` for `0 ≤ λ < q^{1/θ}`
(spectrally positive: `E e^{-λ X_t} = e^{t λ^θ}`), with integrability. -/
theorem integral_exp_neg_eval_expTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ} (hq : 0 < q)
    (hlam : 0 ≤ lam) (hlt : lam < q ^ (1 / θ)) :
    Integrable (fun p : DLoc × ℝ => Real.exp (-lam * p.1.1 p.2.toNNReal)) (expClockLaw θ q) ∧
      ∫ p, Real.exp (-lam * p.1.1 p.2.toNNReal) ∂expClockLaw θ q = q / (q - lam ^ θ) := sorry

/-- **Scalar supremum transform, off the diagonal.** For every `λ ≥ 0`, `λ ≠ q^{1/θ}`:
`E e^{-λ S_{e_q}} = q (Φ-λ) / (Φ (q-λ^θ))`, `Φ = q^{1/θ}`.  (The integrand is bounded by `1`
a.s. since `S ≥ 0` a.s., so the `ℝ`-integral has no junk.) -/
theorem integral_exp_neg_supRunning_expTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ}
    (hq : 0 < q) (hlam : 0 ≤ lam) (hne : lam ≠ q ^ (1 / θ)) :
    ∫ p, Real.exp (-lam * supRunning p.1 p.2.toNNReal) ∂expClockLaw θ q =
      q * (q ^ (1 / θ) - lam) / (q ^ (1 / θ) * (q - lam ^ θ)) := sorry

/-- **Diagonal value** `F_q(Φ) = 1/θ` (removable singularity of the formula above). -/
theorem integral_exp_neg_supRunning_expTime_diag {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ}
    (hq : 0 < q) :
    ∫ p, Real.exp (-(q ^ (1 / θ)) * supRunning p.1 p.2.toNNReal) ∂expClockLaw θ q =
      1 / θ := sorry

/-- **Brownian case**: for `θ = 2`, `S_{e_q} ~ Exp(√q)` (`Φ = q^{1/2}`). -/
theorem law_supRunning_expTime_two {q : ℝ} (hq : 0 < q) :
    (expClockLaw 2 q).map (fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal) =
      expMeasure (q ^ (1 / (2 : ℝ))) := sorry

/-- **Guard (FLAG above)**: for `θ < 2`, `S_{e_q}` is NOT exponential with rate `q^{1/θ}`
(its transform at `Φ` is `1/θ ≠ 1/2`). -/
theorem law_supRunning_expTime_ne_exp {θ : ℝ} (hθ : 1 < θ ∧ θ < 2) {q : ℝ} (hq : 0 < q) :
    (expClockLaw θ q).map (fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal) ≠
      expMeasure (q ^ (1 / θ)) := sorry

end BGW.StableTrees
