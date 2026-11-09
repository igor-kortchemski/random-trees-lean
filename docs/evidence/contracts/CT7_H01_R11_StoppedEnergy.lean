import BGW.StableTrees.SupremumDrawdown
import BGW.StableTrees.SupremumReflectedFamily
import BGW.StableTrees.SupremumLocalTime
import BGW.Probability.DoobL2Resolvent
import BGW.StableTrees.StableLocalLaw
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import BGW.StableTrees.SupremumLocalTimeIdent
import BGW.StableTrees.SupremumLadderTransform
import BGW.StableTrees.SupremumCorrection

/-! Contract probe for H01 node R11 (blueprint R11 "Stopped energy estimate and full stopped
convergence"; AUDIT sol-audit-r09r10 finding 7: the energy theorem `E D² ≤ 4zV + 12V²` belongs to
R11, not R10; finding 9: downstream coverage).  Depends on R07 (stopping representative
`supHitting`, identification) and R10 (error martingale, cutoff); NOT on R09.

Everything here is about the AUXILIARY clock `M^* = supAuxLocalTime` and its inverse
`A^* = supAuxLadderTime` (R05/R06), because R10's `errorMartingale` is built from `M^*`.  The
transfer to the public `supLocalTime`, `supLadderTime` (the three final stopped statements) is
R12's job (`ae_supLocalTime_eq_aux`, `ae_supLadder_eq_aux` of R07); R11 states the same three
theorems in auxiliary form (`..._aux`).
NOT redefined (sealed, imported): `supRunning`, `supReflected`, `supOccupation`,
`supReflectedFrom` (R01), `IsSupOccupationSeq`.
Copied definitions: R05 `compactError … supAuxLimit`; R06 `supAuxLocalTime`, `supAuxInverse`,
`supAuxLadderTime`; R04 `stableScale`, `supCorrection`; R07 `exists_isSupOccupationSeq`,
`supEps`, `supLocalTimeENN`, `supHitting`, `isStoppingTime_supHitting`; R10 `supCorrectionBound`,
`occupationCorrection`, `errorMartingale`, `supReflectedExit`, `errCutoff`, `errStopTime`.
Suppliers consumed by the PROOFS (not restated): R10 `martingale_errorMartingale_stopped`,
`integrable_sq_errorMartingale_stopped`, `integral_errorMartingale_stopped`,
`integral_supOccupation_stopped_le`, `abs_occupationCorrection_le`,
`occupationCorrection_eq_zero`, `ae_errorMartingale_zero`, `ae_rightContinuous_errorMartingale`,
`isStoppingTime_errCutoff`, `errCutoff_le`, `tendsto_errCutoff_top`,
`tendsto_supCorrectionBound`; R06 `ae_supAuxLocalTime_spec`, `ae_supAuxStieltjes_support`,
`ae_supAuxLadder_spec` (`M^*(A^*_z) = z`, `A^*_z ∈ {R = 0}`); R07 `ae_supLadder_geometry`
(`supHitting θ z = A_z` a.s.), `ae_supLadder_eq_aux`, `isStoppingTime_supHitting`;
Mathlib `Martingale`, Doob's `L²` maximal inequality, Fatou / uniform integrability.

Mathematics (hand-checked).  Fix `z`, `ε > 0`; `V = V_ε = supCorrectionBound θ ε`, `σ = A_z`
(stopping representative `supHitting θ z`), `τ = σ ∧ t ∧ cutoff_n` bounded.  `D` is a càdlàg
martingale up to the bounded epoch `τ` on the common good event (R10); continuity of `D` is not
required.  `C = O_ε - M^*` is continuous of finite variation (`O_ε` is Lipschitz for fixed
`ε > 0`, `M^*` continuous and monotone), and `w = D - C = v_ε(R) - v_ε(0)` is càdlàg with
`|w| ≤ 2V`.  Summation by parts on
a mesh with Riemann-Stieltjes limit (continuous finite-variation `C`, so no Itô formula):
`E D_τ² = 2 E ∫_0^τ w dC + E w_τ²`, with `dC = g_ε(R) ds - dM^*`; `w = 0` on `{R = 0}`
which carries `dM^*` (R06 support), so only `E ∫ w g_ε(R) ds ≤ 2V E O_ε(τ)` survives;
`E O_ε(τ) ≤ E M^*_τ + 2V ≤ z + 2V` (R10, `M^*_τ ≤ M^*_{A_z} = z`).  Hence
`E D_τ² ≤ 2·2V·(z + 2V) + 4V² = 4zV + 12V²`.  Doob: `E sup_{s ≤ t}|D_{s∧τ}|² ≤ 4 E D_τ²`.
Removing the cutoff: a.s. `errCutoff n → ⊤` and `A_z < ∞` so `τ = A_z` for large `n, t`; Fatou
gives the same bounds at `A_z`; the `L²` bound gives uniform integrability so `E O_ε(A_z) = z`
(`D` has mean zero, `E w_{A_z} = 0` since `R_{A_z} = 0` there).  Finally `O - M^* = D - w`,
`|w| ≤ 2V`: `sup|O-M^*|² ≤ 2 sup D² + 8V²`, so `E sup ≤ 8(4zV+12V²) + 8V² = 32zV + 104V²
≤ 104 (zV + V²)`.

FLAGS.
(1) `V_ε` is R10's `supCorrectionBound` `(1/Γ(θ)+1/2) ε^{θ-1}` (the blueprint's `sup|v_ε|` is
smaller; all inequalities stay true with the larger `V`).
(2) The level `z` is FIXED (no all-`z` intersection); `τ` is stated at the stopping time
`supHitting θ z` (a genuine stopping time), and transferred to `A^*_z = supAuxLadderTime`
only a.s. (`ae_supHitting_eq_supAuxLadderTime`, from R07 geometry + R06 spec).
(3) The blueprint's `C (zV + V²)` is stated with the explicit constant `104`.
(4) `∀ε>0` is used in R11's integrability statements; the final contract only needs `ε ≤ 1`.
(5) Every integral is of a function proved integrable in the same statement (no default-zero
real integral is a bound).
(6) Estimate 800-1400 lines. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-! ### Copied definitions -/

open scoped Classical in
open scoped Classical in
/-! ### Stopping representative and the stopped epoch -/

/-- The stopping representative of `A^*_z` is `A^*_z`, almost surely, and is finite
(R07 `ae_supLadder_geometry` + `ae_supLadder_eq_aux`). -/
theorem ae_supHitting_eq_supAuxLadderTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      supHitting θ z f = (supAuxLadderTime θ z f : ℝ≥0∞) := sorry

/-- Up to the stopping epoch `τ = σ ∧ t ∧ cutoff_n`, `M^* ≤ z` (monotone, `M^*(A^*_z) = z`),
simultaneously in `n`, `t`. -/
theorem ae_supAuxLocalTime_errStopTime_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ (n : ℕ) (t : ℝ≥0),
      supAuxLocalTime θ f (errStopTime n (supHitting θ z) t f) ≤ (z : ℝ) := sorry

/-- The localization is removed for large parameters: almost surely, eventually in `n`,
`errStopTime n (supHitting θ z) s f = s` for every `s ≤ A^*_z`, and at `s = n` it equals
`A^*_z`. -/
theorem ae_eventually_errStopTime_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ᶠ n : ℕ in atTop,
      (∀ s : ℝ≥0, s ≤ supAuxLadderTime θ z f →
        errStopTime n (supHitting θ z) s f = s) ∧
      errStopTime n (supHitting θ z) n f = supAuxLadderTime θ z f := sorry

/-! ### The energy estimate at a bounded stopping epoch -/

/-- **Mean occupation at the stopped epoch** (blueprint `E[O_ε(τ)] ≤ z + 2 V_ε`), with
integrability (`0 ≤ O_ε(τ) ≤ τ/ε ≤ n/ε`). -/
theorem integral_supOccupation_errStopTime_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ} (hε : 0 < ε)
    (z : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    Integrable (fun f => supOccupation ε f (errStopTime n (supHitting θ z) t f))
        (stableLocalLaw θ : Measure DLoc) ∧
      ∫ f, supOccupation ε f (errStopTime n (supHitting θ z) t f)
        ∂(stableLocalLaw θ : Measure DLoc) ≤ (z : ℝ) + 2 * supCorrectionBound θ ε := sorry

/-- **Energy estimate** `E D_τ² ≤ 4 z V_ε + 12 V_ε²` at `τ = A_z ∧ t ∧ cutoff_n`
(summation by parts for the martingale `D` of R10 against the finite-variation `C = O - M^*`;
the `dM^*` term vanishes since `w = 0` on `{R = 0}`). -/
theorem integral_sq_errorMartingale_stopped_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ}
    (hε : 0 < ε) (z : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    Integrable (fun f => (errorMartingale θ ε (errStopTime n (supHitting θ z) t f) f) ^ 2)
        (stableLocalLaw θ : Measure DLoc) ∧
      ∫ f, (errorMartingale θ ε (errStopTime n (supHitting θ z) t f) f) ^ 2
          ∂(stableLocalLaw θ : Measure DLoc) ≤
        4 * (z : ℝ) * supCorrectionBound θ ε + 12 * supCorrectionBound θ ε ^ 2 := sorry

/-- **Doob `L²` maximal inequality for the stopped `D`**:
`E sup_{s ≤ t}|D_{s∧τ_n}|² ≤ 4 E D_{t∧τ_n}² ≤ 4 (4 z V + 12 V²)`. -/
theorem integral_sq_sup_errorMartingale_stopped_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ}
    (hε : 0 < ε) (z : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    Integrable (fun f => (⨆ s : Set.Iic t,
          |errorMartingale θ ε (errStopTime n (supHitting θ z) s f) f|) ^ 2)
        (stableLocalLaw θ : Measure DLoc) ∧
      ∫ f, (⨆ s : Set.Iic t, |errorMartingale θ ε (errStopTime n (supHitting θ z) s f) f|) ^ 2
          ∂(stableLocalLaw θ : Measure DLoc) ≤
        4 * (4 * (z : ℝ) * supCorrectionBound θ ε + 12 * supCorrectionBound θ ε ^ 2) := sorry

/-! ### Removing the localization: estimates at `A^*_z` -/

/-- **Exact mean**: `E O_ε(A^*_z) = z` (uniform integrability from the `L²` bound; `A^*_z < ∞`
and `R_{A^*_z} = 0`), with integrability. -/
theorem integral_supOccupation_supAuxLadderTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ}
    (hε : 0 < ε) (z : ℝ≥0) :
    Integrable (fun f => supOccupation ε f (supAuxLadderTime θ z f))
        (stableLocalLaw θ : Measure DLoc) ∧
      ∫ f, supOccupation ε f (supAuxLadderTime θ z f) ∂(stableLocalLaw θ : Measure DLoc) =
        (z : ℝ) := sorry

/-- **Stopped energy at `A^*_z`**: `E (O_ε(A^*_z) - z)² ≤ 4 z V_ε + 12 V_ε²`. -/
theorem integral_sq_supOccupation_sub_supAuxLadderTime_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ε : ℝ} (hε : 0 < ε) (z : ℝ≥0) :
    Integrable (fun f => (supOccupation ε f (supAuxLadderTime θ z f) - (z : ℝ)) ^ 2)
        (stableLocalLaw θ : Measure DLoc) ∧
      ∫ f, (supOccupation ε f (supAuxLadderTime θ z f) - (z : ℝ)) ^ 2
          ∂(stableLocalLaw θ : Measure DLoc) ≤
        4 * (z : ℝ) * supCorrectionBound θ ε + 12 * supCorrectionBound θ ε ^ 2 := sorry

/-- **Stopped maximal estimate**:
`E sup_{t ≤ A^*_z}|O_ε(t) - M^*_t|² ≤ 104 (z V_ε + V_ε²)` (`O - M^* = D - w`, `|w| ≤ 2V`). -/
theorem integral_sq_sup_supOccupation_sub_supAuxLocalTime_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ε : ℝ} (hε : 0 < ε) (z : ℝ≥0) :
    Integrable (fun f => (⨆ t : Set.Iic (supAuxLadderTime θ z f),
          |supOccupation ε f t - supAuxLocalTime θ f t|) ^ 2)
        (stableLocalLaw θ : Measure DLoc) ∧
      ∫ f, (⨆ t : Set.Iic (supAuxLadderTime θ z f),
            |supOccupation ε f t - supAuxLocalTime θ f t|) ^ 2
          ∂(stableLocalLaw θ : Measure DLoc) ≤
        104 * ((z : ℝ) * supCorrectionBound θ ε + supCorrectionBound θ ε ^ 2) := sorry

/-- The energy bound vanishes with `ε` (`V_ε → 0`, fixed `z`). -/
theorem tendsto_stopped_energy_bound {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    Tendsto (fun ε : ℝ =>
        104 * ((z : ℝ) * supCorrectionBound θ ε + supCorrectionBound θ ε ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := sorry

/-! ### The three stopped statements of the final contract, in auxiliary form -/

/-- Auxiliary form of `supOccupation_stopped_L2_bound` (`A^*`, same shape). -/
theorem supOccupation_stopped_L2_bound_aux {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Integrable (fun f => (supOccupation ε f (supAuxLadderTime θ z f)) ^ 2)
          (stableLocalLaw θ : Measure DLoc) ∧
      ∫ f, (supOccupation ε f (supAuxLadderTime θ z f)) ^ 2 ∂(stableLocalLaw θ : Measure DLoc)
        ≤ C := sorry

/-- Auxiliary form of `supOccupation_stopped_L2_tendsto`. -/
theorem supOccupation_stopped_L2_tendsto_aux {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Integrable (fun f => (supOccupation ε f (supAuxLadderTime θ z f) - (z : ℝ)) ^ 2)
        (stableLocalLaw θ : Measure DLoc)) ∧
    Tendsto (fun ε : ℝ =>
        ∫ f, (supOccupation ε f (supAuxLadderTime θ z f) - (z : ℝ)) ^ 2
          ∂(stableLocalLaw θ : Measure DLoc)) (𝓝[>] (0 : ℝ)) (𝓝 0) := sorry

/-- Auxiliary form of `supOccupation_stopped_uniform_tendstoInMeasure` (Markov on the stopped
maximal estimate; `z = 0` is the same bound). -/
theorem supOccupation_stopped_uniform_tendstoInMeasure_aux {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (z : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun ε : ℝ =>
        (stableLocalLaw θ : Measure DLoc)
          {f | δ ≤ ⨆ t : Set.Iic (supAuxLadderTime θ z f),
              |supOccupation ε f t - supAuxLocalTime θ f t|})
      (𝓝[>] (0 : ℝ)) (𝓝 0) := sorry

end BGW.StableTrees
