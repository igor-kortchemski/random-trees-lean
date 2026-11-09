import BGW.StableTrees.SupremumDrawdown
import BGW.StableTrees.SupremumReflectedFamily
import BGW.StableTrees.SupremumLocalTime
import BGW.StableTrees.StableLocalLaw
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import BGW.StableTrees.SupremumPotential
import BGW.StableTrees.SupremumLadderRestart
import BGW.StableTrees.SupremumLadderTransform

/-! Contract probe for H01 node R10 (blueprint R10 "Zero-resolvent correction and its
martingale", §3 "A bounded correction supplies the stopped estimates"; AUDIT sol-audit-r04
finding 2: R10 consumes `condExp_reflectedResolvent_tail` from R04 and LOCALIZES BEFORE `q ↓ 0`).
It defines the occupation-error process of the auxiliary clock `M^* = supAuxLocalTime` (R06),
`D_t = O_ε(t) - M^*_t + v_ε(R_t) - v_ε(0)`, proves that `D` stopped at ANY stopping time and at
the localizing cutoff `errCutoff n` is a martingale, and records what R11 consumes.
NOT redefined (sealed, imported): `supRunning`, `supReflected`, `supOccupation`,
`supReflectedFrom`, `supReflectedFrom_nonneg`, `supReflectedFrom_zero_apply`,
`ae_supReflectedFrom_le_leftLim`, `measurable_rawFiltration_supReflectedFrom`,
`measurable_rawFiltration_supOccupation`, `continuous_supOccupation` (R01), `expClockLaw` (R02a).
Definitions copied verbatim: from R04 `stableScale`, `supExpTail`, `supPotential`, `supOccKernel`,
`reflectedResolvent`, `supOccupationResolvent`, `supCorrection`; from R05/R06 the chain
`compactError … supAuxLimit`, `supAuxLocalTime`, `pathStieltjes`, `supAuxStieltjes`.
Suppliers consumed by the PROOFS (not restated): R04 `condExp_reflectedResolvent_tail`,
`tendstoLocallyUniformlyOn_supOccupationResolvent_sub`, `abs_supCorrection_le`,
`continuousOn_supCorrection`, `supCorrection_zero`, `supOccupationResolvent_mem_Icc`,
`supPotential_mem_Icc`; R05 `ae_supOccupation_eq_integral_supOccKernel`,
`measurable_supAuxLimit_uncurry`, `stronglyAdapted_supAuxLimit`, `integrable_sq_supAuxLimit`;
R06 `ae_supAuxLocalTime_spec`, `condExp_supAuxDiscountedTail`, `integrable_supAuxDiscountedTail`,
`integral_supAuxDiscountedTail_zero`; Mathlib `Martingale`, bounded conditional expectation.

Mathematics (hand-checked).  `R_t = R^0_t`.  For `q > 0` put `O^q_t = ∫_0^t e^{-qs} g_ε(R_s) ds`
and `M^q_t = ∫_{(0,t]} e^{-qs} dM^*_s`.  Then
`E[O^q_∞ - M^q_∞ | F_t] = O^q_t - M^q_t + e^{-qt}(u^q_ε - h_q)(R_t)` (R04 tail identity for
`k = g_ε`; R06 tail identity for the clock), a martingale `N^q`.  `q ↓ 0`: `O^q_t → O_ε(t)`,
`M^q_t → M^*_t`, `(u^q_ε - h_q)(y) → v_ε(y)` locally uniformly in `y ≥ 0`.  Domination is only
available while `R ≤ K`; since `R` has no positive jumps (`R ≤ leftLim R`), the stopped process at
`τ_K = inf{t | R_t > K}` satisfies `R ≤ K` (this is why the cutoff is built in).  Subtracting
the constant `v_ε(0) = -1_{θ=2} ε/2` gives `D`.
CONSTANT CHECKS.  `θ = 2`: `W(y) = y`, `v_ε(y) = -(ε-y)_+²/(2ε)` (both ranges `y ≥ ε`, `y < ε`
checked), `v_ε(0) = -ε/2`, `sup|v_ε| = ε/2 ≤ V_ε = (1/Γ(2)+1/2) ε = 3ε/2`.  `θ < 2`: `v_ε(0) = 0`.
`|w_t| = |v_ε(R_t) - v_ε(0)| ≤ 2 V_ε` (`V_ε = (1/Γ(θ)+1/2) ε^{θ-1}`, R04's explicit constant `C_θ`;
the blueprint's `V_ε = sup|v_ε|` is smaller, all its inequalities `E O ≤ z+2V`,
`E D² ≤ 4zV + 12V²` stay true with the larger `V`).  `w = 0` on the contact set `{R = 0}`.
Brownian correction: `Φ h_q(0) = q^{2/θ-1} → 1_{θ=2}`; `Φ³/q = q^{3/θ-1} → 0`, so the
constant is `-1_{θ=2}ε/2`, matching `supCorrection`.  No numerical inconsistency found; the
blueprint's `W((x-r)_+)` equals R04's `stableScale θ (x - r)` (both vanish for negative
argument, `W(0) = 0` since `θ > 1`).
FLAGS.
(1) The clock part of the discounted process is written by INTEGRATION BY PARTS
(`supAuxDiscountedHead`), not as a Stieltjes integral: `supAuxStieltjes` is junk (`0`) on the null
set where `M^*` fails to be monotone and continuous, which is a property of the WHOLE path, so a
Stieltjes-defined process would not be adapted everywhere (raw filtration, no completion).
`ae_supAuxDiscountedHead_eq` links the two a.s. at all `t`.
(2) Stopped processes need PROGRESSIVE measurability of `D` (everywhere), not only adaptedness:
`M^*` is a raw `limsup` of continuous adapted processes, hence progressive
(`isStronglyProgressive_errorMartingale`); right continuity of `D` holds only a.s.
(3) Blueprint's `Martingale (… min t (cutoff n f) …)` is generalized to stopping at
`min (min t σ) (cutoff n)` for an ARBITRARY stopping time `σ`, as R11 stops further at the inverse
level (`supHitting`); `σ = ⊤` is the blueprint statement.  Optional sampling in continuous time is
proved here via a.s. right continuity and dyadic approximation (Mathlib's is discrete).
(4) `cutoff n = min (τ_n) n` has both levels equal; it is `⊤`-divergent for EVERY path
(`R` is bounded on compacts), not only a.s.
(5) Estimate 550-1000 lines. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-! ### Copied definitions -/

open scoped Classical in
open scoped Classical in
/-! ### Definitions of this node -/

/-- `V_ε = (1/Γ(θ) + 1/2) ε^{θ-1}`: R04's explicit bound for `sup_{y ≥ 0} |v_ε(y)|`. -/
noncomputable def supCorrectionBound (θ ε : ℝ) : ℝ := (1 / Real.Gamma θ + 1 / 2) * ε ^ (θ - 1)

/-- The correction increment `w_t = v_ε(R_t) - v_ε(0)`, `R_t = R^0_t`. -/
noncomputable def occupationCorrection (θ ε : ℝ) (t : ℝ≥0) (f : DLoc) : ℝ :=
  supCorrection θ ε (supReflectedFrom 0 f t) - supCorrection θ ε 0

/-- **The error process** `D_t = O_ε(t) - M^*_t + v_ε(R_t) - v_ε(0)` (blueprint §3,
`errorMartingale`), with `M^* = supAuxLocalTime`. -/
noncomputable def errorMartingale (θ ε : ℝ) (t : ℝ≥0) (f : DLoc) : ℝ :=
  (supOccupation ε f t - supAuxLocalTime θ f t) + occupationCorrection θ ε t f

/-- Discounted head of the clock, `∫_{(0,t]} e^{-qs} dM^*_s`, by integration by parts
(`M^*_0 = 0`): `e^{-qt} M^*_t + q ∫_0^t e^{-qs} M^*_s ds`.  Adapted for every path. -/
noncomputable def supAuxDiscountedHead (θ q : ℝ) (t : ℝ≥0) (f : DLoc) : ℝ :=
  Real.exp (-q * t) * supAuxLocalTime θ f t +
    q * ∫ s in Ioc (0 : ℝ) t, Real.exp (-q * s) * supAuxLocalTime θ f s.toNNReal

/-- Discounted head of the occupation, `O^q_t = ∫_0^t e^{-qs} g_ε(R^0_s) ds`. -/
noncomputable def supOccupationDiscountedHead (q ε : ℝ) (t : ℝ≥0) (f : DLoc) : ℝ :=
  ∫ s in Ioc (0 : ℝ) t, Real.exp (-q * s) * supOccKernel ε (supReflectedFrom 0 f s.toNNReal)

/-- **Positive-rate error martingale**
`N^q_t = O^q_t - M^q_t + e^{-qt} (u^q_ε - h_q)(R_t)`. -/
noncomputable def discountedErrorMartingale (θ q ε : ℝ) (t : ℝ≥0) (f : DLoc) : ℝ :=
  (supOccupationDiscountedHead q ε t f - supAuxDiscountedHead θ q t f) +
    Real.exp (-q * t) * (supOccupationResolvent θ q ε (supReflectedFrom 0 f t) -
      supPotential θ q (supReflectedFrom 0 f t))

/-- Strict exit time `τ_K = inf{t | R^0_t > K}` (`⊤` if never). -/
noncomputable def supReflectedExit (K : ℝ) (f : DLoc) : ℝ≥0∞ :=
  ⨅ t : ℝ≥0, if K < supReflectedFrom 0 f t then (t : ℝ≥0∞) else ⊤

/-- The localizing cutoff `min (τ_n) n` (independent of the inverse clock). -/
noncomputable def errCutoff (n : ℕ) (f : DLoc) : ℝ≥0∞ :=
  min (supReflectedExit (n : ℝ) f) (n : ℝ≥0∞)

/-- The stopping epoch `min (min t σ) (cutoff n)` as a finite time. -/
noncomputable def errStopTime (n : ℕ) (σ : DLoc → ℝ≥0∞) (t : ℝ≥0) (f : DLoc) : ℝ≥0 :=
  (min (min (t : ℝ≥0∞) (σ f)) (errCutoff n f)).toNNReal

/-! ### The correction `v_ε`: measurability, bound, contact set -/

theorem measurable_supCorrection (θ ε : ℝ) : Measurable (supCorrection θ ε) := sorry

/-- `|w_t| ≤ 2 V_ε` for every path and time (`R ≥ 0` always; R04 `abs_supCorrection_le`). -/
theorem abs_occupationCorrection_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ} (hε : 0 < ε)
    (t : ℝ≥0) (f : DLoc) : |occupationCorrection θ ε t f| ≤ 2 * supCorrectionBound θ ε := sorry

/-- `w = 0` where the reflected process vanishes (so `w` kills the `dM^*` part, which is
supported on `{R = 0}`). -/
theorem occupationCorrection_eq_zero {θ ε : ℝ} {t : ℝ≥0} {f : DLoc}
    (h : supReflectedFrom 0 f t = 0) : occupationCorrection θ ε t f = 0 := sorry

/-- `V_ε ≤ C_θ ε^{θ-1}` is the defining constant; it tends to `0` as `ε ↓ 0`. -/
theorem tendsto_supCorrectionBound {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    Tendsto (supCorrectionBound θ) (𝓝[>] 0) (𝓝 0) := sorry

/-! ### Localizing cutoff -/

theorem isStoppingTime_supReflectedExit (K : ℝ) :
    IsStoppingTime DLoc.filtration (supReflectedExit K) := sorry

theorem isStoppingTime_errCutoff (n : ℕ) : IsStoppingTime DLoc.filtration (errCutoff n) := sorry

theorem errCutoff_le (n : ℕ) (f : DLoc) : errCutoff n f ≤ n := sorry

theorem monotone_errCutoff (f : DLoc) : Monotone (fun n : ℕ => errCutoff n f) := sorry

/-- The cutoffs diverge for EVERY path (the reflected path is bounded on compacts). -/
theorem tendsto_errCutoff_top (f : DLoc) :
    Tendsto (fun n : ℕ => errCutoff n f) atTop (𝓝 ⊤) := sorry

/-- Up to the cutoff the reflected process is `≤ n`, almost surely, simultaneously in `n`, `t`
(no positive jumps: `R ≤ leftLim R`; `R_0 = 0`). -/
theorem ae_supReflectedFrom_le_of_le_errCutoff {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ (n : ℕ) (t : ℝ≥0),
      (t : ℝ≥0∞) ≤ errCutoff n f → supReflectedFrom 0 f t ≤ n := sorry

/-! ### Pathwise structure of `D` -/

/-- Almost surely the integration-by-parts head is the Stieltjes integral of `dM^*`,
at all times simultaneously. -/
theorem ae_supAuxDiscountedHead_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      supAuxDiscountedHead θ q t f =
        ∫ s in Ioc (0 : ℝ) t, Real.exp (-q * s) ∂(supAuxStieltjes θ f).measure := sorry

theorem isStronglyProgressive_errorMartingale {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ}
    (hε : 0 < ε) :
    IsStronglyProgressive DLoc.filtration (fun t f => errorMartingale θ ε t f) := sorry

theorem isStronglyProgressive_discountedErrorMartingale {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) :
    IsStronglyProgressive DLoc.filtration (fun t f => discountedErrorMartingale θ q ε t f) :=
  sorry

/-- `D_0 = 0` almost surely (`O_ε(0) = 0`, `M^*_0 = 0`, `R_0 = 0`). -/
theorem ae_errorMartingale_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), errorMartingale θ ε 0 f = 0 := sorry

/-- Almost surely every path of `D` is right continuous (`O_ε` continuous, `M^*` continuous,
`v_ε` continuous on `[0,∞)`, `R` càdlàg). -/
theorem ae_rightContinuous_errorMartingale {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s => errorMartingale θ ε s f) (Ici t) t := sorry

/-! ### Positive rate and the passage `q ↓ 0` -/

/-- **Positive-rate martingale**: for `q > 0`, `N^q` is a martingale
(`E[O^q_∞ - M^q_∞ | F_t]`; R04 `condExp_reflectedResolvent_tail` for `k = g_ε`, R06
`condExp_supAuxDiscountedTail`, `O_ε = ∫ g_ε(R)`). -/
theorem martingale_discountedErrorMartingale {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) :
    Martingale (fun t f => discountedErrorMartingale θ q ε t f) DLoc.filtration
      (stableLocalLaw θ : Measure DLoc) := sorry

/-- **Centered zero-rate limit**: `N^q_t - (u^q_ε(0) - h_q(0)) → D_t` as `q ↓ 0`, almost surely
at all `t` (the uncentered limit is `D_t + v_ε(0)`, and `v_ε(0) = -ε/2 ≠ 0` when `θ = 2`).  Uses
the locally uniform limit `u^q_ε - h_q → v_ε` on `[0, sup_{s ≤ t} R_s]`. -/
theorem ae_tendsto_discountedErrorMartingale {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      Tendsto (fun q : ℝ => discountedErrorMartingale θ q ε t f -
          (supOccupationResolvent θ q ε 0 - supPotential θ q 0))
        (𝓝[>] 0) (𝓝 (errorMartingale θ ε t f)) := sorry

/-- **Uniform domination before `q ↓ 0`**, simultaneous in time on `[0, T]`: at every time
`s ≤ T` where the reflected state is at most `K`, `|N^q_s| ≤ T/ε + M^*_T + C` for `q ∈ (0, q₀)`
(one exceptional set for all `s`, so it can be evaluated at stopping epochs). -/
theorem ae_abs_discountedErrorMartingale_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ}
    (hε : 0 < ε) (K : ℝ) (T : ℝ≥0) :
    ∃ q₀ C : ℝ, 0 < q₀ ∧
      ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
        ∀ s : ℝ≥0, s ≤ T → supReflectedFrom 0 f s ≤ K →
          ∀ q : ℝ, 0 < q → q < q₀ →
            |discountedErrorMartingale θ q ε s f| ≤
              (T : ℝ) / ε + supAuxLocalTime θ f T + C := sorry

/-! ### The localized martingale (blueprint R10, main statement) -/

/-- **`D` stopped at `min σ (cutoff n)` is a martingale**, for every stopping time `σ` of the
right-continuous filtration and every `n` (`σ = ⊤` gives the blueprint's
`min t (cutoff n f)`).  Proof: localize `R ≤ n` (cutoff), pass `q ↓ 0` by dominated
convergence in `N^q`, then optional sampling via a.s. right continuity. -/
theorem martingale_errorMartingale_stopped {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ} (hε : 0 < ε)
    (n : ℕ) {σ : DLoc → ℝ≥0∞} (hσ : IsStoppingTime DLoc.filtration σ) :
    Martingale (fun t f => errorMartingale θ ε (errStopTime n σ t f) f) DLoc.filtration
      (stableLocalLaw θ : Measure DLoc) := sorry

/-- Square integrability of the stopped process: `|D_{t∧σ∧cutoff}| ≤ t/ε + M^*_t + 2 V_ε`
(`O_ε ≤ t/ε`, `M^*` monotone a.s., `|w| ≤ 2V_ε`); in particular `∫ D^2 < ∞`
(`integrable_sq_supAuxLimit`). -/
theorem integrable_sq_errorMartingale_stopped {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ}
    (hε : 0 < ε) (n : ℕ) {σ : DLoc → ℝ≥0∞} (hσ : IsStoppingTime DLoc.filtration σ)
    (t : ℝ≥0) :
    Integrable (fun f => (errorMartingale θ ε (errStopTime n σ t f) f) ^ 2)
      (stableLocalLaw θ : Measure DLoc) := sorry

/-- **Mean zero** at a bounded stopping epoch: `E D_{t∧σ∧cutoff} = D_0 = 0`. -/
theorem integral_errorMartingale_stopped {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ} (hε : 0 < ε)
    (n : ℕ) {σ : DLoc → ℝ≥0∞} (hσ : IsStoppingTime DLoc.filtration σ) (t : ℝ≥0) :
    ∫ f, errorMartingale θ ε (errStopTime n σ t f) f ∂(stableLocalLaw θ : Measure DLoc) = 0 :=
  sorry

/-- **Mean occupation at a stopped epoch** (R11 input, blueprint `E[O_ε(τ)] ≤ z + 2 V_ε`):
`E[O_ε(τ') - M^*_{τ'}] = - E[w_{τ'}]` and hence `E O_ε(τ') ≤ E M^*_{τ'} + 2 V_ε`, with
`τ' = errStopTime n σ t`. -/
theorem integral_supOccupation_stopped_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ} (hε : 0 < ε)
    (n : ℕ) {σ : DLoc → ℝ≥0∞} (hσ : IsStoppingTime DLoc.filtration σ) (t : ℝ≥0) :
    (∫ f, (supOccupation ε f (errStopTime n σ t f) - supAuxLocalTime θ f (errStopTime n σ t f))
        ∂(stableLocalLaw θ : Measure DLoc) =
      -∫ f, occupationCorrection θ ε (errStopTime n σ t f) f ∂(stableLocalLaw θ : Measure DLoc)) ∧
    ∫ f, supOccupation ε f (errStopTime n σ t f) ∂(stableLocalLaw θ : Measure DLoc) ≤
      ∫ f, supAuxLocalTime θ f (errStopTime n σ t f) ∂(stableLocalLaw θ : Measure DLoc) +
        2 * supCorrectionBound θ ε := sorry

end BGW.StableTrees
