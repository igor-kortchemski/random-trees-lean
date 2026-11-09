import BGW.Skorokhod.DLoc
import BGW.StableTrees.StableLocalLaw
import BGW.StableTrees.StableLocalMarkov

/-! Contract probe for CT.C6 blueprint Node 8 (first passage below a level, creeping,
escape to `-∞`; F1) for the spectrally POSITIVE local stable law `stableLocalLaw θ`.

Sealed inputs reused (not re-declared): `DLoc.strictPassageBelow`,
`DLoc.isStoppingTime_strictPassageBelow` (so the stopping property of `T_x` is not restated),
`martingale_exp_stableLocalLaw` (`exp(-u X_t - t u^θ)`), `ae_leftLim_le_stableLocalLaw`
(no negative jumps, P4), `DLoc.filtration`.

Sign conventions (checked against the Laplace exponent `E e^{-u X_t} = e^{t u^θ}`).
`T_x := strictPassageBelow (-x) = inf{t | X_t < -x}`, `x > 0`. Spectrally positive: all jumps are
upward, so the path crosses below `-x` CONTINUOUSLY (downward creeping): `X_{T_x} = -x` a.s.
(first passage ABOVE a level jumps over it; not asserted). The Laplace transform follows from
optional sampling for `M_t = exp(-u X_t - t u^θ)`, `u = q^{1/θ}`, `q > 0`:
`E[e^{-q T_x}] = e^{-x q^{1/θ}}` (`E[e^{-q T_x}; T_x<∞] = e^{-ux}` first, then `q ↓ 0` gives
`T_x < ∞` a.s.). `T_x` is genuinely valued in `WithTop ℝ≥0`; the Laplace statement uses
`untopD 0` which is faithful since `T_x < ∞` a.s. (asserted separately).
The blueprint states N08 for all levels simultaneously; the `x > 0` simultaneous form is used
here (`x = 0` needs N06 regularity: `T_0 = 0`, a separate statement).
Stationary independent increments of `x ↦ T_x` are N09 (strong Markov), not stated here.
Estimate 600–1000 lines (sampling via Mathlib dyadic optional stopping, AUDIT item 4). -/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees

/-- The running infimum `I_t = inf_{u ≤ t} X_u` of a local path. -/
noncomputable def runningInfLoc (f : DLoc) (t : ℝ≥0) : ℝ := ⨅ u : Set.Iic t, f.1 u

/-- **Finite first passage.** Almost surely, simultaneously for every level `x > 0`,
`T_x = inf{t | X_t < -x}` is finite. -/
theorem ae_strictPassageBelow_ne_top {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : DLoc ∂(stableLocalLaw θ : Measure DLoc),
      ∀ x : ℝ, 0 < x → DLoc.strictPassageBelow (-x) f ≠ ⊤ := sorry

/-- **Downward creeping.** Almost surely, for every level `x > 0` the first passage below `-x`
occurs continuously: `X_{T_x} = -x`. -/
theorem ae_creeping_down_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : DLoc ∂(stableLocalLaw θ : Measure DLoc),
      ∀ x : ℝ, 0 < x →
        ∃ t : ℝ≥0, DLoc.strictPassageBelow (-x) f = (t : WithTop ℝ≥0) ∧ f.1 t = -x := sorry

/-- **Running infimum.** Almost surely `I` is continuous, nonincreasing and tends to `-∞`. -/
theorem ae_runningInf_continuous_antitone_tendsto {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : DLoc ∂(stableLocalLaw θ : Measure DLoc),
      Continuous (runningInfLoc f) ∧ Antitone (runningInfLoc f) ∧
        Tendsto (runningInfLoc f) atTop atBot := sorry

/-- **Laplace transform of the passage time.** For `x > 0`, `q ≥ 0`:
`E[e^{-q T_x}] = e^{-x q^{1/θ}}` (with `T_x` finite a.s., read via `untopD 0`). -/
theorem integral_exp_neg_strictPassageBelow {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {x q : ℝ}
    (hx : 0 < x) (hq : 0 ≤ q) :
    ∫ f : DLoc, Real.exp (-q * (((DLoc.strictPassageBelow (-x) f).untopD 0 : ℝ≥0) : ℝ))
        ∂(stableLocalLaw θ : Measure DLoc) = Real.exp (-x * q ^ (1 / θ)) := sorry

/-- The first passage time below `-x`, as a process indexed by the level `x ≥ 0`. -/
noncomputable def firstPassageBelow (x : ℝ≥0) (f : DLoc) : WithTop ℝ≥0 :=
  DLoc.strictPassageBelow (-(x : ℝ)) f

/-- Each first passage time is a stopping time of the right-continuous filtration. -/
theorem isStoppingTime_firstPassageBelow (x : ℝ≥0) :
    IsStoppingTime DLoc.filtration (firstPassageBelow x) := sorry

/-- Joint measurability of the first passage times in the level and the path. -/
theorem measurable_firstPassageBelow_uncurry :
    Measurable (fun p : ℝ≥0 × DLoc => firstPassageBelow p.1 p.2) := sorry

/-- **Joint almost-sure event.** Almost surely, the path starts at `0` and, simultaneously for
every level `x > 0`, the first passage below `-x` is finite, positive, and the path takes the
value `-x` there. -/
theorem ae_firstPassageBelow_spec {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), f.1 0 = 0 ∧ ∀ x : ℝ≥0, 0 < x →
      firstPassageBelow x f < ⊤ ∧ 0 < firstPassageBelow x f ∧
        f.1 ((firstPassageBelow x f).untopD 0) = -(x : ℝ) := sorry

/-- **Laplace transform, nonnegative form.** For `x > 0`, `q ≥ 0`. -/
theorem lintegral_exp_neg_firstPassageBelow {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {x : ℝ≥0}
    (hx : 0 < x) {q : ℝ} (hq : 0 ≤ q) :
    ∫⁻ f, ENNReal.ofReal (Real.exp (-q * (((firstPassageBelow x f).untopD 0 : ℝ≥0) : ℝ)))
        ∂(stableLocalLaw θ : Measure DLoc) =
      ENNReal.ofReal (Real.exp (-(x : ℝ) * q ^ (1 / θ))) := sorry

end BGW.StableTrees
