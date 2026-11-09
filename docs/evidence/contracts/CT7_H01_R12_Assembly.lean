import BGW.StableTrees.SupremumDrawdown
import BGW.StableTrees.SupremumReflectedFamily
import BGW.StableTrees.SupremumLocalTime
import BGW.Probability.DoobL2Resolvent
import BGW.StableTrees.StableLocalLaw
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import BGW.StableTrees.SupremumLadderTransform
import BGW.StableTrees.SupremumLadderRestart
import BGW.StableTrees.SupremumLocalTimeIdent
import BGW.StableTrees.SupremumStoppedEnergy

/-! Contract probe for H01 node R12 (blueprint R12 "Public assembly and exact coverage").
**R12 only assembles**: it introduces no new mathematics, no new definition and no new
estimate.  Every H01 statement of the FINAL contract `CT7_H01_SupremumLocalTime.lean` is
supplied by exactly one node below; the sealed definitions `supRunning`, `supReflected`,
`supOccupation`, `IsSupOccupationSeq`, `supLadderExponent` are imported unchanged
(`BGW/StableTrees/SupremumLocalTime.lean`).

EXACT COVERAGE TABLE (final statement -> supplying node).
| Final declaration | Supplier |
| --- | --- |
| `supRunning`, `supReflected`, `supOccupation`, `IsSupOccupationSeq` | sealed W49 (imported) |
| `supLadderExponent` | sealed W49 (imported) |
| `exists_isSupOccupationSeq`, `supEps`, `isSupOccupationSeq_supEps`, `supLocalTime` | R07 |
| `measurable_supLocalTime_uncurry`, `measurable_supLocalTime` | R07 |
| `stronglyAdapted_supLocalTime` | R07 |
| `ae_tendsto_supOccupation`, `ae_tendsto_supOccupation_uniform` | R07 |
| `supOccupation_tendstoInMeasure` | R07 |
| `ae_supLocalTime_spec`, `supLocalTimeStieltjes`, `ae_supLocalTimeStieltjes_support` | R07 |
| `ae_supLocalTime_const_of_lt` | R07 |
| `supLocalTimeInverse`, `supLadderTime`, `supLadderHeight`, `measurable_supLadder_uncurry` | R07 |
| `ae_supLadder_spec`, `exists_isStoppingTime_supLocalTimeInverse` | R07 |
| `ae_supRestart_at_ladderTime` | R08 |
| `integral_exp_neg_supLadder` (all three equalities) | R09 |
| `supOccupation_stopped_L2_bound` | R11 (`_aux` form) + R12 transfer |
| `supOccupation_stopped_L2_tendsto` | R11 (`_aux` form) + R12 transfer |
| `supOccupation_stopped_uniform_tendstoInMeasure` | R11 (`_aux` form) + R12 transfer |

The ONLY statements of the final contract not already proved verbatim by R07/R08/R09 are the
last three; they are restated below VERBATIM (diffed by script against the final contract) and
proved by transfer: R11 proves them for the auxiliary clock `M^* = supAuxLocalTime` and its
inverse `A^* = supAuxLadderTime`; R07 `ae_supLocalTime_eq_aux` and `ae_supLadder_eq_aux` give,
for one full-probability event and all times and levels simultaneously, `supLocalTime = M^*`,
`supLadderTime = A^*`.  Hence the integrands (including inside the random time `A_z`, i.e. the
evaluation `O_ε(A_z)` and the supremum over `Iic A_z`) and the events agree almost surely, and
integrals / measures coincide (`integral_congr_ae`, `measure_congr`); integrability transfers by
`Integrable.congr`.  Public inputs are never the contract probe: no proof module imports it.

FLAGS.
(1) Hypotheses: the three transferred statements carry `1 < θ ∧ θ ≤ 2`, exactly as in the final
contract.  (2) `ε ∈ (0, 1]` quantifiers of the final statements are kept; R11's `_aux` forms
are available for all `ε > 0` as well.  (3) Copied declarations are only those named in the
statements and transfer lemmas; theorems of R07/R11 are copied with `sorry`. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-! ### The three stopped statements of the final contract (verbatim) -/

/-- **Stopped second-moment bound**: for each level `z` there is `C` bounding, uniformly in
`ε ∈ (0, 1]`, the second moment of the approximation stopped at the ladder time `A_z`; the
squared approximation is integrable. -/
theorem supOccupation_stopped_L2_bound {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Integrable (fun f => (supOccupation ε f (supLadderTime θ z f)) ^ 2)
          (stableLocalLaw θ : Measure DLoc) ∧
      ∫ f, (supOccupation ε f (supLadderTime θ z f)) ^ 2 ∂(stableLocalLaw θ : Measure DLoc) ≤ C :=
  sorry

/-- **Stopped `L²` convergence**: `E[(supOccupation ε f (A_z) - z)²] → 0` as `ε ↓ 0`,
consistent with `M(A_z) = z`. The auxiliary clock is constructed from compact-time estimates
before the public choice of `supEps`; this public stopped theorem follows by the
identification of the public local time and the stopped energy estimate. -/
theorem supOccupation_stopped_L2_tendsto {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Integrable (fun f => (supOccupation ε f (supLadderTime θ z f) - (z : ℝ)) ^ 2)
        (stableLocalLaw θ : Measure DLoc)) ∧
    Tendsto (fun ε : ℝ =>
        ∫ f, (supOccupation ε f (supLadderTime θ z f) - (z : ℝ)) ^ 2
          ∂(stableLocalLaw θ : Measure DLoc)) (𝓝[>] (0 : ℝ)) (𝓝 0) := sorry

/-- **Stopped Cauchy bound**: the approximations stopped at `A_z` converge to `M(A_z) = z`
uniformly over the stopped time interval, in probability, as `ε ↓ 0` along the full filter. -/
theorem supOccupation_stopped_uniform_tendstoInMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0)
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun ε : ℝ =>
        (stableLocalLaw θ : Measure DLoc)
          {f | δ ≤ ⨆ t : Set.Iic (supLadderTime θ z f),
              |supOccupation ε f t - supLocalTime θ f t|})
      (𝓝[>] (0 : ℝ)) (𝓝 0) := sorry

end BGW.StableTrees
