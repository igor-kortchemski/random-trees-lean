import BGW.Skorokhod.DLoc
import BGW.Skorokhod.JumpDetection

/-! Contract probe for CT.C6 blueprint Node 10 (stopping-time enumeration of jumps), simplified
route of AUDIT item 3.

Sealed inputs reused: `DLoc.filtration` (right-continuous), `jumpSize`, `firstJumpAbove`,
`firstJumpAbove_lt_iff` (countable description of `{σ_{q,ε} < t}`), `exists_rat_firstJumpAbove_eq`
(every jump time is some `σ_{q,ε}`). No law is involved: purely deterministic path measurability.

Plan. `{σ_{q,ε} < t}` is a countable Boolean combination of the evaluations `f ↦ f b - f a` at
rational times `< t` (`firstJumpAbove_lt_iff`), hence lies in the raw `F_t ≤ F_t^+`; then
`isStoppingTime_of_measurableSet_lt_of_isRightContinuous`. The enumeration `J` is
`σ_{q,ε}` along `Encodable` enumeration of `ℚ≥0 × {ε : ℚ // 0 < ε}`.

Conventions. Jumps are of the path `f.1 : ℝ≥0 → ℝ`; the jump condition `f.1 t ≠ leftLim f.1 t`
is only asserted for `t > 0` (at `0` Mathlib's `leftLim` is junk, so `t = 0` is excluded). Stopping times take values in `WithTop ℝ≥0` (`ℝ≥0∞` is defeq; the cast is
`firstJumpAbove … : ℝ≥0∞` read as `WithTop ℝ≥0`). Estimate 250–450 lines. -/

open MeasureTheory Set Filter Function
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.Skorokhod

/-- **The time `σ_{q,ε}` is a stopping time** of the right-continuous filtration, for rational
`q ≥ 0` and rational `ε > 0` (formulated on `DLoc` paths, as a `WithTop ℝ≥0`-valued time). -/
theorem isStoppingTime_firstJumpAbove (q : ℚ≥0) {ε : ℚ} (hε : 0 < ε) :
    IsStoppingTime DLoc.filtration
      (fun f : DLoc => (firstJumpAbove (q : ℝ≥0) (ε : ℝ) f.1 : WithTop ℝ≥0)) := sorry

/-- **Jump enumeration.** There are countably many stopping times of `DLoc.filtration` such
that every path's every jump time `t > 0` is one of them. -/
theorem exists_jumpStoppingTimes :
    ∃ J : ℕ → DLoc → WithTop ℝ≥0,
      (∀ n, IsStoppingTime DLoc.filtration (J n)) ∧
      ∀ (f : DLoc) (t : ℝ≥0), 0 < t → f.1 t ≠ Function.leftLim f.1 t →
        ∃ n, J n f = (t : WithTop ℝ≥0) := sorry

end BGW.Skorokhod
