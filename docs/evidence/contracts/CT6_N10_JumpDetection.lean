import Mathlib.Topology.Order.Cadlag
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Data.NNRat.Defs
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Contract probe for CT6 blueprint N10 (jump enumeration), in the corrected form of
`r2-ct6-blueprint/AUDIT.md` item 3: `σ_{q,ε} = inf {t > q : |Δx_t| > ε}`, no k-th-jump counting.

Maintained file (proposed): `BGW/Skorokhod/JumpDetection.lean`; Mathlib-only (no BGW import), so
CT7 can apply it to `x ↦ T_x`.

Conventions.
* `x : ℝ≥0 → ℝ` is arbitrary `IsCadlag`; the jump at `t` is `x t - Function.leftLim x t`
  (`leftLim x 0 = x 0`, so there is no jump at `0`).
* `firstJumpAbove q ε x : ℝ≥0∞` is the infimum of `{t | q < t ∧ ε < |jump at t|}` with coercion
  `ℝ≥0 → ℝ≥0∞`; the empty set gives `⊤` (`iInf` over the empty set), `WithTop ℝ≥0 = ℝ≥0∞`.
  Both the `q < t` and `ε < |Δ|` are STRICT.
* Rational data: `q : ℚ≥0` and `ε : ℚ` (cast to `ℝ≥0`, `ℝ`); the `a b` of the characterization
  are `ℚ≥0`.
* Mathlib does not (at this pin) contain finiteness of ε-jumps for càdlàg functions on `ℝ≥0`
  (only boundedness `IsCadlag.isLocallyBounded`, `isBounded_image_of_isCadlag_of_isCompact`);
  the BGW version `Skorokhod.finite_setOf_jump_gt` is for `D T E` on `Icc 0 T`, so it is
  restated here (`finite_setOf_jump_gt_cadlag`).
* Endpoint check for (b) (⇐): a cluster point `c` of the pairs satisfies `q < c < t` when the
  pair straddles `c`; pairs both `≥ c` contradict right-continuity (this covers `c = q`), pairs
  both `< c` contradict existence of the left limit (this covers `c = t`, as `b < t`). So the
  characterization is true with all inequalities `q < a < b < t` strict, `t = 0` gives both sides
  false. -/

open Filter Function
open scoped Topology NNReal ENNReal

namespace BGW.Skorokhod

/-- The absolute jump of `x` at `t`. -/
noncomputable def jumpSize (x : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ := |x t - Function.leftLim x t|

/-- The first time after `q` at which `x` jumps by more than `ε` (`⊤` if there is none). -/
noncomputable def firstJumpAbove (q : ℝ≥0) (ε : ℝ) (x : ℝ≥0 → ℝ) : ℝ≥0∞ :=
  ⨅ t ∈ {t : ℝ≥0 | q < t ∧ ε < jumpSize x t}, (t : ℝ≥0∞)

/-- Finiteness: a càdlàg function has finitely many jumps larger than `ε > 0` on `[0, T]`. -/
theorem finite_setOf_jump_gt_cadlag {x : ℝ≥0 → ℝ} (hx : IsCadlag x) {ε : ℝ} (hε : 0 < ε)
    (T : ℝ≥0) : {t : ℝ≥0 | t ≤ T ∧ ε < jumpSize x t}.Finite := by
  sorry

/-- (a) The infimum is `⊤` iff there is no jump, and otherwise it is attained: it is a jump time
`s > q` with jump larger than `ε`, and no earlier such time exists. -/
theorem firstJumpAbove_eq_top_iff (x : ℝ≥0 → ℝ) (q : ℝ≥0) (ε : ℝ) :
    firstJumpAbove q ε x = ⊤ ↔ ∀ t, q < t → jumpSize x t ≤ ε := by
  sorry

theorem firstJumpAbove_attained {x : ℝ≥0 → ℝ} (hx : IsCadlag x) (q : ℝ≥0) {ε : ℝ}
    (hε : 0 < ε) {s : ℝ≥0} (hs : firstJumpAbove q ε x = s) :
    q < s ∧ ε < jumpSize x s ∧ ∀ t, q < t → ε < jumpSize x t → s ≤ t := by
  sorry

/-- (b) Countable characterization of `{σ_{q,ε} < t}` for a fixed càdlàg path. -/
theorem firstJumpAbove_lt_iff {x : ℝ≥0 → ℝ} (hx : IsCadlag x) (q : ℚ≥0) {ε : ℚ}
    (hε : 0 < ε) (t : ℝ≥0) :
    firstJumpAbove (q : ℝ≥0) (ε : ℝ) x < (t : ℝ≥0∞) ↔
      ∃ ε' : ℚ, ε < ε' ∧ ∀ n : ℕ, ∃ a b : ℚ≥0,
        q < a ∧ a < b ∧ (b : ℝ≥0) < t ∧ ((b : ℝ) - a < 1 / (n + 1)) ∧
          (ε' : ℝ) ≤ |x (b : ℝ≥0) - x (a : ℝ≥0)| := by
  sorry

/-- (c) Every jump time `s > 0` is `σ_{q,ε}` for rational `q ≥ 0`, `ε > 0`. -/
theorem exists_rat_firstJumpAbove_eq {x : ℝ≥0 → ℝ} (hx : IsCadlag x) {s : ℝ≥0} (hs : 0 < s)
    (hj : x s ≠ Function.leftLim x s) :
    ∃ (q : ℚ≥0) (ε : ℚ), 0 < ε ∧ firstJumpAbove (q : ℝ≥0) (ε : ℝ) x = (s : ℝ≥0∞) := by
  sorry

end BGW.Skorokhod
