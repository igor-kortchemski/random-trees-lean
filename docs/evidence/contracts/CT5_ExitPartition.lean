import BGW.Skorokhod.Tightness
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Filter.AtTopBot.Basic

/-! Contract probe for CT.C16/C17 route, blueprint Node 8 (deterministic exit partition bound for
Billingsley's `w'`) with the definitions it needs from Nodes 2 and 7: the real step path
`t ↦ S_{⌊n t⌋} / b` in `D T ℝ`, restart exit times (first exit from radius `r` after the
previous exit), exit counts, close consecutive exits and the initial/terminal window events.
Maintained files: `BGW/Skorokhod/RealStepPath.lean`, `BGW/Probability/RealWalkExits.lean`,
`BGW/Skorokhod/ExitPartition.lean`. -/

open Filter Set

namespace BGW.Probability.RealWalk

-- copied from contract CT5_RealWalk (not part of this contract)
def partialSum (ω : ℕ → ℝ) (m : ℕ) : ℝ := ∑ i ∈ Finset.range m, ω i

open Classical in
/-- The first index `k ∈ (a, M]` with `|S_k - S_a| > r`, and the sentinel `M + 1` if none. -/
noncomputable def nextExit (M : ℕ) (r : ℝ) (ω : ℕ → ℝ) (a : ℕ) : ℕ :=
  if h : ∃ k, a < k ∧ k ≤ M ∧ r < |partialSum ω k - partialSum ω a| then Nat.find h else M + 1

/-- Restart exit times: `exitTimes M r ω 0 = 0` and the `(j+1)`-st exit is the first exit of the
walk restarted at the `j`-th one; the sentinel `M + 1` (absorbing) means "no further exit up to
index `M`". Actual exits are `≤ M`. -/
noncomputable def exitTimes (M : ℕ) (r : ℝ) (ω : ℕ → ℝ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => if exitTimes M r ω j ≤ M then nextExit M r ω (exitTimes M r ω j) else M + 1

open Classical in
/-- The number of actual exits (indices `≤ M`, not counting the starting point `0`). -/
noncomputable def exitCount (M : ℕ) (r : ℝ) (ω : ℕ → ℝ) : ℕ :=
  ((Finset.range (M + 1)).filter (fun j => 1 ≤ j ∧ exitTimes M r ω j ≤ M)).card

/-- Two successive actual exits (the first being a genuine exit, `j ≥ 1`) are at most `l`
indices apart. The gap between the start `0` and the first exit is deliberately not covered
(it is the `initialBad` event). -/
def closeExit (M : ℕ) (r : ℝ) (l : ℕ) (ω : ℕ → ℝ) : Prop :=
  ∃ j : ℕ, 1 ≤ j ∧ exitTimes M r ω (j + 1) ≤ M ∧
    exitTimes M r ω (j + 1) - exitTimes M r ω j ≤ l

/-- The step path value `S_{⌊n t⌋} / b` at a real time `t`. -/
noncomputable def stepValue (n : ℕ) (b : ℝ) (ω : ℕ → ℝ) (t : ℝ) : ℝ :=
  partialSum ω ⌊(n : ℝ) * t⌋₊ / b

/-- Initial window: the path moves by more than `ε` from its start within time `2δ`. -/
def initialBad (T : ℝ) (n : ℕ) (b ε δ : ℝ) (ω : ℕ → ℝ) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ t ≤ 2 * δ ∧ t ≤ T ∧ ε < |stepValue n b ω t - stepValue n b ω 0|

/-- Terminal window: after time `T - 2δ` the path moves by more than `ε` from its value at
`T - 2δ` (measured from the left endpoint of the window, up to and including `T`). -/
def terminalBad (T : ℝ) (n : ℕ) (b ε δ : ℝ) (ω : ℕ → ℝ) : Prop :=
  ∃ t : ℝ, T - 2 * δ ≤ t ∧ t ≤ T ∧
    ε < |stepValue n b ω t - stepValue n b ω (T - 2 * δ)|

/-- Blueprint's `edgeBad`. -/
def edgeBad (T : ℝ) (n : ℕ) (b ε δ : ℝ) (ω : ℕ → ℝ) : Prop :=
  initialBad T n b ε δ ω ∨ terminalBad T n b ε δ ω

end BGW.Probability.RealWalk

namespace BGW.Skorokhod

open BGW.Probability.RealWalk

/-- The càdlàg floor-step path `t ↦ S_{⌊n t⌋} / b` on `[0,T]` (Node 2). The same formula is used
at `T`: if `n T` is an integer there is a genuine terminal jump. -/
noncomputable def realStepPath (T : ℝ) (n : ℕ) (b : ℝ) (ω : ℕ → ℝ) : D T ℝ where
  toFun t := partialSum ω ⌊(n : ℝ) * (t : ℝ)⌋₊ / b
  isCadlag' := sorry

theorem realStepPath_apply {T : ℝ} {n : ℕ} {b : ℝ} {ω : ℕ → ℝ} (t : Set.Icc (0 : ℝ) T) :
    realStepPath T n b ω t = partialSum ω ⌊(n : ℝ) * (t : ℝ)⌋₊ / b := rfl

theorem realStepPath_apply_eq_stepValue {T : ℝ} {n : ℕ} {b : ℝ} {ω : ℕ → ℝ}
    (t : Set.Icc (0 : ℝ) T) : realStepPath T n b ω t = stepValue n b ω t := rfl

/-- Node 8, deterministic bound. Hypotheses (i) no close consecutive exits at scale `ε b`, with
index gap `l = ⌈2 n δ + 2⌉₊` (so that consecutive cuts are more than `2δ` apart in time, the
`+2` absorbing the floors), (ii) no big initial move, (iii) no big terminal move. The exits
live in the walk of length `M = ⌊n T⌋₊`. Conclusion: `w'(δ) ≤ 4 ε` for Billingsley's modulus
(half-open blocks, all steps `> δ`, `δ < T`). -/
theorem cadlagModulus_realStepPath_le {T : ℝ} {n : ℕ} {b ε δ : ℝ} {ω : ℕ → ℝ}
    (hT : 0 < T) (hn : 1 ≤ n) (hb : 0 < b) (hε : 0 < ε) (hδ : 0 < δ) (hδT : 4 * δ < T)
    (hsep : ¬ closeExit ⌊(n : ℝ) * T⌋₊ (ε * b) ⌈2 * n * δ + 2⌉₊ ω)
    (hinit : ¬ initialBad T n b ε δ ω)
    (hterm : ¬ terminalBad T n b ε δ ω) :
    cadlagModulus (realStepPath T n b ω) δ ≤ 4 * ε := sorry

end BGW.Skorokhod
