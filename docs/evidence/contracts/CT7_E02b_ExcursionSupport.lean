import BGW.Skorokhod.DLocShiftAt
import BGW.StableTrees.ReflectedRestart
import BGW.StableTrees.StablePassageSubordinator
import BGW.StableTrees.StablePassageSubordinatorStieltjes
import BGW.StableTrees.StablePassageSubordinatorIncrements
import BGW.StableTrees.StableContinuousMinimum
import BGW.StableTrees.StableStrongMarkov
import BGW.StableTrees.StableRegularity
import BGW.StableTrees.StableLocalLaw
import BGW.ContinuumTrees.ExcursionCarrier

/-! Contract probe for CT7 node E02b (the a.s. SUPPORT theorem of the reflected process under
`stableLocalLaw θ`, `1 < θ ≤ 2`), following `r3-ct7-blueprint/blueprint.md` E02 and the Sol
re-audit requirement: *simultaneously for every positive jump label `x` of the passage process,
`g = T_{x-} > 0`, `d = T_x`, `L_g = x` and `(g,d)` is an excursion candidate*.

Notation: `P = stableLocalLaw θ`, `R = reflectedFrom 0 f = X - I`, `T_x = passageTime x f`,
`T_{x-} = passageTimeMinus x f`, `L = localTime f = -I`.  `passageJumpSet f` is the set of
positive jump levels `{x > 0 | T_{x-} < T_x}`.

PROOF PLAN recorded for the implementer (Sol re-audit; binding).
* An inverse-local-time PLATEAU alone is NOT enough: `L` constant on `[g,d]` permits deterministic
  intermediate returns of `R` to zero.  Strict interior positivity comes from MINIMUM UNIQUENESS.
* Step 1 (`ae_jump_window_inf`, directly from plateau inequalities, BEFORE any uniqueness):
  `T` is strictly increasing with `X(T_y) = -y` and `X ≥ -x` on `[0, T_x)`; hence for every jump
  level `x` and every rational window `r < T_{x-} < q < T_x`, `inf_{[r,q]} X = -x = X(T_{x-}-)`.
* Step 2: the window gives that `T_{x-} - r` is a generalized minimizer of the centered shift at
  `r` restricted to `[0, q-r]` (sealed analogue of E02a's adapters, built from Step 1 rather than
  from the candidate hypothesis); the sealed continuous-minimum theorem on countably many rational
  windows yields continuity of `X` at `T_{x-}`, i.e. `R(T_{x-}) = 0` (no jump start).
* Step 3: a zero of `R` (equivalently an attained or left-limit minimum) at an interior `t ∈ (g,d)`
  would be a second generalized minimizer on a larger rational window ending before `d`,
  contradicting uniqueness of the minimizer; so `R > 0` on `(g,d)`.
* Step 4 (converse): for a candidate `(g,d)`, `L` is constant on `[g,d]` by
  `ae_runningInf_const_off_zeroSet`, `x = L_d`, `g = T_{x-}` (no isolated zero from the left, by
  regularity/uniqueness), `d = T_x` (`d` creeps and `R` immediately re-enters `{X < I}` after a
  zero, simultaneously in all rational restarts).
TRUTH.  `x > 0` is essential (`T_{0-} = 0 = T_0`, no candidate at `0`); the absence of a
candidate with `g = 0` is part of the converse.  All statements are a.s. (the junk conventions of
`passageTime`, `passageTimeMinus` and `leftLim` only matter on null sets).
Estimate 650-1000 lines. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The set of positive **jump levels** of the passage process: `{x > 0 | T_{x-} < T_x}`. -/
def passageJumpSet (f : DLoc) : Set ℝ≥0 :=
  {x | 0 < x ∧ passageTimeMinus x f < passageTime x f}

/-- **Window minima from plateau inequalities** (Step 1; needs no uniqueness).  Simultaneously for
every jump level `x`: `X` has left limit `-x` at `T_{x-}`, `T_{x-} > 0`, and over every rational
window `r < T_{x-} < q < T_x` the infimum of `X` is `-x`. -/
theorem ae_jump_window_inf {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f,
      0 < passageTimeMinus x f ∧ Function.leftLim f.1 (passageTimeMinus x f) = -(x : ℝ) ∧
        ∀ r q : ℚ≥0, (r : ℝ≥0) < passageTimeMinus x f → passageTimeMinus x f < (q : ℝ≥0) →
          (q : ℝ≥0) < passageTime x f →
            (⨅ u : Set.Icc (r : ℝ≥0) (q : ℝ≥0), f.1 u) = -(x : ℝ) := sorry

/-- **Jump levels are countable** (monotone càdlàg `T`). -/
theorem ae_passageJumpSet_countable {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), (passageJumpSet f).Countable := sorry

/-- **No jump start** (Steps 2): a.s., at every jump level the path is continuous at `T_{x-}`,
takes the value `-x` there, and `R (T_{x-}) = 0`. -/
theorem ae_continuousAt_jumpStart {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f,
      ContinuousAt f.1 (passageTimeMinus x f) ∧ f.1 (passageTimeMinus x f) = -(x : ℝ) ∧
        (reflectedFrom 0 f).1 (passageTimeMinus x f) = 0 := sorry

/-- **Simultaneous excursion-candidate supplier (the Sol re-audit assertion).**  A.s., for every
positive jump label `x` simultaneously, `g = T_{x-} > 0`, `d = T_x`, `L_g = L_d = x` and `(g,d)`
is an `IsExcursionCandidate` (strict interior positivity of `R` via minimum uniqueness). -/
theorem ae_isExcursionCandidate_of_jump {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f,
      0 < passageTimeMinus x f ∧ localTime f (passageTimeMinus x f) = x ∧
        localTime f (passageTime x f) = x ∧
          IsExcursionCandidate f (passageTimeMinus x f) (passageTime x f) := sorry

/-- **Excursion intervals from jump levels.**  Same, with the stronger `IsExcursionInterval`
(continuous start, `R(T_{x-}) = 0`, via minimum continuity on rational windows). -/
theorem ae_isExcursionInterval_of_jump {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f,
      IsExcursionInterval f (passageTimeMinus x f) (passageTime x f) := sorry

/-- **Converse for candidates.**  A.s., every excursion candidate `(g,d)` of the reflected path is
`(T_{x-}, T_x)` for the unique level `x = L_g > 0`, which is a jump level; in particular `0 < g`
(no candidate starts at `0`). -/
theorem ae_exists_jump_of_isExcursionCandidate {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ g d : ℝ≥0, IsExcursionCandidate f g d →
      ∃ x ∈ passageJumpSet f, g = passageTimeMinus x f ∧ d = passageTime x f ∧
        x = localTime f g := sorry

/-- **No jump starts, a.s.**: every excursion candidate is an excursion interval (`R g = 0`). -/
theorem ae_isExcursionInterval_of_isExcursionCandidate {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ g d : ℝ≥0, IsExcursionCandidate f g d →
      IsExcursionInterval f g d := sorry

/-- **Characterization of excursion intervals (iff).** -/
theorem ae_isExcursionInterval_iff {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ g d : ℝ≥0, IsExcursionInterval f g d ↔
      ∃ x ∈ passageJumpSet f, g = passageTimeMinus x f ∧ d = passageTime x f := sorry

/-- **Characterization of excursion candidates (iff).** -/
theorem ae_isExcursionCandidate_iff {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ g d : ℝ≥0, IsExcursionCandidate f g d ↔
      ∃ x ∈ passageJumpSet f, g = passageTimeMinus x f ∧ d = passageTime x f := sorry

/-- **Distinct jump levels give disjoint intervals and distinct starts.** -/
theorem ae_jump_intervals_disjoint {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f, ∀ y ∈ passageJumpSet f,
      x < y → passageTime x f < passageTimeMinus y f := sorry

/-- **The zero set of the reflected process is Lebesgue-null** (a.s.; measured in `ℝ` through the
coercion, since `ℝ≥0` carries no `MeasureSpace` instance). -/
theorem ae_zeroSet_volume_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (volume : Measure ℝ) (((↑) : ℝ≥0 → ℝ) '' {t : ℝ≥0 | (reflectedFrom 0 f).1 t = 0}) = 0 :=
  sorry

/-- **The reflected process is positive exactly on the union of the excursion intervals**
(a.s., an equality of sets, not merely up to a null set): `{R > 0} = ⋃_{x ∈ jump levels}
(T_{x-}, T_x)`; equivalently `R` vanishes off the union, and the zero set is the Lebesgue-null
complement of `ae_zeroSet_volume_zero`. -/
theorem ae_pos_set_eq_iUnion_jump_intervals {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      {t : ℝ≥0 | 0 < (reflectedFrom 0 f).1 t} =
        ⋃ x ∈ passageJumpSet f, Set.Ioo (passageTimeMinus x f) (passageTime x f) := sorry

/-- **Lebesgue-almost every time lies in an excursion interval** (consequence of the two
previous statements). -/
theorem ae_volume_compl_iUnion_jump_intervals {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (volume : Measure ℝ) (((↑) : ℝ≥0 → ℝ) ''
        (⋃ x ∈ passageJumpSet f, Set.Ioo (passageTimeMinus x f) (passageTime x f))ᶜ) = 0 :=
  sorry

end BGW.StableTrees
