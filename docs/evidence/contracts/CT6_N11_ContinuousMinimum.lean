import BGW.StableTrees.StableUniqueMinimum
import BGW.StableTrees.StableLocalMarkov
import BGW.StableTrees.StableLocalLaw
import BGW.StableTrees.StableProcessReversal
import BGW.Skorokhod.JumpStopping
import BGW.Skorokhod.DLocShiftAt
import BGW.Skorokhod.ReverseIncrements

/-! Contract probe for CT6 N11, continuity / interior part (wave C): almost surely the path has
exactly one generalized minimizer `g`, `0 < g < T`, and `f` is continuous at `g`
(blueprint `ae_unique_continuous_minimum`).

Maintained file (proposed): `BGW/StableTrees/StableContinuousMinimum.lean`.

Sealed inputs: `genVal`, `genMin`, `IsGenMinimizer`, `IsStableLevyLaw.ae_existsUnique_generalizedMinimizer`
(`BGW.StableTrees.StableUniqueMinimum`), `exists_jumpStoppingTimes` (N10), `shiftAt` (sealed in
`BGW.Skorokhod.DLocShiftAt`; so, unlike the N06 contract, it is NOT copied here),
`IsStableLevyLaw.map_reverseIncrements` (N07).
Copied (audited, unproved): the N06 regularity predicates and
`ae_regular_both_stableLocalLaw`, `ae_regular_both_shiftAt_stableLocalLaw` (the latter packages N05).

Route (blueprint N11 "Interior", "Continuity").
* (a) `ae_regular_after_jumps_stableLocalLaw`: `exists_jumpStoppingTimes` + N06's regularity at each
  `J n`, intersect countably many events; transported to compact horizons by
  `map_restrict_stableLocalLaw` / `IsStableLevyLaw.unique`.
* (b) `ae_not_isGenMinimizer_of_jump`: a minimizer at a jump time `t` must be an upward jump with
  value of the minimum as left limit; the reversed path then has its maximum at a jump time, which
  contradicts (a) for the reversed path (same law by N07).
* (c) not at `0` (path starts at `0` and goes below by N06), not at `T` (no jump at `T`; the reversed
  path would be `≤ 0` but is positive immediately after `0`).
* Continuity at `g`: right-continuity is free; `f g = leftLim f g` since `g` is not a jump (b).

Doubts: none about truth. Convention: at `t = 0`, `leftLim f 0 = f 0` on `Icc 0 T`, so `0` is never a
jump; at `t = T` there is no right neighbourhood, so (a) is stated for `t < T`. -/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace BGW.Skorokhod.DLoc

-- copied from contract CT6_N06_Regularity (not part of this contract)
/-- `0` is regular for `(-∞, 0)`: the path takes negative values at times in `(0, ε)` for every
`ε > 0`. -/
def RegularBelowAtZero (f : DLoc) : Prop :=
  ∀ ε : ℝ≥0, 0 < ε → ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧ DLoc.eval t f < 0

-- copied from contract CT6_N06_Regularity (not part of this contract)
/-- `0` is regular for `(0, ∞)`. -/
def RegularAboveAtZero (f : DLoc) : Prop :=
  ∀ ε : ℝ≥0, 0 < ε → ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧ 0 < DLoc.eval t f

end BGW.Skorokhod.DLoc

namespace BGW.StableTrees

open BGW.Skorokhod

-- copied from contract CT6_N06_Regularity (not part of this contract)
theorem ae_regular_both_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      DLoc.RegularBelowAtZero f ∧ DLoc.RegularAboveAtZero f := sorry

-- copied from contract CT6_N06_Regularity (not part of this contract)
theorem ae_regular_both_shiftAt_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {τ : DLoc → ℝ≥0∞} (hτ : MeasureTheory.IsStoppingTime DLoc.filtration τ) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), τ f < ⊤ →
      DLoc.RegularBelowAtZero (DLoc.shiftAt τ f) ∧ DLoc.RegularAboveAtZero (DLoc.shiftAt τ f) :=
  sorry

/-! ### (a) Regularity immediately after every jump -/

/-- (a) on `DLoc`: almost surely, immediately after every jump time `t > 0` the path takes values
strictly below and strictly above its post-jump value `f t` (N05 at the N10 stopping times + N06). -/
theorem ae_regular_after_jumps_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ∀ t : ℝ≥0, 0 < t → f.1 t ≠ Function.leftLim f.1 t → ∀ ε : ℝ≥0, 0 < ε →
        (∃ s : ℝ≥0, 0 < s ∧ s < ε ∧ f.1 (t + s) < f.1 t) ∧
        (∃ s : ℝ≥0, 0 < s ∧ s < ε ∧ f.1 t < f.1 (t + s)) := by
  sorry

/-- (a) transported to a compact horizon: for a stable Lévy law on `[0,T]`, almost surely at every
jump time `t < T` the path takes values both below and above `f t` in `(t, t + ε)`, `ε > 0`. -/
theorem IsStableLevyLaw.ae_regular_after_jumps {θ T : ℝ} {P : ProbabilityMeasure (D T ℝ)}
    (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) (hP : IsStableLevyLaw θ T P) :
    ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)),
      ∀ t : Set.Icc (0 : ℝ) T, (t : ℝ) < T → f t ≠ Function.leftLim f t → ∀ ε : ℝ, 0 < ε →
        (∃ s : Set.Icc (0 : ℝ) T, (t : ℝ) < s ∧ (s : ℝ) < t + ε ∧ f s < f t) ∧
        (∃ s : Set.Icc (0 : ℝ) T, (t : ℝ) < s ∧ (s : ℝ) < t + ε ∧ f t < f s) := by
  sorry

/-- N06 on a compact horizon: almost surely, `0` is regular for both half-lines. -/
theorem IsStableLevyLaw.ae_regular_at_zero {θ T : ℝ} {P : ProbabilityMeasure (D T ℝ)}
    (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) (hP : IsStableLevyLaw θ T P) :
    ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)),
      ∀ ε : ℝ, 0 < ε →
        (∃ s : Set.Icc (0 : ℝ) T, 0 < (s : ℝ) ∧ (s : ℝ) < ε ∧ f s < f ⟨0, le_rfl, hT.le⟩) ∧
        (∃ s : Set.Icc (0 : ℝ) T, 0 < (s : ℝ) ∧ (s : ℝ) < ε ∧ f ⟨0, le_rfl, hT.le⟩ < f s) := by
  sorry

/-! ### (b) The minimum is not attained at a jump time -/

/-- Deterministic: a path is continuous at `t` as soon as `f t = leftLim f t` (right-continuity is
automatic; at `t = 0` the left limit is `f 0`). -/
theorem continuousAt_of_eq_leftLim {T : ℝ} (f : D T ℝ) {t : Set.Icc (0 : ℝ) T}
    (h : f t = Function.leftLim f t) : ContinuousAt f t := by
  sorry

/-- Deterministic reversal step. If `0 < t < T` is a generalized minimizer at which `f` jumps up
(`leftLim f t < f t`), then the reversed path `reverseIncrements f` attains its global maximum at
`T - t` and jumps up there: its left limit at `T - t` is `f T - f t`, strictly below the maximum
value `f T - leftLim f t`. -/
theorem reverseIncrements_max_at_upward_jump {T : ℝ} (hT : 0 < T) (f : D T ℝ)
    {t : Set.Icc (0 : ℝ) T} (ht0 : 0 < (t : ℝ)) (htT : (t : ℝ) < T)
    (hup : Function.leftLim f t < f t) (hg : IsGenMinimizer f t) :
    (∀ s : Set.Icc (0 : ℝ) T,
        reverseIncrements hT.le f s ≤
          reverseIncrements hT.le f ⟨T - t, by linarith [t.2.2], by linarith [t.2.1]⟩) ∧
      Function.leftLim (reverseIncrements hT.le f) ⟨T - t, by linarith [t.2.2], by linarith [t.2.1]⟩ <
        reverseIncrements hT.le f ⟨T - t, by linarith [t.2.2], by linarith [t.2.1]⟩ := by
  sorry

/-- (b) Almost surely no generalized minimizer is a jump time (upward jumps via the reversal of
N07, downward jumps via (a); the terminal time is no jump a.s.). -/
theorem IsStableLevyLaw.ae_not_isGenMinimizer_of_jump {θ T : ℝ} {P : ProbabilityMeasure (D T ℝ)}
    (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) (hP : IsStableLevyLaw θ T P) :
    ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)),
      ∀ t : Set.Icc (0 : ℝ) T, f t ≠ Function.leftLim f t → ¬ IsGenMinimizer f t := by
  sorry

/-- Consequence: every generalized minimizer is a continuity point. -/
theorem IsStableLevyLaw.ae_continuousAt_of_isGenMinimizer {θ T : ℝ}
    {P : ProbabilityMeasure (D T ℝ)} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    (hP : IsStableLevyLaw θ T P) :
    ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)),
      ∀ g : Set.Icc (0 : ℝ) T, IsGenMinimizer f g → ContinuousAt f g := by
  sorry

/-! ### (c) The minimizer is interior -/

/-- (c) not at `0`: the path starts at `0` and takes negative values (N06). -/
theorem IsStableLevyLaw.ae_not_isGenMinimizer_zero {θ T : ℝ} {P : ProbabilityMeasure (D T ℝ)}
    (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) (hP : IsStableLevyLaw θ T P) :
    ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)), ¬ IsGenMinimizer f ⟨0, le_rfl, hT.le⟩ := by
  sorry

/-- (c) not at `T`: no jump at `T` (N07 / `ae_continuousAt`), and the reversed path (same law, N07)
is positive immediately after `0`, whereas a minimum at `T` would force it to be `≤ 0`. -/
theorem IsStableLevyLaw.ae_not_isGenMinimizer_top {θ T : ℝ} {P : ProbabilityMeasure (D T ℝ)}
    (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) (hP : IsStableLevyLaw θ T P) :
    ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)), ¬ IsGenMinimizer f ⟨T, hT.le, le_rfl⟩ := by
  sorry

/-! ### Main statement -/

/-- **N11 (F6).** For fixed `T > 0`, the minimum, as a value or a left limit, has exactly one
minimizing time, this time is interior, and the path is continuous there. -/
theorem IsStableLevyLaw.ae_unique_continuous_minimum {θ T : ℝ} {P : ProbabilityMeasure (D T ℝ)}
    (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) (hP : IsStableLevyLaw θ T P) :
    ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)),
      ∃ g : Set.Icc (0 : ℝ) T,
        0 < (g : ℝ) ∧ (g : ℝ) < T ∧ ContinuousAt f g ∧
        min (Function.leftLim f g) (f g) = ⨅ t, f t ∧
        ∀ s : Set.Icc (0 : ℝ) T,
          min (Function.leftLim f s) (f s) = (⨅ t, f t) → s = g := by
  sorry

/-- The same for the canonical stable process law. -/
theorem stableProcessLaw_ae_unique_continuous_minimum {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (hT : 0 < T) :
    ∀ᵐ f : D T ℝ ∂(stableProcessLaw θ T : Measure (D T ℝ)),
      ∃ g : Set.Icc (0 : ℝ) T,
        0 < (g : ℝ) ∧ (g : ℝ) < T ∧ ContinuousAt f g ∧
        min (Function.leftLim f g) (f g) = ⨅ t, f t ∧
        ∀ s : Set.Icc (0 : ℝ) T,
          min (Function.leftLim f s) (f s) = (⨅ t, f t) → s = g :=
  (isStableLevyLaw_stableProcessLaw hθ hT).ae_unique_continuous_minimum hθ hT

/-- Transfer to any measure absolutely continuous with respect to a stable Lévy law (used by N17
on bridge prefixes). -/
theorem ae_unique_continuous_minimum_of_absolutelyContinuous {θ T : ℝ}
    {P : ProbabilityMeasure (D T ℝ)} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    (hP : IsStableLevyLaw θ T P) {μ : Measure (D T ℝ)} (hμ : μ ≪ (P : Measure (D T ℝ))) :
    ∀ᵐ f : D T ℝ ∂μ,
      ∃ g : Set.Icc (0 : ℝ) T,
        0 < (g : ℝ) ∧ (g : ℝ) < T ∧ ContinuousAt f g ∧
        min (Function.leftLim f g) (f g) = ⨅ t, f t ∧
        ∀ s : Set.Icc (0 : ℝ) T,
          min (Function.leftLim f s) (f s) = (⨅ t, f t) → s = g :=
  hμ.ae_le (hP.ae_unique_continuous_minimum hθ hT)

end BGW.StableTrees
