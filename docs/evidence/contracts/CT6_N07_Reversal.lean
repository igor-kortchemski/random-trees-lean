import BGW.StableTrees.StableProcess
import BGW.Skorokhod.MeasurableMaps
import BGW.Skorokhod.MeasurableCylinders
import BGW.Skorokhod.Measurable

/-! Contract probe for CT6 blueprint N07 (reversal of increments, F5) at a deterministic horizon.

Maintained files (proposed): `BGW/Skorokhod/Reversal.lean` (the map, its càdlàg proof and
measurability) and `BGW/StableTrees/StableProcessReversal.lean` (the law statements).

The map is the UNCENTERED, unsigned reversal `R f (u) = f T - f ((T-u)-)` with the convention
`f (0-) = f 0` (Mathlib's `Function.leftLim` at the bottom point of `Icc 0 T` is `f 0`), so
`R f 0 = f T - f (T-)` (the terminal jump, `0` a.s. under the stable law by P3) and
`R f T = f T - f 0`. It is NOT claimed to be an involution on arbitrary paths with endpoint jumps.
The plain `u ↦ f T - f (T-u)` is left-continuous, not càdlàg, and is a different map.

FLAG: the definition's càdlàg obligation `isCadlag_reverseIncrementsFun` is a `sorry`-proved
lemma used in the definition (it needs: right-continuity of `u ↦ leftLim f (T-u)` from the
left-continuity of `leftLim f`, and left limits from right-continuity of `f`). It is a true
deterministic statement and must be proved before any proof module depends on this definition. -/

open MeasureTheory
open scoped Topology

namespace BGW.Skorokhod

/-- The reversed-increment function `u ↦ f T - f ((T-u)-)`. -/
noncomputable def reverseIncrementsFun {T : ℝ} (hT : 0 ≤ T) (f : D T ℝ) :
    Set.Icc (0 : ℝ) T → ℝ :=
  fun u => f ⟨T, hT, le_rfl⟩ - Function.leftLim f ⟨T - u, by linarith [u.2.2], by linarith [u.2.1]⟩

/-- FLAG: càdlàg obligation for the reversed path (proof deferred). -/
theorem isCadlag_reverseIncrementsFun {T : ℝ} (hT : 0 ≤ T) (f : D T ℝ) :
    IsCadlag (reverseIncrementsFun hT f) := sorry

/-- The time reversal of increments `R f (u) = f T - f ((T-u)-)`, with `f (0-) = f 0`. -/
noncomputable def reverseIncrements {T : ℝ} (hT : 0 ≤ T) (f : D T ℝ) : D T ℝ :=
  ⟨reverseIncrementsFun hT f, isCadlag_reverseIncrementsFun hT f⟩

/-- Pointwise formula (definitional). -/
theorem reverseIncrements_apply {T : ℝ} (hT : 0 ≤ T) (f : D T ℝ) (u : Set.Icc (0 : ℝ) T) :
    reverseIncrements hT f u =
      f ⟨T, hT, le_rfl⟩ -
        Function.leftLim f ⟨T - u, by linarith [u.2.2], by linarith [u.2.1]⟩ := rfl

/-- `reverseIncrements` is Borel measurable. -/
theorem measurable_reverseIncrements {T : ℝ} (hT : 0 ≤ T) :
    Measurable (reverseIncrements hT) := sorry

end BGW.Skorokhod

namespace BGW.StableTrees

open BGW.Skorokhod

/-- N07, general form: every stable Lévy law on `[0,T]` is invariant under reversal. -/
theorem IsStableLevyLaw.map_reverseIncrements {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    {P : ProbabilityMeasure (D T ℝ)} (hP : IsStableLevyLaw θ T P) :
    P.map (reverseIncrements hT.le) = P := sorry

/-- N07: the stable process law is invariant under reversal of increments. -/
theorem map_reverseIncrements_stableProcessLaw {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) :
    (stableProcessLaw θ T).map (reverseIncrements hT.le) = stableProcessLaw θ T := sorry

end BGW.StableTrees
