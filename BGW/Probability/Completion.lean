/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Representatives and integration under measure completion

Events in a sigma-algebra augmented by null sets have almost-everywhere representatives in the
original sigma-algebra. Integration of a real function against the completed measure agrees with
integration against the original measure, globally and on measurable sets.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace BGW.Probability

/-- An event in the join of a sigma-algebra with the null-set sigma-algebra has a representative
in the original sigma-algebra, almost everywhere equal to the given event. -/
theorem exists_raw_ae_eq_of_mem_sup {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {m : MeasurableSpace Ω} {A : Set Ω} (hA : MeasurableSet[m ⊔
      MeasurableSpace.generateFrom {N : Set Ω | P N = 0}] A) :
    ∃ B, MeasurableSet[m] B ∧ A =ᵐ[P] B := by
  let S : Set (Set Ω) := {B | MeasurableSet[m] B} ∪ {N | P N = 0}
  have hgen : m ⊔ MeasurableSpace.generateFrom {N : Set Ω | P N = 0} =
      MeasurableSpace.generateFrom S := by
    rw [← MeasurableSpace.generateFrom_sup_generateFrom,
      MeasurableSpace.generateFrom_measurableSet]
  have hpi : IsPiSystem S := by
    intro A hA B hB _
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · exact Or.inl (hA.inter hB)
    · exact Or.inr (measure_mono_null inter_subset_right hB)
    · exact Or.inr (measure_mono_null inter_subset_left hA)
    · exact Or.inr (measure_mono_null inter_subset_left hA)
  induction A, hA using MeasurableSpace.induction_on_inter hgen hpi with
  | empty => exact ⟨∅, MeasurableSet.empty, EventuallyEq.refl _ _⟩
  | basic A hA =>
      rcases hA with hA | hA
      · exact ⟨A, hA, EventuallyEq.refl _ _⟩
      · exact ⟨∅, MeasurableSet.empty, ae_eq_empty.2 hA⟩
  | compl A hA ih =>
      obtain ⟨B, hB, hAB⟩ := ih
      exact ⟨Bᶜ, hB.compl, (ae_eq_set_compl_compl.2 hAB)⟩
  | iUnion A hdisj hA ih =>
      choose B hB hAB using ih
      exact ⟨⋃ n, B n, MeasurableSet.iUnion hB,
        Filter.EventuallyEqSet.countable_iUnion hAB⟩

/-- Real integration against a completed measure equals integration against the original measure. -/
theorem integral_completion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {F : Ω → ℝ}
    (hF : AEStronglyMeasurable F P) :
    ∫ f, F f ∂P.completion = ∫ f, F f ∂P := by
  let i : NullMeasurableSpace Ω P → Ω := fun f => f
  have hi : Measurable i := fun _ hs => hs.nullMeasurableSet
  have hmap : P.completion.map i = P := by
    ext A hA
    rw [Measure.map_apply hi hA]
    change P.completion A = P A
    exact Measure.completion_apply P A
  have hF' : AEStronglyMeasurable F (P.completion.map i) := hmap.symm ▸ hF
  calc
    _ = ∫ f, F f ∂P.completion.map i := (integral_map hi.aemeasurable hF').symm
    _ = _ := by rw [hmap]

/-- Set integration against a completed measure equals set integration against the original
measure on every measurable set. -/
theorem setIntegral_completion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {A : Set Ω} (hA : MeasurableSet A) {F : Ω → ℝ} (hF : AEStronglyMeasurable F P) :
    ∫ f in A, F f ∂P.completion = ∫ f in A, F f ∂P := by
  calc
    _ = ∫ f, A.indicator F f ∂P.completion :=
      (integral_indicator hA.nullMeasurableSet).symm
    _ = ∫ f, A.indicator F f ∂P := integral_completion P (hF.indicator hA)
    _ = _ := integral_indicator hA

end BGW.Probability
