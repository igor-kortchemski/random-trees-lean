/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.LocallyFinite.GenerationField

/-!
# Generation histories and offspring transitions

The offspring counts on the current generation use coordinates disjoint from those which
determine the preceding generations. Splitting by the finite set of current vertices gives
the transition law without imposing positive probability on a history.
-/

@[expose] public section

namespace BGW.LocallyFinite

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The prescribed sizes of generations zero through `n`, including both endpoints. -/
def generationHistory (n : ℕ) (z : Fin (n + 1) → ℕ) : Set Tree :=
  {T | ∀ i : Fin (n + 1), generationSize T i.val = z i}

theorem measurableSet_generationHistory (n : ℕ) (z : Fin (n + 1) → ℕ) :
    MeasurableSet (generationHistory n z) := by
  have he : generationHistory n z = ⋂ i : Fin (n + 1), {T | generationSize T i.val = z i} := by
    ext T
    simp [generationHistory]
  rw [he]
  exact MeasurableSet.iInter fun i =>
    (measurable_generationSize i.val) (measurableSet_singleton (z i))

private abbrev PastField (n : ℕ) := {u : Address // u.length < n} → ℕ

private def fillPast (n : ℕ) (g : PastField n) : Offspring :=
  fun u => if h : u.length < n then g ⟨u, h⟩ else 0

private theorem fillPast_restrict (n : ℕ) (f : Offspring) :
    fillPast n (fun u => f u.val) = cutField n f := by
  funext u
  simp [fillPast, cutField]

private theorem measurable_fillPast (n : ℕ) : Measurable (fillPast n) := by
  apply Measurable.of_eval
  intro u
  by_cases h : u.length < n
  · simpa only [fillPast, dite_eq_left h] using
      (measurable_pi_apply (⟨u, h⟩ : {u // u.length < n}))
  · simpa only [fillPast, dite_eq_right h] using
      (measurable_const : Measurable (fun _ : PastField n => (0 : ℕ)))

private theorem history_piece_depends_on_past (n : ℕ) (z : Fin (n + 1) → ℕ)
    (S : Finset Address) (f : Offspring) :
    (prune (fillPast n (fun u => f u.val)) ∈ generationHistory n z ∧
      generation (prune (fillPast n (fun u => f u.val))) n = S) ↔
    (prune f ∈ generationHistory n z ∧ generation (prune f) n = S) := by
  rw [fillPast_restrict]
  have hz : ∀ i : Fin (n + 1),
      generationSize (prune (cutField n f)) i.val = generationSize (prune f) i.val := fun i =>
    congrArg Finset.card (generation_prune_cutField n i.val (by omega) f)
  simp only [generationHistory, Set.mem_ofPred_eq, hz,
    generation_prune_cutField n n le_rfl f]

private theorem raw_history_piece_transition (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) (z : Fin (n + 1) → ℕ) (S : Finset Address)
    (hS : ∀ u ∈ S, u.length = n) (k : ℕ) :
    offspringFieldLaw μ {f | prune f ∈ generationHistory n z ∧
        generation (prune f) n = S ∧ generationSize (prune f) (n + 1) = k} =
      offspringFieldLaw μ {f | prune f ∈ generationHistory n z ∧ generation (prune f) n = S} *
        Measure.pi (fun _ : S => μ) {v | ∑ u : S, v u = k} := by
  let A : Set (PastField n) := {g | prune (fillPast n g) ∈ generationHistory n z ∧
    generation (prune (fillPast n g)) n = S}
  let B : Set (S → ℕ) := {v | ∑ u : S, v u = k}
  have hA : MeasurableSet A :=
    ((measurableSet_generationHistory n z).inter (measurableSet_generation_eq n S)).preimage
      (measurable_prune.comp (measurable_fillPast n))
  have hB : MeasurableSet B := (Set.to_countable _).measurableSet
  have hd : Disjoint {u : Address | u.length < n} (S : Set Address) := by
    apply Set.disjoint_left.mpr
    intro u hu huS
    change u.length < n at hu
    have := hS u huS
    omega
  have hind : IndepFun (fun f : Offspring => fun u : {u : Address // u.length < n} => f u.val)
      (fun f : Offspring => fun u : S => f u.val) (offspringFieldLaw μ) :=
    (iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)).indepFun_set
      _ _ hd (fun _ => measurable_pi_apply _)
  have hmap : (offspringFieldLaw μ).map (fun f => fun u : S => f u.val) =
      Measure.pi (fun _ : S => μ) := by
    rw [offspringFieldLaw,
      Measure.map_infinitePi_infinitePi_of_inj (f := fun u : S => u.val) Subtype.val_injective,
      Measure.infinitePi_eq_pi]
  have he : {f | prune f ∈ generationHistory n z ∧ generation (prune f) n = S ∧
      generationSize (prune f) (n + 1) = k} =
      (fun f : Offspring => fun u : {u : Address // u.length < n} => f u.val) ⁻¹' A ∩
        (fun f : Offspring => fun u : S => f u.val) ⁻¹' B := by
    ext f
    have hp := history_piece_depends_on_past n z S f
    change (prune f ∈ generationHistory n z ∧ generation (prune f) n = S ∧
      generationSize (prune f) (n + 1) = k) ↔
      ((prune (fillPast n (fun u => f u.val)) ∈ generationHistory n z ∧
        generation (prune (fillPast n (fun u => f u.val))) n = S) ∧ ∑ u : S, f u.val = k)
    rw [hp]
    constructor
    · rintro ⟨hH, hgen, hnext⟩
      refine ⟨⟨hH, hgen⟩, ?_⟩
      rw [generationSize_prune_succ, hgen] at hnext
      simpa only [Finset.sum_coe_sort] using hnext
    · rintro ⟨⟨hH, hgen⟩, hnext⟩
      refine ⟨hH, hgen, ?_⟩
      rw [generationSize_prune_succ, hgen]
      simpa only [Finset.sum_coe_sort] using hnext
  have hp : (fun f : Offspring => fun u : {u : Address // u.length < n} => f u.val) ⁻¹' A =
      {f | prune f ∈ generationHistory n z ∧ generation (prune f) n = S} := by
    ext f
    exact history_piece_depends_on_past n z S f
  rw [he, hind.measure_inter_preimage_eq_mul A B hA hB, hp]
  rw [← hmap, Measure.map_apply (Measurable.of_eval fun u => measurable_pi_apply u.val) hB]

private abbrev HistoryShapes (n : ℕ) (z : Fin (n + 1) → ℕ) :=
  {S : Finset Address // (∀ u ∈ S, u.length = n) ∧ S.card = z (Fin.last n)}

private theorem measure_history_partition (P : Measure Tree) (n : ℕ)
    (z : Fin (n + 1) → ℕ) (A : Set Tree) (hA : MeasurableSet A)
    (hsub : A ⊆ generationHistory n z) :
    P A = ∑' S : HistoryShapes n z, P (A ∩ {T | generation T n = S.val}) := by
  have he : A = ⋃ S : HistoryShapes n z, A ∩ {T | generation T n = S.val} := by
    ext T
    constructor
    · intro hT
      have hlevel : ∀ u ∈ generation T n, u.length = n := fun u hu =>
        ((mem_generation T n u).mp hu).2
      have hc : (generation T n).card = z (Fin.last n) := (hsub hT) (Fin.last n)
      exact Set.mem_iUnion.mpr ⟨⟨generation T n, hlevel, hc⟩, hT, rfl⟩
    · intro hT
      obtain ⟨S, hS⟩ := Set.mem_iUnion.mp hT
      exact hS.1
  calc
    P A = P (⋃ S : HistoryShapes n z, A ∩ {T | generation T n = S.val}) := congrArg P he
    _ = _ := measure_iUnion (fun S R hne => Set.disjoint_left.mpr fun T hS hR =>
      hne (Subtype.ext (hS.2.symm.trans hR.2)))
      (fun S => hA.inter (measurableSet_generation_eq n S.val))

private theorem pi_sum_of_card (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (S : Finset Address) (m : ℕ) (hc : S.card = m) (k : ℕ) :
    Measure.pi (fun _ : S => μ) {v | ∑ u : S, v u = k} =
      Measure.pi (fun _ : Fin m => μ) {v | ∑ i : Fin m, v i = k} := by
  let e : S ≃ Fin m := Finset.equivFinOfCardEq hc
  let E := MeasurableEquiv.piCongrLeft (fun _ : Fin m => ℕ) e
  have hs (v : S → ℕ) : ∑ i : Fin m, E v i = ∑ u : S, v u := by
    simpa only [E, MeasurableEquiv.piCongrLeft_apply_apply] using
      (e.sum_comp (fun i => E v i)).symm
  rw [← Measure.pi_map_piCongrLeft e (fun _ : Fin m => μ),
    Measure.map_apply E.measurable (Set.to_countable _).measurableSet]
  congr 1
  ext v
  change (∑ u : S, v u = k) ↔ (∑ i : Fin m, E v i = k)
  rw [hs]

/-- The transition law of generation sizes given their full finite history. This identity of
joint masses also applies to histories of probability zero. -/
theorem bienaymeLaw_generationHistory_next (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) (z : Fin (n + 1) → ℕ) (k : ℕ) :
    bienaymeLaw μ (generationHistory n z ∩ {T | generationSize T (n + 1) = k}) =
      bienaymeLaw μ (generationHistory n z) *
        Measure.pi (fun _ : Fin (z (Fin.last n)) => μ)
          {v | ∑ i, v i = k} := by
  have hH := measurableSet_generationHistory n z
  have hnext : MeasurableSet {T : Tree | generationSize T (n + 1) = k} :=
    (measurable_generationSize (n + 1)) (measurableSet_singleton k)
  have hpiece (S : HistoryShapes n z) :
      bienaymeLaw μ ((generationHistory n z ∩ {T | generationSize T (n + 1) = k}) ∩
          {T | generation T n = S.val}) =
        bienaymeLaw μ (generationHistory n z ∩ {T | generation T n = S.val}) *
          Measure.pi (fun _ : Fin (z (Fin.last n)) => μ) {v | ∑ i, v i = k} := by
    rw [bienaymeLaw_apply μ ((hH.inter hnext).inter (measurableSet_generation_eq n S.val)),
      bienaymeLaw_apply μ (hH.inter (measurableSet_generation_eq n S.val))]
    have he : prune ⁻¹' ((generationHistory n z ∩ {T | generationSize T (n + 1) = k}) ∩
        {T | generation T n = S.val}) =
        {f | prune f ∈ generationHistory n z ∧ generation (prune f) n = S.val ∧
          generationSize (prune f) (n + 1) = k} := by
      ext f
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq]
      tauto
    rw [he, raw_history_piece_transition μ n z S.val S.property.1 k,
      pi_sum_of_card μ S.val _ S.property.2]
    rfl
  calc
    _ = ∑' S : HistoryShapes n z,
        bienaymeLaw μ ((generationHistory n z ∩ {T | generationSize T (n + 1) = k}) ∩
          {T | generation T n = S.val}) :=
      measure_history_partition _ n z _ (hH.inter hnext) (fun _ h => h.1)
    _ = ∑' S : HistoryShapes n z,
        bienaymeLaw μ (generationHistory n z ∩ {T | generation T n = S.val}) *
          Measure.pi (fun _ : Fin (z (Fin.last n)) => μ) {v | ∑ i, v i = k} :=
      tsum_congr hpiece
    _ = _ := by
      rw [ENNReal.tsum_mul_right, ← measure_history_partition _ n z _ hH (fun _ h => h)]

/-- At a history of positive probability, the next size is a sum of as many iid offspring
counts as there are individuals in the current generation. -/
theorem cond_generationHistory_next (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) (z : Fin (n + 1) → ℕ) (k : ℕ)
    (hz : bienaymeLaw μ (generationHistory n z) ≠ 0) :
    (bienaymeLaw μ)[|generationHistory n z] {T | generationSize T (n + 1) = k} =
      Measure.pi (fun _ : Fin (z (Fin.last n)) => μ) {v | ∑ i, v i = k} := by
  rw [ProbabilityTheory.cond_apply (measurableSet_generationHistory n z),
    bienaymeLaw_generationHistory_next, ← mul_assoc,
    ENNReal.inv_mul_cancel hz (measure_ne_top _ _), one_mul]

/-- Extinction is absorbing: an empty generation has no descendants in the next generation. -/
theorem generationSize_succ_eq_zero_of_eq_zero {T : Tree} {n : ℕ}
    (h : generationSize T n = 0) : generationSize T (n + 1) = 0 := by
  have he : generation T n = ∅ := Finset.card_eq_zero.mp h
  rw [generationSize_succ_eq_sum_offspring, he, Finset.sum_empty]

end BGW.LocallyFinite
