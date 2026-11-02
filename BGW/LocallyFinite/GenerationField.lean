/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.LocallyFinite.GenerationLaw

/-!
# Generations determined by an offspring field

The generations through depth `n` only depend on offspring coordinates strictly above depth
`n`. The next generation is the sum of the offspring counts at the current generation. These
deterministic facts separate the explored field from fresh offspring coordinates in the
generation-process law.
-/

@[expose] public section

namespace BGW.LocallyFinite

/-- Retain offspring coordinates strictly above depth `n` and set all others to zero. -/
def cutField (n : ℕ) (f : Offspring) : Offspring :=
  fun u => if u.length < n then f u else 0

theorem measurable_cutField (n : ℕ) : Measurable (cutField n) := by
  apply Measurable.of_eval
  intro u
  by_cases hu : u.length < n
  · simpa only [cutField, ite_eq_left hu] using (measurable_pi_apply u :
      Measurable (fun f : Offspring => f u))
  · simpa only [cutField, ite_eq_right hu] using (measurable_const :
      Measurable (fun _ : Offspring => (0 : ℕ)))

private theorem generation_prune_eq_of_agree (n : ℕ) {f g : Offspring}
    (h : ∀ u : Address, u.length < n → f u = g u) :
    generation (prune f) n = generation (prune g) n := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    have hroot : f [] = g [] := h [] (by simp)
    simp only [generation, degree_prune]
    apply Finset.biUnion_congr (congrArg Finset.range hroot)
    intro j hj
    have hjf : 1 ≤ j + 1 ∧ j + 1 ≤ f [] := by
      simp only [Finset.mem_range] at hj
      omega
    have hjg : 1 ≤ j + 1 ∧ j + 1 ≤ g [] := by omega
    apply congrArg (Finset.image (List.cons (j + 1)))
    rw [child_prune, ite_eq_left hjf, child_prune, ite_eq_left hjg]
    apply ih
    intro u hu
    exact h ((j + 1) :: u) (by simp only [List.length_cons]; omega)

/-- Offspring counts at depth `n` and below do not affect any generation through depth `n`. -/
theorem generation_prune_cutField (n m : ℕ) (hm : m ≤ n) (f : Offspring) :
    generation (prune (cutField n f)) m = generation (prune f) m := by
  apply generation_prune_eq_of_agree
  intro u hu
  simp only [cutField, ite_eq_left (lt_of_lt_of_le hu hm)]

/-- The next generation counts all children of vertices in the current generation. -/
theorem generationSize_succ_eq_sum_offspring (T : Tree) (n : ℕ) :
    generationSize T (n + 1) = ∑ u ∈ generation T n, T.val u := by
  induction n generalizing T with
  | zero => simp [generation, degree]
  | succ n ih =>
    rw [generationSize_succ, generation, Finset.sum_biUnion]
    · apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_image]
      · exact ih (child T (j + 1))
      · intro u _ v _ huv
        exact (List.cons.inj huv).2
    · intro i _ j _ hij
      apply Finset.disjoint_left.mpr
      intro u hu hv
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨w, _, he⟩ := Finset.mem_image.mp hv
      exact hij (by simpa using (List.cons.inj he).1.symm)

/-- At present vertices pruning keeps the original offspring counts. -/
theorem generationSize_prune_succ (f : Offspring) (n : ℕ) :
    generationSize (prune f) (n + 1) = ∑ u ∈ generation (prune f) n, f u := by
  rw [generationSize_succ_eq_sum_offspring]
  apply Finset.sum_congr rfl
  intro u hu
  exact prune_val_of_present ((mem_generation (prune f) n u).mp hu).1

theorem measurableSet_present (u : Address) : MeasurableSet {T : Tree | Present T u} := by
  induction u with
  | nil =>
    simpa only [present_nil, Set.ofPred_true] using
      (MeasurableSet.univ : MeasurableSet (Set.univ : Set Tree))
  | cons j u ih =>
    have hj : MeasurableSet {T : Tree | 1 ≤ j ∧ j ≤ degree T} :=
      (MeasurableSet.of_discrete (s := {k : ℕ | 1 ≤ j ∧ j ≤ k})).preimage
        continuous_degree.measurable
    simpa only [Set.preimage_ofPred_eq, ← Set.ofPred_and, present_cons, and_assoc] using
      hj.inter (ih.preimage (continuous_child j).measurable)

theorem measurable_generation (n : ℕ) : Measurable (fun T : Tree => generation T n) := by
  apply measurable_finset_iff.mpr
  intro u
  apply measurableSet_setOfPred.mp
  by_cases hu : u.length = n
  · simpa only [mem_generation, hu, and_true] using measurableSet_present u
  · simp only [mem_generation, hu, and_false, Set.ofPred_false, MeasurableSet.empty]

theorem measurableSet_generation_eq (n : ℕ) (S : Finset Address) :
    MeasurableSet {T : Tree | generation T n = S} :=
  (measurable_generation n) (measurableSet_singleton S)

end BGW.LocallyFinite
