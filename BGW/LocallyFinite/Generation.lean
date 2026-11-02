/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.LocallyFinite.Extinction
public import Mathlib.Data.Finset.Card

/-!
# Finite generations of locally finite trees

`generation T n` lists exactly the present addresses of length `n`, with the root at generation
zero. Its cardinality is `generationSize T n`. The definition adapts the finite-generation
construction of `Freezing1/PlaneTreeGeometry.lean`; indices in `Finset.range` are shifted by one
to retain the positive child convention. No finiteness of the whole tree is assumed.
-/

@[expose] public section

namespace BGW.LocallyFinite

/-- The finite set of vertices at depth `n`, including the root at depth zero. -/
def generation (T : Tree) : ℕ → Finset Address
  | 0 => {[]}
  | n + 1 => (Finset.range (degree T)).biUnion fun j =>
      (generation (child T (j + 1)) n).image (List.cons (j + 1))

theorem mem_generation (T : Tree) (n : ℕ) (u : Address) :
    u ∈ generation T n ↔ Present T u ∧ u.length = n := by
  induction n generalizing T u with
  | zero =>
    cases u <;> simp [generation]
  | succ n ih =>
    cases u with
    | nil => simp [generation]
    | cons j u =>
      simp only [generation, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
        ih, List.cons.injEq, present_cons, List.length_cons]
      constructor
      · rintro ⟨i, hi, v, hv, ⟨rfl, rfl⟩⟩
        exact ⟨⟨by omega, by omega, hv.1⟩, by omega⟩
      · rintro ⟨⟨hj1, hjT, hu⟩, hlen⟩
        obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
        exact ⟨i, by omega, u, ⟨hu, by omega⟩, rfl, rfl⟩

/-- The number of present vertices at depth `n`. -/
def generationSize (T : Tree) (n : ℕ) : ℕ := (generation T n).card

@[simp] theorem generationSize_zero (T : Tree) : generationSize T 0 = 1 := by
  simp [generationSize, generation]

/-- A generation is the disjoint union of the corresponding generations of existing children. -/
theorem generationSize_succ (T : Tree) (n : ℕ) :
    generationSize T (n + 1) =
      ∑ j ∈ Finset.range (degree T), generationSize (child T (j + 1)) n := by
  unfold generationSize
  rw [generation, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro j _
    exact Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2)
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro u hu hv
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨w, _, he⟩ := Finset.mem_image.mp hv
    exact hij (by simpa using (List.cons.inj he).1.symm)

theorem generationSize_succ_eq_sum (T : Tree) (n : ℕ) :
    generationSize T (n + 1) =
      ∑ i : Fin (degree T), generationSize (child T (i.val + 1)) n := by
  rw [generationSize_succ]
  exact (Fin.sum_univ_eq_sum_range
    (fun j => generationSize (child T (j + 1)) n) (degree T)).symm

@[simp] theorem generationSize_one (T : Tree) : generationSize T 1 = degree T := by
  simp [generationSize_succ]

/-- No vertex at depth `n` is equivalent to extinction by generation `n`. -/
theorem generationSize_eq_zero_iff (T : Tree) (n : ℕ) :
    generationSize T n = 0 ↔ T ∈ extinctBy n := by
  induction n generalizing T with
  | zero => simp [extinctBy_zero]
  | succ n ih =>
    rw [generationSize_succ, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _),
      mem_extinctBy_succ_iff]
    simp only [Finset.mem_range, ih]
    constructor
    · intro h j hj1 hj2
      obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
      exact h i (by omega)
    · intro h i hi
      exact h (i + 1) (by omega) (by omega)

end BGW.LocallyFinite

namespace BGW.PlaneTree

/-- The finite-tree bridge shifts child indices and preserves every generation. -/
theorem generation_toLocallyFinite (t : PlaneTree) (n : ℕ) :
    LocallyFinite.generation t.toLocallyFinite n =
      (t.vertices.toFinset.filter fun u => u.length = n).image positiveAddress := by
  ext u
  simp only [LocallyFinite.mem_generation, Finset.mem_image, Finset.mem_filter,
    List.mem_toFinset, mem_vertices_iff]
  constructor
  · rintro ⟨hu, hn⟩
    obtain ⟨v, rfl⟩ := exists_positiveAddress_of_present hu
    exact ⟨v, ⟨(present_toLocallyFinite t v).mp hu, by simpa [positiveAddress] using hn⟩, rfl⟩
  · rintro ⟨v, ⟨hv, hn⟩, rfl⟩
    exact ⟨(present_toLocallyFinite t v).mpr hv, by simpa [positiveAddress] using hn⟩

theorem generationSize_toLocallyFinite (t : PlaneTree) (n : ℕ) :
    LocallyFinite.generationSize t.toLocallyFinite n = t.generationSize n := by
  have hi : Function.Injective positiveAddress := List.map_injective_iff.mpr Nat.succ_injective
  rw [LocallyFinite.generationSize, generation_toLocallyFinite,
    Finset.card_image_of_injective _ hi]
  have h : t.vertices.toFinset.filter (fun u => u.length = n) =
      (t.vertices.filter fun u => decide (u.length = n)).toFinset := by
    ext u
    simp
  rw [h, List.toFinset_card_of_nodup ((nodup_vertices t).filter _)]
  exact (List.countP_eq_length_filter).symm

end BGW.PlaneTree
