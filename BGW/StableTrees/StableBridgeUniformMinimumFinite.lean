/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Max

/-!
# Finite minimum indices and cyclic increments

The first minimum is a measurable finite-valued function. A cyclic increment vector
recovers its potential up to an additive constant by summation.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter VIII (Vervaat's
transformation and the uniform law of the minimum time); L. Chaumont, *Excursion normalisée,
méandre et pont pour les processus de Lévy stables*, Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory Set Fin.NatCast

namespace BGW.StableTrees

/-- A nonempty finite real vector has a minimizing coordinate. -/
theorem finiteMin_nonempty (M : ℕ) (v : Fin (M + 1) → ℝ) :
    (Finset.univ.filter (fun i => ∀ j, v i ≤ v j)).Nonempty := by
  classical
  obtain ⟨i, hi⟩ := Finite.exists_min v
  exact ⟨i, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi⟩

/-- The first minimizing index of a nonempty finite real vector. -/
noncomputable def finiteMinIndex (M : ℕ) (v : Fin (M + 1) → ℝ) : Fin (M + 1) := by
  classical
  exact (Finset.univ.filter (fun i => ∀ j, v i ≤ v j)).min' (finiteMin_nonempty M v)

/-- The selected coordinate minimizes the vector. -/
theorem finiteMinIndex_le (M : ℕ) (v : Fin (M + 1) → ℝ) (j : Fin (M + 1)) :
    v (finiteMinIndex M v) ≤ v j := by
  classical
  exact (Finset.mem_filter.mp (Finset.min'_mem _ (finiteMin_nonempty M v))).2 j

private theorem finiteMinIndex_first (M : ℕ) (v : Fin (M + 1) → ℝ)
    (j : Fin (M + 1)) (hj : ∀ i, v j ≤ v i) : finiteMinIndex M v ≤ j := by
  classical
  exact Finset.min'_le _ _ (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hj)

/-- A Borel characterization of the first minimum, including ties. -/
theorem finiteMinIndex_eq_iff (M : ℕ) (v : Fin (M + 1) → ℝ) (k : Fin (M + 1)) :
    finiteMinIndex M v = k ↔ (∀ j, v k ≤ v j) ∧ ∀ j, j < k → v k < v j := by
  constructor
  · intro hk
    have hmin : ∀ j, v k ≤ v j := hk ▸ finiteMinIndex_le M v
    refine ⟨hmin, ?_⟩
    intro j hj
    apply lt_of_le_of_ne (hmin j)
    intro heq
    have hfirst := finiteMinIndex_first M v j (fun i => heq ▸ hmin i)
    rw [hk] at hfirst
    exact (not_le_of_gt hj) hfirst
  · rintro ⟨hmin, hfirst⟩
    apply le_antisymm (finiteMinIndex_first M v k hmin)
    by_contra! hk
    exact (hfirst _ hk).not_ge (finiteMinIndex_le M v k)

/-- The first minimizing index is measurable. -/
theorem measurable_finiteMinIndex (M : ℕ) : Measurable (finiteMinIndex M) := by
  classical
  apply measurable_to_countable'
  intro k
  have heq : (finiteMinIndex M) ⁻¹' {k} =
      {v | (∀ j, v k ≤ v j) ∧ ∀ j, j < k → v k < v j} := by
    ext v
    exact finiteMinIndex_eq_iff M v k
  rw [heq]
  simp only [ofPred_and, ofPred_forall]
  exact (MeasurableSet.iInter fun j => measurableSet_le
    (measurable_pi_apply k) (measurable_pi_apply j)).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun (_ : j < k) =>
      measurableSet_lt (measurable_pi_apply k) (measurable_pi_apply j))

/-- An injective vector has a unique minimizing coordinate. -/
theorem finiteMinIndex_eq_of_min (M : ℕ) {v : Fin (M + 1) → ℝ}
    (hv : Function.Injective v) {k : Fin (M + 1)} (hk : ∀ j, v k ≤ v j) :
    finiteMinIndex M v = k :=
  hv (le_antisymm (finiteMinIndex_le M v k) (hk _))

/-- A cyclic vector of adjacent differences. -/
def cyclicDiff (M : ℕ) (v : Fin (M + 1) → ℝ) (i : Fin (M + 1)) : ℝ :=
  v (i + 1) - v i

/-- The partial-sum potential of a cyclic increment vector, normalized to zero at zero. -/
def cyclicPrimitive (M : ℕ) (x : Fin (M + 1) → ℝ) (i : Fin (M + 1)) : ℝ :=
  ∑ j ∈ Finset.range i.val, x (j : Fin (M + 1))

/-- Finite summation recovers a potential from its cyclic differences. -/
theorem cyclicPrimitive_diff (M : ℕ) (v : Fin (M + 1) → ℝ) (i : Fin (M + 1)) :
    cyclicPrimitive M (cyclicDiff M v) i = v i - v 0 := by
  have htel (n : ℕ) :
      (∑ j ∈ Finset.range n, cyclicDiff M v (j : Fin (M + 1))) =
        v (n : Fin (M + 1)) - v 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [cyclicDiff, Nat.cast_add, Nat.cast_one]
      ring
  simpa only [cyclicPrimitive, Fin.cast_val_eq_self] using htel i.val

/-- Partial-sum vectors are measurable functions of the increments. -/
theorem measurable_cyclicPrimitive (M : ℕ) : Measurable (cyclicPrimitive M) :=
  Measurable.of_eval fun i => Finset.measurable_sum (Finset.range i.val)
    fun j _ => measurable_pi_apply (j : Fin (M + 1))

/-- Translating every coordinate leaves the first minimum unchanged. -/
theorem finiteMinIndex_sub_const (M : ℕ) (v : Fin (M + 1) → ℝ) (c : ℝ) :
    finiteMinIndex M (fun i => v i - c) = finiteMinIndex M v := by
  apply (finiteMinIndex_eq_iff M _ _).mpr
  have h := (finiteMinIndex_eq_iff M v (finiteMinIndex M v)).mp rfl
  exact ⟨fun j => sub_le_sub_right (h.1 j) c,
    fun j hj => sub_lt_sub_right (h.2 j hj) c⟩

/-- Cyclically relabeling distinct values relabels their minimum by subtraction. -/
theorem finiteMinIndex_shift (M : ℕ) {v : Fin (M + 1) → ℝ}
    (hv : Function.Injective v) (k : Fin (M + 1)) :
    finiteMinIndex M (fun i => v (i + k)) = finiteMinIndex M v - k := by
  apply finiteMinIndex_eq_of_min M (hv.comp (add_left_injective k))
  intro j
  simpa only [Function.comp_apply, sub_add_cancel] using finiteMinIndex_le M v (j + k)

/-- Partial summation of shifted cyclic differences recovers the shifted potential. -/
theorem cyclicPrimitive_shift_diff (M : ℕ) (v : Fin (M + 1) → ℝ)
    (k i : Fin (M + 1)) :
    cyclicPrimitive M (fun j => cyclicDiff M v (j + k)) i = v (i + k) - v k := by
  have heq : (fun j => cyclicDiff M v (j + k)) = cyclicDiff M (fun j => v (j + k)) := by
    funext j
    simp only [cyclicDiff]
    congr 2
    ac_rfl
  rw [heq, cyclicPrimitive_diff, zero_add]

end BGW.StableTrees
