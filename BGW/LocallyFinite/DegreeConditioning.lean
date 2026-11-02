/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree.DegreeCount

/-!
# Conditioning on size and finitely many degree counts

The conditioning event consists of finite trees with the prescribed size and degree counts.
The finite-size restriction is explicit: no count of all vertices of an infinite tree is
totalized to a natural number. The law, atoms and cyclic bridge mass retain all zero-event
and lattice restrictions through the actual event mass.
-/

@[expose] public section

namespace BGW.LocallyFinite

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Finite trees with size `n` and the indicated finitely many outdegree counts. -/
def degreeSizeEvent (n r : ℕ) (ks cs : Fin r → ℕ) : Set Tree :=
  PlaneTree.toLocallyFinite ''
    {t : PlaneTree | t.size = n ∧ ∀ j, t.degreeCount (ks j) = cs j}

theorem toLocallyFinite_mem_degreeSizeEvent_iff (t : PlaneTree) (n r : ℕ)
    (ks cs : Fin r → ℕ) :
    t.toLocallyFinite ∈ degreeSizeEvent n r ks cs ↔
      t.size = n ∧ ∀ j, t.degreeCount (ks j) = cs j := by
  exact PlaneTree.toLocallyFinite_injective.mem_set_image

theorem measurableSet_degreeSizeEvent (n r : ℕ) (ks cs : Fin r → ℕ) :
    MeasurableSet (degreeSizeEvent n r ks cs) :=
  (Set.to_countable _).image _ |>.measurableSet

theorem degreeSizeEvent_subset (n r : ℕ) (ks cs : Fin r → ℕ) :
    degreeSizeEvent n r ks cs ⊆ sizeEvent n := by
  rintro T ⟨t, ht, rfl⟩
  exact (toLocallyFinite_mem_sizeEvent_iff t n).mpr ht.1

/-- With no degree constraints the event is exactly the original size event. -/
@[simp] theorem degreeSizeEvent_no_marks (n : ℕ) (ks cs : Fin 0 → ℕ) :
    degreeSizeEvent n 0 ks cs = sizeEvent n := by
  rw [degreeSizeEvent, sizeEvent_eq_image]
  congr 1
  ext t
  simp

@[simp] theorem degreeSizeEvent_zero (r : ℕ) (ks cs : Fin r → ℕ) :
    degreeSizeEvent 0 r ks cs = ∅ :=
  Set.eq_empty_of_subset_empty (sizeEvent_zero ▸ degreeSizeEvent_subset 0 r ks cs)

/-- The mass of the marked size class is its finite-tree weight sum. -/
theorem bienaymeLaw_degreeSizeEvent (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n r : ℕ) (ks cs : Fin r → ℕ) :
    bienaymeLaw μ (degreeSizeEvent n r ks cs) =
      ∑' t : {t : PlaneTree // t.size = n}, PlaneTree.weight (fun d => μ {d}) t.val *
        (if ∀ j, t.val.degreeCount (ks j) = cs j then 1 else 0) := by
  classical
  have hA := measurableSet_degreeSizeEvent n r ks cs
  have hsub : degreeSizeEvent n r ks cs ⊆ {T | FiniteVertices T} :=
    fun T hT => (degreeSizeEvent_subset n r ks cs hT).1
  have h : bienaymeLaw μ (degreeSizeEvent n r ks cs) =
      (bienaymeLaw μ).restrict {T | FiniteVertices T} (degreeSizeEvent n r ks cs) := by
    rw [Measure.restrict_apply hA, Set.inter_eq_left.mpr hsub]
  rw [h, bienaymeLaw_restrict_finiteVertices, Measure.sum_apply _ hA]
  trans ∑' t : PlaneTree, Set.indicator {t : PlaneTree | t.size = n}
    (fun t => PlaneTree.weight (fun d => μ {d}) t *
      (if ∀ j, t.degreeCount (ks j) = cs j then 1 else 0)) t
  · apply tsum_congr
    intro t
    rw [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul]
    by_cases hn : t.size = n
    · by_cases hm : ∀ j, t.degreeCount (ks j) = cs j
      · simp [Set.indicator, hn, hm, toLocallyFinite_mem_degreeSizeEvent_iff]
      · simp [Set.indicator, hn, hm, toLocallyFinite_mem_degreeSizeEvent_iff]
    · simp [Set.indicator, hn, toLocallyFinite_mem_degreeSizeEvent_iff]
  · exact (tsum_subtype {t : PlaneTree | t.size = n} _).symm

/-- The degree-marked Kemperman identity in the actual offspring product law. -/
theorem natCast_mul_bienaymeLaw_degreeSizeEvent (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n r : ℕ) (ks cs : Fin r → ℕ) :
    (n : ℝ≥0∞) * bienaymeLaw μ (degreeSizeEvent n r ks cs) =
      Measure.pi (fun _ : Fin n => μ)
        (countBridges n ∩ {ω | ∀ j, (List.ofFn ω).count (ks j) = cs j}) := by
  rw [bienaymeLaw_degreeSizeEvent, PlaneTree.natCast_mul_tsum_weight_degreeCounts,
    pi_eq_tsum_indicator]

theorem isProbabilityMeasure_cond_degreeSizeEvent (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {n r : ℕ} {ks cs : Fin r → ℕ}
    (h : bienaymeLaw μ (degreeSizeEvent n r ks cs) ≠ 0) :
    IsProbabilityMeasure (bienaymeLaw μ)[|degreeSizeEvent n r ks cs] :=
  cond_isProbabilityMeasure h

/-- Marked conditional atoms, including zero conditioning mass. -/
theorem cond_degreeSizeEvent_singleton (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n r : ℕ) (ks cs : Fin r → ℕ) (t : PlaneTree) :
    (bienaymeLaw μ)[|degreeSizeEvent n r ks cs] {t.toLocallyFinite} =
      if t.size = n ∧ ∀ j, t.degreeCount (ks j) = cs j then
        PlaneTree.weight (fun d => μ {d}) t / bienaymeLaw μ (degreeSizeEvent n r ks cs)
      else 0 := by
  classical
  rw [cond_apply (measurableSet_degreeSizeEvent n r ks cs)]
  by_cases ht : t.size = n ∧ ∀ j, t.degreeCount (ks j) = cs j
  · rw [ite_eq_left ht, Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr
      ((toLocallyFinite_mem_degreeSizeEvent_iff t n r ks cs).mpr ht)),
      bienaymeLaw_toLocallyFinite, ENNReal.div_eq_inv_mul]
  · rw [ite_eq_right ht, Set.inter_singleton_eq_empty.mpr
      (fun h => ht ((toLocallyFinite_mem_degreeSizeEvent_iff t n r ks cs).mp h)),
      measure_empty, mul_zero]

end BGW.LocallyFinite
