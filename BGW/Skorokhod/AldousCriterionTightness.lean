/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Measurable
public import BGW.Skorokhod.Tightness

import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Tightness from probability bounds on source spaces

The random variables can live on different probability spaces. Bounds are imposed
directly on source events. This avoids any measurability assumption for the
càdlàg modulus: the final compact set is closed and hence Borel measurable.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace BGW.Skorokhod

variable {T : ℝ}

/-- Source-space versions of the boundedness and modulus estimates imply tightness of laws.

Reference: Billingsley 1999, Section 16. -/
private theorem isTightMeasureSet_of_source_cadlagModulus
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (X : ∀ n, Ω n → D T ℝ) (hX : ∀ n, Measurable (X n))
    (hbdd : ∀ η > 0, ∃ K : Set ℝ, Bornology.IsBounded K ∧
      ∀ n, P n {ω | ∃ t, X n ω t ∉ K} ≤ ENNReal.ofReal η)
    (hmod : ∀ ε > 0, ∀ η > 0, ∃ δ, 0 < δ ∧ δ < T ∧
      ∀ n, P n {ω | ε < cadlagModulus (X n ω) δ} ≤ ENNReal.ofReal η) :
    IsTightMeasureSet (range fun n => (P n).map (X n)) := by
  classical
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro η hη
  obtain ⟨err, herr, hsum⟩ := ENNReal.exists_pos_sum_of_countable hη.ne' (Option ℕ)
  obtain ⟨K, hK, hbound⟩ := hbdd (err none) (NNReal.coe_pos.mpr (herr none))
  let e (j : ℕ) : ℝ := 1 / (j + 1)
  have he (j : ℕ) : 0 < e j := by dsimp [e]; positivity
  choose δ hδ hδT hprob using fun j => hmod (e j) (he j) (err (some j))
    (NNReal.coe_pos.mpr (herr (some j)))
  let bad : Option ℕ → Set (D T ℝ)
    | none => {f | ∃ t, f t ∉ K}
    | some j => {f | e j < cadlagModulus f (δ j)}
  let A := (⋃ j, bad j)ᶜ
  have hvalues : ∀ f ∈ A, ∀ t, f t ∈ K := by
    intro f hf t
    by_contra ht
    exact hf (mem_iUnion.mpr ⟨none, t, ht⟩)
  have hsmall : ∀ ε > 0, ∃ d, 0 < d ∧ d < T ∧ ∀ f ∈ A, cadlagModulus f d ≤ ε := by
    intro ε hε
    have hlim : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
    refine ⟨δ j, hδ j, hδT j, fun f hf => ?_⟩
    have hnot : ¬ e j < cadlagModulus f (δ j) := fun h =>
      hf (mem_iUnion.mpr ⟨some j, h⟩)
    exact (le_of_not_gt hnot).trans hj.le
  refine ⟨closure A, isCompact_closure_of_cadlagModulus hK hvalues hsmall, ?_⟩
  rintro μ ⟨n, rfl⟩
  rw [Measure.map_apply (hX n) isClosed_closure.measurableSet.compl]
  have hbad (j) : P n ((X n) ⁻¹' bad j) ≤ (err j : ℝ≥0∞) := by
    cases j with
    | none => simpa only [bad, preimage, mem_ofPred_eq,
        ENNReal.ofReal_coe_nnreal] using hbound n
    | some j => simpa only [bad, preimage, mem_ofPred_eq,
        ENNReal.ofReal_coe_nnreal] using hprob j n
  calc
    P n ((X n) ⁻¹' (closure A)ᶜ) ≤ P n (⋃ j, (X n) ⁻¹' bad j) := measure_mono (by
      intro ω hω
      by_contra hnot
      apply hω
      apply subset_closure
      intro hmem
      obtain ⟨j, hj⟩ := mem_iUnion.mp hmem
      exact hnot (mem_iUnion.mpr ⟨j, hj⟩))
    _ ≤ ∑' j, P n ((X n) ⁻¹' bad j) := measure_iUnion_le _
    _ ≤ ∑' j, (err j : ℝ≥0∞) := ENNReal.tsum_le_tsum hbad
    _ ≤ η := hsum.le

private theorem exists_compact_initial_source
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (X : ∀ n, Ω n → D T ℝ) (hX : ∀ n, Measurable (X n))
    (htight : ∀ n, IsTightMeasureSet {(P n).map (X n)}) (N : ℕ)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ C : Set (D T ℝ), IsCompact C ∧ ∀ n < N, P n ((X n) ⁻¹' Cᶜ) ≤ η := by
  classical
  have h (n : Fin N) : ∃ C : Set (D T ℝ), IsCompact C ∧ P n ((X n) ⁻¹' Cᶜ) ≤ η := by
    obtain ⟨C, hC, hprob⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
      (htight n) η hη
    refine ⟨C, hC, ?_⟩
    rw [← Measure.map_apply (hX n) hC.isClosed.measurableSet.compl]
    exact hprob _ (mem_singleton _)
  choose C hC hprob using h
  refine ⟨⋃ n, C n, isCompact_iUnion hC, fun n hn => ?_⟩
  exact (measure_mono (preimage_mono (compl_subset_compl.mpr
    (subset_iUnion C ⟨n, hn⟩)))).trans (hprob ⟨n, hn⟩)

/-- Eventual source-space estimates suffice when the finitely many initial laws are tight.

Reference: Billingsley 1999, Section 16. -/
theorem isTightMeasureSet_of_source_cadlagModulus_eventually
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (X : ∀ n, Ω n → D T ℝ) (hX : ∀ n, Measurable (X n))
    (htight : ∀ n, IsTightMeasureSet {(P n).map (X n)})
    (hbdd : ∀ η > 0, ∃ K : Set ℝ, Bornology.IsBounded K ∧
      ∃ N, ∀ n ≥ N, P n {ω | ∃ t, X n ω t ∉ K} ≤ ENNReal.ofReal η)
    (hmod : ∀ ε > 0, ∀ η > 0, ∃ δ, 0 < δ ∧ δ < T ∧
      ∃ N, ∀ n ≥ N, P n {ω | ε < cadlagModulus (X n ω) δ} ≤ ENNReal.ofReal η) :
    IsTightMeasureSet (range fun n => (P n).map (X n)) := by
  apply isTightMeasureSet_of_source_cadlagModulus P X hX
  · intro η hη
    obtain ⟨K, hK, N, htail⟩ := hbdd η hη
    obtain ⟨C, hC, hprob⟩ := exists_compact_initial_source P X hX htight N
      (ENNReal.ofReal_pos.mpr hη)
    obtain ⟨L, hL, hvalues⟩ := exists_isBounded_values_of_isCompact hC
    refine ⟨K ∪ L, hK.union hL, fun n => ?_⟩
    by_cases hn : N ≤ n
    · exact (measure_mono (by
        rintro ω ⟨t, ht⟩
        exact ⟨t, fun h => ht (Or.inl h)⟩)).trans (htail n hn)
    · apply le_trans (measure_mono ?_) (hprob n (lt_of_not_ge hn))
      rintro ω ⟨t, ht⟩ hω
      exact ht (Or.inr (hvalues (X n ω) hω t))
  · intro ε hε η hη
    obtain ⟨δ, hδ, hδT, N, htail⟩ := hmod ε hε η hη
    obtain ⟨C, hC, hprob⟩ := exists_compact_initial_source P X hX htight N
      (ENNReal.ofReal_pos.mpr hη)
    obtain ⟨d, hd, hdT, hsmall⟩ := exists_uniform_cadlagModulus_of_isCompact hC
      (hδ.trans hδT) hε
    refine ⟨min δ d, lt_min hδ hd, (min_le_left _ _).trans_lt hδT, fun n => ?_⟩
    by_cases hn : N ≤ n
    · apply le_trans (measure_mono ?_) (htail n hn)
      intro ω hω
      exact hω.trans_le (cadlagModulus_mono (X n ω) (min_le_left _ _) hδ hδT)
    · apply le_trans (measure_mono ?_) (hprob n (lt_of_not_ge hn))
      intro ω hω hωC
      exact (not_lt_of_ge ((cadlagModulus_mono (X n ω) (min_le_right _ _) hd hdT).trans
        (hsmall (X n ω) hωC))) hω

end BGW.Skorokhod
