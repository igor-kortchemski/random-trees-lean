/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.GHPChainMeasures
public import BGW.MetricMeasure.CompactHausdorffHull
public import BGW.MetricMeasure.GHPSeparability
public import BGW.MetricMeasure.CompactSupportLimit
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Topology.MetricSpace.Polish

/-!
# Completeness of the whole-space GHP metric

Fast successive couplings are realized in one complete ambient space. Their
compact images have a Hausdorff limit and all lie in a compact hull. Pushed
probability measures have a weakly convergent subsequence on that hull; its
ambient pushforward is carried by the limiting compact set. Restriction
produces a probability on that entire set. This gives a GHP limit and hence
completeness, without requiring full support or separability of the initially
constructed ambient space.

Adapted from `Freezing2/Geometry/GHPCompleteness.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
-/

@[expose] public section

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped Topology

universe u

namespace BGW.MetricMeasure

/-- A geometric sequence of actual measured coupling costs has a limit
represented by a compact metric space with a Borel probability measure. -/
theorem exists_measured_limit_of_geometric_couplings
    (X : ℕ → CompactMeasuredSpace.{u})
    (C : ∀ n, GHPCoupling (X n) (X (n + 1)))
    (hC : ∀ n, (C n).cost ((X n).law : Measure (X n))
      ((X (n + 1)).law : Measure (X (n + 1))) < (1 / 2 : ℝ) ^ n) :
    ∃ Y : CompactMeasuredSpace.{u},
      Tendsto (fun n ↦ toMeasuredGHSpace (X n)) atTop (𝓝 (toMeasuredGHSpace Y)) := by
  classical
  obtain ⟨Z, m, hcomplete, ι, hι, hcost⟩ :=
    GHPChain.exists_complete_measured_realization (fun n ↦ X n)
      (fun n ↦ (X n).law : ∀ n, Measure (X n)) C
  let := m
  let : TopologicalSpace Z := m.toUniformSpace.toTopologicalSpace
  let : MeasurableSpace Z := borel Z
  let : BorelSpace Z := ⟨rfl⟩
  let : CompleteSpace Z := hcomplete
  let S : ℕ → NonemptyCompacts Z := fun n ↦
    ⟨⟨range (ι n), isCompact_range (hι n).continuous⟩, range_nonempty _⟩
  have hstepS (n : ℕ) : dist (S n) (S (n + 1)) ≤ (1 / 2 : ℝ) ^ n := by
    change hausdorffDist (range (ι n)) (range (ι (n + 1))) ≤ _
    exact (le_add_of_nonneg_left ENNReal.toReal_nonneg).trans
      ((hcost n).trans (hC n).le)
  have hcS : CauchySeq S := cauchySeq_of_le_geometric (1 / 2) 1 (by norm_num)
    (fun n ↦ by simpa only [one_mul] using hstepS n)
  obtain ⟨L, K, hSL, hLK, hSK⟩ := exists_common_compact_of_cauchySeq S hcS
  let ιK : ∀ n, X n → K := fun n x ↦ ⟨ι n x, hSK n (mem_range_self x)⟩
  have hιK (n : ℕ) : Isometry (ιK n) := Isometry.of_dist_eq (fun x y ↦ (hι n).dist_eq x y)
  let ν : ℕ → ProbabilityMeasure K := fun n ↦ (X n).law.map (ιK n)
  have hmapK (n : ℕ) : (ν n : Measure K).map (fun x : K ↦ (x : Z)) =
      ((X n).law : Measure (X n)).map (ι n) := by
    change (((X n).law : Measure (X n)).map (ιK n)).map _ = _
    rw [Measure.map_map continuous_subtype_val.measurable (hιK n).continuous.measurable]
    rfl
  obtain ⟨ν₀, φ, hφ, hν⟩ := CompactSpace.tendsto_subseq ν
  let νZ : ProbabilityMeasure Z := ν₀.map (fun x : K ↦ (x : Z))
  let νs : ℕ → ProbabilityMeasure Z := fun n ↦ (X (φ n)).law.map (ι (φ n))
  have hνZ : Tendsto νs atTop (𝓝 νZ) := by
    have h := (ProbabilityMeasure.continuous_map continuous_subtype_val).tendsto ν₀ |>.comp hν
    convert h using 1
    funext n
    apply ProbabilityMeasure.toMeasure_injective
    exact (hmapK (φ n)).symm
  have hs : ∀ n, (νs n : Measure Z) (S (φ n) : Set Z) = 1 := by
    intro n
    change (((X (φ n)).law : Measure (X (φ n))).map (ι (φ n))) (range (ι (φ n))) = 1
    rw [Measure.map_apply (hι _).continuous.measurable (isCompact_range (hι _).continuous).measurableSet,
      preimage_range, measure_univ]
  have hsupport := probabilityMeasure_compact_limit_eq_one hνZ
    (hSL.comp hφ.tendsto_atTop) hs
  obtain ⟨η, hη⟩ := exists_probabilityMeasure_on_compact νZ L hsupport
  let Y : CompactMeasuredSpace.{u} := CompactMeasuredSpace.of ↥L η
  have hLP := tendsto_levyProkhorovDist_of_tendsto hν
  have hHaus : Tendsto (fun n ↦ hausdorffDist (range (ι (φ n))) (L : Set Z))
      atTop (𝓝 0) := by
    have h := (hSL.comp hφ.tendsto_atTop).dist
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ L) atTop (𝓝 L))
    have h' : Tendsto (fun n ↦ dist (S (φ n)) L) atTop (𝓝 0) := by
      simpa only [dist_self, Function.comp_def] using h
    convert h' using 1
    funext n
    rfl
  have hdist0 : Tendsto (fun n ↦ ghpDistance ((X (φ n)).law : Measure (X (φ n)))
      (η : Measure ↥L)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n ↦ ghpDistance_nonneg _ _) _
      (by simpa only [zero_add] using hLP.add hHaus)
    intro n
    have hbound := ghpDistance_le_of_isometries
      ((X (φ n)).law : Measure (X (φ n))) (η : Measure ↥L) Z
      (ι (φ n)) (fun x : L ↦ (x : Z)) (hι _) isometry_subtype_coe
    have hprob : levyProkhorovDist (((X (φ n)).law : Measure (X (φ n))).map (ι (φ n)))
        ((η : Measure ↥L).map (fun x : L ↦ (x : Z))) ≤
          levyProkhorovDist (ν (φ n) : Measure K) (ν₀ : Measure K) := by
      rw [hη, ← hmapK]
      exact levyProkhorovDist_map_le _ _ (isometry_subtype_coe.lipschitzWith)
    have hRange : range (fun x : L ↦ (x : Z)) = (L : Set Z) := Subtype.range_coe
    rw [hRange] at hbound
    exact hbound.trans (add_le_add hprob le_rfl)
  have hsub : Tendsto ((fun n ↦ toMeasuredGHSpace (X n)) ∘ φ)
      atTop (𝓝 (toMeasuredGHSpace Y)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact hdist0
  have hstep (n : ℕ) : dist (toMeasuredGHSpace (X n)) (toMeasuredGHSpace (X (n + 1))) ≤
      (1 / 2 : ℝ) ^ n := by
    have h := ghpDistance_le_of_isometries
      ((X n).law : Measure (X n)) ((X (n + 1)).law : Measure (X (n + 1)))
      (C n).ambient (C n).left (C n).right (C n).left_isometry (C n).right_isometry
    exact h.trans (hC n).le
  have hc : CauchySeq (fun n ↦ toMeasuredGHSpace (X n)) :=
    cauchySeq_of_le_geometric (1 / 2) 1 (by norm_num)
      (fun n ↦ by simpa only [one_mul] using hstep n)
  exact ⟨Y, tendsto_nhds_of_cauchySeq_of_subseq hc hφ.tendsto_atTop hsub⟩

namespace MeasuredGHSpace

/-- The exact whole-space GHP metric is complete. -/
noncomputable instance : CompleteSpace MeasuredGHSpace.{u} := by
  let d : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) ^ n
  refine Metric.complete_of_convergent_controlled_sequences d (fun _ ↦ by positivity) ?_
  intro u hu
  let X : ℕ → CompactMeasuredSpace.{u} := fun n ↦ Quotient.out (u n)
  have hX (n : ℕ) : toMeasuredGHSpace (X n) = u n := Quotient.out_eq (u n)
  have hdist (n : ℕ) : ghpDistance ((X n).law : Measure (X n))
      ((X (n + 1)).law : Measure (X (n + 1))) < d n := by
    have h := hu n n (n + 1) le_rfl (Nat.le_succ n)
    rw [← hX n, ← hX (n + 1)] at h
    exact h
  choose C hC using fun n ↦ exists_ghpCoupling_cost_lt
    ((X n).law : Measure (X n)) ((X (n + 1)).law : Measure (X (n + 1))) (hdist n)
  obtain ⟨Y, hY⟩ := exists_measured_limit_of_geometric_couplings X C hC
  exact ⟨toMeasuredGHSpace Y, by simpa only [hX] using hY⟩

/-- The source whole-space quotient, with its already defined GHP topology,
is a Polish space. -/
theorem polishSpace : PolishSpace MeasuredGHSpace.{u} := inferInstance

end MeasuredGHSpace
end BGW.MetricMeasure
