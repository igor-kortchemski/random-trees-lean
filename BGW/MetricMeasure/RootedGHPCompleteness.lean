/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.GHPCompleteness
public import BGW.MetricMeasure.RootedGHPSeparability

/-!
# Completeness of the existing rooted GHP metric

The successive rooted couplings are glued in one complete ambient space.
The same isometric factorizations retain their root distances and their
Lévy–Prokhorov and whole-carrier Hausdorff costs. The roots form a Cauchy
sequence, whose limit lies in the limiting compact carrier. The limiting
probability is constructed on that entire carrier, without requiring the
root to belong to its support.

This extends `BGW.MetricMeasure.GHPCompleteness` and its common-space proof,
adapted from `Freezing2/Geometry/GHPCompleteness.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0). No new quotient,
metric, topology, or measurable-space instance is introduced.
-/

@[expose] public section

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped Topology

universe u

namespace BGW.MetricMeasure

private theorem exists_rootedGHPCoupling_cost_lt {X Y : Type u}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (μ : Measure X) (ν : Measure Y) (x : X) (y : Y) {ε : ℝ}
    (hε : rootedGHPDistance μ ν x y < ε) :
    ∃ C : GHPCoupling X Y, C.rootedCost μ ν x y < ε := by
  obtain ⟨r, hr, hlt⟩ := exists_lt_of_csInf_lt (rootedGHPCosts_nonempty μ ν x y) hε
  obtain ⟨C, rfl⟩ := hr
  exact ⟨C, hlt⟩

/-- Geometrically small actual rooted coupling costs yield a rooted compact measured limit.
The probability and the limiting root both live on the full Hausdorff-limit carrier. -/
theorem exists_rooted_measured_limit_of_geometric_couplings
    (X : ℕ → RootedCompactMeasuredSpace.{u})
    (C : ∀ n, GHPCoupling (X n).space (X (n + 1)).space)
    (hC : ∀ n, (C n).rootedCost
      ((X n).space.law : Measure (X n).space)
      ((X (n + 1)).space.law : Measure (X (n + 1)).space)
      (X n).root (X (n + 1)).root < (1 / 2 : ℝ) ^ n) :
    ∃ Y : RootedCompactMeasuredSpace.{u},
      Tendsto (fun n ↦ toRootedMeasuredGHSpace (X n)) atTop
        (𝓝 (toRootedMeasuredGHSpace Y)) := by
  classical
  obtain ⟨Z, m, hcomplete, ι, hι, hfactor⟩ :=
    GHPChain.exists_complete_realization (fun n ↦ (X n).space) C
  let := m
  let : TopologicalSpace Z := m.toUniformSpace.toTopologicalSpace
  let : MeasurableSpace Z := borel Z
  let : BorelSpace Z := ⟨rfl⟩
  let : CompleteSpace Z := hcomplete
  let r : ℕ → Z := fun n ↦ ι n (X n).root
  let S : ℕ → NonemptyCompacts Z := fun n ↦
    ⟨⟨range (ι n), isCompact_range (hι n).continuous⟩, range_nonempty _⟩
  have hcost (n : ℕ) : dist (r n) (r (n + 1)) +
      (levyProkhorovDist
        (((X n).space.law : Measure (X n).space).map (ι n))
        (((X (n + 1)).space.law : Measure (X (n + 1)).space).map (ι (n + 1))) +
        hausdorffDist (range (ι n)) (range (ι (n + 1)))) ≤
      (C n).rootedCost ((X n).space.law : Measure (X n).space)
        ((X (n + 1)).space.law : Measure (X (n + 1)).space)
        (X n).root (X (n + 1)).root := by
    obtain ⟨j, hj, hl, hr⟩ := hfactor n
    dsimp only [r]
    rw [hl, hr]
    change dist (j ((C n).left (X n).root)) (j ((C n).right (X (n + 1)).root)) + _ ≤ _
    rw [hj.dist_eq]
    have hc := (C n).cost_le_after_isometry
      ((X n).space.law : Measure (X n).space)
      ((X (n + 1)).space.law : Measure (X (n + 1)).space) j hj
    dsimp only [GHPCoupling.rootedCost]
    linarith only [hc]
  have hstepS (n : ℕ) : dist (S n) (S (n + 1)) ≤ (1 / 2 : ℝ) ^ n := by
    change hausdorffDist (range (ι n)) (range (ι (n + 1))) ≤ _
    exact (le_add_of_nonneg_left ENNReal.toReal_nonneg).trans
      ((le_add_of_nonneg_left dist_nonneg).trans ((hcost n).trans (hC n).le))
  have hcS : CauchySeq S := cauchySeq_of_le_geometric (1 / 2) 1 (by norm_num)
    (fun n ↦ by simpa only [one_mul] using hstepS n)
  obtain ⟨L, K, hSL, hLK, hSK⟩ := exists_common_compact_of_cauchySeq S hcS
  have hstepR (n : ℕ) : dist (r n) (r (n + 1)) ≤ (1 / 2 : ℝ) ^ n := by
    exact (le_add_of_nonneg_right (add_nonneg ENNReal.toReal_nonneg hausdorffDist_nonneg)).trans
      ((hcost n).trans (hC n).le)
  have hcR : CauchySeq r := cauchySeq_of_le_geometric (1 / 2) 1 (by norm_num)
    (fun n ↦ by simpa only [one_mul] using hstepR n)
  obtain ⟨ρ, hr⟩ := cauchySeq_tendsto_of_complete hcR
  have hρL : ρ ∈ (L : Set Z) := by
    apply (L.isCompact.isClosed.mem_iff_infDist_zero L.nonempty).mpr
    have hcont : Continuous
        (fun p : Z × NonemptyCompacts Z ↦ infDist p.1 (p.2 : Set Z)) :=
      (NonemptyCompacts.uniformContinuous_infDist (α := Z)).continuous
    have ht : Tendsto (fun n ↦ infDist (r n) (S n : Set Z)) atTop
        (𝓝 (infDist ρ (L : Set Z))) := by
      simpa only [Function.comp_def] using
        (hcont.tendsto (ρ, L)).comp (hr.prodMk_nhds hSL)
    have hzero (n : ℕ) : infDist (r n) (S n : Set Z) = 0 :=
      infDist_zero_of_mem (mem_range_self (X n).root)
    have htzero : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 (infDist ρ (L : Set Z))) := by
      simpa only [hzero] using ht
    exact (tendsto_nhds_unique tendsto_const_nhds htzero).symm
  let ιK : ∀ n, (X n).space → K := fun n x ↦ ⟨ι n x, hSK n (mem_range_self x)⟩
  have hιK (n : ℕ) : Isometry (ιK n) := Isometry.of_dist_eq (fun x y ↦ (hι n).dist_eq x y)
  let ν : ℕ → ProbabilityMeasure K := fun n ↦ (X n).space.law.map (ιK n)
  have hmapK (n : ℕ) : (ν n : Measure K).map (fun x : K ↦ (x : Z)) =
      ((X n).space.law : Measure (X n).space).map (ι n) := by
    change (((X n).space.law : Measure (X n).space).map (ιK n)).map _ = _
    rw [Measure.map_map continuous_subtype_val.measurable (hιK n).continuous.measurable]
    rfl
  obtain ⟨ν₀, φ, hφ, hν⟩ := CompactSpace.tendsto_subseq ν
  let νZ : ProbabilityMeasure Z := ν₀.map (fun x : K ↦ (x : Z))
  let νs : ℕ → ProbabilityMeasure Z := fun n ↦ (X (φ n)).space.law.map (ι (φ n))
  have hνZ : Tendsto νs atTop (𝓝 νZ) := by
    have h := (ProbabilityMeasure.continuous_map continuous_subtype_val).tendsto ν₀ |>.comp hν
    convert h using 1
    funext n
    apply ProbabilityMeasure.toMeasure_injective
    exact (hmapK (φ n)).symm
  have hs : ∀ n, (νs n : Measure Z) (S (φ n) : Set Z) = 1 := by
    intro n
    change (((X (φ n)).space.law : Measure (X (φ n)).space).map (ι (φ n)))
      (range (ι (φ n))) = 1
    rw [Measure.map_apply (hι _).continuous.measurable
      (isCompact_range (hι _).continuous).measurableSet, preimage_range, measure_univ]
  have hsupport := probabilityMeasure_compact_limit_eq_one hνZ
    (hSL.comp hφ.tendsto_atTop) hs
  obtain ⟨η, hη⟩ := exists_probabilityMeasure_on_compact νZ L hsupport
  let Y : RootedCompactMeasuredSpace.{u} :=
    ⟨CompactMeasuredSpace.of ↥L η, ⟨ρ, hρL⟩⟩
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
  have hRoot : Tendsto (fun n ↦ dist (r (φ n)) ρ) atTop (𝓝 0) := by
    have h := (hr.comp hφ.tendsto_atTop).dist
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ ρ) atTop (𝓝 ρ))
    simpa only [dist_self, Function.comp_def] using h
  have hdist0 : Tendsto (fun n ↦ rootedGHPDistance
      ((X (φ n)).space.law : Measure (X (φ n)).space) (η : Measure ↥L)
      (X (φ n)).root (⟨ρ, hρL⟩ : ↥L)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n ↦ rootedGHPDistance_nonneg _ _ _ _) _
      (by simpa only [zero_add] using hRoot.add (hLP.add hHaus))
    intro n
    have hbound := rootedGHPDistance_le_of_isometries
      ((X (φ n)).space.law : Measure (X (φ n)).space) (η : Measure ↥L)
      (X (φ n)).root (⟨ρ, hρL⟩ : ↥L) Z
      (ι (φ n)) (fun x : L ↦ (x : Z)) (hι _) isometry_subtype_coe
    have hprob : levyProkhorovDist
        (((X (φ n)).space.law : Measure (X (φ n)).space).map (ι (φ n)))
        ((η : Measure ↥L).map (fun x : L ↦ (x : Z))) ≤
          levyProkhorovDist (ν (φ n) : Measure K) (ν₀ : Measure K) := by
      rw [hη, ← hmapK]
      exact levyProkhorovDist_map_le _ _ (isometry_subtype_coe.lipschitzWith)
    have hRange : range (fun x : L ↦ (x : Z)) = (L : Set Z) := Subtype.range_coe
    rw [hRange] at hbound
    exact hbound.trans (add_le_add le_rfl (add_le_add hprob le_rfl))
  have hsub : Tendsto ((fun n ↦ toRootedMeasuredGHSpace (X n)) ∘ φ)
      atTop (𝓝 (toRootedMeasuredGHSpace Y)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact hdist0
  have hstep (n : ℕ) :
      dist (toRootedMeasuredGHSpace (X n)) (toRootedMeasuredGHSpace (X (n + 1))) ≤
        (1 / 2 : ℝ) ^ n := by
    exact (rootedGHPDistance_le_of_coupling
      ((X n).space.law : Measure (X n).space)
      ((X (n + 1)).space.law : Measure (X (n + 1)).space)
      (X n).root (X (n + 1)).root (C n)).trans (hC n).le
  have hc : CauchySeq (fun n ↦ toRootedMeasuredGHSpace (X n)) :=
    cauchySeq_of_le_geometric (1 / 2) 1 (by norm_num)
      (fun n ↦ by simpa only [one_mul] using hstep n)
  exact ⟨Y, tendsto_nhds_of_cauchySeq_of_subseq hc hφ.tendsto_atTop hsub⟩

namespace RootedMeasuredGHSpace

/-- The existing whole-carrier rooted GHP metric is complete. -/
noncomputable instance : CompleteSpace RootedMeasuredGHSpace.{u} := by
  let d : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) ^ n
  refine Metric.complete_of_convergent_controlled_sequences d (fun _ ↦ by positivity) ?_
  intro u hu
  let X : ℕ → RootedCompactMeasuredSpace.{u} := fun n ↦ Quotient.out (u n)
  have hX (n : ℕ) : toRootedMeasuredGHSpace (X n) = u n := Quotient.out_eq (u n)
  have hdist (n : ℕ) : rootedGHPDistance
      ((X n).space.law : Measure (X n).space)
      ((X (n + 1)).space.law : Measure (X (n + 1)).space)
      (X n).root (X (n + 1)).root < d n := by
    have h := hu n n (n + 1) le_rfl (Nat.le_succ n)
    rw [← hX n, ← hX (n + 1)] at h
    exact h
  choose C hC using fun n ↦ exists_rootedGHPCoupling_cost_lt
    ((X n).space.law : Measure (X n).space)
    ((X (n + 1)).space.law : Measure (X (n + 1)).space)
    (X n).root (X (n + 1)).root (hdist n)
  obtain ⟨Y, hY⟩ := exists_rooted_measured_limit_of_geometric_couplings X C hC
  exact ⟨toRootedMeasuredGHSpace Y, by simpa only [hX] using hY⟩

/-- The existing rooted GHP metric topology is Polish. -/
theorem polishSpace : PolishSpace RootedMeasuredGHSpace.{u} := inferInstance

end RootedMeasuredGHSpace
end BGW.MetricMeasure
