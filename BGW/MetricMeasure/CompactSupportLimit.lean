/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Weak limits carried by Hausdorff limits of compact sets

The full compact carrier is retained, even when the limiting measure has
smaller support. Restriction to the carrier is an actual comap probability
measure whose inclusion pushforward recovers the ambient probability.

Adapted from `Freezing2/Probability/CompactSupportLimit.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
-/

@[expose] public section

open Filter MeasureTheory Set Metric TopologicalSpace
open scoped Topology ENNReal

namespace BGW.MetricMeasure

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Simultaneous weak and Hausdorff convergence preserves concentration on
the limiting compact carrier; no full-support hypothesis is needed. -/
theorem probabilityMeasure_compact_limit_eq_one
    {μ : ℕ → ProbabilityMeasure X} {ν : ProbabilityMeasure X}
    {S : ℕ → NonemptyCompacts X} {L : NonemptyCompacts X}
    (hμ : Tendsto μ atTop (𝓝 ν)) (hS : Tendsto S atTop (𝓝 L))
    (hs : ∀ n, (μ n : Measure X) (S n : Set X) = 1) :
    (ν : Measure X) (L : Set X) = 1 := by
  have hneigh (ε : ℝ) (hε : 0 < ε) :
      (ν : Measure X) {x | infDist x (L : Set X) ≤ ε} = 1 := by
    have hclosed : IsClosed {x | infDist x (L : Set X) ≤ ε} :=
      isClosed_le (continuous_infDist_pt _) continuous_const
    have hevent : (fun n ↦ (μ n : Measure X) {x | infDist x (L : Set X) ≤ ε})
        =ᶠ[atTop] fun _ ↦ (1 : ℝ≥0∞) := by
      filter_upwards [(Metric.tendsto_nhds.mp hS) ε hε] with n hn
      apply le_antisymm prob_le_one
      rw [← hs n]
      apply measure_mono
      intro x hx
      exact (infDist_le_hausdorffDist_of_mem hx
        (hausdorffEDist_ne_top_of_nonempty_of_bounded (S n).nonempty L.nonempty
          (S n).isCompact.isBounded L.isCompact.isBounded)).trans
        (by simpa only [TopologicalSpace.NonemptyCompacts.dist_eq] using hn.le)
    have h := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ hclosed
    rw [limsup_congr hevent, limsup_const] at h
    exact le_antisymm prob_le_one h
  apply (mem_ae_iff_prob_eq_one L.isCompact.measurableSet).mp
  have ha : ∀ m : ℕ, ∀ᵐ x ∂(ν : Measure X),
      infDist x (L : Set X) ≤ 1 / ((m : ℝ) + 1) := by
    intro m
    exact (mem_ae_iff_prob_eq_one (isClosed_le (continuous_infDist_pt _) continuous_const).measurableSet).mpr
      (hneigh (1 / ((m : ℝ) + 1)) (by positivity))
  filter_upwards [ae_all_iff.mpr ha] with x hx
  apply (L.isCompact.isClosed.mem_iff_infDist_zero L.nonempty).mpr
  apply le_antisymm _ infDist_nonneg
  have ht : Tendsto (fun m : ℕ ↦ 1 / ((m : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds ht (Eventually.of_forall hx)

/-- Restrict a probability carried by a compact set to that entire set.
Points of mass zero are retained in the subtype. -/
theorem exists_probabilityMeasure_on_compact (ν : ProbabilityMeasure X)
    (L : NonemptyCompacts X) (hν : (ν : Measure X) (L : Set X) = 1) :
    ∃ η : ProbabilityMeasure ↥L,
      (η : Measure ↥L).map (fun x : ↥L ↦ (x : X)) = (ν : Measure X) := by
  let η : Measure ↥L := (ν : Measure X).comap (fun x : ↥L ↦ (x : X))
  have hprob : IsProbabilityMeasure η := ⟨by
    change (ν : Measure X).comap (Subtype.val : ↥(L : Set X) → X) Set.univ = 1
    rw [comap_subtype_coe_apply L.isCompact.measurableSet,
      Set.image_univ, Subtype.range_coe]
    exact hν⟩
  refine ⟨⟨η, hprob⟩, ?_⟩
  change ((ν : Measure X).comap (Subtype.val : ↥(L : Set X) → X)).map Subtype.val =
    (ν : Measure X)
  rw [map_comap_subtype_coe L.isCompact.measurableSet]
  exact Measure.restrict_eq_self_of_ae_mem
    ((mem_ae_iff_prob_eq_one L.isCompact.measurableSet).mpr hν)

end BGW.MetricMeasure

