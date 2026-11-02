/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.GHPSeparability
public import BGW.MetricMeasure.GHPChainGluing
public import BGW.MetricMeasure.CompactHausdorffHull
public import BGW.MetricMeasure.GHPUnderlyingProjection
public import BGW.MetricMeasure.CompactSupportLimit
public import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Compactness transfer from GH to GHP

Hausdorff-precompact full carriers can be put in a common compact hull.
Probability compactness on that hull gives a measured convergent subsequence,
regardless of the original measures. The limit retains the entire Hausdorff
carrier. Consequently the inverse image of a compact GH set under the
underlying-space projection is compact for the exact GHP metric.

Adapted from `Freezing2/Geometry/GHPCompactness.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
-/

@[expose] public section

open MeasureTheory Metric Set Filter TopologicalSpace GromovHausdorff
open scoped Topology Uniformity

universe u

namespace BGW.MetricMeasure

/-- Hausdorff-Cauchy full carrier images in a complete common ambient space
have a GHP-convergent measured subsequence. The measures need not be Cauchy. -/
theorem exists_measured_subsequence_of_common_ambient
    (X : ℕ → CompactMeasuredSpace.{u}) {Z : Type u}
    [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z] [CompleteSpace Z]
    (ι : ∀ n, X n → Z) (hι : ∀ n, Isometry (ι n))
    (S : ℕ → NonemptyCompacts Z) (hS : ∀ n, (S n : Set Z) = range (ι n))
    (hcS : CauchySeq S) :
    ∃ Y : CompactMeasuredSpace.{u}, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto ((fun n ↦ toMeasuredGHSpace (X n)) ∘ φ) atTop (𝓝 (toMeasuredGHSpace Y)) := by
  classical
  borelize Z
  obtain ⟨L, K, hSL, hLK, hSK⟩ := exists_common_compact_of_cauchySeq S hcS
  let ιK : ∀ n, X n → K := fun n x ↦ ⟨ι n x, hSK n (by rw [hS n]; exact mem_range_self x)⟩
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
    rw [hS]
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
    simpa only [TopologicalSpace.NonemptyCompacts.dist_eq, hS] using h'
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
  exact ⟨Y, φ, hφ, hsub⟩

/-- GH-Cauchy underlying carriers admit a GHP-convergent subsequence for
arbitrary Borel probability measures on their entire carriers. -/
theorem exists_measured_subsequence_of_gh_cauchy
    (X : ℕ → CompactMeasuredSpace.{u})
    (hc : CauchySeq (fun n ↦ toGHSpace (X n))) :
    ∃ Y : CompactMeasuredSpace.{u}, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto ((fun n ↦ toMeasuredGHSpace (X n)) ∘ φ) atTop (𝓝 (toMeasuredGHSpace Y)) := by
  classical
  have hV (n : ℕ) : {p : GHSpace × GHSpace | dist p.1 p.2 < (1 / 2 : ℝ) ^ n}
      ∈ 𝓤 GHSpace := dist_mem_uniformity (by positivity)
  obtain ⟨σ, hσ, hstep⟩ := hc.subseq_mem hV
  let C : ∀ n, GHPCoupling (X (σ n)) (X (σ (n + 1))) := fun n ↦
    { ambient := OptimalGHCoupling (X (σ n)) (X (σ (n + 1)))
      metric := inferInstance
      left := optimalGHInjl _ _
      right := optimalGHInjr _ _
      left_isometry := isometry_optimalGHInjl _ _
      right_isometry := isometry_optimalGHInjr _ _ }
  obtain ⟨Z, m, hcomplete, ι, hι, hfactor⟩ :=
    GHPChain.exists_complete_realization (fun n ↦ X (σ n)) C
  let := m
  let : TopologicalSpace Z := m.toUniformSpace.toTopologicalSpace
  let : MeasurableSpace Z := borel Z
  let : BorelSpace Z := ⟨rfl⟩
  let : CompleteSpace Z := hcomplete
  let S : ℕ → NonemptyCompacts Z := fun n ↦
    ⟨⟨range (ι n), isCompact_range (hι n).continuous⟩, range_nonempty _⟩
  have hdist (n : ℕ) : dist (S n) (S (n + 1)) ≤ (1 / 2 : ℝ) ^ n := by
    change hausdorffDist (range (ι n)) (range (ι (n + 1))) ≤ _
    obtain ⟨j, hj, hl, hr⟩ := hfactor n
    rw [hl, hr, range_comp, range_comp, hausdorffDist_image hj]
    change hausdorffDist (range (optimalGHInjl (X (σ n)) (X (σ (n + 1)))))
      (range (optimalGHInjr (X (σ n)) (X (σ (n + 1))))) ≤ _
    rw [hausdorffDist_optimal]
    have h : dist (toGHSpace (X (σ (n + 1)))) (toGHSpace (X (σ n))) < (1 / 2 : ℝ) ^ n :=
      hstep n
    simpa only [ghDist, dist_comm] using h.le
  have hcS : CauchySeq S := cauchySeq_of_le_geometric (1 / 2) 1 (by norm_num)
    (fun n ↦ by simpa only [one_mul] using hdist n)
  obtain ⟨Y, τ, hτ, hlim⟩ := exists_measured_subsequence_of_common_ambient
    (fun n ↦ X (σ n)) ι hι S (fun _ ↦ rfl) hcS
  exact ⟨Y, σ ∘ τ, hσ.comp hτ, by simpa only [Function.comp_def] using hlim⟩

namespace MeasuredGHSpace

/-- Forgetting the measure has compact inverse images of compact GH sets.
No uniform lower bound on masses, or full-support hypothesis, is imposed. -/
theorem isCompact_preimage_underlyingGH {A : Set GHSpace} (hA : IsCompact A) :
    IsCompact (underlyingGH.{u} ⁻¹' A) := by
  classical
  apply IsSeqCompact.isCompact
  intro u hu
  obtain ⟨a, ha, σ, hσ, hGH⟩ := hA.tendsto_subseq
    (x := fun n ↦ underlyingGH (u n)) (fun n ↦ hu n)
  let X : ℕ → CompactMeasuredSpace.{u} := fun n ↦ Quotient.out (u (σ n))
  have hX (n : ℕ) : toMeasuredGHSpace (X n) = u (σ n) := Quotient.out_eq _
  have hrep (n : ℕ) : toGHSpace (X n) = underlyingGH (u (σ n)) := by
    rw [← hX]
    rfl
  have hc : CauchySeq (fun n ↦ toGHSpace (X n)) := by
    simpa only [hrep, Function.comp_def] using hGH.cauchySeq
  obtain ⟨Y, τ, hτ, hY⟩ := exists_measured_subsequence_of_gh_cauchy X hc
  have hlim : Tendsto (u ∘ (σ ∘ τ)) atTop (𝓝 (toMeasuredGHSpace Y)) := by
    simpa only [Function.comp_def, hX] using hY
  have hlimGH : Tendsto (underlyingGH ∘ u ∘ (σ ∘ τ)) atTop
      (𝓝 (underlyingGH (toMeasuredGHSpace Y))) :=
    (continuous_underlyingGH.tendsto _).comp hlim
  have hlimGH' : Tendsto (underlyingGH ∘ u ∘ (σ ∘ τ)) atTop (𝓝 a) := by
    simpa only [Function.comp_def] using hGH.comp hτ.tendsto_atTop
  have heq := tendsto_nhds_unique hlimGH hlimGH'
  refine ⟨toMeasuredGHSpace Y, ?_, σ ∘ τ, hσ.comp hτ, hlim⟩
  change underlyingGH (toMeasuredGHSpace Y) ∈ A
  rwa [heq]

end MeasuredGHSpace
end BGW.MetricMeasure
