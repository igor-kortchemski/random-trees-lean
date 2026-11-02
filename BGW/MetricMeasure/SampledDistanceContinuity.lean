/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.GHPCompactness
public import BGW.MetricMeasure.SampledDistanceLaw

/-!
# GHP continuity of the actual finite iid distance-matrix laws

The compactness extraction is retained together with its fixed compact
ambient sampling measures. Their weak convergence gives every finite matrix
law by product continuity. For a GHP-convergent sequence, uniqueness identifies
every subsequential limit, giving continuity of the quotient observable.
Neither distinct samples nor full measure support is assumed.

Adapted from `Freezing2/Probability/SampledDistanceContinuity.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
-/

@[expose] public section

open MeasureTheory Metric Set Filter TopologicalSpace GromovHausdorff
open scoped Topology Uniformity BoundedContinuousFunction

universe u

namespace BGW.MetricMeasure

/-- Hausdorff-Cauchy full carrier images admit a measured subsequence on
which every finite iid matrix law also converges to the same limit.
The measures need not be Cauchy. -/
private theorem exists_sampled_subsequence_of_common_ambient
    (X : ℕ → CompactMeasuredSpace.{u}) {Z : Type u}
    [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z] [CompleteSpace Z]
    (ι : ∀ n, X n → Z) (hι : ∀ n, Isometry (ι n))
    (S : ℕ → NonemptyCompacts Z) (hS : ∀ n, (S n : Set Z) = range (ι n))
    (hcS : CauchySeq S) :
    ∃ Y : CompactMeasuredSpace.{u}, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto ((fun n ↦ toMeasuredGHSpace (X n)) ∘ φ) atTop (𝓝 (toMeasuredGHSpace Y)) ∧
      ∀ k : ℕ, Tendsto (fun n ↦ iidDistanceLaw (X (φ n)) k) atTop (𝓝 (iidDistanceLaw Y k)) := by
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
  let jL : L → K := fun x ↦ ⟨(x : Z), hLK x.property⟩
  have hjL : Isometry jL := Isometry.of_dist_eq (fun _ _ ↦ rfl)
  have hηK : η.map jL = ν₀ := by
    apply ProbabilityMeasure.toMeasure_injective
    apply (MeasurableEmbedding.subtype_coe K.isCompact.measurableSet).map_injective
    change ((η : Measure ↥L).map jL).map (fun x : K ↦ (x : Z)) =
      (ν₀ : Measure K).map (fun x : K ↦ (x : Z))
    rw [Measure.map_map continuous_subtype_val.measurable hjL.continuous.measurable]
    exact hη
  refine ⟨Y, φ, hφ, hsub, ?_⟩
  intro k
  have h := (continuous_iidDistanceLawOn (X := K) k).tendsto ν₀ |>.comp hν
  have hleft (n : ℕ) : iidDistanceLawOn (ν (φ n)) k = iidDistanceLaw (X (φ n)) k :=
    iidDistanceLawOn_map_isometry (X (φ n)).law (ιK (φ n)) (hιK (φ n)) k
  have hright : iidDistanceLawOn ν₀ k = iidDistanceLaw Y k := by
    rw [← hηK]
    exact iidDistanceLawOn_map_isometry η jL hjL k
  simpa only [Function.comp_def, hleft, hright] using h

/-- GH-Cauchy underlying carriers admit a measured subsequence, retaining
all finite sampled-distance limits for arbitrary probability measures. -/
private theorem exists_sampled_subsequence_of_gh_cauchy
    (X : ℕ → CompactMeasuredSpace.{u})
    (hc : CauchySeq (fun n ↦ toGHSpace (X n))) :
    ∃ Y : CompactMeasuredSpace.{u}, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto ((fun n ↦ toMeasuredGHSpace (X n)) ∘ φ) atTop (𝓝 (toMeasuredGHSpace Y)) ∧
      ∀ k : ℕ, Tendsto (fun n ↦ iidDistanceLaw (X (φ n)) k) atTop (𝓝 (iidDistanceLaw Y k)) := by
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
  obtain ⟨Y, τ, hτ, hlim, hmatrix⟩ := exists_sampled_subsequence_of_common_ambient
    (fun n ↦ X (σ n)) ι hι S (fun _ ↦ rfl) hcS
  refine ⟨Y, σ ∘ τ, hσ.comp hτ, by simpa only [Function.comp_def] using hlim, ?_⟩
  intro k
  simpa only [Function.comp_def] using hmatrix k

namespace MeasuredGHSpace

/-- Every finite iid sampled-distance law is continuous for the exact source
GHP topology on whole-space measured-isometry classes. -/
theorem continuous_sampledDistanceLaw (k : ℕ) : Continuous (sampledDistanceLaw.{u} k) := by
  classical
  apply SeqContinuous.continuous
  intro u p hu
  apply tendsto_of_subseq_tendsto
  intro ns hns
  let X : ℕ → CompactMeasuredSpace.{u} := fun n ↦ Quotient.out (u (ns n))
  have hX (n : ℕ) : toMeasuredGHSpace (X n) = u (ns n) := Quotient.out_eq _
  have hseq : Tendsto (fun n ↦ toMeasuredGHSpace (X n)) atTop (𝓝 p) := by
    simpa only [hX, Function.comp_def] using hu.comp hns
  have hGH : CauchySeq (fun n ↦ toGHSpace (X n)) :=
    ((continuous_underlyingGH.tendsto p).comp hseq).cauchySeq
  obtain ⟨Y, φ, hφ, hY, hmatrix⟩ := exists_sampled_subsequence_of_gh_cauchy X hGH
  have heq : toMeasuredGHSpace Y = p := tendsto_nhds_unique hY (hseq.comp hφ.tendsto_atTop)
  refine ⟨φ, ?_⟩
  have hleft (n : ℕ) : iidDistanceLaw (X n) k = sampledDistanceLaw k (u (ns n)) := by
    rw [← hX]
    rfl
  have hright : iidDistanceLaw Y k = sampledDistanceLaw k p := by
    rw [← heq]
    rfl
  simpa only [hleft, hright, Function.comp_def] using hmatrix k

/-- The finite sampled-distance observables are Borel measurable. -/
theorem measurable_sampledDistanceLaw (k : ℕ) :
    letI : MeasurableSpace (ProbabilityMeasure (Fin k → Fin k → ℝ)) := borel _
    Measurable (sampledDistanceLaw.{u} k) := by
  let : MeasurableSpace (ProbabilityMeasure (Fin k → Fin k → ℝ)) := borel _
  let : BorelSpace (ProbabilityMeasure (Fin k → Fin k → ℝ)) := ⟨rfl⟩
  exact (continuous_sampledDistanceLaw k).measurable

end MeasuredGHSpace
end BGW.MetricMeasure
