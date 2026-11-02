/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.LocallyFinite.Branching
public import BGW.LocallyFinite.Cylinders

/-!
# Uniqueness of the branching law

The branching property determines every finite offspring cylinder, by induction on the largest
address depth, conditioning on the root count and keeping the zero constraints at absent addresses.
These cylinders generate the Borel σ-algebra of `Tree`. Hence a probability measure with the
branching property for `ρ` is `bienaymeLaw ρ`. Adapted from `Freezing1/PlaneBienaymeUniqueness.lean`
and `exists_unique_bienaymeLaw` of `Freezing1/PlaneGeometricBienayme.lean`.
-/

@[expose] public section

namespace BGW.LocallyFinite

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

variable {μ ν : Measure Tree} {ρ : Measure ℕ}

theorem IsBienayme.degree_mass (h : IsBienayme μ ρ) (k : ℕ) :
    μ {T | degree T = k} = ρ {k} := by
  have hh := congrArg (fun m : Measure ℕ => m {k}) h.1
  rw [Measure.map_apply continuous_degree.measurable (measurableSet_singleton k)] at hh
  exact hh

theorem IsBienayme.childrenEvent_measure [IsProbabilityMeasure μ]
    (h : IsBienayme μ ρ) (k : ℕ) (E : Fin k → Set Tree)
    (hE : ∀ i, MeasurableSet (E i)) :
    μ (childrenEvent k E) = ρ {k} * ∏ i : Fin k, μ (E i) := by
  by_cases hk : μ {T | degree T = k} = 0
  · have hz : μ (childrenEvent k E) = 0 :=
      measure_mono_null (fun _ ht => ht.1) hk
    rw [hz, ← h.degree_mass k, hk, zero_mul]
  · let V : Set Tree := (fun T (i : Fin k) => child T (i.val + 1)) ⁻¹' Set.pi Set.univ E
    have hdeg : MeasurableSet {T | degree T = k} :=
      continuous_degree.measurable (measurableSet_singleton k)
    have hh := congrArg (fun m : Measure (Fin k → Tree) => m (Set.pi Set.univ E)) (h.2 k hk)
    rw [Measure.map_apply (Measurable.of_eval fun i =>
      (continuous_child (i.val + 1)).measurable) (MeasurableSet.univ_pi hE),
      Measure.pi_pi] at hh
    have hc := ProbabilityTheory.cond_mul_eq_inter hdeg V μ
    have he : {T | degree T = k} ∩ V = childrenEvent k E := by
      ext T
      simp [V, childrenEvent]
    rw [he] at hc
    change ProbabilityTheory.cond μ {T | degree T = k} V = _ at hh
    rw [hh, h.degree_mass k] at hc
    exact hc.symm.trans (mul_comm _ _)

open scoped Classical in
private theorem IsBienayme.cylinder_degree_measure [IsProbabilityMeasure μ]
    (h : IsBienayme μ ρ) (F : Finset Address) (E : Address → Set ℕ) (k : ℕ) :
    μ (offspringCylinder F E ∩ {T | degree T = k}) =
      if rootCompatible F E k then ρ {k} * ∏ i : Fin k,
        μ (offspringCylinder (childIndices F (i.val + 1)) (fun u => E ((i.val + 1) :: u)))
      else 0 := by
  let C : Fin k → Set Tree := fun i =>
    offspringCylinder (childIndices F (i.val + 1)) (fun u => E ((i.val + 1) :: u))
  have he : offspringCylinder F E ∩ {T | degree T = k} =
      if rootCompatible F E k then childrenEvent k C else ∅ := by
    ext T
    by_cases hd : degree T = k
    · rw [Set.mem_inter_iff]
      simp only [Set.mem_ofPred_eq, hd, and_true]
      rw [mem_offspringCylinder_iff_root F E T k hd]
      by_cases hc : rootCompatible F E k <;>
        simp [hc, C, childrenEvent, hd]
    · by_cases hc : rootCompatible F E k <;>
        simp [hc, C, childrenEvent, hd]
  rw [he]
  split_ifs
  · exact h.childrenEvent_measure k C fun i => measurableSet_offspringCylinder _ _
  · exact measure_empty

theorem IsBienayme.offspringCylinder_eq [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsBienayme μ ρ) (hν : IsBienayme ν ρ) (n : ℕ)
    (F : Finset Address) (E : Address → Set ℕ)
    (hF : ∀ u ∈ F, u.length ≤ n) :
    μ (offspringCylinder F E) = ν (offspringCylinder F E) := by
  induction n generalizing F E with
  | zero =>
      let A : Set ℕ := {k | ∀ u ∈ F, k ∈ E u}
      have he : offspringCylinder F E = degree ⁻¹' A := by
        ext T
        constructor
        · intro h u hu
          have hz : u = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (hF u hu))
          simpa only [hz, degree] using h u hu
        · intro h u hu
          have hz : u = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (hF u hu))
          simpa only [hz, degree] using h u hu
      calc
        μ (offspringCylinder F E) = (μ.map degree) A := by
          rw [Measure.map_apply continuous_degree.measurable (by trivial), he]
        _ = (ν.map degree) A := by rw [hμ.1, hν.1]
        _ = ν (offspringCylinder F E) := by
          rw [Measure.map_apply continuous_degree.measurable (by trivial), he]
  | succ n ih =>
      have each : ∀ k : ℕ,
          μ (offspringCylinder F E ∩ {T | degree T = k}) =
            ν (offspringCylinder F E ∩ {T | degree T = k}) := by
        intro k
        rw [hμ.cylinder_degree_measure, hν.cylinder_degree_measure]
        split_ifs
        · congr 1
          apply Finset.prod_congr rfl
          intro i _
          exact ih _ _ (childIndices_length_le F n (i.val + 1) hF)
        · rfl
      have he : offspringCylinder F E = ⋃ k : ℕ,
          offspringCylinder F E ∩ {T | degree T = k} := by
        ext T
        simp
      have hdisj : Pairwise (fun i j : ℕ => Disjoint
          (offspringCylinder F E ∩ {T | degree T = i})
          (offspringCylinder F E ∩ {T | degree T = j})) := by
        intro i j hij
        apply Set.disjoint_left.mpr
        intro T hi hj
        exact hij (hi.2.symm.trans hj.2)
      have hmeas : ∀ k : ℕ, MeasurableSet
          (offspringCylinder F E ∩ {T | degree T = k}) := fun k =>
        (measurableSet_offspringCylinder F E).inter
          (continuous_degree.measurable (measurableSet_singleton k))
      calc
        _ = ∑' k : ℕ, μ (offspringCylinder F E ∩ {T | degree T = k}) := by
          conv_lhs => rw [he]
          exact measure_iUnion hdisj hmeas
        _ = ∑' k : ℕ, ν (offspringCylinder F E ∩ {T | degree T = k}) := tsum_congr each
        _ = _ := by
          conv_rhs => rw [he]
          exact (measure_iUnion hdisj hmeas).symm

/-- The branching characterization uniquely determines a probability law
on the actual Borel space of locally finite plane trees. -/
theorem IsBienayme.unique [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsBienayme μ ρ) (hν : IsBienayme ν ρ) : μ = ν := by
  have he0 : Topology.IsClosedEmbedding (Subtype.val : Tree → Offspring) :=
    isClosed_canonical.isClosedEmbedding_subtypeVal
  have he : MeasurableEmbedding (Subtype.val : Tree → Offspring) := he0.measurableEmbedding
  apply he.map_injective
  apply MeasureTheory.ext_of_generate_finite
    (MeasureTheory.squareCylinders (fun _ : Address => {s : Set ℕ | MeasurableSet s}))
    MeasureTheory.generateFrom_squareCylinders.symm
    (MeasureTheory.isPiSystem_squareCylinders
      (fun _ => MeasurableSpace.isPiSystem_measurableSet)
      (fun _ => show MeasurableSet (Set.univ : Set ℕ) from MeasurableSet.univ))
  · rintro _ ⟨F, E, hE, rfl⟩
    have hmeas : MeasurableSet ((F : Set Address).pi E) :=
      MeasurableSet.pi F.countable_toSet fun u _ => hE u (Set.mem_univ _)
    rw [Measure.map_apply he.measurable hmeas, Measure.map_apply he.measurable hmeas]
    exact hμ.offspringCylinder_eq hν (F.sup List.length) F E fun u hu =>
      Finset.le_sup (f := List.length) hu
  · simp [Measure.map_apply he.measurable MeasurableSet.univ]

/-- A probability measure with the branching property for `ρ` is the constructed law. -/
theorem IsBienayme.eq_bienaymeLaw {μ : Measure Tree} [IsProbabilityMeasure μ]
    {ρ : Measure ℕ} [IsProbabilityMeasure ρ] (h : IsBienayme μ ρ) :
    μ = bienaymeLaw ρ := h.unique (isBienayme_bienaymeLaw ρ)

/-- For every offspring probability measure `ρ`, the constructed law has the branching property
and is the only probability measure on `Tree` that has it. -/
theorem exists_unique_bienaymeLaw (ρ : Measure ℕ) [IsProbabilityMeasure ρ] :
    IsBienayme (bienaymeLaw ρ) ρ ∧
      ∀ μ : Measure Tree, IsProbabilityMeasure μ → IsBienayme μ ρ → μ = bienaymeLaw ρ := by
  refine ⟨isBienayme_bienaymeLaw ρ, fun μ hprob h => ?_⟩
  have := hprob
  exact h.eq_bienaymeLaw

end BGW.LocallyFinite
