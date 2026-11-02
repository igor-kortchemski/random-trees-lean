/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.MeasuredGHSpace
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

/-!
# Actual finite iid sampled-distance laws

The law is the pushforward of the full product probability measure by the
literal distance matrix. Repeated sampled points remain possible. Measured
isometries preserve the law, so it is defined on the source whole-space
measured-isometry quotient. On a fixed metric carrier it varies continuously
with the sampling probability measure.

Adapted from `Freezing2/Probability/SampledDistanceLaw.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
-/

@[expose] public section

open MeasureTheory TopologicalSpace
open scoped Topology

universe u

namespace BGW.MetricMeasure

/-- Distances between all sampled points, with the exact zero diagonal. -/
def distanceMatrix {X : Type*} [PseudoMetricSpace X] (k : ℕ) (v : Fin k → X) :
    Fin k → Fin k → ℝ := fun i j ↦ dist (v i) (v j)

@[simp] theorem distanceMatrix_diag {X : Type*} [PseudoMetricSpace X]
    (k : ℕ) (v : Fin k → X) (i : Fin k) : distanceMatrix k v i i = 0 := dist_self _

theorem continuous_distanceMatrix {X : Type*} [PseudoMetricSpace X] (k : ℕ) :
    Continuous (distanceMatrix (X := X) k) := by
  unfold distanceMatrix
  fun_prop

variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology Y]

/-- The genuine iid distance-matrix law, including collisions and `k=0`. -/
noncomputable def iidDistanceLawOn (μ : ProbabilityMeasure X) (k : ℕ) :
    ProbabilityMeasure (Fin k → Fin k → ℝ) :=
  (ProbabilityMeasure.pi (fun _ : Fin k ↦ μ)).map (distanceMatrix k)

/-- Fixed-carrier weak convergence of sampling measures gives weak
convergence of the entire finite sampled-distance matrix. -/
theorem continuous_iidDistanceLawOn (k : ℕ) :
    Continuous (fun μ : ProbabilityMeasure X ↦ iidDistanceLawOn μ k) := by
  exact (ProbabilityMeasure.continuous_map (continuous_distanceMatrix k)).comp
    (ProbabilityMeasure.continuous_pi.comp (continuous_pi (fun _ ↦ continuous_id)))

omit [SecondCountableTopology X] in
/-- Isometric mapping of the sampling measure preserves the sampled law. -/
theorem iidDistanceLawOn_map_isometry (μ : ProbabilityMeasure X)
    (f : X → Y) (hf : Isometry f) (k : ℕ) :
    iidDistanceLawOn (μ.map f) k = iidDistanceLawOn μ k := by
  apply ProbabilityMeasure.toMeasure_injective
  change (Measure.pi (fun _ : Fin k ↦ (μ : Measure X).map f)).map (distanceMatrix k) =
    (Measure.pi (fun _ : Fin k ↦ (μ : Measure X))).map (distanceMatrix k)
  have hp : (Measure.pi (fun _ : Fin k ↦ (μ : Measure X))).map
      (fun v i ↦ f (v i)) = Measure.pi (fun _ : Fin k ↦ (μ : Measure X).map f) :=
    Measure.pi_map_pi (fun _ ↦ hf.continuous.measurable.aemeasurable)
  have hfm : Measurable f := hf.continuous.measurable
  rw [← hp, Measure.map_map (continuous_distanceMatrix k).measurable
    (by fun_prop : Measurable (fun v : Fin k → X ↦ fun i ↦ f (v i)))]
  congr 1
  funext v i j
  exact hf.dist_eq _ _

/-- The finite iid matrix law of a represented compact measured space. -/
noncomputable def iidDistanceLaw (X : CompactMeasuredSpace.{u}) (k : ℕ) :
    ProbabilityMeasure (Fin k → Fin k → ℝ) := iidDistanceLawOn X.law k

/-- Whole-space measured isometry leaves every finite sampled law unchanged. -/
theorem iidDistanceLaw_eq_of_measuredIsometry {X Y : CompactMeasuredSpace.{u}}
    (h : X.MeasuredIsometry Y) (k : ℕ) : iidDistanceLaw X k = iidDistanceLaw Y k := by
  obtain ⟨e, he⟩ := h
  have hp : X.law.map e = Y.law := ProbabilityMeasure.toMeasure_injective he
  change iidDistanceLawOn X.law k = iidDistanceLawOn Y.law k
  rw [← hp]
  exact (iidDistanceLawOn_map_isometry X.law e e.isometry k).symm

namespace MeasuredGHSpace

/-- The sampled-distance law on the source quotient. No sample distinctness
or full-support condition is added by passage to isometry classes. -/
noncomputable def sampledDistanceLaw (k : ℕ) :
    MeasuredGHSpace.{u} → ProbabilityMeasure (Fin k → Fin k → ℝ) :=
  Quotient.lift (fun X ↦ iidDistanceLaw X k)
    (fun _ _ h ↦ iidDistanceLaw_eq_of_measuredIsometry h k)

@[simp] theorem sampledDistanceLaw_toMeasuredGHSpace (X : CompactMeasuredSpace.{u}) (k : ℕ) :
    sampledDistanceLaw k (toMeasuredGHSpace X) = iidDistanceLaw X k := rfl

end MeasuredGHSpace
end BGW.MetricMeasure
