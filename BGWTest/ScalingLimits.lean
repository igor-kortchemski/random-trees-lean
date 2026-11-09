/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

import BGW.StableTrees.ExcursionJump
import BGW.StableTrees.StableProcessBrownian
import BGW.Skorokhod.OptionalGaps
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Consumer examples: stable excursions and Donsker's theorem

These examples use narrow public imports, as an external project would. The first applies the
jump dichotomy of the normalized stable excursion (C22) to concrete indices. The second derives
a consequence that is not in the library: the largest rescaled jump of the Łukasiewicz path of
a critical finite-variance BGW tree converges in law to `0`, by combining the library's
Donsker theorem and Lipschitz bound on the largest jump with Mathlib's continuous mapping
theorem.
-/

open MeasureTheory Filter Topology
open BGW.Skorokhod BGW.StableTrees BGW.ContinuumTrees BGW.ContinuumTrees.BrownianD

/-- For `θ = 3/2` the normalized excursion has a positive jump almost surely. -/
example : ∀ᵐ x ∂(levyExcLaw (3 / 2) : Measure (D 1 ℝ)), 0 < maxJump x :=
  ae_maxJump_pos_levyExcLaw (by norm_num) (by norm_num)

/-- At `θ = 2` it is continuous, so the normalized excursion laws at `3/2` and `2` differ. -/
example : levyExcLaw (3 / 2) ≠ levyExcLaw 2 := by
  intro h
  have h1 := ae_maxJump_pos_levyExcLaw (θ := 3 / 2) (by norm_num) (by norm_num)
  have h2 := ae_maxJump_eq_zero_levyExcLaw_two
  rw [h] at h1
  have : ∀ᵐ x ∂(levyExcLaw 2 : Measure (D 1 ℝ)), False := by
    filter_upwards [h1, h2] with x hx1 hx2
    linarith [hx2.1]
  simpa using (ae_iff.1 this)

/-- The law of the largest rescaled jump of the Łukasiewicz path converges to the law of the
largest jump of the Brownian limit. -/
theorem tendsto_maxJump_stepPathLaw {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hfinite : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n => (stepPathLaw (realOffspringStepLaw μ) T
        (fun n : ℕ => (Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ) / Real.sqrt 2) *
          Real.sqrt n) n).map maxJump) atTop
      (𝓝 ((wienerD (NNReal.sqrt 2) T).map maxJump)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_stepPathLaw_wienerD_of_finiteVariance hc hne hfinite hT)
    lipschitzWith_two_maxJump.continuous

/-- Brownian paths have no jump, so the limit law is the Dirac mass at `0`. -/
theorem map_maxJump_wienerD (c : NNReal) (T : ℝ) :
    ((wienerD c T).map maxJump : Measure ℝ) = Measure.dirac 0 := by
  have h : ∀ᵐ f ∂(wienerD c T : Measure (D T ℝ)), maxJump f = 0 := by
    filter_upwards [ae_mem_range_ofContinuous_wienerD c T] with f hf
    obtain ⟨g, rfl⟩ := hf
    exact maxJump_eq_zero_of_continuous g.continuous
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_congr h, Measure.map_const]
  simp

/-- Hence the largest rescaled jump converges in law to `0`. -/
example {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hfinite : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n => ((stepPathLaw (realOffspringStepLaw μ) T
        (fun n : ℕ => (Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ) / Real.sqrt 2) *
          Real.sqrt n) n).map maxJump : ProbabilityMeasure ℝ)) atTop
      (𝓝 ⟨Measure.dirac 0, inferInstance⟩) := by
  convert tendsto_maxJump_stepPathLaw hc hne hfinite hT using 2
  congr 1
  apply ProbabilityMeasure.toMeasure_injective
  rw [map_maxJump_wienerD]
  rfl
