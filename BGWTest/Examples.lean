/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

import BGW

/-!
# Public API examples

These consumer examples use ordinary imports, including the finite-tree API, probability
law, GHP structures, continuous coding and finite-variance scalar application.
-/

open BGW BGW.PlaneTree MeasureTheory

example : (node [leaf, leaf]).size = 3 := by
  simp

-- The two README snippets of "Tree interface", kept compiled.
example : (node [leaf, leaf]).increments = [1, -1, -1] := by
  simp [leaf]

example : (ofIncrements? [1, -1, -1]).map size = some 3 := by
  decide

example (s t : PlaneTree) (h : s.children = t.children) : s = t := by
  ext1
  exact h

example (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (BGW.LocallyFinite.bienaymeLaw μ) := inferInstance

example : CompleteSpace BGW.MetricMeasure.RootedMeasuredGHSpace := inferInstance

example : PolishSpace BGW.MetricMeasure.RootedMeasuredGHSpace := inferInstance

example : BorelSpace BGW.MetricMeasure.RootedMeasuredGHSpace := inferInstance

example (g : C(unitInterval, ℝ)) :
    BGW.ContinuumTrees.RealTree.IsRealTree (BGW.ContinuumTrees.Coding.Space g) :=
  BGW.ContinuumTrees.Coding.isRealTree g

open BGW.StableTrees in
example (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hfinite : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure) :
    StableDomain μ 2 (fun n : ℕ =>
      (Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ) / Real.sqrt 2) * Real.sqrt n) :=
  Scalar.stableDomain_of_finiteVariance hc hne hfinite
