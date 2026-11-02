/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

import BGW.ContinuumTrees.ContourLawConvergence

/-!
# Measurable finite-tree inputs for contour law convergence

A local discrete measurable structure on the countable finite-tree type makes every
observable measurable. Thus a measurable tree-valued input supplies the two observable
measurability hypotheses of the contour-to-rooted-law transfer theorem.
-/

open BGW BGW.ContinuumTrees BGW.MetricMeasure Filter MeasureTheory
open scoped Topology

section

local instance : MeasurableSpace PlaneTree := ⊤

example {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n))
    (t : (n : ℕ) → Ω n → PlaneTree) (ht : ∀ n, Measurable (t n))
    (b : ℕ → ℝ) (hb : ∀ n, 0 < b n) (hbinfty : Tendsto b atTop atTop)
    (hratio : ∀ r > 0, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | r < b n / ((t n ω).size : ℝ)}) atTop (𝓝 0))
    {ν : ProbabilityMeasure C(unitInterval, ℝ)}
    (hlim : Tendsto (fun n => (μ n).map
      (fun ω : Ω n => (b n)⁻¹ • (t n ω).contourFunction)) atTop (𝓝 ν)) :
    Tendsto (fun n => (μ n).map (fun ω : Ω n =>
      RootedMeasuredGHSpace.scale (b n)⁻¹ (inv_pos.mpr (hb n))
        (toRootedMeasuredGHSpace (FiniteTree.rootedCompactMeasuredSpace (t n ω)))))
      atTop (𝓝 (ν.map Coding.rootedMeasuredGHSpace)) := by
  have hF (n : ℕ) : Measurable (fun ω : Ω n =>
      RootedMeasuredGHSpace.scale (b n)⁻¹ (inv_pos.mpr (hb n))
        (toRootedMeasuredGHSpace (FiniteTree.rootedCompactMeasuredSpace (t n ω)))) :=
    (measurable_of_countable (fun s : PlaneTree =>
      RootedMeasuredGHSpace.scale (b n)⁻¹ (inv_pos.mpr (hb n))
        (toRootedMeasuredGHSpace (FiniteTree.rootedCompactMeasuredSpace s)))).comp (ht n)
  have hG (n : ℕ) : Measurable (fun ω : Ω n => (b n)⁻¹ • (t n ω).contourFunction) :=
    (measurable_of_countable (fun s : PlaneTree => (b n)⁻¹ • s.contourFunction)).comp (ht n)
  exact FiniteTree.tendsto_rooted_laws_of_contour μ t b hb hbinfty hF hG hratio hlim

end
