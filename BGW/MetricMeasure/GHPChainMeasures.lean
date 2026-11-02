/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.GHPChainGluing

/-!
# Measured cost control in a common ambient space

The isometric factorizations of successive couplings preserve their Hausdorff
contributions and do not increase their Prokhorov contributions. The single
complete ambient space therefore retains both parts of every supplied cost.

Adapted from `Freezing2/Geometry/GHPChainMeasures.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
-/

@[expose] public section

open MeasureTheory Metric Set

universe u

namespace BGW.MetricMeasure
namespace GHPCoupling

/-- An isometric embedding of a coupling's ambient space cannot increase
its measured cost. The pushed measures are exactly the original marginals
followed by the same ambient embedding. -/
theorem cost_le_after_isometry {X Y Z : Type u}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (C : GHPCoupling X Y) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (j : C.ambient → Z) (hj : Isometry j) :
    levyProkhorovDist (μ.map (j ∘ C.left)) (ν.map (j ∘ C.right)) +
        hausdorffDist (range (j ∘ C.left)) (range (j ∘ C.right)) ≤ C.cost μ ν := by
  unfold cost
  rw [range_comp, range_comp, hausdorffDist_image hj]
  refine add_le_add ?_ le_rfl
  rw [← Measure.map_map hj.continuous.measurable C.left_isometry.continuous.measurable,
    ← Measure.map_map hj.continuous.measurable C.right_isometry.continuous.measurable]
  exact levyProkhorovDist_map_le _ _ hj.lipschitzWith

end GHPCoupling

namespace GHPChain

variable (X : ℕ → Type u) [∀ n, MetricSpace (X n)] [∀ n, Nonempty (X n)]
  [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
  (μ : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
  (C : ∀ n, GHPCoupling (X n) (X (n + 1)))

/-- All adjacent measured costs are simultaneously controlled in one genuine
complete metric space with its metric-induced Borel structure. -/
theorem exists_complete_measured_realization :
    ∃ Z : Type u, ∃ m : MetricSpace Z,
      letI := m
      letI : TopologicalSpace Z := m.toUniformSpace.toTopologicalSpace
      letI : MeasurableSpace Z := borel Z
      ∃ _ : CompleteSpace Z, ∃ ι : ∀ n, X n → Z,
        (∀ n, Isometry (ι n)) ∧ ∀ n,
          levyProkhorovDist ((μ n).map (ι n)) ((μ (n + 1)).map (ι (n + 1))) +
            hausdorffDist (range (ι n)) (range (ι (n + 1))) ≤
              (C n).cost (μ n) (μ (n + 1)) := by
  obtain ⟨Z, m, hcomplete, ι, hι, hfactor⟩ := exists_complete_realization X C
  let := m
  let : TopologicalSpace Z := m.toUniformSpace.toTopologicalSpace
  let : MeasurableSpace Z := borel Z
  let : BorelSpace Z := ⟨rfl⟩
  refine ⟨Z, m, hcomplete, ι, hι, ?_⟩
  intro n
  obtain ⟨j, hj, hl, hr⟩ := hfactor n
  rw [hl, hr]
  exact (C n).cost_le_after_isometry (μ n) (μ (n + 1)) j hj

end GHPChain
end BGW.MetricMeasure
