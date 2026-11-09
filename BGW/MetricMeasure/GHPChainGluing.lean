/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
/-
The inductive gluing construction below adapts the construction in Mathlib's
Topology/MetricSpace/GromovHausdorff.lean, by Sébastien Gouëzel (Apache 2.0).
Here the successive couplings are supplied explicitly so that their measured
costs, as well as their underlying Hausdorff bounds, can be retained.
-/
module

public import BGW.MetricMeasure.GHPSeparation
public import Mathlib.Topology.MetricSpace.Completion
public import Mathlib.Topology.MetricSpace.Gluing

/-!
# A common complete ambient space for successive GHP couplings

Glue each next coupling along the entire current carrier, form the metric
inductive limit, and take its completion. Each original coupling embeds
isometrically in the resulting space. This is a geometric construction; the
probability measures are subsequently transported through those embeddings.

Adapted from `Freezing2/Geometry/GHPChainGluing.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
-/

@[expose] public section

open MeasureTheory Metric Set

universe u

namespace BGW.MetricMeasure

/-- An actual near-optimal coupling is supplied by the defining infimum. -/
theorem exists_ghpCoupling_cost_lt {X Y : Type u}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (μ : Measure X) (ν : Measure Y) {ε : ℝ} (hε : ghpDistance μ ν < ε) :
    ∃ C : GHPCoupling X Y, C.cost μ ν < ε := by
  obtain ⟨r, hr, hlt⟩ := exists_lt_of_csInf_lt (ghpCosts_nonempty μ ν) hε
  obtain ⟨A, m, i, j, hi, hj, rfl⟩ := hr
  let := m
  let : TopologicalSpace A := m.toUniformSpace.toTopologicalSpace
  let : MeasurableSpace A := borel A
  exact ⟨⟨A, m, i, j, hi, hj⟩, hlt⟩

namespace GHPChain

/-- One finite stage, recording the embedding of its latest carrier. -/
structure Stage (A : Type u) [MetricSpace A] where
  /-- The common ambient carrier at this finite gluing stage. -/
  ambient : Type u
  /-- The metric on the ambient carrier. -/
  metric : MetricSpace ambient
  /-- The isometric embedding of the latest carrier into this stage. -/
  embed : A → ambient
  isom : @Isometry A ambient inferInstance
    (@PseudoMetricSpace.toPseudoEMetricSpace _ metric.toPseudoMetricSpace) embed

instance {A : Type u} [MetricSpace A] (S : Stage A) : MetricSpace S.ambient := S.metric

variable (X : ℕ → Type u) [∀ n, MetricSpace (X n)] [∀ n, Nonempty (X n)]
  (C : ∀ n, GHPCoupling (X n) (X (n + 1)))

/-- The finite stages are glued using the given couplings, without replacing
those couplings by merely unmeasured optimal realizations. -/
noncomputable def stage (n : ℕ) : Stage (X n) :=
  Nat.recOn n
    { ambient := X 0, metric := inferInstance, embed := id, isom := isometry_id }
    fun n Y ↦
      { ambient := GlueSpace Y.isom (C n).left_isometry
        metric := inferInstance
        embed := toGlueR Y.isom (C n).left_isometry ∘ (C n).right
        isom := (toGlueR_isometry _ _).comp (C n).right_isometry }

/-- Every successive coupling factors isometrically through one common
complete ambient space. The factorization identifies the whole shared
carrier, and will therefore preserve the pushed middle probability measure. -/
theorem exists_complete_realization :
    ∃ Z : Type u, ∃ m : MetricSpace Z,
      letI := m
      letI : TopologicalSpace Z := m.toUniformSpace.toTopologicalSpace
      ∃ _ : CompleteSpace Z, ∃ ι : ∀ n, X n → Z,
        (∀ n, Isometry (ι n)) ∧
        ∀ n, ∃ j : (C n).ambient → Z, Isometry j ∧
          ι n = j ∘ (C n).left ∧ ι (n + 1) = j ∘ (C n).right := by
  let Y := stage X C
  have E : ∀ n, GlueSpace (Y n).isom (C n).left_isometry = (Y (n + 1)).ambient :=
    fun n ↦ by dsimp only [Y, stage]; rfl
  let c n := cast (E n)
  have ic : ∀ n, Isometry (c n) := fun n x y ↦ by dsimp only [Y, stage]; rfl
  let f : ∀ n, (Y n).ambient → (Y (n + 1)).ambient :=
    fun n ↦ c n ∘ toGlueL (Y n).isom (C n).left_isometry
  have I : ∀ n, Isometry (f n) := fun n ↦ (ic n).comp (toGlueL_isometry _ _)
  let Z₀ := Metric.InductiveLimit I
  let Z := UniformSpace.Completion Z₀
  let Φ := toInductiveLimit I
  let coeZ := ((↑) : Z₀ → Z)
  let ι : ∀ n, X n → Z := fun n ↦ coeZ ∘ Φ n ∘ (Y n).embed
  have hι : ∀ n, Isometry (ι n) := fun n ↦
    UniformSpace.Completion.coe_isometry.comp ((toInductiveLimit_isometry _ _).comp (Y n).isom)
  refine ⟨Z, inferInstance, inferInstance, ι, hι, ?_⟩
  intro n
  let j : (C n).ambient → Z :=
    coeZ ∘ Φ (n + 1) ∘ c n ∘ toGlueR (Y n).isom (C n).left_isometry
  have hj : Isometry j := UniformSpace.Completion.coe_isometry.comp
    ((toInductiveLimit_isometry _ _).comp ((ic n).comp (toGlueR_isometry _ _)))
  refine ⟨j, hj, ?_, ?_⟩
  · change coeZ ∘ Φ n ∘ (Y n).embed = j ∘ (C n).left
    dsimp only [Φ]
    rw [← toInductiveLimit_commute I]
    simp only [f, j, Φ, ← toGlue_commute, Function.comp_assoc]
  · rfl

end GHPChain
end BGW.MetricMeasure

