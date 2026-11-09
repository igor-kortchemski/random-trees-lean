/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.ContinuumTrees.CodingStability
public import BGW.MetricMeasure.GHPUnderlyingProjection
public import BGW.MetricMeasure.RootedMeasuredGHSpace
import Mathlib.Tactic.Linarith

/-! # Gromov--Hausdorff stability of coded trees

The identity correspondence on the coding interval has distortion at most four times the
uniform distance between two coding functions. Approximate metric gluing turns this into a
Gromov--Hausdorff bound with constant two. Forgetting both the root and measure is the composition
of the existing nonexpansive quotient maps.
-/

@[expose] public section

open MeasureTheory Metric Set GromovHausdorff

namespace BGW.ContinuumTrees.Coding

/-- The Gromov--Hausdorff distance between the trees coded by `g` and `h` is at most
`2 ‖g - h‖` (Le Gall 2005, Lemma 2.4; Duquesne--Le Gall 2005, Lemma 2.3) (C37.4). -/
theorem ghDist_le_two_mul_norm (g h : C(unitInterval, ℝ)) :
    GromovHausdorff.ghDist (Space g) (Space h) ≤ 2 * ‖g - h‖ := by
  apply le_of_forall_pos_le_add
  intro η hη
  let ε := 2 * ‖g - h‖ + η
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hdis : ∀ s t,
      |dist (projection g s) (projection g t) - dist (projection h s) (projection h t)| ≤
        2 * ε := by
    intro s t
    simpa only [dist_projection] using
      (abs_codingDist_sub_le_norm g h s t).trans (by dsimp [ε]; nlinarith)
  let m : MetricSpace (Space g ⊕ Space h) :=
    Metric.glueMetricApprox (projection g) (projection h) ε hε hdis
  let := m
  let : TopologicalSpace (Space g ⊕ Space h) := m.toUniformSpace.toTopologicalSpace
  have hl : Isometry (@Sum.inl (Space g) (Space h)) :=
    Isometry.of_dist_eq fun _ _ => rfl
  have hr : Isometry (@Sum.inr (Space g) (Space h)) :=
    Isometry.of_dist_eq fun _ _ => rfl
  have hglue (s : unitInterval) :
      dist (Sum.inl (projection g s) : Space g ⊕ Space h)
        (Sum.inr (projection h s)) = ε :=
    Metric.glueDist_glued_points (projection g) (projection h) ε s
  have hH : hausdorffDist (range (@Sum.inl (Space g) (Space h)))
      (range (@Sum.inr (Space g) (Space h))) ≤ ε := by
    apply hausdorffDist_le_of_mem_dist hε.le
    · rintro _ ⟨x, rfl⟩
      obtain ⟨s, rfl⟩ := projection_surjective g x
      exact ⟨Sum.inr (projection h s), mem_range_self _, (hglue s).le⟩
    · rintro _ ⟨y, rfl⟩
      obtain ⟨s, rfl⟩ := projection_surjective h y
      refine ⟨Sum.inl (projection g s), mem_range_self _, ?_⟩
      simpa only [dist_comm] using (hglue s).le
  have hGH : GromovHausdorff.ghDist (Space g) (Space h) ≤ ε :=
    (GromovHausdorff.ghDist_le_hausdorffDist hl hr).trans hH
  dsimp [ε] at hGH
  linarith

/-- The Gromov--Hausdorff class of the coded tree is a 2-Lipschitz function of the coding
function (C37.4). -/
theorem lipschitzWith_two_toGHSpace :
    LipschitzWith 2 (fun g : C(unitInterval, ℝ) => GromovHausdorff.toGHSpace (Space g)) := by
  apply LipschitzWith.of_dist_le_mul
  intro g h
  simpa only [GromovHausdorff.ghDist, dist_eq_norm, NNReal.coe_ofNat] using
    ghDist_le_two_mul_norm g h

end BGW.ContinuumTrees.Coding

universe u

namespace BGW.MetricMeasure.RootedMeasuredGHSpace

/-- Forgetting the root and the measure is 1-Lipschitz from rooted measured GHP to GH (C37.5). -/
theorem lipschitzWith_underlyingGH_forgetRoot :
    LipschitzWith 1 (MeasuredGHSpace.underlyingGH.{u} ∘ forgetRoot.{u}) := by
  simpa using
    (MeasuredGHSpace.lipschitzWith_underlyingGH.comp lipschitzWith_forgetRoot)

end BGW.MetricMeasure.RootedMeasuredGHSpace
