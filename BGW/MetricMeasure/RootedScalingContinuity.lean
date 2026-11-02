/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.RootedScaling
public import BGW.MetricMeasure.RootedCommonSource
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Joint continuity of positive spatial scaling

Two positive scalings of one represented compact probability space are
compared using their common original carrier and probability law. The
distortion is the difference of factors times the original diameter. The
common-source gluing estimate therefore gives the rooted GHP bound with
constant `3 / 2`.

Combining this estimate with the fixed-factor Lipschitz bound proves joint
continuity on positive factors and rooted measured isometry classes. The
argument fixes a representative only at the point of continuity; it does
not introduce a global choice of representatives or a diameter observable
on the quotient. Probability masses are unchanged throughout.
-/

@[expose] public section

open Filter MeasureTheory Metric Set
open scoped Topology

universe u

namespace BGW.MetricMeasure

namespace RootedCompactMeasuredSpace

/-- Changing the scaling factor on one represented space is controlled by its diameter. -/
theorem distance_scale_scale_le (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (X : RootedCompactMeasuredSpace.{u}) :
    distance (scale c hc X) (scale d hd X) ≤
      (3 / 2 : ℝ) * |c - d| * Metric.diam (Set.univ : Set X.space) := by
  let c' : Set.Ioi (0 : ℝ) := ⟨c, hc⟩
  let d' : Set.Ioi (0 : ℝ) := ⟨d, hd⟩
  let δ : ℝ := |c - d| * Metric.diam (Set.univ : Set X.space)
  have hδ : 0 ≤ δ := mul_nonneg (abs_nonneg _) Metric.diam_nonneg
  apply le_of_forall_pos_le_add
  intro ε hε
  let η : ℝ := δ / 2 + ε / 3
  have hη : 0 < η := by dsimp [η]; linarith
  have hdis (x y : X.space) :
      |dist (ScaledMetric.toScaled c' x) (ScaledMetric.toScaled c' y) -
        dist (ScaledMetric.toScaled d' x) (ScaledMetric.toScaled d' y)| ≤ 2 * η := by
    rw [ScaledMetric.dist_toScaled, ScaledMetric.dist_toScaled,
      ← sub_mul, abs_mul, abs_of_nonneg dist_nonneg]
    have hdiam := Metric.dist_le_diam_of_mem
      (isCompact_univ : IsCompact (Set.univ : Set X.space)).isBounded
      (mem_univ x) (mem_univ y)
    have hb := mul_le_mul_of_nonneg_left hdiam (abs_nonneg (c - d))
    change |c - d| * dist x y ≤ 2 * η
    change |c - d| * dist x y ≤ δ at hb
    dsimp [η]
    linarith
  have hb := rootedGHPDistance_map_le_of_distortion
    (X := ScaledMetric c' X.space) (Y := ScaledMetric d' X.space)
    (X.space.law : Measure X.space)
    (ScaledMetric.toScaled c' (X := X.space)) (ScaledMetric.toScaled d' (X := X.space))
    (ScaledMetric.measurable_toScaled c') (ScaledMetric.measurable_toScaled d')
    (ScaledMetric.equiv c' X.space).surjective (ScaledMetric.equiv d' X.space).surjective
    hη hdis X.root
  change distance (scale c hc X) (scale d hd X) ≤ 3 * η at hb
  dsimp [η, δ] at hb
  linarith

end RootedCompactMeasuredSpace

namespace RootedMeasuredGHSpace

/-- Spatial scaling is continuous jointly in the positive factor and the rooted measured space. -/
theorem continuous_scale_joint :
    Continuous (fun p : Set.Ioi (0 : ℝ) × RootedMeasuredGHSpace.{u} =>
      scale p.1.val p.1.property p.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨c, Z⟩
  induction Z using Quotient.inductionOn with
  | _ X =>
    let D : ℝ := Metric.diam (Set.univ : Set X.space)
    have hcont : Continuous (fun p : Set.Ioi (0 : ℝ) × RootedMeasuredGHSpace.{u} =>
        max (p.1 : ℝ) 1 * dist p.2 (toRootedMeasuredGHSpace X) +
          (3 / 2 : ℝ) * |(p.1 : ℝ) - (c : ℝ)| * D) := by
      fun_prop
    have hzero : Tendsto
        (fun p : Set.Ioi (0 : ℝ) × RootedMeasuredGHSpace.{u} =>
          max (p.1 : ℝ) 1 * dist p.2 (toRootedMeasuredGHSpace X) +
            (3 / 2 : ℝ) * |(p.1 : ℝ) - (c : ℝ)| * D)
        (𝓝 (c, toRootedMeasuredGHSpace X)) (𝓝 0) := by
      simpa only [dist_self, sub_self, abs_zero, mul_zero, zero_mul, add_zero, zero_add] using
        hcont.tendsto (c, toRootedMeasuredGHSpace X)
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) ?_ hzero
    intro p
    calc
      dist (scale p.1.val p.1.property p.2)
          (scale c.val c.property (toRootedMeasuredGHSpace X)) ≤
        dist (scale p.1.val p.1.property p.2)
            (scale p.1.val p.1.property (toRootedMeasuredGHSpace X)) +
          dist (scale p.1.val p.1.property (toRootedMeasuredGHSpace X))
            (scale c.val c.property (toRootedMeasuredGHSpace X)) := dist_triangle _ _ _
      _ ≤ max (p.1 : ℝ) 1 * dist p.2 (toRootedMeasuredGHSpace X) +
          (3 / 2 : ℝ) * |(p.1 : ℝ) - (c : ℝ)| * D := by
        apply add_le_add (dist_scale_le p.1.val p.1.property p.2 (toRootedMeasuredGHSpace X))
        exact RootedCompactMeasuredSpace.distance_scale_scale_le
          p.1.val c.val p.1.property c.property X

/-- Joint measurability uses the second countability of the positive real factor. -/
theorem measurable_scale_joint :
    Measurable (fun p : Set.Ioi (0 : ℝ) × RootedMeasuredGHSpace.{u} =>
      scale p.1.val p.1.property p.2) :=
  continuous_scale_joint.measurable

end RootedMeasuredGHSpace

end BGW.MetricMeasure
