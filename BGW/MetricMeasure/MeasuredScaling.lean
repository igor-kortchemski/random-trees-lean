/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.RootedScalingContinuity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Positive spatial scaling of unrooted measured GH classes

The same representative scaling used for rooted compact probability spaces descends to the
unrooted whole-carrier measured-isometry quotient. Measure transport is unchanged. As in the
rooted case, GHP estimates use `max factor 1` because the Lévy–Prokhorov component is not
homogeneous under spatial scaling.
-/

@[expose] public section

open Filter MeasureTheory Metric Set
open scoped Topology

universe u

namespace BGW.MetricMeasure

namespace CompactMeasuredSpace

/-- Whole-carrier measured isometries remain so after positive spatial scaling. -/
theorem measuredIsometry_scale (factor : ℝ) (hfactor : 0 < factor)
    {X Y : CompactMeasuredSpace.{u}} (h : MeasuredIsometry X Y) :
    MeasuredIsometry (scale factor hfactor X) (scale factor hfactor Y) := by
  obtain ⟨e, he⟩ := h
  let c : Set.Ioi (0 : ℝ) := ⟨factor, hfactor⟩
  refine ⟨ScaledMetric.isometryEquiv c (X := X) (Y := Y) e, ?_⟩
  change ((X.law : Measure X).map (ScaledMetric.toScaled c)).map
      (ScaledMetric.map c e) = (Y.law : Measure Y).map (ScaledMetric.toScaled c)
  rw [ScaledMetric.map_measure_toScaled c _ e.continuous.measurable, he]

/-- Positive scaling is Lipschitz for the represented unrooted GHP distance. -/
theorem distance_scale_le (factor : ℝ) (hfactor : 0 < factor)
    (X Y : CompactMeasuredSpace.{u}) :
    distance (scale factor hfactor X) (scale factor hfactor Y) ≤
      max factor 1 * distance X Y := by
  let c : Set.Ioi (0 : ℝ) := ⟨factor, hfactor⟩
  have hM : 0 < max factor 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hdiv : distance (scale factor hfactor X) (scale factor hfactor Y) / max factor 1 ≤
      distance X Y := by
    apply le_csInf (ghpCosts_nonempty (X.law : Measure X) (Y.law : Measure Y))
    rintro r ⟨Z, m, i, j, hi, hj, rfl⟩
    let : MetricSpace Z := m
    let : MeasurableSpace Z := _root_.borel Z
    let : BorelSpace Z := ⟨rfl⟩
    let C : GHPCoupling X Y :=
      { ambient := Z, metric := inferInstance, left := i, right := j,
        left_isometry := hi, right_isometry := hj }
    apply (div_le_iff₀ hM).mpr
    have hP := levyProkhorovDist_map_le_mul ((X.law : Measure X).map C.left)
      ((Y.law : Measure Y).map C.right)
      (ScaledMetric.lipschitzWith_toScaled c (X := C.ambient))
    have hH := hausdorffDist_image_le_mul_of_lipschitz
      (ScaledMetric.lipschitzWith_toScaled c (X := C.ambient))
      (isCompact_range C.left_isometry.continuous) (isCompact_range C.right_isometry.continuous)
      (range_nonempty C.left) (range_nonempty C.right)
    change levyProkhorovDist
      (((X.law : Measure X).map C.left).map (ScaledMetric.toScaled c))
      (((Y.law : Measure Y).map C.right).map (ScaledMetric.toScaled c)) ≤
        max (c : ℝ) 1 * levyProkhorovDist ((X.law : Measure X).map C.left)
          ((Y.law : Measure Y).map C.right) at hP
    change hausdorffDist (ScaledMetric.toScaled c '' range C.left)
      (ScaledMetric.toScaled c '' range C.right) ≤
        (c : ℝ) * hausdorffDist (range C.left) (range C.right) at hH
    have hbound : (C.scale c).cost ((X.law : Measure X).map (ScaledMetric.toScaled c))
        ((Y.law : Measure Y).map (ScaledMetric.toScaled c)) ≤
          max (c : ℝ) 1 * C.cost (X.law : Measure X) (Y.law : Measure Y) := by
      change levyProkhorovDist
        (((X.law : Measure X).map (ScaledMetric.toScaled c)).map (ScaledMetric.map c C.left))
        (((Y.law : Measure Y).map (ScaledMetric.toScaled c)).map (ScaledMetric.map c C.right)) +
        hausdorffDist (range (ScaledMetric.map c C.left))
          (range (ScaledMetric.map c C.right)) ≤ _
      rw [ScaledMetric.map_measure_toScaled c (X.law : Measure X)
          C.left_isometry.continuous.measurable,
        ScaledMetric.map_measure_toScaled c (Y.law : Measure Y)
          C.right_isometry.continuous.measurable,
        ScaledMetric.range_map, ScaledMetric.range_map]
      change _ ≤ max (c : ℝ) 1 *
        (levyProkhorovDist ((X.law : Measure X).map C.left)
          ((Y.law : Measure Y).map C.right) +
            hausdorffDist (range C.left) (range C.right))
      have hP' := mul_le_mul_of_nonneg_right (le_max_right (c : ℝ) 1)
        (show 0 ≤ levyProkhorovDist ((X.law : Measure X).map C.left)
          ((Y.law : Measure Y).map C.right) from ENNReal.toReal_nonneg)
      have hH' := mul_le_mul_of_nonneg_right (le_max_left (c : ℝ) 1)
        (show 0 ≤ hausdorffDist (range C.left) (range C.right) from hausdorffDist_nonneg)
      nlinarith
    have hreal := ghpDistance_le_of_isometries
      ((X.law : Measure X).map (ScaledMetric.toScaled c))
      ((Y.law : Measure Y).map (ScaledMetric.toScaled c))
      (C.scale c).ambient (C.scale c).left (C.scale c).right
      (C.scale c).left_isometry (C.scale c).right_isometry
    exact (hreal.trans hbound).trans_eq (mul_comm _ _)
  simpa only [mul_comm] using (div_le_iff₀ hM).mp hdiv

/-- Scaling by one preserves the represented unrooted measured isometry class. -/
theorem measuredIsometry_scale_one (X : CompactMeasuredSpace.{u}) :
    MeasuredIsometry (scale 1 zero_lt_one X) X := by
  let c : Set.Ioi (0 : ℝ) := ⟨1, zero_lt_one⟩
  let e : scale 1 zero_lt_one X ≃ᵢ X :=
    { toEquiv := (ScaledMetric.equiv c X).symm
      isometry_toFun := by
        apply Isometry.of_dist_eq
        intro x y
        change @dist X X.metric.toPseudoMetricSpace.toDist
            (ScaledMetric.ofScaled c (X := X) x)
            (ScaledMetric.ofScaled c (X := X) y) =
          (1 : ℝ) * @dist X X.metric.toPseudoMetricSpace.toDist
            (ScaledMetric.ofScaled c (X := X) x)
            (ScaledMetric.ofScaled c (X := X) y)
        rw [one_mul] }
  refine ⟨e, ?_⟩
  change ((X.law : Measure X).map (ScaledMetric.toScaled c)).map
      (ScaledMetric.ofScaled c) = (X.law : Measure X)
  exact ScaledMetric.map_ofScaled_map_toScaled c _

/-- Scaling by the positive reciprocal cancels the first scaling, including the measure. -/
theorem measuredIsometry_scale_inv (factor : ℝ) (hfactor : 0 < factor)
    (X : CompactMeasuredSpace.{u}) :
    MeasuredIsometry (scale factor⁻¹ (inv_pos.mpr hfactor) (scale factor hfactor X)) X := by
  let c : Set.Ioi (0 : ℝ) := ⟨factor, hfactor⟩
  let ci : Set.Ioi (0 : ℝ) := ⟨factor⁻¹, inv_pos.mpr hfactor⟩
  let e : scale factor⁻¹ (inv_pos.mpr hfactor) (scale factor hfactor X) ≃ᵢ X :=
    { toEquiv := (ScaledMetric.equiv ci (ScaledMetric c X)).symm.trans
        (ScaledMetric.equiv c X).symm
      isometry_toFun := by
        apply Isometry.of_dist_eq
        intro x y
        change @dist X X.metric.toPseudoMetricSpace.toDist
            (ScaledMetric.ofScaled c (X := X)
              (ScaledMetric.ofScaled ci (X := ScaledMetric c X) x))
            (ScaledMetric.ofScaled c (X := X)
              (ScaledMetric.ofScaled ci (X := ScaledMetric c X) y)) =
          factor⁻¹ * (factor * @dist X X.metric.toPseudoMetricSpace.toDist
            (ScaledMetric.ofScaled c (X := X)
              (ScaledMetric.ofScaled ci (X := ScaledMetric c X) x))
            (ScaledMetric.ofScaled c (X := X)
              (ScaledMetric.ofScaled ci (X := ScaledMetric c X) y)))
        rw [← mul_assoc, inv_mul_cancel₀ hfactor.ne', one_mul] }
  refine ⟨e, ?_⟩
  change (((X.law : Measure X).map (ScaledMetric.toScaled c)).map
      (ScaledMetric.toScaled ci)).map (ScaledMetric.ofScaled c ∘ ScaledMetric.ofScaled ci) =
        (X.law : Measure X)
  rw [← Measure.map_map (ScaledMetric.measurable_ofScaled c)
    (ScaledMetric.measurable_ofScaled ci), ScaledMetric.map_ofScaled_map_toScaled,
    ScaledMetric.map_ofScaled_map_toScaled]

/-- The inverse scaling gives the lower bound with factor `min factor 1`. -/
theorem min_mul_distance_le_scale (factor : ℝ) (hfactor : 0 < factor)
    (X Y : CompactMeasuredSpace.{u}) :
    min factor 1 * distance X Y ≤ distance (scale factor hfactor X) (scale factor hfactor Y) := by
  have hInv := distance_scale_le factor⁻¹ (inv_pos.mpr hfactor)
    (scale factor hfactor X) (scale factor hfactor Y)
  rw [distance_congr (measuredIsometry_scale_inv factor hfactor X)
    (measuredIsometry_scale_inv factor hfactor Y)] at hInv
  rcases le_total factor 1 with hf | hf
  · rw [min_eq_left hf]
    rw [max_eq_left ((one_le_inv₀ hfactor).mpr hf)] at hInv
    calc factor * distance X Y ≤ factor *
        (factor⁻¹ * distance (scale factor hfactor X) (scale factor hfactor Y)) :=
          mul_le_mul_of_nonneg_left hInv hfactor.le
      _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hfactor.ne', one_mul]
  · rw [min_eq_right hf, one_mul]
    rw [max_eq_right ((inv_le_one₀ hfactor).mpr hf), one_mul] at hInv
    exact hInv

/-- Changing the positive scaling factor is controlled by the representative diameter. -/
theorem distance_scale_scale_le (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (X : CompactMeasuredSpace.{u}) :
    distance (scale c hc X) (scale d hd X) ≤
      |c - d| * Metric.diam (Set.univ : Set X) := by
  let c' : Set.Ioi (0 : ℝ) := ⟨c, hc⟩
  let d' : Set.Ioi (0 : ℝ) := ⟨d, hd⟩
  let δ : ℝ := |c - d| * Metric.diam (Set.univ : Set X)
  have hδ : 0 ≤ δ := mul_nonneg (abs_nonneg _) Metric.diam_nonneg
  apply le_of_forall_pos_le_add
  intro ε hε
  let η : ℝ := δ / 2 + ε / 2
  have hη : 0 < η := by dsimp [η]; linarith
  have hdis (x y : X) :
      |dist (ScaledMetric.toScaled c' x) (ScaledMetric.toScaled c' y) -
        dist (ScaledMetric.toScaled d' x) (ScaledMetric.toScaled d' y)| ≤ 2 * η := by
    rw [ScaledMetric.dist_toScaled, ScaledMetric.dist_toScaled,
      ← sub_mul, abs_mul, abs_of_nonneg dist_nonneg]
    have hdiam := Metric.dist_le_diam_of_mem
      (isCompact_univ : IsCompact (Set.univ : Set X)).isBounded
      (mem_univ x) (mem_univ y)
    have hb := mul_le_mul_of_nonneg_left hdiam (abs_nonneg (c - d))
    change |c - d| * dist x y ≤ 2 * η
    change |c - d| * dist x y ≤ δ at hb
    dsimp [η]
    linarith
  have hb := ghpDistance_map_le_of_distortion
    (X := ScaledMetric c' X) (Y := ScaledMetric d' X)
    (X.law : Measure X)
    (ScaledMetric.toScaled c' (X := X)) (ScaledMetric.toScaled d' (X := X))
    (ScaledMetric.measurable_toScaled c') (ScaledMetric.measurable_toScaled d')
    (ScaledMetric.equiv c' X).surjective (ScaledMetric.equiv d' X).surjective hη hdis
  change distance (scale c hc X) (scale d hd X) ≤ 2 * η at hb
  dsimp [η, δ] at hb
  linarith

end CompactMeasuredSpace

namespace MeasuredGHSpace

/-- Positive spatial scaling on whole-carrier unrooted measured isometry classes. -/
noncomputable def scale (factor : ℝ) (hfactor : 0 < factor) :
    MeasuredGHSpace.{u} → MeasuredGHSpace.{u} :=
  Quotient.map (CompactMeasuredSpace.scale factor hfactor)
    (fun _ _ h => CompactMeasuredSpace.measuredIsometry_scale factor hfactor h)

/-- Scaling a quotient class is scaling any of its compact measured representatives. -/
@[simp] theorem scale_toMeasuredGHSpace (factor : ℝ) (hfactor : 0 < factor)
    (X : CompactMeasuredSpace.{u}) :
    scale factor hfactor (toMeasuredGHSpace X) =
      toMeasuredGHSpace (CompactMeasuredSpace.scale factor hfactor X) := rfl

/-- Scaling an unrooted measured GH class by one is the identity. -/
@[simp] theorem scale_one (X : MeasuredGHSpace.{u}) : scale 1 zero_lt_one X = X := by
  induction X using Quotient.inductionOn with
  | _ X =>
    apply Quotient.sound
    exact CompactMeasuredSpace.measuredIsometry_scale_one X

/-- Scaling by a positive factor and its reciprocal is the identity on unrooted measured classes. -/
@[simp] theorem scale_inv (factor : ℝ) (hfactor : 0 < factor) (X : MeasuredGHSpace.{u}) :
    scale factor⁻¹ (inv_pos.mpr hfactor) (scale factor hfactor X) = X := by
  induction X using Quotient.inductionOn with
  | _ X =>
    apply Quotient.sound
    exact CompactMeasuredSpace.measuredIsometry_scale_inv factor hfactor X

/-- Positive spatial scaling has the same upper GHP Lipschitz bound as in the rooted case. -/
theorem dist_scale_le (factor : ℝ) (hfactor : 0 < factor) (X Y : MeasuredGHSpace.{u}) :
    dist (scale factor hfactor X) (scale factor hfactor Y) ≤ max factor 1 * dist X Y := by
  induction X using Quotient.inductionOn with
  | _ X =>
    induction Y using Quotient.inductionOn with
    | _ Y => exact CompactMeasuredSpace.distance_scale_le factor hfactor X Y

/-- Positive spatial scaling has the lower GHP expansion bound `min factor 1`. -/
theorem min_mul_dist_le_scale (factor : ℝ) (hfactor : 0 < factor)
    (X Y : MeasuredGHSpace.{u}) :
    min factor 1 * dist X Y ≤ dist (scale factor hfactor X) (scale factor hfactor Y) := by
  induction X using Quotient.inductionOn with
  | _ X =>
    induction Y using Quotient.inductionOn with
    | _ Y => exact CompactMeasuredSpace.min_mul_distance_le_scale factor hfactor X Y

/-- Fixed-factor spatial scaling is Lipschitz for the unrooted measured GHP metric. -/
theorem lipschitzWith_scale (factor : ℝ) (hfactor : 0 < factor) :
    LipschitzWith ⟨max factor 1, zero_le_one.trans (le_max_right _ _)⟩
      (scale factor hfactor : MeasuredGHSpace.{u} → MeasuredGHSpace.{u}) :=
  lipschitzWith_iff_dist_le_mul.mpr (dist_scale_le factor hfactor)

/-- Fixed-factor spatial scaling is continuous on unrooted measured GH classes. -/
theorem continuous_scale (factor : ℝ) (hfactor : 0 < factor) :
    Continuous (scale factor hfactor : MeasuredGHSpace.{u} → MeasuredGHSpace.{u}) :=
  (lipschitzWith_scale factor hfactor).continuous

/-- Fixed-factor spatial scaling is Borel measurable on unrooted measured GH classes. -/
theorem measurable_scale (factor : ℝ) (hfactor : 0 < factor) :
    Measurable (scale factor hfactor : MeasuredGHSpace.{u} → MeasuredGHSpace.{u}) :=
  (continuous_scale factor hfactor).measurable

/-- Spatial scaling is jointly continuous in its positive factor and unrooted measured class. -/
theorem continuous_scale_joint :
    Continuous (fun p : Set.Ioi (0 : ℝ) × MeasuredGHSpace.{u} =>
      scale p.1.val p.1.property p.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨c, Z⟩
  induction Z using Quotient.inductionOn with
  | _ X =>
    let D : ℝ := Metric.diam (Set.univ : Set X)
    have hcont : Continuous (fun p : Set.Ioi (0 : ℝ) × MeasuredGHSpace.{u} =>
        max (p.1 : ℝ) 1 * dist p.2 (toMeasuredGHSpace X) +
          |(p.1 : ℝ) - (c : ℝ)| * D) := by
      fun_prop
    have hzero : Tendsto
        (fun p : Set.Ioi (0 : ℝ) × MeasuredGHSpace.{u} =>
          max (p.1 : ℝ) 1 * dist p.2 (toMeasuredGHSpace X) +
            |(p.1 : ℝ) - (c : ℝ)| * D)
        (𝓝 (c, toMeasuredGHSpace X)) (𝓝 0) := by
      simpa only [dist_self, sub_self, abs_zero, mul_zero, zero_mul, add_zero, zero_add] using
        hcont.tendsto (c, toMeasuredGHSpace X)
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) ?_ hzero
    intro p
    calc
      dist (scale p.1.val p.1.property p.2)
          (scale c.val c.property (toMeasuredGHSpace X)) ≤
        dist (scale p.1.val p.1.property p.2)
            (scale p.1.val p.1.property (toMeasuredGHSpace X)) +
          dist (scale p.1.val p.1.property (toMeasuredGHSpace X))
            (scale c.val c.property (toMeasuredGHSpace X)) := dist_triangle _ _ _
      _ ≤ max (p.1 : ℝ) 1 * dist p.2 (toMeasuredGHSpace X) +
          |(p.1 : ℝ) - (c : ℝ)| * D := by
        apply add_le_add (dist_scale_le p.1.val p.1.property p.2 (toMeasuredGHSpace X))
        exact CompactMeasuredSpace.distance_scale_scale_le
          p.1.val c.val p.1.property c.property X

/-- Joint spatial scaling is Borel measurable for the product Borel structure. -/
theorem measurable_scale_joint :
    Measurable (fun p : Set.Ioi (0 : ℝ) × MeasuredGHSpace.{u} =>
      scale p.1.val p.1.property p.2) :=
  continuous_scale_joint.measurable

end MeasuredGHSpace
end BGW.MetricMeasure
