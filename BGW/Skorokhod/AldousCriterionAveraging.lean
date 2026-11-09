/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod

import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Averaging bounds for short exit gaps

Displacements at two nearby random times are compared with their displacements
over deterministic offsets by averaging over an interval of offsets. Translation
invariance removes the random difference of the two starting times.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal

namespace BGW.Skorokhod

/-- Averaging a pointwise cover of an interval bounds its length by two integrals.

Reference: Billingsley 1999, Section 16. -/
private theorem aldous_average_cover {a b : ℝ → ℝ≥0∞} (ha : Measurable a)
    (δ d : ℝ) (hcover : ∀ u ∈ Icc δ (2 * δ), 1 ≤ a u + b (u - d)) :
    ENNReal.ofReal δ ≤ (∫⁻ u, a u) + ∫⁻ u, b u := by
  have hpoint : ∀ u, (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ≥0∞)) u ≤
      a u + b (u - d) := by
    intro u
    by_cases hu : u ∈ Icc δ (2 * δ)
    · simpa only [indicator_of_mem hu] using hcover u hu
    · simp only [indicator_of_notMem hu, zero_le]
  have hint := lintegral_mono (μ := volume) hpoint
  rw [lintegral_indicator_const measurableSet_Icc, one_mul, Real.volume_Icc,
    show 2 * δ - δ = δ by ring, lintegral_add_left ha,
    lintegral_sub_right_eq_self] at hint
  exact hint

/-- A pointwise interval cover and uniform integral bounds yield a probability bound.
The offset `d` can depend arbitrarily on the sample.

Reference: Billingsley 1999, Section 16. -/
theorem measure_le_four_mul_of_aldous_cover {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] {δ : ℝ} (hδ : 0 < δ) {η : ℝ≥0∞}
    {A B : ℝ → Ω → ℝ≥0∞} (hA : Measurable (Function.uncurry A))
    (hB : Measurable (Function.uncurry B)) {E : Set Ω} (hE : MeasurableSet E)
    (d : Ω → ℝ)
    (hcover : ∀ ω ∈ E, ∀ u ∈ Icc δ (2 * δ), 1 ≤ A u ω + B (u - d ω) ω)
    (hAbound : ∀ u, (∫⁻ ω, A u ω ∂P) ≤
      (Icc (0 : ℝ) (2 * δ)).indicator (fun _ => η) u)
    (hBbound : ∀ u, (∫⁻ ω, B u ω ∂P) ≤
      (Icc (0 : ℝ) (2 * δ)).indicator (fun _ => η) u) : P E ≤ 4 * η := by
  have hpoint (ω) : E.indicator (fun _ => ENNReal.ofReal δ) ω ≤
      (∫⁻ u, A u ω) + ∫⁻ u, B u ω := by
    by_cases hω : ω ∈ E
    · rw [indicator_of_mem hω]
      exact aldous_average_cover (hA.comp (measurable_id.prodMk measurable_const))
        δ (d ω) (hcover ω hω)
    · simp only [indicator_of_notMem hω, zero_le]
  have hAint : Measurable (fun ω => ∫⁻ u, A u ω) := hA.lintegral_prod_left
  have htotal : ENNReal.ofReal δ * P E ≤
      (∫⁻ u, ∫⁻ ω, A u ω ∂P) + ∫⁻ u, ∫⁻ ω, B u ω ∂P := by
    have hint := lintegral_mono (μ := P) hpoint
    rw [lintegral_indicator_const hE, lintegral_add_left hAint,
      ← lintegral_lintegral_swap hA.aemeasurable,
      ← lintegral_lintegral_swap hB.aemeasurable] at hint
    exact hint
  have hboundA : (∫⁻ u, ∫⁻ ω, A u ω ∂P) ≤ ENNReal.ofReal (2 * δ) * η := by
    apply (lintegral_mono hAbound).trans_eq
    rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc, sub_zero, mul_comm]
  have hboundB : (∫⁻ u, ∫⁻ ω, B u ω ∂P) ≤ ENNReal.ofReal (2 * δ) * η := by
    apply (lintegral_mono hBbound).trans_eq
    rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc, sub_zero, mul_comm]
  have hmul : ENNReal.ofReal δ * P E ≤ ENNReal.ofReal δ * (4 * η) := by
    apply htotal.trans
    apply (add_le_add hboundA hboundB).trans_eq
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
    ring
  have hcancel : (ENNReal.ofReal δ)⁻¹ * (ENNReal.ofReal δ * P E) ≤
      (ENNReal.ofReal δ)⁻¹ * (ENNReal.ofReal δ * (4 * η)) := by
    gcongr 1
  simpa only [← mul_assoc,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hδ).ne' ENNReal.ofReal_ne_top,
    one_mul] using hcancel

end BGW.Skorokhod
