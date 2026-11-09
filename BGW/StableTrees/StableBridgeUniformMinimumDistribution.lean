/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableBridgeUniformMinimumLimit
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Distribution functions of finite-grid minimum times

Uniform finite minimum indices give a grid distribution function converging to the identity.
Almost sure convergence and atomlessness identify the limiting distribution function.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter VIII (Vervaat's
transformation and the uniform law of the minimum time); L. Chaumont, *Excursion normalisée,
méandre et pont pour les processus de Lévy stables*, Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Exact distribution function of a finite-grid minimum time below one. -/
theorem stableBridgeLaw_bridgeGridMinTime_le {θ x : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (hx : 0 ≤ x) (hx1 : x < 1) (M : ℕ) :
    (stableBridgeLaw θ : Measure (D 1 ℝ)) {f | (bridgeGridMinTime M f : ℝ) ≤ x} =
      ENNReal.ofReal (((⌊((M : ℝ) + 1) * x⌋₊ : ℝ) + 1) / ((M : ℝ) + 1)) := by
  classical
  have hd : (0 : ℝ) < M + 1 := by positivity
  have hn : 0 ≤ ((M : ℝ) + 1) * x := mul_nonneg hd.le hx
  have hfloor : ⌊((M : ℝ) + 1) * x⌋₊ < M + 1 := by
    apply (Nat.floor_lt hn).mpr
    push_cast
    exact mul_lt_of_lt_one_right hd hx1
  let q : Fin (M + 1) := ⟨⌊((M : ℝ) + 1) * x⌋₊, hfloor⟩
  have hevent : {f : D 1 ℝ | (bridgeGridMinTime M f : ℝ) ≤ x} =
      (bridgeGridMinIndex M) ⁻¹' (↑(Finset.Iic q) : Set (Fin (M + 1))) := by
    ext f
    simp only [mem_ofPred_eq, mem_preimage, Finset.mem_coe, Finset.mem_Iic]
    rw [show (bridgeGridMinTime M f : ℝ) =
      (bridgeGridMinIndex M f : ℝ) / (M + 1) from gridTime_coe M _ (by omega)]
    rw [div_le_iff₀ hd]
    change ((bridgeGridMinIndex M f).val : ℝ) ≤ x * (M + 1) ↔
      (bridgeGridMinIndex M f).val ≤ ⌊((M : ℝ) + 1) * x⌋₊
    simpa only [mul_comm] using (Nat.le_floor_iff hn).symm
  rw [hevent]
  have hsum := sum_measure_preimage_singleton
    (μ := (stableBridgeLaw θ : Measure (D 1 ℝ))) (Finset.Iic q)
    (f := bridgeGridMinIndex M) (fun _ _ => (measurable_bridgeGridMinIndex M)
      (measurableSet_singleton _))
  change (∑ b ∈ Finset.Iic q, (stableBridgeLaw θ : Measure (D 1 ℝ))
    {f | bridgeGridMinIndex M f = b}) = _ at hsum
  simp only [stableBridgeLaw_bridgeGridMinIndex_eq hθ, Finset.sum_const,
    Fin.card_Iic, nsmul_eq_mul] at hsum
  rw [← hsum, ENNReal.ofReal_div_of_pos hd]
  simp [q, ENNReal.ofReal_add, div_eq_mul_inv]

/-- The finite-grid distribution functions tend to the uniform distribution function. -/
theorem tendsto_stableBridgeLaw_bridgeGridMinTime_le {θ x : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (hx : 0 ≤ x) (hx1 : x < 1) :
    Tendsto (fun M => (stableBridgeLaw θ : Measure (D 1 ℝ))
      {f | (bridgeGridMinTime M f : ℝ) ≤ x}) atTop (𝓝 (ENNReal.ofReal x)) := by
  have hreal : Tendsto (fun M : ℕ =>
      ((⌊((M : ℝ) + 1) * x⌋₊ : ℝ) + 1) / ((M : ℝ) + 1)) atTop (𝓝 x) := by
    have hd (M : ℕ) : (0 : ℝ) < M + 1 := by positivity
    have hupper : Tendsto (fun M : ℕ => x + 1 / ((M : ℝ) + 1)) atTop (𝓝 (x + 0)) :=
      (tendsto_const_nhds (x := x)).add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at hupper
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · intro M
      apply (le_div_iff₀ (hd M)).mpr
      nlinarith [Nat.lt_floor_add_one (((M : ℝ) + 1) * x)]
    · intro M
      apply (div_le_iff₀ (hd M)).mpr
      have hlo := Nat.floor_le (mul_nonneg (hd M).le hx)
      have hinv : (1 / ((M : ℝ) + 1)) * ((M : ℝ) + 1) = 1 :=
        div_mul_cancel₀ 1 (hd M).ne'
      nlinarith
  simpa only [Function.comp_def, stableBridgeLaw_bridgeGridMinTime_le hθ hx hx1] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal

/-- Almost sure convergence and absence of atoms give convergence of the grid event masses. -/
theorem tendsto_bridgeGridMinTime_event {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ) :
    Tendsto (fun M => (stableBridgeLaw θ : Measure (D 1 ℝ))
      {f | (bridgeGridMinTime M f : ℝ) ≤ x}) atTop
      (𝓝 ((stableBridgeLaw θ : Measure (D 1 ℝ)) {f | (vervaatTime f : ℝ) ≤ x})) := by
  let μ := (stableBridgeLaw θ : Measure (D 1 ℝ))
  let A (M : ℕ) := {f : D 1 ℝ | (bridgeGridMinTime M f : ℝ) ≤ x}
  let B := {f : D 1 ℝ | (vervaatTime f : ℝ) ≤ x}
  have hA (M : ℕ) : MeasurableSet (A M) :=
    measurableSet_le (measurable_bridgeGridMinTime M) measurable_const
  have hB : MeasurableSet B := measurableSet_le
    (measurable_subtype_coe.comp measurable_vervaatTime) measurable_const
  have hlim : ∀ᵐ f ∂μ, Tendsto (fun M => (A M).indicator (fun _ => (1 : ℝ≥0∞)) f)
      atTop (𝓝 (B.indicator (fun _ => (1 : ℝ≥0∞)) f)) := by
    filter_upwards [stableBridgeLaw_ae_tendsto_bridgeGridMinTime hθ,
      stableBridgeLaw_ae_vervaatTime_ne hθ x] with f hf hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hev := (tendsto_order.mp hf).2 x hlt
      have heq : (fun M => (A M).indicator (fun _ => (1 : ℝ≥0∞)) f) =ᶠ[atTop]
          (fun _ => 1) := by
        filter_upwards [hev] with M hM
        rw [indicator_of_mem (show f ∈ A M from hM.le)]
      rw [indicator_of_mem (show f ∈ B from hlt.le)]
      exact tendsto_const_nhds.congr' heq.symm
    · have hev := (tendsto_order.mp hf).1 x hgt
      have heq : (fun M => (A M).indicator (fun _ => (1 : ℝ≥0∞)) f) =ᶠ[atTop]
          (fun _ => 0) := by
        filter_upwards [hev] with M hM
        rw [indicator_of_notMem (show f ∉ A M from not_le_of_gt hM)]
      rw [indicator_of_notMem (show f ∉ B from not_le_of_gt hgt)]
      exact tendsto_const_nhds.congr' heq.symm
  have h := tendsto_lintegral_of_dominated_convergence (μ := μ) (fun _ => 1)
    (fun M => measurable_const.indicator (hA M))
    (fun M => ae_of_all _ fun f => by simp only [indicator_apply]; split_ifs <;> simp)
    (by simp [μ]) hlim
  simpa only [lintegral_indicator (hA _), lintegral_indicator hB,
    lintegral_const, one_mul, Measure.restrict_apply_univ] using h

end BGW.StableTrees
