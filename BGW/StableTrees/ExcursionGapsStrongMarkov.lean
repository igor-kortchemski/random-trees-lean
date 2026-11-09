/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableStrongMarkov
public import BGW.StableTrees.ReflectedRestart

import BGW.StableTrees.StablePassageSubordinatorPath
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Strong Markov property of the reflected stable process

Progressive measurability of the running infimum and reflection gives an everywhere measurable
version of the stopped reflected state.  The centered stable strong-Markov property then yields
the reflected transition kernel at almost surely finite stopping times.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Reflected state at a random time, with the standard `toNNReal` junk branch at infinity. -/
noncomputable def reflectedStateAt (τ : DLoc → ℝ≥0∞) (f : DLoc) : ℝ≥0 :=
  ⟨(reflectedFrom 0 f).1 (τ f).toNNReal, reflectedFrom_nonneg 0 f _⟩

/-- Post-`τ` reflected path, restarted from its stopped state on the centered stable future. -/
noncomputable def reflectedFutureAt (τ : DLoc → ℝ≥0∞) (f : DLoc) : DLoc :=
  reflectedFrom (reflectedStateAt τ f) (DLoc.shiftAt τ f)

/-- On `{τ < ∞}`, `reflectedFutureAt` is literally the reflected path after time `τ`. -/
theorem reflectedFutureAt_apply (τ : DLoc → ℝ≥0∞) {f : DLoc} (hτfin : τ f < ⊤)
    (u : ℝ≥0) :
    (reflectedFutureAt τ f).1 u = (reflectedFrom 0 f).1 ((τ f).toNNReal + u) := by
  exact (reflectedFrom_restart_shiftAt 0 τ hτfin u).symm

private theorem stoppedVersion_reflectedState {τ : DLoc → ℝ≥0∞} (f : DLoc) (hf : τ f < ⊤) :
    (stoppedValue (fun t f => (reflectedFrom 0 f).1 t) τ f).toNNReal =
      reflectedStateAt τ f := by
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hf)
  apply Subtype.ext
  simp only [stoppedValue, ← ht, reflectedStateAt]
  exact Real.coe_toNNReal _ (reflectedFrom_nonneg 0 f _)

private theorem integral_reflectedFuture_strongMarkov {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ)
    {A : Set DLoc} (hA : MeasurableSet[hτ.measurableSpace] A)
    (hAτ : A ⊆ {f | τ f < ⊤}) {G : DLoc → ℝ} (hG : Measurable G)
    (hGb : ∃ C : ℝ, ∀ p, |G p| ≤ C) :
    ∫ f in A, G (reflectedFutureAt τ f) ∂(stableLocalLaw θ : Measure DLoc) =
      ∫ f in A, (∫ g, G (reflectedFrom (reflectedStateAt τ f) g)
        ∂(stableLocalLaw θ : Measure DLoc)) ∂(stableLocalLaw θ : Measure DLoc) := by
  let P : Measure DLoc := stableLocalLaw θ
  let Y : DLoc → ℝ≥0 := fun f =>
    (stoppedValue (fun t f => (reflectedFrom 0 f).1 t) τ f).toNNReal
  let H : ℝ≥0 × DLoc → ℝ := fun p => G (reflectedFrom p.1 p.2)
  have hY : Measurable[hτ.measurableSpace] Y :=
    (measurable_stoppedValue isStronglyProgressive_reflectedFrom_zero hτ).real_toNNReal
  have he : ∀ f ∈ A, Y f = reflectedStateAt τ f := by
    intro f hf
    exact stoppedVersion_reflectedState f (hAτ hf)
  have hH : Measurable H := hG.comp measurable_reflectedFrom
  have hHb : ∃ C : ℝ, ∀ p, |H p| ≤ C := by
    obtain ⟨C, hC⟩ := hGb
    exact ⟨C, fun p => hC _⟩
  have hAg : MeasurableSet A := hτ.measurableSpace_le _ hA
  calc
    _ = ∫ f in A, H (Y f, DLoc.shiftAt τ f) ∂P := by
      apply setIntegral_congr_fun hAg
      intro f hf
      dsimp [H, reflectedFutureAt]
      rw [he f hf]
    _ = ∫ f in A, (∫ g, H (Y f, g) ∂P) ∂P := by
      apply integral_freeze_shiftAt P P (DLoc.measurable_shiftAt hτ) hH hHb
        (m := hτ.measurableSpace) hτ.measurableSpace_le hY hA
      intro B hB hBA C hC
      exact measure_inter_preimage_shiftAt hθ hτ hB (hBA.trans hAτ) hC
    _ = _ := by
      apply setIntegral_congr_fun hAg
      intro f hf
      dsimp [H]
      rw [he f hf]

/-- **C20.1, strong Markov property.**  Conditionally on `F_τ`, the post-τ reflected path has
the reflected stable transition law started at its stopped reflected value. -/
theorem condExp_reflectedFutureAt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ)
    (hfin : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), τ f < ⊤)
    {G : DLoc → ℝ} (hG : Measurable G) (hGb : ∃ C : ℝ, ∀ p, |G p| ≤ C) :
    (stableLocalLaw θ : Measure DLoc)[fun f => G (reflectedFutureAt τ f) |
        hτ.measurableSpace] =ᵐ[(stableLocalLaw θ : Measure DLoc)]
      fun f => ∫ g, G (reflectedFrom (reflectedStateAt τ f) g)
        ∂(stableLocalLaw θ : Measure DLoc) := by
  let P : Measure DLoc := stableLocalLaw θ
  let S : Set DLoc := {f | τ f < ⊤}
  let Y : DLoc → ℝ≥0 := fun f =>
    (stoppedValue (fun t f => (reflectedFrom 0 f).1 t) τ f).toNNReal
  let H : ℝ≥0 × DLoc → ℝ := fun p => G (reflectedFrom p.1 p.2)
  have hS : MeasurableSet[hτ.measurableSpace] S := DLoc.measurableSet_lt_top_stopped hτ
  have hY : Measurable[hτ.measurableSpace] Y :=
    (measurable_stoppedValue isStronglyProgressive_reflectedFrom_zero hτ).real_toNNReal
  have hH : Measurable H := hG.comp measurable_reflectedFrom
  obtain ⟨C, hC⟩ := hGb
  have hHb : ∀ p, |H p| ≤ C := fun p => hC _
  have hK : StronglyMeasurable (fun y => ∫ g, H (y, g) ∂P) :=
    hH.stronglyMeasurable.integral_prod_right'
  have hKb : ∀ y, ‖∫ g, H (y, g) ∂P‖ ≤ C := by
    intro y
    simpa using (norm_integral_le_of_norm_le_const (μ := P)
      (Eventually.of_forall fun g => (show ‖H (y, g)‖ ≤ C by
        simpa only [Real.norm_eq_abs] using hHb (y, g))))
  have hHiY : Integrable (fun f => H (Y f, DLoc.shiftAt τ f)) P :=
    Integrable.of_bound (hH.comp ((hY.mono hτ.measurableSpace_le le_rfl).prodMk
      (DLoc.measurable_shiftAt hτ))).aestronglyMeasurable C
      (Eventually.of_forall fun f => by simpa only [Real.norm_eq_abs] using hHb _)
  have hKiY : Integrable (fun f => ∫ g, H (Y f, g) ∂P) P :=
    Integrable.of_bound (hK.comp_measurable
      (hY.mono hτ.measurableSpace_le le_rfl)).aestronglyMeasurable C
      (Eventually.of_forall fun f => hKb _)
  have hfun : (fun f => H (Y f, DLoc.shiftAt τ f)) =ᵐ[P]
      fun f => G (reflectedFutureAt τ f) := by
    filter_upwards [hfin] with f hf
    dsimp [H, reflectedFutureAt]
    have he : Y f = reflectedStateAt τ f := stoppedVersion_reflectedState f hf
    rw [he]
  have hres : (fun f => ∫ g, H (Y f, g) ∂P) =ᵐ[P]
      fun f => ∫ g, G (reflectedFrom (reflectedStateAt τ f) g) ∂P := by
    filter_upwards [hfin] with f hf
    dsimp [H]
    have he : Y f = reflectedStateAt τ f := stoppedVersion_reflectedState f hf
    rw [he]
  have hi : Integrable (fun f => G (reflectedFutureAt τ f)) P := hHiY.congr hfun
  have hki : Integrable (fun f => ∫ g, G (reflectedFrom (reflectedStateAt τ f) g) ∂P) P :=
    hKiY.congr hres
  have hmeas : AEStronglyMeasurable[hτ.measurableSpace]
      (fun f => ∫ g, G (reflectedFrom (reflectedStateAt τ f) g) ∂P) P :=
    (hK.comp_measurable hY).aestronglyMeasurable.congr hres
  apply (ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le hi
    (fun _ _ _ => hki.integrableOn) _ hmeas).symm
  intro A hA _
  symm
  have hAS : A ∩ S =ᵐ[P] A := by
    filter_upwards [hfin] with f hf
    apply propext
    change (f ∈ A ∧ τ f < ⊤) ↔ f ∈ A
    exact and_iff_left hf
  have hfact := integral_reflectedFuture_strongMarkov hθ hτ (hA.inter hS)
    inter_subset_right hG ⟨C, hC⟩
  rw [Measure.restrict_congr_set hAS] at hfact
  exact hfact

end BGW.StableTrees
