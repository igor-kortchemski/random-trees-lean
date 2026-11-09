/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.UnitExcursionLawMixture

import BGW.StableTrees.UnitExcursionLawLifetime
import Mathlib.MeasureTheory.SetAlgebra

/-!
# Itô’s excursion family indexed by lifetime

The scaled unit laws have exact lifetimes and satisfy the stable scaling group law.  Restricting
the lifetime mixtures to measurable lifetime sets identifies a competing family almost everywhere;
a countable generating algebra removes the exceptional lifetime, and scaling proves uniqueness
at every positive lifetime.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **C22, exact lifetime.**  For every `a > 0`, `N_(a)` assigns mass one to `{ζ = a}`. -/
theorem measure_lifetime_excursionAt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (a : Set.Ioi (0 : ℝ)) :
    excursionAt θ a {e : Excursion | (e.lifetime : ℝ) = (a : ℝ)} = 1 := by
  let _ : IsProbabilityMeasure (excursionAt θ a) := isProbabilityMeasure_excursionAt θ a
  rw [← mem_ae_iff_prob_eq_one
    (measurableSet_eq_fun measurable_excursion_lifetime.coe_nnreal_real measurable_const)]
  exact ae_lifetime_excursionAt hθ a

/-- **C22, scaling.**  `(S^(λ))_* N_(a) = N_(λa)` for every `λ,a > 0`. -/
theorem excursionAt_scaling (θ : ℝ) (c a : Set.Ioi (0 : ℝ)) :
    (excursionAt θ a).map (excursionScale θ c) =
      excursionAt θ ⟨(c : ℝ) * (a : ℝ), Set.mem_Ioi.2 (mul_pos c.2 a.2)⟩ := by
  exact map_excursionScale_excursionAt θ c a

private theorem measure_inter_lifetime_preimage_aux {μ : Measure Excursion}
    (a : Set.Ioi (0 : ℝ))
    (hlife : ∀ᵐ e ∂μ, (e.lifetime : ℝ) = (a : ℝ))
    (A : Set Excursion) (B : Set (Set.Ioi (0 : ℝ))) :
    μ (A ∩ Excursion.lifetimePos ⁻¹' B) = B.indicator (fun _ => μ A) a := by
  by_cases ha : a ∈ B
  · rw [indicator_of_mem ha]
    apply measure_congr
    filter_upwards [hlife] with e he
    have he' : e.lifetimePos = a := Subtype.ext he
    simp only [mem_inter_iff, mem_preimage, he', ha, and_true]
  · rw [indicator_of_notMem ha, ← measure_empty (μ := μ)]
    apply measure_congr
    filter_upwards [hlife] with e he
    have he' : e.lifetimePos = a := Subtype.ext he
    simp only [mem_inter_iff, mem_preimage, he', ha, and_false, mem_empty_iff_false]

private theorem ae_eval_eq_excursionAt_aux {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (ν : Set.Ioi (0 : ℝ) → Measure Excursion)
    (hprob : ∀ a, ν a Set.univ = 1)
    (hlife : ∀ a, ν a {e : Excursion | (e.lifetime : ℝ) = (a : ℝ)} = 1)
    (hmeas : ∀ A : Set Excursion, MeasurableSet A → Measurable (fun a => ν a A))
    (hmix : ∀ A : Set Excursion, MeasurableSet A → excursionMeasure θ A =
      ∫⁻ a, ν a A * lifetimeDensity θ a ∂volIoi)
    (A : Set Excursion) (hA : MeasurableSet A) :
    (fun a => ν a A) =ᵐ[volIoi] fun a => excursionAt θ a A := by
  let _ : SigmaFinite volIoi := sigmaFinite_volIoi
  have hmul : (fun a => ν a A * lifetimeDensity θ a) =ᵐ[volIoi]
      (fun a => excursionAt θ a A * lifetimeDensity θ a) := by
    apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
      ((hmeas A hA).mul (measurable_lifetimeDensity θ))
      ((measurable_excursionAt_apply θ hA).mul (measurable_lifetimeDensity θ))
    intro B hB _
    have hνlife (a : Set.Ioi (0 : ℝ)) :
        ∀ᵐ e ∂(ν a), (e.lifetime : ℝ) = (a : ℝ) := by
      let _ : IsProbabilityMeasure (ν a) := ⟨hprob a⟩
      exact (mem_ae_iff_prob_eq_one
        (measurableSet_eq_fun measurable_excursion_lifetime.coe_nnreal_real measurable_const)).2
        (hlife a)
    have hAB : MeasurableSet (A ∩ Excursion.lifetimePos ⁻¹' B) :=
      hA.inter (hB.preimage measurable_lifetimePos)
    have hνint : (∫⁻ a in B, ν a A * lifetimeDensity θ a ∂volIoi) =
        ∫⁻ a, ν a (A ∩ Excursion.lifetimePos ⁻¹' B) * lifetimeDensity θ a ∂volIoi := by
      calc
        _ = ∫⁻ a, B.indicator (fun a => ν a A * lifetimeDensity θ a) a ∂volIoi :=
          (lintegral_indicator hB _).symm
        _ = _ := by
          apply lintegral_congr
          intro a
          let _ : IsProbabilityMeasure (ν a) := ⟨hprob a⟩
          rw [measure_inter_lifetime_preimage_aux a (hνlife a) A B]
          by_cases ha : a ∈ B <;> simp [ha]
    have hExcint : (∫⁻ a in B, excursionAt θ a A * lifetimeDensity θ a ∂volIoi) =
        ∫⁻ a, excursionAt θ a (A ∩ Excursion.lifetimePos ⁻¹' B) *
          lifetimeDensity θ a ∂volIoi := by
      calc
        _ = ∫⁻ a, B.indicator (fun a => excursionAt θ a A * lifetimeDensity θ a) a ∂volIoi :=
          (lintegral_indicator hB _).symm
        _ = _ := by
          apply lintegral_congr
          intro a
          let _ : IsProbabilityMeasure (excursionAt θ a) := isProbabilityMeasure_excursionAt θ a
          rw [measure_inter_lifetime_preimage_aux a (ae_lifetime_excursionAt hθ a) A B]
          by_cases ha : a ∈ B <;> simp [ha]
    exact hνint.trans ((hmix _ hAB).symm.trans
      ((excursionMeasure_eq_lifetime_mixture hθ hAB).trans hExcint.symm))
  filter_upwards [hmul] with a ha
  have hG : 0 < Real.Gamma (1 - 1 / θ) :=
    Real.Gamma_pos_of_pos (sub_pos.mpr ((div_lt_one (by linarith)).mpr hθ.1))
  have hd0 : lifetimeDensity θ (a : ℝ) ≠ 0 := by
    rw [lifetimeDensity]
    have hθpos : 0 < θ := lt_trans zero_lt_one hθ.1
    have hp : 0 < (1 / θ) / Real.Gamma (1 - 1 / θ) * (a : ℝ) ^ (-1 - 1 / θ) :=
      mul_pos (div_pos (one_div_pos.mpr hθpos) hG) (Real.rpow_pos_of_pos a.2 _)
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  exact (ENNReal.mul_left_inj hd0 ENNReal.ofReal_ne_top).mp ha

/-- **C22, uniqueness of the Itô family.**  A measurable probability family with exact lifetime
support, the stable scaling law and the lifetime mixture of `N` is `excursionAt θ`. -/
theorem excursionAt_unique {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (ν : Set.Ioi (0 : ℝ) → Measure Excursion)
    (hprob : ∀ a, ν a Set.univ = 1)
    (hlife : ∀ a, ν a {e : Excursion | (e.lifetime : ℝ) = (a : ℝ)} = 1)
    (hscale : ∀ c a, (ν a).map (excursionScale θ c) =
      ν ⟨(c : ℝ) * (a : ℝ), Set.mem_Ioi.2 (mul_pos c.2 a.2)⟩)
    (hmeas : ∀ A : Set Excursion, MeasurableSet A → Measurable (fun a => ν a A))
    (hmix : ∀ A : Set Excursion, MeasurableSet A → excursionMeasure θ A =
      ∫⁻ a, ν a A * lifetimeDensity θ a ∂volIoi) (a : Set.Ioi (0 : ℝ)) :
    ν a = excursionAt θ a := by
  let C : Set (Set Excursion) :=
    generateSetAlgebra (MeasurableSpace.countableGeneratingSet Excursion)
  have hCc : C.Countable :=
    countable_generateSetAlgebra MeasurableSpace.countable_countableGeneratingSet
  have hCgen : (inferInstance : MeasurableSpace Excursion) = MeasurableSpace.generateFrom C := by
    dsimp [C]
    rw [generateFrom_generateSetAlgebra_eq,
      MeasurableSpace.generateFrom_countableGeneratingSet]
  have hCpi : IsPiSystem C := fun s hs t ht _ =>
    isSetAlgebra_generateSetAlgebra.inter_mem hs ht
  have hCmeas {A : Set Excursion} (hA : A ∈ C) : MeasurableSet A := by
    have h : MeasurableSet[MeasurableSpace.generateFrom C] A :=
      MeasurableSpace.measurableSet_generateFrom hA
    rw [← hCgen] at h
    exact h
  have hgood : ∀ᵐ b ∂volIoi, ∀ A (hA : A ∈ C), ν b A = excursionAt θ b A :=
    (ae_ball_iff hCc).2 fun A hA =>
      ae_eval_eq_excursionAt_aux hθ ν hprob hlife hmeas hmix A (hCmeas hA)
  have huniv : volIoi Set.univ = ∞ := by
    rw [volIoi, (MeasurableEmbedding.subtype_coe measurableSet_Ioi).comap_apply]
    simp only [Set.image_univ, Subtype.range_coe]
    exact Real.volume_Ioi
  have hne : volIoi ≠ 0 := by
    intro hzero
    have := congrArg (fun μ : Measure (Set.Ioi (0 : ℝ)) => μ Set.univ) hzero
    simp [huniv] at this
  let _ : NeBot (ae volIoi) := ae_neBot.2 hne
  obtain ⟨b, hb⟩ := hgood.exists
  have hbeq : ν b = excursionAt θ b := by
    let _ : IsProbabilityMeasure (ν b) := ⟨hprob b⟩
    let _ : IsProbabilityMeasure (excursionAt θ b) := isProbabilityMeasure_excursionAt θ b
    exact MeasureTheory.ext_of_generate_finite C hCgen hCpi (fun A hA => hb A hA)
      (by simp [hprob b])
  let c : Set.Ioi (0 : ℝ) := ⟨(a : ℝ) / (b : ℝ), Set.mem_Ioi.2 (div_pos a.2 b.2)⟩
  have hcb : (c : ℝ) * (b : ℝ) = (a : ℝ) := by
    dsimp [c]
    exact div_mul_cancel₀ (a : ℝ) b.2.ne'
  have hscaled := hscale c b
  rw [hbeq, map_excursionScale_excursionAt] at hscaled
  have hba : (⟨(c : ℝ) * (b : ℝ), Set.mem_Ioi.2 (mul_pos c.2 b.2)⟩ :
      Set.Ioi (0 : ℝ)) = a := Subtype.ext hcb
  simpa only [hba] using hscaled.symm

end BGW.StableTrees
