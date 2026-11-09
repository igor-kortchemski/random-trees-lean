/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Scalar.Density
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Weighted bounds for the stable density

Differentiation under Fourier inversion and integration by parts give boundedness
of the density and its derivative after multiplication by the spatial variable.

Reference: V. M. Zolotarev, *One-dimensional Stable Distributions*, AMS, 1986, Section 2.4.
-/

@[expose] public section

open MeasureTheory Complex Filter Set
open scoped Topology

namespace BGW.StableTrees.Scalar

variable {α : ℝ}

private lemma hasDerivAt_power (hα : 1 < α) (u : ℝ) :
    HasDerivAt (fun v : ℝ => (-((v : ℂ) * I)) ^ (α : ℂ))
      ((α : ℂ) * (-((u : ℂ) * I)) ^ ((α - 1 : ℝ) : ℂ) * (-I)) u := by
  by_cases hu : u = 0
  · subst u
    have hα0 : α ≠ 0 := by linarith
    have hα1 : α - 1 ≠ 0 := by linarith
    simp only [ofReal_zero, zero_mul, neg_zero,
      Complex.zero_cpow (ofReal_ne_zero.mpr hα1), mul_zero]
    rw [hasDerivAt_iff_tendsto]
    simp only [ofReal_zero, zero_mul, neg_zero,
      Complex.zero_cpow (ofReal_ne_zero.mpr hα0), sub_zero, smul_zero,
      norm_neg, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, norm_cpow_real]
    have heq : (fun v : ℝ => |v|⁻¹ * |v| ^ α) = fun v : ℝ => |v| ^ (α - 1) := by
      funext v
      by_cases hv : v = 0
      · simp [hv, Real.zero_rpow hα1]
      · rw [Real.rpow_sub (abs_pos.mpr hv), Real.rpow_one, div_eq_mul_inv, mul_comm]
    rw [heq]
    simpa [Real.zero_rpow hα1] using
      (show Continuous (fun v : ℝ => |v| ^ (α - 1)) from
        continuous_abs.rpow_const (fun _ => Or.inr (by linarith))).tendsto 0
  · have hs : -((u : ℂ) * I) ∈ slitPlane := by
      rw [mem_slitPlane_iff]
      right
      simpa using hu
    have hd : HasDerivAt (fun v : ℝ => -((v : ℂ) * I)) (-I) u := by
      simpa using! ((hasDerivAt_id u).ofReal_comp.mul_const I).neg
    convert! (Complex.hasStrictDerivAt_cpow_const (c := (α : ℂ)) hs).hasDerivAt.scomp u hd
      using 1; simp [Complex.ofReal_sub, mul_comm]

private lemma hasDerivAt_cf (hα : 1 < α) (u : ℝ) :
    HasDerivAt (stableCF α)
      (cexp ((-((u : ℂ) * I)) ^ (α : ℂ)) *
        ((α : ℂ) * (-((u : ℂ) * I)) ^ ((α - 1 : ℝ) : ℂ) * (-I))) u :=
  (hasDerivAt_power hα u).cexp

private lemma integrable_rpow_cf (hα : 1 < α ∧ α ≤ 2) {s : ℝ} (hs : -1 < s) :
    Integrable (fun u : ℝ => |u| ^ s * ‖stableCF α u‖) := by
  convert integrable_rpow_abs_mul_exp_neg hs (by linarith : 0 < α)
    (neg_pos.mpr (cos_pi_mul_div_two_neg hα)) using 1
  ext u
  rw [norm_stableCF (by linarith)]
  simp

private lemma norm_deriv_cf (hα : 1 < α ∧ α ≤ 2) (u : ℝ) :
    ‖deriv (stableCF α) u‖ = α * (|u| ^ (α - 1) * ‖stableCF α u‖) := by
  rw [(hasDerivAt_cf hα.1 u).deriv]
  simp only [norm_mul, norm_neg, norm_I, mul_one, norm_cpow_real,
    norm_real, Real.norm_eq_abs, abs_of_pos (show 0 < α by linarith)]
  change ‖stableCF α u‖ * (α * |u| ^ (α - 1)) = _
  ring

private lemma integrable_deriv_cf (hα : 1 < α ∧ α ≤ 2) :
    Integrable (deriv (stableCF α)) := by
  apply ((integrable_rpow_cf hα (by linarith : -1 < α - 1)).const_mul α).mono'
    (aestronglyMeasurable_deriv _ _)
  exact Eventually.of_forall fun u => (norm_deriv_cf hα u).le

private lemma integrable_mul_cf (hα : 1 < α ∧ α ≤ 2) :
    Integrable (fun u : ℝ => (u : ℂ) * stableCF α u) := by
  apply (integrable_abs_mul_norm_stableCF hα).mono'
    ((Complex.continuous_ofReal.mul (continuous_stableCF (by linarith))).aestronglyMeasurable)
  exact Eventually.of_forall fun u => by simp

private lemma integrable_mul_deriv_cf (hα : 1 < α ∧ α ≤ 2) :
    Integrable (fun u : ℝ => (u : ℂ) * deriv (stableCF α) u) := by
  apply ((integrable_rpow_cf hα (by linarith : -1 < α)).const_mul α).mono'
    ((by fun_prop : AEStronglyMeasurable (fun u : ℝ => (u : ℂ)) volume).mul
      (aestronglyMeasurable_deriv _ _))
  refine Eventually.of_forall fun u => ?_
  simp only [Pi.mul_apply]
  rw [norm_mul, norm_deriv_cf hα, norm_real, Real.norm_eq_abs]
  have hp : |u| ^ α = |u| * |u| ^ (α - 1) := by
    convert Real.rpow_add_of_nonneg (abs_nonneg u) (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : 0 ≤ α - 1) using 1 <;> simp
  rw [hp]
  ring_nf
  exact le_refl _

private lemma hasDerivAt_osc (u x : ℝ) :
    HasDerivAt (fun v : ℝ => cexp (-((v : ℂ) * x * I)))
      (cexp (-((u : ℂ) * x * I)) * (-((x : ℂ) * I))) u := by
  convert (((Complex.ofRealCLM.hasDerivAt.mul_const (x : ℂ)).mul_const I).neg.cexp) using 1 <;>
    simp

private lemma bound_fourier {f f' : ℝ → ℂ} (hf : Integrable f)
    (hf' : Integrable f') (hd : ∀ u, HasDerivAt f (f' u) u) (x : ℝ) :
    |x| * ‖∫ u : ℝ, f u * cexp (-((u : ℂ) * x * I))‖ ≤ ∫ u, ‖f' u‖ := by
  have hi (g : ℝ → ℂ) (hg : Integrable g) :
      Integrable (fun u : ℝ => g u * cexp (-((u : ℂ) * x * I))) :=
    hg.mul_bdd (c := 1) (by fun_prop)
      (Eventually.of_forall fun u => (BGW.StableTrees.Scalar.norm_cexp_neg_mul_I u x).le)
  have hb := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (u' := f')
    (v := fun u : ℝ => cexp (-((u : ℂ) * x * I)))
    (v' := fun u : ℝ => cexp (-((u : ℂ) * x * I)) * (-((x : ℂ) * I)))
    (fun u _ => hd u) (fun u _ => hasDerivAt_osc u x)
    (by simpa only [Pi.mul_apply, mul_assoc] using! (hi f hf).mul_const (-((x : ℂ) * I)))
    (hi f' hf') (hi f hf)
  have heq : (∫ u : ℝ, f u * cexp (-((u : ℂ) * x * I))) * (-((x : ℂ) * I)) =
      -(∫ u : ℝ, f' u * cexp (-((u : ℂ) * x * I))) := by
    simpa only [← integral_mul_const, mul_assoc] using hb
  calc |x| * ‖∫ u : ℝ, f u * cexp (-((u : ℂ) * x * I))‖
      = ‖(∫ u : ℝ, f u * cexp (-((u : ℂ) * x * I))) * (-((x : ℂ) * I))‖ := by
        simp [mul_comm]
    _ = ‖∫ u : ℝ, f' u * cexp (-((u : ℂ) * x * I))‖ := by rw [heq, norm_neg]
    _ ≤ ∫ u : ℝ, ‖f' u * cexp (-((u : ℂ) * x * I))‖ := norm_integral_le_integral_norm _
    _ = ∫ u, ‖f' u‖ := by
      congr 1; funext u
      rw [norm_mul, BGW.StableTrees.Scalar.norm_cexp_neg_mul_I, mul_one]

private lemma density_hasDeriv (hα : 1 < α ∧ α ≤ 2) (x : ℝ) :
    HasDerivAt (BGW.StableTrees.Scalar.stableDensity α)
      ((1 / (2 * Real.pi)) * (∫ u : ℝ,
        BGW.StableTrees.Scalar.stableCF α u *
          (cexp (-((u : ℂ) * x * I)) * (-((u : ℂ) * I)))).re) x := by
  let F : ℝ → ℝ → ℂ := fun x u => BGW.StableTrees.Scalar.stableCF α u *
    cexp (-((u : ℂ) * x * I))
  let F' : ℝ → ℝ → ℂ := fun x u => BGW.StableTrees.Scalar.stableCF α u *
    (cexp (-((u : ℂ) * x * I)) * (-((u : ℂ) * I)))
  have hd (u y : ℝ) : HasDerivAt (fun z => F z u) (F' y u) y := by
    have h := (hasDerivAt_osc y u).const_mul (BGW.StableTrees.Scalar.stableCF α u)
    convert! h using 1
    · funext z
      dsimp [F]
      congr 2
      ring
    · dsimp [F']
      congr 2
      congr 1
      ring
  have hn (u y : ℝ) : ‖F' y u‖ = |u| * ‖BGW.StableTrees.Scalar.stableCF α u‖ := by
    dsimp [F']
    rw [norm_mul, norm_mul, BGW.StableTrees.Scalar.norm_cexp_neg_mul_I]
    simp [mul_comm]
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (s := Set.univ) (bound := fun u : ℝ =>
      |u| * ‖BGW.StableTrees.Scalar.stableCF α u‖) (by simp)
    (Eventually.of_forall fun y =>
      (BGW.StableTrees.Scalar.integrable_stableCF_mul_cexp hα y).aestronglyMeasurable)
    (BGW.StableTrees.Scalar.integrable_stableCF_mul_cexp hα x)
    (by dsimp [F']; exact ((BGW.StableTrees.Scalar.continuous_stableCF (by linarith)).mul
      (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun u y _ => (hn u y).le)
    (BGW.StableTrees.Scalar.integrable_abs_mul_norm_stableCF hα)
    (Eventually.of_forall fun u y _ => hd u y)
  exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hi.2).const_mul _

private lemma bound_real_fourier {f f' : ℝ → ℂ} (hf : Integrable f)
    (hf' : Integrable f') (hd : ∀ u, HasDerivAt f (f' u) u)
    (z : ℂ) (hz : ‖z‖ = 1) (x : ℝ) :
    |x * ((1 / (2 * Real.pi)) *
      (z * ∫ u : ℝ, f u * cexp (-((u : ℂ) * x * I))).re)| ≤
      (1 / (2 * Real.pi)) * ∫ u, ‖f' u‖ := by
  have hc : 0 ≤ 1 / (2 * Real.pi) := by positivity
  rw [abs_mul, abs_mul, abs_of_nonneg hc]
  calc |x| * ((1 / (2 * Real.pi)) *
        |(z * ∫ u : ℝ, f u * cexp (-((u : ℂ) * x * I))).re|)
      = (1 / (2 * Real.pi)) * (|x| *
        |(z * ∫ u : ℝ, f u * cexp (-((u : ℂ) * x * I))).re|) := by ring
    _ ≤ (1 / (2 * Real.pi)) * (|x| *
        ‖z * ∫ u : ℝ, f u * cexp (-((u : ℂ) * x * I))‖) := by
      gcongr
      exact Complex.abs_re_le_norm _
    _ = (1 / (2 * Real.pi)) * (|x| *
        ‖∫ u : ℝ, f u * cexp (-((u : ℂ) * x * I))‖) := by rw [norm_mul, hz, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (bound_fourier hf hf' hd x) hc

end BGW.StableTrees.Scalar

open Real

namespace BGW.StableTrees

/-- `sup_x |x p_1(x)| < ∞`. -/
theorem exists_abs_mul_stableDensity_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ C : ℝ, ∀ x : ℝ, |x * Scalar.stableDensity θ x| ≤ C := by
  refine ⟨(1 / (2 * Real.pi)) * ∫ u, ‖deriv (Scalar.stableCF θ) u‖, fun x => ?_⟩
  simpa only [Scalar.stableDensity, one_mul] using
    Scalar.bound_real_fourier (Scalar.integrable_stableCF hθ)
      (Scalar.integrable_deriv_cf hθ)
      (fun u => (Scalar.hasDerivAt_cf hθ.1 u).differentiableAt.hasDerivAt)
      1 (norm_one) x

/-- `p_1` is differentiable. -/
theorem differentiable_stableDensity {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    Differentiable ℝ (Scalar.stableDensity θ) := by
  intro x
  exact (Scalar.density_hasDeriv hθ x).differentiableAt

/-- `sup_x |x p_1'(x)| < ∞`. -/
theorem exists_abs_mul_deriv_stableDensity_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ C : ℝ, ∀ x : ℝ, |x * deriv (Scalar.stableDensity θ) x| ≤ C := by
  let f : ℝ → ℂ := fun u => (u : ℂ) * Scalar.stableCF θ u
  let f' : ℝ → ℂ := fun u => Scalar.stableCF θ u +
    (u : ℂ) * deriv (Scalar.stableCF θ) u
  have hd (u : ℝ) : HasDerivAt f (f' u) u := by
    simpa [f, f'] using!
      (Complex.ofRealCLM.hasDerivAt.mul
        (Scalar.hasDerivAt_cf hθ.1 u).differentiableAt.hasDerivAt)
  have hf : Integrable f := Scalar.integrable_mul_cf hθ
  have hf' : Integrable f' :=
    (Scalar.integrable_stableCF hθ).add (Scalar.integrable_mul_deriv_cf hθ)
  refine ⟨(1 / (2 * Real.pi)) * ∫ u, ‖f' u‖, fun x => ?_⟩
  rw [(Scalar.density_hasDeriv hθ x).deriv]
  have heq : (∫ u : ℝ, Scalar.stableCF θ u *
        (cexp (-((u : ℂ) * x * I)) * (-((u : ℂ) * I)))) =
      -I * ∫ u : ℝ, f u * cexp (-((u : ℂ) * x * I)) := by
    rw [← integral_const_mul]
    congr 1; funext u; dsimp [f]; ring
  rw [heq]
  exact Scalar.bound_real_fourier hf hf' hd (-I) (by simp) x

end BGW.StableTrees

