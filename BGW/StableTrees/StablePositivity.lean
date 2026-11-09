/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableLaw
public import BGW.StableTrees.StableDensityAPI
import BGW.StableTrees.StableKendall
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Sign probabilities of the spectrally positive stable law

Kendall's density at level one has total mass one. Substituting `u = s^(-1/θ)`
identifies this mass with `θ` times the negative half-line mass of the stable density.
The positive half-line probability follows by complementation, and positive spatial
scaling preserves the sign probabilities of every positive-time marginal.

References: J. Bertoin, *Lévy Processes* (1996), Chapter VIII;
V. M. Zolotarev, *One-dimensional Stable Distributions* (1986), Chapter I.4.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BGW.StableTrees

/-- No atom at `0`. -/
theorem stableLaw_singleton_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (stableLaw θ : Measure ℝ) {0} = 0 := by
  rw [stableLaw_eq_withDensity hθ, withDensity_apply _ (measurableSet_singleton 0)]
  simp

/-- Density form: `∫_{u>0} p_1(-u) du = 1/θ`. -/
theorem integral_stableDensity_neg_Ioi {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∫ u in Set.Ioi (0 : ℝ), Scalar.stableDensity θ (-u) = 1 / θ := by
  have hθpos : 0 < θ := by linarith [hθ.1]
  have hp : -1 / θ < 0 := div_neg_of_neg_of_pos (by norm_num) hθpos
  have hK : (∫ s in Set.Ioi (0 : ℝ), kendallKernel θ 1 s) = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_restrict_of_forall_mem measurableSet_Ioi
        (fun s hs => kendallKernel_nonneg hθ (by norm_num) hs))
      ((continuousOn_kendallKernel_time hθ 1).aestronglyMeasurable measurableSet_Ioi)]
    simpa using congrArg ENNReal.toReal (lintegral_kendallKernel hθ (x := 1) (by norm_num))
  have hsub := integral_comp_rpow_Ioi (fun u : ℝ => Scalar.stableDensity θ (-u)) hp.ne
  have heq : (∫ s in Set.Ioi (0 : ℝ),
      (|-1 / θ| * s ^ (-1 / θ - 1)) • Scalar.stableDensity θ (-(s ^ (-1 / θ)))) =
      (1 / θ) * ∫ s in Set.Ioi (0 : ℝ), kendallKernel θ 1 s := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    dsimp only
    rw [smul_eq_mul, abs_of_neg hp, neg_div, neg_neg,
      Real.rpow_sub hs, Real.rpow_one]
    simp only [kendallKernel, stableDensityAt, mul_neg_one, neg_div]
    ring
  rw [heq, hK, mul_one] at hsub
  exact hsub.symm

/-- `P(X_1 < 0) = 1/θ` for the spectrally positive stable law. -/
theorem stableLaw_Iio_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (stableLaw θ : Measure ℝ) (Set.Iio 0) = ENNReal.ofReal (1 / θ) := by
  obtain ⟨μ, a, h⟩ := exists_stableDomain hθ
  have hi := (Scalar.integrable_stableDensity h).integrableOn (s := Set.Iio 0)
  have hint : (∫ x in Set.Iio (0 : ℝ), Scalar.stableDensity θ x) = 1 / θ := by
    simpa only [integral_comp_neg_Ioi, neg_zero, integral_Iic_eq_integral_Iio] using
      integral_stableDensity_neg_Ioi hθ
  rw [stableLaw_eq_withDensity hθ, withDensity_apply _ measurableSet_Iio,
    ← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (stableDensity_nonneg hθ)), hint]

/-- `P(X_1 > 0) = 1 - 1/θ` for the spectrally positive stable law. -/
theorem stableLaw_Ioi_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (stableLaw θ : Measure ℝ) (Set.Ioi 0) = ENNReal.ofReal (1 - 1 / θ) := by
  have hsum : (stableLaw θ : Measure ℝ) (Set.Iio 0) +
      (stableLaw θ : Measure ℝ) (Set.Ioi 0) = 1 := by
    rw [← measure_union (Set.disjoint_left.mpr (by
      intro x hx hy
      exact (lt_trans hx hy).false)) measurableSet_Ioi, Set.Iio_union_Ioi,
      measure_compl (measurableSet_singleton 0) (measure_ne_top _ _),
      measure_univ, stableLaw_singleton_zero hθ, tsub_zero]
  have hreal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    stableLaw_Iio_zero hθ,
    ENNReal.toReal_ofReal (div_nonneg (by norm_num) (by linarith [hθ.1]) : 0 ≤ 1 / θ),
    ENNReal.toReal_one] at hreal
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by
    have : 0 < θ := by linarith [hθ.1]
    exact sub_nonneg.mpr ((div_le_one this).mpr (by linarith [hθ.1])))]
  linarith

/-- Every time marginal has the same sign probabilities (scaling). -/
theorem stableLawAt_Iio_zero {θ t : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ht : 0 < t) :
    (stableLawAt θ t : Measure ℝ) (Set.Iio 0) = ENNReal.ofReal (1 / θ) := by
  have hc : 0 < t ^ (1 / θ) := Real.rpow_pos_of_pos ht _
  rw [stableLawAt, ProbabilityMeasure.map_apply' _ (by fun_prop) measurableSet_Iio]
  have heq : (fun x : ℝ => t ^ (1 / θ) * x) ⁻¹' Set.Iio 0 = Set.Iio 0 := by
    ext x
    change t ^ (1 / θ) * x < 0 ↔ x < 0
    constructor
    · intro hx
      nlinarith
    · exact mul_neg_of_pos_of_neg hc
  rw [heq, stableLaw_Iio_zero hθ]

end BGW.StableTrees
