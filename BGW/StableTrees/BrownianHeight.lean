/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightProcess
public import BGW.StableTrees.StableFirstPassagePath
import BGW.StableTrees.StableProcessBrownian
public import BGW.StableTrees.HeightContinuity

/-!
# The continuous height at stability index two

At `θ = 2`, Brownian path continuity upgrades the fixed-time formula `H = X - I` to an
almost sure identity simultaneously at all times for the common continuous modification.

## Public proof helpers

* `futureInf_zero_eq_runningInfLoc`: the initial future infimum is the running infimum.
* `ae_heightLoc_two`: simultaneous identification of the continuous height and reflected path.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

@[expose] public section

namespace BGW.StableTrees

/-- The future infimum from time `0` is the running infimum. -/
theorem futureInf_zero_eq_runningInfLoc (f : DLoc) (t : ℝ≥0) :
    futureInf f t 0 = runningInfLoc f t := by
  exact futureInf_zero_eq_runningInf f t

private lemma continuousAt_of_continuous_restrict {f : DLoc} {t T : ℝ≥0} (htT : t < T)
    (h : ContinuousAt (DLoc.restrict T f)
      ⟨t, t.2, (show (t : ℝ) ≤ (T : ℝ) from htT.le)⟩) :
    ContinuousAt f.1 t := by
  let t' : Set.Icc (0 : ℝ) (T : ℝ) := ⟨t, t.2, htT.le⟩
  rw [Metric.continuousAt_iff] at h ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := h ε hε
  refine ⟨min δ ((T : ℝ) - (t : ℝ)), lt_min hδ (sub_pos.mpr htT), ?_⟩
  intro u hu
  have huδ : dist u t < δ := hu.trans_le (min_le_left _ _)
  have huTdist : dist u t < (T : ℝ) - (t : ℝ) := hu.trans_le (min_le_right _ _)
  have huT : u < T := by
    have hu_abs : |(u : ℝ) - (t : ℝ)| < (T : ℝ) - (t : ℝ) := by
      simpa only [NNReal.dist_eq, Real.dist_eq] using huTdist
    have huT' : (u : ℝ) < (T : ℝ) := by
      have hh := (abs_lt.mp hu_abs).2
      linarith
    exact_mod_cast huT'
  let u' : Set.Icc (0 : ℝ) (T : ℝ) := ⟨u, u.2, huT.le⟩
  have hu' : dist u' t' < δ := by
    simpa [u', t', Subtype.dist_eq, NNReal.dist_eq, Real.dist_eq] using huδ
  exact hδf hu'

private lemma ae_continuous_restrict_two {T : ℝ≥0} (hT : 0 < T) :
    ∀ᵐ f ∂(stableLocalLaw 2 : Measure DLoc), Continuous (DLoc.restrict T f) := by
  have hθ : 1 < (2 : ℝ) ∧ (2 : ℝ) ≤ 2 := by norm_num
  have h := ae_mem_range_ofContinuous_stableProcessLaw_two (show 0 < (T : ℝ) from hT)
  rw [← map_restrict_stableLocalLaw hθ (by exact_mod_cast hT)] at h
  have h' := ae_of_ae_map (DLoc.measurable_restrict T).aemeasurable h
  filter_upwards [h'] with f hf
  obtain ⟨g, hg⟩ := hf
  rw [← hg]
  exact g.continuous

private lemma ae_continuous_two :
    ∀ᵐ f ∂(stableLocalLaw 2 : Measure DLoc), Continuous f.1 := by
  have hrestrict : ∀ n : ℕ, ∀ᵐ f ∂(stableLocalLaw 2 : Measure DLoc),
      Continuous (DLoc.restrict ((n : ℝ≥0) + 1) f) := by
    intro n
    exact ae_continuous_restrict_two (by positivity)
  filter_upwards [ae_all_iff.mpr hrestrict] with f hf
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt (t : ℝ)
  have ht : t < (n : ℝ≥0) + 1 := by
    have hnt : t < (n : ℝ≥0) := by exact_mod_cast hn
    exact hnt.trans_le (le_add_right le_rfl)
  exact continuousAt_of_continuous_restrict ht (hf n).continuousAt

/-- **C26 (K17).**  At `θ = 2`, almost surely, the continuous height is `X - I` at every time. -/
theorem ae_heightLoc_two :
    ∀ᵐ f ∂(stableLocalLaw 2 : Measure DLoc), ∀ t : ℝ≥0,
      heightLoc 2 f t = f.1 t - runningInfLoc f t := by
  have hθ : 1 < (2 : ℝ) ∧ (2 : ℝ) ≤ 2 := by norm_num
  have hrat : ∀ q : ℚ, ∀ᵐ f ∂(stableLocalLaw 2 : Measure DLoc),
      heightLoc 2 f (q : ℝ).toNNReal =
        f.1 (q : ℝ).toNNReal - runningInfLoc f (q : ℝ).toNNReal := by
    intro q
    filter_upwards [ae_heightLoc_eq_height hθ (q : ℝ).toNNReal,
      ae_height_two (q : ℝ).toNNReal] with f hloc hh
    rw [hloc, hh, futureInf_zero_eq_runningInfLoc]
  filter_upwards [ae_all_iff.mpr hrat, ae_continuous_two] with f hqf hf
  have hI : Continuous (runningInfLoc f) := by
    apply runningInfLoc_continuous
    intro t
    exact (hf.continuousAt.continuousWithinAt.leftLim_eq).le
  have heq : heightLoc 2 f = fun t => f.1 t - runningInfLoc f t := by
    apply Continuous.ext_on dense_isRationalTime (continuous_heightLoc 2 f) (hf.sub hI)
    intro t ht
    obtain ⟨q, hq⟩ := ht
    have hqt : (q : ℝ).toNNReal = t := by
      have hq0 : 0 ≤ (q : ℝ) := t.2.trans hq.ge
      apply NNReal.coe_injective
      rw [Real.coe_toNNReal _ hq0]
      exact hq
    rw [← hqt]
    exact hqf q
  exact congrFun heq

end BGW.StableTrees
