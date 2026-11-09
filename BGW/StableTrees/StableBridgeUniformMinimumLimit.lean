/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableBridgeUniformMinimumDiscrete
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Convergence of finite-grid minimum times

The completed lower envelope has a positive gap away from its unique minimizer.
A grid point near a continuous minimizer forces every grid minimum into that neighborhood.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter VIII (Vervaat's
transformation and the uniform law of the minimum time); L. Chaumont, *Excursion normalisée,
méandre et pont pour les processus de Lévy stables*, Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem completedValue_lowerSemicontinuous (f : D 1 ℝ) :
    LowerSemicontinuous (fun t => min (Function.leftLim f t) (f t)) := by
  intro t c hc
  obtain ⟨b, hcb, hbt⟩ := exists_between hc
  have he : ∀ᶠ s in 𝓝 t, b < f s := by
    rw [← nhdsLT_sup_nhdsGE t, eventually_sup]
    constructor
    · exact ((isCadlag f).tendsto_nhdsLT_leftLim t).eventually
        (eventually_gt_nhds (lt_min_iff.mp hbt).1)
    · have hge : ContinuousWithinAt f (Ici t) t := by
        rw [ContinuousWithinAt, ← nhdsGT_sup_nhdsWithin_singleton t, tendsto_sup]
        exact ⟨(isCadlag f).isRightContinuous t,
          by simpa only [nhdsWithin_singleton] using tendsto_pure_nhds f t⟩
      exact hge.eventually (eventually_gt_nhds (lt_min_iff.mp hbt).2)
  filter_upwards [he, eventually_eventually_nhds.mpr he] with s hs hsn
  apply lt_min
  · exact hcb.trans_le (isClosed_Ici.mem_of_mapClusterPt
      ((mapClusterPt_leftLim f s).mono nhdsWithin_le_nhds)
      (hsn.mono fun _ h => h.le))
  · exact hcb.trans hs

private theorem iInf_le_completedValue (f : D 1 ℝ) (t : Icc (0 : ℝ) 1) :
    (⨅ s, f s) ≤ min (Function.leftLim f t) (f t) := by
  refine le_min ?_ (ciInf_le (isBounded_range f).bddBelow t)
  apply isClosed_Ici.mem_of_mapClusterPt (mapClusterPt_leftLim f t)
  exact Eventually.of_forall fun s => ciInf_le (isBounded_range f).bddBelow s

private theorem minimum_gap {f : D 1 ℝ}
    (huniq : ∀ t : Icc (0 : ℝ) 1,
      min (Function.leftLim f t) (f t) = ⨅ s, f s → t = vervaatTime f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t : Icc (0 : ℝ) 1, ε ≤ dist t (vervaatTime f) →
      (⨅ s, f s) + δ ≤ min (Function.leftLim f t) (f t) := by
  let K : Set (Icc (0 : ℝ) 1) := {t | ε ≤ dist t (vervaatTime f)}
  have hK : IsCompact K := (isClosed_le continuous_const
    (continuous_id.dist continuous_const)).isCompact
  by_cases hne : K.Nonempty
  · obtain ⟨q, hq, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne hK
      ((completedValue_lowerSemicontinuous f).lowerSemicontinuousOn K)
    have hlt : (⨅ s, f s) < min (Function.leftLim f q) (f q) := by
      refine lt_of_le_of_ne (iInf_le_completedValue f q) ?_
      intro heq
      have hqg := huniq q heq.symm
      have hbad : ε ≤ 0 := by simpa [K, hqg] using hq
      exact hε.not_ge hbad
    refine ⟨min (Function.leftLim f q) (f q) - (⨅ s, f s), sub_pos.mpr hlt, ?_⟩
    intro t ht
    have hle : min (Function.leftLim f q) (f q) ≤ min (Function.leftLim f t) (f t) :=
      hmin ht
    linarith
  · refine ⟨1, one_pos, ?_⟩
    intro t ht
    exact (hne ⟨t, ht⟩).elim

/-- The minimum time of the finite grid, excluding the duplicate terminal endpoint. -/
noncomputable def bridgeGridMinTime (M : ℕ) (f : D 1 ℝ) : Set.Icc (0 : ℝ) 1 :=
  gridTime M (bridgeGridMinIndex M f)

/-- The real finite-grid minimum time is measurable. -/
theorem measurable_bridgeGridMinTime (M : ℕ) :
    Measurable (fun f => (bridgeGridMinTime M f : ℝ)) := by
  exact (measurable_of_countable (fun i : Fin (M + 1) => (gridTime M i : ℝ))).comp
    (measurable_bridgeGridMinIndex M)

/-- Finite-grid minimum times converge at a unique continuous interior minimum. -/
theorem tendsto_bridgeGridMinTime {f : D 1 ℝ}
    (huniq : ∀ t : Icc (0 : ℝ) 1,
      min (Function.leftLim f t) (f t) = ⨅ s, f s → t = vervaatTime f)
    (hcont : ContinuousAt f (vervaatTime f)) (hg1 : (vervaatTime f : ℝ) < 1) :
    Tendsto (fun M => bridgeGridMinTime M f) atTop (𝓝 (vervaatTime f)) := by
  let g := vervaatTime f
  have hden (M : ℕ) : (0 : ℝ) < M + 1 := by positivity
  have hfloor (M : ℕ) : ⌊((M : ℝ) + 1) * (g : ℝ)⌋₊ < M + 1 := by
    apply (Nat.floor_lt (mul_nonneg (hden M).le g.2.1)).mpr
    push_cast
    exact mul_lt_of_lt_one_right (hden M) hg1
  let q (M : ℕ) : Fin (M + 1) := ⟨⌊((M : ℝ) + 1) * (g : ℝ)⌋₊, hfloor M⟩
  let u (M : ℕ) := gridTime M (q M)
  have hdist (M : ℕ) : dist (u M) g ≤ 1 / ((M : ℝ) + 1) := by
    rw [Subtype.dist_eq, Real.dist_eq]
    have hq : (u M : ℝ) = (⌊((M : ℝ) + 1) * (g : ℝ)⌋₊ : ℝ) / (M + 1) :=
      gridTime_coe M (q M) (by have := hfloor M; dsimp [q]; omega)
    rw [hq]
    have hlo := Nat.floor_le (mul_nonneg (hden M).le g.2.1)
    have hhi := Nat.lt_floor_add_one (((M : ℝ) + 1) * (g : ℝ))
    have hle : (⌊((M : ℝ) + 1) * (g : ℝ)⌋₊ : ℝ) / (M + 1) ≤ (g : ℝ) :=
      (div_le_iff₀ (hden M)).mpr (by nlinarith)
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    apply (le_div_iff₀ (hden M)).mpr
    have hcancel : ((⌊((M : ℝ) + 1) * (g : ℝ)⌋₊ : ℝ) / (M + 1)) * (M + 1) =
        (⌊((M : ℝ) + 1) * (g : ℝ)⌋₊ : ℝ) := div_mul_cancel₀ _ (hden M).ne'
    nlinarith
  have hu : Tendsto u atTop (𝓝 g) := by
    apply (tendsto_iff_dist_tendsto_zero).mpr
    exact squeeze_zero (fun _ => dist_nonneg) hdist
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hval : f g = ⨅ s, f s := by
    have hleft := hcont.continuousWithinAt.leftLim_eq
    simpa only [hleft, min_self] using min_leftLim_vervaatTime f
  have hfu : Tendsto (fun M => f (u M)) atTop (𝓝 (⨅ s, f s)) := by
    rw [← hval]
    exact hcont.tendsto.comp hu
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hgap⟩ := minimum_gap huniq hε
  have hev := (tendsto_order.mp hfu).2 ((⨅ s, f s) + δ) (by linarith)
  filter_upwards [hev] with M hM
  by_contra! hout
  have hnear := hgap (bridgeGridMinTime M f) hout
  have hmin : f (bridgeGridMinTime M f) ≤ f (u M) :=
    finiteMinIndex_le M (bridgeGridValues M f) (q M)
  exact (not_lt_of_ge (hnear.trans (min_le_right _ _))) (hmin.trans_lt hM)

/-- Under the stable bridge law, all finite-grid minimum times converge almost surely. -/
theorem stableBridgeLaw_ae_tendsto_bridgeGridMinTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)),
      Tendsto (fun M => (bridgeGridMinTime M f : ℝ)) atTop (𝓝 (vervaatTime f : ℝ)) := by
  filter_upwards [stableBridgeLaw_ae_minimum hθ] with f hf
  exact continuous_subtype_val.continuousAt.tendsto.comp
    (tendsto_bridgeGridMinTime hf.2.2.2 hf.2.2.1 hf.2.1.2)

end BGW.StableTrees
