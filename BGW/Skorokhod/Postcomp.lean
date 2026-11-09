/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Measurable
import BGW.Skorokhod.Continuous
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Basic.Real.Pointwise
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Postcomposition of càdlàg paths

Postcomposition by a continuous map preserves càdlàg paths. It is continuous for the J1 topology:
a convergent sequence of paths is eventually spatially close to the compact closure of the range
of its limit, where Heine--Cantor gives uniform control. In particular, postcomposition is Borel
measurable. A spatial `K`-Lipschitz map gives a J1 Lipschitz bound with constant `max K 1`; the
time-displacement part of J1 is not compressed when `K < 1`.
-/

@[expose] public section

open Set Filter Topology
open scoped NNReal

namespace BGW.Skorokhod

variable {T : ℝ} {E F G : Type*}

/-- Values along times converging from one side have a convergent subsequence in the closure of
the path range. -/
private theorem exists_subseq_tendsto_of_tendsto_time [MetricSpace E] (f : D T E)
    {u : ℕ → Set.Icc (0 : ℝ) T} {t : Set.Icc (0 : ℝ) T}
    (hu : Tendsto u atTop (𝓝 t)) :
    ∃ z ∈ closure (Set.range f), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => f (u (φ n))) atTop (𝓝 z) := by
  by_cases hright : ∃ᶠ n in atTop, t < u n
  · obtain ⟨φ, hφ, hside⟩ := extraction_of_frequently_atTop hright
    refine ⟨f t, subset_closure ⟨t, rfl⟩, φ, hφ, ?_⟩
    have htime : Tendsto (u ∘ φ) atTop (𝓝[>] t) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨hu.comp hφ.tendsto_atTop, Eventually.of_forall hside⟩
    exact (isCadlag f).isRightContinuous t |>.tendsto.comp htime
  have hle : ∀ᶠ n in atTop, u n ≤ t := by
    simpa only [not_frequently, not_lt] using hright
  by_cases hleft : ∃ᶠ n in atTop, u n < t
  · obtain ⟨φ, hφ, hside⟩ := extraction_of_frequently_atTop hleft
    have htime : Tendsto (u ∘ φ) atTop (𝓝[<] t) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨hu.comp hφ.tendsto_atTop, Eventually.of_forall hside⟩
    have hlim : Tendsto (fun n => f (u (φ n))) atTop (𝓝 (Function.leftLim f t)) :=
      (isCadlag f).tendsto_nhdsLT_leftLim t |>.comp htime
    refine ⟨Function.leftLim f t, ?_, φ, hφ, hlim⟩
    exact mem_closure_of_tendsto hlim (Eventually.of_forall fun n => ⟨u (φ n), rfl⟩)
  have heq : ∀ᶠ n in atTop, u n = t := by
    filter_upwards [hle, show ∀ᶠ n in atTop, ¬u n < t by
      simpa only [not_frequently] using hleft] with n htn hnt
    exact le_antisymm htn (le_of_not_gt hnt)
  refine ⟨f t, subset_closure ⟨t, rfl⟩, id, strictMono_id, ?_⟩
  exact tendsto_const_nhds.congr' (heq.mono fun n hn => by simp [hn])

/-- A càdlàg path on a nonempty compact interval has compact closed spatial range. -/
private theorem isCompact_closure_range [MetricSpace E] (f : D T E) :
    IsCompact (closure (Set.range f)) := by
  rw [isCompact_iff_isSeqCompact]
  intro x hx
  choose y hy hyx using fun n => Metric.mem_closure_iff.mp (hx n)
    ((n + 1 : ℝ)⁻¹) (by positivity)
  choose t ht using hy
  obtain ⟨_, _, φ, hφ, hts⟩ := isCompact_univ.isSeqCompact (fun n => Set.mem_univ (t n))
  obtain ⟨z, hz, ψ, hψ, hlim⟩ := exists_subseq_tendsto_of_tendsto_time f hts
  refine ⟨z, hz, φ ∘ ψ, hφ.comp hψ, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  have herr : Tendsto (fun n : ℕ => (n + 1 : ℝ)⁻¹) atTop (𝓝 0) :=
    by simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hxy : Tendsto (fun n => dist (x (φ (ψ n))) (f (t (φ (ψ n))))) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) (fun n => by
      simpa only [← ht] using (hyx (φ (ψ n))).le)
    exact herr.comp (hφ.comp hψ).tendsto_atTop
  have hyz : Tendsto (fun n => dist (f (t (φ (ψ n)))) z) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hlim
  apply squeeze_zero (fun _ => dist_nonneg) (fun n => dist_triangle _ _ _)
  simpa using hxy.add hyz

namespace D

/-- Postcompose a càdlàg path by a continuous map. -/
def postcomp [TopologicalSpace E] [TopologicalSpace F] (g : C(E, F)) : D T E → D T F :=
  fun f => ⟨fun t => g (f t), (isCadlag f).continuous_comp g.continuous⟩

/-- Postcomposition evaluates pointwise. -/
@[simp] theorem postcomp_apply [TopologicalSpace E] [TopologicalSpace F]
    (g : C(E, F)) (f : D T E) (t : Set.Icc (0 : ℝ) T) : postcomp g f t = g (f t) := rfl

/-- Postcomposition by the identity is the identity on càdlàg paths. -/
@[simp] theorem postcomp_id [TopologicalSpace E] (f : D T E) :
    postcomp (ContinuousMap.id E) f = f := by
  ext t
  rfl

/-- Postcomposition respects composition of continuous maps. -/
@[simp] theorem postcomp_comp [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
    (g : C(E, F)) (h : C(F, G)) (f : D T E) :
    postcomp (h.comp g) f = postcomp h (postcomp g f) := by
  ext t
  rfl

/-- Postcomposition by a continuous map is continuous for the Skorokhod J1 topology. -/
theorem continuous_postcomp [MetricSpace E] [MetricSpace F] (g : C(E, F)) :
    Continuous (postcomp (T := T) g) := by
  by_cases hT : 0 ≤ T
  · apply continuous_iff_seqContinuous.mpr
    intro u f hu
    obtain ⟨σ, hd, hp⟩ := tendsto_iff_exists_timeChange.mp hu
    apply tendsto_iff_exists_timeChange.mpr
    refine ⟨σ, hd, ?_⟩
    let K : Set E := closure (Set.range f)
    have hK : IsCompact K := isCompact_closure_range f
    have : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have huniform := hK.uniformContinuousAt_of_continuousAt g
      (fun _ _ => g.continuous.continuousAt) (Metric.dist_mem_uniformity (half_pos hε))
    obtain ⟨δ, hδ, hclose⟩ := Metric.mem_uniformity_dist.mp huniform
    have hev : ∀ᶠ n in atTop, (⨆ t, dist (u n (σ n t)) (f t)) < δ :=
      hp.eventually (gt_mem_nhds hδ)
    filter_upwards [hev] with n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (Real.iSup_nonneg fun t => dist_nonneg)]
    apply (ciSup_le ?_).trans_lt (half_lt_self hε)
    intro t
    have hdist : dist (f t) (u n (σ n t)) < δ := by
      rw [dist_comm]
      exact (le_ciSup (bddAbove_comp_dist hT (u n) f (σ n)) t).trans_lt hn
    have hfmem : f t ∈ K := subset_closure ⟨t, rfl⟩
    have := hclose hdist hfmem
    rw [dist_comm]
    exact this.le
  · have hneg : T < 0 := lt_of_not_ge hT
    have : IsEmpty (Set.Icc (0 : ℝ) T) :=
      ⟨fun t => (not_le_of_gt hneg) (le_trans t.property.1 t.property.2)⟩
    let _ : Subsingleton (D T E) := ⟨fun f g => by ext t; exact isEmptyElim t⟩
    apply continuous_iff_continuousAt.mpr
    intro f
    have heq : postcomp (T := T) g = fun _ => postcomp g f := by
      funext u
      rw [Subsingleton.elim u f]
    rw [heq]
    exact continuousAt_const

/-- Postcomposition is Borel measurable. -/
theorem measurable_postcomp [MetricSpace E] [MetricSpace F] (g : C(E, F)) :
    Measurable (postcomp (T := T) g) :=
  (continuous_postcomp g).measurable

end D

/-- A spatial Lipschitz map is J1 Lipschitz after postcomposition, with constant `max K 1`.
The `1` accounts for the unchanged time-displacement component of the J1 cost. -/
theorem D.lipschitzWith_postcomp [MetricSpace E] [MetricSpace F]
    {K : ℝ≥0} {g : C(E, F)} (hg : LipschitzWith K g) :
    LipschitzWith (max K 1) (D.postcomp (T := T) g) := by
  apply LipschitzWith.of_dist_le_mul
  intro f h
  change j1Dist (D.postcomp g f) (D.postcomp g h) ≤
    ((max K 1 : ℝ≥0) : ℝ) * j1Dist f h
  simp only [j1Dist]
  rw [Real.mul_iInf_of_nonneg (by positivity)]
  apply le_ciInf
  intro σ
  have hbdd : BddBelow (Set.range fun τ : TimeChange T =>
      max (⨆ t, |(τ t : ℝ) - t|)
        (⨆ t, dist (D.postcomp g f t) (D.postcomp g h (τ t)))) := by
    refine ⟨0, ?_⟩
    rintro x ⟨τ, rfl⟩
    exact le_max_of_le_right (Real.iSup_nonneg fun t => dist_nonneg)
  apply (ciInf_le hbdd σ).trans
  apply max_le
  · calc
        (⨆ t, |(σ t : ℝ) - t|) ≤
            1 * max (⨆ t, |(σ t : ℝ) - t|) (⨆ t, dist (f t) (h (σ t))) := by
          rw [one_mul]
          exact le_max_left _ _
        _ ≤ ((max K 1 : ℝ≥0) : ℝ) *
            max (⨆ t, |(σ t : ℝ) - t|) (⨆ t, dist (f t) (h (σ t))) := by
          apply mul_le_mul_of_nonneg_right _ (le_max_of_le_left
            (Real.iSup_nonneg fun t => abs_nonneg _))
          exact_mod_cast le_max_right K 1
  · calc
        (⨆ t, dist (g (f t)) (g (h (σ t)))) ≤
            (K : ℝ) * (⨆ t, dist (f t) (h (σ t))) := by
          refine Real.iSup_le ?_
            (mul_nonneg K.coe_nonneg (Real.iSup_nonneg fun t => dist_nonneg))
          intro t
          exact (hg.dist_le_mul _ _).trans
            (mul_le_mul_of_nonneg_left (le_ciSup (bddAbove_range_dist f h σ) t) K.coe_nonneg)
        _ ≤ ((max K 1 : ℝ≥0) : ℝ) *
            max (⨆ t, |(σ t : ℝ) - t|) (⨆ t, dist (f t) (h (σ t))) := by
          calc
            _ ≤ ((max K 1 : ℝ≥0) : ℝ) * (⨆ t, dist (f t) (h (σ t))) := by
              apply mul_le_mul_of_nonneg_right _ (Real.iSup_nonneg fun t => dist_nonneg)
              exact_mod_cast le_max_left K 1
            _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)

end BGW.Skorokhod
