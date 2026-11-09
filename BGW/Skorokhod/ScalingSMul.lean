/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Scaling
public import Mathlib.Topology.CompactOpen
import BGW.Skorokhod.ScalingTimeChange
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Module

/-!
# Time and real scalar space scaling of càdlàg paths

This is the normed-vector-space analogue of `timeSpaceScale`. Positive time scaling is clipped
at the terminal time, while the spatial coordinate is multiplied by a real scalar. The original
ring-multiplication API is unchanged.
-/

@[expose] public section

open Set Filter Topology

namespace BGW.Skorokhod

variable {T : ℝ} {E : Type*}

/-- Time–space scaling restricted to `[0,a]`: `t ↦ k * g (min (s * t) T)` for a spatial factor
`k` (coordinatewise for `E = Fin d → ℝ`) and a time factor `s > 0` (C6.4). -/
def timeSpaceScaleSMul [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (hT : 0 ≤ T) (p : D T E × ℝ × Set.Ioi (0 : ℝ)) :
    D a E where
  toFun t := p.2.1 • p.1 ⟨min (p.2.2 * t) T,
    le_min (mul_nonneg (le_of_lt p.2.2.2) t.2.1) hT, min_le_right _ _⟩
  isCadlag' := by
    let s : ℝ := p.2.2
    have hs : 0 < s := p.2.2.2
    let κ : Icc (0 : ℝ) a → Icc (0 : ℝ) T := fun t =>
      ⟨min (s * t) T, le_min (mul_nonneg hs.le t.2.1) hT, min_le_right _ _⟩
    have hκ : Continuous κ := Continuous.subtype_mk
      ((continuous_const.mul continuous_subtype_val).min continuous_const) _
    have hcad : IsCadlag (p.1 ∘ κ) := by
      constructor
      · intro t
        by_cases ht : s * (t : ℝ) < T
        · apply (isCadlag p.1).isRightContinuous (κ t) |>.comp
            hκ.continuousAt.continuousWithinAt
          intro u hu
          change (t : ℝ) < u at hu
          change min (s * (t : ℝ)) T < min (s * (u : ℝ)) T
          rw [min_eq_left ht.le]
          exact lt_min (mul_lt_mul_of_pos_left hu hs) ht
        · have heq (u : Icc (0 : ℝ) a) (hu : u ∈ Ioi t) : κ u = κ t := by
            apply Subtype.ext
            have htu : (t : ℝ) < u := hu
            change min (s * (u : ℝ)) T = min (s * (t : ℝ)) T
            rw [min_eq_right (le_of_not_gt ht),
              min_eq_right ((le_of_not_gt ht).trans
                (mul_le_mul_of_nonneg_left htu.le hs.le))]
          exact tendsto_nhdsWithin_congr
            (fun u hu => congrArg p.1 (heq u hu).symm) tendsto_const_nhds
      · intro t
        by_cases ht : s * (t : ℝ) ≤ T
        · obtain ⟨l, hl⟩ := (isCadlag p.1).tendsto_nhdsLT (κ t)
          refine ⟨l, hl.comp (tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩)⟩
          · exact tendsto_nhdsWithin_of_tendsto_nhds hκ.continuousAt
          · filter_upwards [self_mem_nhdsWithin] with u hu
            have hut : (u : ℝ) < t := hu
            change min (s * (u : ℝ)) T < min (s * (t : ℝ)) T
            rw [min_eq_left ht, min_eq_left
              ((mul_lt_mul_of_pos_left hut hs).le.trans ht)]
            exact mul_lt_mul_of_pos_left hut hs
        · have ht' : T < s * (t : ℝ) := lt_of_not_ge ht
          have hmem : ∀ᶠ u : Icc (0 : ℝ) a in 𝓝[<] t, T < s * (u : ℝ) :=
            (tendsto_nhdsWithin_of_tendsto_nhds
              ((continuous_const.mul continuous_subtype_val).continuousAt)).eventually
                (Ioi_mem_nhds ht')
          let top : Icc (0 : ℝ) T := ⟨T, hT, le_rfl⟩
          have heq : (p.1 ∘ κ) =ᶠ[𝓝[<] t] fun _ => p.1 top := by
            filter_upwards [hmem] with u hu
            apply congrArg p.1
            exact Subtype.ext (min_eq_right hu.le)
          exact ⟨p.1 top, (tendsto_congr' heq).2 tendsto_const_nhds⟩
    exact hcad.continuous_comp (continuous_const_smul p.2.1)


/-- Scalar multiplication of a càdlàg path by a fixed real number. -/
private def smulPath [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℝ) (f : D T E) : D T E :=
  ⟨fun t => k • f t, (isCadlag f).continuous_comp (continuous_const_smul k)⟩

/-- Real spatial factors tending to one preserve J1 convergence under scalar multiplication. -/
private theorem tendsto_smulPath_one [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} {l : Filter ι} (hT : 0 ≤ T)
    {u : ι → D T E} {f : D T E} {k : ι → ℝ}
    (hu : Tendsto u l (𝓝 f)) (hk : Tendsto k l (𝓝 1)) :
    Tendsto (fun i => smulPath (k i) (u i)) l (𝓝 f) := by
  have : Nonempty (Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
  let z : D T E := ⟨fun _ => 0, IsCadlag.const⟩
  obtain ⟨B, hB⟩ := bddAbove_range_dist f z (OrderIso.refl _)
  have hnorm (t : Icc (0 : ℝ) T) : ‖f t‖ ≤ B := by
    simpa [z, dist_zero_right] using hB ⟨t, rfl⟩
  obtain ⟨σ, hd, hp⟩ := tendsto_iff_exists_timeChange.mp hu
  apply tendsto_iff_exists_timeChange.mpr
  refine ⟨σ, hd, ?_⟩
  let e := fun i => ⨆ t, dist (u i (σ i t)) (f t)
  have hbound (i : ι) (t : Icc (0 : ℝ) T) :
      dist (smulPath (k i) (u i) (σ i t)) (f t) ≤
        ‖k i‖ * e i + ‖k i - 1‖ * B := by
    have halg : k i • u i (σ i t) - f t =
        k i • (u i (σ i t) - f t) + (k i - 1) • f t := by
      module
    change dist (k i • u i (σ i t)) (f t) ≤ _
    rw [dist_eq_norm, halg]
    calc
      _ ≤ ‖k i • (u i (σ i t) - f t)‖ + ‖(k i - 1) • f t‖ := norm_add_le _ _
      _ = ‖k i‖ * ‖u i (σ i t) - f t‖ + ‖k i - 1‖ * ‖f t‖ := by
        rw [norm_smul, norm_smul]
      _ ≤ ‖k i‖ * e i + ‖k i - 1‖ * B := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          simpa only [e, dist_eq_norm] using
            le_ciSup (bddAbove_comp_dist hT (u i) f (σ i)) t
        · exact mul_le_mul_of_nonneg_left (hnorm t) (norm_nonneg _)
  have hlim : Tendsto (fun i => ‖k i‖ * e i + ‖k i - 1‖ * B) l (𝓝 0) := by
    have h := (hk.norm.mul hp).add (((hk.sub_const 1).norm).mul_const B)
    simpa using h
  apply squeeze_zero _ (fun i => ciSup_le (hbound i)) hlim
  intro i
  exact le_ciSup_of_le (bddAbove_comp_dist hT (smulPath (k i) (u i)) f (σ i))
    ⟨0, le_rfl, hT⟩ dist_nonneg

/-- Time scaling followed by scalar multiplication at factor one is controlled by restriction. -/
private theorem tendsto_timeScaleSMul_one [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) (haT : a < T)
    {f : D T E} (hf : ContinuousAt f ⟨a, ha.le, haT.le⟩)
    {ι : Type*} {l : Filter ι} {u : ι → D T E} {s : ι → Ioi (0 : ℝ)}
    (hu : Tendsto u l (𝓝 f)) (hs : Tendsto (fun i => (s i : ℝ)) l (𝓝 1)) :
    Tendsto (fun i => timeSpaceScaleSMul a (ha.le.trans haT.le) (u i, 1, s i)) l
      (𝓝 (restrict haT.le f)) := by
  have : Nonempty (Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, ha.le.trans haT.le⟩⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨η, hη, hηrest⟩ :=
    (Metric.continuousAt_iff.mp (continuousAt_restrict ha.le haT.le hf)) ε hε
  have hγ := eventually_exists_timeChange_scale ha haT hs (show 0 < η / 4 by positivity)
  have hu' := Metric.tendsto_nhds.mp hu (η / 2) (by positivity)
  filter_upwards [hγ, hu'] with i hi hui
  obtain ⟨γ, hhead, hdisp⟩ := hi
  have hdist : dist (reparam (u i) γ) (u i) ≤ η / 4 :=
    (dist_reparam_le (ha.le.trans haT.le) (u i) γ).trans (ciSup_le hdisp)
  have hw : dist (reparam (u i) γ) f < η :=
    (dist_triangle _ _ _).trans_lt (by linarith)
  have heq : timeSpaceScaleSMul a (ha.le.trans haT.le) (u i, 1, s i) =
      restrict haT.le (reparam (u i) γ) := by
    apply ext
    intro t
    let tT : Icc (0 : ℝ) T := ⟨t, t.2.1, t.2.2.trans haT.le⟩
    have hh : (γ tT : ℝ) = (s i : ℝ) * t := hhead tT t.2.2
    have hb : (s i : ℝ) * t ≤ T := by rw [← hh]; exact (γ tT).2.2
    change (1 : ℝ) • u i _ = u i (γ tT)
    rw [one_smul]
    apply congrArg (u i)
    exact Subtype.ext (by simpa only [min_eq_left hb] using hh.symm)
  simpa only [heq] using hηrest hw

/-- Time–space scaling is continuous at `(f, 1, 1)` when `f` is continuous at `a < T`
(C6.4, the core of the source's Lemma 5.7). -/
theorem continuousAt_timeSpaceScaleSMul [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) (haT : a < T)
    {f : D T E} (hf : ContinuousAt f ⟨a, ha.le, haT.le⟩) :
    ContinuousAt (timeSpaceScaleSMul a (ha.le.trans haT.le))
      (f, 1, ⟨1, Set.mem_Ioi.mpr one_pos⟩) := by
  let p₀ : D T E × ℝ × Ioi (0 : ℝ) := (f, 1, ⟨1, one_pos⟩)
  have hu : Tendsto (fun p : D T E × ℝ × Ioi (0 : ℝ) => p.1) (𝓝 p₀) (𝓝 f) :=
    continuous_fst.continuousAt
  have hs : Tendsto (fun p : D T E × ℝ × Ioi (0 : ℝ) => (p.2.2 : ℝ))
      (𝓝 p₀) (𝓝 1) :=
    continuous_subtype_val.continuousAt.comp continuous_snd.snd.continuousAt
  have hk : Tendsto (fun p : D T E × ℝ × Ioi (0 : ℝ) => p.2.1)
      (𝓝 p₀) (𝓝 1) := continuous_snd.fst.continuousAt
  have hv := tendsto_timeScaleSMul_one ha haT hf hu hs
  have hm := tendsto_smulPath_one ha.le hv hk
  have heq : (fun p : D T E × ℝ × Ioi (0 : ℝ) =>
      smulPath p.2.1 (timeSpaceScaleSMul a (ha.le.trans haT.le) (p.1, 1, p.2.2))) =
      timeSpaceScaleSMul a (ha.le.trans haT.le) := by
    funext p
    apply ext
    intro t
    simp [smulPath, timeSpaceScaleSMul]
  rw [heq] at hm
  have hbase : timeSpaceScaleSMul a (ha.le.trans haT.le) p₀ = restrict haT.le f := by
    apply ext
    intro t
    change (1 : ℝ) • f _ = f _
    rw [one_smul]
    apply congrArg f
    apply Subtype.ext
    simp only [p₀, one_mul, min_eq_left (t.2.2.trans haT.le)]
  change Tendsto _ (𝓝 p₀) (𝓝 (timeSpaceScaleSMul a (ha.le.trans haT.le) p₀))
  rw [hbase]
  exact hm

/-- Time–space scaling of continuous paths with a real spatial factor. -/
def timeSpaceScaleSMulC [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℝ) (hT : 0 ≤ T)
    (p : C(Set.Icc (0 : ℝ) T, E) × ℝ × Set.Ioi (0 : ℝ)) :
    C(Set.Icc (0 : ℝ) a, E) where
  toFun t := p.2.1 • p.1 ⟨min (p.2.2 * t) T,
    le_min (mul_nonneg (le_of_lt p.2.2.2) t.2.1) hT, min_le_right _ _⟩
  continuous_toFun := by
    apply Continuous.const_smul _ p.2.1
    apply p.1.continuous.comp
    apply Continuous.subtype_mk
    fun_prop

/-- Time–space scaling with real spatial factors is continuous on continuous paths. -/
theorem continuous_timeSpaceScaleSMulC [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (hT : 0 ≤ T) : Continuous (timeSpaceScaleSMulC (E := E) a hT) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun q : (C(Set.Icc (0 : ℝ) T, E) × ℝ × Set.Ioi (0 : ℝ)) ×
    Set.Icc (0 : ℝ) a => q.1.2.1 • q.1.1 ⟨min (q.1.2.2 * q.2) T,
      le_min (mul_nonneg (le_of_lt q.1.2.2.2) q.2.2.1) hT, min_le_right _ _⟩)
  fun_prop

/-- On real-valued paths, real scalar spatial scaling agrees with ring multiplication. -/
@[simp] theorem timeSpaceScaleSMul_real (a : ℝ) (hT : 0 ≤ T)
    (p : D T ℝ × ℝ × Set.Ioi (0 : ℝ)) :
    timeSpaceScaleSMul a hT p = timeSpaceScale a hT p := by
  ext t
  exact smul_eq_mul _ _

end BGW.Skorokhod
