/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StablePassageSubordinator
public import BGW.Skorokhod.Vervaat
import BGW.Skorokhod.StepApprox

/-!
# Support of the Stieltjes measure of local time

The negative running infimum is constant on intervals where the path and its left limits stay
strictly above that infimum.  This is the deterministic input for the concentration of its
Stieltjes measure on the zero set of the reflected path (J. Bertoin, *Lévy Processes*, Cambridge
University Press, 1996, Chapter IV).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees

private lemma eventually_lt_min_leftLim_eval (f : DLoc) (u : ℝ≥0) {a : ℝ}
    (ha : a < min (Function.leftLim f.1 u) (f.1 u)) : ∀ᶠ v in 𝓝 u, a < f.1 v := by
  rw [← nhdsLT_sup_nhdsGE u, eventually_sup]
  constructor
  · exact (f.2.tendsto_nhdsLT_leftLim u).eventually (eventually_gt_nhds (lt_min_iff.mp ha).1)
  · have hge : ContinuousWithinAt f.1 (Ici u) u := by
      rw [ContinuousWithinAt, ← nhdsGT_sup_nhdsWithin_singleton u, tendsto_sup]
      exact ⟨f.2.isRightContinuous u,
        by simpa only [nhdsWithin_singleton] using tendsto_pure_nhds f.1 u⟩
    exact hge.eventually (eventually_gt_nhds (lt_min_iff.mp ha).2)

private lemma lowerSemicontinuous_min_leftLim_eval (f : DLoc) :
    LowerSemicontinuous (fun u => min (Function.leftLim f.1 u) (f.1 u)) := by
  intro u a ha
  obtain ⟨b, hab, hb⟩ := exists_between ha
  have he := eventually_lt_min_leftLim_eval f u hb
  have he' := eventually_eventually_nhds.mpr he
  filter_upwards [he, he'] with v hv hvn
  apply lt_min
  · apply hab.trans_le
    apply isClosed_Ici.mem_of_mapClusterPt
      ((mapClusterPt_leftLim f.1 v).mono nhdsWithin_le_nhds)
    exact hvn.mono fun _ h => h.le
  · exact hab.trans hv

private lemma runningInfLoc_const_of_gap (f : DLoc) {s t : ℝ≥0} (hst : s ≤ t)
    (h : ∀ u : ℝ≥0, s ≤ u → u ≤ t →
      runningInfLoc f u < f.1 u ∧ runningInfLoc f u < Function.leftLim f.1 u) :
    runningInfLoc f t = runningInfLoc f s := by
  let F : ℝ≥0 → ℝ := fun u => min (Function.leftLim f.1 u) (f.1 u)
  let m : ℝ := ⨅ u : Set.Icc s t, f.1 u
  let _ : Nonempty (Set.Icc s t) := ⟨⟨s, left_mem_Icc.mpr hst⟩⟩
  have hbm : BddBelow (Set.range (fun u : Set.Icc s t => f.1 u)) := by
    apply (bddBelow_runningInf_range f t).mono
    rintro _ ⟨u, rfl⟩
    exact ⟨⟨u, u.2.2⟩, rfl⟩
  have hdecomp : runningInfLoc f t = min (runningInfLoc f s) m := by
    apply le_antisymm
    · apply le_min
      · exact runningInfLoc_antitone f hst
      · apply le_ciInf
        intro u
        exact runningInfLoc_le_eval f t ⟨u, u.2.2⟩
    · apply le_runningInfLoc
      intro u
      rcases le_or_gt u.1 s with hus | hsu
      · exact (min_le_left _ _).trans (runningInfLoc_le_eval f s ⟨u, hus⟩)
      · have hsu' : s ≤ u.1 := hsu.le
        exact (min_le_right _ _).trans (ciInf_le hbm ⟨u, hsu', u.2⟩)
  have hcont : runningInfLoc f t ≤ runningInfLoc f s := runningInfLoc_antitone f hst
  apply le_antisymm hcont
  by_contra hlt
  have hlt' : runningInfLoc f t < runningInfLoc f s := lt_of_not_ge hlt
  have hlsc : LowerSemicontinuousOn F (Set.Icc s t) := by
    simpa only [F] using
      (lowerSemicontinuous_min_leftLim_eval f).lowerSemicontinuousOn (Set.Icc s t)
  obtain ⟨u, hu, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn
    (f := F) (s := Set.Icc s t) ⟨s, left_mem_Icc.mpr hst⟩ isCompact_Icc hlsc
  have hFm_le (v : Set.Icc s t) : F u ≤ f.1 v := by
    exact (hmin v.2).trans (min_le_right _ _)
  have hIm : m < runningInfLoc f s := by
    rw [hdecomp] at hlt'
    by_cases hms : runningInfLoc f s ≤ m
    · rw [min_eq_left hms] at hlt'
      exact (lt_irrefl _ hlt').elim
    · rw [min_eq_right (le_of_not_ge hms)] at hlt'
      exact hlt'
  have hsu : s < u.1 := by
    apply lt_of_le_of_ne hu.1
    intro hus
    have hFs : runningInfLoc f s < F s := lt_min (h s le_rfl hst).2 (h s le_rfl hst).1
    have hFum : F u ≤ m := le_ciInf fun v => hFm_le v
    rw [← hus] at hFum
    exact (not_lt_of_ge hFs.le) (hFum.trans_lt hIm)
  have hm_le : m ≤ F u := by
    by_cases huf : Function.leftLim f.1 u ≤ f.1 u
    · change m ≤ min (Function.leftLim f.1 u) (f.1 u)
      rw [min_eq_left huf]
      apply isClosed_Ici.mem_of_mapClusterPt
        (mapClusterPt_leftLim f.1 u)
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hsu)] with v hvu hvs
      exact ciInf_le hbm ⟨v, hvs.le, hvu.trans hu.2⟩
    · change m ≤ min (Function.leftLim f.1 u) (f.1 u)
      rw [min_eq_right (le_of_not_ge huf)]
      exact ciInf_le hbm ⟨u, hu⟩
  have hFm : F u = m := by
    apply le_antisymm
    · apply le_ciInf
      intro v
      exact hFm_le v
    · exact hm_le
  have huF : runningInfLoc f u < F u := lt_min (h u hu.1 hu.2).2 (h u hu.1 hu.2).1
  have hIt : runningInfLoc f t = m := by rw [hdecomp, min_eq_right hIm.le]
  rw [hFm, ← hIt] at huF
  exact (not_lt_of_ge (runningInfLoc_antitone f hu.2)) huF

/-- **Stieltjes measure of `L = -I` is carried by `{X = I}`**: a.s., on any interval `[s, t]`
on which both the path and its left limit stay strictly above the running infimum,
`L` is constant. -/
theorem ae_runningInf_const_off_zeroSet {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ s t : ℝ≥0, s ≤ t →
      (∀ u : ℝ≥0, s ≤ u → u ≤ t →
        runningInfLoc f u < f.1 u ∧ runningInfLoc f u < Function.leftLim f.1 u) →
      runningInfLoc f t = runningInfLoc f s := by
  have _hθ := hθ
  exact Filter.Eventually.of_forall fun f s t hst h => runningInfLoc_const_of_gap f hst h

private lemma isOpen_gap (f : DLoc) (hI : Continuous (runningInfLoc f)) :
    IsOpen {s : ℝ | runningInfLoc f s.toNNReal <
      min (Function.leftLim f.1 s.toNNReal) (f.1 s.toNNReal)} := by
  apply isOpen_iff_mem_nhds.mpr
  intro s hs
  obtain ⟨a, hIa, ha⟩ := exists_between hs
  have hpath := lowerSemicontinuous_min_leftLim_eval f s.toNNReal a ha
  have hinf := (hI.continuousAt (x := s.toNNReal)).eventually (eventually_lt_nhds hIa)
  have hto : ContinuousAt Real.toNNReal s := continuous_real_toNNReal.continuousAt
  filter_upwards [hto.eventually hinf, hto.eventually hpath] with r hrI hrF
  exact hrI.trans hrF

private lemma leftLim_restrict_pos {f : DLoc} {t T : ℝ≥0} (ht : 0 < t) (htT : t < T) :
    Function.leftLim (DLoc.restrict T f)
      ⟨t, t.2, (show (t : ℝ) ≤ (T : ℝ) from htT.le)⟩ = Function.leftLim f.1 t := by
  let t' : Set.Icc (0 : ℝ) (T : ℝ) := ⟨t, t.2, htT.le⟩
  let inc : Set.Icc (0 : ℝ) (T : ℝ) → ℝ≥0 := fun u => ⟨u, u.2.1⟩
  have hinc : Continuous inc := Continuous.subtype_mk continuous_subtype_val fun u => u.2.1
  have hleft : Tendsto inc (𝓝[<] t') (𝓝[<] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_nhdsWithin_of_tendsto_nhds hinc.continuousAt, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hu
  let z : Set.Icc (0 : ℝ) (T : ℝ) := ⟨0, le_rfl, T.2⟩
  have hz : z < t' := ht
  let _ : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  let _ : (𝓝[<] t').NeBot := nhdsLT_neBot_of_exists_lt ⟨z, hz⟩
  apply leftLim_eq_of_tendsto
  exact (f.2.tendsto_nhdsLT_leftLim t).comp hleft

private lemma pos_of_jump {f : DLoc} {s : ℝ}
    (hs : Function.leftLim f.1 s.toNNReal ≠ f.1 s.toNNReal) : 0 < s := by
  by_contra hn
  have hz : s.toNNReal = 0 := Real.toNNReal_of_nonpos (not_lt.mp hn)
  apply hs
  rw [hz, leftLim_eq_of_isBot isBot_zero]

private lemma countable_jumps (f : DLoc) :
    {s : ℝ | Function.leftLim f.1 s.toNNReal ≠ f.1 s.toNNReal}.Countable := by
  let J : ℕ → Set ℝ := fun n => {s | s.toNNReal ≤ (n : ℝ≥0) ∧
    Function.leftLim f.1 s.toNNReal ≠ f.1 s.toNNReal}
  have hJ (n : ℕ) : (J n).Countable := by
    let T : ℝ≥0 := n + 1
    let K := {u : Set.Icc (0 : ℝ) (T : ℝ) |
      Function.leftLim (DLoc.restrict T f) u ≠ (DLoc.restrict T f) u}
    let φ : ℝ → ℝ := fun s => (s.toNNReal : ℝ)
    let TK : Set ℝ := Set.image (fun u : Set.Icc (0 : ℝ) (T : ℝ) => (u : ℝ)) K
    apply MapsTo.countable_of_injOn (s := J n) (t := TK) (f := φ)
    · intro s hs
      have hspos : 0 < s.toNNReal := by
        apply pos_iff_ne_zero.mpr
        intro hz
        apply hs.2
        rw [hz, leftLim_eq_of_isBot isBot_zero]
      have hsT : s.toNNReal < T := by
        exact hs.1.trans_lt (show (n : ℝ≥0) < T by simp [T])
      let u : Set.Icc (0 : ℝ) (T : ℝ) :=
        ⟨s.toNNReal, hspos.le, by exact_mod_cast hsT.le⟩
      refine ⟨u, ?_, rfl⟩
      change Function.leftLim (DLoc.restrict T f) u ≠ (DLoc.restrict T f) u
      rw [leftLim_restrict_pos hspos hsT]
      exact hs.2
    · intro s hs r hr heq
      have hspos : 0 < s := pos_of_jump hs.2
      have hrpos : 0 < r := pos_of_jump hr.2
      apply (Real.toNNReal_eq_toNNReal_iff hspos.le hrpos.le).mp
      change (s.toNNReal : ℝ) = (r.toNNReal : ℝ) at heq
      exact_mod_cast heq
    · have hc := countable_setOf_jump_ne (DLoc.restrict T f)
      exact hc.image (fun u : Set.Icc (0 : ℝ) (T : ℝ) => (u : ℝ))
  have hcover : {s : ℝ | Function.leftLim f.1 s.toNNReal ≠ f.1 s.toNNReal} = ⋃ n, J n := by
    ext s
    constructor
    · intro hs
      have hspos : 0 < s := pos_of_jump hs
      have hn : s.toNNReal ≤ (⌈s⌉₊ : ℝ≥0) := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hspos.le]
        exact_mod_cast Nat.le_ceil s
      exact mem_iUnion.mpr ⟨⌈s⌉₊, hn, hs⟩
    · intro hs
      obtain ⟨n, hn, hs⟩ := mem_iUnion.mp hs
      exact hs
  rw [hcover]
  exact countable_iUnion hJ

private lemma localTimeStieltjes_apply (f : DLoc) (h : Monotone (localTime f) ∧
    Continuous (localTime f)) (s : ℝ) : localTimeStieltjes f s = localTime f s.toNNReal := by
  simp [localTimeStieltjes, h]

private lemma localTimeStieltjes_continuous (f : DLoc) (h : Monotone (localTime f) ∧
    Continuous (localTime f)) : Continuous (localTimeStieltjes f) := by
  have heq : (fun s : ℝ => localTimeStieltjes f s) = fun s => localTime f s.toNNReal := by
    funext s
    exact localTimeStieltjes_apply f h s
  change Continuous (fun s : ℝ => localTimeStieltjes f s)
  rw [heq]
  exact h.2.comp continuous_real_toNNReal

private lemma measure_Ioo_of_gap (f : DLoc) (h : Monotone (localTime f) ∧
    Continuous (localTime f)) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hsub : Set.Ioo a b ⊆ {s : ℝ | runningInfLoc f s.toNNReal <
      min (Function.leftLim f.1 s.toNNReal) (f.1 s.toNNReal)}) :
    (localTimeStieltjes f).measure (Set.Ioo a b) = 0 := by
  let G := localTimeStieltjes f
  have hG := localTimeStieltjes_apply f h
  have hGc := localTimeStieltjes_continuous f h
  have hconst {x y : ℝ} (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b) : G x = G y := by
    wlog hxy : x ≤ y generalizing x y
    · exact (this hy hx (le_of_not_ge hxy)).symm
    have hx0 : 0 ≤ x := ha.trans hx.1.le
    have hy0 : 0 ≤ y := ha.trans hy.1.le
    rw [hG, hG]
    apply congrArg Neg.neg
    symm
    apply runningInfLoc_const_of_gap f (Real.toNNReal_mono hxy)
    intro u hxu hyu
    have hu : (u : ℝ) ∈ Set.Ioo a b := by
      constructor
      · have hcast : (x.toNNReal : ℝ) ≤ (u : ℝ) := by exact_mod_cast hxu
        rw [Real.coe_toNNReal _ hx0] at hcast
        exact hx.1.trans_le hcast
      · have hcast : (u : ℝ) ≤ (y.toNNReal : ℝ) := by exact_mod_cast hyu
        rw [Real.coe_toNNReal _ hy0] at hcast
        exact hcast.trans_lt hy.2
    have hgap := hsub hu
    have hgap' : runningInfLoc f u < min (Function.leftLim f.1 u) (f.1 u) := by
      simpa only [Set.mem_ofPred_eq, Real.toNNReal_coe] using hgap
    exact ⟨hgap'.trans_le (min_le_right _ _), hgap'.trans_le (min_le_left _ _)⟩
  let c : ℝ := (a + b) / 2
  have hc : c ∈ Set.Ioo a b := ⟨by dsimp [c]; linarith, by dsimp [c]; linarith⟩
  have hGa : G a = G c := by
    refine tendsto_nhds_unique' (nhdsGT_neBot_of_exists_gt ⟨b, hab⟩)
      ((hGc.continuousAt (x := a)).tendsto.mono_left nhdsWithin_le_nhds) ?_
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT hab] with x hx
    exact hconst hc hx
  have hGb : G b = G c := by
    refine tendsto_nhds_unique' (nhdsLT_neBot_of_exists_lt ⟨a, hab⟩)
      ((hGc.continuousAt (x := b)).tendsto.mono_left nhdsWithin_le_nhds) ?_
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT hab] with x hx
    exact (hconst hx hc).symm
  rw [StieltjesFunction.measure_Ioo, hGc.continuousAt.continuousWithinAt.leftLim_eq, hGa, hGb,
    sub_self, ENNReal.ofReal_zero]

/-- **Stieltjes measure of `L` is carried by `{X = I}`**: almost surely `dL {t | X_t ≠ I_t} = 0`
(`{X > I}` is the union of an open set on which `L` is constant and the countable set of jump
times; `L` is continuous so has no atoms). Negative `s` are harmless: `X_0 = I_0 = 0`. -/
theorem ae_localTimeStieltjes_measure_ne_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (localTimeStieltjes f).measure {s : ℝ | f.1 s.toNNReal ≠ runningInfLoc f s.toNNReal} = 0 := by
  filter_upwards [ae_firstPassageBelow_spec hθ,
    ae_runningInf_continuous_antitone_tendsto hθ, ae_localTime_spec hθ] with f hf hI hL
  let G := localTimeStieltjes f
  let V : Set ℝ := {s : ℝ | runningInfLoc f s.toNNReal <
    min (Function.leftLim f.1 s.toNNReal) (f.1 s.toNNReal)}
  let J : Set ℝ := {s : ℝ | Function.leftLim f.1 s.toNNReal ≠ f.1 s.toNNReal}
  let Q := {p : ℚ × ℚ // 0 ≤ p.1 ∧ p.1 < p.2 ∧
    Set.Ioo (p.1 : ℝ) (p.2 : ℝ) ⊆ V}
  let U : Set ℝ := ⋃ p : Q, Set.Ioo (p.1.1 : ℝ) (p.1.2 : ℝ)
  have hLc : Monotone (localTime f) ∧ Continuous (localTime f) := ⟨hL.2.1, hL.2.2.1⟩
  have hGc := localTimeStieltjes_continuous f hLc
  let _ : NullSingletonClass G.measure := ⟨fun s => by
    rw [StieltjesFunction.measure_singleton, hGc.continuousAt.continuousWithinAt.leftLim_eq,
      sub_self, ENNReal.ofReal_zero]⟩
  have hU0 : G.measure U = 0 := by
    apply measure_iUnion_null
    intro p
    apply measure_Ioo_of_gap f hLc (a := (p.1.1 : ℝ)) (b := (p.1.2 : ℝ))
    · exact_mod_cast p.2.1
    · exact_mod_cast p.2.2.1
    · exact p.2.2.2
  have hJ0 : G.measure J = 0 := (countable_jumps f).measure_zero _
  apply measure_mono_null (t := U ∪ J) ?_ (measure_union_null hU0 hJ0)
  intro s hs
  by_cases hsJ : s ∈ J
  · exact Or.inr hsJ
  have hspos : 0 < s := by
    by_contra hn
    have hz : s.toNNReal = 0 := Real.toNNReal_of_nonpos (not_lt.mp hn)
    have hI0 : runningInfLoc f 0 = 0 := by
      have h0 := hL.1
      rw [localTime] at h0
      linarith
    apply hs
    simp only [hz, hf.1, hI0]
  have hsV : s ∈ V := by
    have hlt : runningInfLoc f s.toNNReal < f.1 s.toNNReal :=
      lt_of_le_of_ne (runningInfLoc_le_eval f s.toNNReal ⟨s.toNNReal, by simp⟩) hs.symm
    have heq : Function.leftLim f.1 s.toNNReal = f.1 s.toNNReal := by
      simpa only [J, Set.mem_ofPred_eq, not_not] using hsJ
    have hlt' : runningInfLoc f s.toNNReal < Function.leftLim f.1 s.toNNReal := by
      rw [heq]
      exact hlt
    exact lt_min hlt' hlt
  obtain ⟨a, b, hsab, habV⟩ :=
    (mem_nhds_iff_exists_Ioo_subset).mp ((isOpen_gap f hI.1).mem_nhds hsV)
  obtain ⟨q, hq, hqs⟩ := exists_rat_btwn (max_lt hsab.1 hspos)
  obtain ⟨r, hsr, hrb⟩ := exists_rat_btwn hsab.2
  have hq0 : 0 ≤ q := by exact_mod_cast (le_max_right a 0).trans hq.le
  have hqr : q < r := by exact_mod_cast hqs.trans hsr
  have hsub : Set.Ioo (q : ℝ) (r : ℝ) ⊆ V := by
    apply subset_trans _ habV
    exact Set.Ioo_subset_Ioo (le_trans (le_max_left a 0) hq.le) hrb.le
  refine Or.inl (mem_iUnion.mpr ⟨⟨(q, r), hq0, hqr, hsub⟩, hqs, hsr⟩)

end BGW.StableTrees
