/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.ContinuumTrees.BrownianBridgeMinimum
public import BGW.ContinuumTrees.BrownianBridgeGrid
public import BGW.ContinuumTrees.VervaatBridge

import Mathlib.Tactic.Positivity

/-!
# Unique minimum of the Brownian bridge

A countable collection of deterministic comparisons between interval minima rules out two
distinct global minimizers almost surely. Since the global minimum is negative and the bridge
vanishes at its endpoints, the unique minimizer is interior. Rotating at that minimizer in the
Vervaat construction consequently gives a path strictly positive on the open unit interval.

The probabilistic input is
`BrownianBridge.measure_prefixMin_eq_intervalMin` (Kim–Pollard regression), applied to rational
interval endpoints, together with `BrownianBridge.ae_intervalMin_neg`; see Vervaat (1979) and
Le Gall, *Random trees and applications* (2005), §2, for the classical statement.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace BGW.ContinuumTrees.BrownianBridge

private def timeOfRat (q : Set.Icc (0 : ℚ) 1) : unitInterval :=
  ⟨(q : ℝ), by exact_mod_cast q.property.1, by exact_mod_cast q.property.2⟩

@[simp] private theorem coe_timeOfRat (q : Set.Icc (0 : ℚ) 1) :
    (timeOfRat q : ℝ) = (q : ℝ) := rfl

private theorem ae_rational_intervalMin_ne :
    ∀ᵐ f ∂(law : Measure C(unitInterval, ℝ)), ∀ b c d : Set.Icc (0 : ℚ) 1,
      (b : ℝ) < c → (c : ℝ) ≤ d → (d : ℝ) < 1 →
      Coding.intervalMin f 0 (timeOfRat b) ≠ Coding.intervalMin f (timeOfRat c) (timeOfRat d) := by
  have hne (b c d : Set.Icc (0 : ℚ) 1) :
      ∀ᵐ f ∂(law : Measure C(unitInterval, ℝ)),
        (b : ℝ) < c → (c : ℝ) ≤ d → (d : ℝ) < 1 →
        Coding.intervalMin f 0 (timeOfRat b) ≠
          Coding.intervalMin f (timeOfRat c) (timeOfRat d) := by
    by_cases hbc : (b : ℝ) < c
    · by_cases hcd : (c : ℝ) ≤ d
      · by_cases hd : (d : ℝ) < 1
        · have hzero := measure_prefixMin_eq_intervalMin (timeOfRat b) (timeOfRat c)
            (timeOfRat d) hbc hcd hd
          filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with f hf
          intro _ _ _ heq
          exact hf heq
        · exact ae_of_all _ fun _ _ _ hd' => (hd hd').elim
      · exact ae_of_all _ fun _ _ hcd' => (hcd hcd').elim
    · exact ae_of_all _ fun _ hbc' => (hbc hbc').elim
  filter_upwards [ae_all_iff.mpr fun b => ae_all_iff.mpr fun c =>
    ae_all_iff.mpr fun d => hne b c d] with f hf
  exact hf

private theorem isMin_mem_Ioo (f : C(unitInterval, ℝ)) (h0 : f 0 = 0) (h1 : f 1 = 0)
    (hneg : Coding.intervalMin f 0 1 < 0) {t : unitInterval} (ht : ∀ s, f t ≤ f s) :
    0 < (t : ℝ) ∧ (t : ℝ) < 1 := by
  obtain ⟨r, _, hr⟩ := Coding.exists_intervalMin f 0 1
  have hrneg : f r < 0 := by rw [← hr]; exact hneg
  have htneg : f t < 0 := (ht r).trans_lt hrneg
  have ht0 : t ≠ 0 := by
    intro h
    subst t
    rw [h0] at htneg
    exact (lt_irrefl 0 htneg).elim
  have ht1 : t ≠ 1 := by
    intro h
    subst t
    rw [h1] at htneg
    exact (lt_irrefl 0 htneg).elim
  exact ⟨(unitInterval.nonneg t).lt_of_ne' (unitInterval.coe_ne_zero.mpr ht0),
    (unitInterval.le_one t).lt_of_ne (unitInterval.coe_ne_one.mpr ht1)⟩

private theorem not_two_isMin (f : C(unitInterval, ℝ))
    (hf : ∀ b c d : Set.Icc (0 : ℚ) 1,
      (b : ℝ) < c → (c : ℝ) ≤ d → (d : ℝ) < 1 →
      Coding.intervalMin f 0 (timeOfRat b) ≠ Coding.intervalMin f (timeOfRat c) (timeOfRat d))
    (h0 : f 0 = 0) (h1 : f 1 = 0) (hneg : Coding.intervalMin f 0 1 < 0)
    {s t : unitInterval} (hst : s < t) (hs : ∀ u, f s ≤ f u) (ht : ∀ u, f t ≤ f u) : False := by
  obtain ⟨hs0, hs1⟩ := isMin_mem_Ioo f h0 h1 hneg hs
  obtain ⟨ht0, ht1⟩ := isMin_mem_Ioo f h0 h1 hneg ht
  obtain ⟨b, hsb, hbt⟩ := exists_rat_btwn (show (s : ℝ) < t from hst)
  obtain ⟨c, hbc, hct⟩ := exists_rat_btwn hbt
  obtain ⟨d, htd, hd1⟩ := exists_rat_btwn ht1
  have hb0 : (0 : ℝ) < b := hs0.trans hsb
  have hb1 : (b : ℝ) < 1 := hbt.trans ht1
  have hc0 : (0 : ℝ) < c := hb0.trans hbc
  have hc1 : (c : ℝ) < 1 := hct.trans ht1
  have hd0 : (0 : ℝ) < d := ht0.trans htd
  let b' : Set.Icc (0 : ℚ) 1 := ⟨b, by exact_mod_cast hb0.le, by exact_mod_cast hb1.le⟩
  let c' : Set.Icc (0 : ℚ) 1 := ⟨c, by exact_mod_cast hc0.le, by exact_mod_cast hc1.le⟩
  let d' : Set.Icc (0 : ℚ) 1 := ⟨d, by exact_mod_cast hd0.le, by exact_mod_cast hd1.le⟩
  have hleft : Coding.intervalMin f 0 (timeOfRat b') = f s := by
    apply le_antisymm
    · apply Coding.intervalMin_le
      rw [Set.uIcc_of_le (show (0 : unitInterval) ≤ timeOfRat b' from unitInterval.nonneg')]
      exact ⟨unitInterval.nonneg', hsb.le⟩
    · exact Coding.le_intervalMin f 0 (timeOfRat b') fun u _ => hs u
  have hcd : timeOfRat c' ≤ timeOfRat d' := hct.le.trans htd.le
  have hright : Coding.intervalMin f (timeOfRat c') (timeOfRat d') = f t := by
    apply le_antisymm
    · apply Coding.intervalMin_le
      rw [Set.uIcc_of_le hcd]
      exact ⟨hct.le, htd.le⟩
    · exact Coding.le_intervalMin f (timeOfRat c') (timeOfRat d') fun u _ => ht u
  apply hf b' c' d' hbc (hct.le.trans htd.le) hd1
  rw [hleft, hright]
  exact le_antisymm (hs t) (ht s)

/-- Almost surely, the Brownian bridge attains its global minimum at exactly one time. -/
theorem ae_existsUnique_isMin :
    ∀ᵐ f ∂(law : Measure C(unitInterval, ℝ)), ∃! t : unitInterval, ∀ s, f t ≤ f s := by
  filter_upwards [ae_intervalMin_neg, ae_endpoints, ae_rational_intervalMin_ne] with f hneg he hf
  obtain ⟨r, _, hr⟩ := Coding.exists_intervalMin f 0 1
  have hrmin : ∀ s, f r ≤ f s := by
    intro s
    rw [← hr]
    exact Coding.intervalMin_le f 0 1
      (by simp only [Set.uIcc_of_le (show (0 : unitInterval) ≤ 1 from zero_le_one),
        Set.mem_Icc]; exact ⟨bot_le, le_top⟩)
  refine ⟨r, hrmin, fun t ht => ?_⟩
  by_contra htr
  rcases lt_or_gt_of_ne htr with hrt | htr
  · exact not_two_isMin f hf he.1 he.2 hneg hrt ht hrmin
  · exact not_two_isMin f hf he.1 he.2 hneg htr hrmin ht

/-- Almost surely, the first (hence unique) minimum time lies in the open interval `(0,1)`. -/
theorem ae_firstMinimum_mem_Ioo :
    ∀ᵐ f ∂(law : Measure C(unitInterval, ℝ)),
      0 < (Vervaat.firstMinimum f : ℝ) ∧ (Vervaat.firstMinimum f : ℝ) < 1 := by
  filter_upwards [ae_intervalMin_neg, ae_endpoints] with f hneg he
  apply isMin_mem_Ioo f he.1 he.2 hneg
  intro s
  rw [(Vervaat.isLeast_firstMinimum f).1]
  exact Coding.intervalMin_le f 0 1
    (by simp only [Set.uIcc_of_le (show (0 : unitInterval) ≤ 1 from zero_le_one),
      Set.mem_Icc]; exact ⟨bot_le, le_top⟩)

end BrownianBridge

namespace VervaatBridge

private theorem circularShift_ne (m t : unitInterval)
    (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) : Coding.circularShift m t ≠ m := by
  intro h
  have hfract : Int.fract ((m : ℝ) + t) = (m : ℝ) := congrArg Subtype.val h
  obtain ⟨-, -, z, hz⟩ := Int.fract_eq_iff.mp hfract
  have htz : (t : ℝ) = (z : ℝ) := by linarith
  rw [htz] at ht0 ht1
  have hz0 : (0 : ℤ) < z := by exact_mod_cast ht0
  have hz1 : z < 1 := by exact_mod_cast ht1
  omega

/-- Almost surely, the Vervaat transform of the anchored bridge is strictly positive on `(0,1)`. -/
theorem ae_path_pos :
    ∀ᵐ ω ∂gaussianLimit, ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < path ω t := by
  have hu : ∀ᵐ ω ∂gaussianLimit,
      ∃! t : unitInterval, ∀ s, BrownianBridge.path ω t ≤ BrownianBridge.path ω s := by
    exact ae_of_ae_map BrownianBridge.measurable_path.aemeasurable
      (p := fun f => ∃! t : unitInterval, ∀ s, f t ≤ f s) (by
        simpa only [← BrownianBridge.coe_law] using BrownianBridge.ae_existsUnique_isMin)
  have hi : ∀ᵐ ω ∂gaussianLimit,
      0 < (Vervaat.firstMinimum (BrownianBridge.path ω) : ℝ) ∧
        (Vervaat.firstMinimum (BrownianBridge.path ω) : ℝ) < 1 := by
    exact ae_of_ae_map BrownianBridge.measurable_path.aemeasurable
      (p := fun f => 0 < (Vervaat.firstMinimum f : ℝ) ∧
        (Vervaat.firstMinimum f : ℝ) < 1) (by
        simpa only [← BrownianBridge.coe_law] using BrownianBridge.ae_firstMinimum_mem_Ioo)
  filter_upwards [hu, hi] with ω hu hi t ht0 ht1
  let f := BrownianBridge.path ω
  let m := Vervaat.firstMinimum f
  have hm : ∀ s, f m ≤ f s := by
    intro s
    rw [(Vervaat.isLeast_firstMinimum f).1]
    exact Coding.intervalMin_le f 0 1
      (by simp only [Set.uIcc_of_le (show (0 : unitInterval) ≤ 1 from zero_le_one),
        Set.mem_Icc]; exact ⟨bot_le, le_top⟩)
  have hshift : Coding.circularShift m t ≠ m := circularShift_ne m t ht0 ht1
  have hlt : f m < f (Coding.circularShift m t) := by
    apply (hm _).lt_of_ne
    intro heq
    apply hshift
    apply hu.unique
    · intro s
      rw [← heq]
      exact hm s
    · exact hm
  change 0 < f (Coding.circularShift m t) - Coding.intervalMin f 0 1
  rw [← (Vervaat.isLeast_firstMinimum f).1]
  exact sub_pos.mpr hlt

private noncomputable def innerLeft (n : ℕ) : unitInterval :=
  ⟨1 / (n + 3 : ℝ), unitInterval.div_mem zero_le_one (by positivity) (by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)⟩

@[simp] private theorem coe_innerLeft (n : ℕ) : (innerLeft n : ℝ) = 1 / (n + 3 : ℝ) := rfl

private theorem continuous_intervalMin (a b : unitInterval) :
    Continuous (fun f : C(unitInterval, ℝ) => Coding.intervalMin f a b) := by
  exact (isCompact_uIcc : IsCompact (uIcc a b)).continuous_sInf
    (f := fun f : C(unitInterval, ℝ) => fun t => f t) continuous_eval

private theorem isClosed_exists_nonpos (a b : unitInterval) :
    IsClosed {f : C(unitInterval, ℝ) | ∃ t ∈ uIcc a b, f t ≤ 0} := by
  have hset : {f : C(unitInterval, ℝ) | ∃ t ∈ uIcc a b, f t ≤ 0} =
      {f | Coding.intervalMin f a b ≤ 0} := by
    ext f
    constructor
    · rintro ⟨t, ht, hft⟩
      exact (Coding.intervalMin_le f a b ht).trans hft
    · intro hf
      obtain ⟨t, ht, heq⟩ := Coding.exists_intervalMin f a b
      exact ⟨t, ht, heq ▸ hf⟩
  rw [hset]
  exact isClosed_le (continuous_intervalMin a b) continuous_const

private theorem measurableSet_interior_pos :
    MeasurableSet {f : C(unitInterval, ℝ) |
      ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < f t} := by
  have hleft_right (n : ℕ) : innerLeft n ≤ unitInterval.symm (innerLeft n) := by
    change 1 / (n + 3 : ℝ) ≤ 1 - 1 / (n + 3 : ℝ)
    have hn : (0 : ℝ) < n + 3 := by positivity
    have hle : 1 / (n + 3 : ℝ) ≤ 1 / 2 := by
      exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (by
        exact_mod_cast (show 2 ≤ n + 3 by omega))
    linarith
  have hcompl : {f : C(unitInterval, ℝ) |
      ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < f t}ᶜ =
      ⋃ n : ℕ, {f | ∃ t ∈ uIcc (innerLeft n) (unitInterval.symm (innerLeft n)), f t ≤ 0} := by
    ext f
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hf
      push Not at hf
      obtain ⟨t, ht0, ht1, hft⟩ := hf
      have hmin : 0 < min (t : ℝ) (1 - t) := lt_min ht0 (sub_pos.mpr ht1)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hmin
      refine ⟨n + 2, t, ?_, hft⟩
      rw [Set.uIcc_of_le (hleft_right (n + 2))]
      have hsmall : 1 / ((n + 2 : ℕ) + 3 : ℝ) < min (t : ℝ) (1 - t) := by
        apply lt_trans _ hn
        apply one_div_lt_one_div_of_lt (by positivity)
        exact_mod_cast (show n + 1 < n + 2 + 3 by omega)
      change 1 / (((n + 2 : ℕ) : ℝ) + 3) ≤ (t : ℝ) ∧
        (t : ℝ) ≤ 1 - 1 / (((n + 2 : ℕ) : ℝ) + 3)
      exact ⟨(hsmall.trans_le (min_le_left _ _)).le,
        by have h := (hsmall.trans_le (min_le_right _ _)).le; linarith⟩
    · rintro ⟨n, t, ht, hft⟩ hf
      rw [Set.uIcc_of_le (hleft_right n)] at ht
      have hn : 0 < (innerLeft n : ℝ) := by simp; positivity
      have ht1' : (t : ℝ) < 1 := by
        have ht2 : (t : ℝ) ≤ 1 - (innerLeft n : ℝ) := ht.2
        rw [coe_innerLeft] at ht2
        have hn' : 0 < 1 / (n + 3 : ℝ) := by positivity
        linarith
      exact (not_le_of_gt (hf t (hn.trans_le ht.1) ht1')) hft
  rw [← MeasurableSet.compl_iff, hcompl]
  exact MeasurableSet.iUnion fun n => (isClosed_exists_nonpos _ _).measurableSet

/-- The Vervaat path law is carried by paths strictly positive on `(0,1)`. -/
theorem ae_law_pos :
    ∀ᵐ f ∂(law : Measure C(unitInterval, ℝ)),
      ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < f t := by
  rw [coe_law, ae_map_iff measurable_path.aemeasurable measurableSet_interior_pos]
  exact ae_path_pos

end BGW.ContinuumTrees.VervaatBridge
