/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.UnpaddedContourClock

import BGW.StableTrees.DiscreteHeightApproxCutoff
import BGW.StableTrees.HeightTightnessUniformModulus

/-!
# Comparison of the padded and unpadded forest contours

The walk maximum bounds the number of completed trees on a fixed contour
horizon.  The height modulus and the sealed contour/height comparison then
control the small clock shift uniformly.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.StableTrees

namespace BGW.StableTrees.ForestContour

open BGW.StableTrees.DiscreteForest BGW.PlaneTree
open BGW.StableTrees.HeightTightness BGW.Probability.RealWalk
open BGW.StableTrees.DiscreteHeightApprox

private theorem unpaddedBlock_le_of_walk_bound {ω : ℕ → ℕ} (hω : LadderFinite ω)
    {n : ℕ} (hn : 0 < n) {T K b : ℝ} (hK : 0 < K) (hb : 0 < b) (hbn : K * b < n)
    (hwalk : ∀ u ≤ ⌊n * (T + 1)⌋₊, |(walk ω u : ℝ)| ≤ K * b)
    (t : Set.Icc (0 : ℝ) T) :
    (unpaddedBlock ω ⌊2 * (n : ℝ) * (t : ℝ)⌋₊ : ℝ) ≤ K * b := by
  let m := ⌊2 * (n : ℝ) * (t : ℝ)⌋₊
  let r := unpaddedBlock ω m
  let R := ⌊K * b⌋₊ + 1
  have hKb : 0 ≤ K * b := mul_nonneg hK.le hb.le
  have hRn : R ≤ n := by
    apply Nat.succ_le_of_lt
    exact (Nat.floor_lt hKb).mpr hbn
  have hrR : r < R := by
    by_contra! hRr
    have hstartR : unpaddedStart ω R ≤ m := by
      apply (monotone_unpaddedStart hω hRr).trans
      exact unpaddedBlock_start (ω := ω) m
    have hm : (m : ℝ) ≤ 2 * (n : ℝ) * T := by
      apply (Nat.floor_le (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) t.2.1)).trans
      exact mul_le_mul_of_nonneg_left t.2.2 (by positivity)
    have hstartR' : (unpaddedStart ω R : ℝ) ≤ 2 * (n : ℝ) * T := by
      exact (Nat.cast_le.mpr hstartR).trans hm
    have hclockR : 2 * (ladderTime ω R : ℝ) =
        (unpaddedStart ω R : ℝ) + 2 * (R : ℝ) := by
      exact_mod_cast two_mul_ladderTime_eq_unpaddedStart hω R
    have htime : (ladderTime ω R : ℝ) ≤ (n : ℝ) * (T + 1) := by
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      have hTR : (R : ℝ) ≤ (n : ℝ) := by exact_mod_cast hRn
      nlinarith
    have htimeNat : ladderTime ω R ≤ ⌊(n : ℝ) * (T + 1)⌋₊ :=
      Nat.le_floor htime
    have hw := hwalk (ladderTime ω R) htimeNat
    rw [walk_ladderTime hω] at hw
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg] at hw
    have hRnonneg : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
    rw [abs_of_nonneg hRnonneg] at hw
    have hlt : K * b < (R : ℝ) := by
      exact_mod_cast (Nat.lt_floor_add_one (K * b))
    linarith
  have hrFloor : r ≤ ⌊K * b⌋₊ := by
    dsimp [R] at hrR
    omega
  exact (Nat.cast_le.mpr hrFloor).trans (Nat.floor_le hKb)

private theorem unpaddedError_le_two_contourError_add_oscillation {ω : ℕ → ℕ}
    (hω : LadderFinite ω) (hdiv : Tendsto (unpaddedStart ω) atTop atTop)
    (B : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (T : ℝ≥0) {δ : ℝ}
    (hr : ∀ t : Set.Icc (0 : ℝ) (T : ℝ),
      (unpaddedBlock ω ⌊2 * (n : ℝ) * (t : ℝ)⌋₊ : ℝ) / n ≤ δ)
    (hKBn : ∀ t : Set.Icc (0 : ℝ) (T : ℝ),
      (unpaddedBlock ω ⌊2 * (n : ℝ) * (t : ℝ)⌋₊ : ℝ) ≤ n) :
    forestContourUnpaddedError B n T ω ≤
      2 * forestContourHeightError B n (T + 1) ω +
        heightOscillation B n ((T : ℝ) + 1) δ ω := by
  let S : ℝ≥0 := T + 1
  let : Nonempty (Set.Icc (0 : ℝ) (T : ℝ)) := ⟨⟨0, le_rfl, T.coe_nonneg⟩⟩
  unfold forestContourUnpaddedError
  apply ciSup_le
  intro t
  let r := unpaddedBlock ω ⌊2 * (n : ℝ) * (t : ℝ)⌋₊
  let x : Set.Icc (0 : ℝ) ((S : ℝ≥0) : ℝ) :=
    ⟨(t : ℝ) + (r : ℝ) / n,
      add_nonneg t.2.1 (div_nonneg (Nat.cast_nonneg r) (Nat.cast_nonneg n)), by
      have hrt := hKBn t
      have ht := t.2.2
      change (t : ℝ) + (r : ℝ) / n ≤ ((T + 1 : ℝ≥0) : ℝ)
      push_cast
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
      have hrn : (r : ℝ) ≤ 1 * n := by simpa using hrt
      have := (div_le_iff₀ hnR).mpr hrn
      change (r : ℝ) / n ≤ 1 at this
      dsimp [r] at this ⊢
      linarith⟩
  let y : Set.Icc (0 : ℝ) ((S : ℝ≥0) : ℝ) :=
    ⟨(t : ℝ), t.2.1, by
      change (t : ℝ) ≤ (T : ℝ) + 1
      linarith [t.2.2]⟩
  have htime_x : 2 * (n : ℝ) * (x : ℝ) =
      2 * (n : ℝ) * (t : ℝ) + 2 * (r : ℝ) := by
    dsimp [x]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    field_simp
  have hheight_x : (n : ℝ) * (x : ℝ) = (n : ℝ) * (t : ℝ) + r := by
    dsimp [x]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    field_simp
  have hcontour (z : Set.Icc (0 : ℝ) ((S : ℝ≥0) : ℝ)) :
      |B n / n * forestContourLin ω (2 * (n : ℝ) * (z : ℝ)) -
        B n / n * forestHeightLin ω ((n : ℝ) * (z : ℝ))| ≤
        forestContourHeightError B n S ω := by
    have hd := ContinuousMap.dist_apply_le_dist
      (f := forestContourPath B n S ω) (g := forestHeightPath B n S ω) z
    rw [forestContourPath_apply] at hd
    change dist (B n / n * forestContourLin ω (2 * (n : ℝ) * (z : ℝ)))
      (B n / n * forestHeightLin ω ((n : ℝ) * (z : ℝ))) ≤
        dist (forestContourPath B n S ω) (forestHeightPath B n S ω) at hd
    rw [Real.dist_eq, dist_forestContourPath_forestHeightPath] at hd
    exact hd
  have hxy : |(x : ℝ) - (y : ℝ)| ≤ δ := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hrn := hr t
    change |(t : ℝ) + (r : ℝ) / n - (t : ℝ)| ≤ δ
    rw [add_sub_cancel_left, abs_of_nonneg (div_nonneg (Nat.cast_nonneg r) hnR.le)]
    exact hrn
  have hheight := heightDifference_le_heightOscillation B n S.coe_nonneg ω x y hxy
  rw [hheight_x] at hheight
  rw [forestContourUnpaddedLin_eq hω hdiv
    (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) t.2.1)]
  have hcx := hcontour x
  have hcy := hcontour y
  rw [htime_x, hheight_x] at hcx
  have hheight' : |B n / n * forestHeightLin ω ((n : ℝ) * (t : ℝ) + r) -
      B n / n * forestHeightLin ω ((n : ℝ) * (t : ℝ))| ≤
      heightOscillation B n ((T : ℝ) + 1) δ ω := by
    simpa [S, y] using hheight
  change |B n / n * forestContourLin ω (2 * (n : ℝ) * (t : ℝ)) -
    B n / n * forestHeightLin ω ((n : ℝ) * (t : ℝ))| ≤ _ at hcy
  calc
    |B n / n * forestContourLin ω (2 * n * t + 2 * r) -
        B n / n * forestContourLin ω (2 * n * t)| ≤
        |B n / n * forestContourLin ω (2 * n * t + 2 * r) -
          B n / n * forestHeightLin ω (n * t + r)| +
        |B n / n * forestHeightLin ω (n * t + r) -
          B n / n * forestContourLin ω (2 * n * t)| := abs_sub_le _ _ _
    _ ≤ |B n / n * forestContourLin ω (2 * n * t + 2 * r) -
          B n / n * forestHeightLin ω (n * t + r)| +
        (|B n / n * forestHeightLin ω (n * t + r) -
          B n / n * forestHeightLin ω (n * t)| +
        |B n / n * forestHeightLin ω (n * t) -
          B n / n * forestContourLin ω (2 * n * t)|) :=
        add_le_add (le_refl _) (abs_sub_le _ _ _)
    _ ≤ 2 * forestContourHeightError B n S ω +
        heightOscillation B n ((T : ℝ) + 1) δ ω := by
      rw [abs_sub_comm (B n / n * forestHeightLin ω (n * t))]
      dsimp [S] at hcx hcy ⊢
      linarith [hheight']

/-- **Padded/unpadded comparison** on every positive horizon: the two normalized contours are
uniformly close in probability. -/
theorem unpadded_contour_error_tendstoInMeasure {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure (offspringSeqLaw μ : Measure (ℕ → ℕ))
      (fun n ω => forestContourUnpaddedError B n T ω) atTop (fun _ => (0 : ℝ)) := by
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro η hη
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun _ => ha.trans_le measureReal_nonneg
  · intro b hb
    obtain ⟨K, hK, N, htail⟩ := h.isRealStableAttracted.horizon_max_tight
      (show 0 < (T : ℝ) + 1 by positivity) (b / 4) (by positivity)
    obtain ⟨δ, hδ, hOevent⟩ := exists_pos_uniform_height_modulus_probability_small h
      (T := T + 1) (by positivity) (η := η / 3) (ε := b / 4) (by positivity) (by positivity)
    let A (n : ℕ) : Set (ℕ → ℕ) := {ω | ∃ u ≤ ⌊(n : ℝ) * ((T : ℝ) + 1)⌋₊,
      K * B n < |(walk ω u : ℝ)|}
    let E (n : ℕ) : Set (ℕ → ℕ) :=
      {ω | η / 3 ≤ ‖forestContourHeightError B n (T + 1) ω - 0‖}
    let O (n : ℕ) : Set (ℕ → ℕ) :=
      {ω | η / 3 < heightOscillation B n ((T : ℝ) + 1) δ ω}
    let F (n : ℕ) : Set (ℕ → ℕ) :=
      {ω | η ≤ ‖forestContourUnpaddedError B n T ω - 0‖}
    have hAevent : ∀ᶠ n : ℕ in atTop,
        (offspringSeqLaw μ).toMeasure.real (A n) ≤ b / 4 := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have heq : (offspringSeqLaw μ).toMeasure.real (A n) =
          maxTail (realOffspringStepLaw μ) ⌊(n : ℝ) * ((T : ℝ) + 1)⌋₊
            (K * B n) := by
        change ((offspringSeqLaw μ).toMeasure (A n)).toReal = _
        rw [measure_walk_maximum, ENNReal.toReal_ofReal (maxTail_nonneg _ _ _)]
      rw [heq]
      exact htail n hn
    have hEevent : ∀ᶠ n : ℕ in atTop,
        (offspringSeqLaw μ).toMeasure.real (E n) < b / 4 := by
      have hlim := (tendstoInMeasure_iff_measureReal_norm.mp
        (contour_height_error_tendstoInMeasure h (T := T + 1) (by positivity)))
          (η / 3) (by positivity)
      exact hlim.eventually (gt_mem_nhds (show 0 < b / 4 by positivity))
    have hKn : Tendsto (fun n : ℕ => K * (B n / n)) atTop (𝓝 0) := by
      simpa using (Survival.tendsto_B_div_n h).const_mul K
    have hKδ : ∀ᶠ n : ℕ in atTop, K * (B n / n) < δ :=
      hKn.eventually (gt_mem_nhds hδ)
    have hK1 : ∀ᶠ n : ℕ in atTop, K * (B n / n) < 1 :=
      hKn.eventually (gt_mem_nhds zero_lt_one)
    filter_upwards [hAevent, hEevent, hKδ, hK1, eventually_ge_atTop 1]
      with n hnA hnE hnKδ hnK1 hn1
    have hn : 0 < n := by omega
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hB : 0 < B n := h.pos n hn1
    have hKBn : K * B n < (n : ℝ) := by
      have heq : K * (B n / n) = K * B n / n := by ring
      rw [heq] at hnK1
      exact (div_lt_one hnR).mp hnK1
    have hsub : ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure,
        ω ∈ F n → ω ∈ A n ∪ (E n ∪ O n) := by
      filter_upwards [ae_ladderFinite μ h.critical h.nondegenerate,
        ae_tendsto_unpaddedStart μ h.critical h.nondegenerate] with ω hω hdiv
      intro hF
      by_cases ha : ω ∈ A n
      · exact Or.inl ha
      by_cases he : ω ∈ E n
      · exact Or.inr (Or.inl he)
      by_cases ho : ω ∈ O n
      · exact Or.inr (Or.inr ho)
      exfalso
      have hwalk : ∀ u ≤ ⌊(n : ℝ) * ((T : ℝ) + 1)⌋₊,
          |(walk ω u : ℝ)| ≤ K * B n := by
        intro u hu
        exact le_of_not_gt (fun hlt => ha ⟨u, hu, hlt⟩)
      have hr0 (t : Set.Icc (0 : ℝ) (T : ℝ)) :
          (unpaddedBlock ω ⌊2 * (n : ℝ) * (t : ℝ)⌋₊ : ℝ) ≤ K * B n :=
        unpaddedBlock_le_of_walk_bound hω hn hK hB hKBn hwalk t
      have hr (t : Set.Icc (0 : ℝ) (T : ℝ)) :
          (unpaddedBlock ω ⌊2 * (n : ℝ) * (t : ℝ)⌋₊ : ℝ) / n ≤ δ := by
        apply (div_le_div_of_nonneg_right (hr0 t) hnR.le).trans
        have heq : K * (B n / n) = K * B n / n := by ring
        rw [← heq]
        exact hnKδ.le
      have hrn (t : Set.Icc (0 : ℝ) (T : ℝ)) :
          (unpaddedBlock ω ⌊2 * (n : ℝ) * (t : ℝ)⌋₊ : ℝ) ≤ n :=
        (hr0 t).trans hKBn.le
      have herr := unpaddedError_le_two_contourError_add_oscillation hω hdiv B hn T hr hrn
      have hsmallE : forestContourHeightError B n (T + 1) ω < η / 3 := by
        have hnonneg : 0 ≤ forestContourHeightError B n (T + 1) ω := by
          unfold forestContourHeightError
          exact Real.iSup_nonneg fun _ => abs_nonneg _
        have hh : ‖forestContourHeightError B n (T + 1) ω - 0‖ < η / 3 :=
          lt_of_not_ge he
        simpa only [sub_zero, Real.norm_eq_abs, abs_of_nonneg hnonneg] using hh
      have hsmallO : heightOscillation B n ((T : ℝ) + 1) δ ω ≤ η / 3 := le_of_not_gt ho
      have hnonneg : 0 ≤ forestContourUnpaddedError B n T ω := by
        unfold forestContourUnpaddedError
        exact Real.iSup_nonneg fun _ => abs_nonneg _
      change η ≤ ‖forestContourUnpaddedError B n T ω - 0‖ at hF
      rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hnonneg] at hF
      linarith
    calc
      (offspringSeqLaw μ).toMeasure.real (F n) ≤
          (offspringSeqLaw μ).toMeasure.real (A n ∪ (E n ∪ O n)) :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
      _ ≤ (offspringSeqLaw μ).toMeasure.real (A n) +
          (offspringSeqLaw μ).toMeasure.real (E n ∪ O n) := measureReal_union_le _ _
      _ ≤ (offspringSeqLaw μ).toMeasure.real (A n) +
          ((offspringSeqLaw μ).toMeasure.real (E n) +
            (offspringSeqLaw μ).toMeasure.real (O n)) :=
        add_le_add le_rfl (measureReal_union_le _ _)
      _ < b := by
        have hO := hOevent n
        change (offspringSeqLaw μ).toMeasure.real (O n) ≤ b / 4 at hO
        linarith

end BGW.StableTrees.ForestContour
