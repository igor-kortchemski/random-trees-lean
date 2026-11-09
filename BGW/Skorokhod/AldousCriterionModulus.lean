/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.AldousCriterionCounting
public import BGW.Skorokhod.AldousCriterionTerminalPartition
public import BGW.Skorokhod.AldousCriterionTerminalBound

/-!
# Aldous's uniform modulus estimate

First bound the number of genuine exits in probability. Then exclude short gaps
among a fixed finite number of exits and control a deterministic terminal window.
Merging the last block produces a partition admissible for Billingsley's modulus.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology ENNReal BigOperators

namespace BGW.Skorokhod

variable {T : ℝ}

/-- Aldous's sequence condition controls the càdlàg modulus, uniformly for large indices.

Reference: Billingsley 1999, Section 16. -/
private theorem aldous_modulus_bound_aux (hT : 0 < T)
    {Ω : ℕ → Type*} [m : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (𝓕 : ∀ n, Filtration (Icc (0 : ℝ) T) (m n))
    (X : ∀ n, Ω n → D T ℝ) (hX : ∀ n, Measurable (X n))
    (hadapted : ∀ n t, Measurable[𝓕 n t] (fun ω => X n ω t))
    (hAldous : ∀ (τ : ∀ n, Ω n → Icc (0 : ℝ) T), (∀ n, IsStopTime (𝓕 n) (τ n)) →
      ∀ h : ℕ → ℝ, (∀ n, 0 ≤ h n) → Tendsto h atTop (𝓝 0) →
      ∀ ε > 0, Tendsto
        (fun n => P n {ω | ε ≤ |X n ω (projIcc 0 T hT.le (τ n ω + h n)) - X n ω (τ n ω)|})
        atTop (𝓝 0))
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ, 0 < δ ∧ δ < T ∧ ∃ N : ℕ, ∀ n ≥ N,
      P n {ω | 4 * ε < cadlagModulus (X n ω) δ} ≤ 16 * ENNReal.ofReal η := by
  classical
  obtain ⟨d₀, hd₀, N₀, hbase⟩ := exists_uniform_aldous_exit_gap_bound
    hT P 𝓕 X hX hadapted hAldous hε hη
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * T / d₀)
  have hK' : 2 * T < (K : ℝ) * d₀ := (div_lt_iff₀ hd₀).mp hK
  have hden : (0 : ℝ) < K + 1 := by positivity
  obtain ⟨d₁, hd₁, N₁, hsmall⟩ := exists_uniform_aldous_exit_gap_bound
    hT P 𝓕 X hX hadapted hAldous hε (div_pos hη hden)
  obtain ⟨d₂, hd₂, N₂, hoptional⟩ := exists_uniform_aldous_optional_bound
    hT P 𝓕 X hAldous (show 0 < ε / 3 by positivity) hη
  let δ := min (T / 8) (min (d₁ / 2) (d₂ / 4))
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hδT : 4 * δ < T := by
    have hle : δ ≤ T / 8 := min_le_left _ _
    linarith
  have hδ₁ : 2 * δ ≤ d₁ := by
    have hle : δ ≤ d₁ / 2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hδ₂ : 4 * δ ≤ d₂ := by
    have hle : δ ≤ d₂ / 4 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  let a : Icc (0 : ℝ) T := ⟨T - 2 * δ, by constructor <;> linarith⟩
  refine ⟨δ, hδ, by linarith, max N₀ (max N₁ N₂), fun n hn => ?_⟩
  have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
  have hn₁ : N₁ ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hn₂ : N₂ ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  let τ (j : ℕ) (ω : Ω n) := aldousExitTimes hT.le (X n ω) ε j
  let A : Set (Ω n) := {ω | (τ K ω : ℝ) < T}
  let B (i : Fin K) : Set (Ω n) := {ω | (τ (i + 1) ω : ℝ) < T ∧
    (τ (i + 1) ω : ℝ) - τ i ω ≤ d₁}
  let C : Set (Ω n) := {ω | ∃ t : Icc (0 : ℝ) T, a ≤ t ∧ ε < |X n ω t - X n ω a|}
  have hA : P n A ≤ 8 * ENNReal.ofReal η := by
    have h := measure_aldousExitTimes_lt_terminal_le hT.le (P n) (𝓕 n) (X n)
      (hadapted n) ε hd₀ hK' (hbase n hn₀)
    convert h using 1; ring
  have hB : P n (⋃ i, B i) ≤ 4 * ENNReal.ofReal η := by
    have hreal : (K : ℝ) * (4 * (η / (K + 1))) ≤ 4 * η := by
      have hc : ((K : ℝ) + 1) * (η / (K + 1)) = η := by field_simp
      have hq : 0 ≤ η / (K + 1) := (div_pos hη hden).le
      nlinarith
    calc
      P n (⋃ i, B i) ≤ ∑ i, P n (B i) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _i : Fin K, 4 * ENNReal.ofReal (η / (K + 1)) :=
        Finset.sum_le_sum fun i _ => hsmall n hn₁ i
      _ = ENNReal.ofReal ((K : ℝ) * (4 * (η / (K + 1)))) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
        norm_num
      _ ≤ ENNReal.ofReal (4 * η) := ENNReal.ofReal_le_ofReal hreal
      _ = 4 * ENNReal.ofReal η := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
  have hC : P n C ≤ 4 * ENNReal.ofReal η :=
    measure_aldous_terminal_oscillation_le hT.le (P n) (𝓕 n) (X n) (hX n)
      (hadapted n) a hε (show 0 < 2 * δ by positivity)
      (by dsimp [a]; linarith) (by
        intro ρ hρ u hu hud
        exact hoptional n hn₂ ρ hρ u hu (by linarith))
  have hsub : {ω | 4 * ε < cadlagModulus (X n ω) δ} ⊆ A ∪ ((⋃ i, B i) ∪ C) := by
    intro ω hω
    by_contra hbad
    have hnotA : ω ∉ A := fun h => hbad (Or.inl h)
    have hnotB : ∀ i, ω ∉ B i := fun i h => hbad (Or.inr (Or.inl (mem_iUnion.mpr ⟨i, h⟩)))
    have hnotC : ω ∉ C := fun h => hbad (Or.inr (Or.inr h))
    have hstop : (τ K ω : ℝ) = T := le_antisymm (τ K ω).2.2 (le_of_not_gt hnotA)
    have hmod := cadlagModulus_le_of_aldous_gaps hT (X n ω) hε.le hδ hδT K hstop
      (by
        intro j hj hterminal
        have hnot : ¬ ((τ (j + 1) ω : ℝ) - τ j ω ≤ d₁) :=
          fun h => hnotB ⟨j, hj⟩ ⟨hterminal, h⟩
        exact hδ₁.trans_lt (lt_of_not_ge hnot))
      (by
        intro t ht
        exact le_of_not_gt (fun h => hnotC ⟨t, ht, h⟩))
    exact (not_lt_of_ge hmod) hω
  calc
    P n {ω | 4 * ε < cadlagModulus (X n ω) δ} ≤ P n (A ∪ ((⋃ i, B i) ∪ C)) :=
      measure_mono hsub
    _ ≤ P n A + (P n (⋃ i, B i) + P n C) :=
      (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ 8 * ENNReal.ofReal η + (4 * ENNReal.ofReal η + 4 * ENNReal.ofReal η) :=
      add_le_add hA (add_le_add hB hC)
    _ = 16 * ENNReal.ofReal η := by ring

/-- Aldous's sequence condition makes the modulus small in probability for all large indices.

Reference: Billingsley 1999, Section 16. -/
theorem exists_uniform_aldous_modulus_bound (hT : 0 < T)
    {Ω : ℕ → Type*} [m : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (𝓕 : ∀ n, Filtration (Icc (0 : ℝ) T) (m n))
    (X : ∀ n, Ω n → D T ℝ) (hX : ∀ n, Measurable (X n))
    (hadapted : ∀ n t, Measurable[𝓕 n t] (fun ω => X n ω t))
    (hAldous : ∀ (τ : ∀ n, Ω n → Icc (0 : ℝ) T), (∀ n, IsStopTime (𝓕 n) (τ n)) →
      ∀ h : ℕ → ℝ, (∀ n, 0 ≤ h n) → Tendsto h atTop (𝓝 0) →
      ∀ ε > 0, Tendsto
        (fun n => P n {ω | ε ≤ |X n ω (projIcc 0 T hT.le (τ n ω + h n)) - X n ω (τ n ω)|})
        atTop (𝓝 0))
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ, 0 < δ ∧ δ < T ∧ ∃ N : ℕ, ∀ n ≥ N,
      P n {ω | ε < cadlagModulus (X n ω) δ} ≤ ENNReal.ofReal η := by
  obtain ⟨δ, hδ, hδT, N, hbound⟩ := aldous_modulus_bound_aux hT P 𝓕 X hX hadapted hAldous
    (show 0 < ε / 4 by positivity) (show 0 < η / 16 by positivity)
  have heps : 4 * (ε / 4) = ε := by ring
  have hscale : 16 * ENNReal.ofReal (η / 16) = ENNReal.ofReal η := by
    calc
      16 * ENNReal.ofReal (η / 16) = ENNReal.ofReal (16 * (η / 16)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
        norm_num
      _ = ENNReal.ofReal η := by congr 1; ring
  exact ⟨δ, hδ, hδT, N, fun n hn => by simpa only [heps, hscale] using hbound n hn⟩

end BGW.Skorokhod
