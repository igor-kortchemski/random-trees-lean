/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.AldousCriterionOptionalBounds
public import BGW.Skorokhod.AldousCriterionAveraging
public import BGW.Skorokhod.AldousCriterionOptionalExits
public import BGW.Skorokhod.AldousCriterionFiniteExits

import Mathlib.Topology.Order.ProjIcc

/-!
# Probability bounds for nearby optional times

Averaging over deterministic offsets bounds a large displacement between optional
times at distance at most `δ`. The estimate applies to genuine exits, where a
large displacement is present; it does not count the terminal sentinel as an exit.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Topology

namespace BGW.Skorokhod

variable {T : ℝ}

/-- Uniform deterministic-offset bounds control large displacements between nearby optional
times, with no independence assumption.

Reference: Billingsley 1999, Section 16. -/
theorem measure_short_aldous_pair_le {Ω : Type*} [m : MeasurableSpace Ω]
    (hT : 0 ≤ T) (P : Measure Ω) [IsFiniteMeasure P]
    (𝓕 : Filtration (Icc (0 : ℝ) T) m) (X : Ω → D T ℝ) (hX : Measurable X)
    (τ σ : Ω → Icc (0 : ℝ) T) (hτ : IsOptionalTime 𝓕 τ) (hσ : IsOptionalTime 𝓕 σ)
    {ε δ : ℝ} {η : ℝ≥0∞} (hδ : 0 < δ)
    (hbound : ∀ ρ : Ω → Icc (0 : ℝ) T, IsOptionalTime 𝓕 ρ →
      ∀ u : ℝ, 0 ≤ u → u ≤ 2 * δ →
        P {ω | ε < |X ω (projIcc 0 T hT (ρ ω + u)) - X ω (ρ ω)|} ≤ η) :
    P {ω | τ ω ≤ σ ω ∧ (σ ω : ℝ) - τ ω ≤ δ ∧
      2 * ε < |X ω (σ ω) - X ω (τ ω)|} ≤ 4 * η := by
  classical
  let F (ρ : Ω → Icc (0 : ℝ) T) (p : ℝ × Ω) : ℝ :=
    |X p.2 (projIcc 0 T hT ((ρ p.2 : ℝ) + p.1)) - X p.2 (ρ p.2)|
  have hF (ρ : Ω → Icc (0 : ℝ) T) (hρ : IsOptionalTime 𝓕 ρ) : Measurable (F ρ) := by
    have hρsnd : Measurable (fun p : ℝ × Ω => ρ p.2) :=
      hρ.measurable.comp measurable_snd
    have htime : Measurable (fun p : ℝ × Ω =>
        projIcc 0 T hT ((ρ p.2 : ℝ) + p.1)) :=
      continuous_projIcc.measurable.comp
        (((continuous_subtype_val.measurable).comp hρsnd).add measurable_fst)
    exact continuous_abs.measurable.comp
      ((measurable_eval₂.comp ((hX.comp measurable_snd).prodMk htime)).sub
        (measurable_eval₂.comp ((hX.comp measurable_snd).prodMk hρsnd)))
  let B (ρ : Ω → Icc (0 : ℝ) T) : Set (ℝ × Ω) :=
    {p | p.1 ∈ Icc (0 : ℝ) (2 * δ) ∧ ε < F ρ p}
  have hB (ρ) (hρ : IsOptionalTime 𝓕 ρ) : MeasurableSet (B ρ) :=
    (measurable_fst measurableSet_Icc).inter (measurableSet_lt measurable_const (hF ρ hρ))
  let A (ρ : Ω → Icc (0 : ℝ) T) (u : ℝ) (ω : Ω) : ℝ≥0∞ :=
    (B ρ).indicator (fun _ => 1) (u, ω)
  have hA (ρ) (hρ : IsOptionalTime 𝓕 ρ) : Measurable (Function.uncurry (A ρ)) :=
    measurable_const.indicator (hB ρ hρ)
  have hAbound (ρ) (hρ : IsOptionalTime 𝓕 ρ) (u : ℝ) :
      (∫⁻ ω, A ρ u ω ∂P) ≤ (Icc (0 : ℝ) (2 * δ)).indicator (fun _ => η) u := by
    by_cases hu : u ∈ Icc (0 : ℝ) (2 * δ)
    · rw [indicator_of_mem hu]
      have heq : (fun ω => A ρ u ω) =
          {ω | ε < F ρ (u, ω)}.indicator (fun _ => (1 : ℝ≥0∞)) := by
        funext ω
        simp only [A, B, indicator, mem_ofPred_eq, hu, true_and]
      have hset : MeasurableSet {ω : Ω | ε < F ρ (u, ω)} :=
        measurableSet_lt measurable_const
          ((hF ρ hρ).comp (measurable_const.prodMk measurable_id))
      rw [heq, lintegral_indicator_const hset, one_mul]
      exact hbound ρ hρ u hu.1 hu.2
    · have heq : (fun ω => A ρ u ω) = 0 := by
        funext ω
        simp only [A, B, indicator, mem_ofPred_eq, hu, false_and, ite_false, Pi.zero_apply]
      rw [heq, indicator_of_notMem hu]
      change (∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P) ≤ 0
      simp only [lintegral_zero, le_refl]
  let E : Set Ω := {ω | τ ω ≤ σ ω ∧ (σ ω : ℝ) - τ ω ≤ δ ∧
    2 * ε < |X ω (σ ω) - X ω (τ ω)|}
  have hE : MeasurableSet E := by
    have hτval := continuous_subtype_val.measurable.comp hτ.measurable
    have hσval := continuous_subtype_val.measurable.comp hσ.measurable
    have hdiff := (measurable_eval₂.comp (hX.prodMk hσ.measurable)).sub
      (measurable_eval₂.comp (hX.prodMk hτ.measurable))
    exact (measurableSet_le hτ.measurable hσ.measurable).inter
      ((measurableSet_le (hσval.sub hτval) measurable_const).inter
        (measurableSet_lt measurable_const (continuous_abs.measurable.comp hdiff)))
  apply measure_le_four_mul_of_aldous_cover P hδ (hA τ hτ) (hA σ hσ) hE
    (fun ω => (σ ω : ℝ) - τ ω) ?_ (hAbound τ hτ) (hAbound σ hσ)
  intro ω hω u hu
  have hd0 : 0 ≤ (σ ω : ℝ) - τ ω := sub_nonneg.mpr hω.1
  have hv : u - ((σ ω : ℝ) - τ ω) ∈ Icc (0 : ℝ) (2 * δ) := by
    constructor <;> linarith [hu.1, hu.2, hω.2.1]
  have hu' : u ∈ Icc (0 : ℝ) (2 * δ) := ⟨hδ.le.trans hu.1, hu.2⟩
  by_cases hfirst : ε < F τ (u, ω)
  · have hmem : (u, ω) ∈ B τ := ⟨hu', hfirst⟩
    change 1 ≤ (B τ).indicator (fun _ => 1) (u, ω) + _
    rw [indicator_of_mem hmem]
    exact le_add_of_nonneg_right bot_le
  · have hsecond : ε < F σ (u - ((σ ω : ℝ) - τ ω), ω) := by
      have heq : projIcc 0 T hT ((σ ω : ℝ) + (u - ((σ ω : ℝ) - τ ω))) =
          projIcc 0 T hT ((τ ω : ℝ) + u) := by congr 1; ring
      have hfirst' : |X ω (projIcc 0 T hT ((τ ω : ℝ) + u)) - X ω (τ ω)| ≤ ε :=
        le_of_not_gt hfirst
      by_contra! hsecond
      change |X ω (projIcc 0 T hT ((σ ω : ℝ) + (u - ((σ ω : ℝ) - τ ω)))) -
        X ω (σ ω)| ≤ ε at hsecond
      rw [heq, abs_sub_comm] at hsecond
      have htri := abs_sub_le (X ω (σ ω))
        (X ω (projIcc 0 T hT ((τ ω : ℝ) + u))) (X ω (τ ω))
      linarith [hω.2.2]
    have hmem : (u - ((σ ω : ℝ) - τ ω), ω) ∈ B σ := ⟨hv, hsecond⟩
    change 1 ≤ _ + (B σ).indicator (fun _ => 1) (u - ((σ ω : ℝ) - τ ω), ω)
    rw [indicator_of_mem hmem]
    exact le_add_of_nonneg_left bot_le

/-- Aldous's sequence condition bounds every genuine short exit gap uniformly in its index.
The terminal sentinel is excluded because its gap can be arbitrarily short.

Reference: Billingsley 1999, Section 16. -/
theorem exists_uniform_aldous_exit_gap_bound (hT : 0 < T)
    {Ω : ℕ → Type*} [m : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (𝓕 : ∀ n, Filtration (Icc (0 : ℝ) T) (m n))
    (X : ∀ n, Ω n → D T ℝ) (hX : ∀ n, Measurable (X n))
    (hadapted : ∀ n t, Measurable[𝓕 n t] (fun ω => X n ω t))
    (hAldous : ∀ (τ : ∀ n, Ω n → Icc (0 : ℝ) T), (∀ n, IsStopTime (𝓕 n) (τ n)) →
      ∀ h : ℕ → ℝ, (∀ n, 0 ≤ h n) → Filter.Tendsto h Filter.atTop (𝓝 0) →
      ∀ ε > 0, Filter.Tendsto
        (fun n => P n {ω | ε ≤ |X n ω (projIcc 0 T hT.le (τ n ω + h n)) - X n ω (τ n ω)|})
        Filter.atTop (𝓝 0))
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ k : ℕ,
      P n {ω | (aldousExitTimes hT.le (X n ω) ε (k + 1) : ℝ) < T ∧
        (aldousExitTimes hT.le (X n ω) ε (k + 1) : ℝ) -
          aldousExitTimes hT.le (X n ω) ε k ≤ δ} ≤ 4 * ENNReal.ofReal η := by
  obtain ⟨d, hd, N, hbound⟩ := exists_uniform_aldous_optional_bound hT P 𝓕 X hAldous
    (show 0 < ε / 3 by positivity) hη
  refine ⟨d / 2, half_pos hd, N, fun n hn k => ?_⟩
  let τ (ω : Ω n) := aldousExitTimes hT.le (X n ω) ε k
  let σ (ω : Ω n) := aldousExitTimes hT.le (X n ω) ε (k + 1)
  have hτ : IsOptionalTime (𝓕 n) τ :=
    isOptionalTime_aldousExitTimes hT.le (𝓕 n) (X n) (hadapted n) ε k
  have hσ : IsOptionalTime (𝓕 n) σ :=
    isOptionalTime_aldousExitTimes hT.le (𝓕 n) (X n) (hadapted n) ε (k + 1)
  have hpair := measure_short_aldous_pair_le hT.le (P n) (𝓕 n) (X n) (hX n)
    τ σ hτ hσ (half_pos hd) (ε := ε / 3) (η := ENNReal.ofReal η) (by
      intro ρ hρ u hu hud
      exact hbound n hn ρ hρ u hu (by linarith))
  apply (measure_mono ?_).trans hpair
  intro ω hω
  have hinc : ε ≤ |X n ω (σ ω) - X n ω (τ ω)| :=
    le_abs_sub_aldousExitTime (X n ω) ε (τ ω) hω.1
  exact ⟨le_aldousExitTime (X n ω) ε (τ ω), hω.2, by linarith⟩

end BGW.Skorokhod
