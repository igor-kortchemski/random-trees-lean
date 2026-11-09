/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.AldousCriterionFiniteExits
public import BGW.Skorokhod.AldousCriterionOptionalExits
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin

/-!
# Counting short exit gaps

Among sufficiently many successive gaps in a bounded horizon, at least half are
short. A finite counting argument turns uniform probability bounds for individual
short gaps into a bound for the event that many exits occur.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace BGW.Skorokhod

variable {T : ℝ}

/-- In a bounded nondecreasing time sequence, at least half of sufficiently many gaps are
short. This statement counts capped gaps too; probability applications exclude them separately.

Reference: Billingsley 1999, Section 16. -/
private theorem half_le_card_short_aldous_gaps (hT : 0 ≤ T) (f : D T ℝ) (ε : ℝ)
    {δ : ℝ} (hδ : 0 < δ) {K : ℕ} (hK : 2 * T < (K : ℝ) * δ) :
    K ≤ 2 * ((Finset.range K).filter fun k =>
      (aldousExitTimes hT f ε (k + 1) : ℝ) - aldousExitTimes hT f ε k ≤ δ).card := by
  classical
  let τ := aldousExitTimes hT f ε
  let g (k : ℕ) := (τ (k + 1) : ℝ) - τ k
  let S := (Finset.range K).filter fun k => g k ≤ δ
  let L := (Finset.range K).filter fun k => ¬ g k ≤ δ
  have hg (k) : 0 ≤ g k := sub_nonneg.mpr (le_aldousExitTime f ε _)
  have htel (N : ℕ) : ∑ k ∈ Finset.range N, g k = (τ N : ℝ) - τ 0 := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih]; dsimp [g]; ring
  have hlong : (L.card : ℝ) * δ ≤ T := by
    calc
      (L.card : ℝ) * δ = ∑ _k ∈ L, δ := by simp
      _ ≤ ∑ k ∈ L, g k := Finset.sum_le_sum fun k hk =>
        (lt_of_not_ge (Finset.mem_filter.mp hk).2).le
      _ ≤ ∑ k ∈ Finset.range K, g k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun k _ _ => hg k)
      _ = (τ K : ℝ) := by rw [htel]; simp [τ, aldousExitTimes]
      _ ≤ T := (τ K).2.2
  have hcard : (S.card : ℝ) + (L.card : ℝ) = K := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not
      (s := Finset.range K) (fun k => g k ≤ δ)).trans (Finset.card_range K)
  have hhalf : (K : ℝ) ≤ 2 * S.card := by nlinarith
  exact_mod_cast hhalf

open Classical in
/-- If an event forces membership in at least half of a finite family of events, each of
measure at most `η`, its measure is at most `2 * η`.

Reference: Billingsley 1999, Section 16. -/
private theorem measure_le_two_mul_of_half_cover {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] (P : Measure Ω) {E : Set Ω} (hE : MeasurableSet E)
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) {η : ℝ≥0∞}
    (hprob : ∀ i, P (A i) ≤ η)
    (hcount : ∀ ω ∈ E,
      Fintype.card ι ≤ 2 * (Finset.univ.filter fun i => ω ∈ A i).card) : P E ≤ 2 * η := by
  classical
  let c : ℝ≥0∞ := Fintype.card ι
  have hpoint (ω) : c * E.indicator (fun _ => (1 : ℝ≥0∞)) ω ≤
      2 * ∑ i, (A i).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    by_cases hω : ω ∈ E
    · rw [indicator_of_mem hω, mul_one]
      have hsum : (∑ i, (A i).indicator (fun _ => (1 : ℝ≥0∞)) ω) =
          ((Finset.univ.filter fun i => ω ∈ A i).card : ℝ≥0∞) := by
        simp only [indicator_apply, Finset.sum_boole]
      rw [hsum]
      dsimp [c]
      exact_mod_cast hcount ω hω
    · simp only [indicator_of_notMem hω, mul_zero, zero_le]
  have hsum_meas : Measurable (fun ω => ∑ i, (A i).indicator (fun _ => (1 : ℝ≥0∞)) ω) :=
    Finset.measurable_sum _ (fun i _ => measurable_const.indicator (hA i))
  have hint := lintegral_mono (μ := P) hpoint
  rw [lintegral_const_mul c (measurable_const.indicator hE),
    lintegral_indicator_const hE, one_mul,
    lintegral_const_mul 2 hsum_meas,
    lintegral_finsetSum Finset.univ (fun i _ => measurable_const.indicator (hA i))] at hint
  simp only [lintegral_indicator_const, hA, one_mul] at hint
  have hsum : ∑ i, P (A i) ≤ c * η := by
    calc
      ∑ i, P (A i) ≤ ∑ _i : ι, η := Finset.sum_le_sum fun i _ => hprob i
      _ = c * η := by simp [c]
  have htotal : c * P E ≤ c * (2 * η) := by
    calc
      c * P E ≤ 2 * ∑ i, P (A i) := hint
      _ ≤ 2 * (c * η) := by gcongr
      _ = c * (2 * η) := by ring
  have hcancel : c⁻¹ * (c * P E) ≤ c⁻¹ * (c * (2 * η)) := by gcongr 1
  have hc : c ≠ 0 := by simp [c, Fintype.card_ne_zero]
  have hctop : c ≠ ⊤ := by simp [c]
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel hc hctop, one_mul] using hcancel

/-- Uniform bounds on individual genuine short gaps bound the tail of the number of exits.

Reference: Billingsley 1999, Section 16. -/
theorem measure_aldousExitTimes_lt_terminal_le {Ω : Type*} [m : MeasurableSpace Ω]
    (hT : 0 ≤ T) (P : Measure Ω) (𝓕 : Filtration (Icc (0 : ℝ) T) m)
    (X : Ω → D T ℝ) (hadapted : ∀ t, Measurable[𝓕 t] (fun ω => X ω t))
    (ε : ℝ) {δ : ℝ} {η : ℝ≥0∞} (hδ : 0 < δ) {K : ℕ}
    (hK : 2 * T < (K : ℝ) * δ)
    (hgap : ∀ k, P {ω | (aldousExitTimes hT (X ω) ε (k + 1) : ℝ) < T ∧
      (aldousExitTimes hT (X ω) ε (k + 1) : ℝ) - aldousExitTimes hT (X ω) ε k ≤ δ} ≤ η) :
    P {ω | (aldousExitTimes hT (X ω) ε K : ℝ) < T} ≤ 2 * η := by
  classical
  let τ (k : ℕ) (ω : Ω) := aldousExitTimes hT (X ω) ε k
  have hm (k) : Measurable (τ k) :=
    (isOptionalTime_aldousExitTimes hT 𝓕 X hadapted ε k).measurable
  have hmv (k) : Measurable (fun ω => (τ k ω : ℝ)) :=
    continuous_subtype_val.measurable.comp (hm k)
  let E : Set Ω := {ω | (τ K ω : ℝ) < T}
  let A (i : Fin K) : Set Ω := {ω | (τ (i + 1) ω : ℝ) < T ∧
    (τ (i + 1) ω : ℝ) - τ i ω ≤ δ}
  have hKpos : 0 < K := by
    by_contra! hz
    have : K = 0 := Nat.eq_zero_of_le_zero hz
    subst K
    simp only [Nat.cast_zero, zero_mul] at hK
    linarith
  let : Nonempty (Fin K) := ⟨⟨0, hKpos⟩⟩
  apply measure_le_two_mul_of_half_cover (ι := Fin K) P (E := E) (η := η)
    (measurableSet_lt (hmv K) measurable_const) A
    (fun i => (measurableSet_lt (hmv (i + 1)) measurable_const).inter
      (measurableSet_le ((hmv (i + 1)).sub (hmv i)) measurable_const))
    (fun i => hgap i)
  intro ω hω
  have hgenuine (i : Fin K) : (τ (i + 1) ω : ℝ) < T := by
    have hle : (τ (i + 1) ω : ℝ) ≤ (τ K ω : ℝ) :=
      (monotone_aldousExitTimes hT (X ω) ε) (show i.val + 1 ≤ K from i.isLt)
    exact hle.trans_lt hω
  have hcard : (Finset.univ.filter fun i : Fin K => ω ∈ A i).card =
      ((Finset.range K).filter fun k => (τ (k + 1) ω : ℝ) - τ k ω ≤ δ).card := by
    have hsum := Fin.sum_univ_eq_sum_range
      (fun k => if (τ (k + 1) ω : ℝ) - τ k ω ≤ δ then (1 : ℕ) else 0) K
    simp only [Finset.sum_boole] at hsum
    convert hsum using 1
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, A, mem_ofPred_eq,
      hgenuine i]
  have hhalf : K ≤ 2 * ((Finset.range K).filter fun k =>
      (τ (k + 1) ω : ℝ) - τ k ω ≤ δ).card :=
    half_le_card_short_aldous_gaps hT (X ω) ε hδ hK
  have htarget : K ≤ 2 * (Finset.univ.filter fun i : Fin K => ω ∈ A i).card :=
    hhalf.trans_eq (congrArg (fun j : ℕ => 2 * j) hcard.symm)
  convert htarget using 1
  · exact Fintype.card_fin K
  · congr 2
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end BGW.Skorokhod
