/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.AldousCriterionBasic
public import Mathlib.Algebra.Order.Floor.Semiring

import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Optional times and strict upward discretization

The convention for optional times here is measurability of `{σ < t}` at time `t`.
Strict upward rounding is necessary: ordinary ceiling rounding fixes grid points
and can retain a failure of measurability of `{σ ≤ t}`.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace BGW.Skorokhod

variable {T : ℝ} {Ω : Type*} {m : MeasurableSpace Ω}

/-- An optional time in the strict sublevel-set convention, without regularity of the filtration.

Reference: Billingsley 1999, Section 16. -/
def IsOptionalTime (𝓕 : Filtration (Icc (0 : ℝ) T) m) (σ : Ω → Icc (0 : ℝ) T) : Prop :=
  ∀ t, MeasurableSet[𝓕 t] {ω | σ ω < t}

/-- An optional time is measurable for the ambient σ-algebra.

Reference: Billingsley 1999, Section 16. -/
theorem IsOptionalTime.measurable {𝓕 : Filtration (Icc (0 : ℝ) T) m}
    {σ : Ω → Icc (0 : ℝ) T} (hσ : IsOptionalTime 𝓕 σ) : Measurable σ :=
  measurable_of_Iio fun t => 𝓕.le t _ (hσ t)

/-- Strict upward dyadic rounding, capped at the horizon.

Reference: Billingsley 1999, Section 16. -/
noncomputable def aldousRoundTime (hT : 0 ≤ T) (j : ℕ) (t : Icc (0 : ℝ) T) :
    Icc (0 : ℝ) T :=
  ⟨min (((⌊(2 : ℝ) ^ j * (t : ℝ)⌋₊ + 1 : ℕ) : ℝ) / (2 : ℝ) ^ j) T,
    le_min (by positivity) hT, min_le_right _ _⟩

/-- Strict upward rounding never moves a time backwards.

Reference: Billingsley 1999, Section 16. -/
theorem le_aldousRoundTime (hT : 0 ≤ T) (j : ℕ) (t : Icc (0 : ℝ) T) :
    t ≤ aldousRoundTime hT j t := by
  apply le_min _ t.2.2
  apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ j)).mpr
  simpa [mul_comm] using (Nat.lt_floor_add_one ((2 : ℝ) ^ j * (t : ℝ))).le

/-- The rounded time is strictly later whenever the original time precedes the horizon.

Reference: Billingsley 1999, Section 16. -/
private theorem lt_aldousRoundTime (hT : 0 ≤ T) (j : ℕ) {t : Icc (0 : ℝ) T}
    (ht : (t : ℝ) < T) : t < aldousRoundTime hT j t := by
  apply lt_min _ ht
  apply (lt_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ j)).mpr
  simpa [mul_comm] using Nat.lt_floor_add_one ((2 : ℝ) ^ j * (t : ℝ))

/-- At a fixed mesh level the rounded times take only finitely many values.

Reference: Billingsley 1999, Section 16. -/
private theorem finite_range_aldousRoundTime (hT : 0 ≤ T) (j : ℕ) :
    (range (aldousRoundTime hT j)).Finite := by
  let N := ⌊(2 : ℝ) ^ j * T⌋₊
  let g (k : Fin (N + 1)) : Icc (0 : ℝ) T :=
    ⟨min (((k.val + 1 : ℕ) : ℝ) / (2 : ℝ) ^ j) T,
      le_min (by positivity) hT, min_le_right _ _⟩
  apply (finite_range g).subset
  rintro _ ⟨t, rfl⟩
  have hk : ⌊(2 : ℝ) ^ j * (t : ℝ)⌋₊ < N + 1 :=
    Nat.lt_succ_of_le (Nat.floor_mono (mul_le_mul_of_nonneg_left t.2.2 (by positivity)))
  exact ⟨⟨_, hk⟩, rfl⟩

/-- Rounding an optional time strictly upwards gives a stopping time.

Reference: Billingsley 1999, Section 16. -/
theorem IsOptionalTime.isStopTime_aldousRoundTime
    {𝓕 : Filtration (Icc (0 : ℝ) T) m} {σ : Ω → Icc (0 : ℝ) T}
    (hσ : IsOptionalTime 𝓕 σ) (hT : 0 ≤ T) (j : ℕ) :
    IsStopTime 𝓕 (fun ω => aldousRoundTime hT j (σ ω)) := by
  intro t
  by_cases ht : (t : ℝ) = T
  · have hall : ∀ ω, aldousRoundTime hT j (σ ω) ≤ t := by
      intro ω
      exact (aldousRoundTime hT j (σ ω)).2.2.trans_eq ht.symm
    simp only [hall, Set.ofPred_true, MeasurableSet.univ]
  · have htT : (t : ℝ) < T := lt_of_le_of_ne t.2.2 ht
    let a : ℝ := (2 : ℝ) ^ j
    have ha : 0 < a := by dsimp [a]; positivity
    let b : Icc (0 : ℝ) T := ⟨(⌊a * (t : ℝ)⌋₊ : ℝ) / a,
      by positivity,
      (div_le_iff₀ ha).mpr ((Nat.floor_le (mul_nonneg ha.le t.2.1)).trans
        (by nlinarith [t.2.2]))⟩
    have hbt : b ≤ t := (div_le_iff₀ ha).mpr (by
      simpa [mul_comm] using Nat.floor_le (mul_nonneg ha.le t.2.1))
    have heq : {ω | aldousRoundTime hT j (σ ω) ≤ t} = {ω | σ ω < b} := by
      ext ω
      change min (((⌊a * (σ ω : ℝ)⌋₊ + 1 : ℕ) : ℝ) / a) T ≤ (t : ℝ) ↔
        (σ ω : ℝ) < (⌊a * (t : ℝ)⌋₊ : ℝ) / a
      rw [min_le_iff, or_iff_left (not_le_of_gt htT), div_le_iff₀ ha,
        ← Nat.le_floor_iff (mul_nonneg t.2.1 ha.le), ← Nat.lt_iff_add_one_le,
        Nat.floor_lt (mul_nonneg ha.le (σ ω).2.1), lt_div_iff₀ ha]
      simp only [mul_comm]
    rw [heq]
    exact 𝓕.mono hbt _ (hσ b)

/-- The rounding error is at most the grid size.

Reference: Billingsley 1999, Section 16. -/
private theorem aldousRoundTime_sub_le (hT : 0 ≤ T) (j : ℕ) (t : Icc (0 : ℝ) T) :
    (aldousRoundTime hT j t : ℝ) - t ≤ ((2 : ℝ) ^ j)⁻¹ := by
  have ha : 0 < (2 : ℝ) ^ j := by positivity
  have hfloor := Nat.floor_le (mul_nonneg ha.le t.2.1)
  have hupper : (aldousRoundTime hT j t : ℝ) ≤
      (((⌊(2 : ℝ) ^ j * (t : ℝ)⌋₊ + 1 : ℕ) : ℝ) / (2 : ℝ) ^ j) := min_le_left _ _
  have hraw : (((⌊(2 : ℝ) ^ j * (t : ℝ)⌋₊ + 1 : ℕ) : ℝ) / (2 : ℝ) ^ j) ≤
      (t : ℝ) + ((2 : ℝ) ^ j)⁻¹ := by
    rw [div_le_iff₀ ha]
    push_cast
    field_simp
    nlinarith
  linarith

/-- Strict upward dyadic rounding converges to the original time.

Reference: Billingsley 1999, Section 16. -/
theorem tendsto_aldousRoundTime (hT : 0 ≤ T) (t : Icc (0 : ℝ) T) :
    Tendsto (fun j => aldousRoundTime hT j t) atTop (𝓝 t) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hlim : Tendsto (fun j : ℕ => ((2 : ℝ) ^ j)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  refine squeeze_zero (fun _ => dist_nonneg) (fun j => ?_) hlim
  rw [Subtype.dist_eq, Real.dist_eq,
    abs_of_nonneg (sub_nonneg.mpr
      (show (t : ℝ) ≤ (aldousRoundTime hT j t : ℝ) from le_aldousRoundTime hT j t))]
  exact aldousRoundTime_sub_le hT j t

/-- Evaluation along rounded times converges by right continuity, including at the horizon.

Reference: Billingsley 1999, Section 16. -/
theorem tendsto_eval_aldousRoundTime (hT : 0 ≤ T) (f : D T ℝ) (t : Icc (0 : ℝ) T) :
    Tendsto (fun j => f (aldousRoundTime hT j t)) atTop (𝓝 (f t)) := by
  by_cases ht : (t : ℝ) = T
  · have heq (j) : aldousRoundTime hT j t = t :=
      le_antisymm (by exact (aldousRoundTime hT j t).2.2.trans_eq ht.symm)
        (le_aldousRoundTime hT j t)
    simp only [heq]
    exact tendsto_const_nhds
  · apply ((isCadlag f).isRightContinuous t).tendsto.comp
    exact tendsto_nhdsWithin_iff.mpr ⟨tendsto_aldousRoundTime hT t,
      Eventually.of_forall fun j => lt_aldousRoundTime hT j (lt_of_le_of_ne t.2.2 ht)⟩

end BGW.Skorokhod
