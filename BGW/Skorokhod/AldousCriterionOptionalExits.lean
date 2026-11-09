/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.AldousCriterionExits
public import BGW.Skorokhod.AldousCriterionOptionalEval

import BGW.Skorokhod.StepApprox
import Mathlib.Data.Rat.Encodable

/-!
# Successive exits are optional times

Strict exits have a countable characterization by rational evaluations. Together
with adapted evaluation at optional times, this proves the optional-time property
for every finite stage of the successive-exit construction.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace BGW.Skorokhod

variable {T : ℝ}

/-- The next exit is strictly before `t` exactly when a strict displacement occurs before `t`.

Reference: Billingsley 1999, Section 16. -/
private theorem aldousExitTime_lt_iff (f : D T ℝ) (ε : ℝ) (s t : Icc (0 : ℝ) T) :
    aldousExitTime f ε s < t ↔ ∃ u : Icc (0 : ℝ) T,
      s < u ∧ ε < |f u - f s| ∧ u < t := by
  constructor
  · intro h
    obtain ⟨v, hv, hvt⟩ := (csInf_lt_iff ⟨(s : ℝ), aldousExitSet_lower f ε s⟩
      (aldousExitSet_nonempty f ε s)).mp h
    rcases hv with rfl | ⟨u, hu, rfl⟩
    · exact False.elim ((not_lt_of_ge t.2.2) hvt)
    · exact ⟨u, hu.1, hu.2, hvt⟩
  · rintro ⟨u, hsu, hbig, hut⟩
    have hle := csInf_le ⟨(s : ℝ), aldousExitSet_lower f ε s⟩
      (show (u : ℝ) ∈ aldousExitSet f ε s from Or.inr ⟨u, ⟨hsu, hbig⟩, rfl⟩)
    exact hle.trans_lt hut

/-- Rational evaluations detect strict exits before a fixed time.

Reference: Billingsley 1999, Section 16. -/
private theorem aldousExitTime_lt_iff_rat (f : D T ℝ) (ε : ℝ) (s t : Icc (0 : ℝ) T) :
    aldousExitTime f ε s < t ↔
      ∃ q : {q : ℚ // (q : ℝ) ∈ Icc (0 : ℝ) T ∧ (q : ℝ) < t},
        s < ⟨(q.val : ℝ), q.2.1⟩ ∧ ε < |f ⟨(q.val : ℝ), q.2.1⟩ - f s| := by
  rw [aldousExitTime_lt_iff]
  constructor
  · rintro ⟨u, hsu, hbig, hut⟩
    obtain ⟨d, hd, hclose⟩ := exists_right_oscillation f u (sub_pos.mpr hbig)
    obtain ⟨q, huq, hq⟩ := exists_rat_btwn
      (show (u : ℝ) < min (t : ℝ) ((u : ℝ) + d) from
        lt_min hut (lt_add_of_pos_right _ hd))
    have hqt : (q : ℝ) < t := hq.trans_le (min_le_left _ _)
    have hqd : (q : ℝ) < (u : ℝ) + d := hq.trans_le (min_le_right _ _)
    have hqI : (q : ℝ) ∈ Icc (0 : ℝ) T :=
      ⟨u.2.1.trans huq.le, hqt.le.trans t.2.2⟩
    let v : Icc (0 : ℝ) T := ⟨q, hqI⟩
    have huv : u < v := huq
    refine ⟨⟨q, hqI, hqt⟩, hsu.trans huv, ?_⟩
    have hsmall := hclose v huv.le hqd
    rw [Real.dist_eq, abs_sub_comm (f v)] at hsmall
    have htri := abs_sub_le (f u) (f v) (f s)
    change ε < |f v - f s|
    linarith
  · rintro ⟨q, hsq, hbig⟩
    exact ⟨⟨q.val, q.2.1⟩, hsq, hbig, q.2.2⟩

/-- The next strict exit after an optional time is optional for every adapted càdlàg process.

Reference: Billingsley 1999, Section 16. -/
theorem IsOptionalTime.aldousExitTime {Ω : Type*} {m : MeasurableSpace Ω}
    {𝓕 : Filtration (Icc (0 : ℝ) T) m} {σ : Ω → Icc (0 : ℝ) T}
    (hσ : IsOptionalTime 𝓕 σ) (X : Ω → D T ℝ)
    (hadapted : ∀ t, Measurable[𝓕 t] (fun ω => X ω t)) (ε : ℝ) :
    IsOptionalTime 𝓕 (fun ω => aldousExitTime (X ω) ε (σ ω)) := by
  intro t
  have heq : {ω | BGW.Skorokhod.aldousExitTime (X ω) ε (σ ω) < t} =
      ⋃ q : {q : ℚ // (q : ℝ) ∈ Icc (0 : ℝ) T ∧ (q : ℝ) < t},
        {ω | σ ω < ⟨(q.val : ℝ), q.2.1⟩ ∧
          ε < |X ω ⟨(q.val : ℝ), q.2.1⟩ - X ω (σ ω)|} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, aldousExitTime_lt_iff_rat]
  rw [heq]
  apply MeasurableSet.iUnion
  intro q
  exact 𝓕.mono q.2.2.le _
    (hσ.measurableSet_displacement X hadapted ⟨q.val, q.2.1⟩ ε)

/-- Every finite stage of the successive-exit construction is an optional time.

Reference: Billingsley 1999, Section 16. -/
theorem isOptionalTime_aldousExitTimes {Ω : Type*} {m : MeasurableSpace Ω}
    (hT : 0 ≤ T) (𝓕 : Filtration (Icc (0 : ℝ) T) m) (X : Ω → D T ℝ)
    (hadapted : ∀ t, Measurable[𝓕 t] (fun ω => X ω t)) (ε : ℝ) (k : ℕ) :
    IsOptionalTime 𝓕 (fun ω => aldousExitTimes hT (X ω) ε k) := by
  induction k with
  | zero =>
    intro t
    change MeasurableSet[𝓕 t] {ω : Ω | (⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T) < t}
    exact MeasurableSet.const _
  | succ k ih => exact ih.aldousExitTime X hadapted ε

end BGW.Skorokhod
