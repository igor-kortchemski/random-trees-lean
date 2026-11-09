/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Tightness

import BGW.Skorokhod.StepApprox

/-!
# Deterministic exit partitions for Aldous's criterion

Successive strict exits from balls of radius `ε` control the oscillation by `2 * ε`
on each half-open block. The terminal block is included in the mesh hypothesis:
separation of the genuine exits alone does not ensure an admissible partition.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace BGW.Skorokhod

variable {T : ℝ}

/-- Times of strict exits from the ball about `f s`, together with the terminal sentinel.

Reference: Billingsley 1999, Section 16. -/
def aldousExitSet (f : D T ℝ) (ε : ℝ) (s : Icc (0 : ℝ) T) : Set ℝ :=
  insert T (Subtype.val '' {u : Icc (0 : ℝ) T | s < u ∧ ε < |f u - f s|})

/-- The terminal sentinel makes the exit set nonempty.

Reference: Billingsley 1999, Section 16. -/
theorem aldousExitSet_nonempty (f : D T ℝ) (ε : ℝ) (s : Icc (0 : ℝ) T) :
    (aldousExitSet f ε s).Nonempty := ⟨T, Or.inl rfl⟩

/-- Every candidate exit is at or after the starting time.

Reference: Billingsley 1999, Section 16. -/
theorem aldousExitSet_lower (f : D T ℝ) (ε : ℝ) (s : Icc (0 : ℝ) T) :
    ∀ u ∈ aldousExitSet f ε s, (s : ℝ) ≤ u := by
  intro u hu
  rcases hu with rfl | ⟨v, hv, rfl⟩
  · exact s.2.2
  · exact hv.1.le

/-- First strict exit from the ball of radius `ε` about `f s` after `s`, capped at `T`.

Reference: Billingsley 1999, Section 16. -/
noncomputable def aldousExitTime (f : D T ℝ) (ε : ℝ) (s : Icc (0 : ℝ) T) :
    Icc (0 : ℝ) T := by
  refine ⟨sInf (aldousExitSet f ε s), ?_, ?_⟩
  · exact s.2.1.trans
      (le_csInf (aldousExitSet_nonempty f ε s) (aldousExitSet_lower f ε s))
  · exact csInf_le ⟨(s : ℝ), aldousExitSet_lower f ε s⟩ (Or.inl rfl)

/-- The capped next exit is no earlier than the starting time.

Reference: Billingsley 1999, Section 16. -/
theorem le_aldousExitTime (f : D T ℝ) (ε : ℝ) (s : Icc (0 : ℝ) T) :
    s ≤ aldousExitTime f ε s := by
  exact le_csInf (aldousExitSet_nonempty f ε s) (aldousExitSet_lower f ε s)

/-- Before the next strict exit, the path stays within the prescribed radius.

Reference: Billingsley 1999, Section 16. -/
theorem abs_sub_le_before_aldousExitTime (f : D T ℝ) {ε : ℝ}
    {s u : Icc (0 : ℝ) T} (hε : 0 ≤ ε) (hsu : s ≤ u)
    (hu : u < aldousExitTime f ε s) : |f u - f s| ≤ ε := by
  by_contra! hbad
  have hsu' : s < u := lt_of_le_of_ne hsu (by
    intro heq
    subst u
    have : ε < 0 := by simpa only [sub_self, abs_zero] using hbad
    exact (not_lt_of_ge hε) this)
  have hmem : (u : ℝ) ∈ aldousExitSet f ε s := Or.inr ⟨u, ⟨hsu', hbad⟩, rfl⟩
  have hle := csInf_le ⟨(s : ℝ), aldousExitSet_lower f ε s⟩ hmem
  exact (not_le_of_gt hu) hle

/-- Positive-radius exits strictly advance before the horizon, by right continuity.

Reference: Billingsley 1999, Section 16. -/
theorem lt_aldousExitTime (f : D T ℝ) {ε : ℝ} (hε : 0 < ε)
    {s : Icc (0 : ℝ) T} (hs : (s : ℝ) < T) : s < aldousExitTime f ε s := by
  obtain ⟨d, hd, hclose⟩ := exists_right_oscillation f s hε
  let b := min ((s : ℝ) + d) T
  have hsb : (s : ℝ) < b := lt_min (lt_add_of_pos_right _ hd) hs
  have hb : b ≤ (aldousExitTime f ε s : ℝ) := by
    apply le_csInf (aldousExitSet_nonempty f ε s)
    intro u hu
    rcases hu with rfl | ⟨v, hv, rfl⟩
    · exact min_le_right _ _
    · by_contra! hlt
      have hnear : (v : ℝ) < (s : ℝ) + d := hlt.trans_le (min_le_left _ _)
      have hsmall := hclose v hv.1.le hnear
      rw [Real.dist_eq] at hsmall
      exact (not_lt_of_gt hv.2) hsmall
  exact hsb.trans_le hb

/-- Successive strict exits from balls of radius `ε`, with the terminal time absorbing.

Reference: Billingsley 1999, Section 16. -/
noncomputable def aldousExitTimes (hT : 0 ≤ T) (f : D T ℝ) (ε : ℝ) :
    ℕ → Icc (0 : ℝ) T
  | 0 => ⟨0, le_rfl, hT⟩
  | k + 1 => aldousExitTime f ε (aldousExitTimes hT f ε k)

/-- A finite exit partition, including its terminal gap, bounds the càdlàg modulus.

Reference: Billingsley 1999, Section 16. -/
theorem cadlagModulus_le_of_aldousExitTimes (hT : 0 ≤ T) (f : D T ℝ)
    {ε δ : ℝ} (hε : 0 ≤ ε) {K : ℕ}
    (hterminal : (aldousExitTimes hT f ε K : ℝ) = T)
    (hmono : StrictMono (fun i : Fin (K + 1) => aldousExitTimes hT f ε i))
    (hgap : ∀ i : Fin K,
      δ < (aldousExitTimes hT f ε i.succ : ℝ) - aldousExitTimes hT f ε i.castSucc) :
    cadlagModulus f δ ≤ 2 * ε := by
  apply cadlagModulus_le_of_partition f (by positivity)
    (fun i : Fin (K + 1) => (aldousExitTimes hT f ε i : ℝ))
    rfl hterminal hmono hgap
  intro i s u hs hs' hu hu'
  have hsbound : |f s - f (aldousExitTimes hT f ε i)| ≤ ε :=
    abs_sub_le_before_aldousExitTime f hε hs hs'
  have hubound : |f u - f (aldousExitTimes hT f ε i)| ≤ ε :=
    abs_sub_le_before_aldousExitTime f hε hu hu'
  rw [Real.dist_eq]
  calc
    |f s - f u| ≤ |f s - f (aldousExitTimes hT f ε i)| +
        |f (aldousExitTimes hT f ε i) - f u| := abs_sub_le _ _ _
    _ ≤ 2 * ε := by rw [abs_sub_comm (f (aldousExitTimes hT f ε i))]; linarith

end BGW.Skorokhod
