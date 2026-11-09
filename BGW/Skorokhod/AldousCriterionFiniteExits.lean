/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.AldousCriterionExits

import BGW.Skorokhod.StepApprox
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Finiteness of successive exits

At a nonterminal exit the displacement is at least the radius. Infinitely many
positive-radius exits would accumulate from the left, contradicting the left
limit of the càdlàg path.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace BGW.Skorokhod

variable {T : ℝ}

/-- At a nonterminal strict exit, the displacement is at least the exit radius.

Reference: Billingsley 1999, Section 16. -/
theorem le_abs_sub_aldousExitTime (f : D T ℝ) (ε : ℝ) (s : Icc (0 : ℝ) T)
    (hterminal : (aldousExitTime f ε s : ℝ) < T) :
    ε ≤ |f (aldousExitTime f ε s) - f s| := by
  by_contra! hsmall
  let a := aldousExitTime f ε s
  obtain ⟨d, hd, hclose⟩ := exists_right_oscillation f a (sub_pos.mpr hsmall)
  let b := min ((a : ℝ) + d) T
  have hab : (a : ℝ) < b := lt_min (lt_add_of_pos_right _ hd) hterminal
  have hba : b ≤ (a : ℝ) := by
    apply le_csInf (aldousExitSet_nonempty f ε s)
    intro u hu
    rcases hu with rfl | ⟨v, hv, rfl⟩
    · exact min_le_right _ _
    · by_contra! hlt
      have hav : a ≤ v := csInf_le ⟨(s : ℝ), aldousExitSet_lower f ε s⟩
        (Or.inr ⟨v, hv, rfl⟩)
      have hnear : (v : ℝ) < (a : ℝ) + d := hlt.trans_le (min_le_left _ _)
      have hdist := hclose v hav hnear
      rw [Real.dist_eq] at hdist
      have htri := abs_sub_le (f v) (f a) (f s)
      change |f a - f s| < ε at hsmall
      linarith [hv.2]
  exact (not_le_of_gt hab) hba

/-- If a strict displacement occurs, the capped exit also has a large displacement,
including when the exit is at the horizon.

Reference: Billingsley 1999, Section 16. -/
theorem le_abs_sub_aldousExitTime_of_exists (f : D T ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (s : Icc (0 : ℝ) T) (hex : ∃ u : Icc (0 : ℝ) T, s ≤ u ∧ ε < |f u - f s|) :
    ε ≤ |f (aldousExitTime f ε s) - f s| := by
  by_cases ht : (aldousExitTime f ε s : ℝ) < T
  · exact le_abs_sub_aldousExitTime f ε s ht
  · have htop : (aldousExitTime f ε s : ℝ) = T :=
      le_antisymm (aldousExitTime f ε s).2.2 (le_of_not_gt ht)
    obtain ⟨u, hsu, hbig⟩ := hex
    have hu : u ≤ aldousExitTime f ε s := by
      change (u : ℝ) ≤ (aldousExitTime f ε s : ℝ)
      exact u.2.2.trans_eq htop.symm
    by_cases hlt : u < aldousExitTime f ε s
    · exact False.elim ((not_lt_of_ge
        (abs_sub_le_before_aldousExitTime f hε hsu hlt)) hbig)
    · have heq : u = aldousExitTime f ε s := le_antisymm hu (le_of_not_gt hlt)
      simpa only [heq] using hbig.le

/-- Successive capped exits form a nondecreasing sequence.

Reference: Billingsley 1999, Section 16. -/
theorem monotone_aldousExitTimes (hT : 0 ≤ T) (f : D T ℝ) (ε : ℝ) :
    Monotone (aldousExitTimes hT f ε) := by
  apply monotone_nat_of_le_succ
  intro k
  exact le_aldousExitTime f ε _

/-- Only finitely many positive-radius exits occur before a compact horizon.

Reference: Billingsley 1999, Section 16. -/
theorem exists_aldousExitTimes_eq_terminal (hT : 0 ≤ T) (f : D T ℝ)
    {ε : ℝ} (hε : 0 < ε) : ∃ K, (aldousExitTimes hT f ε K : ℝ) = T := by
  by_contra! hnot
  let τ := aldousExitTimes hT f ε
  have hbefore (k) : (τ k : ℝ) < T := lt_of_le_of_ne (τ k).2.2 (hnot k)
  have hstrict : StrictMono τ := by
    apply strictMono_nat_of_lt_succ
    exact fun k => lt_aldousExitTime f hε (hbefore k)
  have hbdd : BddAbove (range fun k => (τ k : ℝ)) :=
    ⟨T, forall_mem_range.mpr fun k => (τ k).2.2⟩
  let a : Icc (0 : ℝ) T := ⟨⨆ k, (τ k : ℝ),
    le_ciSup_of_le hbdd 0 (τ 0).2.1, ciSup_le fun k => (τ k).2.2⟩
  have hlim : Tendsto τ atTop (𝓝 a) := tendsto_subtype_rng.mpr
    (tendsto_atTop_ciSup (fun i j hij => hstrict.monotone hij) hbdd)
  have hlt (k) : τ k < a := (hstrict (Nat.lt_succ_self k)).trans_le
    (le_ciSup hbdd (k + 1))
  have hleft : Tendsto τ atTop (𝓝[<] a) := tendsto_nhdsWithin_iff.mpr
    ⟨hlim, Eventually.of_forall hlt⟩
  have hpath := ((isCadlag f).tendsto_nhdsLT_leftLim a).comp hleft
  have hdiff : Tendsto (fun k => |f (τ (k + 1)) - f (τ k)|) atTop (𝓝 0) := by
    convert ((hpath.comp (tendsto_add_atTop_nat 1)).sub hpath).abs using 1 <;> simp
  obtain ⟨k, hk⟩ := (hdiff.eventually (gt_mem_nhds hε)).exists
  have hlower : ε ≤ |f (τ (k + 1)) - f (τ k)| :=
    le_abs_sub_aldousExitTime f ε (τ k) (hbefore (k + 1))
  exact (not_lt_of_ge hlower) hk

end BGW.Skorokhod
