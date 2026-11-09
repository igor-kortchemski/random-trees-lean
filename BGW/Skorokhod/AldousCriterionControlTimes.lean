/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Tightness

import BGW.Skorokhod.TightnessMatching

/-!
# Finite deterministic control times

A finite net of the time interval meets every block of a partition whose gaps
exceed `δ`. A modulus bound therefore turns bounds at finitely many deterministic
times, including the horizon, into a bound at every time.
-/

@[expose] public section

open Set

namespace BGW.Skorokhod

variable {T : ℝ}

/-- A fixed finite set of time evaluations controls the supremum of every path with
`cadlagModulus f δ ≤ 1`.

Reference: Billingsley 1999, Section 16. -/
theorem exists_finite_aldous_control_times (hT : 0 < T) {δ : ℝ}
    (hδ : 0 < δ) (hδT : δ < T) :
    ∃ S : Set (Icc (0 : ℝ) T), S.Finite ∧
      ∀ f : D T ℝ, ∀ c : ℝ, (∀ t ∈ S, |f t| ≤ c) →
        cadlagModulus f δ ≤ 1 → ∀ t, |f t| ≤ c + 2 := by
  classical
  obtain ⟨C, hC, hcover⟩ := Metric.totallyBounded_iff.mp
    (isCompact_univ : IsCompact (univ : Set (Icc (0 : ℝ) T))).totallyBounded
    (δ / 4) (by positivity)
  let top : Icc (0 : ℝ) T := ⟨T, hT.le, le_rfl⟩
  refine ⟨insert top C, hC.insert top, fun f c hc hmod t => ?_⟩
  by_cases ht : (t : ℝ) = T
  · have heq : t = top := Subtype.ext ht
    have hb := hc top (mem_insert _ _)
    rw [heq]
    linarith
  · obtain ⟨r, p, hp0, hpT, hp, hgap, hosc⟩ :=
      exists_partition_of_cadlagModulus_lt f hδ hδT
        (hmod.trans_lt (by norm_num : (1 : ℝ) < 2))
    obtain ⟨i, hi, hi'⟩ := exists_halfOpen_partition_block p
      (by simpa only [hp0] using t.2.1) (by
        rw [hpT]
        exact lt_of_le_of_ne t.2.2 ht)
    have hleft : 0 ≤ p i.castSucc := by
      rw [← hp0]
      exact hp.monotone (Fin.zero_le _)
    have hright : p i.succ ≤ T := by
      rw [← hpT]
      exact hp.monotone (Fin.le_last _)
    let mid : Icc (0 : ℝ) T := ⟨(p i.castSucc + p i.succ) / 2,
      by constructor <;> linarith [hgap i]⟩
    obtain ⟨q, hqC, hq⟩ := mem_iUnion₂.mp (hcover (mem_univ mid))
    have hdist : |(mid : ℝ) - q| < δ / 4 := by
      simpa only [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] using hq
    have hqleft : p i.castSucc ≤ q := by
      have := (abs_lt.mp hdist).2
      dsimp [mid] at this
      linarith [hgap i]
    have hqright : (q : ℝ) < p i.succ := by
      have := (abs_lt.mp hdist).1
      dsimp [mid] at this
      linarith [hgap i]
    have hsmall := hosc i t q hi hi' hqleft hqright
    rw [Real.dist_eq] at hsmall
    have hb := hc q (mem_insert_of_mem _ hqC)
    have htri := abs_sub_le (f t) (f q) 0
    simp only [sub_zero] at htri
    linarith

end BGW.Skorokhod
