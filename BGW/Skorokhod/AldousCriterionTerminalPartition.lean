/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.AldousCriterionExits

/-!
# Merging the terminal block of an exit partition

Only genuine exits need to be well separated. If the terminal sentinel is too
close to the last exit, merge the last two blocks. Control of the oscillation
in a deterministic terminal window bounds the resulting block.
-/

@[expose] public section

open Set

namespace BGW.Skorokhod

variable {T : ℝ}

/-- Separated interior cuts and a controlled terminal window give a valid modulus partition,
even if the final gap is short.

Reference: Billingsley 1999, Section 16. -/
private theorem cadlagModulus_le_of_terminal_merge (f : D T ℝ) {ε δ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hδT : 4 * δ < T)
    (τ : ℕ → ℝ) (L : ℕ) (hτ0 : τ 0 = 0) (hτT : τ (L + 1) = T)
    (hτlt : ∀ j ≤ L, τ j < T)
    (hgap : ∀ j < L, 2 * δ < τ (j + 1) - τ j)
    (hosc : ∀ j ≤ L, ∀ s u : Icc (0 : ℝ) T,
      τ j ≤ s → (s : ℝ) < τ (j + 1) → τ j ≤ u → (u : ℝ) < τ (j + 1) →
        |f s - f u| ≤ 2 * ε)
    (hterm : ∀ t : Icc (0 : ℝ) T, T - 2 * δ ≤ t →
      |f t - f ⟨T - 2 * δ, by constructor <;> linarith⟩| ≤ ε) :
    cadlagModulus f δ ≤ 4 * ε := by
  classical
  let K := if 0 < L ∧ T - τ L ≤ δ then L - 1 else L
  have hcases : K = L ∧ δ < T - τ L ∨
      K = 0 ∧ L = 0 ∨ 0 < L ∧ K + 1 = L ∧ T - τ L ≤ δ := by
    by_cases hL : 0 < L
    · by_cases ht : T - τ L ≤ δ
      · right; right
        exact ⟨hL, by dsimp [K]; simp only [hL, ht, and_self, ite_true]; omega, ht⟩
      · left
        exact ⟨by simp only [K, hL, ht, and_false, ite_false], lt_of_not_ge ht⟩
    · right; left
      have hL0 : L = 0 := Nat.eq_zero_of_not_pos hL
      exact ⟨by simp [K, hL0], hL0⟩
  have hKL : K ≤ L := by rcases hcases with h | h | h <;> omega
  let p (i : Fin (K + 2)) : ℝ := if i.val = K + 1 then T else τ i
  have hp0 : p 0 = 0 := by simp [p, hτ0]
  have hpT : p (Fin.last (K + 1)) = T := by simp [p]
  have hpleft (i : Fin (K + 1)) : p i.castSucc = τ i := by
    simp only [p, Fin.val_castSucc, ite_eq_right (by omega : i.val ≠ K + 1)]
  have hpright (i : Fin (K + 1)) : p i.succ = if i.val = K then T else τ (i + 1) := by
    simp only [p, Fin.val_succ, Nat.add_right_cancel_iff]
  have hpstep (i : Fin (K + 1)) : δ < p i.succ - p i.castSucc := by
    rw [hpleft, hpright]
    by_cases hi : i.val = K
    · rw [ite_eq_left hi, hi]
      rcases hcases with h | h | h
      · simpa only [h.1] using h.2
      · simp only [h.1, hτ0]
        linarith
      · have hg := hgap K (by omega)
        rw [h.2.1] at hg
        have hlast := hτlt L le_rfl
        linarith
    · rw [ite_eq_right hi]
      have hg := hgap i (by omega)
      linarith
  have hpmono : StrictMono p := Fin.strictMono_iff_lt_succ.mpr (fun i => by
    have hg := hpstep i
    linarith)
  apply cadlagModulus_le_of_partition f (by positivity) p hp0 hpT hpmono hpstep
  intro i s u hs hs' hu hu'
  rw [hpleft] at hs hu
  rw [hpright] at hs' hu'
  rw [Real.dist_eq]
  by_cases hi : i.val = K
  · rw [ite_eq_left hi] at hs' hu'
    rcases hcases with h | h | h
    · rw [hi, h.1] at hs hu
      exact (hosc L le_rfl s u hs (hs'.trans_eq hτT.symm)
        hu (hu'.trans_eq hτT.symm)).trans (by linarith)
    · have hi0 : i.val = 0 := by omega
      rw [hi0] at hs hu
      have hτ1 : τ 1 = T := by simpa only [h.2] using hτT
      exact (hosc 0 (by omega) s u hs (hs'.trans_eq hτ1.symm)
        hu (hu'.trans_eq hτ1.symm)).trans (by linarith)
    · have hiL : i.val + 1 = L := by omega
      let q : Icc (0 : ℝ) T := ⟨T - 2 * δ, by constructor <;> linarith⟩
      have hqhi : (q : ℝ) < τ L := by dsimp [q]; linarith [h.2.2]
      have hqlo : τ i ≤ q := by
        have hg := hgap i (by omega)
        rw [hiL] at hg
        have hlast := hτlt L le_rfl
        dsimp [q]
        linarith
      have hpoint (v : Icc (0 : ℝ) T) (hv : τ i ≤ v) : |f v - f q| ≤ 2 * ε := by
        by_cases hvL : (v : ℝ) < τ L
        · have hqhi' : (q : ℝ) < τ (i.val + 1) := by rwa [hiL]
          have hvL' : (v : ℝ) < τ (i.val + 1) := by rwa [hiL]
          exact hosc i (by omega) v q hv hvL' hqlo hqhi'
        · have hvq : T - 2 * δ ≤ v := by dsimp [q] at hqhi; linarith
          exact (hterm v hvq).trans (by linarith)
      have hsbound := hpoint s hs
      have hubound := hpoint u hu
      have htri := abs_sub_le (f s) (f q) (f u)
      rw [abs_sub_comm (f q)] at htri
      linarith
  · rw [ite_eq_right hi] at hs' hu'
    exact (hosc i (by omega) s u hs hs' hu hu').trans (by linarith)

/-- Genuine exit gaps suffice for a modulus bound once the terminal window is controlled.

Reference: Billingsley 1999, Section 16. -/
theorem cadlagModulus_le_of_aldous_gaps (hT : 0 < T) (f : D T ℝ) {ε δ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hδT : 4 * δ < T) (K : ℕ)
    (hstop : (aldousExitTimes hT.le f ε K : ℝ) = T)
    (hgap : ∀ j < K, (aldousExitTimes hT.le f ε (j + 1) : ℝ) < T →
      2 * δ < (aldousExitTimes hT.le f ε (j + 1) : ℝ) - aldousExitTimes hT.le f ε j)
    (hterm : ∀ t : Icc (0 : ℝ) T, T - 2 * δ ≤ t →
      |f t - f ⟨T - 2 * δ, by constructor <;> linarith⟩| ≤ ε) :
    cadlagModulus f δ ≤ 4 * ε := by
  let τ := aldousExitTimes hT.le f ε
  have hex : ∃ j, (τ j : ℝ) = T := ⟨K, hstop⟩
  let N := Nat.find hex
  have hNT : (τ N : ℝ) = T := Nat.find_spec hex
  have hNK : N ≤ K := Nat.find_le hstop
  have hbefore (j : ℕ) (hj : j < N) : (τ j : ℝ) < T :=
    lt_of_le_of_ne (τ j).2.2 (Nat.find_min hex hj)
  have hNpos : 0 < N := by
    by_contra! hz
    have hN0 : N = 0 := Nat.eq_zero_of_le_zero hz
    have : (0 : ℝ) = T := by simpa only [hN0, τ, aldousExitTimes] using hNT
    linarith
  let L := N - 1
  have hLN : L + 1 = N := Nat.sub_add_cancel hNpos
  apply cadlagModulus_le_of_terminal_merge f hε hδ hδT (fun j => (τ j : ℝ)) L
    rfl (by simpa only [hLN] using hNT) (fun j hj => hbefore j (by omega))
    (fun j hj => hgap j (by omega) (hbefore (j + 1) (by omega))) ?_ hterm
  intro j _ s u hs hs' hu hu'
  have hsbound : |f s - f (τ j)| ≤ ε :=
    abs_sub_le_before_aldousExitTime f hε hs hs'
  have hubound : |f u - f (τ j)| ≤ ε :=
    abs_sub_le_before_aldousExitTime f hε hu hu'
  have htri := abs_sub_le (f s) (f (τ j)) (f u)
  rw [abs_sub_comm (f (τ j))] at htri
  linarith

end BGW.Skorokhod
