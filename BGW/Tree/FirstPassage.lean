/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree.ForestCycle
import Lean.Elab.Tactic.Omega

/-!
# First-passage decomposition of forest bridge words

For `ℓ ≥ 1`, a word of length `N`, entries at least `-1` and sum `-ℓ` has a first time `q ≤ N` at
which its prefix sum equals `-ℓ`. Its prefix of length `q` is then a forest code, and the remaining
suffix is a word of length `N - q`, entries at least `-1` and sum `0`. Conversely a forest code
followed by such a suffix is a word of length `N` with sum `-ℓ`, and `q` is recovered as the length
of the code (the first passage time is unique). Since the walk weight is multiplicative under
concatenation, this gives, for arbitrary step masses `p` and every `N`,

`∑ weight(forestBridgeWords ℓ N)
  = ∑_{q ≤ N} forestWeight p ℓ q * ∑ weight(forestBridgeWords 0 (N - q))`

(`tsum_forestBridgeWords_eq_sum`). The suffixes are the words of `forestBridgeWords 0 (N - q)`, the
bridges back to level `0`. No criticality, positivity or lattice hypothesis is used. Adapted from
`PoissonDeclumping/Bridge/Kemperman.lean` (`firstPassageAt_take_unique`, `walkMass_neg_eq_sum`);
the measure statement is in `BGW.LocallyFinite.FirstPassageLaw`.
-/

@[expose] public section

namespace BGW

open scoped ENNReal

/-- The walk weight is multiplicative under concatenation. -/
theorem walkWeight_append (p : ℕ → ℝ≥0∞) (a b : List ℤ) :
    walkWeight p (a ++ b) = walkWeight p a * walkWeight p b := by
  simp [walkWeight, List.map_append, List.prod_append]

/-- The first passage time to `-ℓ` is unique: two prefixes of a word that are forest codes
have the same length. -/
theorem length_eq_of_isForestCode_take {x : List ℤ} {ℓ q q' : ℕ} (hq : q ≤ x.length)
    (hq' : q' ≤ x.length) (h : IsForestCode ℓ (x.take q)) (h' : IsForestCode ℓ (x.take q')) :
    q = q' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := h'.2.2 q (by rw [List.length_take]; omega)
    rw [List.take_take, min_eq_left hlt.le, h.2.1] at this
    exact lt_irrefl _ this
  · have := h.2.2 q' (by rw [List.length_take]; omega)
    rw [List.take_take, min_eq_left hlt.le, h'.2.1] at this
    exact lt_irrefl _ this

/-- A word of length `N`, entries at least `-1` and sum `-ℓ` (`ℓ ≥ 0`) whose prefix of length `q`
is a forest code: the words cut at the first passage time `q`. -/
def firstPassageWords (ℓ N q : ℕ) : Set (List ℤ) :=
  {x | x ∈ forestBridgeWords ℓ N ∧ q ≤ N ∧ IsForestCode ℓ (x.take q)}

/-- Cutting a word at `q` is the same as a forest code of length `q` followed by a bridge of
length `N - q` at level `0`. -/
theorem mem_firstPassageWords_iff {ℓ N q : ℕ} (hq : q ≤ N) (x : List ℤ) :
    x ∈ firstPassageWords ℓ N q ↔
      (IsForestCode ℓ (x.take q) ∧ (x.take q).length = q) ∧
        x.drop q ∈ forestBridgeWords 0 (N - q) := by
  constructor
  · rintro ⟨⟨hlen, hge, hsum⟩, -, hcode⟩
    have htake : (x.take q).length = q := by rw [List.length_take]; omega
    refine ⟨⟨hcode, htake⟩, ?_, fun a ha => hge a (List.mem_of_mem_drop ha), ?_⟩
    · rw [List.length_drop]; omega
    · have h1 := List.sum_take_add_sum_drop x q
      rw [hcode.2.1, hsum] at h1
      simp only [Nat.cast_zero, neg_zero]
      omega
  · rintro ⟨⟨hcode, htake⟩, hlen, hge, hsum⟩
    simp only [Nat.cast_zero, neg_zero] at hsum
    have hxlen : x.length = N := by
      rw [List.length_drop] at hlen
      have : q ≤ x.length := by rw [List.length_take] at htake; omega
      omega
    refine ⟨⟨hxlen, fun a ha => ?_, ?_⟩, hq, hcode⟩
    · rw [← List.take_append_drop q x, List.mem_append] at ha
      exact ha.elim (hcode.1 a) (hge a)
    · rw [← List.sum_take_add_sum_drop x q, hcode.2.1, hsum]
      simp

/-- The sets `firstPassageWords ℓ N q`, `q ≤ N`, partition the words of `forestBridgeWords ℓ N`
(`1 ≤ ℓ` is not needed: for `ℓ = 0` the cut is at `q = 0`). -/
theorem sum_indicator_firstPassageWords {ℓ N : ℕ} (F : List ℤ → ℝ≥0∞) (x : List ℤ) :
    ∑ q ∈ Finset.range (N + 1), Set.indicator (firstPassageWords ℓ N q) F x =
      Set.indicator (forestBridgeWords ℓ N) F x := by
  by_cases hx : x ∈ forestBridgeWords ℓ N
  · obtain ⟨hlen, hge, hsum⟩ := hx
    obtain ⟨l, hlN, hl, hlt⟩ := exists_first_sum_take_eq hge (v := -(ℓ : ℤ)) (b := N)
      (by omega) (by rw [List.take_of_length_le (by omega), hsum])
    have hmem : x ∈ firstPassageWords ℓ N l := by
      refine ⟨⟨hlen, hge, hsum⟩, hlN, fun a ha => hge a (List.mem_of_mem_take ha), hl, ?_⟩
      intro i hi
      rw [List.length_take] at hi
      rw [List.take_take, min_eq_left (by omega)]
      exact hlt i (by omega)
    rw [Finset.sum_eq_single l, Set.indicator_of_mem hmem,
      Set.indicator_of_mem (show x ∈ forestBridgeWords ℓ N from ⟨hlen, hge, hsum⟩)]
    · intro q hq hne
      refine Set.indicator_of_notMem (fun h => hne ?_) _
      have := Finset.mem_range.mp hq
      exact length_eq_of_isForestCode_take (by omega) (by omega) h.2.2 hmem.2.2
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  · rw [Set.indicator_of_notMem hx]
    exact Finset.sum_eq_zero fun q _ => Set.indicator_of_notMem (fun h => hx h.1) _

/-- The total walk weight of the words cut at `q` factors as forest codes times bridges at level
`0`. -/
theorem tsum_firstPassageWords_walkWeight (p : ℕ → ℝ≥0∞) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {N q : ℕ}
    (hq : q ≤ N) :
    ∑' x : List ℤ, Set.indicator (firstPassageWords ℓ N q) (walkWeight p) x =
      forestWeight p ℓ q *
        ∑' x : List ℤ, Set.indicator (forestBridgeWords 0 (N - q)) (walkWeight p) x := by
  set C : Set (List ℤ) := {x | IsForestCode ℓ x ∧ x.length = q} with hC
  set B : Set (List ℤ) := forestBridgeWords 0 (N - q) with hB
  set g : List ℤ → List ℤ × List ℤ := fun x => (x.take q, x.drop q) with hg
  set f : List ℤ × List ℤ → ℝ≥0∞ := fun s =>
    Set.indicator C (walkWeight p) s.1 * Set.indicator B (walkWeight p) s.2 with hf
  have hginj : Function.Injective g := fun x y h => by
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [hg] at h1 h2
    rw [← List.take_append_drop q x, ← List.take_append_drop q y, h1, h2]
  have hrange : Function.support f ⊆ Set.range g := by
    intro s hs
    have hs1 : s.1 ∈ C := by
      by_contra h
      exact hs (by simp [hf, Set.indicator_of_notMem h])
    exact ⟨s.1 ++ s.2, Prod.ext (List.take_left' hs1.2) (List.drop_left' hs1.2)⟩
  have hpoint : ∀ x : List ℤ, Set.indicator (firstPassageWords ℓ N q) (walkWeight p) x =
      f (g x) := by
    intro x
    by_cases hx : x ∈ firstPassageWords ℓ N q
    · obtain ⟨h1, h2⟩ := (mem_firstPassageWords_iff hq x).mp hx
      rw [Set.indicator_of_mem hx]
      simp only [hf, hg]
      rw [Set.indicator_of_mem (show x.take q ∈ C from h1),
        Set.indicator_of_mem (show x.drop q ∈ B from h2), ← walkWeight_append,
        List.take_append_drop]
    · have : ¬ (x.take q ∈ C ∧ x.drop q ∈ B) := fun h =>
        hx ((mem_firstPassageWords_iff hq x).mpr h)
      rw [Set.indicator_of_notMem hx]
      simp only [hf, hg]
      by_cases h1 : x.take q ∈ C
      · rw [Set.indicator_of_notMem (fun h2 => this ⟨h1, h2⟩), mul_zero]
      · rw [Set.indicator_of_notMem h1, zero_mul]
  rw [tsum_congr hpoint, hginj.tsum_eq hrange, hf, ENNReal.tsum_prod' (f := f)]
  simp only [hf]
  rw [forestWeight_eq_tsum_codes p hℓ q, ← hC]
  simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

/-- **First-passage decomposition of the walk weights.** For `1 ≤ ℓ`, every `N` and every
`p : ℕ → ℝ≥0∞`, the total weight of the words of length `N`, entries at least `-1` and sum `-ℓ`
is the sum over the first passage time `q ≤ N` of `forestWeight p ℓ q` times the total weight of
the words of length `N - q`, entries at least `-1` and sum `0`. -/
theorem tsum_forestBridgeWords_eq_sum (p : ℕ → ℝ≥0∞) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (N : ℕ) :
    ∑' x : List ℤ, Set.indicator (forestBridgeWords ℓ N) (walkWeight p) x =
      ∑ q ∈ Finset.range (N + 1), forestWeight p ℓ q *
        ∑' x : List ℤ, Set.indicator (forestBridgeWords 0 (N - q)) (walkWeight p) x := by
  have h : ∀ x : List ℤ, Set.indicator (forestBridgeWords ℓ N) (walkWeight p) x =
      ∑ q ∈ Finset.range (N + 1), Set.indicator (firstPassageWords ℓ N q) (walkWeight p) x :=
    fun x => (sum_indicator_firstPassageWords _ x).symm
  rw [tsum_congr h, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact Finset.sum_congr rfl fun q hq =>
    tsum_firstPassageWords_walkWeight p hℓ (by have := Finset.mem_range.mp hq; omega)

end BGW
