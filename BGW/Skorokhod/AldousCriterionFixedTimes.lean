/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.AldousCriterionControlTimes
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Fixed-time tightness and compact containment

Finite deterministic control times convert fixed-time tightness and a modulus
estimate into an eventual uniform bound on all path values.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology ENNReal BigOperators

namespace BGW.Skorokhod

variable {T : ℝ}

/-- Fixed-time tightness and a probability bound for the modulus imply compact containment.

Reference: Billingsley 1999, Section 16. -/
theorem exists_eventual_value_bound_of_fixedTimes (hT : 0 < T)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (X : ∀ n, Ω n → D T ℝ)
    (hfixed : ∀ t : Icc (0 : ℝ) T, ∀ η > 0, ∃ c : ℝ,
      limsup (fun n => P n {ω | c ≤ |X n ω t|}) atTop ≤ ENNReal.ofReal η)
    (hmod : ∀ η > 0, ∃ δ, 0 < δ ∧ δ < T ∧ ∃ N : ℕ, ∀ n ≥ N,
      P n {ω | 1 < cadlagModulus (X n ω) δ} ≤ ENNReal.ofReal η) :
    ∀ η > 0, ∃ K : Set ℝ, Bornology.IsBounded K ∧
      ∃ N, ∀ n ≥ N, P n {ω | ∃ t, X n ω t ∉ K} ≤ ENNReal.ofReal η := by
  classical
  intro η hη
  obtain ⟨δ, hδ, hδT, N₀, hmod⟩ := hmod (η / 2) (half_pos hη)
  obtain ⟨S, hS, hcontrol⟩ := exists_finite_aldous_control_times hT hδ hδT
  let : Fintype S := hS.fintype
  let M := Fintype.card S
  let err : ℝ := η / (4 * (M + 1))
  have herr : 0 < err := by dsimp [err]; positivity
  have hpoint (t : S) : ∃ c : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      P n {ω | c ≤ |X n ω t.val|} ≤ ENNReal.ofReal (2 * err) := by
    obtain ⟨c, hc⟩ := hfixed t err herr
    have hlt : limsup (fun n => P n {ω | c ≤ |X n ω t.val|}) atTop <
        ENNReal.ofReal (2 * err) := hc.trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith))
    obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt hlt)
    exact ⟨c, N, fun n hn => (hN n hn).le⟩
  choose c N hprob using hpoint
  obtain ⟨C, hC⟩ := (finite_range c).bddAbove
  have hc (t : S) : c t ≤ C := hC (mem_range_self t)
  let r := max C 0 + 2
  refine ⟨Icc (-r) r, Metric.isBounded_Icc _ _, max N₀ (Finset.univ.sup N), fun n hn => ?_⟩
  have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
  have hnS (t : S) : N t ≤ n :=
    (Finset.le_sup (Finset.mem_univ t)).trans ((le_max_right _ _).trans hn)
  let B (t : S) : Set (Ω n) := {ω | c t ≤ |X n ω t.val|}
  have hsum : P n (⋃ t, B t) ≤ ENNReal.ofReal (η / 2) := by
    have hreal : (M : ℝ) * (2 * err) ≤ η / 2 := by
      have hcancel : (4 * ((M : ℝ) + 1)) * err = η := by dsimp [err]; field_simp
      nlinarith [herr.le]
    calc
      P n (⋃ t, B t) ≤ ∑ t, P n (B t) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _t : S, ENNReal.ofReal (2 * err) :=
        Finset.sum_le_sum fun t _ => hprob t n (hnS t)
      _ = ENNReal.ofReal ((M : ℝ) * (2 * err)) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        change (M : ℝ≥0∞) * ENNReal.ofReal (2 * err) =
          ENNReal.ofReal ((M : ℝ) * (2 * err))
        rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ M from Nat.cast_nonneg M),
          ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (η / 2) := ENNReal.ofReal_le_ofReal hreal
  have hsub : {ω | ∃ t, X n ω t ∉ Icc (-r) r} ⊆
      {ω | 1 < cadlagModulus (X n ω) δ} ∪ ⋃ t, B t := by
    rintro ω ⟨t, ht⟩
    by_cases hm : 1 < cadlagModulus (X n ω) δ
    · exact Or.inl hm
    · right
      by_contra hnot
      have hvalues : ∀ s ∈ S, |X n ω s| ≤ max C 0 := by
        intro s hs
        have hb : ¬ c ⟨s, hs⟩ ≤ |X n ω s| := fun h =>
          hnot (mem_iUnion.mpr ⟨⟨s, hs⟩, h⟩)
        exact (lt_of_not_ge hb).le.trans ((hc ⟨s, hs⟩).trans (le_max_left _ _))
      have hb := hcontrol (X n ω) (max C 0) hvalues (le_of_not_gt hm) t
      exact ht (abs_le.mp hb)
  calc
    P n {ω | ∃ t, X n ω t ∉ Icc (-r) r} ≤
        P n ({ω | 1 < cadlagModulus (X n ω) δ} ∪ ⋃ t, B t) := measure_mono hsub
    _ ≤ P n {ω | 1 < cadlagModulus (X n ω) δ} + P n (⋃ t, B t) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := add_le_add (hmod n hn₀) hsum
    _ = ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_add (half_pos hη).le (half_pos hη).le]
      congr 1
      ring

end BGW.Skorokhod
