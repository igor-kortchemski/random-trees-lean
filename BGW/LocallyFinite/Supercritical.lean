/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.LocallyFinite.Normalization

/-!
# Classification of the extinction probability by the mean

Let `q = bienaymeLaw μ {T | FiniteVertices T}` be the probability that the tree is finite, for an
offspring probability measure `μ` with mean `∫⁻ k, k ∂μ` in `[0, ∞]` (infinite mean allowed).

* `q ≤ s` as soon as `offspringGF μ s ≤ s` (a sub-fixed point bounds the iterates from above);
* if the mean exceeds one, there is `s < 1` with `offspringGF μ s ≤ s`
  (`exists_lt_one_offspringGF_le`), hence `q < 1` (`bienaymeLaw_finiteVertices_lt_one`);
* `q = 1` exactly when the mean is at most one and `μ {1} ≠ 1`
  (`bienaymeLaw_finiteVertices_eq_one_iff`): for `μ {1} = 1` the tree is an infinite line and
  `q = 0`.

No source in `PoissonDeclumping` states the supercritical case, which the paper does not need.
Convexity and derivatives are not used: the bound `1 - f x ≥ x ^ N (1 - x) M` comes from the
elementary inequality `k x ^ N (1 - x) ≤ 1 - x ^ k` for `k ≤ N`.
-/

@[expose] public section

namespace BGW.LocallyFinite

open MeasureTheory
open scoped ENNReal

/-- A sub-fixed point of the generating function bounds the probability of finiteness from
above. -/
theorem bienaymeLaw_finiteVertices_le_of_offspringGF_le (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {s : ℝ≥0∞} (hs : offspringGF μ s ≤ s) : bienaymeLaw μ {T | FiniteVertices T} ≤ s := by
  rw [bienaymeLaw_finiteVertices_eq_iSup]
  refine iSup_le fun n => ?_
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (offspringGF_mono μ ih).trans hs

/-- **Supercritical case.** For every offspring probability measure of mean greater than one,
possibly infinite, the tree is infinite with positive probability: `q < 1`. -/
theorem bienaymeLaw_finiteVertices_lt_one (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : 1 < ∫⁻ k : ℕ, (k : ℝ≥0∞) ∂μ) : bienaymeLaw μ {T | FiniteVertices T} < 1 := by
  rw [lintegral_countable'] at hm
  obtain ⟨s, hs1, hs⟩ := exists_lt_one_offspringGF_le μ hm
  exact (bienaymeLaw_finiteVertices_le_of_offspringGF_le μ hs).trans_lt hs1

/-- For `μ {1} = 1` the tree is an infinite line: the probability of finiteness is zero. -/
theorem bienaymeLaw_finiteVertices_eq_zero_of_singleton_one (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (h1 : μ {1} = 1) :
    bienaymeLaw μ {T | FiniteVertices T} = 0 := by
  have h0 : μ {0} = 0 := by
    have hle : μ {0} + μ {1} ≤ 1 := by
      rw [← measure_union (by simp) (measurableSet_singleton _)]
      exact prob_le_one
    rw [h1] at hle
    have h : μ {0} + 1 ≤ 0 + 1 := by simpa using hle
    exact nonpos_iff_eq_zero.1 ((ENNReal.add_le_add_iff_right ENNReal.one_ne_top).1 h)
  exact nonpos_iff_eq_zero.1 (bienaymeLaw_finiteVertices_le_of_offspringGF_le μ
    (s := 0) (by rw [offspringGF_zero, h0]))

/-- **Classification.** The probability that the tree is finite is `1` exactly when the mean is at
most one and `μ {1} ≠ 1`; otherwise it is `< 1`. -/
theorem bienaymeLaw_finiteVertices_eq_one_iff (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    bienaymeLaw μ {T | FiniteVertices T} = 1 ↔ ∫⁻ k : ℕ, (k : ℝ≥0∞) ∂μ ≤ 1 ∧ μ {1} ≠ 1 := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => bienaymeLaw_finiteVertices_eq_one μ h.1 h.2⟩
  · by_contra hm
    exact (bienaymeLaw_finiteVertices_lt_one μ (not_le.1 hm)).ne h
  · intro h1
    rw [bienaymeLaw_finiteVertices_eq_zero_of_singleton_one μ h1] at h
    exact zero_ne_one h

end BGW.LocallyFinite
