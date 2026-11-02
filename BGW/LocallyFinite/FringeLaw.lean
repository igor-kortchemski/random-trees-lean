/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree.FringeWeight

/-!
# The exact uniform-vertex fringe identity

At an admissible size `n`, a tree with the size-conditioned law has `n` vertices. Averaging a
fringe observable over its certified DFS addresses is therefore the uniform-vertex average.
The theorem expresses this expectation through finite-tree atoms, without adding a measurable
structure on `PlaneTree`. Indicator observables give Corollary `cor:cyclicshift` of
Kortchemski–Vetter (source lines 777–824). The remainder walk ends at zero and its time is
guarded by the fringe size being at most `n`.

The identity holds for arbitrary nonnegative extended observables and every size. At an
inadmissible size both sides are zero, including when the observable takes the value infinity:
the weighted numerator is then zero, so the totalized quotient is `0 / 0 = 0`.
-/

@[expose] public section

namespace BGW.LocallyFinite

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Atomic form of the uniform-vertex fringe formula, valid for every offspring probability
measure. At admissible sizes the left side is the expected fringe observable at a uniform vertex. -/
theorem cond_uniformFringe_eq_tsum (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) (G : PlaneTree → ℝ≥0∞) :
    (∑' t : {t : PlaneTree // t.size = n},
      (bienaymeLaw μ)[|sizeEvent n] {t.val.toLocallyFinite} *
        ((n : ℝ≥0∞)⁻¹ * PlaneTree.fringeSum G t.val)) =
      (∑' s : PlaneTree, if s.size ≤ n then PlaneTree.weight (fun d => μ {d}) s * G s *
        Measure.pi (fun _ : Fin (n - s.size) => μ)
          (countForestBridges 0 (n - s.size)) else 0) /
        Measure.pi (fun _ : Fin n => μ) (countBridges n) := by
  have hterm (t : {t : PlaneTree // t.size = n}) :
      (bienaymeLaw μ)[|sizeEvent n] {t.val.toLocallyFinite} *
          ((n : ℝ≥0∞)⁻¹ * PlaneTree.fringeSum G t.val) =
        ((n : ℝ≥0∞) * bienaymeLaw μ (sizeEvent n))⁻¹ *
          (PlaneTree.weight (fun d => μ {d}) t.val * PlaneTree.fringeSum G t.val) := by
    rw [cond_sizeEvent_singleton, ite_eq_left t.property, ENNReal.div_eq_inv_mul,
      ENNReal.mul_inv (Or.inr (measure_ne_top _ _)) (Or.inl (ENNReal.natCast_ne_top n))]
    ac_rfl
  have hreturn (r : ℕ) :
      (∑' x : List ℤ, Set.indicator (forestBridgeWords 0 r) (walkWeight fun d => μ {d}) x) =
        Measure.pi (fun _ : Fin r => μ) (countForestBridges 0 r) := by
    rw [tsum_forestBridgeWords_walkWeight, ← pi_eq_tsum_indicator]
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_left, PlaneTree.tsum_weight_fringeSum]
  simp_rw [hreturn]
  rw [ENNReal.div_eq_inv_mul, ← natCast_mul_bienaymeLaw_sizeEvent_eq_pi]

end BGW.LocallyFinite
