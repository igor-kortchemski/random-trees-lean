/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree.Weight

/-!
# Exponential tilting of finite-tree weights

Replacing degree weights `p k` by `a * b ^ k * p k` multiplies the weight of a tree with
`n` vertices by `a ^ n * b ^ (n - 1)`. The identity uses only that the sum of the outdegrees
is `n - 1`; no normalization, positivity or finiteness of the weights is needed.
The conditioned-law consequence is in `BGW.LocallyFinite.Tilting`.
-/

@[expose] public section

namespace BGW.PlaneTree

open scoped ENNReal

private theorem prod_map_tilt (p : ℕ → ℝ≥0∞) (a b : ℝ≥0∞) (ds : List ℕ) :
    (ds.map fun k => a * b ^ k * p k).prod =
      (a ^ ds.length * b ^ ds.sum) * (ds.map p).prod := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, List.sum_cons, ih,
      pow_succ, pow_add]
    ac_rfl

/-- Exponential tilting multiplies a tree's weight by a factor depending only on its size.
This algebraic identity also allows zero or infinite weights and tilt parameters. -/
theorem weight_tilt (p : ℕ → ℝ≥0∞) (a b : ℝ≥0∞) (t : PlaneTree) :
    weight (fun k => a * b ^ k * p k) t =
      (a ^ t.size * b ^ (t.size - 1)) * weight p t := by
  have hsum : t.degrees.sum = t.size - 1 := by
    have := t.sum_degrees_add_one
    omega
  simp only [weight]
  rw [prod_map_tilt, length_degrees, hsum]

end BGW.PlaneTree
