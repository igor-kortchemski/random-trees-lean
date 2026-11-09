/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.MarchalChainStep
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The binary case of Marchal growth

At `α = 2`, internal positions of a binary tree have weight zero and edge
positions have weight one. Edge grafts therefore give Rémy growth.
-/

@[expose] public section

open scoped ENNReal Classical

namespace BGW.StableTrees.Marchal

/-- At `α = 2`, on a binary tree every internal vertex has weight zero
(`d - 1 - α = 0`): only edges are selected. -/
theorem selectionWeight_two_binary {n : ℕ} (T : LTree n)
    (hb : ∀ v, T.G.degree v = 1 ∨ T.G.degree v = 3) (p : T.G.edgeSet ⊕ {v // 3 ≤ T.G.degree v}) :
    selectionWeight T.G 2 p = match p with | .inl _ => 1 | .inr _ => 0 := by
  cases p with
  | inl e => simp [selectionWeight]; norm_num
  | inr v =>
    have := (hb v.val).resolve_left (by have := v.property; omega)
    simp [selectionWeight, this]; norm_num

/-- Edge grafting preserves binary trees. -/
theorem graft_inl_binary {n : ℕ} (T : LTree n) (e : T.G.edgeSet)
    (hb : ∀ v, T.G.degree v = 1 ∨ T.G.degree v = 3) (y : Fin (T.m + 2)) :
    (graftGraph T.G (.inl e)).degree y = 1 ∨ (graftGraph T.G (.inl e)).degree y = 3 := by
  refine Fin.lastCases ?_ (fun y => ?_) y
  · change (graftGraph T.G (.inl e)).degree (edgeNewLeaf T.m) = 1 ∨ _
    rw [graftGraph_inl_degree_new]
    exact Or.inl rfl
  · refine Fin.lastCases ?_ (fun x => ?_) y
    · change (graftGraph T.G (.inl e)).degree (edgeMidpoint T.m) = 1 ∨
        (graftGraph T.G (.inl e)).degree (edgeMidpoint T.m) = 3
      rw [graftGraph_inl_degree_mid]
      exact Or.inr rfl
    · change (graftGraph T.G (.inl e)).degree (edgeOld x) = 1 ∨
        (graftGraph T.G (.inl e)).degree (edgeOld x) = 3
      rw [graftGraph_inl_degree_old]
      exact hb x

/-- The initial edge is binary. -/
theorem startState_binary : startState.IsBinary := by
  intro v
  fin_cases v <;>
    simp [SimpleGraph.degree, SimpleGraph.neighborFinset, Finset.card_compl]

/-- At `α = 2`, the numerator is one on every binary tree. -/
theorem lawWeight_two_binary {n : ℕ} (T : LTree n)
    (hb : ∀ v, T.G.degree v = 1 ∨ T.G.degree v = 3) : T.lawWeight 2 = 1 := by
  have hd : ∀ v : {v : Fin T.m // 3 ≤ T.G.degree v}, T.G.degree v.val = 3 := by
    intro v
    exact (hb v.val).resolve_left (by have := v.property; omega)
  norm_num [LTree.lawWeight, hd]

/-- The odd-factor denominator is the corresponding double factorial. -/
theorem prod_two_denominator (k : ℕ) :
    ∏ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) * 2 - 1) =
      ((2 * (k + 1) - 3).doubleFactorial : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    cases k with
    | zero => norm_num
    | succ k =>
      rw [Finset.prod_range_succ, ih]
      have hd : (2 * (k + 2 + 1) - 3) = (2 * (k + 2) - 3) + 2 := by omega
      rw [hd, Nat.doubleFactorial_add_two, Nat.cast_mul]
      have hf : (2 * (k + 2) - 3) + 2 = 2 * (k + 1) + 1 := by omega
      rw [hf]
      push_cast
      ring

/-- `α = 2` support: only binary states have positive mass (all steps from `A_0 — A_1`). -/
theorem law_two_support_binary (k : ℕ) :
    (law (α := 2) (by norm_num) le_rfl k).support ⊆ {s | s.IsBinary} := by
  induction k with
  | zero =>
    intro s hs
    rw [law, PMF.mem_support_pure_iff] at hs
    rw [hs]
    exact startState_binary
  | succ k ih =>
    intro s hs
    rw [law, PMF.mem_support_bind_iff] at hs
    obtain ⟨q, hq, hs⟩ := hs
    have hqb : q.IsBinary := ih hq
    revert hqb hs
    refine Quotient.inductionOn q (fun T => ?_)
    intro hs hqb
    change s ∈ (stepRep (α := 2) (by norm_num) le_rfl T).support at hs
    unfold stepRep at hs
    rw [PMF.mem_support_map_iff] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    cases p with
    | inl e =>
      intro v
      exact graft_inl_binary T e (by exact hqb) v
    | inr v =>
      have hzero : selectionPMF T.G T.tree T.labels T.leaf T.branch
          (Nat.le_add_left 1 k) 2 (by norm_num) le_rfl (.inr v) = 0 := by
        rw [selectionPMF_apply, selectionWeight_two_binary T (hqb)]
        simp
      exact (hp hzero).elim

/-- `α = 2` step is Rémy's step: from a binary state, graft at a uniformly chosen one of the
`2k+1` edges (no plane order is involved: states are non-plane). -/
theorem step_two_binary (k : ℕ) (T : LTree (k + 1))
    (hb : ∀ v, T.G.degree v = 1 ∨ T.G.degree v = 3) (t : State (k + 2)) :
    step (α := 2) (by norm_num) le_rfl k ⟦T⟧ t =
      ({e : T.G.edgeSet | ⟦graft T (.inl e)⟧ = t}.ncard : ℝ≥0∞) /
        ((2 * k + 1 : ℕ) : ℝ≥0∞) := by
  have hden : ENNReal.ofReal (((k + 1 : ℕ) : ℝ) * 2 - 1) =
      ((2 * k + 1 : ℕ) : ℝ≥0∞) := by
    rw [show ((k + 1 : ℕ) : ℝ) * 2 - 1 = ((2 * k + 1 : ℕ) : ℝ) by
      push_cast
      ring]
    exact ENNReal.ofReal_natCast _
  change (selectionPMF T.G T.tree T.labels T.leaf T.branch (Nat.le_add_left 1 k)
    2 (by norm_num) le_rfl).map (fun p => ⟦graft T p⟧) t = _
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_sum_type]
  simp only [selectionPMF_apply, selectionWeight_two_binary T hb, ENNReal.ofReal_one,
    ENNReal.ofReal_zero, hden]
  simp only [zero_mul, ite_self, Finset.sum_const_zero, add_zero, div_eq_mul_inv]
  have hcard : (Finset.univ.filter (fun e : T.G.edgeSet => t = ⟦graft T (.inl e)⟧)).card =
      {e : T.G.edgeSet | ⟦graft T (.inl e)⟧ = t}.ncard := by
    rw [Set.ncard_eq_toFinset_card]
    congr 1
    ext e
    simp [eq_comm]
  calc
    _ = (∑ e : T.G.edgeSet, if t = ⟦graft T (.inl e)⟧ then 1 else 0) *
        ((2 * k + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> simp
    _ = (Finset.univ.filter (fun e : T.G.edgeSet =>
        t = ⟦graft T (.inl e)⟧)).card * ((2 * k + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
      rw [Finset.sum_boole]
    _ = _ := by rw [hcard]

end BGW.StableTrees.Marchal
