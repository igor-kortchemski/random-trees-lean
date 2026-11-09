/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.MarchalLawWeights
public import BGW.StableTrees.MarchalLawRigidity
public import BGW.StableTrees.MarchalLawPrune
public import BGW.StableTrees.MarchalLawSurjective

/-!
# Marchal law along its unique histories

The unique-parent and injective-position lemmas reduce the mass of a graft
to a single term in the transition and in the bind defining the chain.

Every labelled state has a graft decomposition. Induction therefore gives the
all-state product formula, and the binary specialization gives the exact count
of binary states by normalization of the probability mass function.

Each state has a unique history (remove the last leaf and suppress the resulting degree-two
vertex), so its probability is a single product of selection weights. References: P. Marchal,
*A note on the fragmentation of a stable tree*, DMTCS Proc. (2008); N. Curien and B. Haas,
*The stable trees are nested*, arXiv:1207.5418, §§1.1, 1.3.
-/

@[expose] public section

open scoped ENNReal Classical

namespace BGW.StableTrees.Marchal

/-- A graft has exactly the mass of the position that produced it. -/
theorem step_apply_graft {k : ℕ} {α : ℝ} (hα : 1 < α) (hα2 : α ≤ 2)
    (T : LTree (k + 1)) (p : Position T.G) :
    step hα hα2 k ⟦T⟧ ⟦graft T p⟧ =
      ENNReal.ofReal (selectionWeight T.G α p) /
        ENNReal.ofReal (((k + 1 : ℕ) : ℝ) * α - 1) := by
  change (stepRep hα hα2 T) ⟦graft T p⟧ = _
  rw [stepRep, PMF.map_apply, tsum_eq_single p]
  · simp
  · intro q hq
    have hne : (⟦graft T p⟧ : State (k + 2)) ≠ ⟦graft T q⟧ := by
      intro h
      exact hq ((graft_state_injective T h).symm)
    simp [hne]

/-- A transition to a given graft vanishes at every other parent state. -/
theorem step_apply_graft_of_ne {k : ℕ} {α : ℝ} (hα : 1 < α) (hα2 : α ≤ 2)
    (T : LTree (k + 1)) (p : Position T.G) (s : State (k + 1))
    (hs : s ≠ ⟦T⟧) : step hα hα2 k s ⟦graft T p⟧ = 0 := by
  induction s using Quotient.inductionOn with | _ S =>
  change (stepRep hα hα2 S) ⟦graft T p⟧ = 0
  rw [stepRep, PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro q
  have hne : (⟦graft T p⟧ : State (k + 2)) ≠ ⟦graft S q⟧ := by
    intro h
    exact hs (graft_parent_eq p q h).symm
  simp [hne]

/-- The probability recurrence has a single parent and a single position. -/
theorem law_apply_graft {k : ℕ} {α : ℝ} (hα : 1 < α) (hα2 : α ≤ 2)
    (T : LTree (k + 1)) (p : Position T.G) :
    law hα hα2 (k + 1) ⟦graft T p⟧ = law hα hα2 k ⟦T⟧ *
      (ENNReal.ofReal (selectionWeight T.G α p) /
        ENNReal.ofReal (((k + 1 : ℕ) : ℝ) * α - 1)) := by
  rw [law, PMF.bind_apply, tsum_eq_single (⟦T⟧ : State (k + 1))]
  · rw [step_apply_graft]
  · intro s hs
    rw [step_apply_graft_of_ne hα hα2 T p s hs, mul_zero]

/-- The numerator on the initial edge is one. -/
theorem startState_lawWeight (α : ℝ) : startState.lawWeight α = 1 := by
  change (α - 1) ^ _ * _ = 1
  norm_num [LTree.internalCount, SimpleGraph.degree, SimpleGraph.neighborFinset,
    Finset.card_compl]

/-- The normalizing product is strictly positive throughout the stable range. -/
theorem law_denominator_pos {α : ℝ} (hα : 1 < α) (k : ℕ) :
    0 < ∏ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) * α - 1) := by
  apply Finset.prod_pos
  intro j _
  exact normalizer_pos (by omega) hα

/-- The product formula propagates from a parent to any one of its grafts. -/
theorem law_apply_graft_of_formula {k : ℕ} {α : ℝ} (hα : 1 < α) (hα2 : α ≤ 2)
    (T : LTree (k + 1)) (p : Position T.G)
    (hT : law hα hα2 k ⟦T⟧ = ENNReal.ofReal
      (T.lawWeight α / ∏ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) * α - 1))) :
    law hα hα2 (k + 1) ⟦graft T p⟧ = ENNReal.ofReal
      ((graft T p).lawWeight α /
        ∏ j ∈ Finset.range (k + 1), (((j + 1 : ℕ) : ℝ) * α - 1)) := by
  rw [law_apply_graft, hT, T.lawWeight_graft, Finset.prod_range_succ]
  rw [← ENNReal.ofReal_div_of_pos (normalizer_pos (by omega) hα),
    ← ENNReal.ofReal_mul' (div_nonneg (selectionWeight_nonneg T.G hα hα2 p)
      (normalizer_pos (by omega) hα).le)]
  congr 1
  exact div_mul_div_comm _ _ _ _

/-- The exact product formula holds at every state in the support of the chain. -/
theorem law_apply_of_mem_support {α : ℝ} (hα : 1 < α) (hα2 : α ≤ 2)
    (k : ℕ) (s : State (k + 1)) (hs : s ∈ (law hα hα2 k).support) :
    law hα hα2 k s =
      ENNReal.ofReal (s.lawWeight α /
        ∏ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) * α - 1)) := by
  induction k with
  | zero =>
    rw [law, PMF.mem_support_pure_iff] at hs
    subst s
    simp [law, startState_lawWeight]
  | succ k ih =>
    rw [law, PMF.mem_support_bind_iff] at hs
    obtain ⟨t, ht, hs⟩ := hs
    have hformula := ih t ht
    revert hs hformula
    induction t using Quotient.inductionOn with | _ T =>
    intro hs hformula
    change s ∈ (stepRep hα hα2 T).support at hs
    rw [stepRep, PMF.mem_support_map_iff] at hs
    obtain ⟨p, _, rfl⟩ := hs
    exact law_apply_graft_of_formula hα hα2 T p hformula

/-- At index two every supported state has the double-factorial mass. -/
theorem law_two_apply_of_mem_support (k : ℕ) (s : State (k + 1))
    (hs : s ∈ (law (α := 2) (by norm_num) le_rfl k).support) :
    law (α := 2) (by norm_num) le_rfl k s =
      ((2 * (k + 1) - 3).doubleFactorial : ℝ≥0∞)⁻¹ := by
  have hb := law_two_support_binary k hs
  have hw : s.lawWeight 2 = 1 := by
    induction s using Quotient.inductionOn with | _ T =>
    exact lawWeight_two_binary T hb
  rw [law_apply_of_mem_support (by norm_num) le_rfl k s hs,
    hw, prod_two_denominator, ENNReal.ofReal_div_of_pos
      (Nat.cast_pos.mpr (Nat.doubleFactorial_pos _))]
  simp

/-- The number of supported states at index two is the double factorial. -/
theorem ncard_law_two_support (k : ℕ) :
    (law (α := 2) (by norm_num) le_rfl k).support.ncard =
      (2 * (k + 1) - 3).doubleFactorial := by
  let p := law (α := 2) (by norm_num) le_rfl k
  let _ : Finite (State (k + 1)) := finite_state _
  let _ := Fintype.ofFinite (State (k + 1))
  let S := p.support
  let N := (2 * (k + 1) - 3).doubleFactorial
  have hsum : (S.ncard : ℝ≥0∞) * (N : ℝ≥0∞)⁻¹ = 1 := by
    calc
      _ = ∑' s : S, p s := by
        rw [Set.ncard_eq_toFinset_card S, tsum_fintype]
        simp_rw [show ∀ s : S, p s = (N : ℝ≥0∞)⁻¹ from
          fun s => law_two_apply_of_mem_support k s.val s.property]
        simp
      _ = ∑' s, p s := tsum_subtype_eq_of_support_subset (by exact fun _ h => h)
      _ = 1 := p.tsum_coe
  have hN : (N : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos (2 * (k + 1) - 3)).ne'
  have hc := congrArg (fun x : ℝ≥0∞ => x * (N : ℝ≥0∞)) hsum
  rw [mul_assoc, ENNReal.inv_mul_cancel hN (by finiteness), mul_one, one_mul] at hc
  exact_mod_cast hc

/-- Exact finite-tree law of the Marchal chain. Step `n = k+1`; denominator
the denominator `∏_{j=1}^{k} (j α - 1)` is written as `∏_{j<k} ((j+1) α - 1)`. -/
theorem law_apply {α : ℝ} (hα : 1 < α) (hα2 : α ≤ 2) (k : ℕ) (s : State (k + 1)) :
    law hα hα2 k s =
      ENNReal.ofReal (s.lawWeight α / ∏ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) * α - 1)) := by
  induction k with
  | zero =>
    rw [state_one_eq_start s]
    simp [law, startState_lawWeight]
  | succ k ih =>
    obtain ⟨T, p, rfl⟩ := exists_graft_state k s
    exact law_apply_graft_of_formula hα hα2 T p (ih ⟦T⟧)

/-- `α = 2`: Rémy's law — uniform on binary states, mass `1/(2n-3)!!` with `n = k+1`. -/
theorem law_two_binary_apply (k : ℕ) (s : State (k + 1)) (hs : s.IsBinary) :
    law (α := 2) (by norm_num) le_rfl k s = ((2 * (k + 1) - 3).doubleFactorial : ℝ≥0∞)⁻¹ := by
  have hw : s.lawWeight 2 = 1 := by
    induction s using Quotient.inductionOn with | _ T =>
    exact lawWeight_two_binary T hs
  rw [law_apply, hw, prod_two_denominator, ENNReal.ofReal_div_of_pos
    (Nat.cast_pos.mpr (Nat.doubleFactorial_pos _))]
  simp

/-- There are `(2n-3)!!` binary leaf-labelled trees with leaves `A_0..A_n`, `n = k+1`
(with `(-1)!! = 1` read as `0‼ = 1`; checked at `n = 1,2,3`: `1, 1, 3`). -/
theorem ncard_binary_states (k : ℕ) :
    {s : State (k + 1) | s.IsBinary}.ncard = (2 * (k + 1) - 3).doubleFactorial := by
  have heq : (law (α := 2) (by norm_num) le_rfl k).support =
      {s : State (k + 1) | s.IsBinary} := by
    apply Set.Subset.antisymm (law_two_support_binary k)
    intro s hs
    change law (α := 2) (by norm_num) le_rfl k s ≠ 0
    rw [law_two_binary_apply k s hs]
    exact ENNReal.inv_ne_zero.mpr (by finiteness)
  rw [← heq]
  exact ncard_law_two_support k

end BGW.StableTrees.Marchal
