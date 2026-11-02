/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Marchal selection weights on a finite labelled tree

The graph is an existing finite `SimpleGraph`, with its leaves enumerated
injectively by `Fin (n + 1)`. Positions are edges or vertices of degree at
least three. No plane order, tree-state quotient, or growth operation is
introduced here.

The intended selection weights are those of Curien–Haas, *The stable trees
are nested*, arXiv:1207.5418v1, Section 1.3, equation (2): an edge has weight
`α - 1`, and a vertex of degree `d ≥ 3` has weight `d - 1 - α`.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace BGW.StableTrees.Marchal

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The existing graph's edges and internal vertices, as distinct selection positions. -/
abbrev Position := G.edgeSet ⊕ {v : V // 3 ≤ G.degree v}

/-- Marchal's real selection weight at one edge or one internal vertex. -/
def selectionWeight (α : ℝ) : Position G → ℝ
  | .inl _ => α - 1
  | .inr v => (G.degree v.val : ℝ) - 1 - α

omit [DecidableEq V] in
/-- Every selectable position has nonnegative weight throughout the stable parameter range. -/
theorem selectionWeight_nonneg {α : ℝ} (hα : 1 < α) (hα2 : α ≤ 2)
    (p : Position G) : 0 ≤ selectionWeight G α p := by
  cases p with
  | inl e => exact sub_nonneg.mpr hα.le
  | inr v =>
    change 0 ≤ (G.degree v.val : ℝ) - 1 - α
    have hd : (3 : ℝ) ≤ G.degree v.val := by exact_mod_cast v.property
    linarith

omit [DecidableEq V] in
/-- Exhaustive leaf labels and the absence of other small degrees give the exact total weight.
This identity is algebraic in `α`; its positivity is a separate result. -/
theorem sum_selectionWeight {n : ℕ} (hT : G.IsTree) (labels : Fin (n + 1) ↪ V)
    (hleaf : ∀ v, G.degree v = 1 ↔ v ∈ Set.range labels)
    (hbranch : ∀ v, G.degree v ≠ 1 → 3 ≤ G.degree v) (α : ℝ) :
    ∑ p : Position G, selectionWeight G α p = (n : ℝ) * α - 1 := by
  classical
  let eL : Fin (n + 1) ≃ {v : V // G.degree v = 1} :=
    Equiv.ofBijective (fun i => ⟨labels i, (hleaf _).mpr ⟨i, rfl⟩⟩) (by
      constructor
      · intro i j h
        exact labels.injective (congrArg Subtype.val h)
      · intro v
        obtain ⟨i, hi⟩ := (hleaf v.val).mp v.property
        exact ⟨i, Subtype.ext hi⟩)
  have hL : Fintype.card {v : V // G.degree v = 1} = n + 1 := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr eL).symm
  let eI : {v : V // G.degree v ≠ 1} ≃ {v : V // 3 ≤ G.degree v} :=
    Equiv.subtypeEquivRight (fun v => ⟨hbranch v, fun h h₁ => by omega⟩)
  have hI : Fintype.card {v : V // G.degree v ≠ 1} =
      Fintype.card {v : V // 3 ≤ G.degree v} := Fintype.card_congr eI
  have hV : Fintype.card {v : V // G.degree v = 1} +
      Fintype.card {v : V // G.degree v ≠ 1} = Fintype.card V := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Nat.cast_id] using
      Fintype.sum_subtype_add_sum_subtype (fun v => G.degree v = 1) (fun _ => (1 : ℕ))
  rw [hL, hI] at hV
  have hE : Fintype.card G.edgeSet + 1 = Fintype.card V := by
    simpa only [SimpleGraph.edgeFinset_card] using hT.card_edgeFinset
  have hEI : Fintype.card G.edgeSet = n + Fintype.card {v : V // 3 ≤ G.degree v} := by
    omega
  have hLeafSum : (∑ v : {v : V // G.degree v = 1}, G.degree v.val) = n + 1 := by
    calc
      _ = ∑ _v : {v : V // G.degree v = 1}, (1 : ℕ) :=
        Finset.sum_congr rfl (fun v _ => v.property)
      _ = n + 1 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hL, Nat.cast_id]
  have hInternalSum :
      (∑ v : {v : V // G.degree v ≠ 1}, G.degree v.val) =
        ∑ v : {v : V // 3 ≤ G.degree v}, G.degree v.val :=
    Fintype.sum_equiv eI _ _ (fun _ => rfl)
  have hdegree := Fintype.sum_subtype_add_sum_subtype
    (fun v => G.degree v = 1) (fun v => G.degree v)
  rw [hLeafSum, hInternalSum, G.sum_degrees_eq_twice_card_edges,
    SimpleGraph.edgeFinset_card] at hdegree
  have hdegreeR : (n : ℝ) + 1 + (∑ v : {v : V // 3 ≤ G.degree v}, (G.degree v.val : ℝ)) =
      2 * (Fintype.card G.edgeSet : ℝ) := by exact_mod_cast hdegree
  have hEIR : (Fintype.card G.edgeSet : ℝ) =
      (n : ℝ) + (Fintype.card {v : V // 3 ≤ G.degree v} : ℝ) := by exact_mod_cast hEI
  have hsumR : (∑ v : {v : V // 3 ≤ G.degree v}, (G.degree v.val : ℝ)) =
      2 * (Fintype.card G.edgeSet : ℝ) - ((n : ℝ) + 1) := by linarith
  rw [Fintype.sum_sum_type]
  simp only [selectionWeight, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [hsumR, hEIR]
  ring

/-- The Marchal normalizer is strictly positive at every valid starting index. -/
theorem normalizer_pos {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα : 1 < α) :
    0 < (n : ℝ) * α - 1 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hprod := mul_le_mul_of_nonneg_right hnR (show 0 ≤ α by linarith)
  linarith

/-- The normalized Marchal selection law on the graph's actual edges and internal vertices. -/
noncomputable def selectionPMF {n : ℕ} (hT : G.IsTree) (labels : Fin (n + 1) ↪ V)
    (hleaf : ∀ v, G.degree v = 1 ↔ v ∈ Set.range labels)
    (hbranch : ∀ v, G.degree v ≠ 1 → 3 ≤ G.degree v)
    (hn : 1 ≤ n) (α : ℝ) (hα : 1 < α) (hα2 : α ≤ 2) : PMF (Position G) :=
  PMF.ofFintype
    (fun p => ENNReal.ofReal (selectionWeight G α p) / ENNReal.ofReal ((n : ℝ) * α - 1))
    (by
      rw [← ENNReal.sum_div,
        ← ENNReal.ofReal_sum_of_nonneg (fun p _ => selectionWeight_nonneg G hα hα2 p),
        sum_selectionWeight G hT labels hleaf hbranch α]
      exact ENNReal.div_self
        (ne_of_gt (ENNReal.ofReal_pos.mpr (normalizer_pos hn hα))) ENNReal.ofReal_ne_top)

omit [DecidableEq V] in
/-- Each atom is its nonnegative real selection weight divided by `n * α - 1`. -/
@[simp] theorem selectionPMF_apply {n : ℕ} (hT : G.IsTree) (labels : Fin (n + 1) ↪ V)
    (hleaf : ∀ v, G.degree v = 1 ↔ v ∈ Set.range labels)
    (hbranch : ∀ v, G.degree v ≠ 1 → 3 ≤ G.degree v)
    (hn : 1 ≤ n) (α : ℝ) (hα : 1 < α) (hα2 : α ≤ 2) (p : Position G) :
    selectionPMF G hT labels hleaf hbranch hn α hα hα2 p =
      ENNReal.ofReal (selectionWeight G α p) / ENNReal.ofReal ((n : ℝ) * α - 1) := rfl

end BGW.StableTrees.Marchal
