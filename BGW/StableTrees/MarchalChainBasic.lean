/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.MarchalWeights
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Basic finite labelled trees for the Marchal chain

This module defines labelled trees, their quotient by label-preserving graph
isomorphism, the initial edge, and the weight invariant used in Marchal's
exact law.
-/

@[expose] public section

open scoped ENNReal Classical

namespace BGW.StableTrees.Marchal

/-- Finite leaf-labelled trees with leaves exactly `A_0, …, A_n` and no degree-two vertex. -/
structure LTree (n : ℕ) where
  /-- Number of vertices. -/
  m : ℕ
  /-- The tree. -/
  G : SimpleGraph (Fin m)
  tree : G.IsTree
  /-- Leaf `A_i` is the vertex `labels i`. -/
  labels : Fin (n + 1) ↪ Fin m
  leaf : ∀ v, G.degree v = 1 ↔ v ∈ Set.range labels
  branch : ∀ v, G.degree v ≠ 1 → 3 ≤ G.degree v

/-- Label-preserving graph isomorphism. -/
instance LTree.setoid (n : ℕ) : Setoid (LTree n) where
  r T T' := Nonempty {e : T.G ≃g T'.G // ∀ i, e (T.labels i) = T'.labels i}
  iseqv :=
    ⟨fun T => ⟨⟨SimpleGraph.Iso.refl, fun _ => rfl⟩⟩,
     fun ⟨⟨e, h⟩⟩ => ⟨⟨e.symm, fun i => by rw [← h i]; simp⟩⟩,
     fun ⟨⟨e, h⟩⟩ ⟨⟨f, g⟩⟩ => ⟨⟨e.trans f, fun i => by simp [h i, g i]⟩⟩⟩

/-- Marchal states at step `n`: trees with leaves `A_0..A_n`, modulo labelled isomorphism. -/
abbrev State (n : ℕ) := Quotient (LTree.setoid n)

/-- The start state: the single edge `A_0 — A_1`. -/
def startState : State 1 :=
  ⟦{ m := 2, G := ⊤, tree := by
        have h := SimpleGraph.isTree_pathGraph_add_one 1
        rw [show (⊤ : SimpleGraph (Fin 2)) = SimpleGraph.pathGraph 2 by
          ext u v
          fin_cases u <;> fin_cases v <;> simp [SimpleGraph.pathGraph]]
        exact h,
     labels := Function.Embedding.refl _,
     leaf := by
       intro v
       fin_cases v <;>
         simp [SimpleGraph.degree, SimpleGraph.neighborFinset, Finset.card_compl],
     branch := by
       intro v hv
       fin_cases v <;>
         simp [SimpleGraph.degree, SimpleGraph.neighborFinset, Finset.card_compl] at hv ⊢ }⟧

/-- Number of vertices of degree `≥ 3`. -/
noncomputable def LTree.internalCount {n : ℕ} (T : LTree n) : ℕ :=
  Fintype.card {v : Fin T.m // 3 ≤ T.G.degree v}

/-- Numerator of the exact law: `(α-1)^{#internal} ∏_v ∏_{j=2}^{deg v - 2} (j - α)`. -/
noncomputable def LTree.lawWeight {n : ℕ} (α : ℝ) (T : LTree n) : ℝ :=
  (α - 1) ^ T.internalCount *
    ∏ v : {v : Fin T.m // 3 ≤ T.G.degree v},
      ∏ j ∈ Finset.Icc 2 (T.G.degree v.val - 2), ((j : ℝ) - α)

/-- The equivalence on internal vertices induced by a graph isomorphism. -/
noncomputable def LTree.internalEquiv {n : ℕ} {T T' : LTree n} (e : T.G ≃g T'.G) :
    {v : Fin T.m // 3 ≤ T.G.degree v} ≃ {v : Fin T'.m // 3 ≤ T'.G.degree v} where
  toFun v := ⟨e v.val, by rw [e.degree_eq]; exact v.property⟩
  invFun v := ⟨e.symm v.val, by
    have hd : T.G.degree (e.symm v.val) = T'.G.degree v.val := by
      rw [← e.degree_eq, e.apply_symm_apply]
    rw [hd]
    exact v.property⟩
  left_inv v := by apply Subtype.ext; simp
  right_inv v := by apply Subtype.ext; simp

/-- The weight is invariant under labelled isomorphism. -/
theorem LTree.lawWeight_congr {n : ℕ} (α : ℝ) {T T' : LTree n} (h : T ≈ T') :
    T.lawWeight α = T'.lawWeight α := by
  obtain ⟨⟨e, _⟩⟩ := h
  unfold LTree.lawWeight LTree.internalCount
  rw [Fintype.card_congr (LTree.internalEquiv e)]
  congr 1
  apply Fintype.prod_equiv (LTree.internalEquiv e)
  intro v
  rw [show T'.G.degree ((LTree.internalEquiv e) v).val = T.G.degree v.val by
    change T'.G.degree (e v.val) = T.G.degree v.val
    exact e.degree_eq v.val]

/-- Numerator of the exact law on states. -/
noncomputable def State.lawWeight {n : ℕ} (α : ℝ) : State n → ℝ :=
  Quotient.lift (LTree.lawWeight α) fun _ _ h => LTree.lawWeight_congr α h

/-- A state is binary if every vertex has degree one or three. -/
def State.IsBinary {n : ℕ} : State n → Prop :=
  Quotient.lift (fun T : LTree n => ∀ v, T.G.degree v = 1 ∨ T.G.degree v = 3)
    fun T T' h => by
      obtain ⟨⟨e, _⟩⟩ := h
      apply propext
      constructor
      · intro hT v
        have h := hT (e.symm v)
        rw [show T'.G.degree v = T.G.degree (e.symm v) by
          rw [← e.degree_eq]; simp]
        exact h
      · intro hT v
        have h := hT (e v)
        rw [e.degree_eq] at h
        exact h

end BGW.StableTrees.Marchal
