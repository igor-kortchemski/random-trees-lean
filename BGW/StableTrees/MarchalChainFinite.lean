/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.MarchalChainBasic
import Mathlib.Tactic.Ring

/-!
# Finiteness of Marchal states

A leaf-labelled tree with `n + 1` leaves and no degree-two vertex has at most
`2 * n` vertices. Encoding its vertices by an initial segment therefore puts
all representatives, and hence their quotient, in a finite type.
-/

@[expose] public section

open scoped ENNReal Classical

namespace BGW.StableTrees.Marchal

/-- The vertex bound for a tree with `n + 1` leaves and no degree-two vertices. -/
theorem LTree.m_le_two_mul {n : ℕ} (T : LTree n) : T.m ≤ 2 * n := by
  let L := {v : Fin T.m // T.G.degree v = 1}
  let I := {v : Fin T.m // T.G.degree v ≠ 1}
  let eL : Fin (n + 1) ≃ L :=
    Equiv.ofBijective (fun i => ⟨T.labels i, (T.leaf _).mpr ⟨i, rfl⟩⟩) (by
      constructor
      · intro i j h
        exact T.labels.injective (congrArg Subtype.val h)
      · intro v
        obtain ⟨i, hi⟩ := (T.leaf v.val).mp v.property
        exact ⟨i, Subtype.ext hi⟩)
  have hL : Fintype.card L = n + 1 := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr eL).symm
  have hV : Fintype.card L + Fintype.card I = T.m := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.cast_id, Fintype.card_fin] using
      Fintype.sum_subtype_add_sum_subtype (fun v : Fin T.m => T.G.degree v = 1)
        (fun _ => (1 : ℕ))
  have hE : Fintype.card T.G.edgeSet + 1 = T.m := by
    simpa only [SimpleGraph.edgeFinset_card, Fintype.card_fin] using T.tree.card_edgeFinset
  have hLeafSum : (∑ v : L, T.G.degree v.val) = n + 1 := by
    calc
      _ = ∑ _v : L, (1 : ℕ) := Finset.sum_congr rfl (fun v _ => v.property)
      _ = n + 1 := by simp [hL]
  have hInternalLower : 3 * Fintype.card I ≤ ∑ v : I, T.G.degree v.val := by
    calc
      3 * Fintype.card I = ∑ _v : I, (3 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun v _ => T.branch v.val v.property)
  have hdegree := Fintype.sum_subtype_add_sum_subtype
    (fun v : Fin T.m => T.G.degree v = 1) (fun v => T.G.degree v)
  rw [T.G.sum_degrees_eq_twice_card_edges, SimpleGraph.edgeFinset_card] at hdegree
  change (∑ v : L, T.G.degree v.val) + (∑ v : I, T.G.degree v.val) = _ at hdegree
  rw [hLeafSum] at hdegree
  omega

private noncomputable def LTree.finiteEncoding {n : ℕ} (T : LTree n) :
    Σ i : Fin (2 * n + 1), SimpleGraph (Fin i.val) × (Fin (n + 1) ↪ Fin i.val) :=
  ⟨⟨T.m, by have := T.m_le_two_mul; omega⟩, (T.G, T.labels)⟩

private theorem LTree.finiteEncoding_injective {n : ℕ} :
    Function.Injective (LTree.finiteEncoding (n := n)) := by
  intro T T' h
  have hm : T.m = T'.m := congrArg (fun x => x.1.val) h
  cases T with
  | mk m G tree labels leaf branch =>
    cases T' with
    | mk m' G' tree' labels' leaf' branch' =>
      dsimp at hm
      subst m'
      simp [LTree.finiteEncoding] at h
      rcases h with ⟨rfl, rfl⟩
      rfl

/-- The states are finitely many. -/
theorem finite_state (n : ℕ) : Finite (State n) := by
  let _ : Finite (LTree n) := Finite.of_injective LTree.finiteEncoding
    LTree.finiteEncoding_injective
  infer_instance

end BGW.StableTrees.Marchal
