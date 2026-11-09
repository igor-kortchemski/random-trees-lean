/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.MarchalLawPrune

/-!
# Reindexing Marchal trees

Equivalences of finite vertex sets transport both graphs and leaf labels.
Swaps then place the leaf to be pruned, and optionally its neighbour, last.
-/

@[expose] public section

open scoped Classical

namespace BGW.StableTrees.Marchal

/-- Transport a labelled tree along an equivalence from the new vertex set. -/
noncomputable def LTree.reindex {n m : ℕ} (T : LTree n) (e : Fin m ≃ Fin T.m) :
    LTree n where
  m := m
  G := T.G.comap e
  tree := (SimpleGraph.Iso.comap e T.G).isTree_iff.mpr T.tree
  labels := T.labels.trans e.symm.toEmbedding
  leaf x := by
    rw [← (SimpleGraph.Iso.comap e T.G).degree_eq, SimpleGraph.Iso.comap_apply, T.leaf]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, by simp [hi]⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, by simpa using congrArg e hi⟩
  branch x hx := by
    rw [← (SimpleGraph.Iso.comap e T.G).degree_eq] at hx ⊢
    exact T.branch _ hx

/-- Reindexing preserves the labelled state. -/
theorem LTree.reindex_state {n m : ℕ} (T : LTree n) (e : Fin m ≃ Fin T.m) :
    (⟦T.reindex e⟧ : State n) = ⟦T⟧ := by
  apply Quotient.sound
  exact ⟨⟨SimpleGraph.Iso.comap e T.G, fun i => e.apply_symm_apply (T.labels i)⟩⟩

/-- Every state with two labelled leaves is the initial edge. -/
theorem state_one_eq_start (s : State 1) : s = startState := by
  induction s using Quotient.inductionOn with | _ T =>
  have hm : T.m = 2 := by
    have hle := T.m_le_two_mul
    have hge := Fintype.card_le_of_injective T.labels T.labels.injective
    simp only [Fintype.card_fin] at hge
    omega
  have hbij : Function.Bijective T.labels :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨T.labels.injective, by simp [hm]⟩
  let e : Fin 2 ≃ Fin T.m := Equiv.ofBijective T.labels hbij
  have hdeg : ∀ x, T.G.degree x = 1 := by
    intro x
    exact (T.leaf x).mpr (hbij.surjective x)
  have hG : T.G.comap e = ⊤ := by
    have h01 : T.G.Adj (e 0) (e 1) := by
      obtain ⟨w, hw, _⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp (hdeg (e 0))
      obtain ⟨i, rfl⟩ := e.surjective w
      fin_cases i
      · exact (T.G.irrefl hw).elim
      · exact hw
    ext x y
    fin_cases x <;> fin_cases y <;> simp [h01, h01.symm]
  rw [← T.reindex_state e]
  apply Quotient.sound
  let E : (T.reindex e).G ≃g (⊤ : SimpleGraph (Fin 2)) :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := by
        intro x y
        change (⊤ : SimpleGraph (Fin 2)).Adj x y ↔ (T.G.comap e).Adj x y
        rw [hG] }
  refine ⟨⟨E, fun i => ?_⟩⟩
  change e.symm (T.labels i) = i
  exact e.symm_apply_apply i

/-- A swap places a specified vertex last under a given indexing equivalence. -/
noncomputable def placeLast {m M : ℕ} (e : Fin (m + 1) ≃ Fin M) (z : Fin M) :
    Fin (m + 1) ≃ Fin M :=
  e.trans (Equiv.swap (e (Fin.last m)) z)

@[simp] theorem placeLast_last {m M : ℕ} (e : Fin (m + 1) ≃ Fin M) (z : Fin M) :
    placeLast e z (Fin.last m) = z := by simp [placeLast]

/-- Two swaps place distinct specified vertices at the midpoint and last indices. -/
noncomputable def placeLastTwo {m M : ℕ} (e : Fin (m + 2) ≃ Fin M)
    (z u : Fin M) : Fin (m + 2) ≃ Fin M :=
  (Equiv.swap (Fin.last m).castSucc ((placeLast e z).symm u)).trans (placeLast e z)

@[simp] theorem placeLastTwo_mid {m M : ℕ} (e : Fin (m + 2) ≃ Fin M) (z u : Fin M) :
    placeLastTwo e z u (Fin.last m).castSucc = u := by simp [placeLastTwo]

@[simp] theorem placeLastTwo_last {m M : ℕ} (e : Fin (m + 2) ≃ Fin M)
    (z u : Fin M) (hzu : z ≠ u) : placeLastTwo e z u (Fin.last (m + 1)) = z := by
  have hu : Fin.last (m + 1) ≠ (placeLast e z).symm u := by
    intro h
    have hh := congrArg (placeLast e z) h
    simp only [placeLast_last, Equiv.apply_symm_apply] at hh
    exact hzu hh
  simp [placeLastTwo, Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_ne_last _).symm hu]

end BGW.StableTrees.Marchal
