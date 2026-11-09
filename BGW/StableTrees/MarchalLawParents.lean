/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.MarchalLawTransport

/-!
# Recovering labelled parents from graph reconstructions

A reconstruction isomorphism and the old leaf labels determine the parent
leaf and branching conditions. This separates graph surgery from labels.
-/

@[expose] public section

open scoped Classical

namespace BGW.StableTrees.Marchal

/-- An edge-graft reconstruction with the right leaf labels gives a labelled parent. -/
theorem exists_graft_inl_of_iso {n m : ℕ} (T : LTree (n + 1))
    (G : SimpleGraph (Fin m)) (a : G.edgeSet)
    (e : graftGraph G (.inl a) ≃g T.G) (f : Fin (n + 1) ↪ Fin m)
    (hold : ∀ i, e (f i).castSucc.castSucc = T.labels i.castSucc)
    (hnew : e (Fin.last (m + 1)) = T.labels (Fin.last (n + 1))) :
    ∃ S : LTree n, ∃ p : Position S.G, (⟦graft S p⟧ : State (n + 1)) = ⟦T⟧ := by
  have hdeg : ∀ x : Fin m, T.G.degree (e x.castSucc.castSucc) = G.degree x := by
    intro x
    rw [e.degree_eq]
    exact graftGraph_inl_degree_old G a x
  have hleaf : ∀ x : Fin m, G.degree x = 1 ↔ x ∈ Set.range f := by
    intro x
    rw [← hdeg, T.leaf]
    constructor
    · rintro ⟨i, hi⟩
      revert hi
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro hi
        rw [← hnew] at hi
        exact (Fin.castSucc_ne_last x.castSucc (e.injective hi).symm).elim
      · intro hi
        rw [← hold j] at hi
        exact ⟨j, Fin.castSucc_injective _ (Fin.castSucc_injective _ (e.injective hi))⟩
    · rintro ⟨j, hj⟩
      exact ⟨j.castSucc, by rw [← hold j, hj]⟩
  let S : LTree n :=
    { m := m
      G := G
      tree := isTree_of_graftGraph_inl G a (e.isTree_iff.mpr T.tree)
      labels := f
      leaf := hleaf
      branch := fun x hx => by
        rw [← hdeg] at hx ⊢
        exact T.branch _ hx }
  refine ⟨S, .inl a, Quotient.sound ⟨⟨e, ?_⟩⟩⟩
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [graft_labels_last]
    exact hnew
  · rw [graft_labels_old]
    exact hold j

end BGW.StableTrees.Marchal
