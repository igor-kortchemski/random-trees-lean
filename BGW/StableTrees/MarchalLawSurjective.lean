/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.MarchalLawVertexPrune

/-!
# Every Marchal state has a parent

Two swaps put the newest leaf and its neighbour last. The neighbour has degree
at least three, so one of the two canonical pruning constructions applies.
-/

@[expose] public section

open scoped Classical

namespace BGW.StableTrees.Marchal

/-- The neighbour of a leaf in a tree with at least three labels is internal. -/
theorem LTree.leaf_neighbor_internal {k : ℕ} (T : LTree (k + 2)) (u : Fin T.m)
    (hadj : T.G.Adj (T.labels (Fin.last (k + 2))) u) : 3 ≤ T.G.degree u := by
  let z := T.labels (Fin.last (k + 2))
  have hcard : 3 ≤ T.m := by
    have h := Fintype.card_le_of_injective T.labels T.labels.injective
    simp only [Fintype.card_fin] at h
    omega
  apply T.branch u
  intro hu
  have hz : T.G.degree z = 1 := (T.leaf _).mpr ⟨Fin.last _, rfl⟩
  have huniq := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hz
  obtain ⟨w, _, hw⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hu
  have hsub : (T.G.neighborSet u).Subsingleton :=
    fun _ ha _ hb => (hw _ ha).trans (hw _ hb).symm
  obtain ⟨y, hyz, hyu⟩ : ∃ y : Fin T.m, y ≠ z ∧ y ≠ u := by
    by_contra! h
    have hset : (Finset.univ : Finset (Fin T.m)) ⊆ {z, u} := by
      intro y _
      by_cases hy : y = z
      · simp [hy]
      · simp [h y hy]
    have hle := Finset.card_le_card hset
    have htwo := Finset.card_insert_le z ({u} : Finset (Fin T.m))
    simp only [Finset.card_univ, Fintype.card_fin, Finset.card_singleton] at hle htwo
    omega
  obtain ⟨p, hp⟩ := T.tree.connected.exists_isPath z y
  have hnil : ¬p.Nil := SimpleGraph.Walk.not_nil_of_ne hyz.symm
  have hsnd : p.snd = u := huniq.unique (p.adj_snd hnil) hadj
  have hmem : u ∈ p.support := by
    rw [← hsnd]
    exact List.mem_of_mem_tail (p.snd_mem_tail_support hnil)
  exact hp.isTrail.notMem_support_of_subsingleton_neighborSet hadj.ne' hyu.symm hsub hmem

/-- Every tree with at least three labelled leaves is a graft of a smaller labelled tree. -/
theorem exists_graft_parent {k : ℕ} (T : LTree (k + 2)) :
    ∃ S : LTree (k + 1), ∃ p : Position S.G,
      (⟦graft S p⟧ : State (k + 2)) = ⟦T⟧ := by
  let z := T.labels (Fin.last (k + 2))
  have hz : T.G.degree z = 1 := (T.leaf _).mpr ⟨Fin.last _, rfl⟩
  obtain ⟨u, hzu, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hz
  have hu := T.leaf_neighbor_internal u hzu
  have hm : 2 ≤ T.m := by
    have h := Fintype.card_le_of_injective T.labels T.labels.injective
    simp only [Fintype.card_fin] at h
    omega
  obtain ⟨m, hm⟩ : ∃ m, T.m = m + 2 := ⟨T.m - 2, by omega⟩
  let e₀ : Fin (m + 2) ≃ Fin T.m := finCongr hm.symm
  let e := placeLastTwo e₀ z u
  have helast : e (Fin.last (m + 1)) = z := placeLastTwo_last e₀ z u hzu.ne
  have hemid : e (Fin.last m).castSucc = u := placeLastTwo_mid e₀ z u
  let Q := T.reindex e
  have hlast : Q.labels (Fin.last (k + 2)) = Fin.last (m + 1) := by
    change e.symm z = Fin.last (m + 1)
    exact e.symm_apply_eq.mpr helast.symm
  have hnew : ∀ x : Fin (m + 2), Q.G.Adj (Fin.last (m + 1)) x ↔
      x = (Fin.last m).castSucc := by
    intro x
    change T.G.Adj (e (Fin.last (m + 1))) (e x) ↔ x = (Fin.last m).castSucc
    rw [helast]
    constructor
    · intro h
      apply e.injective
      rw [hemid]
      exact (huniq _ h).trans (huniq _ hzu).symm
    · rintro rfl
      rw [hemid]
      exact hzu
  have hdegree : Q.G.degree (Fin.last m).castSucc = T.G.degree u := by
    change (T.G.comap e).degree (Fin.last m).castSucc = T.G.degree u
    rw [← (SimpleGraph.Iso.comap e T.G).degree_eq, SimpleGraph.Iso.comap_apply, hemid]
  have hparent : ∃ S : LTree (k + 1), ∃ p : Position S.G,
      (⟦graft S p⟧ : State (k + 2)) = ⟦Q⟧ := by
    by_cases hd : T.G.degree u = 3
    · exact exists_graft_edge_canonical Q.G Q.tree Q.labels Q.leaf Q.branch
        hlast hnew (hdegree.trans hd)
    · have hd' : 4 ≤ Q.G.degree (Fin.last m).castSucc := by omega
      apply exists_graft_vertex_canonical Q.G Q.tree Q.labels Q.leaf Q.branch
        hlast (Fin.last m) _ hd'
      intro x
      simpa only [Fin.castSucc_inj] using hnew x.castSucc
  obtain ⟨S, p, hp⟩ := hparent
  exact ⟨S, p, hp.trans (T.reindex_state e)⟩

/-- Grafting is surjective onto the next quotient state space. -/
theorem exists_graft_state (k : ℕ) (s : State (k + 2)) :
    ∃ T : LTree (k + 1), ∃ p : Position T.G, (⟦graft T p⟧ : State (k + 2)) = s := by
  induction s using Quotient.inductionOn with | _ T =>
  exact exists_graft_parent T

end BGW.StableTrees.Marchal
