/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.MarchalLawInverse

/-!
# Rigidity of leaf-labelled trees

A longest extension of a path from the root ends at a leaf. An automorphism
fixing all leaves fixes this path pointwise by uniqueness of paths in a tree.
-/

@[expose] public section

open scoped Classical

namespace BGW.StableTrees.Marchal

/-- Every automorphism fixing the leaf labels fixes every vertex. -/
theorem LTree.iso_apply_eq {n : ℕ} (T : LTree n) (e : T.G ≃g T.G)
    (he : ∀ i, e (T.labels i) = T.labels i) (v : Fin T.m) : e v = v := by
  let r := T.labels 0
  obtain ⟨p₀, hp₀⟩ := T.tree.connected.exists_isPath r v
  let lengths := {l : ℕ | ∃ (w : Fin T.m) (p : T.G.Walk r w),
    p.IsPath ∧ v ∈ p.support ∧ p.length = l}
  have hfinite : lengths.Finite :=
    (Set.finite_le_nat T.m).subset (by
      rintro l ⟨w, p, hp, _, rfl⟩
      have h : p.length + 1 ≤ T.m := by
        simpa only [SimpleGraph.Walk.length_support, Fintype.card_fin] using
          hp.support_nodup.length_le_card
      exact (Nat.lt_of_succ_le h).le)
  obtain ⟨l, ⟨⟨w, p, hp, hv, rfl⟩, hmax⟩⟩ :=
    hfinite.exists_maximal ⟨p₀.length, v, p₀, hp₀, p₀.end_mem_support, rfl⟩
  by_cases hr : v = r
  · subst v
    exact he 0
  have hnil : ¬p.Nil := by
    intro h
    have := p.nil_iff_support_eq.mp h
    rw [this, List.mem_singleton] at hv
    exact hr hv
  have hwdeg : T.G.degree w = 1 := by
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
    refine ⟨p.penultimate, (p.adj_penultimate hnil).symm, fun z hz => ?_⟩
    apply T.tree.isAcyclic.eq_penultimate_of_adj_end hp hz
    by_contra hnot
    have hpath := hp.concat hnot hz
    have hb := hmax ⟨z, p.concat hz, hpath,
      p.support_subset_support_concat hz hv, rfl⟩ (by
        simp only [SimpleGraph.Walk.length_concat]
        omega)
    simp only [SimpleGraph.Walk.length_concat] at hb
    omega
  obtain ⟨i, hi⟩ := (T.leaf w).mp hwdeg
  have hw : e w = w := by rw [← hi]; exact he i
  let q : T.G.Walk r w := (p.map e.toHom).copy (he 0) hw
  have hq : q.IsPath := by
    rw [SimpleGraph.Walk.isPath_copy]
    exact hp.map (f := e.toHom) e.injective
  have hpq : p = q := (T.tree.existsUnique_path r w).unique hp hq
  have hget := congrArg (fun t : T.G.Walk r w => t.getVert (p.support.idxOf v)) hpq
  simpa only [q, SimpleGraph.Walk.getVert_copy, SimpleGraph.Walk.getVert_map,
    p.getVert_support_idxOf hv, RelEmbedding.coe_toRelHom,
    RelIso.coe_toRelEmbedding] using hget.symm

/-- Two positions in a leaf-labelled tree give distinct graft states. -/
theorem graft_state_injective {n : ℕ} (T : LTree n) :
    Function.Injective (fun p : Position T.G => (⟦graft T p⟧ : State (n + 1))) := by
  intro p q hpq
  obtain ⟨⟨e, he⟩⟩ := Quotient.exact hpq
  have hlast := he (Fin.last (n + 1))
  simp only [graft_labels_last] at hlast
  cases p with
  | inl a =>
    cases q with
    | inl a' =>
      have hlabels : ∀ i, ungraftEdgeIso e hlast (T.labels i) = T.labels i := by
        intro i
        have hi := he i.castSucc
        simp only [graft_labels_old] at hi
        apply Fin.castSucc_injective
        apply Fin.castSucc_injective
        rw [show (ungraftEdgeIso e hlast (T.labels i)).castSucc.castSucc =
          e (edgeOld (T.labels i)) from ungraftEdgeEquiv_cast e hlast _]
        exact hi
      have hf : ⇑(ungraftEdgeEquiv e hlast) = id :=
        funext (T.iso_apply_eq (ungraftEdgeIso e hlast) hlabels)
      have ha := ungraftEdgeEquiv_edge e hlast
      rw [hf, Sym2.map_id] at ha
      exact congrArg Sum.inl (Subtype.ext ha)
    | inr v' =>
      exact (graftVertex_ne_edge v' a e.symm (e.symm_apply_eq.mpr hlast.symm)).elim
  | inr v =>
    cases q with
    | inl a' => exact (graftVertex_ne_edge v a' e hlast).elim
    | inr v' =>
      have hlabels : ∀ i, ungraftVertexIso e hlast (T.labels i) = T.labels i := by
        intro i
        have hi := he i.castSucc
        simp only [graft_labels_old] at hi
        apply Fin.castSucc_injective
        rw [show (ungraftVertexIso e hlast (T.labels i)).castSucc =
          e.toEquiv (vertexOld (T.labels i)) from
            removeLastEquiv_castSucc e.toEquiv hlast _]
        exact hi
      have hv := ungraftVertexIso_position e hlast
      rw [T.iso_apply_eq (ungraftVertexIso e hlast) hlabels] at hv
      exact congrArg Sum.inr (Subtype.ext hv)

end BGW.StableTrees.Marchal
