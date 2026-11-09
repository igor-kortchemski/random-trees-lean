/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.MarchalLawCanonical

/-!
# Pruning a leaf at a vertex of degree at least four

Deleting the last leaf leaves its neighbour selectable as an internal vertex.
-/

@[expose] public section

open scoped Classical

namespace BGW.StableTrees.Marchal

/-- If a vertex graft is a tree, its parent graph is a tree. -/
theorem isTree_of_graftGraph_inr {m : ℕ} (G : SimpleGraph (Fin m))
    (v : {v : Fin m // 3 ≤ G.degree v}) (hG : (graftGraph G (.inr v)).IsTree) :
    G.IsTree := by
  let f : Fin (m + 1) → Fin m := Fin.lastCases v.val id
  have hadj : ∀ x y : Fin (m + 1), (graftGraph G (.inr v)).Adj x y →
      G.Reachable (f x) (f y) := by
    intro x y
    refine Fin.lastCases ?_ (fun x => ?_) x <;>
      refine Fin.lastCases ?_ (fun y => ?_) y
    · simp
    · intro h
      have hy := (inr_adj_new_old_cast G v y).mp h
      subst y
      simp [f]
    · intro h
      have hx := (inr_adj_old_new_cast G v x).mp h
      subst x
      simp [f]
    · intro h
      simpa [f] using ((inr_adj_old_old_cast G v x y).mp h).reachable
  have hreach : ∀ x y, (graftGraph G (.inr v)).Reachable x y →
      G.Reachable (f x) (f y) := by
    intro x y ⟨p⟩
    induction p with
    | nil => exact .rfl
    | cons h p ih => exact (hadj _ _ h).trans ih
  have hconn : G.Connected := by
    let _ : Nonempty (Fin m) := ⟨v.val⟩
    exact ⟨fun x y => by simpa [f] using hreach _ _ (hG.connected x.castSucc y.castSucc)⟩
  let F : G →g graftGraph G (.inr v) :=
    ⟨Fin.castSucc, fun h => (inr_adj_old_old_cast G v _ _).mpr h⟩
  exact { connected := hconn, isAcyclic := hG.isAcyclic.comap F (Fin.castSucc_injective _) }

/-- A vertex-graft reconstruction with the right labels gives a labelled parent. -/
theorem exists_graft_inr_of_iso {n m : ℕ} (T : LTree (n + 1))
    (G : SimpleGraph (Fin m)) (v : {v : Fin m // 3 ≤ G.degree v})
    (e : graftGraph G (.inr v) ≃g T.G) (f : Fin (n + 1) ↪ Fin m)
    (hold : ∀ i, e (f i).castSucc = T.labels i.castSucc)
    (hnew : e (Fin.last m) = T.labels (Fin.last (n + 1))) :
    ∃ S : LTree n, ∃ p : Position S.G, (⟦graft S p⟧ : State (n + 1)) = ⟦T⟧ := by
  have hdeg : ∀ x : Fin m, G.degree x = 1 ↔ T.G.degree (e x.castSucc) = 1 := by
    intro x
    rw [e.degree_eq]
    by_cases hx : x = v.val
    · subst x
      rw [show (graftGraph G (.inr v)).degree v.val.castSucc = G.degree v.val + 1 from
        graftGraph_inr_degree_old_self G v]
      have := v.property
      omega
    · rw [show (graftGraph G (.inr v)).degree x.castSucc = G.degree x from
        graftGraph_inr_degree_old_of_ne G v x hx]
  have hleaf : ∀ x : Fin m, G.degree x = 1 ↔ x ∈ Set.range f := by
    intro x
    rw [hdeg, T.leaf]
    constructor
    · rintro ⟨i, hi⟩
      revert hi
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro hi
        rw [← hnew] at hi
        exact (Fin.castSucc_ne_last x (e.injective hi).symm).elim
      · intro hi
        rw [← hold j] at hi
        exact ⟨j, Fin.castSucc_injective _ (e.injective hi)⟩
    · rintro ⟨j, hj⟩
      exact ⟨j.castSucc, by rw [← hold j, hj]⟩
  let S : LTree n :=
    { m := m
      G := G
      tree := isTree_of_graftGraph_inr G v (e.isTree_iff.mpr T.tree)
      labels := f
      leaf := hleaf
      branch := fun x hx => by
        by_cases hxv : x = v.val
        · subst x
          exact v.property
        · have hd : T.G.degree (e x.castSucc) = G.degree x := by
            rw [e.degree_eq]
            exact graftGraph_inr_degree_old_of_ne G v x hxv
          rw [← hd]
          exact T.branch _ ((hdeg x).not.mp hx) }
  refine ⟨S, .inr v, Quotient.sound ⟨⟨e, ?_⟩⟩⟩
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [graft_labels_last]
    exact hnew
  · rw [graft_labels_old]
    exact hold j

/-- Deleting the last vertex removes exactly its possible incident edge at each old vertex. -/
theorem degree_comap_castSucc_add {m : ℕ} (G : SimpleGraph (Fin (m + 1))) (x : Fin m) :
    (G.comap Fin.castSucc).degree x +
      (if G.Adj x.castSucc (Fin.last m) then 1 else 0) = G.degree x.castSucc := by
  have hsum {M : ℕ} (H : SimpleGraph (Fin M)) [DecidableRel H.Adj] (v : Fin M) :
      H.degree v = ∑ w, if H.Adj v w then 1 else 0 := by
    rw [Finset.sum_boole, ← H.card_neighborFinset_eq_degree]
    congr 1
    ext w
    simp
  rw [hsum (G.comap Fin.castSucc) x, hsum G x.castSucc, Fin.sum_univ_castSucc]
  rfl

/-- Canonical pruning at an old vertex of degree at least four gives a labelled parent. -/
theorem exists_graft_vertex_canonical {n m : ℕ}
    (G : SimpleGraph (Fin (m + 1))) (tree : G.IsTree)
    (labels : Fin (n + 2) ↪ Fin (m + 1))
    (leaf : ∀ v, G.degree v = 1 ↔ v ∈ Set.range labels)
    (branch : ∀ v, G.degree v ≠ 1 → 3 ≤ G.degree v)
    (hlast : labels (Fin.last (n + 1)) = Fin.last m)
    (u : Fin m) (hnew : ∀ x, G.Adj (Fin.last m) x.castSucc ↔ x = u)
    (hdegree : 4 ≤ G.degree u.castSucc) :
    ∃ S : LTree n, ∃ p : Position S.G, (⟦graft S p⟧ : State (n + 1)) =
      ⟦(⟨m + 1, G, tree, labels, leaf, branch⟩ : LTree (n + 1))⟧ := by
  let H := G.comap Fin.castSucc
  have hu : 3 ≤ H.degree u := by
    have h := degree_comap_castSucc_add G u
    have hadj := ((hnew u).mpr rfl).symm
    rw [ite_eq_left hadj] at h
    change H.degree u + 1 = G.degree u.castSucc at h
    omega
  let v : {v : Fin m // 3 ≤ H.degree v} := ⟨u, hu⟩
  have hrec : graftGraph H (.inr v) = G := by
    ext x y
    refine Fin.lastCases ?_ (fun x => ?_) x <;>
      refine Fin.lastCases ?_ (fun y => ?_) y
    · simp
    · rw [inr_adj_new_old_cast H v y, hnew]
    · rw [inr_adj_old_new_cast H v x, SimpleGraph.adj_comm (G := G), hnew]
    · rw [inr_adj_old_old_cast H v x y]
      rfl
  have hbound : ∀ i : Fin (n + 1), (labels i.castSucc).val < m := by
    intro i
    apply Fin.val_lt_last
    rw [← hlast]
    exact labels.injective.ne (Fin.castSucc_ne_last i)
  let f := restrictLabels labels hbound
  let E : graftGraph H (.inr v) ≃g G :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := by intro x y; rw [hrec]; rfl }
  apply exists_graft_inr_of_iso ⟨m + 1, G, tree, labels, leaf, branch⟩ H v E f
  · intro i
    exact Fin.ext rfl
  · exact hlast.symm

end BGW.StableTrees.Marchal
