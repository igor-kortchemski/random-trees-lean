/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.MarchalLawInverse

/-!
# Tree structure before grafting

Connectivity can be pulled back through an edge graft by collapsing both new
vertices onto one endpoint of the subdivided edge. The degree sum then recovers
the tree edge count.
-/

@[expose] public section

open scoped Classical

namespace BGW.StableTrees.Marchal

/-- If an edge graft is a tree, its parent graph is a tree. -/
theorem isTree_of_graftGraph_inl {m : ℕ} (G : SimpleGraph (Fin m)) (e : G.edgeSet)
    (hG : (graftGraph G (.inl e)).IsTree) : G.IsTree := by
  classical
  let a := e.val.out.1
  let b := e.val.out.2
  have he : s(a, b) = e.val := e.val.out_eq
  have hab : G.Adj a b := by
    rw [← SimpleGraph.mem_edgeSet, he]
    exact e.property
  have hmem : ∀ x : Fin m, x ∈ e.val → G.Reachable a x := by
    intro x hx
    rw [← he, Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · exact .rfl
    · exact hab.reachable
  let f : Fin (m + 2) → Fin m :=
    Fin.lastCases a (Fin.lastCases a id)
  have hold : ∀ x : Fin m, f x.castSucc.castSucc = x := by
    intro x
    simp [f]
  have hmid : f (Fin.last m).castSucc = a := by simp [f]
  have hnew : f (Fin.last (m + 1)) = a := by simp [f]
  have hadj : ∀ x y : Fin (m + 2), (graftGraph G (.inl e)).Adj x y →
      G.Reachable (f x) (f y) := by
    intro x y
    refine Fin.lastCases ?_ (fun x => ?_) x
    · refine Fin.lastCases ?_ (fun y => ?_) y
      · simp
      · refine Fin.lastCases ?_ (fun y => ?_) y
        · intro _
          rw [hnew, hmid]
        · simp
    · refine Fin.lastCases ?_ (fun x => ?_) x
      · refine Fin.lastCases ?_ (fun y => ?_) y
        · intro _
          rw [hmid, hnew]
        · refine Fin.lastCases ?_ (fun y => ?_) y
          · simp
          · intro h
            rw [hmid, hold]
            exact hmem y ((inl_adj_mid_old_cast G e y).mp h)
      · refine Fin.lastCases ?_ (fun y => ?_) y
        · simp
        · refine Fin.lastCases ?_ (fun y => ?_) y
          · intro h
            rw [hold, hmid]
            exact (hmem x ((inl_adj_old_mid_cast G e x).mp h)).symm
          · intro h
            rw [hold, hold]
            exact ((inl_adj_old_old_cast G e x y).mp h).1.reachable
  have hreach : ∀ u v : Fin (m + 2), (graftGraph G (.inl e)).Reachable u v →
      G.Reachable (f u) (f v) := by
    intro u v ⟨p⟩
    induction p with
    | nil => exact .rfl
    | cons h p ih => exact (hadj _ _ h).trans ih
  have hconn : G.Connected := by
    let _ : Nonempty (Fin m) := ⟨a⟩
    refine ⟨?_⟩
    intro x y
    simpa only [hold] using hreach _ _ (hG.connected x.castSucc.castSucc y.castSucc.castSucc)
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hconn, ?_⟩
  have hsum : (∑ x : Fin (m + 2), (graftGraph G (.inl e)).degree x) =
      (∑ x : Fin m, G.degree x) + 4 := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have ho : ∀ x : Fin m,
        (graftGraph G (.inl e)).degree x.castSucc.castSucc = G.degree x :=
      graftGraph_inl_degree_old G e
    simp_rw [ho]
    have hm : (graftGraph G (.inl e)).degree (Fin.last m).castSucc = 3 :=
      graftGraph_inl_degree_mid G e
    have hn : (graftGraph G (.inl e)).degree (Fin.last (m + 1)) = 1 :=
      graftGraph_inl_degree_new G e
    rw [hm, hn]
  have hnew := (graftGraph G (.inl e)).sum_degrees_eq_twice_card_edges
  have hold' := G.sum_degrees_eq_twice_card_edges
  have he' := hG.card_edgeFinset
  rw [hsum] at hnew
  simp only [SimpleGraph.edgeFinset_card, Fintype.card_fin,
    Nat.card_eq_fintype_card] at hnew hold' he' ⊢
  omega

/-- Delete the two last vertices and restore the edge between `a` and `b`. -/
def edgePruneGraph {m : ℕ} (G : SimpleGraph (Fin (m + 2))) (a b : Fin m) :
    SimpleGraph (Fin m) :=
  G.comap (fun x => x.castSucc.castSucc) ⊔ SimpleGraph.fromEdgeSet {s(a, b)}

/-- The restored edge in the pruned graph. -/
def edgePrunePosition {m : ℕ} (G : SimpleGraph (Fin (m + 2)))
    (a b : Fin m) (hab : a ≠ b) : (edgePruneGraph G a b).edgeSet :=
  ⟨s(a, b), by simp [SimpleGraph.mem_edgeSet, edgePruneGraph, hab]⟩

/-- Grafting after explicit deletion and suppression recovers the original graph. -/
theorem graftGraph_edgePruneGraph {m : ℕ} (G : SimpleGraph (Fin (m + 2)))
    (a b : Fin m) (hab : a ≠ b)
    (hnew : ∀ x, G.Adj (Fin.last (m + 1)) x ↔ x = (Fin.last m).castSucc)
    (hmid : ∀ x : Fin m, G.Adj (Fin.last m).castSucc x.castSucc.castSucc ↔
      x = a ∨ x = b)
    (hnot : ¬G.Adj a.castSucc.castSucc b.castSucc.castSucc) :
    graftGraph (edgePruneGraph G a b) (.inl (edgePrunePosition G a b hab)) = G := by
  have hremoved : ∀ x y : Fin m, G.Adj x.castSucc.castSucc y.castSucc.castSucc →
      s(x, y) ≠ s(a, b) := by
    intro x y hxy heq
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hnot hxy
    · exact hnot hxy.symm
  ext x y
  refine Fin.lastCases ?_ (fun x => ?_) x
  · rw [graftEdge_new_adj_iff, hnew]
  · refine Fin.lastCases ?_ (fun x => ?_) x
    · refine Fin.lastCases ?_ (fun y => ?_) y
      · rw [SimpleGraph.adj_comm, SimpleGraph.adj_comm (G := G),
          graftEdge_new_adj_iff, hnew]
      · refine Fin.lastCases ?_ (fun y => ?_) y
        · simp
        · rw [inl_adj_mid_old_cast, hmid]
          exact Sym2.mem_iff
    · refine Fin.lastCases ?_ (fun y => ?_) y
      · rw [SimpleGraph.adj_comm, SimpleGraph.adj_comm (G := G),
          graftEdge_new_adj_iff, hnew]
      · refine Fin.lastCases ?_ (fun y => ?_) y
        · rw [SimpleGraph.adj_comm, SimpleGraph.adj_comm (G := G),
            inl_adj_mid_old_cast, hmid]
          exact Sym2.mem_iff
        · rw [inl_adj_old_old_cast]
          change ((edgePruneGraph G a b).Adj x y ∧ s(x, y) ≠ s(a, b)) ↔ _
          simp only [edgePruneGraph, SimpleGraph.sup_adj, SimpleGraph.comap_adj,
            SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff]
          constructor
          · rintro ⟨h | ⟨h, _⟩, hne⟩
            · exact h
            · exact (hne h).elim
          · intro h
            exact ⟨Or.inl h, hremoved x y h⟩

/-- Explicit deletion and suppression of a terminal cherry preserves the tree property. -/
theorem edgePruneGraph_isTree {m : ℕ} (G : SimpleGraph (Fin (m + 2))) (hG : G.IsTree)
    (a b : Fin m) (hab : a ≠ b)
    (hnew : ∀ x, G.Adj (Fin.last (m + 1)) x ↔ x = (Fin.last m).castSucc)
    (hmid : ∀ x : Fin m, G.Adj (Fin.last m).castSucc x.castSucc.castSucc ↔
      x = a ∨ x = b)
    (hnot : ¬G.Adj a.castSucc.castSucc b.castSucc.castSucc) :
    (edgePruneGraph G a b).IsTree := by
  apply isTree_of_graftGraph_inl _ (edgePrunePosition G a b hab)
  rw [graftGraph_edgePruneGraph G a b hab hnew hmid hnot]
  exact hG

end BGW.StableTrees.Marchal
