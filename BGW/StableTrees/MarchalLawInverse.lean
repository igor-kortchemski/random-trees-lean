/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.MarchalChain
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Recovering parent graphs from Marchal grafts

An isomorphism of grafts that preserves the new leaf restricts to the old
vertices. In an edge graft it also preserves the new leaf's unique neighbour,
the midpoint, and the missing edge can be recovered from its neighbours.
-/

@[expose] public section

open scoped Classical

namespace BGW.StableTrees.Marchal

/-- Restrict an equivalence preserving the last element to the preceding elements. -/
def removeLastEquiv {m m' : ℕ} (e : Fin (m + 1) ≃ Fin (m' + 1))
    (he : e (Fin.last m) = Fin.last m') : Fin m ≃ Fin m' :=
  (finSuccAboveEquiv (Fin.last m)).trans
    ((e.subtypeEquiv (fun x => by rw [← he, e.injective.ne_iff])).trans
      (finSuccAboveEquiv (Fin.last m')).symm)

@[simp] theorem removeLastEquiv_castSucc {m m' : ℕ}
    (e : Fin (m + 1) ≃ Fin (m' + 1)) (he : e (Fin.last m) = Fin.last m')
    (x : Fin m) : (removeLastEquiv e he x).castSucc = e x.castSucc := by
  simp [removeLastEquiv, finSuccAboveEquiv_apply, finSuccAboveEquiv_symm_apply_last]

/-- An isomorphism of vertex grafts preserving the new leaf recovers their parents. -/
def ungraftVertexIso {n : ℕ} {T T' : LTree n}
    {v : {v : Fin T.m // 3 ≤ T.G.degree v}}
    {v' : {v : Fin T'.m // 3 ≤ T'.G.degree v}}
    (e : graftGraph T.G (.inr v) ≃g graftGraph T'.G (.inr v'))
    (he : e (Fin.last T.m) = Fin.last T'.m) : T.G ≃g T'.G where
  toEquiv := removeLastEquiv e.toEquiv he
  map_rel_iff' := by
    intro x y
    rw [← inr_adj_old_old_cast T'.G v', removeLastEquiv_castSucc,
      removeLastEquiv_castSucc]
    change (graftGraph T'.G (.inr v')).Adj (e x.castSucc) (e y.castSucc) ↔ _
    rw [e.map_rel_iff, inr_adj_old_old_cast]

/-- The parent isomorphism of vertex grafts takes the selected vertex to its counterpart. -/
theorem ungraftVertexIso_position {n : ℕ} {T T' : LTree n}
    {v : {v : Fin T.m // 3 ≤ T.G.degree v}}
    {v' : {v : Fin T'.m // 3 ≤ T'.G.degree v}}
    (e : graftGraph T.G (.inr v) ≃g graftGraph T'.G (.inr v'))
    (he : e (Fin.last T.m) = Fin.last T'.m) : ungraftVertexIso e he v.val = v'.val := by
  have h := (e.map_rel_iff).mpr (inr_adj_new_old_cast T.G v v.val |>.mpr rfl)
  rw [he] at h
  change (graftGraph T'.G (.inr v')).Adj (Fin.last T'.m) (e.toEquiv v.val.castSucc) at h
  rw [← removeLastEquiv_castSucc e.toEquiv he v.val,
    inr_adj_new_old_cast] at h
  exact h

/-- A new leaf in an edge graft has the midpoint as its unique neighbour. -/
theorem graftEdge_new_adj_iff {m : ℕ} (G : SimpleGraph (Fin m)) (a : G.edgeSet)
    (x : Fin (m + 2)) :
    (graftGraph G (.inl a)).Adj (Fin.last (m + 1)) x ↔
      x = (Fin.last m).castSucc := by
  refine Fin.lastCases ?_ (fun x => ?_) x
  · simp [eq_comm]
  · refine Fin.lastCases ?_ (fun x => ?_) x
    · simp
    · simp

/-- A graft isomorphism preserving the new leaf also preserves the midpoint. -/
theorem graftEdgeIso_midpoint {n : ℕ} {T T' : LTree n}
    {a : T.G.edgeSet} {a' : T'.G.edgeSet}
    (e : graftGraph T.G (.inl a) ≃g graftGraph T'.G (.inl a'))
    (he : e (Fin.last (T.m + 1)) = Fin.last (T'.m + 1)) :
    e (Fin.last T.m).castSucc = (Fin.last T'.m).castSucc := by
  have h := (e.map_rel_iff).mpr (inl_adj_new_mid_cast T.G a)
  rw [he, graftEdge_new_adj_iff] at h
  exact h

/-- Restriction of an edge-graft isomorphism to the original vertices. -/
def ungraftEdgeEquiv {n : ℕ} {T T' : LTree n}
    {a : T.G.edgeSet} {a' : T'.G.edgeSet}
    (e : graftGraph T.G (.inl a) ≃g graftGraph T'.G (.inl a'))
    (he : e (Fin.last (T.m + 1)) = Fin.last (T'.m + 1)) : Fin T.m ≃ Fin T'.m :=
  removeLastEquiv (removeLastEquiv e.toEquiv he) (by
    apply Fin.castSucc_injective
    rw [removeLastEquiv_castSucc]
    exact graftEdgeIso_midpoint e he)

@[simp] theorem ungraftEdgeEquiv_cast {n : ℕ} {T T' : LTree n}
    {a : T.G.edgeSet} {a' : T'.G.edgeSet}
    (e : graftGraph T.G (.inl a) ≃g graftGraph T'.G (.inl a'))
    (he : e (Fin.last (T.m + 1)) = Fin.last (T'.m + 1)) (x : Fin T.m) :
    (ungraftEdgeEquiv e he x).castSucc.castSucc = e x.castSucc.castSucc := by
  simp [ungraftEdgeEquiv]

/-- The endpoints of the removed edge are recovered as old neighbours of the midpoint. -/
theorem ungraftEdgeEquiv_mem {n : ℕ} {T T' : LTree n}
    {a : T.G.edgeSet} {a' : T'.G.edgeSet}
    (e : graftGraph T.G (.inl a) ≃g graftGraph T'.G (.inl a'))
    (he : e (Fin.last (T.m + 1)) = Fin.last (T'.m + 1)) (x : Fin T.m) :
    ungraftEdgeEquiv e he x ∈ a'.val ↔ x ∈ a.val := by
  rw [← inl_adj_mid_old_cast T'.G a', ungraftEdgeEquiv_cast,
    ← graftEdgeIso_midpoint e he, e.map_rel_iff, inl_adj_mid_old_cast]

/-- The parent equivalence recovers the edge that was subdivided. -/
theorem ungraftEdgeEquiv_edge {n : ℕ} {T T' : LTree n}
    {a : T.G.edgeSet} {a' : T'.G.edgeSet}
    (e : graftGraph T.G (.inl a) ≃g graftGraph T'.G (.inl a'))
    (he : e (Fin.last (T.m + 1)) = Fin.last (T'.m + 1)) :
    Sym2.map (ungraftEdgeEquiv e he) a.val = a'.val := by
  apply Sym2.ext
  intro y
  obtain ⟨x, rfl⟩ := (ungraftEdgeEquiv e he).surjective y
  rw [Sym2.mem_map]
  constructor
  · rintro ⟨z, hz, hzx⟩
    have hz' : z = x := (ungraftEdgeEquiv e he).injective hzx
    subst z
    exact (ungraftEdgeEquiv_mem e he x).mpr hz
  · intro hx
    exact ⟨x, (ungraftEdgeEquiv_mem e he x).mp hx, rfl⟩

/-- Removing the leaf and suppressing the midpoint recovers an edge-graft parent. -/
def ungraftEdgeIso {n : ℕ} {T T' : LTree n}
    {a : T.G.edgeSet} {a' : T'.G.edgeSet}
    (e : graftGraph T.G (.inl a) ≃g graftGraph T'.G (.inl a'))
    (he : e (Fin.last (T.m + 1)) = Fin.last (T'.m + 1)) : T.G ≃g T'.G where
  toEquiv := ungraftEdgeEquiv e he
  map_rel_iff' := by
    intro x y
    let f := ungraftEdgeEquiv e he
    have hedge : s(f x, f y) = a'.val ↔ s(x, y) = a.val := by
      rw [← ungraftEdgeEquiv_edge e he, ← Sym2.map_mk]
      exact (Sym2.map.injective f.injective).eq_iff
    have hadj : (T'.G.Adj (f x) (f y) ∧ s(f x, f y) ≠ a'.val) ↔
        (T.G.Adj x y ∧ s(x, y) ≠ a.val) := by
      rw [← inl_adj_old_old_cast T'.G a', ungraftEdgeEquiv_cast,
        ungraftEdgeEquiv_cast, e.map_rel_iff, inl_adj_old_old_cast]
    by_cases hxy : s(x, y) = a.val
    · have hxy' := hedge.mpr hxy
      have h₁ : T.G.Adj x y := by
        rw [← SimpleGraph.mem_edgeSet, hxy]
        exact a.property
      have h₂ : T'.G.Adj (f x) (f y) := by
        rw [← SimpleGraph.mem_edgeSet, hxy']
        exact a'.property
      exact iff_of_true h₂ h₁
    · exact ⟨fun h => (hadj.mp ⟨h, fun hh => hxy (hedge.mp hh)⟩).1,
        fun h => (hadj.mpr ⟨h, hxy⟩).1⟩

/-- A vertex graft cannot be isomorphic to an edge graft while preserving the new leaf. -/
theorem graftVertex_ne_edge {n : ℕ} {T T' : LTree n}
    (v : {v : Fin T.m // 3 ≤ T.G.degree v}) (a : T'.G.edgeSet)
    (e : graftGraph T.G (.inr v) ≃g graftGraph T'.G (.inl a))
    (he : e (Fin.last T.m) = Fin.last (T'.m + 1)) : False := by
  have hadj := (e.map_rel_iff).mpr (inr_adj_new_old_cast T.G v v.val |>.mpr rfl)
  rw [he, graftEdge_new_adj_iff] at hadj
  have hd := e.degree_eq v.val.castSucc
  rw [hadj] at hd
  have hmid : (graftGraph T'.G (.inl a)).degree (Fin.last T'.m).castSucc = 3 :=
    graftGraph_inl_degree_mid T'.G a
  have hv : (graftGraph T.G (.inr v)).degree v.val.castSucc = T.G.degree v.val + 1 :=
    graftGraph_inr_degree_old_self T.G v
  rw [hmid, hv] at hd
  have := v.property
  omega

/-- Equality of graft states determines the parent state, for either kind of position. -/
theorem graft_parent_eq {n : ℕ} {T T' : LTree n} (p : Position T.G) (q : Position T'.G)
    (h : (⟦graft T p⟧ : State (n + 1)) = ⟦graft T' q⟧) :
    (⟦T⟧ : State n) = ⟦T'⟧ := by
  obtain ⟨⟨e, he⟩⟩ := Quotient.exact h
  have hlast := he (Fin.last (n + 1))
  simp only [graft_labels_last] at hlast
  cases p with
  | inl a =>
    cases q with
    | inl a' =>
      apply Quotient.sound
      refine ⟨⟨ungraftEdgeIso e hlast, fun i => ?_⟩⟩
      have hi := he i.castSucc
      simp only [graft_labels_old] at hi
      apply Fin.castSucc_injective
      apply Fin.castSucc_injective
      rw [show (ungraftEdgeIso e hlast (T.labels i)).castSucc.castSucc =
        e (edgeOld (T.labels i)) from ungraftEdgeEquiv_cast e hlast _]
      exact hi
    | inr v' =>
      exact (graftVertex_ne_edge v' a e.symm (e.symm_apply_eq.mpr hlast.symm)).elim
  | inr v =>
    cases q with
    | inl a' => exact (graftVertex_ne_edge v a' e hlast).elim
    | inr v' =>
      apply Quotient.sound
      refine ⟨⟨ungraftVertexIso e hlast, fun i => ?_⟩⟩
      have hi := he i.castSucc
      simp only [graft_labels_old] at hi
      apply Fin.castSucc_injective
      rw [show (ungraftVertexIso e hlast (T.labels i)).castSucc =
        e.toEquiv (vertexOld (T.labels i)) from removeLastEquiv_castSucc e.toEquiv hlast _]
      exact hi

end BGW.StableTrees.Marchal
