/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.MarchalChainFinite
import Mathlib.Tactic.FinCases

/-!
# Grafting a leaf on a finite tree

The graph operation either adds a leaf at an existing branch vertex or
subdivides an edge and attaches the new leaf to the subdivision vertex.
-/

@[expose] public section

open scoped ENNReal Classical

namespace BGW.StableTrees.Marchal

/-- Graft a new leaf `A_{n+1}` (the last vertex) on the middle of an edge (new midpoint `m`,
new leaf `m+1`) or on an internal vertex (new leaf `m`). -/
noncomputable def graftGraph {m : ℕ} (G : SimpleGraph (Fin m)) :
    (p : G.edgeSet ⊕ {v : Fin m // 3 ≤ G.degree v}) →
      SimpleGraph (Fin (match p with | .inl _ => m + 2 | .inr _ => m + 1))
  | .inl e => SimpleGraph.fromRel fun x y =>
      (∃ x' y' : Fin m, x.val = x'.val ∧ y.val = y'.val ∧ G.Adj x' y' ∧ s(x', y') ≠ e.val) ∨
      (x.val = m ∧ (y.val = m + 1 ∨ ∃ z : Fin m, z ∈ (e.val : Sym2 (Fin m)) ∧ y.val = z.val))
  | .inr v => SimpleGraph.fromRel fun x y =>
      (∃ x' y' : Fin m, x.val = x'.val ∧ y.val = y'.val ∧ G.Adj x' y') ∨
      (x.val = m ∧ y.val = v.val.val)

/-- The new leaf in a vertex graft. -/
def vertexNewLeaf (m : ℕ) : Fin (m + 1) := ⟨m, by omega⟩

/-- Old vertices in a vertex graft. -/
def vertexOld {m : ℕ} (x : Fin m) : Fin (m + 1) := Fin.castAdd 1 x

@[simp] theorem graftGraph_inr_adj_old_old {m : ℕ} (G : SimpleGraph (Fin m))
    (v : {v : Fin m // 3 ≤ G.degree v}) (x y : Fin m) :
    (graftGraph G (.inr v)).Adj (vertexOld x) (vertexOld y) ↔ G.Adj x y := by
  simp only [graftGraph, SimpleGraph.fromRel_adj, vertexOld, Fin.val_castAdd]
  constructor
  · rintro ⟨hne, h | h⟩
    · rcases h with ⟨x', y', hx, hy, hadj⟩ | ⟨hx, hy⟩
      · have ex : x = x' := Fin.ext hx
        have ey : y = y' := Fin.ext hy
        simpa [ex, ey] using hadj
      · omega
    · rcases h with ⟨x', y', hx, hy, hadj⟩ | ⟨hx, hy⟩
      · have ex : x = y' := Fin.ext hy
        have ey : y = x' := Fin.ext hx
        simpa [ex, ey] using hadj.symm
      · omega
  · intro hadj
    refine ⟨?_, Or.inl (Or.inl ⟨x, y, rfl, rfl, hadj⟩)⟩
    intro h
    exact hadj.ne (Fin.ext (congrArg (fun z : Fin (m + 1) => z.val) h))

@[simp] theorem graftGraph_inr_adj_old_new {m : ℕ} (G : SimpleGraph (Fin m))
    (v : {v : Fin m // 3 ≤ G.degree v}) (x : Fin m) :
    (graftGraph G (.inr v)).Adj (vertexOld x) (vertexNewLeaf m) ↔ x = v.val := by
  simp only [graftGraph, SimpleGraph.fromRel_adj, vertexOld, vertexNewLeaf,
    Fin.val_castAdd]
  constructor
  · rintro ⟨hne, h | h⟩
    · rcases h with ⟨x', y', hx, hy, hadj⟩ | ⟨hx, hy⟩ <;> omega
    · rcases h with ⟨x', y', hx, hy, hadj⟩ | ⟨hx, hy⟩
      · omega
      · exact Fin.ext hy
  · intro hxv
    subst x
    refine ⟨?_, Or.inr (Or.inr ⟨trivial, rfl⟩)⟩
    apply Fin.ne_of_val_ne
    simp only [Fin.val_castAdd]
    omega

theorem graftGraph_inr_adj_new_new {m : ℕ} (G : SimpleGraph (Fin m))
    (v : {v : Fin m // 3 ≤ G.degree v}) :
    ¬(graftGraph G (.inr v)).Adj (vertexNewLeaf m) (vertexNewLeaf m) := by
  simp

@[simp] theorem graftGraph_inr_adj_new_old {m : ℕ} (G : SimpleGraph (Fin m))
    (v : {v : Fin m // 3 ≤ G.degree v}) (x : Fin m) :
    (graftGraph G (.inr v)).Adj (vertexNewLeaf m) (vertexOld x) ↔ x = v.val := by
  rw [SimpleGraph.adj_comm]
  simp

private theorem inr_neighborFinset_new {m : ℕ} (G : SimpleGraph (Fin m))
    (v : {v : Fin m // 3 ≤ G.degree v}) :
    (graftGraph G (.inr v)).neighborFinset (vertexNewLeaf m) = {vertexOld v.val} := by
  ext y
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
  change Fin (m + 1) at y
  refine Fin.lastCases ?_ (fun z => ?_) y
  · change (graftGraph G (.inr v)).Adj (vertexNewLeaf m) (vertexNewLeaf m) ↔ _
    simp only [graftGraph_inr_adj_new_new, false_iff]
    intro h
    have hval := congrArg (fun z : Fin (m + 1) => z.val) h
    simp only [Fin.last, Fin.val_castAdd, vertexOld] at hval
    omega
  · change (graftGraph G (.inr v)).Adj (vertexNewLeaf m) (vertexOld z) ↔ _
    rw [graftGraph_inr_adj_new_old]
    constructor
    · intro h
      subst z
      rfl
    · intro h
      exact Fin.ext (congrArg (fun w : Fin (m + 1) => w.val) h)

@[simp] theorem graftGraph_inr_degree_new {m : ℕ} (G : SimpleGraph (Fin m))
    (v : {v : Fin m // 3 ≤ G.degree v}) :
    (graftGraph G (.inr v)).degree (vertexNewLeaf m) = 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, inr_neighborFinset_new,
    Finset.card_singleton]

private theorem inr_neighborFinset_old_of_ne {m : ℕ} (G : SimpleGraph (Fin m))
    (v : {v : Fin m // 3 ≤ G.degree v}) (x : Fin m) (hx : x ≠ v.val) :
    (graftGraph G (.inr v)).neighborFinset (vertexOld x) =
      (G.neighborFinset x).map (Fin.castAddEmb 1) := by
  ext y
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_map]
  change Fin (m + 1) at y
  refine Fin.lastCases ?_ (fun z => ?_) y
  · change (graftGraph G (.inr v)).Adj (vertexOld x) (vertexNewLeaf m) ↔ _
    rw [graftGraph_inr_adj_old_new]
    constructor
    · intro h
      exact (hx h).elim
    · rintro ⟨a, ha, hEq⟩
      have hval := congrArg (fun z : Fin (m + 1) => z.val) hEq
      simp only [Fin.coe_castAddEmb, Fin.val_castAdd, Fin.last] at hval
      omega
  · change (graftGraph G (.inr v)).Adj (vertexOld x) (vertexOld z) ↔ _
    rw [graftGraph_inr_adj_old_old]
    constructor
    · intro h
      exact ⟨z, h, rfl⟩
    · rintro ⟨a, ha, hEq⟩
      have haz : a = z := Fin.ext (congrArg (fun w : Fin (m + 1) => w.val) hEq)
      subst a
      exact ha

@[simp] theorem graftGraph_inr_degree_old_of_ne {m : ℕ} (G : SimpleGraph (Fin m))
    (v : {v : Fin m // 3 ≤ G.degree v}) (x : Fin m) (hx : x ≠ v.val) :
    (graftGraph G (.inr v)).degree (vertexOld x) = G.degree x := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, inr_neighborFinset_old_of_ne G v x hx,
    Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree]

private theorem inr_neighborFinset_old_self {m : ℕ} (G : SimpleGraph (Fin m))
    (v : {v : Fin m // 3 ≤ G.degree v}) :
    (graftGraph G (.inr v)).neighborFinset (vertexOld v.val) =
      insert (vertexNewLeaf m) ((G.neighborFinset v.val).map (Fin.castAddEmb 1)) := by
  ext y
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_map]
  change Fin (m + 1) at y
  refine Fin.lastCases ?_ (fun z => ?_) y
  · change (graftGraph G (.inr v)).Adj (vertexOld v.val) (vertexNewLeaf m) ↔ _
    rw [graftGraph_inr_adj_old_new]
    simp only [true_iff]
    exact Or.inl rfl
  · change (graftGraph G (.inr v)).Adj (vertexOld v.val) (vertexOld z) ↔ _
    rw [graftGraph_inr_adj_old_old]
    constructor
    · intro h
      exact Or.inr ⟨z, h, rfl⟩
    · rintro (h | ⟨a, ha, hEq⟩)
      · have hval := congrArg (fun z : Fin (m + 1) => z.val) h
        simp only [Fin.val_castSucc, vertexNewLeaf] at hval
        omega
      · have haz : a = z := Fin.ext (congrArg (fun w : Fin (m + 1) => w.val) hEq)
        subst a
        exact ha

@[simp] theorem graftGraph_inr_degree_old_self {m : ℕ} (G : SimpleGraph (Fin m))
    (v : {v : Fin m // 3 ≤ G.degree v}) :
    (graftGraph G (.inr v)).degree (vertexOld v.val) = G.degree v.val + 1 := by
  have hnew : vertexNewLeaf m ∉ (G.neighborFinset v.val).map (Fin.castAddEmb 1) := by
    intro h
    obtain ⟨x, hx, hxnew⟩ := Finset.mem_map.mp h
    have hval := congrArg (fun z : Fin (m + 1) => z.val) hxnew
    simp only [Fin.coe_castAddEmb, Fin.val_castAdd, vertexNewLeaf] at hval
    omega
  rw [← SimpleGraph.card_neighborFinset_eq_degree, inr_neighborFinset_old_self,
    Finset.card_insert_of_notMem hnew, Finset.card_map,
    SimpleGraph.card_neighborFinset_eq_degree]

/-- The subdivision midpoint in an edge graft. -/
def edgeMidpoint (m : ℕ) : Fin (m + 2) := ⟨m, by omega⟩

/-- The new leaf in an edge graft. -/
def edgeNewLeaf (m : ℕ) : Fin (m + 2) := ⟨m + 1, by omega⟩

/-- Old vertices in an edge graft. -/
def edgeOld {m : ℕ} (x : Fin m) : Fin (m + 2) := Fin.castAdd 2 x

@[simp] theorem graftGraph_inl_adj_old_old {m : ℕ} (G : SimpleGraph (Fin m))
    (e : G.edgeSet) (x y : Fin m) :
    (graftGraph G (.inl e)).Adj (edgeOld x) (edgeOld y) ↔
      G.Adj x y ∧ s(x, y) ≠ e.val := by
  simp only [graftGraph, SimpleGraph.fromRel_adj, edgeOld, Fin.val_castAdd]
  constructor
  · rintro ⟨hne, h | h⟩
    · rcases h with ⟨x', y', hx, hy, hadj, hed⟩ | ⟨hx, hy⟩
      · have ex : x = x' := Fin.ext hx
        have ey : y = y' := Fin.ext hy
        simpa [ex, ey] using And.intro hadj hed
      · omega
    · rcases h with ⟨x', y', hx, hy, hadj, hed⟩ | ⟨hx, hy⟩
      · have ex : x = y' := Fin.ext hy
        have ey : y = x' := Fin.ext hx
        subst x
        subst y
        exact ⟨hadj.symm, fun h => hed (by rw [Sym2.eq_swap]; exact h)⟩
      · omega
  · rintro ⟨hadj, hed⟩
    refine ⟨?_, Or.inl (Or.inl ⟨x, y, rfl, rfl, hadj, hed⟩)⟩
    intro h
    exact hadj.ne (Fin.ext (congrArg (fun z : Fin (m + 2) => z.val) h))

@[simp] theorem graftGraph_inl_adj_old_mid {m : ℕ} (G : SimpleGraph (Fin m))
    (e : G.edgeSet) (x : Fin m) :
    (graftGraph G (.inl e)).Adj (edgeOld x) (edgeMidpoint m) ↔ x ∈ e.val := by
  simp only [graftGraph, SimpleGraph.fromRel_adj, edgeOld, edgeMidpoint, Fin.val_castAdd]
  constructor
  · rintro ⟨hne, h | h⟩
    · rcases h with ⟨x', y', hx, hy, hadj, hed⟩ | ⟨hx, hy⟩ <;> omega
    · rcases h with ⟨x', y', hx, hy, hadj, hed⟩ | ⟨hx, hy⟩
      · omega
      · rcases hy with hy | ⟨z, hz, hzx⟩
        · omega
        · have ex : x = z := Fin.ext hzx
          simpa [ex] using hz
  · intro hx
    refine ⟨?_, Or.inr (Or.inr ⟨trivial, Or.inr ⟨x, hx, rfl⟩⟩)⟩
    apply Fin.ne_of_val_ne
    simp only [Fin.val_castAdd]
    omega

@[simp] theorem graftGraph_inl_adj_mid_new {m : ℕ} (G : SimpleGraph (Fin m))
    (e : G.edgeSet) :
    (graftGraph G (.inl e)).Adj (edgeMidpoint m) (edgeNewLeaf m) := by
  simp only [graftGraph, SimpleGraph.fromRel_adj, edgeMidpoint, edgeNewLeaf]
  refine ⟨?_, Or.inl (Or.inr ⟨trivial, Or.inl trivial⟩)⟩
  apply Fin.ne_of_val_ne
  simp []

@[simp] theorem graftGraph_inl_adj_old_new {m : ℕ} (G : SimpleGraph (Fin m))
    (e : G.edgeSet) (x : Fin m) :
    ¬(graftGraph G (.inl e)).Adj (edgeOld x) (edgeNewLeaf m) := by
  simp only [graftGraph, SimpleGraph.fromRel_adj, edgeOld, edgeNewLeaf, Fin.val_castAdd]
  rintro ⟨hne, h | h⟩
  · rcases h with ⟨x', y', hx, hy, hadj, hed⟩ | ⟨hx, hy⟩
    · omega
    · rcases hy with hy | ⟨z, hz, hzy⟩ <;> omega
  · rcases h with ⟨x', y', hx, hy, hadj, hed⟩ | ⟨hx, hy⟩
    · omega
    · rcases hy with hy | ⟨z, hz, hzy⟩ <;> omega

theorem graftGraph_inl_adj_mid_mid {m : ℕ} (G : SimpleGraph (Fin m))
    (e : G.edgeSet) :
    ¬(graftGraph G (.inl e)).Adj (edgeMidpoint m) (edgeMidpoint m) := by
  simp

theorem graftGraph_inl_adj_new_new {m : ℕ} (G : SimpleGraph (Fin m))
    (e : G.edgeSet) :
    ¬(graftGraph G (.inl e)).Adj (edgeNewLeaf m) (edgeNewLeaf m) := by
  simp

@[simp] theorem graftGraph_inl_adj_mid_old {m : ℕ} (G : SimpleGraph (Fin m))
    (e : G.edgeSet) (x : Fin m) :
    (graftGraph G (.inl e)).Adj (edgeMidpoint m) (edgeOld x) ↔ x ∈ e.val := by
  rw [SimpleGraph.adj_comm]
  simp

@[simp] theorem graftGraph_inl_adj_new_old {m : ℕ} (G : SimpleGraph (Fin m))
    (e : G.edgeSet) (x : Fin m) :
    ¬(graftGraph G (.inl e)).Adj (edgeNewLeaf m) (edgeOld x) := by
  rw [SimpleGraph.adj_comm]
  simp

@[simp] theorem graftGraph_inl_adj_new_mid {m : ℕ} (G : SimpleGraph (Fin m))
    (e : G.edgeSet) :
    (graftGraph G (.inl e)).Adj (edgeNewLeaf m) (edgeMidpoint m) := by
  rw [SimpleGraph.adj_comm]
  simp

private theorem inl_neighborFinset_new {m : ℕ} (G : SimpleGraph (Fin m))
    (e : G.edgeSet) :
    (graftGraph G (.inl e)).neighborFinset (edgeNewLeaf m) = {edgeMidpoint m} := by
  ext y
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
  change Fin (m + 2) at y
  refine Fin.lastCases ?_ (fun y => ?_) y
  · change (graftGraph G (.inl e)).Adj (edgeNewLeaf m) (edgeNewLeaf m) ↔ _
    simp only [graftGraph_inl_adj_new_new, false_iff]
    intro h
    have hval := congrArg (fun z : Fin (m + 2) => z.val) h
    change m + 1 = m at hval
    omega
  · change Fin (m + 1) at y
    refine Fin.lastCases ?_ (fun z => ?_) y
    · change (graftGraph G (.inl e)).Adj (edgeNewLeaf m) (edgeMidpoint m) ↔ _
      simp only [graftGraph_inl_adj_new_mid, true_iff]
      rfl
    · change (graftGraph G (.inl e)).Adj (edgeNewLeaf m) (edgeOld z) ↔ _
      simp only [graftGraph_inl_adj_new_old, false_iff]
      intro h
      have hval := congrArg (fun w : Fin (m + 2) => w.val) h
      change z.val = m at hval
      omega

@[simp] theorem graftGraph_inl_degree_new {m : ℕ} (G : SimpleGraph (Fin m))
    (e : G.edgeSet) :
    (graftGraph G (.inl e)).degree (edgeNewLeaf m) = 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, inl_neighborFinset_new,
    Finset.card_singleton]

private theorem inl_neighborFinset_mid {m : ℕ} (G : SimpleGraph (Fin m))
    (e : G.edgeSet) :
    (graftGraph G (.inl e)).neighborFinset (edgeMidpoint m) =
      insert (edgeNewLeaf m) (e.val.toFinset.map (Fin.castAddEmb 2)) := by
  ext y
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_map,
    Sym2.mem_toFinset]
  change Fin (m + 2) at y
  refine Fin.lastCases ?_ (fun y => ?_) y
  · change (graftGraph G (.inl e)).Adj (edgeMidpoint m) (edgeNewLeaf m) ↔ _
    simp only [graftGraph_inl_adj_mid_new, true_iff]
    exact Or.inl rfl
  · change Fin (m + 1) at y
    refine Fin.lastCases ?_ (fun z => ?_) y
    · change (graftGraph G (.inl e)).Adj (edgeMidpoint m) (edgeMidpoint m) ↔ _
      simp only [graftGraph_inl_adj_mid_mid, false_iff]
      rintro (h | ⟨a, ha, hEq⟩)
      · have hval := congrArg (fun z : Fin (m + 2) => z.val) h
        change m = m + 1 at hval
        omega
      · have hval := congrArg (fun z : Fin (m + 2) => z.val) hEq
        change a.val = m at hval
        omega
    · change (graftGraph G (.inl e)).Adj (edgeMidpoint m) (edgeOld z) ↔ _
      rw [graftGraph_inl_adj_mid_old]
      constructor
      · intro hz
        exact Or.inr ⟨z, hz, rfl⟩
      · rintro (h | ⟨a, ha, hEq⟩)
        · have hval := congrArg (fun w : Fin (m + 2) => w.val) h
          change z.val = m + 1 at hval
          omega
        · have haz : a = z := Fin.ext (congrArg (fun w : Fin (m + 2) => w.val) hEq)
          simpa [haz] using ha

@[simp] theorem graftGraph_inl_degree_mid {m : ℕ} (G : SimpleGraph (Fin m))
    (e : G.edgeSet) :
    (graftGraph G (.inl e)).degree (edgeMidpoint m) = 3 := by
  have hnew : edgeNewLeaf m ∉ e.val.toFinset.map (Fin.castAddEmb 2) := by
    intro h
    obtain ⟨a, ha, hEq⟩ := Finset.mem_map.mp h
    have hval := congrArg (fun z : Fin (m + 2) => z.val) hEq
    simp only [Fin.coe_castAddEmb, Fin.val_castAdd, edgeNewLeaf] at hval
    omega
  have hcard : e.val.toFinset.card = 2 :=
    Sym2.card_toFinset_of_not_isDiag e.val (G.not_isDiag_of_mem_edgeSet e.property)
  rw [← SimpleGraph.card_neighborFinset_eq_degree, inl_neighborFinset_mid,
    Finset.card_insert_of_notMem hnew, Finset.card_map, hcard]

private theorem old_filtered_map_iff {m : ℕ} (G : SimpleGraph (Fin m))
    (e : G.edgeSet) (x z : Fin m) :
    (∃ a, (G.Adj x a ∧ s(x, a) ≠ e.val) ∧ edgeOld a = edgeOld z) ↔
      G.Adj x z ∧ s(x, z) ≠ e.val := by
  constructor
  · rintro ⟨a, ⟨ha, he⟩, hEq⟩
    have haz : a = z := Fin.ext (congrArg (fun w : Fin (m + 2) => w.val) hEq)
    simpa [haz] using And.intro ha he
  · intro h
    exact ⟨z, h, rfl⟩

private theorem inl_neighborFinset_old {m : ℕ} (G : SimpleGraph (Fin m))
    (e : G.edgeSet) (x : Fin m) :
    (graftGraph G (.inl e)).neighborFinset (edgeOld x) =
      (if _ : x ∈ e.val then {edgeMidpoint m} else ∅) ∪
        ((G.neighborFinset x).filter (fun y => s(x, y) ≠ e.val)).map
          (Fin.castAddEmb 2) := by
  by_cases hx : x ∈ e.val
  · simp only [hx, ↓reduceDIte, Finset.singleton_union]
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_map,
      Finset.mem_filter]
    change Fin (m + 2) at y
    refine Fin.lastCases ?_ (fun y => ?_) y
    · change (graftGraph G (.inl e)).Adj (edgeOld x) (edgeNewLeaf m) ↔ _
      simp only [graftGraph_inl_adj_old_new, false_iff]
      rintro (h | ⟨a, ha, hEq⟩)
      · have hval := congrArg (fun z : Fin (m + 2) => z.val) h
        change m + 1 = m at hval
        omega
      · have hval := congrArg (fun z : Fin (m + 2) => z.val) hEq
        change a.val = m + 1 at hval
        omega
    · change Fin (m + 1) at y
      refine Fin.lastCases ?_ (fun z => ?_) y
      · change (graftGraph G (.inl e)).Adj (edgeOld x) (edgeMidpoint m) ↔ _
        simp only [graftGraph_inl_adj_old_mid, hx, true_iff]
        exact Or.inl rfl
      · change (graftGraph G (.inl e)).Adj (edgeOld x) (edgeOld z) ↔ _
        rw [graftGraph_inl_adj_old_old]
        constructor
        · intro h
          exact Or.inr (old_filtered_map_iff G e x z |>.mpr h)
        · rintro (h | h)
          · have hval := congrArg (fun w : Fin (m + 2) => w.val) h
            change z.val = m at hval
            omega
          · exact (old_filtered_map_iff G e x z).mp h
  · simp only [hx, ↓reduceDIte, Finset.empty_union]
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_map, Finset.mem_filter]
    change Fin (m + 2) at y
    refine Fin.lastCases ?_ (fun y => ?_) y
    · change (graftGraph G (.inl e)).Adj (edgeOld x) (edgeNewLeaf m) ↔ _
      simp only [graftGraph_inl_adj_old_new, false_iff]
      rintro ⟨a, ha, hEq⟩
      have hval := congrArg (fun z : Fin (m + 2) => z.val) hEq
      change a.val = m + 1 at hval
      omega
    · change Fin (m + 1) at y
      refine Fin.lastCases ?_ (fun z => ?_) y
      · change (graftGraph G (.inl e)).Adj (edgeOld x) (edgeMidpoint m) ↔ _
        simp only [graftGraph_inl_adj_old_mid, hx, false_iff]
        rintro ⟨a, ha, hEq⟩
        have hval := congrArg (fun z : Fin (m + 2) => z.val) hEq
        change a.val = m at hval
        omega
      · change (graftGraph G (.inl e)).Adj (edgeOld x) (edgeOld z) ↔ _
        rw [graftGraph_inl_adj_old_old]
        exact (old_filtered_map_iff G e x z).symm

private theorem neighbor_filter_of_not_mem {m : ℕ} (G : SimpleGraph (Fin m))
    (e : G.edgeSet) (x : Fin m) (hx : x ∉ e.val) :
    (G.neighborFinset x).filter (fun y => s(x, y) ≠ e.val) = G.neighborFinset x := by
  ext y
  simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, and_iff_left_iff_imp]
  intro hxy heq
  apply hx
  rw [← heq]
  exact Sym2.mem_mk_left x y

private theorem neighbor_filter_of_mem {m : ℕ} (G : SimpleGraph (Fin m))
    (e : G.edgeSet) (x : Fin m) (hx : x ∈ e.val) :
    (G.neighborFinset x).filter (fun y => s(x, y) ≠ e.val) =
      (G.neighborFinset x).erase (Sym2.Mem.other hx) := by
  ext y
  simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, Finset.mem_erase]
  constructor
  · rintro ⟨hadj, hne⟩
    exact ⟨fun hy => hne (by rw [hy, Sym2.other_spec hx]), hadj⟩
  · rintro ⟨hy, hadj⟩
    refine ⟨hadj, fun heq => hy ?_⟩
    apply (Sym2.congr_right (a := x) (b := y) (c := Sym2.Mem.other hx)).mp
    exact heq.trans (Sym2.other_spec hx).symm

@[simp] theorem graftGraph_inl_degree_old {m : ℕ} (G : SimpleGraph (Fin m))
    (e : G.edgeSet) (x : Fin m) :
    (graftGraph G (.inl e)).degree (edgeOld x) = G.degree x := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, inl_neighborFinset_old]
  by_cases hx : x ∈ e.val
  · simp only [hx, ↓reduceDIte, Finset.singleton_union]
    rw [neighbor_filter_of_mem G e x hx]
    have hmid : edgeMidpoint m ∉
        ((G.neighborFinset x).erase (Sym2.Mem.other hx)).map (Fin.castAddEmb 2) := by
      intro h
      obtain ⟨a, ha, hEq⟩ := Finset.mem_map.mp h
      have hval := congrArg (fun z : Fin (m + 2) => z.val) hEq
      change a.val = m at hval
      omega
    have hox : Sym2.Mem.other hx ∈ G.neighborFinset x := by
      rw [SimpleGraph.mem_neighborFinset, ← SimpleGraph.mem_edgeSet, Sym2.other_spec hx]
      exact e.property
    rw [Finset.card_insert_of_notMem hmid, Finset.card_map, Finset.card_erase_add_one hox,
      SimpleGraph.card_neighborFinset_eq_degree]
  · simp only [hx, ↓reduceDIte, Finset.empty_union]
    rw [neighbor_filter_of_not_mem G e x hx, Finset.card_map,
      SimpleGraph.card_neighborFinset_eq_degree]

/-- An edge graft subdivides one edge and adds a leaf, hence remains a tree. -/
theorem graftGraph_inl_isTree {m : ℕ} (G : SimpleGraph (Fin m))
    (e : G.edgeSet) (hG : G.IsTree) :
    (graftGraph G (.inl e)).IsTree := by
  classical
  let H := graftGraph G (.inl e)
  have edge_reachable : ∀ {x y : Fin m}, G.Adj x y →
      H.Reachable (edgeOld x) (edgeOld y) := by
    intro x y hxy
    by_cases he : s(x, y) = e.val
    · have hx : x ∈ e.val := by rw [← he]; exact Sym2.mem_mk_left x y
      have hy : y ∈ e.val := by rw [← he]; exact Sym2.mem_mk_right x y
      exact (SimpleGraph.Adj.reachable ((graftGraph_inl_adj_old_mid G e x).mpr hx)).trans
        (SimpleGraph.Adj.reachable ((graftGraph_inl_adj_mid_old G e y).mpr hy))
    · exact SimpleGraph.Adj.reachable ((graftGraph_inl_adj_old_old G e x y).mpr ⟨hxy, he⟩)
  have old_reachable : ∀ {x y : Fin m}, G.Reachable x y →
      H.Reachable (edgeOld x) (edgeOld y) := by
    intro x y h
    obtain ⟨p⟩ := h
    induction p with
    | nil => exact SimpleGraph.Reachable.rfl
    | cons h p ih => exact (edge_reachable h).trans ih
  have hz : e.val.out.1 ∈ e.val := Sym2.out_fst_mem e.val
  have hconn : H.Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨edgeOld e.val.out.1, fun y => ?_⟩
    change Fin (m + 2) at y
    refine Fin.lastCases ?_ (fun y => ?_) y
    · change H.Reachable (edgeOld e.val.out.1) (edgeNewLeaf m)
      exact (SimpleGraph.Adj.reachable ((graftGraph_inl_adj_old_mid G e _).mpr hz)).trans
        (SimpleGraph.Adj.reachable (graftGraph_inl_adj_mid_new G e))
    · change Fin (m + 1) at y
      refine Fin.lastCases ?_ (fun z => ?_) y
      · change H.Reachable (edgeOld e.val.out.1) (edgeMidpoint m)
        exact SimpleGraph.Adj.reachable ((graftGraph_inl_adj_old_mid G e _).mpr hz)
      · exact old_reachable (hG.connected _ z)
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hconn, ?_⟩
  have hsum : (∑ x : Fin (m + 2), H.degree x) = (∑ x : Fin m, G.degree x) + 4 := by
    rw [Fin.sum_univ_castSucc]
    change (∑ x : Fin (m + 1), H.degree (Fin.castSucc x)) +
      H.degree (edgeNewLeaf m) = _
    rw [Fin.sum_univ_castSucc]
    change (∑ x : Fin m, H.degree (edgeOld x)) + H.degree (edgeMidpoint m) +
      H.degree (edgeNewLeaf m) = _
    have ho : ∀ x : Fin m, H.degree (edgeOld x) = G.degree x :=
      fun x => graftGraph_inl_degree_old G e x
    simp_rw [ho]
    change _ + (graftGraph G (.inl e)).degree (edgeMidpoint m) +
      (graftGraph G (.inl e)).degree (edgeNewLeaf m) = _
    rw [graftGraph_inl_degree_mid, graftGraph_inl_degree_new]
  have hnew := H.sum_degrees_eq_twice_card_edges
  have hold := G.sum_degrees_eq_twice_card_edges
  rw [hsum] at hnew
  have he := hG.card_edgeFinset
  simp only [SimpleGraph.edgeFinset_card, Fintype.card_fin,
    Nat.card_eq_fintype_card] at hnew hold he ⊢
  change Fintype.card H.edgeSet + 1 = m + 2
  omega

/-- A vertex graft adds exactly one edge and preserves connectivity. -/
theorem graftGraph_inr_isTree {m : ℕ} (G : SimpleGraph (Fin m))
    (v : {v : Fin m // 3 ≤ G.degree v}) (hG : G.IsTree) :
    (graftGraph G (.inr v)).IsTree := by
  classical
  let H := graftGraph G (.inr v)
  let f : G →g H :=
    { toFun := vertexOld
      map_rel' := fun h => (graftGraph_inr_adj_old_old G v _ _).mpr h }
  have hconn : H.Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨vertexOld v.val, fun y => ?_⟩
    change Fin (m + 1) at y
    refine Fin.lastCases ?_ (fun z => ?_) y
    · change H.Reachable (vertexOld v.val) (vertexNewLeaf m)
      exact SimpleGraph.Adj.reachable ((graftGraph_inr_adj_old_new G v v.val).mpr rfl)
    · change H.Reachable (f v.val) (f z)
      exact (hG.connected v.val z).map f
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hconn, ?_⟩
  have hsumOld : (∑ x : Fin m, H.degree (vertexOld x)) =
      (∑ x : Fin m, G.degree x) + 1 := by
    calc
      _ = ∑ x : Fin m, (G.degree x + if x = v.val then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x = v.val
        · subst x
          simp only [↓reduceIte]
          exact graftGraph_inr_degree_old_self G v
        · simp only [hx, ↓reduceIte]
          exact graftGraph_inr_degree_old_of_ne G v x hx
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  have hsum : (∑ x : Fin (m + 1), H.degree x) = (∑ x : Fin m, G.degree x) + 2 := by
    rw [Fin.sum_univ_castSucc]
    change (∑ x : Fin m, H.degree (vertexOld x)) + H.degree (vertexNewLeaf m) = _
    rw [hsumOld]
    change _ + (graftGraph G (.inr v)).degree (vertexNewLeaf m) = _
    rw [graftGraph_inr_degree_new]
  have hnew := H.sum_degrees_eq_twice_card_edges
  have hold := G.sum_degrees_eq_twice_card_edges
  rw [hsum] at hnew
  have he := hG.card_edgeFinset
  simp only [SimpleGraph.edgeFinset_card, Fintype.card_fin,
    Nat.card_eq_fintype_card] at hnew hold he ⊢
  change Fintype.card H.edgeSet + 1 = m + 1
  omega

/-- Extend a label embedding by a new final label outside its range. -/
def extendLast {n M : ℕ} (f : Fin (n + 1) ↪ Fin M) (z : Fin M)
    (hz : z ∉ Set.range f) : Fin (n + 2) ↪ Fin M where
  toFun := Fin.lastCases z f
  inj' := by
    intro i
    refine Fin.lastCases ?_ (fun a => ?_) i
    · intro j
      refine Fin.lastCases ?_ (fun b => ?_) j
      · intro _
        rfl
      · intro h
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at h
        exact (hz ⟨b, h.symm⟩).elim
    · intro j
      refine Fin.lastCases ?_ (fun b => ?_) j
      · intro h
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at h
        exact (hz ⟨a, h⟩).elim
      · intro h
        simp only [Fin.lastCases_castSucc] at h
        exact congrArg Fin.castSucc (f.injective h)

@[simp] theorem extendLast_apply_last {n M : ℕ} (f : Fin (n + 1) ↪ Fin M)
    (z : Fin M) (hz : z ∉ Set.range f) :
    extendLast f z hz (Fin.last (n + 1)) = z := by
  simp [extendLast]

@[simp] theorem extendLast_apply_old {n M : ℕ} (f : Fin (n + 1) ↪ Fin M)
    (z : Fin M) (hz : z ∉ Set.range f) (i : Fin (n + 1)) :
    extendLast f z hz i.castSucc = f i := by
  simp [extendLast]

/-- The range after extending labels is the new label together with the old range. -/
theorem range_extendLast {n M : ℕ} (f : Fin (n + 1) ↪ Fin M) (z : Fin M)
    (hz : z ∉ Set.range f) (y : Fin M) :
    y ∈ Set.range (extendLast f z hz) ↔ y = z ∨ y ∈ Set.range f := by
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.lastCases ?_ (fun a => ?_) i
    · exact Or.inl (extendLast_apply_last f z hz)
    · exact Or.inr ⟨a, (extendLast_apply_old f z hz a).symm⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨Fin.last (n + 1), extendLast_apply_last f _ _⟩
    · exact ⟨i.castSucc, extendLast_apply_old f _ _ i⟩

private theorem old_vertex_not_new {m : ℕ} (x : Fin m) :
    vertexOld x ≠ vertexNewLeaf m := by
  intro h
  have hval := congrArg (fun z : Fin (m + 1) => z.val) h
  change x.val = m at hval
  omega

private theorem old_edge_not_mid {m : ℕ} (x : Fin m) :
    edgeOld x ≠ edgeMidpoint m := by
  intro h
  have hval := congrArg (fun z : Fin (m + 2) => z.val) h
  change x.val = m at hval
  omega

private theorem old_edge_not_new {m : ℕ} (x : Fin m) :
    edgeOld x ≠ edgeNewLeaf m := by
  intro h
  have hval := congrArg (fun z : Fin (m + 2) => z.val) h
  change x.val = m + 1 at hval
  omega

private theorem vertexMid_not_new {m : ℕ} : edgeMidpoint m ≠ edgeNewLeaf m := by
  intro h
  have hval := congrArg (fun z : Fin (m + 2) => z.val) h
  change m = m + 1 at hval
  omega

/-- The tree obtained by grafting `A_{n+1}` at a position of `T`. -/
noncomputable def graft {n : ℕ} (T : LTree n) (p : Position T.G) : LTree (n + 1) :=
  match p with
  | .inl e =>
    let f := T.labels.trans (Fin.castAddEmb 2)
    let z := edgeNewLeaf T.m
    have hz : z ∉ Set.range f := by
      rintro ⟨i, hi⟩
      have hval := congrArg (fun w : Fin (T.m + 2) => w.val) hi
      change (T.labels i).val = T.m + 1 at hval
      omega
    { m := T.m + 2
      G := graftGraph T.G (.inl e)
      tree := graftGraph_inl_isTree T.G e T.tree
      labels := extendLast f z hz
      leaf := by
        intro y
        change Fin (T.m + 2) at y
        refine Fin.lastCases ?_ (fun y => ?_) y
        · constructor
          · intro _
            exact ⟨Fin.last (n + 1), extendLast_apply_last f z hz⟩
          · intro _
            exact graftGraph_inl_degree_new T.G e
        · change Fin (T.m + 1) at y
          refine Fin.lastCases ?_ (fun x => ?_) y
          · have hrange : edgeMidpoint T.m ∉ Set.range (extendLast f z hz) := by
              rw [range_extendLast]
              rintro (h | h)
              · exact vertexMid_not_new h
              · obtain ⟨i, hi⟩ := h
                exact old_edge_not_mid (T.labels i) hi
            change (graftGraph T.G (.inl e)).degree (edgeMidpoint T.m) = 1 ↔ _
            rw [graftGraph_inl_degree_mid]
            exact iff_of_false (by omega) (fun hmem => hrange (by
              change edgeMidpoint T.m ∈ Set.range (extendLast f z hz) at hmem
              exact hmem))
          · change (graftGraph T.G (.inl e)).degree (edgeOld x) = 1 ↔ _
            rw [graftGraph_inl_degree_old]
            have hrange : edgeOld x ∈ Set.range (extendLast f z hz) ↔
                x ∈ Set.range T.labels := by
              rw [range_extendLast]
              constructor
              · rintro (h | ⟨i, hi⟩)
                · exact (old_edge_not_new x h).elim
                · exact ⟨i, Fin.ext (congrArg (fun w : Fin (T.m + 2) => w.val) hi)⟩
              · rintro ⟨i, hi⟩
                refine Or.inr ⟨i, ?_⟩
                change Fin.castAdd 2 (T.labels i) = edgeOld x
                exact congrArg (Fin.castAdd 2) hi
            change _ ↔ edgeOld x ∈ Set.range (extendLast f z hz)
            rw [hrange]
            exact T.leaf x
      branch := by
        intro y hy
        change Fin (T.m + 2) at y
        revert hy
        refine Fin.lastCases ?_ (fun y => ?_) y
        · intro hy
          change (graftGraph T.G (.inl e)).degree (edgeNewLeaf T.m) ≠ 1 at hy
          rw [graftGraph_inl_degree_new] at hy
          exact (hy rfl).elim
        · change Fin (T.m + 1) at y
          refine Fin.lastCases ?_ (fun x => ?_) y
          · intro _
            change 3 ≤ (graftGraph T.G (.inl e)).degree (edgeMidpoint T.m)
            rw [graftGraph_inl_degree_mid]
          · intro hy
            change (graftGraph T.G (.inl e)).degree (edgeOld x) ≠ 1 at hy
            change 3 ≤ (graftGraph T.G (.inl e)).degree (edgeOld x)
            rw [graftGraph_inl_degree_old] at hy ⊢
            exact T.branch x hy }
  | .inr v =>
    let f := T.labels.trans (Fin.castAddEmb 1)
    let z := vertexNewLeaf T.m
    have hz : z ∉ Set.range f := by
      rintro ⟨i, hi⟩
      have hval := congrArg (fun w : Fin (T.m + 1) => w.val) hi
      change (T.labels i).val = T.m at hval
      omega
    { m := T.m + 1
      G := graftGraph T.G (.inr v)
      tree := graftGraph_inr_isTree T.G v T.tree
      labels := extendLast f z hz
      leaf := by
        intro y
        change Fin (T.m + 1) at y
        refine Fin.lastCases ?_ (fun x => ?_) y
        · constructor
          · intro _
            exact ⟨Fin.last (n + 1), extendLast_apply_last f z hz⟩
          · intro _
            exact graftGraph_inr_degree_new T.G v
        · have hrange : vertexOld x ∈ Set.range (extendLast f z hz) ↔
              x ∈ Set.range T.labels := by
            rw [range_extendLast]
            constructor
            · rintro (h | ⟨i, hi⟩)
              · exact (old_vertex_not_new x h).elim
              · exact ⟨i, Fin.ext (congrArg (fun w : Fin (T.m + 1) => w.val) hi)⟩
            · rintro ⟨i, hi⟩
              refine Or.inr ⟨i, ?_⟩
              change Fin.castAdd 1 (T.labels i) = vertexOld x
              exact congrArg (Fin.castAdd 1) hi
          change (graftGraph T.G (.inr v)).degree (vertexOld x) = 1 ↔
            vertexOld x ∈ Set.range (extendLast f z hz)
          rw [hrange]
          by_cases hx : x = v.val
          · subst x
            have hv : T.G.degree v.val ≠ 1 := by
              have := v.property
              omega
            rw [graftGraph_inr_degree_old_self]
            exact iff_of_false (fun h => hv (by omega)) (fun h => hv ((T.leaf _).mpr h))
          · rw [graftGraph_inr_degree_old_of_ne T.G v x hx]
            exact T.leaf x
      branch := by
        intro y hy
        change Fin (T.m + 1) at y
        revert hy
        refine Fin.lastCases ?_ (fun x => ?_) y
        · intro hy
          change (graftGraph T.G (.inr v)).degree (vertexNewLeaf T.m) ≠ 1 at hy
          rw [graftGraph_inr_degree_new] at hy
          exact (hy rfl).elim
        · by_cases hx : x = v.val
          · intro _
            subst x
            change 3 ≤ (graftGraph T.G (.inr v)).degree (vertexOld v.val)
            rw [graftGraph_inr_degree_old_self]
            have := v.property
            omega
          · intro hy
            change (graftGraph T.G (.inr v)).degree (vertexOld x) ≠ 1 at hy
            change 3 ≤ (graftGraph T.G (.inr v)).degree (vertexOld x)
            rw [graftGraph_inr_degree_old_of_ne T.G v x hx] at hy ⊢
            exact T.branch x hy }

end BGW.StableTrees.Marchal
