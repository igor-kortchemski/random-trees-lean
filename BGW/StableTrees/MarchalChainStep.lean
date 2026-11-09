/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.MarchalChainGraft
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Functoriality of the Marchal step

A labelled graph isomorphism transports selection positions and induces an
isomorphism after grafting. The representative transition therefore descends
to the quotient state space.
-/

@[expose] public section

open scoped ENNReal Classical

namespace BGW.StableTrees.Marchal

/-- Transport of old, midpoint and new vertices under an equivalence. -/
def edgeVertexCongr {m m' : ℕ} (e : Fin m ≃ Fin m') : Fin (m + 2) ≃ Fin (m' + 2) where
  toFun := Fin.lastCases (Fin.last (m' + 1)) (Fin.lastCases (Fin.last m').castSucc
    (fun x => (e x).castSucc.castSucc))
  invFun := Fin.lastCases (Fin.last (m + 1)) (Fin.lastCases (Fin.last m).castSucc
    (fun x => (e.symm x).castSucc.castSucc))
  left_inv i := by
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun x => ?_) i
      · simp
      · simp
  right_inv i := by
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun x => ?_) i
      · simp
      · simp

/-- Transport of old and new vertices under an equivalence. -/
def vertexVertexCongr {m m' : ℕ} (e : Fin m ≃ Fin m') : Fin (m + 1) ≃ Fin (m' + 1) where
  toFun := Fin.lastCases (Fin.last m') (fun x => (e x).castSucc)
  invFun := Fin.lastCases (Fin.last m) (fun x => (e.symm x).castSucc)
  left_inv i := by
    refine Fin.lastCases ?_ (fun x => ?_) i <;>
      simp
  right_inv i := by
    refine Fin.lastCases ?_ (fun x => ?_) i <;>
      simp

@[simp] theorem inr_adj_new_old_cast {m : ℕ} (G : SimpleGraph (Fin m))
    (v : {v : Fin m // 3 ≤ G.degree v}) (x : Fin m) :
    (graftGraph G (.inr v)).Adj (Fin.last m) x.castSucc ↔ x = v.val :=
  graftGraph_inr_adj_new_old G v x

@[simp] theorem inr_adj_old_new_cast {m : ℕ} (G : SimpleGraph (Fin m))
    (v : {v : Fin m // 3 ≤ G.degree v}) (x : Fin m) :
    (graftGraph G (.inr v)).Adj x.castSucc (Fin.last m) ↔ x = v.val :=
  graftGraph_inr_adj_old_new G v x

@[simp] theorem inr_adj_old_old_cast {m : ℕ} (G : SimpleGraph (Fin m))
    (v : {v : Fin m // 3 ≤ G.degree v}) (x y : Fin m) :
    (graftGraph G (.inr v)).Adj x.castSucc y.castSucc ↔ G.Adj x y :=
  graftGraph_inr_adj_old_old G v x y

@[simp] theorem inl_adj_new_mid_cast {m : ℕ} (G : SimpleGraph (Fin m))
    (e : G.edgeSet) :
    (graftGraph G (.inl e)).Adj (Fin.last (m + 1)) (Fin.last m).castSucc :=
  graftGraph_inl_adj_new_mid G e

@[simp] theorem inl_adj_new_old_cast {m : ℕ} (G : SimpleGraph (Fin m))
    (e : G.edgeSet) (x : Fin m) :
    ¬(graftGraph G (.inl e)).Adj (Fin.last (m + 1)) x.castSucc.castSucc :=
  graftGraph_inl_adj_new_old G e x

@[simp] theorem inl_adj_mid_new_cast {m : ℕ} (G : SimpleGraph (Fin m))
    (e : G.edgeSet) :
    (graftGraph G (.inl e)).Adj (Fin.last m).castSucc (Fin.last (m + 1)) :=
  graftGraph_inl_adj_mid_new G e

@[simp] theorem inl_adj_mid_old_cast {m : ℕ} (G : SimpleGraph (Fin m))
    (e : G.edgeSet) (x : Fin m) :
    (graftGraph G (.inl e)).Adj (Fin.last m).castSucc x.castSucc.castSucc ↔ x ∈ e.val :=
  graftGraph_inl_adj_mid_old G e x

@[simp] theorem inl_adj_old_new_cast {m : ℕ} (G : SimpleGraph (Fin m))
    (e : G.edgeSet) (x : Fin m) :
    ¬(graftGraph G (.inl e)).Adj x.castSucc.castSucc (Fin.last (m + 1)) :=
  graftGraph_inl_adj_old_new G e x

@[simp] theorem inl_adj_old_mid_cast {m : ℕ} (G : SimpleGraph (Fin m))
    (e : G.edgeSet) (x : Fin m) :
    (graftGraph G (.inl e)).Adj x.castSucc.castSucc (Fin.last m).castSucc ↔ x ∈ e.val :=
  graftGraph_inl_adj_old_mid G e x

@[simp] theorem inl_adj_old_old_cast {m : ℕ} (G : SimpleGraph (Fin m))
    (e : G.edgeSet) (x y : Fin m) :
    (graftGraph G (.inl e)).Adj x.castSucc.castSucc y.castSucc.castSucc ↔
      G.Adj x y ∧ s(x, y) ≠ e.val :=
  graftGraph_inl_adj_old_old G e x y

/-- The positions transported by a graph isomorphism. -/
noncomputable def positionCongr {n : ℕ} {T T' : LTree n} (e : T.G ≃g T'.G) :
    Position T.G ≃ Position T'.G :=
  Equiv.sumCongr e.mapEdgeSet (LTree.internalEquiv e)

/-- Grafting on corresponding branch vertices gives isomorphic graphs. -/
noncomputable def graftVertexIso {n : ℕ} {T T' : LTree n} (e : T.G ≃g T'.G)
    (v : {v : Fin T.m // 3 ≤ T.G.degree v}) :
    graftGraph T.G (.inr v) ≃g
      graftGraph T'.G (.inr (LTree.internalEquiv e v)) where
  toEquiv := vertexVertexCongr e.toEquiv
  map_rel_iff' := by
    intro x y
    refine Fin.lastCases ?_ (fun a => ?_) x <;>
      refine Fin.lastCases ?_ (fun b => ?_) y <;>
      simp [vertexVertexCongr, LTree.internalEquiv]
    exact e.map_rel_iff

/-- Grafting on corresponding edges gives isomorphic graphs. -/
noncomputable def graftEdgeIso {n : ℕ} {T T' : LTree n} (e : T.G ≃g T'.G)
    (a : T.G.edgeSet) :
    graftGraph T.G (.inl a) ≃g graftGraph T'.G (.inl (e.mapEdgeSet a)) where
  toEquiv := edgeVertexCongr e.toEquiv
  map_rel_iff' := by
    intro x y
    refine Fin.lastCases ?_ (fun x => ?_) x
    · refine Fin.lastCases ?_ (fun y => ?_) y
      · simp [edgeVertexCongr]
      · refine Fin.lastCases ?_ (fun b => ?_) y
        · simp [edgeVertexCongr]
        · simp [edgeVertexCongr]
    · refine Fin.lastCases ?_ (fun x => ?_) x
      · refine Fin.lastCases ?_ (fun y => ?_) y
        · simp [edgeVertexCongr]
        · refine Fin.lastCases ?_ (fun b => ?_) y
          · simp [edgeVertexCongr]
          · simp [edgeVertexCongr, SimpleGraph.Iso.mapEdgeSet, Sym2.mem_map]
      · refine Fin.lastCases ?_ (fun y => ?_) y
        · simp [edgeVertexCongr]
        · refine Fin.lastCases ?_ (fun b => ?_) y
          · simp [edgeVertexCongr]
          · simp [edgeVertexCongr, SimpleGraph.Iso.mapEdgeSet]
            rw [← Sym2.map_mk, e.map_rel_iff]
            simp only [(Sym2.map.injective e.injective).eq_iff]

private theorem edgeNew_not_label_range {n : ℕ} (T : LTree n) :
    edgeNewLeaf T.m ∉ Set.range (T.labels.trans (Fin.castAddEmb 2)) := by
  rintro ⟨i, hi⟩
  have hval := congrArg (fun w : Fin (T.m + 2) => w.val) hi
  change (T.labels i).val = T.m + 1 at hval
  omega

private theorem vertexNew_not_label_range {n : ℕ} (T : LTree n) :
    vertexNewLeaf T.m ∉ Set.range (T.labels.trans (Fin.castAddEmb 1)) := by
  rintro ⟨i, hi⟩
  have hval := congrArg (fun w : Fin (T.m + 1) => w.val) hi
  change (T.labels i).val = T.m at hval
  omega

@[simp] theorem graft_labels_last {n : ℕ} (T : LTree n) (p : Position T.G) :
    (graft T p).labels (Fin.last (n + 1)) =
      match p with
      | .inl _ => edgeNewLeaf T.m
      | .inr _ => vertexNewLeaf T.m := by
  cases p with
  | inl e => exact extendLast_apply_last _ _ (edgeNew_not_label_range T)
  | inr v => exact extendLast_apply_last _ _ (vertexNew_not_label_range T)

@[simp] theorem graft_labels_old {n : ℕ} (T : LTree n) (p : Position T.G)
    (i : Fin (n + 1)) :
    (graft T p).labels i.castSucc =
      match p with
      | .inl _ => edgeOld (T.labels i)
      | .inr _ => vertexOld (T.labels i) := by
  cases p with
  | inl e => exact extendLast_apply_old _ _ (edgeNew_not_label_range T) i
  | inr v => exact extendLast_apply_old _ _ (vertexNew_not_label_range T) i


/-- Grafting commutes with labelled isomorphism, through `positionCongr`. -/
theorem graft_congr {n : ℕ} {T T' : LTree n} (e : T.G ≃g T'.G)
    (he : ∀ i, e (T.labels i) = T'.labels i) (p : Position T.G) :
    (⟦graft T p⟧ : State (n + 1)) = ⟦graft T' (positionCongr e p)⟧ := by
  apply Quotient.sound
  cases p with
  | inl a =>
    refine ⟨⟨graftEdgeIso e a, ?_⟩⟩
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [graft_labels_last, graft_labels_last]
      change (edgeVertexCongr e.toEquiv) (edgeNewLeaf T.m) = edgeNewLeaf T'.m
      rw [show edgeNewLeaf T.m = Fin.last (T.m + 1) from rfl,
        show edgeNewLeaf T'.m = Fin.last (T'.m + 1) from rfl]
      change (Fin.lastCases _ _ (Fin.last (T.m + 1)) : Fin (T'.m + 2)) =
        Fin.last (T'.m + 1)
      exact Fin.lastCases_last
    · rw [graft_labels_old, graft_labels_old]
      change (edgeVertexCongr e.toEquiv) (edgeOld (T.labels j)) = edgeOld (T'.labels j)
      rw [show edgeOld (T.labels j) = (T.labels j).castSucc.castSucc from rfl,
        show edgeOld (T'.labels j) = (T'.labels j).castSucc.castSucc from rfl]
      change (Fin.lastCases _ _ (T.labels j).castSucc.castSucc : Fin (T'.m + 2)) =
        (T'.labels j).castSucc.castSucc
      simp only [Fin.lastCases_castSucc]
      exact congrArg (fun x => x.castSucc.castSucc) (he j)
  | inr v =>
    refine ⟨⟨graftVertexIso e v, ?_⟩⟩
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [graft_labels_last, graft_labels_last]
      change (vertexVertexCongr e.toEquiv) (vertexNewLeaf T.m) = vertexNewLeaf T'.m
      rw [show vertexNewLeaf T.m = Fin.last T.m from rfl,
        show vertexNewLeaf T'.m = Fin.last T'.m from rfl]
      change (Fin.lastCases _ _ (Fin.last T.m) : Fin (T'.m + 1)) = Fin.last T'.m
      exact Fin.lastCases_last
    · rw [graft_labels_old, graft_labels_old]
      change (vertexVertexCongr e.toEquiv) (vertexOld (T.labels j)) = vertexOld (T'.labels j)
      rw [show vertexOld (T.labels j) = (T.labels j).castSucc from rfl,
        show vertexOld (T'.labels j) = (T'.labels j).castSucc from rfl]
      change (Fin.lastCases _ _ (T.labels j).castSucc : Fin (T'.m + 1)) =
        (T'.labels j).castSucc
      simp only [Fin.lastCases_castSucc]
      exact congrArg (fun x => x.castSucc) (he j)

private theorem map_equiv_apply {α β : Type*} (E : α ≃ β) (p : PMF α) (b : β) :
    p.map E b = p (E.symm b) := by
  rw [PMF.map_apply]
  rw [tsum_eq_single (E.symm b)]
  · simp
  · intro a ha
    simp only [ite_eq_right_iff]
    intro h
    exfalso
    apply ha
    apply E.injective
    simpa using h.symm

/-- One Marchal step on a representative: select a position (`selectionPMF`), graft, take class. -/
noncomputable def stepRep {k : ℕ} {α : ℝ} (hα : 1 < α) (hα2 : α ≤ 2) (T : LTree (k + 1)) :
    PMF (State (k + 2)) :=
  (selectionPMF T.G T.tree T.labels T.leaf T.branch (Nat.le_add_left 1 k) α hα hα2).map
    fun p => ⟦graft T p⟧

/-- Grafting commutes with labelled isomorphism, up to the induced bijection of positions. -/
theorem stepRep_congr {k : ℕ} {α : ℝ} (hα : 1 < α) (hα2 : α ≤ 2) {T T' : LTree (k + 1)}
    (h : T ≈ T') : stepRep hα hα2 T = stepRep hα hα2 T' := by
  obtain ⟨⟨e, he⟩⟩ := h
  let E := positionCongr e
  have hsel :
      (selectionPMF T.G T.tree T.labels T.leaf T.branch (Nat.le_add_left 1 k)
        α hα hα2).map E =
      selectionPMF T'.G T'.tree T'.labels T'.leaf T'.branch (Nat.le_add_left 1 k)
        α hα hα2 := by
    ext p
    rw [← E.apply_symm_apply p, map_equiv_apply]
    cases q : E.symm p with
    | inl a =>
      have hp : E (.inl a) = p := by rw [← q]; exact E.apply_symm_apply p
      simp [E, positionCongr, selectionWeight]
    | inr v =>
      have hp : E (.inr v) = p := by rw [← q]; exact E.apply_symm_apply p
      simp [E, positionCongr, selectionWeight, LTree.internalEquiv, e.degree_eq]
  unfold stepRep
  have hfun :
      (fun p' : Position T'.G => (⟦graft T' p'⟧ : State (k + 2))) ∘ E =
        (fun p : Position T.G => (⟦graft T p⟧ : State (k + 2))) := by
    funext p
    exact (graft_congr e he p).symm
  rw [← hfun, ← PMF.map_comp, hsel]

/-- The transition kernel `State (k+1) → PMF (State (k+2))`. -/
noncomputable def step {α : ℝ} (hα : 1 < α) (hα2 : α ≤ 2) (k : ℕ) :
    State (k + 1) → PMF (State (k + 2)) :=
  Quotient.lift (stepRep hα hα2) fun _ _ h => stepRep_congr hα hα2 h

/-- Total selection weight at step `n = k+1` is `n α - 1`. -/
theorem sum_selectionWeight_step {k : ℕ} (T : LTree (k + 1)) (α : ℝ) :
    ∑ p : Position T.G, selectionWeight T.G α p = ((k + 1 : ℕ) : ℝ) * α - 1 :=
  sum_selectionWeight T.G T.tree T.labels T.leaf T.branch α

/-- The law of the state with leaves `A_0..A_{k+1}`, started from the edge `A_0 — A_1`. -/
noncomputable def law {α : ℝ} (hα : 1 < α) (hα2 : α ≤ 2) : (k : ℕ) → PMF (State (k + 1))
  | 0 => PMF.pure startState
  | k + 1 => (law hα hα2 k).bind (step hα hα2 k)

end BGW.StableTrees.Marchal
