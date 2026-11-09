/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.MarchalLawParents

/-!
# Pruning after placing the new leaf last

The degree-three case suppresses the penultimate vertex and restores the edge
between its other two neighbours.
-/

@[expose] public section

open scoped Classical

namespace BGW.StableTrees.Marchal

/-- Restrict old labels to a smaller initial segment containing them. -/
def restrictLabels {n m M : ℕ} (f : Fin (n + 2) ↪ Fin M)
    (h : ∀ i : Fin (n + 1), (f i.castSucc).val < m) : Fin (n + 1) ↪ Fin m where
  toFun i := ⟨(f i.castSucc).val, h i⟩
  inj' _ _ hij := Fin.castSucc_injective _
    (f.injective (Fin.ext (congrArg (fun x : Fin m => x.val) hij)))

/-- Canonical degree-three pruning gives a labelled parent. -/
theorem exists_graft_edge_canonical {n m : ℕ}
    (G : SimpleGraph (Fin (m + 2))) (tree : G.IsTree)
    (labels : Fin (n + 2) ↪ Fin (m + 2))
    (leaf : ∀ v, G.degree v = 1 ↔ v ∈ Set.range labels)
    (branch : ∀ v, G.degree v ≠ 1 → 3 ≤ G.degree v)
    (hlast : labels (Fin.last (n + 1)) = Fin.last (m + 1))
    (hnew : ∀ x, G.Adj (Fin.last (m + 1)) x ↔ x = (Fin.last m).castSucc)
    (hdegree : G.degree (Fin.last m).castSucc = 3) :
    ∃ S : LTree n, ∃ p : Position S.G, (⟦graft S p⟧ : State (n + 1)) =
      ⟦(⟨m + 2, G, tree, labels, leaf, branch⟩ : LTree (n + 1))⟧ := by
  classical
  let mid := (Fin.last m).castSucc
  let z := Fin.last (m + 1)
  have hmz : G.Adj mid z := ((hnew mid).mpr rfl).symm
  let s := (G.neighborFinset mid).erase z
  have hcard : s.card = 2 := by
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr hmz),
      G.card_neighborFinset_eq_degree, hdegree]
  obtain ⟨x, y, hxy, hs⟩ := Finset.card_eq_two.mp hcard
  have hxmem : x ∈ s := by rw [hs]; simp
  have hymem : y ∈ s := by rw [hs]; simp
  have hbound : ∀ v ∈ s, v.val < m := by
    intro v hv
    have hvz := (Finset.mem_erase.mp hv).1
    have hvm : v ≠ mid := by
      intro h
      have hvadj := (G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hv).2
      rw [h] at hvadj
      exact G.irrefl hvadj
    have hz := Fin.val_lt_last hvz
    have hm : v.val ≠ m := fun hh => hvm (Fin.ext hh)
    omega
  let a : Fin m := ⟨x.val, hbound x hxmem⟩
  let b : Fin m := ⟨y.val, hbound y hymem⟩
  have hxa : x = a.castSucc.castSucc := Fin.ext rfl
  have hyb : y = b.castSucc.castSucc := Fin.ext rfl
  have hab : a ≠ b := by
    intro h
    apply hxy
    rw [hxa, hyb, h]
  have hmid : ∀ v : Fin m, G.Adj mid v.castSucc.castSucc ↔ v = a ∨ v = b := by
    intro v
    calc
      _ ↔ v.castSucc.castSucc ∈ s := by simp [s, z]
      _ ↔ _ := by rw [hs, hxa, hyb]; simp
  have hma := (hmid a).mpr (Or.inl rfl)
  have hmb := (hmid b).mpr (Or.inr rfl)
  have hnot : ¬G.Adj a.castSucc.castSucc b.castSucc.castSucc := by
    intro hadj
    let p := SimpleGraph.Walk.cons hma.symm
      (SimpleGraph.Walk.cons hmb SimpleGraph.Walk.nil)
    have hp : p.IsPath := by
      simp [p, SimpleGraph.Walk.cons_isPath_iff, hab, mid]
      exact (Fin.castSucc_ne_last b).symm
    have heq := tree.isAcyclic.eq_snd_of_adj_start hp hadj (by simp [p])
    have hh := congrArg Fin.val heq
    change b.val = m at hh
    omega
  have hboundLabels : ∀ i : Fin (n + 1), (labels i.castSucc).val < m := by
    intro i
    have hdz : G.degree (labels i.castSucc) = 1 := (leaf _).mpr ⟨i.castSucc, rfl⟩
    have hneZ : labels i.castSucc ≠ z := by
      change labels i.castSucc ≠ Fin.last (m + 1)
      rw [← hlast]
      exact labels.injective.ne (Fin.castSucc_ne_last i)
    have hneM : labels i.castSucc ≠ mid := by
      intro h
      rw [h, hdegree] at hdz
      omega
    have hz := Fin.val_lt_last hneZ
    have hm : (labels i.castSucc).val ≠ m := fun hh => hneM (Fin.ext hh)
    omega
  let f := restrictLabels labels hboundLabels
  have hf : ∀ i, (f i).castSucc.castSucc = labels i.castSucc := fun _ => Fin.ext rfl
  let H := edgePruneGraph G a b
  let e := edgePrunePosition G a b hab
  have hrec : graftGraph H (.inl e) = G :=
    graftGraph_edgePruneGraph G a b hab hnew hmid hnot
  let E : graftGraph H (.inl e) ≃g G :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := by intro v w; rw [hrec]; rfl }
  exact exists_graft_inl_of_iso
    ⟨m + 2, G, tree, labels, leaf, branch⟩ H e E f hf hlast.symm

end BGW.StableTrees.Marchal
