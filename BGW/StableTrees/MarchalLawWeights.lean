/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.MarchalChain
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Local factors in the exact Marchal law

Writing the numerator as a product over all vertices makes its change under
each of the two graft operations explicit.
-/

@[expose] public section

open scoped ENNReal Classical

namespace BGW.StableTrees.Marchal

/-- Contribution of a degree to the numerator, with contribution one for leaves. -/
noncomputable def degreeLawFactor (α : ℝ) (d : ℕ) : ℝ :=
  if 3 ≤ d then (α - 1) * ∏ j ∈ Finset.Icc 2 (d - 2), ((j : ℝ) - α) else 1

@[simp] theorem degreeLawFactor_one (α : ℝ) : degreeLawFactor α 1 = 1 := by
  simp [degreeLawFactor]

@[simp] theorem degreeLawFactor_three (α : ℝ) : degreeLawFactor α 3 = α - 1 := by
  simp [degreeLawFactor]

/-- Increasing an internal degree contributes the next Marchal vertex weight. -/
theorem degreeLawFactor_succ (α : ℝ) {d : ℕ} (hd : 3 ≤ d) :
    degreeLawFactor α (d + 1) = degreeLawFactor α d * ((d : ℝ) - 1 - α) := by
  have hd' : 3 ≤ d + 1 := by omega
  have he : d + 1 - 2 = (d - 2) + 1 := by omega
  have heR : ((d - 2 + 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_add, Nat.cast_sub (by omega : 2 ≤ d)]
    norm_num
    ring
  simp only [degreeLawFactor, ite_eq_left hd, ite_eq_left hd', he]
  rw [Finset.prod_Icc_succ_top (by omega : 2 ≤ (d - 2) + 1), heR]
  ring

/-- The law numerator is a product of local degree factors over all vertices. -/
theorem LTree.lawWeight_eq_prod {n : ℕ} (T : LTree n) (α : ℝ) :
    T.lawWeight α = ∏ v : Fin T.m, degreeLawFactor α (T.G.degree v) := by
  conv_rhs =>
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun v : Fin T.m => 3 ≤ T.G.degree v)]
  have hn : (∏ v : {v : Fin T.m // ¬3 ≤ T.G.degree v},
      degreeLawFactor α (T.G.degree v.val)) = 1 := by
    apply Finset.prod_eq_one
    intro v _
    simp [degreeLawFactor, v.property]
  rw [hn, mul_one]
  calc
    _ = ∏ v : {v : Fin T.m // 3 ≤ T.G.degree v},
        (α - 1) * ∏ j ∈ Finset.Icc 2 (T.G.degree v.val - 2), ((j : ℝ) - α) := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        LTree.lawWeight, LTree.internalCount]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro v _
      exact (ite_eq_left v.property).symm

/-- Grafting on an edge multiplies the exact-law numerator by its selection weight. -/
theorem LTree.lawWeight_graft_inl {n : ℕ} (T : LTree n) (α : ℝ) (e : T.G.edgeSet) :
    (graft T (.inl e)).lawWeight α = T.lawWeight α * (α - 1) := by
  rw [LTree.lawWeight_eq_prod, LTree.lawWeight_eq_prod]
  change (∏ v : Fin (T.m + 2), degreeLawFactor α ((graftGraph T.G (.inl e)).degree v)) = _
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  have hnew : (graftGraph T.G (.inl e)).degree (Fin.last (T.m + 1)) = 1 :=
    graftGraph_inl_degree_new T.G e
  have hmid : (graftGraph T.G (.inl e)).degree (Fin.last T.m).castSucc = 3 :=
    graftGraph_inl_degree_mid T.G e
  simp only [hnew, hmid, degreeLawFactor_one, degreeLawFactor_three, mul_one]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  rw [show (graftGraph T.G (.inl e)).degree v.castSucc.castSucc = T.G.degree v from
    graftGraph_inl_degree_old T.G e v]

/-- Grafting on an internal vertex multiplies the numerator by its selection weight. -/
theorem LTree.lawWeight_graft_inr {n : ℕ} (T : LTree n) (α : ℝ)
    (v : {v : Fin T.m // 3 ≤ T.G.degree v}) :
    (graft T (.inr v)).lawWeight α =
      T.lawWeight α * ((T.G.degree v.val : ℝ) - 1 - α) := by
  rw [LTree.lawWeight_eq_prod, LTree.lawWeight_eq_prod]
  change (∏ x : Fin (T.m + 1), degreeLawFactor α ((graftGraph T.G (.inr v)).degree x)) = _
  rw [Fin.prod_univ_castSucc]
  have hnew : (graftGraph T.G (.inr v)).degree (Fin.last T.m) = 1 :=
    graftGraph_inr_degree_new T.G v
  rw [hnew, degreeLawFactor_one, mul_one]
  classical
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v.val),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ v.val)]
  have hself : (graftGraph T.G (.inr v)).degree v.val.castSucc = T.G.degree v.val + 1 :=
    graftGraph_inr_degree_old_self T.G v
  rw [hself, degreeLawFactor_succ α v.property]
  have hrest : (∏ x ∈ Finset.univ.erase v.val,
      degreeLawFactor α ((graftGraph T.G (.inr v)).degree x.castSucc)) =
      ∏ x ∈ Finset.univ.erase v.val, degreeLawFactor α (T.G.degree x) := by
    apply Finset.prod_congr rfl
    intro x hx
    rw [show (graftGraph T.G (.inr v)).degree x.castSucc = T.G.degree x from
      graftGraph_inr_degree_old_of_ne T.G v x (Finset.mem_erase.mp hx).1]
  rw [hrest]
  ring

/-- Every graft contributes exactly the selected Marchal weight to the numerator. -/
theorem LTree.lawWeight_graft {n : ℕ} (T : LTree n) (α : ℝ) (p : Position T.G) :
    (graft T p).lawWeight α = T.lawWeight α * selectionWeight T.G α p := by
  cases p with
  | inl e => exact T.lawWeight_graft_inl α e
  | inr v => exact T.lawWeight_graft_inr α v

end BGW.StableTrees.Marchal
