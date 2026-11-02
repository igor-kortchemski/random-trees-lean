/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree.FringeWalk
public import BGW.LocallyFinite.BridgeLaw
import BGW.Tree.FirstPassage

/-!
# Exact weighted fringe identities

Summing an observable over all fringe occurrences in trees of size `n` gives the convolution
of its tree weight with the mass of a zero-sum walk of the remaining length. The identity is
unnormalized, holds for arbitrary nonnegative extended weights, and includes `n = 0`.

This adapts `PoissonDeclumping/Lukasiewicz/Excursion.lean`,
`tsum_sum_weight_mul_fringe` (lines 202–215), the weighted form of Corollary
`cor:cyclicshift` in Kortchemski–Vetter (manuscript lines 778–824). The first-tree/suffix
decomposition is proved directly on words; no stopping-time framework or measure on finite
trees is added.
-/

@[expose] public section

namespace BGW.PlaneTree

open scoped ENNReal

/-- Sum an observable over every fringe occurrence, including the root. -/
noncomputable def fringeSum (G : PlaneTree → ℝ≥0∞) (t : PlaneTree) : ℝ≥0∞ :=
  (t.vertices.map (fun u => (t.fringe? u).elim 0 G)).sum

private theorem isForestCode_one_increments (t : PlaneTree) : IsForestCode 1 t.increments := by
  refine ⟨fun _ hx => neg_one_le_increment t hx, ?_, fun i hi => ?_⟩
  · simpa using sum_increments t
  · have hp := sum_take_increments_nonneg t hi
    change (-1 : ℤ) < (t.increments.take i).sum
    omega

private theorem eq_of_increments_prefix {s t : PlaneTree} {x : List ℤ}
    (hs : s.increments <+: x) (ht : t.increments <+: x) : s = t := by
  have hsl : s.size ≤ x.length := by simpa only [length_increments] using hs.length_le
  have htl : t.size ≤ x.length := by simpa only [length_increments] using ht.length_le
  have hsc : x.take s.size = s.increments := by
    simpa only [length_increments] using (List.prefix_iff_eq_take.mp hs).symm
  have htc : x.take t.size = t.increments := by
    simpa only [length_increments] using (List.prefix_iff_eq_take.mp ht).symm
  have hlen : s.size = t.size := length_eq_of_isForestCode_take hsl htl
    (hsc.symm ▸ isForestCode_one_increments s) (htc.symm ▸ isForestCode_one_increments t)
  apply increments_injective
  rw [← hsc, ← htc, hlen]

private noncomputable def firstTree? (x : List ℤ) : Option PlaneTree := by
  classical
  exact if h : ∃ t : PlaneTree, t.increments <+: x then some h.choose else none

private theorem firstTree?_eq_some_iff {x : List ℤ} {t : PlaneTree} :
    firstTree? x = some t ↔ t.increments <+: x := by
  classical
  unfold firstTree?
  split_ifs with h
  · rw [Option.some.injEq]
    constructor
    · rintro rfl
      exact h.choose_spec
    · exact eq_of_increments_prefix h.choose_spec
  · simp only [false_iff]
    intro ht
    exact h ⟨t, ht⟩

private theorem firstTree?_increments_append (t : PlaneTree) (y : List ℤ) :
    firstTree? (t.increments ++ y) = some t :=
  firstTree?_eq_some_iff.mpr (List.prefix_append _ _)

private theorem firstTree?_rotate_of_fringe {t s : PlaneTree} {u : List ℕ} {i : ℕ}
    (hi : t.vertices[i]? = some u) (hs : t.fringe? u = some s) :
    firstTree? (t.increments.rotate i) = some s := by
  apply firstTree?_eq_some_iff.mpr
  apply List.prefix_iff_eq_take.mpr
  rw [length_increments]
  exact (take_rotate_increments_fringe hi hs).symm

private theorem fringeSum_eq_sum_firstTree (G : PlaneTree → ℝ≥0∞) (t : PlaneTree) :
    fringeSum G t = ∑ i : Fin t.size, (firstTree? (t.increments.rotate i)).elim 0 G := by
  have hsum : fringeSum G t = ∑ i : Fin t.vertices.length,
      (t.fringe? t.vertices[i]).elim 0 G := by
    rw [fringeSum, ← List.ofFn_getElem_eq_map, List.sum_ofFn]
    rfl
  rw [← length_vertices t, hsum]
  apply Finset.sum_congr rfl
  intro i _
  have hi : t.vertices[i.val]? = some (t.vertices[i.val]'i.isLt) :=
    List.getElem?_eq_getElem i.isLt
  obtain ⟨s, hs⟩ := (mem_vertices_iff t _).mp (List.mem_of_getElem? hi)
  change (t.fringe? (t.vertices[i.val]'i.isLt)).elim 0 G =
    (firstTree? (t.increments.rotate i.val)).elim 0 G
  rw [hs, firstTree?_rotate_of_fringe hi hs]

private abbrev BridgeRemainders (n : ℕ) :=
  Σ t : {t : PlaneTree // t.size ≤ n},
    {y : List ℤ // y ∈ forestBridgeWords 0 (n - t.val.size)}

private def appendBridge (n : ℕ) : BridgeRemainders n → {x : List ℤ // x ∈ bridgeWords n} := by
  rintro ⟨⟨t, ht⟩, ⟨y, hylen, hyge, hysum⟩⟩
  refine ⟨t.increments ++ y, ?_, ?_, ?_⟩
  · rw [List.length_append, length_increments, hylen]
    change t.size + (n - t.size) = n
    omega
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact neg_one_le_increment t ha
    · exact hyge a ha
  · rw [List.sum_append, sum_increments, hysum]
    simp

private theorem appendBridge_bijective (n : ℕ) : Function.Bijective (appendBridge n) := by
  constructor
  · rintro ⟨⟨s, hs⟩, ⟨y, hy⟩⟩ ⟨⟨t, ht⟩, ⟨z, hz⟩⟩ h
    have hw := congrArg Subtype.val h
    change s.increments ++ y = t.increments ++ z at hw
    have hst : s = t := eq_of_increments_prefix (List.prefix_append s.increments y)
      (by rw [hw]; exact List.prefix_append _ _)
    subst t
    have hyz : y = z := List.append_cancel_left hw
    subst z
    rfl
  · rintro ⟨x, hlen, hge, hsum⟩
    obtain ⟨m, hmn, hend, hbefore⟩ := exists_first_sum_take_eq hge (v := -1) (b := n)
      (by omega) (by rw [List.take_of_length_le (by omega), hsum])
    have hexc : IsTreeExcursion (x.take m) := by
      refine ⟨fun a ha => hge a (List.mem_of_mem_take ha), hend, fun j hj => ?_⟩
      have hjm : j < m := by rw [List.length_take] at hj; omega
      rw [List.take_take, Nat.min_eq_left hjm.le]
      have := hbefore j hjm
      omega
    obtain ⟨t, ht⟩ := exists_ofIncrements?_eq_some (x.take m) hexc
    have hcode := increments_ofIncrements? ht
    have hsize : t.size = m := by
      have h := congrArg List.length hcode
      simpa only [length_increments, List.length_take, hlen, Nat.min_eq_left hmn] using h
    have htail : (x.drop m).sum = 0 := by
      have h := List.sum_take_add_sum_drop x m
      rw [hend, hsum] at h
      omega
    refine ⟨⟨⟨t, by omega⟩, ⟨x.drop m, ?_, ?_, ?_⟩⟩, Subtype.ext ?_⟩
    · simp only [List.length_drop, hlen, hsize]
    · intro a ha
      exact hge a (List.mem_of_mem_drop ha)
    · simpa using htail
    · change t.increments ++ x.drop m = x
      rw [hcode, List.take_append_drop]

private noncomputable def appendBridgeEquiv (n : ℕ) :
    BridgeRemainders n ≃ {x : List ℤ // x ∈ bridgeWords n} :=
  Equiv.ofBijective _ (appendBridge_bijective n)

private theorem tsum_bridge_firstTree (p : ℕ → ℝ≥0∞) (n : ℕ) (G : PlaneTree → ℝ≥0∞) :
    ∑' x : List ℤ, Set.indicator (bridgeWords n)
        (fun x => walkWeight p x * (firstTree? x).elim 0 G) x =
      ∑' t : PlaneTree, if t.size ≤ n then weight p t * G t *
        ∑' y : List ℤ, Set.indicator (forestBridgeWords 0 (n - t.size)) (walkWeight p) y else 0 := by
  rw [← tsum_subtype (bridgeWords n)
    (fun x => walkWeight p x * (firstTree? x).elim 0 G),
    ← (appendBridgeEquiv n).tsum_eq, ENNReal.tsum_sigma']
  have hpoint (q : BridgeRemainders n) :
      walkWeight p (appendBridgeEquiv n q).val * (firstTree? (appendBridgeEquiv n q).val).elim 0 G =
        weight p q.1.val * G q.1.val * walkWeight p q.2.val := by
    rcases q with ⟨⟨t, ht⟩, ⟨y, hy⟩⟩
    change walkWeight p (t.increments ++ y) * (firstTree? (t.increments ++ y)).elim 0 G = _
    rw [firstTree?_increments_append, walkWeight_append, walkWeight_increments]
    simp only [Option.elim_some]
    exact mul_right_comm _ _ _
  simp_rw [hpoint, ENNReal.tsum_mul_left]
  have hzero (t : {t : PlaneTree // t.size ≤ n}) :
      ∑' y : {y : List ℤ // y ∈ forestBridgeWords 0 (n - t.val.size)}, walkWeight p y.val =
        ∑' y : List ℤ, Set.indicator (forestBridgeWords 0 (n - t.val.size)) (walkWeight p) y :=
    tsum_subtype _ _
  simp_rw [hzero]
  refine (tsum_subtype {t : PlaneTree | t.size ≤ n}
    (fun t => weight p t * G t *
      ∑' y : List ℤ, Set.indicator (forestBridgeWords 0 (n - t.size)) (walkWeight p) y)).trans ?_
  apply tsum_congr
  intro t
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]

/-- Exact weighted fringe convolution. The remainder is a bridge to level zero, and trees
larger than `n` contribute zero. No normalization, criticality or moment hypothesis is used. -/
theorem tsum_weight_fringeSum (p : ℕ → ℝ≥0∞) (G : PlaneTree → ℝ≥0∞) (n : ℕ) :
    ∑' t : {t : PlaneTree // t.size = n}, weight p t.val * fringeSum G t.val =
      ∑' s : PlaneTree, if s.size ≤ n then weight p s * G s *
        ∑' x : List ℤ, Set.indicator (forestBridgeWords 0 (n - s.size)) (walkWeight p) x else 0 := by
  calc
    _ = ∑' q : {t : PlaneTree // t.size = n} × Fin n,
        weight p q.1.val * (firstTree? (q.1.val.increments.rotate q.2)).elim 0 G := by
      rw [ENNReal.tsum_prod']
      apply tsum_congr
      rintro ⟨t, ht⟩
      subst n
      rw [fringeSum_eq_sum_firstTree, tsum_fintype, Finset.mul_sum]
    _ = ∑' x : List ℤ, Set.indicator (bridgeWords n)
        (fun x => walkWeight p x * (firstTree? x).elim 0 G) x :=
      tsum_shift_weight_mul p n (fun x => (firstTree? x).elim 0 G)
    _ = _ := tsum_bridge_firstTree p n G

end BGW.PlaneTree
