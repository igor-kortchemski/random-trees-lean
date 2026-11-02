/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.ContinuumTrees.ContourEmbedding
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.List.Chain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Density of vertices in the contour-coded finite tree

Every grid visit represents the same coded point as the first visit to its
address, including return visits. Every interpolated contour point is within
distance one of an embedded vertex: in its interpolation cell, choose the
endpoint of lower height. The two endpoint heights differ by one, and the
contour stays above the lower endpoint throughout that cell.

The zero-duration contour is constant zero, so the singleton case is included.
No scaling, measure comparison, or convergence assertion is made here.
-/

@[expose] public section

open BGW.PlaneTree

namespace BGW.ContinuumTrees.FiniteTree

/-- Every contour visit represents the embedded vertex at its address, even on a return. -/
theorem projection_contourTime_eq_vertexEmbedding (t : PlaneTree)
    (k : Fin t.contour.length) (u : Vertex t)
    (hk : t.vertexContour[k.val]? = some u.val) :
    Coding.projection t.contourFunction (t.contourTime k) = vertexEmbedding t u := by
  have hdfs := List.getElem?_idxOf ((mem_vertices_iff t u.val).mpr u.property)
  let b : Fin t.contour.length := ⟨2 * t.vertices.idxOf u.val - u.val.length,
    (List.getElem?_eq_some_iff.mp (getElem?_contour_first_visit hdfs)).1⟩
  have hb : t.vertexContour[b.val]? = some u.val := by
    obtain ⟨hb, hval, _⟩ := List.idxOf?_eq_some_iff.mp
      (idxOf?_vertexContour_of_getElem?_vertices hdfs)
    exact List.getElem?_eq_some_iff.mpr ⟨hb, hval⟩
  change Coding.projection t.contourFunction (t.contourTime k) =
    Coding.projection t.contourFunction (t.contourTime b)
  apply (Coding.projection_eq_iff _ _ _).mpr
  rw [ContourCoding.codingDist_contourTime_of_vertices k b hk hb, graphDist_self,
    Nat.cast_zero]

private theorem exists_vertex_at_contourTime (t : PlaneTree) (k : Fin t.contour.length) :
    ∃ u : Vertex t, Coding.projection t.contourFunction (t.contourTime k) =
      vertexEmbedding t u := by
  have hlen : t.vertexContour.length = t.contour.length := by
    have h := congrArg List.length (map_length_vertexContour t)
    simpa only [List.length_map] using h
  have hk : k.val < t.vertexContour.length := by rw [hlen]; exact k.isLt
  let u : Vertex t := ⟨t.vertexContour[k.val]'hk,
    (mem_vertexContour_iff t _).mp (List.getElem_mem hk)⟩
  refine ⟨u, projection_contourTime_eq_vertexEmbedding t k u ?_⟩
  exact List.getElem?_eq_getElem hk

private theorem contour_cell_bounds (t : PlaneTree) (k : ℕ)
    (hk : k + 1 < t.contour.length) (s : unitInterval)
    (hlo : (k : ℝ) ≤ ((t.contour.length - 1 : ℕ) : ℝ) * (s : ℝ))
    (hhi : ((t.contour.length - 1 : ℕ) : ℝ) * (s : ℝ) ≤ (k : ℝ) + 1) :
    min (t.contour[k]'(by omega) : ℝ) (t.contour[k + 1]'hk : ℝ) ≤ t.contourFunction s ∧
      t.contourFunction s ≤ max (t.contour[k]'(by omega) : ℝ) (t.contour[k + 1]'hk : ℝ) := by
  let θ : ℝ := ((t.contour.length - 1 : ℕ) : ℝ) * (s : ℝ) - k
  have hθ0 : 0 ≤ θ := sub_nonneg.mpr hlo
  have hθ1 : 0 ≤ 1 - θ := by dsimp [θ]; linarith
  let A : ℝ := t.contour[k]'(by omega)
  let B : ℝ := t.contour[k + 1]'hk
  have hlinear : t.contourFunction s = (1 - θ) * A + θ * B :=
    contourFunction_on_segment t k s hk hlo hhi
  change min A B ≤ t.contourFunction s ∧ t.contourFunction s ≤ max A B
  rw [hlinear]
  constructor
  · calc
      min A B = (1 - θ) * min A B + θ * min A B := by ring
      _ ≤ (1 - θ) * A + θ * B :=
        add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _) hθ1)
          (mul_le_mul_of_nonneg_left (min_le_right _ _) hθ0)
  · calc
      (1 - θ) * A + θ * B ≤ (1 - θ) * max A B + θ * max A B :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hθ1)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hθ0)
      _ = max A B := by ring

private theorem exists_vertex_near_projection (t : PlaneTree) (s : unitInterval) :
    ∃ u : Vertex t, dist (Coding.projection t.contourFunction s) (vertexEmbedding t u) ≤ 1 := by
  by_cases hN : t.contour.length - 1 = 0
  · have hsame : t.contourFunction s = t.contourFunction 0 := by
      change (∑ i : Fin t.contour.length, _) = ∑ i : Fin t.contour.length, _
      simp only [hN, Nat.cast_zero, zero_mul]
    have hs0 : t.contourFunction s = 0 := hsame.trans (contourFunction_zero t)
    refine ⟨root t, ?_⟩
    rw [vertexEmbedding_root, dist_comm, Coding.dist_root_projection _
      (contourFunction_nonneg t) (contourFunction_zero t), hs0]
    exact zero_le_one
  · by_cases hs1 : s = 1
    · subst s
      have heq : Coding.projection t.contourFunction 1 = Coding.root t.contourFunction :=
        (Coding.projection_zero_eq_one _ (contourFunction_nonneg t)
          (contourFunction_zero t) (contourFunction_one t)).symm
      refine ⟨root t, ?_⟩
      rw [vertexEmbedding_root, heq, dist_self]
      exact zero_le_one
    · have hNR : (0 : ℝ) < ((t.contour.length - 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 0 < t.contour.length - 1 by omega)
      have hslt : (s : ℝ) < 1 := by
        apply lt_of_le_of_ne s.property.2
        intro h
        apply hs1
        exact Subtype.ext h
      let x : ℝ := ((t.contour.length - 1 : ℕ) : ℝ) * (s : ℝ)
      have hx0 : 0 ≤ x := mul_nonneg hNR.le s.property.1
      have hxN : x < ((t.contour.length - 1 : ℕ) : ℝ) := by
        have h := mul_lt_mul_of_pos_left hslt hNR
        simpa only [mul_one] using h
      let k : ℕ := Nat.floor x
      have hkN : k < t.contour.length - 1 := (Nat.floor_lt hx0).mpr hxN
      have hk : k + 1 < t.contour.length := by omega
      have hxlo : (k : ℝ) ≤ x := Nat.floor_le hx0
      have hxhi : x ≤ (k : ℝ) + 1 := (Nat.lt_floor_add_one x).le
      let a : Fin t.contour.length := ⟨k, by omega⟩
      let b : Fin t.contour.length := ⟨k + 1, hk⟩
      have has : t.contourTime a ≤ s := by
        change (t.contourTime a : ℝ) ≤ (s : ℝ)
        apply (mul_le_mul_iff_right₀ hNR).mp
        rw [duration_mul_contourTime]
        exact hxlo
      have hsb : s ≤ t.contourTime b := by
        change (s : ℝ) ≤ (t.contourTime b : ℝ)
        apply (mul_le_mul_iff_right₀ hNR).mp
        rw [duration_mul_contourTime]
        simpa only [b, Fin.val_mk, Nat.cast_add, Nat.cast_one] using hxhi
      let A : ℝ := t.contour[k]'(by omega)
      let B : ℝ := t.contour[k + 1]'hk
      let d : ℝ := min A B
      have hbounds (r : unitInterval)
          (hr : r ∈ Set.Icc (t.contourTime a) (t.contourTime b)) :
          d ≤ t.contourFunction r ∧ t.contourFunction r ≤ max A B := by
        apply contour_cell_bounds t k hk r
        · have hr1 : (t.contourTime a : ℝ) ≤ (r : ℝ) := hr.1
          have h := mul_le_mul_of_nonneg_left hr1 hNR.le
          rw [duration_mul_contourTime] at h
          exact h
        · have hr2 : (r : ℝ) ≤ (t.contourTime b : ℝ) := hr.2
          have h := mul_le_mul_of_nonneg_left hr2 hNR.le
          rw [duration_mul_contourTime] at h
          simpa only [b, Fin.val_mk, Nat.cast_add, Nat.cast_one] using h
      have hgap : max A B ≤ d + 1 := by
        rcases (isChain_contour t).getElem k hk with hup | hdown
        · have h : A + 1 = B := by
            dsimp only [A, B]
            exact_mod_cast hup
          change max A B ≤ min A B + 1
          rw [max_eq_right (by linarith), min_eq_left (by linarith)]
          linarith
        · have h : B + 1 = A := by
            dsimp only [A, B]
            exact_mod_cast hdown
          change max A B ≤ min A B + 1
          rw [max_eq_left (by linarith), min_eq_right (by linarith)]
          linarith
      obtain ⟨q, hqcell, hqheight⟩ : ∃ q : Fin t.contour.length,
          t.contourTime q ∈ Set.Icc (t.contourTime a) (t.contourTime b) ∧
            t.contourFunction (t.contourTime q) = d := by
        rcases le_total A B with hAB | hBA
        · refine ⟨a, ⟨le_rfl, has.trans hsb⟩, ?_⟩
          rw [contourFunction_contourTime]
          exact (min_eq_left hAB).symm
        · refine ⟨b, ⟨has.trans hsb, le_rfl⟩, ?_⟩
          rw [contourFunction_contourTime]
          exact (min_eq_right hBA).symm
      have hmin : Coding.intervalMin t.contourFunction s (t.contourTime q) = d := by
        apply le_antisymm
        · exact (Coding.intervalMin_le_right _ _ _).trans_eq hqheight
        · apply Coding.le_intervalMin
          intro r hr
          exact (hbounds r (Set.uIcc_subset_Icc ⟨has, hsb⟩ hqcell hr)).1
      have hdist : dist (Coding.projection t.contourFunction s)
          (Coding.projection t.contourFunction (t.contourTime q)) ≤ 1 := by
        rw [Coding.dist_projection, Coding.codingDist, hmin, hqheight]
        have hupper := (hbounds s ⟨has, hsb⟩).2.trans hgap
        linarith
      obtain ⟨u, hu⟩ := exists_vertex_at_contourTime t q
      exact ⟨u, by rw [← hu]; exact hdist⟩

/-- Every point of the contour-coded tree is within one edge length of an embedded vertex. -/
theorem exists_vertex_dist_le_one (t : PlaneTree) (x : Coding.Space t.contourFunction) :
    ∃ u : Vertex t, dist x (vertexEmbedding t u) ≤ 1 := by
  obtain ⟨s, rfl⟩ := Coding.projection_surjective t.contourFunction x
  exact exists_vertex_near_projection t s

end BGW.ContinuumTrees.FiniteTree
