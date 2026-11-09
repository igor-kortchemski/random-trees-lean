import BGW.Tree.Height
import BGW.Tree.ContourVertices
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Basic.Real.Basic

/-! Contract probe for CT8 node K12a (`r5-ct8-blueprint/blueprint.md` K12, and the correction of
finding 7 of `r5-ct8-blueprint/AUDIT.md`): the deterministic FINITE-TREE local bracketing of
the contour by the DFS heights, stated independently of any probabilistic forest theorem (K16
applies it under exact-size conditioning; K12b applies it to the forest).

CONVENTIONS (blueprint §1).  For a finite plane tree of size `z` with DFS vertices
`v_0, ..., v_{z-1}`: `heightSeq t i = |v_i|` for `i < z` and `0` for `i ≥ z` (the value
`H_z = 0`); `contourAt t m` is the contour at integer time `m` (original speed, `0` after
`2(z-1)`); `heightLin` and `contourLin` interpolate linearly at integer times (the contour runs
at time scale `2nt`, heights at `nt`).  The first visit of `v_i` is at `b_i = 2i - H_i`
(sealed `getElem?_contour_first_visit`); with `H_z = 0` the formula gives `b_z = 2z`, the end of
the tree padded by two zero units.

TRUTH CHECK.  `H_i ≤ i` (an ancestor precedes its descendants), `H_{i+1} ≤ H_i + 1` (the next
DFS vertex is a child of `v_i` or of an ancestor of `v_i`; at `i + 1 = z` the value is `0`).
Hence `b_{i+1} - b_i = 2 - (H_{i+1} - H_i) ≥ 1`, the brackets `[b_i, b_{i+1}]`, `i < z`, have
integer endpoints, length `≥ 1`, and cover `[0, 2z]`.  On a bracket: if `v_{i+1}` is a child of
`v_i`, then `b_{i+1} = b_i + 1` and the contour moves from `H_i` to `H_i + 1`; otherwise `v_i` is
a leaf, the contour descends from `H_i` to the common ancestor at height `H_{i+1} - 1` and
climbs to `H_{i+1}`, staying in `[H_{i+1} - 1, H_i]`; for `i = z - 1` it descends to `0` and
stays there.  In all cases `|C_m - H_i| ≤ |H_{i+1} - H_i| + 1`.  For real `s ∈ [0, 2z]` the unit
interval `[⌊s⌋, ⌊s⌋ + 1]` lies in one bracket `i`, the interpolation is a convex combination,
and `b_i ≤ s ≤ b_{i+1}` gives `s/2 - 1 ≤ i ≤ s/2 + H_i/2`.

PROOF PLAN.  Induction on the tree through `contour_node` and the DFS vertex list, or directly
from `idxOf?_vertexContour_of_getElem?_vertices` and the parent/child structure of consecutive
DFS vertices.  Size 300-600 lines.

ACYCLICITY.  Suppliers: the sealed `BGW.Tree` library only.

BINDER SCOPE (AUDITOR_RULES): no integral or big operator appears in the statements. -/

namespace BGW.PlaneTree

/-- DFS heights extended by `0`: `|v_i|` for `i < size`, and `0` for `i ≥ size`. -/
def heightSeq (t : PlaneTree) (i : ℕ) : ℕ := ((t.vertices[i]?).map List.length).getD 0

/-- The contour at integer time `m` (original speed), `0` after the end of the contour. -/
def contourAt (t : PlaneTree) (m : ℕ) : ℕ := t.contour.getD m 0

/-- Linear interpolation of the heights at integer times (used for `u ≥ 0`). -/
noncomputable def heightLin (t : PlaneTree) (u : ℝ) : ℝ :=
  (1 - (u - ⌊u⌋₊)) * (t.heightSeq ⌊u⌋₊ : ℝ) + (u - ⌊u⌋₊) * (t.heightSeq (⌊u⌋₊ + 1) : ℝ)

/-- Linear interpolation of the contour at integer times (used for `s ≥ 0`). -/
noncomputable def contourLin (t : PlaneTree) (s : ℝ) : ℝ :=
  (1 - (s - ⌊s⌋₊)) * (t.contourAt ⌊s⌋₊ : ℝ) + (s - ⌊s⌋₊) * (t.contourAt (⌊s⌋₊ + 1) : ℝ)

/-! ### Heights -/

theorem heightSeq_of_lt (t : PlaneTree) {i : ℕ} (hi : i < t.size) :
    t.heightSeq i = t.height ⟨i, hi⟩ := sorry

theorem heightSeq_of_le (t : PlaneTree) {i : ℕ} (hi : t.size ≤ i) : t.heightSeq i = 0 := sorry

/-- A vertex is deeper than its DFS index at most. -/
theorem heightSeq_le (t : PlaneTree) (i : ℕ) : t.heightSeq i ≤ i := sorry

/-- Heights increase by at most one along the DFS order. -/
theorem heightSeq_succ_le (t : PlaneTree) (i : ℕ) : t.heightSeq (i + 1) ≤ t.heightSeq i + 1 :=
  sorry

theorem heightLin_natCast (t : PlaneTree) (i : ℕ) : t.heightLin i = t.heightSeq i := sorry

theorem contourLin_natCast (t : PlaneTree) (m : ℕ) : t.contourLin m = t.contourAt m := sorry

/-! ### Contour values -/

theorem contourAt_of_lt (t : PlaneTree) {m : ℕ} (hm : 2 * (t.size - 1) < m) :
    t.contourAt m = 0 := sorry

/-- First visit of the DFS vertex `i` at time `2i - H_i`. -/
theorem contourAt_firstVisit (t : PlaneTree) {i : ℕ} (hi : i < t.size) :
    t.contourAt (2 * i - t.heightSeq i) = t.heightSeq i := sorry

/-- Every contour value is at most the depth of some vertex (a depth, before the end). -/
theorem exists_contourAt_le_heightSeq (t : PlaneTree) (m : ℕ) :
    ∃ i < t.size, t.contourAt m ≤ t.heightSeq i := sorry

/-- Before the end, every contour value is the depth of some vertex. -/
theorem exists_contourAt_eq_heightSeq (t : PlaneTree) {m : ℕ} (hm : m < 2 * t.size - 1) :
    ∃ i < t.size, t.contourAt m = t.heightSeq i := sorry

/-! ### Local bracketing -/

/-- **Integer bracketing**: between the first visits of `v_i` and `v_{i+1}` (with `b_z = 2z`),
the contour stays within `|H_{i+1} - H_i| + 1` of `H_i`. -/
theorem contourAt_bracket (t : PlaneTree) {i m : ℕ} (hi : i < t.size)
    (hm1 : 2 * i - t.heightSeq i ≤ m) (hm2 : m ≤ 2 * (i + 1) - t.heightSeq (i + 1)) :
    |(t.contourAt m : ℤ) - t.heightSeq i| ≤ |(t.heightSeq (i + 1) : ℤ) - t.heightSeq i| + 1 :=
  sorry

/-- **Real-time bracketing**: every contour time `s ∈ [0, 2z]` lies in a bracket `i` with
`s/2 - 1 ≤ i ≤ s/2 + H_i/2`, and the interpolated contour at `s` is within
`|H_{i+1} - H_i| + 1` of `H_i`. -/
theorem contourLin_bracket (t : PlaneTree) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 2 * t.size) :
    ∃ i < t.size, s / 2 - 1 ≤ i ∧ (i : ℝ) ≤ s / 2 + (t.heightSeq i : ℝ) / 2 ∧
      |t.contourLin s - t.heightSeq i| ≤ |(t.heightSeq (i + 1) : ℝ) - t.heightSeq i| + 1 :=
  sorry

/-- **Prefix-local comparison** of the contour at time `2u` with the interpolated height at
`u`: if `ω ≥ 1` bounds half the heights of the vertices of index `≤ 2u`, and `δ` bounds the
oscillation of `heightLin` over windows of width `ω` inside `[0, z]`, then the two differ by at
most `2δ + 1`.  Only indices `≤ 2u` are used (K16 applies it on a larger prefix `a' < 1`). -/
theorem contourLin_two_mul_sub_heightLin_le (t : PlaneTree) {u ω δ : ℝ} (hu0 : 0 ≤ u)
    (hu : u ≤ t.size) (hω1 : 1 ≤ ω)
    (hω2 : ∀ j : ℕ, j < t.size → (j : ℝ) ≤ 2 * u → (t.heightSeq j : ℝ) / 2 ≤ ω)
    (hδ : ∀ x y : ℝ, 0 ≤ x → x ≤ t.size → 0 ≤ y → y ≤ t.size → |x - y| ≤ ω →
      |t.heightLin x - t.heightLin y| ≤ δ) :
    |t.contourLin (2 * u) - t.heightLin u| ≤ 2 * δ + 1 := sorry

end BGW.PlaneTree
