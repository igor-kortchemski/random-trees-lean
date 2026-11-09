import BGW.StableTrees.PathTail
import BGW.StableTrees.DiscreteForest
import BGW.StableTrees.UnitExcursionLaw
import BGW.StableTrees.StableLocalLaw
import BGW.Tree.ContourBracket
import BGW.Tree.Weight
import BGW.ContinuumTrees.ContourAdapters
import BGW.Skorokhod.Restrict
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import BGW.StableTrees.HeightProcess
import BGW.StableTrees.HeightBridges
import BGW.StableTrees.HeightContinuity
import BGW.StableTrees.ExcursionHeight
import BGW.StableTrees.JointExcursion
import BGW.StableTrees.TailPair
import BGW.StableTrees.ExactPair

/-! Contract probe for CT8 node K16 (`r5-ct8-blueprint/blueprint.md` §1, K16; `AUDIT.md`
finding 7; `CLASSICAL_THEORY_INPUTS.md` C29): the joint height/contour theorem for BGW trees
conditioned on their exact size, along every unbounded sequence of admissible sizes: the
rescaled height and contour converge jointly to the SAME excursion height.

DEFINITIONS (concrete, no `sorry`).
* `PlaneTree.mirror = fold (fun ts => node ts.reverse)`: reverse the children of every vertex
  (`mirror (node ts) = node (ts.map mirror).reverse`).
* `treeMirror τ`: `mirror` of the decoded finite tree, re-encoded by `toLocallyFinite`; the
  identity on infinite trees.
* `treeContourLin τ s`: K12a's `PlaneTree.contourLin` (contour at original speed, linearly
  interpolated, `0` after time `2(z-1)`) of the decoded finite tree; `0` on infinite trees.
* `treeContourPath B n T τ`: `t ↦ (B n / n) * treeContourLin τ (2 n t)` in `C([0,T], ℝ)`; dite
  junk `0` on a discontinuity that never occurs (`continuous_treeContourLin`).
* `heightContourPath B n τ = (treeHeightPath B n 1 τ, treeContourPath B n 1 τ)` (K14 height at
  time scale `nt`, contour at `2nt`), and `exactHeightContourLaw μ B n hn` its law under the
  sealed K02 `exactTreeLaw μ n` (ONE tree; `hn` unused by the body, as in the sealed
  `exactWalkLaw`; exports quantify `hq : ∀ k, Admissible μ (q k)`).
* `contourHeightError B n a τ = sup_{t ∈ [0,a]} |(B n/n) C(2nt) - (B n/n) H_lin(nt)|`.
* Library convention: `heightLibContourPath B n τ` pairs the height with
  `(B n / n) • PlaneTree.contourFunction` (sealed, `s ↦ C(2(z-1)s)`), and
  `exactHeightLibContourLaw` is its law.
* Copied from contracts (not part of this contract): H04 `IsExcursionHeightVersion`,
  `excursionHeight`; J01 `heightRestrict`, `excursionPair`, `restrictPair`, `excLaw`,
  `excLaw_height_endpoints_pos`; K14 `treeHeightLin`, `treeHeightPath`, `treePairPath`;
  K15 `exactPairLaw`, `tendsto_exactPairLaw_prefix`.

CONTOUR CLOCK RECONCILIATION (blueprint §1 and K16; `AUDIT.md` finding 7).  The main convention is
the blueprint's `2nt` (the scale of K13's forest contour), which for a tree of size `n` is EXACTLY
the paper convention `s ↦ C_{2ζ s}` of the sealed adapters:
`treeContourPath_eq_paperContourFunction` (`= (B n / n) * PlaneTree.paperContourFunction`).  The
library convention `2(n-1)t` (`PlaneTree.contourFunction`) is uniformly within `2 |B n / n|`:
`abs_treeContourPath_sub_contourFunction_le` (adjacent contour values differ by at most `1`, and
the clocks `min(2ns, 2(n-1))` and `2(n-1)s` differ by at most `2s ≤ 2` contour units).  Since
`B n / n → 0`, the theorem holds verbatim in both conventions:
`tendsto_exactHeightContourLaw` and `tendsto_exactHeightLibContourLaw`.

TRUTH CHECK.
(1) Mirror.  `mirror` preserves size and the multiset of outdegrees, hence the offspring-product
weight (`size_mirror`, `weight_mirror`), and is an involution (`mirror_mirror`); so it preserves
`bienaymeLaw` on finite trees and every exact-size conditioned law, including the Dirac leaf of
the junk branch (`mirror leaf = leaf`, sealed `toLocallyFinite_leaf`): `map_treeMirror_exactTreeLaw`
for EVERY `n`.  Contour: the mirrored contour walk is the reversed contour word, so
`C_mirror(m) = C(2(z-1) - m)` for `m ≤ 2(z-1)` (`contourAt_mirror`, from the sealed
`contour_node`: `0 :: ⋯ ++ [0]` reverses blockwise), and the same for the interpolation
(`contourLin_mirror`, `2(z-1)` is an integer).  No time reversal of the HEIGHT sequence is
claimed: the mirrored DFS order is not the reversed DFS order.
(2) Endpoints.  For a tree of size `n`: `H_lin(n) = heightSeq n = 0`, `C(2nt) = 0` for
`t ≥ (n-1)/n`, both start at `0`; the limit `(H^exc, H^exc)` vanishes at `0` and `1` (J01
`excLaw_height_endpoints_pos`).
(3) Target `(excLaw θ).map (fun p => (p.2, p.2))`: the H04 height of ONE unit excursion in both
coordinates.  At `θ = 2` (variance-2 library process) it is `(√2 e, √2 e)` for the standard
Brownian excursion `e` (J01 `excLaw_height_eq_path_two` with K18b `levyExcLaw_two`; the pair
form is the K18 blueprint's `excLaw_two`), consistent with the classical
`(σ/(2√n)) C_{2nt} → e` since `B_n/n = σ/√(2n) = √2 · σ/(2√n)` for `B_n = σ√(n/2)`; no `2/σ²`
is inserted.  Constants exactly `1`.
(4) Scope.  Every unbounded admissible `q` (periodic laws included: the span `d` is handled in
the sealed K03/K07 weights consumed by K15); height and contour only, no walk coordinate (a full
joint triple would be a separate export).
(5) No junk: `treeContourPath`, `heightContourPath` are measurable (countable finite carrier);
the continuity dites never take their junk branch; `exactTreeLaw μ (q k)` is never the Dirac
branch under `hq`.

PROOF PLAN (blueprint K16; AUDIT finding 7, larger-prefix buffer).  (a) Mirror algebra by
`PlaneTree.induction_on` (`fold_node`, `contour_node`, `degrees`).  (b) Prefix error
`tendsto_contourHeightError_prefix`: sealed K12a `contourLin_bracket` (a bracket index `i` with
`i ≤ s/2 + H_i/2`); for `s = 2nt ≤ 2na` and `a < a' < 1`, an index `i > na'` would force
`H_⌊na'⌋ ≥ 2n(a' - a) - O(1)` (`heightSeq_succ_le`: heights rise by at most `1` per index),
excluded w.h.p. by K15 at `a'`; on `[0,a']` the K15 height prefix is tight and its modulus is
controlled (continuous limit), giving the local estimate (as in K12a
`contourLin_two_mul_sub_heightLin_le`, restricted to the prefix).  The unconditioned forest
estimate of K12b is NOT used: it does not transfer through exact-size conditioning.
(c) Terminal window `tendsto_exactContour_terminalWindow`: by `contourLin_mirror` the terminal
window of `C` is the initial window of `C_mirror` (time shift `1/n`), whose law is the same
(`map_treeMirror_exactTreeLaw`); the initial window is controlled by (b) and K15 with
`H^exc(0) = 0` and continuity.  (d) Contour tightness on `[0,1]` from (b) on `[0,a]`, (c) on
`[a,1]`, and identification of all prefixes `[0,a]`, `a < 1` (K15 + (b)); continuity at `1` of
the limit identifies the contour limit with `H^exc`.  (e) Global error `tendsto_contourHeightError`:
`H_i = C(2i - H_i)` (first visits, K12a `contourAt_firstVisit`) and `sup H ≤ sup C`, so the
first-visit clock error `H_i/(2n)` vanishes uniformly, and contour equicontinuity gives
`sup |H(nt) - C(2nt)| (B_n/n) → 0`, including the final interpolation to `H_n = 0`.  (f) Joint
limit from (d), (e) (Slutsky, sealed `tendsto_map_prodMk_of_tendsto_of_error` and the map
`(c, d) ↦ (c + d, c)`).  (g) Library convention from the deterministic bound and `B n / n → 0`.
Size 900-1600 lines.  RISK: reversed height is not the mirrored height; using global exact-size
height tightness to prove the contour bound that is supposed to establish it.

ACYCLICITY.  Sealed suppliers: K02 (`exactTreeLaw`), K12a (`ContourBracket`), CT9
`ContourAdapters` (`paperContourFunction`), `Tree.Contour*`, `Tree.Weight`.  Contract
suppliers (copied statements): K15, K14 (definitions), J01, H04.  No K12b/K13 (unconditioned
forest), no K17-K19 (K19 consumes this node), no C35.

BINDER SCOPE (AUDITOR_RULES).  The supremum in `contourHeightError` has the absolute value
`|a - b|` as body and nothing follows it.  The window events use `∃ t, ... ∧ ε < ...`, no big
operator.  In `contourLin_mirror` and `treeContourLin_treeMirror` the reflected time is
`2 * ((t.size : ℝ) - 1) - s`, with `t.size - 1` computed in `ℝ` (size `≥ 1`). -/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees

end BGW.StableTrees

namespace BGW.StableTrees.TailPair

open BGW.StableTrees.DiscreteForest BGW.StableTrees.PathTail

end BGW.StableTrees.TailPair

namespace BGW.StableTrees.ExactPair

open BGW.StableTrees.DiscreteForest BGW.StableTrees.TailPair

end BGW.StableTrees.ExactPair

namespace BGW.PlaneTree

/-! ### Mirror image of a plane tree -/

/-- **Mirror image** of a plane tree: the children of every vertex in reverse order
(`mirror (node ts) = node (ts.map mirror).reverse`). -/
def mirror : PlaneTree → PlaneTree := fold fun ts => node ts.reverse

theorem mirror_node (ts : List PlaneTree) : (node ts).mirror = node (ts.map mirror).reverse :=
  sorry

/-- The mirror is an involution. -/
theorem mirror_mirror (t : PlaneTree) : t.mirror.mirror = t := sorry

/-- The mirror preserves the size. -/
theorem size_mirror (t : PlaneTree) : t.mirror.size = t.size := sorry

/-- The mirror preserves the offspring-product weight (same multiset of outdegrees). -/
theorem weight_mirror (p : ℕ → ℝ≥0∞) (t : PlaneTree) : weight p t.mirror = weight p t := sorry

/-- **Contour of the mirror**: `C_mirror(m) = C(2(z-1) - m)` for `m ≤ 2(z-1)`. -/
theorem contourAt_mirror (t : PlaneTree) {m : ℕ} (hm : m ≤ 2 * (t.size - 1)) :
    t.mirror.contourAt m = t.contourAt (2 * (t.size - 1) - m) := sorry

/-- **Interpolated contour of the mirror**: `C_mirror(s) = C(2(z-1) - s)` on `[0, 2(z-1)]`. -/
theorem contourLin_mirror (t : PlaneTree) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s ≤ 2 * ((t.size : ℝ) - 1)) :
    t.mirror.contourLin s = t.contourLin (2 * ((t.size : ℝ) - 1) - s) := sorry

end BGW.PlaneTree

namespace BGW.StableTrees.ExactContour

open BGW.StableTrees.DiscreteForest BGW.StableTrees.TailPair

/-! ### Mirror on the locally finite carrier -/

/-- Mirror on the locally finite carrier: the mirror of the decoded finite tree, and the
identity on infinite trees. -/
noncomputable def treeMirror (τ : BGW.LocallyFinite.Tree) : BGW.LocallyFinite.Tree :=
  if h : BGW.LocallyFinite.FiniteVertices τ then
    (PlaneTree.equivFiniteVertices.symm ⟨τ, h⟩).mirror.toLocallyFinite
  else τ

theorem measurable_treeMirror : Measurable treeMirror := sorry

/-- **Mirror invariance** of the exact-size conditioned law, for every `n` (size and weight are
preserved; the Dirac leaf of the junk branch is mirror invariant). -/
theorem map_treeMirror_exactTreeLaw (μ : PMF ℕ) (n : ℕ) :
    (exactTreeLaw μ n).map treeMirror = exactTreeLaw μ n := sorry

/-! ### Contour paths and laws -/

/-- The interpolated contour (original speed, `0` after time `2(z-1)`) of the decoded finite
tree; `0` for an infinite tree. -/
noncomputable def treeContourLin (τ : BGW.LocallyFinite.Tree) (s : ℝ) : ℝ :=
  if h : BGW.LocallyFinite.FiniteVertices τ then
    (PlaneTree.equivFiniteVertices.symm ⟨τ, h⟩).contourLin s
  else 0

/-- The interpolated tree contour is continuous (the junk branch of `treeContourPath` never
occurs). -/
theorem continuous_treeContourLin (τ : BGW.LocallyFinite.Tree) :
    Continuous (treeContourLin τ) := sorry

/-- **Tree contour path** on `[0,T]`: `t ↦ (B n / n) * treeContourLin τ (2 n t)`; junk `0` if the
interpolation were discontinuous (never, `continuous_treeContourLin`). -/
noncomputable def treeContourPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0)
    (τ : BGW.LocallyFinite.Tree) : C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) :=
  if h : Continuous (treeContourLin τ) then
    ⟨fun t => B n / n * treeContourLin τ (2 * (n : ℝ) * (t : ℝ)),
      continuous_const.mul (h.comp (continuous_const.mul continuous_subtype_val))⟩
  else 0

/-- The (height, contour) pair path on `[0,1]` at time scales `nt` and `2nt`, amplitude
`B n / n` for both. -/
noncomputable def heightContourPath (B : ℕ → ℝ) (n : ℕ) (τ : BGW.LocallyFinite.Tree) :
    C(Set.Icc (0 : ℝ) 1, ℝ) × C(Set.Icc (0 : ℝ) 1, ℝ) :=
  (treeHeightPath B n 1 τ, treeContourPath B n 1 τ)

/-- **The exact-size height/contour law** on `[0,1]`: height and contour of ONE BGW tree
conditioned on size exactly `n` (sealed K02 `exactTreeLaw`, totalized). -/
noncomputable def exactHeightContourLaw (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (_hn : Admissible μ n) :
    ProbabilityMeasure (C(Set.Icc (0 : ℝ) 1, ℝ) × C(Set.Icc (0 : ℝ) 1, ℝ)) :=
  (exactTreeLaw μ n).map (heightContourPath B n)

/-- The uniform distance on `[0,a]` between the normalized contour at time `2nt` and the
normalized interpolated height at time `nt`, for one tree. -/
noncomputable def contourHeightError (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0)
    (τ : BGW.LocallyFinite.Tree) : ℝ :=
  ⨆ t : Set.Icc (0 : ℝ) (a : ℝ),
    |B n / n * treeContourLin τ (2 * (n : ℝ) * (t : ℝ)) -
      B n / n * treeHeightLin τ ((n : ℝ) * (t : ℝ))|

/-- The (height, contour) pair in the library contour convention (`s ↦ C(2(z-1)s)`, sealed
`PlaneTree.contourFunction`), scaled by `B n / n`; `0` contour for an infinite tree. -/
noncomputable def heightLibContourPath (B : ℕ → ℝ) (n : ℕ) (τ : BGW.LocallyFinite.Tree) :
    C(Set.Icc (0 : ℝ) 1, ℝ) × C(Set.Icc (0 : ℝ) 1, ℝ) :=
  (treeHeightPath B n 1 τ,
    if h : BGW.LocallyFinite.FiniteVertices τ then
      (B n / n) • (PlaneTree.equivFiniteVertices.symm ⟨τ, h⟩).contourFunction
    else 0)

/-- Measurability guard for the library-clock pair (Sol audit k13k16, finding 4). -/
theorem measurable_heightLibContourPath (B : ℕ → ℝ) (n : ℕ) :
    Measurable (heightLibContourPath B n) := sorry

/-- The exact-size height/contour law in the library contour convention. -/
noncomputable def exactHeightLibContourLaw (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ)
    (_hn : Admissible μ n) :
    ProbabilityMeasure (C(Set.Icc (0 : ℝ) 1, ℝ) × C(Set.Icc (0 : ℝ) 1, ℝ)) :=
  (exactTreeLaw μ n).map (heightLibContourPath B n)

theorem measurable_treeContourPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    Measurable (treeContourPath B n T) := sorry

theorem measurable_heightContourPath (B : ℕ → ℝ) (n : ℕ) :
    Measurable (heightContourPath B n) := sorry

/-- The mirrored tree's contour is the reflected contour (the `LocallyFinite` form of
`PlaneTree.contourLin_mirror`). -/
theorem treeContourLin_treeMirror (t : PlaneTree) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s ≤ 2 * ((t.size : ℝ) - 1)) :
    treeContourLin (treeMirror t.toLocallyFinite) s =
      treeContourLin t.toLocallyFinite (2 * ((t.size : ℝ) - 1) - s) := sorry

/-! ### Clock reconciliation -/

/-- **Paper convention, exactly**: for a tree of size `n` the contour path at scale `2nt` is
`(B n / n)` times the sealed `PlaneTree.paperContourFunction` (`s ↦ C_{2ζ s}`). -/
theorem treeContourPath_eq_paperContourFunction (B : ℕ → ℝ) {n : ℕ} (t : PlaneTree)
    (ht : t.size = n) (s : unitInterval) :
    treeContourPath B n 1 t.toLocallyFinite s = B n / n * t.paperContourFunction s := sorry

/-- **Library convention** (`2(n-1)t`, sealed `PlaneTree.contourFunction`): uniformly within
`2 |B n / n|` of the `2nt` convention. -/
theorem abs_treeContourPath_sub_contourFunction_le (B : ℕ → ℝ) {n : ℕ} (t : PlaneTree)
    (ht : t.size = n) (s : unitInterval) :
    |treeContourPath B n 1 t.toLocallyFinite s - B n / n * t.contourFunction s| ≤
      2 * |B n / n| := sorry

/-! ### Prefix, terminal and global contour estimates under exact-size conditioning -/

/-- **Prefix contour error** (finite-tree K12a bracketing with K15 on a larger prefix `a' < 1`):
on `[0,a]`, `a < 1`, the normalized contour at `2nt` is uniformly close to the normalized height
at `nt`, in probability under the exact-size laws. -/
theorem tendsto_contourHeightError_prefix {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun k => (exactTreeLaw μ (q k) : Measure BGW.LocallyFinite.Tree).real
      {τ | ε < contourHeightError B (q k) a τ}) atTop (𝓝 0) := sorry

/-- **Terminal contour window** (mirror symmetry and `H^exc(0) = 0`): the probability that the
normalized contour exceeds `ε` on `[1 - δ, 1]` is asymptotically small as `δ ↓ 0`. -/
theorem tendsto_exactContour_terminalWindow {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun δ : ℝ => limsup (fun k : ℕ =>
        (exactTreeLaw μ (q k) : Measure BGW.LocallyFinite.Tree).real
          {τ | ∃ t : Set.Icc (0 : ℝ) 1, 1 - δ ≤ (t : ℝ) ∧
            ε < B (q k) / q k * treeContourLin τ (2 * (q k : ℝ) * (t : ℝ))}) atTop)
      (𝓝[>] 0) (𝓝 0) := sorry

/-- **Global contour/height error** on `[0,1]` (first visits `H_i = C(2i - H_i)`,
`sup H ≤ sup C`, contour equicontinuity): it tends to `0` in probability. -/
theorem tendsto_contourHeightError {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (exactTreeLaw μ (q k) : Measure BGW.LocallyFinite.Tree).real
      {τ | ε < contourHeightError B (q k) 1 τ}) atTop (𝓝 0) := sorry

/-! ### C29 -/

/-- **C29 (joint height/contour, exact size)**: along every unbounded sequence of admissible
sizes, the rescaled height (time `nt`) and contour (time `2nt`) of the exact-size BGW tree
converge jointly to the excursion height `H^exc` in BOTH coordinates. -/
theorem tendsto_exactHeightContourLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) :
    Tendsto (fun k => exactHeightContourLaw μ B (q k) (hq k)) atTop
      (𝓝 ((excLaw θ).map (fun p => (p.2, p.2)))) := sorry

/-- **C29 in the library contour convention** (`2(n-1)t`): the same limit. -/
theorem tendsto_exactHeightLibContourLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) :
    Tendsto (fun k => exactHeightLibContourLaw μ B (q k) (hq k)) atTop
      (𝓝 ((excLaw θ).map (fun p => (p.2, p.2)))) := sorry

end BGW.StableTrees.ExactContour
