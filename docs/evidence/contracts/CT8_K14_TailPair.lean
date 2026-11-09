import BGW.StableTrees.PathTail
import BGW.StableTrees.DiscreteForest
import BGW.StableTrees.LongExtraction
import BGW.StableTrees.FirstLongMark
import BGW.StableTrees.UnitExcursionLaw
import BGW.StableTrees.StableLocalLaw
import BGW.Tree.ContourBracket
import BGW.Skorokhod.Restrict
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import BGW.StableTrees.HeightProcess
import BGW.StableTrees.HeightBridges
import BGW.StableTrees.HeightContinuity
import BGW.StableTrees.ExcursionHeight
import BGW.StableTrees.JointExcursion
import BGW.StableTrees.HeightTightness

/-! Contract probe for CT8 node K14 (`r5-ct8-blueprint/blueprint.md` §1, K14;
`CLASSICAL_THEORY_INPUTS.md` C28; `r5-ct8-blueprint/AUDIT.md` finding 8): the size-tail
theorem for the joint (walk, height) pair of a BGW tree conditioned on having at least `n`
vertices, on EVERY positive horizon `T` (also `T > 1`), with the sample size `n` (not the random
tree size) as time scale.

DEFINITIONS (concrete, no `sorry`; junk only off the finite part of `LocallyFinite.Tree`, or
on a discontinuity branch that never occurs).
* `treeHeightLin τ u`: K12a's `PlaneTree.heightLin` (linear interpolation of the DFS heights
  `|v_i|`, `i < z`, and of the values `0` from index `z` on) of the finite tree decoded by
  `PlaneTree.equivFiniteVertices` (as K02's `treePrefix`); `0` on infinite trees.
* `treeHeightPath B n T τ`: `t ↦ (B n / n) * treeHeightLin τ (n t)` in `C([0,T], ℝ)`; dite junk
  `0` if `treeHeightLin τ` were discontinuous (never: `continuous_treeHeightLin`).  For a tree of
  size `z` it interpolates `H_z = 0` and vanishes from time `z/n` on (`treeHeightPath_eq_zero`).
* `treePairPath B n T τ = (treePrefixPath B n T τ, treeHeightPath B n T τ)`: the sealed K05b walk
  path (`W_⌊nt⌋ / B n`) and the height path of the SAME tree, in `D T ℝ × C([0,T], ℝ)` (J1 ×
  uniform).  Walk convention: the sealed `treePrefixPath` keeps the terminal step, so the walk
  is `-1/B n` from time `z/n` on; the blueprint's zero-at/after-`z` path is the sealed
  `closedTreeIncrementSeq` path, uniformly within `|1/B n|` (`treePrefixPath_close_error`).
  Keeping the sealed map makes the first marginal literally `tailWalkLaw` (`tailPairLaw_map_fst`).
* `tailPairLaw μ B n T = (tailTreeLaw μ n).map (treePairPath B n T)`: one tree, both
  coordinates (never independent sampling).  `tailTreeLaw` is K02's totalized law (Dirac leaf
  if the tail mass vanished, which never happens for critical nondegenerate `μ`).
* `extractedHeight h g d t = if t ≤ d - g then h (g + t) else 0`: the height of the block
  `[g, d]` read off a height function, stopped at zero (used on both sides of the coupling).
* Copied from contracts (not part of this contract): H04 `IsExcursionHeightVersion`,
  `excursionHeight`, `ae_heightLoc_passageEndpoints`, `ae_jumpExcursion_heightVersion`; J01
  `heightRestrict`, `excursionPair`, `tailExcLaw`, `measurable_excursionPair`,
  `tailExcLaw_map_fst`; K11 `tendsto_forestPairLaw` (the walk/height part of K13's C27, which is
  all K14 consumes; K13's contour coordinate is not used).

TRUTH CHECK.
(1) Target.  `tailExcLaw θ T = (tailExcursionLaw θ).map (excursionPair θ T)`: the whole
excursion under `N(· | ζ > 1)` and its H04 height, both restricted to `[0,T]` and identically
`0` after the lifetime, for every `T > 0`; J01 `tailExcLaw_eq_mixture` describes it for
`T > 1` too, with ONE common lifetime `u` of density `(1/θ) u^(-1-1/θ)` on `(1, ∞)`, path scaled
by `u^(1/θ)`, height by `u^(1-1/θ)`, both stopped at zero.  Its first marginal is the sealed
`tailLevyExcLaw θ T` (J01 `tailExcLaw_map_fst`), the limit of the sealed `tailWalkLaw`
(`tendsto_tailWalkLaw`), consistent with `tailPairLaw_map_fst`.
(2) Scales.  Time `nt` for both coordinates, amplitudes `1/B_n` (walk) and `B_n/n` (height), as
in K02's forest pair; the random size `ζ ≥ n` is not used as a clock.  Under the tail law
`ζ/n` has the nondegenerate limit law of the lifetime (density above), so `T > 1` is a genuine
horizon: the pair is stopped at zero after `ζ/n`.
(3) Normalization, constants exactly `1`.  The library `θ = 2` process has Laplace exponent
`λ²` (variance `2`), its height is `X - I` (H02 `ae_height_two`), so the `θ = 2` excursion height
is the excursion path (H04 `ae_excursionHeight_two`), so at `θ = 2` both coordinates of the
limit coincide.  Discrete check with finite variance `σ²`, `B_n = σ√(n/2)`: the classical
approximation `H_k ≈ (2/σ²) W_k` gives `(B_n/n) H_{nt} ≈ (B_n/n)(2/σ²) W_{nt} = W_{nt}/B_n`,
the walk coordinate, as required; no `2/σ²` is inserted in the continuum limit.
(4) Locality.  Discrete: `treeHeightPath_blockLF` (K02 `forestHeight_eq_treeHeight`, heights
`0` at ladder times).  Continuous: `ae_excursionHeight_firstLongMark` (H04 locality at the first
long label, which is a passage jump a.s., sealed `ae_firstLongLabel_mem`).  The selected trees
are identified by K02 (`map_offspringSeqLaw_firstLongTree`) and the selected marks by K05
(`map_firstLongMark_excursionPair`), so no new conditioning argument is needed.
(5) Coupling bound `abs_extractedHeight_sub_le` (deterministic, checked case by case): with
`‖H_n - H‖ ≤ ε` on `[0,M]`, `0 ≤ g ≤ d ≤ M`, `0 ≤ g_n`, `d_n ≤ M`, `H d = 0`, and `η` bounding
the oscillation of `H` on `[0,M]` at lag `|g_n - g| + |d_n - d|`: if `t` is inside both blocks
the error is `≤ ε + η` (lag `|g_n - g|`); inside the discrete block only, `|H_n(g_n + t)| ≤ ε +
|H(g_n + t) - H(d)|` with `g_n + t - d ∈ (g_n - g, d_n - d]`; inside the limit block only,
`|H(g + t) - H(d)|` with `d - g - t < (d - d_n) + (g_n - g)`; outside both, `0`.  `ε, η ≥ 0`
follow from the hypotheses at `0 ∈ [0,M]`.  The limit endpoint zero `H d = 0` is H04
`ae_heightLoc_passageEndpoints`; no discrete endpoint zero is needed.
(6) No junk.  `treePairPath` is measurable (countable finite carrier, `measurable_treePairPath`);
the limit map is measurable (J01); the continuity dite never takes its junk branch.

PROOF PLAN (blueprint K14).  Fix `T`; localize on `{d < M}` for a deterministic `M > T`, then
`M → ∞` (sealed `tendsto_measure_firstLongEnd_lt`).  Skorokhod-couple K11's forest pair on
`[0,M]` (limit: the H03 graph, i.e. `heightLoc θ f` on one event,
H03 `ae_heightPrefix_restrict_all`) with the sealed K05b/K04 selected triple
`(g_n, d_n, cut_n) → (g, d, cut)` of the same walk (`tendsto_selectedBlockTripleLaw`; the
deterministic K04 extraction applies a.s. on `GoodLongExtractionCutPath M T`, K05
`ae_goodLongExtractionCutPath`).  Walk: K05b's closed-path comparison plus K04's
endpoint-aligned J1 estimate.  Height: `treeHeightPath_blockLF` writes the tree height as
`extractedHeight` of the forest height at `(g_n, d_n)`, `ae_excursionHeight_firstLongMark`
writes the limit height as `extractedHeight` of `heightLoc` at `(g, d)`, and
`abs_extractedHeight_sub_le` with the uniform forest error and the modulus of `heightLoc` on
`[0,M]` (continuous, H03) gives uniform convergence on `[0,T]` (the continuity at the end is
H04 `ae_heightLoc_passageEndpoints`).  Joint a.s. convergence of the pair, then
`map_offspringSeqLaw_firstLongTree` and `map_firstLongMark_excursionPair` identify the laws.
Size 450-850 lines.  RISK: independent sampling of path/height or of their lifetime;
replacing the all-horizon target by a unit-horizon corollary; using `ζ` as clock.

ACYCLICITY.  Sealed suppliers: K02 (`DiscreteForest*`), K04 (`LongExtraction*`), K05
(`FirstLongMark*`), K05b (`PathTail*`), K12a (`ContourBracket`), H03 (`HeightContinuity*`),
E06 (`UnitExcursionLaw*`).  Contract suppliers (copied statements): H04, J01, K11.  No K13
contour, no K15-K19 (K15 consumes this node), no C35.

BINDER SCOPE (AUDITOR_RULES).  No integral, sum or supremum occurs in the new declarations;
`extractedHeight` is an `if`; `ε + η` contains no big operator.  In the copied H04 statements
each `∀ᵐ` body runs to the end of the statement and the `if ... else 0` is the whole right-hand
side. -/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees

end BGW.StableTrees

namespace BGW.StableTrees.HeightTightness

open BGW.StableTrees.DiscreteForest

end BGW.StableTrees.HeightTightness

namespace BGW.StableTrees.TailPair

open BGW.StableTrees.DiscreteForest BGW.StableTrees.PathTail

/-! ### Tree height and pair paths -/

/-- Linear interpolation at real time `u` of the DFS heights of a locally finite tree: K12a's
`PlaneTree.heightLin` of the decoded finite tree (heights `|v_i|` for `i < z`, then `0`), and
`0` for an infinite tree. -/
noncomputable def treeHeightLin (τ : BGW.LocallyFinite.Tree) (u : ℝ) : ℝ :=
  if h : BGW.LocallyFinite.FiniteVertices τ then
    (PlaneTree.equivFiniteVertices.symm ⟨τ, h⟩).heightLin u
  else 0

/-- The interpolated tree height is continuous (the junk branch of `treeHeightPath` never
occurs). -/
theorem continuous_treeHeightLin (τ : BGW.LocallyFinite.Tree) :
    Continuous (treeHeightLin τ) := sorry

/-- **Tree height path** on `[0,T]`: `t ↦ (B n / n) * treeHeightLin τ (n t)`, with the sample
size `n` (not the tree size) as time scale; junk `0` if the interpolation were discontinuous
(never, `continuous_treeHeightLin`). -/
noncomputable def treeHeightPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (τ : BGW.LocallyFinite.Tree) :
    C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) :=
  if h : Continuous (treeHeightLin τ) then
    ⟨fun t => B n / n * treeHeightLin τ ((n : ℝ) * (t : ℝ)),
      continuous_const.mul (h.comp (continuous_const.mul continuous_subtype_val))⟩
  else 0

/-- **Tree pair path** on `[0,T]`: the sealed K05b walk path `W_⌊nt⌋ / B n` and the height path
of the same tree. -/
noncomputable def treePairPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (τ : BGW.LocallyFinite.Tree) :
    D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) :=
  (treePrefixPath B n T τ, treeHeightPath B n T τ)

/-- **The size-tail pair law** on `[0,T]`: the (walk, height) pair of a BGW tree conditioned on
size `≥ n`, at scales `nt`, `1/B n`, `B n / n`. -/
noncomputable def tailPairLaw (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    ProbabilityMeasure (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) :=
  (tailTreeLaw μ n).map (treePairPath B n T)

/-- The height of the block `[g, d]` read off a height function `h`: `h (g + t)` for
`t ≤ d - g`, and `0` afterwards (stopped at zero). -/
noncomputable def extractedHeight (h : ℝ → ℝ) (g d t : ℝ) : ℝ :=
  if t ≤ d - g then h (g + t) else 0

/-! ### Measurability and consistency -/

theorem measurable_treeHeightPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    Measurable (treeHeightPath B n T) := sorry

theorem measurable_treePairPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    Measurable (treePairPath B n T) := sorry

/-- On a finite tree the height path is the scaled `PlaneTree.heightLin` (decoding inverts
`toLocallyFinite`). -/
theorem treeHeightPath_toLocallyFinite (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (t : PlaneTree)
    (x : Set.Icc (0 : ℝ) (T : ℝ)) :
    treeHeightPath B n T t.toLocallyFinite x = B n / n * t.heightLin ((n : ℝ) * (x : ℝ)) :=
  sorry

/-- The height path vanishes from time `z/n` on, `z` the size of the tree (stopped at zero). -/
theorem treeHeightPath_eq_zero (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (t : PlaneTree)
    (x : Set.Icc (0 : ℝ) (T : ℝ)) (hx : (t.size : ℝ) ≤ (n : ℝ) * (x : ℝ)) :
    treeHeightPath B n T t.toLocallyFinite x = 0 := sorry

/-- The first marginal of the pair law is exactly the sealed K05b tail walk law. -/
theorem tailPairLaw_map_fst (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    (tailPairLaw μ B n T).map Prod.fst = tailWalkLaw μ B n T := sorry

/-- **Selected discrete tree** (K02 `firstLongTree_law`): the pair law is the image of the iid
offspring sequence under the pair path of its first ladder block of size `≥ n`. -/
theorem map_offspringSeqLaw_firstLongTree {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (n : ℕ) (T : ℝ≥0) :
    (offspringSeqLaw μ).map (fun ω => treePairPath B n T (firstLongTree n ω)) =
      tailPairLaw μ B n T := sorry

/-- **Selected limit mark** (K05 `map_firstLongMark`): the target is the image of the stable
law under the excursion/height pair of its first excursion longer than `1`. -/
theorem map_firstLongMark_excursionPair {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) :
    (stableLocalLaw θ).map (fun f => excursionPair θ T (firstLongMark f)) = tailExcLaw θ T :=
  sorry

/-! ### Locality on both sides and the finite-window coupling bound -/

/-- **Discrete locality** (deterministic, K02 `forestHeight_eq_treeHeight`): the height path of
the `r`-th ladder block is the normalized forest height extracted at the block endpoints
`(L_r / n, L_{r+1} / n)`. -/
theorem treeHeightPath_blockLF (B : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (T : ℝ≥0) {ω : ℕ → ℕ}
    (hω : LadderFinite ω) (r : ℕ) (x : Set.Icc (0 : ℝ) (T : ℝ)) :
    treeHeightPath B n T (blockLF ω r) x =
      extractedHeight (fun s => B n / n * forestHeightLin ω ((n : ℝ) * s))
        ((DiscreteForest.ladderTime ω r : ℝ) / n)
        ((DiscreteForest.ladderTime ω (r + 1) : ℝ) / n) x := sorry

/-- **Continuous locality** (H04 at the first long label): almost surely the height of the first
excursion longer than `1` is the continuous host height extracted at its endpoints. -/
theorem ae_excursionHeight_firstLongMark {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      excursionHeight θ (firstLongMark f) t =
        extractedHeight (fun s => heightLoc θ f s.toNNReal) (firstLongEnds f).1
          (firstLongEnds f).2 t := sorry

/-- **Finite-window coupling bound** (deterministic): the extracted-height error is at most the
uniform error `ε` on `[0,M]` plus the oscillation `η` of the limit height at lag
`|g_n - g| + |d_n - d|`, given the limit endpoint zero `H d = 0`. -/
theorem abs_extractedHeight_sub_le {Hn H : ℝ → ℝ} {gn dn g d M ε η t : ℝ}
    (hg : 0 ≤ g) (hgd : g ≤ d) (hdM : d ≤ M) (hgn : 0 ≤ gn) (hdnM : dn ≤ M)
    (hε : ∀ s ∈ Set.Icc 0 M, |Hn s - H s| ≤ ε) (hd : H d = 0)
    (hη : ∀ x ∈ Set.Icc 0 M, ∀ y ∈ Set.Icc 0 M, |x - y| ≤ |gn - g| + |dn - d| →
      |H x - H y| ≤ η)
    (ht : 0 ≤ t) :
    |extractedHeight Hn gn dn t - extractedHeight H g d t| ≤ ε + η := sorry

/-! ### C28 -/

/-- **C28, every positive horizon**: the rescaled (walk, height) pair of a BGW tree conditioned
on size `≥ n` converges jointly to the excursion/height pair under `N(· | ζ > 1)` on `[0,T]`. -/
theorem tendsto_tailPairLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {T : ℝ≥0} (hT : 0 < T) :
    Tendsto (fun n : ℕ => tailPairLaw μ B n T) atTop (𝓝 (tailExcLaw θ T)) := sorry

end BGW.StableTrees.TailPair
