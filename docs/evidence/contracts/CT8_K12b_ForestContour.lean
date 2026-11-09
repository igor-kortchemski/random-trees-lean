import BGW.StableTrees.DiscreteForest
import BGW.Tree.ContourBracket
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import BGW.StableTrees.HeightTightness

/-! Contract probe for CT8 node K12b (`r5-ct8-blueprint/blueprint.md` §1 forest contour
convention and K12; `r5-ct8-blueprint/AUDIT.md` finding 7): the padded contour of the infinite
forest coded by the iid offspring sequence, its deterministic bracketing by the forest heights
(derived tree by tree from the sealed finite-tree bracketing K12a), the probabilistic comparison
`sup_{t ≤ T} |(B_n/n) C(2nt) - (B_n/n) H_lin(nt)| → 0` in probability on every positive horizon,
and, separately, the padded/unpadded comparison.

DEFINITIONS.  K02 (sealed): `offspringSeqLaw μ`, `walk`, `forestHeight ω k = H_k`,
`forestHeightLin`, `forestHeightPath B n T ω t = (B_n/n) H_lin(nt)`, ladder times `L r =
ladderTime ω r`, `LadderFinite`, `blockTree ω r` (on `LadderFinite` a tree of size
`z_r = L (r+1) - L r`, `size_blockTree`).  K12a (sealed, `BGW.PlaneTree`): `heightSeq`
(DFS heights, `0` from index `z` on), `contourAt` (contour at integer times, original speed,
length `2z - 1`, `0` afterwards), `heightLin`, `contourLin`.  New, padded clock (blueprint §1):
tree `r` occupies `[2 L r, 2 L (r+1)]`, its own contour (duration `2(z_r - 1)`) followed by two
zero units, total `2 z_r` (a singleton occupies two units at height `0`).
`contourBlock ω m = inf {r | m < 2 L (r+1)}`; `forestContour ω m` is `contourAt` of
`blockTree ω r` at local time `m - 2 L r`, `r = contourBlock ω m`, on `LadderFinite`, junk `0`
off it.  `forestContourLin` interpolates linearly at integer times (the formula of
`forestHeightLin`); `forestContourPath B n T ω t = (B_n/n) C_lin(2nt)` on `[0,T]` (dite junk `0`
if `C_lin` were discontinuous, which never happens: `continuous_forestContourLin`).
`forestContourHeightError B n T ω = sup_{t ∈ [0,T]} |(B_n/n) C_lin(2nt) - (B_n/n) H_lin(nt)|`,
the uniform distance of `forestContourPath` and `forestHeightPath`.  Unpadded clock (AUDIT
finding 7): `unpaddedStart ω r = 2 (L r - r)` (each earlier tree contributes `2(z - 1)`, zero
for a singleton), `unpaddedBlock`, `forestContourUnpadded`, `forestContourUnpaddedLin`, and
`forestContourUnpaddedError`, its uniform distance to the padded contour at the same time scale
`2nt`.  K11 (contract, copied below): `heightOscillation` (modulus of `(B_n/n) H_lin(n·)` on
`[0,T]`), `maxHeightJump` (normalized largest jump `|H_{k+1} - H_k|`, `k ≤ ⌊nT⌋`).

TRUTH CHECK.  (1) First visits.  For global index `k = L r + i`, `i < z_r`, K12a's first visit is
at local time `2i - H_i`, hence at global time `2 L r + 2i - H_i = 2k - H_k`, since
`H_k = heightSeq i` (`forestHeight_eq_treeHeight`, `heightSeq_of_lt`); for `i = z_r` both are
`0` (next root).  Padding is what makes `b_k = 2k - H_k` global; unpadded it is `2k - H_k - 2r`.
(2) Blocks.  On `LadderFinite`, `L 0 = 0` and `L` is strictly increasing, so `contourBlock`
selects the unique `r` with `2 L r ≤ m < 2 L (r+1)`; `r ≤ L r` makes `L r - r` exact.  At the
right end, local time `2 z_r`, K12a's `contourAt` and `contourLin` vanish and the forest
contour is the next root's height `0`, so the forest and tree interpolations agree on the closed
block (local times `2z - 2, 2z - 1, 2z` all carry `0`); likewise heights on `[L r, L r + z_r]`
(`heightSeq z = 0 = H_{L (r+1)}`).  (3) Bracketing: K12a `contourAt_bracket` and
`contourLin_bracket` for tree `r` transfer through (1)-(2); at the last vertex of a tree
`H_{k+1} = 0` and `b_{k+1} = 2 L (r+1)`.  (4) Normalized bound: with `u = nt`, the bracket index
satisfies `k ≤ 2u` (`H_k ≤ k`), so `H_k/2 ≤ w`, `|k - u| ≤ w` (`w ≥ 1`); if `w + 1 ≤ n` then
`k + 1 ≤ n(T+1)`, so the jump at `k` is counted by `maxHeightJump B n (T+1)` and `(k/n, t)` is a
pair of `[0,T+1]` at distance `≤ w/n`: error `≤ osc(T+1, w/n) + maxJump(T+1) + B_n/n`.
(5) Limit: under `StableDomain`, `B_n → ∞` and `B_n/n → 0` (sealed `Survival.tendsto_B_atTop`,
`Survival.tendsto_B_div_n`).  Take `M` from `forestHeight_sup_tight` at horizon `2T` and
`w_n = max 1 (nM/(2B_n))`: `w_n/n → 0`, `w_n + 1 ≤ n` eventually, and the three terms tend to
`0` in probability (`forestHeight_modulus` at `T+1` with monotonicity in `δ`;
`maxHeightJump_tendstoInMeasure` at `T+1`).  (6) Normalization: no extra constant; time `2nt`
(two contour units per vertex), amplitude `B_n/n` as for the height.  The library `θ = 2` limit
has Laplace exponent `λ²`, i.e. variance `2`, so `H = 2(X - I)/2 = X - I`; with
`B_n = σ√(n/2)`, `(B_n/n)(2/σ²)(W - I)_{nt} → X - I`, and `C(2nt) ≈ H(nt)` gives the contour the
same limit with constant exactly `1`.  (7) Unpadded: for `r = unpaddedBlock ω m`,
`C^u(m) = C(m + 2r)`; across a block boundary both sides are `0` (next nonsingleton root; local
time `2z - 2` of the padded block), so the identity holds for the interpolations, with shift
`2r` read at `⌊s⌋`.  `r = -W_{L r}` and `L r ≤ m/2 + r`; the number of nonsingleton trees among
the first `r` is at most `m/2` (law of large numbers, `μ 0 < 1`), so `r = O_P(B_n)` uniformly in
`m ≤ 2nT` (walk FCLT), the time shift `r/n → 0` in probability, and the contour modulus (from (5)
at horizon `T+1` and the height modulus) gives the comparison.  Blocks are iid with
`P(z ≥ 2) = 1 - μ 0 > 0`, so `unpaddedStart ω r → ∞` a.s.; if it stayed bounded,
`unpaddedBlock` would be junk, hence the divergence hypothesis of the identity.

PROOF PLAN.  Deterministic part (300-500 lines): block adapters from `size_blockTree`,
`forestHeight_eq_treeHeight`, `heightSeq_of_lt/of_le`, `contourAt_of_lt`, strict monotonicity of
`L` (`ladderTime_lt_succ`, `exists_ladderTime_le_lt`); first visit from `contourAt_firstVisit`;
brackets from `contourAt_bracket`/`contourLin_bracket` translated by the adapters (the
right-closed block needs the zero padding at local time `2z`); the normalized bound as in (4).
Probabilistic part (300-500 lines) as in (5): split on the three events, `ae_ladderFinite`.
Unpadded part (200-400 lines): `unpaddedStart_succ` from `size_blockTree`; divergence from
`blockTrees_law` (iid blocks, infinitely many of size `≥ 2`); the identity by the same block
bookkeeping; the comparison by (7).  Size 800-1400 lines.  RISK: the `2(z-1)` edge duration,
root transitions, zero-duration singletons (unpadded), and applying the modulus at horizon `T`
instead of `T + 1`.  The finite-tree adapter alone does not prove the forest comparison.

ACYCLICITY.  Suppliers: K02 and K12a (sealed), `BGW.StableTrees.Survival` (sealed, scalar facts
on `B`), K11 (contract: `forestHeight_modulus`, `maxHeightJump_tendstoInMeasure`,
`forestHeight_sup_tight`, copied below as statements), CT5 walk FCLT (unpadded part).  No
K13-K19, no H03: no continuum height occurs in this file.

BINDER SCOPE (AUDITOR_RULES): the suprema in `forestContourHeightError` and
`forestContourUnpaddedError` have the absolute value `|a - b|` as body and nothing follows them;
the K11 copies are verbatim (bodies `if ... else 0`, `Finset.sup` of a lambda); the sums
`osc + maxJump + B n / n` contain no big operator. -/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.StableTrees

namespace BGW.StableTrees.HeightTightness

open BGW.StableTrees.DiscreteForest

end BGW.StableTrees.HeightTightness

namespace BGW.StableTrees.ForestContour

open BGW.StableTrees.DiscreteForest BGW.StableTrees.HeightTightness

/-! ### The padded forest contour -/

/-- The block whose padded contour interval `[2 L r, 2 L (r+1))` contains the integer time `m`
(junk `0` when no block does, which happens only off `LadderFinite`). -/
noncomputable def contourBlock (ω : ℕ → ℕ) (m : ℕ) : ℕ :=
  sInf {r | m < 2 * ladderTime ω (r + 1)}

/-- **Padded forest contour** at integer time `m`: the contour of `blockTree ω r` at local time
`m - 2 L r`, `r = contourBlock ω m`, so that tree `r` occupies `[2 L r, 2 L (r+1)]` (its contour,
then two zero units); junk `0` off `LadderFinite`. -/
noncomputable def forestContour (ω : ℕ → ℕ) (m : ℕ) : ℕ :=
  if LadderFinite ω then
    (blockTree ω (contourBlock ω m)).contourAt (m - 2 * ladderTime ω (contourBlock ω m))
  else 0

/-- Linear interpolation of the padded forest contour at integer times. -/
noncomputable def forestContourLin (ω : ℕ → ℕ) (s : ℝ) : ℝ :=
  (1 - (s - ⌊s⌋₊)) * (forestContour ω ⌊s⌋₊ : ℝ) +
    (s - ⌊s⌋₊) * (forestContour ω (⌊s⌋₊ + 1) : ℝ)

/-- The normalized contour path `t ↦ (B n / n) * forestContourLin ω (2 n t)` on `[0,T]` (the
junk branch never occurs, `continuous_forestContourLin`). -/
noncomputable def forestContourPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (ω : ℕ → ℕ) :
    C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) :=
  if h : Continuous (forestContourLin ω) then
    ⟨fun t => (B n / n) * forestContourLin ω (2 * (n : ℝ) * (t : ℝ)),
      continuous_const.mul (h.comp (continuous_const.mul continuous_subtype_val))⟩
  else 0

/-- The uniform distance on `[0,T]` between the normalized contour at time `2nt` and the
normalized interpolated height at time `nt`. -/
noncomputable def forestContourHeightError (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (ω : ℕ → ℕ) : ℝ :=
  ⨆ t : Set.Icc (0 : ℝ) (T : ℝ),
    |B n / n * forestContourLin ω (2 * (n : ℝ) * (t : ℝ)) -
      B n / n * forestHeightLin ω ((n : ℝ) * (t : ℝ))|

theorem continuous_forestContourLin (ω : ℕ → ℕ) : Continuous (forestContourLin ω) := sorry

theorem forestContourPath_apply (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (ω : ℕ → ℕ)
    (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    forestContourPath B n T ω t = B n / n * forestContourLin ω (2 * (n : ℝ) * (t : ℝ)) := sorry

theorem measurable_forestContour (m : ℕ) : Measurable (fun ω => forestContour ω m) := sorry

theorem measurable_forestContourPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    Measurable (forestContourPath B n T) := sorry

theorem measurable_forestContourHeightError (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    Measurable (forestContourHeightError B n T) := sorry

/-- The error is the uniform distance between the contour and height paths. -/
theorem dist_forestContourPath_forestHeightPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0)
    (ω : ℕ → ℕ) :
    dist (forestContourPath B n T ω) (forestHeightPath B n T ω) =
      forestContourHeightError B n T ω := sorry

/-! ### Tree-by-tree adapters to K12a -/

/-- The padded clock: tree `r` occupies `2 z_r` time units, also when it is a singleton. -/
theorem two_mul_ladderTime_succ {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ) :
    2 * ladderTime ω (r + 1) = 2 * ladderTime ω r + 2 * (blockTree ω r).size := sorry

/-- On block `r` the padded forest contour is the contour of `blockTree ω r`, followed by two
zero units (local times `2 z_r - 2` and `2 z_r - 1`). -/
theorem forestContour_two_mul_ladderTime_add {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ)
    {m : ℕ} (hm : m < 2 * (blockTree ω r).size) :
    forestContour ω (2 * ladderTime ω r + m) = (blockTree ω r).contourAt m := sorry

/-- Interpolated form, on the closed block `[2 L r, 2 L r + 2 z_r]`. -/
theorem forestContourLin_two_mul_ladderTime_add {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ)
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 2 * (blockTree ω r).size) :
    forestContourLin ω (2 * ladderTime ω r + s) = (blockTree ω r).contourLin s := sorry

/-- Forest heights on block `r` are the DFS heights of `blockTree ω r`, including the value
`0` at index `z_r` (the next root). -/
theorem forestHeight_ladderTime_add {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ) {i : ℕ}
    (hi : i ≤ (blockTree ω r).size) :
    forestHeight ω (ladderTime ω r + i) = (blockTree ω r).heightSeq i := sorry

/-- Interpolated form, on the closed block `[L r, L r + z_r]`. -/
theorem forestHeightLin_ladderTime_add {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ)
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ (blockTree ω r).size) :
    forestHeightLin ω (ladderTime ω r + u) = (blockTree ω r).heightLin u := sorry

/-! ### Forest bracketing -/

/-- **Forest first visit**: the DFS vertex of global index `k` is first visited by the padded
contour at time `b_k = 2k - H_k`. -/
theorem forestContour_firstVisit {ω : ℕ → ℕ} (hω : LadderFinite ω) (k : ℕ) :
    forestContour ω (2 * k - forestHeight ω k) = forestHeight ω k := sorry

/-- **Integer forest bracketing**: between the first visits `b_k` and `b_{k+1}`, the padded
contour stays within `|H_{k+1} - H_k| + 1` of `H_k` (across a tree boundary, `H_{k+1} = 0`). -/
theorem forestContour_bracket {ω : ℕ → ℕ} (hω : LadderFinite ω) {k m : ℕ}
    (hm1 : 2 * k - forestHeight ω k ≤ m) (hm2 : m ≤ 2 * (k + 1) - forestHeight ω (k + 1)) :
    |(forestContour ω m : ℤ) - forestHeight ω k| ≤
      |(forestHeight ω (k + 1) : ℤ) - forestHeight ω k| + 1 := sorry

/-- **Real-time forest bracketing**: every contour time `s ≥ 0` lies in a bracket `k` with
`s/2 - 1 ≤ k ≤ s/2 + H_k/2`, and the interpolated contour at `s` is within
`|H_{k+1} - H_k| + 1` of `H_k`. -/
theorem forestContourLin_bracket {ω : ℕ → ℕ} (hω : LadderFinite ω) {s : ℝ} (hs : 0 ≤ s) :
    ∃ k : ℕ, s / 2 - 1 ≤ k ∧ (k : ℝ) ≤ s / 2 + (forestHeight ω k : ℝ) / 2 ∧
      |forestContourLin ω s - forestHeight ω k| ≤
        |(forestHeight ω (k + 1) : ℝ) - forestHeight ω k| + 1 := sorry

/-- **Normalized deterministic bound**: if `w ≥ 1` bounds half the heights of indices `≤ 2nT`
and `w + 1 ≤ n`, the contour/height error on `[0,T]` is at most the height oscillation at
scale `w/n` plus the largest adjacent jump, both on the horizon `T + 1`, plus `B_n/n`. -/
theorem forestContourHeightError_le {ω : ℕ → ℕ} (hω : LadderFinite ω) (B : ℕ → ℝ) {n : ℕ}
    (hB : 0 ≤ B n) (T : ℝ≥0) {w : ℝ} (hw1 : 1 ≤ w) (hwn : w + 1 ≤ n)
    (hw : ∀ j : ℕ, (j : ℝ) ≤ 2 * n * T → (forestHeight ω j : ℝ) / 2 ≤ w) :
    forestContourHeightError B n T ω ≤
      heightOscillation B n ((T : ℝ) + 1) (w / n) ω + maxHeightJump B n ((T : ℝ) + 1) ω +
        B n / n := sorry

/-! ### The probabilistic comparison -/

/-- **Contour/height comparison** (blueprint K12) on every positive horizon:
`sup_{t ≤ T} |(B_n/n) C(2nt) - (B_n/n) H_lin(nt)| → 0` in probability. -/
theorem contour_height_error_tendstoInMeasure {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure (offspringSeqLaw μ : Measure (ℕ → ℕ))
      (fun n ω => forestContourHeightError B n T ω) atTop (fun _ => (0 : ℝ)) := sorry

end BGW.StableTrees.ForestContour
