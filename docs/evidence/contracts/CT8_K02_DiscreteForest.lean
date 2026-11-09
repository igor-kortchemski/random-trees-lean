import BGW.StableTrees.WalkPathTightness
import BGW.StableTrees.RealAttraction
import BGW.StableTrees.Scalar.ForestWalkBridge
import BGW.LocallyFinite.SizeConditioning
import BGW.LocallyFinite.ForestWalkLaw
import BGW.Tree.Height
import BGW.Tree.Decode
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import BGW.StableTrees.ForestLocalLimit

/-! Contract probe for CT8 node K02 (infinite forest coding, regeneration, prefix identities),
following `r5-ct8-blueprint/blueprint.md` §1, §2, K01-K02 and finding 3 and the "first nodes"
item 1 of `AUDIT.md`.  The minimal shared K01 carriers are inlined here (a contract file cannot
import another contract file); no `CT8_K01_Carriers.lean` is written.

TRUTH.  Let `μ : PMF ℕ` be an offspring law and `ω = (ω 0, ω 1, ...)` an iid sequence of
offspring numbers (`offspringSeqLaw μ`, indexing from 0).  The walk has increments `ω i - 1`:
`walk ω k = ∑_{i<k} (ω i - 1)`, `walk ω 0 = 0`.  It is coded as an infinite forest in
depth-first order.  `forestHeight ω k` is the number of weak records of the walk seen from
`k`: `#{j < k | ∀ l ∈ [j,k], W_j ≤ W_l}` (the library count of `PlaneTree.height_eq_card_recordMin`
with the whole forest in place of one tree).  Ladder times `L r = inf {k | W_k = -r}` (junk `0`
when the set is empty) are finite for all `r` a.s. when `μ` is critical and `μ 1 ≠ 1`
(the walk is skip-free downward and oscillates), `L 0 = 0`, `L` is strictly increasing, and
the `r`-th block `ω_{L r}, ..., ω_{L(r+1)-1}` is the degree sequence of a plane tree
(`blockTree`).  The blocks are iid BGW trees; on each block the forest height is the tree
height (`forestHeight_eq_treeHeight`).  Hypotheses: only `IsCritical μ` and `μ 1 ≠ 1`
(no stable domain) are needed for everything in this file; `θ`, `B` do not occur except in
the path map of `forestPairLaw`, where `B` is an arbitrary normaliser.

PROOF PLAN.
1. Shifted height identity (deterministic, no probability): for the shifted sequence
   `shiftSeq m ω i = ω (m+i)`, `H_{m+k} - min_{0≤i≤k} H_{m+i} = H_k(shiftSeq m ω)`.  Split the
   records `j < m+k` into `j ≥ m` (records of the shifted walk) and `j < m`; the latter
   are the records at `m` whose value is `≤ I = min_{[m,m+k]} W`; the minimum of `H` over
   `[m,m+k]` is attained at the first time of `I` and equals that count.
2. Stopped iid restart: for a stopping time `N` (`N ω = n` decided by `ω 0..ω (n-1)`),
   a.s. finite, an event `E` of the pre-`N` sigma-field and a measurable `A`,
   `P(E ∩ {shiftSeq N ω ∈ A}) = P(E) P(A)`: decompose along `N = n`, use the product law
   of `offspringSeqLaw` (`(P).map (shiftSeq n) = P` and independence of the first `n`
   coordinates from the rest).  No continuous height Markov property is used.
3. Ladder finiteness a.s.: critical nondegenerate walk has `liminf = -∞`; skip-free
   downward gives all levels.  Blocks: `blockTree` is the `PlaneTree.ofDegrees?` decoding of the
   block degrees; sizes `L(r+1) - L r`; blocks of the walk before `L r` have all values `> -r`.
4. `forestHeight_eq_treeHeight` from `PlaneTree.height_eq_card_recordMin`: records `j` in earlier
   blocks fail because `W (L r) = -r < W_j`.
5. `forestPairLaw_fst`: `walk ω = partialSum (ω i - 1)` and the push-forward of
   `offspringSeqLaw μ` under `ω ↦ (ω i - 1 : ℝ)` is `iidLaw (realOffspringStepLaw μ)`.
6. Blocks are iid BGW (`blockTrees_law`): strong Markov at the ladder times (item 2 with
   `N = L r`) plus the branching/atom product (`bienaymeLaw` atoms are `PlaneTree.weight`
   and `forestWeight`).  `firstLongTree_law` follows from the geometric series
   `P(first long block index = r, block ∈ A) = P(short)^r P(long, A)`, not by optional
   stopping at the start of the block (selection depends on the block's future).
7. Prefix identities: the first `m` degrees `a` of a tree of size `≥ n > m` form a surviving
   prefix (all partial path values `≥ 0`), `j = W_m + 1` trees remain, and
   `P(prefix = a, ζ ≥ n) = ∏ μ(a_i) G_j(n-m)`, `P(prefix = a, ζ = n) = ∏ μ(a_i) f_j(n-m)`,
   where `f_j(r) = (forestWeight μ j r).toReal`, `G_j(r) = ∑_{k ≥ r} f_j(k)`.  Divide by
   `G_1(n)`, `f_1(n)` for the tail and exact laws.
   The bridge version is `P(prefix = a, W_n = -1) = ∏ μ(a_i) * P(W_{n-m} = -1 - W_m(a))`.

CONVENTIONS (binding for later nodes).
* walk increments `ξ - 1`; time indexed from 0; `walk ω 0 = 0`; `walk ω k` is the Łukasiewicz
  path value BEFORE exploring vertex `k` (library `PlaneTree.lukasiewicz`).
* all offspring laws: `μ : PMF ℕ`; critical (`IsCritical`) and `μ 1 ≠ 1` are explicit hypotheses
  of each theorem that needs them (finite ladder times, block laws, tail mass); the carriers
  and deterministic statements are for arbitrary `ω` / arbitrary `μ`.
* ladder times use `ℕ`-valued `sInf` (junk `0` off `LadderFinite ω`); every statement about
  blocks assumes `LadderFinite ω` or holds a.s.
* trees as measure-space points are `BGW.LocallyFinite.Tree` (library carrier); blocks are
  mapped by `PlaneTree.toLocallyFinite`; there is no measurable structure on `PlaneTree`.
* `tailTreeLaw`/`exactTreeLaw` are totalised by a Dirac leaf when the conditioning event has
  mass zero; every export quantifies the positivity (`Admissible μ n`).
* ladder-block lengths `L (r+1) - L r` are tree sizes; a "long" block has size `≥ n`.
* `firstLongTree_law` is stated for `IsCritical μ` and `μ 1 ≠ 1` only; the stable domain is
  not needed here; `n ≥ 1` is not needed either (blocks have size `≥ 1`).
Estimate 1000-1800 lines. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical

open BGW.LocallyFinite (bienaymeLaw sizeEvent)

-- Shared definitions `Admissible`, `forestMass`, `forestTail`, `exactPrefixWeight` and
-- `forestTail_one_eq_sizeGe`: `BGW.StableTrees.ForestLocalLimit` (sealed).


namespace BGW.StableTrees.DiscreteForest

open BGW.Skorokhod BGW.Probability.RealWalk

/-! ## 1. The iid offspring sequence, its walk and the record-count height -/

/-- The law of an iid sequence of offspring numbers with law `μ`, indexed from `0`. -/
noncomputable def offspringSeqLaw (μ : PMF ℕ) : ProbabilityMeasure (ℕ → ℕ) :=
  ⟨Measure.infinitePi (fun _ : ℕ => μ.toMeasure), inferInstance⟩

/-- The walk `W ω k = ∑_{i<k} (ω i - 1)`, with `W ω 0 = 0`. -/
def walk (ω : ℕ → ℕ) (k : ℕ) : ℤ := ∑ i ∈ Finset.range k, ((ω i : ℤ) - 1)

/-- The shifted offspring sequence `i ↦ ω (m + i)`. -/
def shiftSeq (m : ℕ) (ω : ℕ → ℕ) : ℕ → ℕ := fun i => ω (m + i)

/-- The record-count height of the infinite forest coded by `ω` at time `k`: the number of
weak running minima `j < k` of the walk seen from `k`, namely
`#{j < k | ∀ l ∈ [j,k], W_j ≤ W_l}`. -/
noncomputable def forestHeight (ω : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((Finset.range k).filter
    (fun j => ∀ l, j ≤ l → l ≤ k → walk ω j ≤ walk ω l)).card

/-- Linear interpolation of the integer-time heights (not of the walk). -/
noncomputable def forestHeightLin (ω : ℕ → ℕ) (t : ℝ) : ℝ :=
  (1 - (t - ⌊t⌋₊)) * (forestHeight ω ⌊t⌋₊ : ℝ) + (t - ⌊t⌋₊) * (forestHeight ω (⌊t⌋₊ + 1) : ℝ)

/-- The interpolated height is continuous. -/
theorem continuous_forestHeightLin (ω : ℕ → ℕ) : Continuous (forestHeightLin ω) := sorry

/-- The normalised interpolated height path `t ↦ (B n / n) * forestHeightLin ω (n t)` on
`[0,T]`. -/
noncomputable def forestHeightPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (ω : ℕ → ℕ) :
    C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) :=
  ⟨fun t => (B n / n) * forestHeightLin ω ((n : ℝ) * (t : ℝ)),
    (continuous_const.mul ((continuous_forestHeightLin ω).comp
      (continuous_const.mul continuous_subtype_val)))⟩

/-- The rescaled floor-step walk `t ↦ W_{⌊n t⌋} / B n` as an element of `D T ℝ`. -/
noncomputable def forestWalkPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (ω : ℕ → ℕ) : D (T : ℝ) ℝ :=
  realStepPath (T : ℝ) n (B n) (fun i => ((ω i : ℤ) - 1 : ℝ))

/-- The pair `(walk, height)` path of the forest, with uniform topology on heights. -/
noncomputable def forestPairPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (ω : ℕ → ℕ) :
    D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) :=
  (forestWalkPath B n T ω, forestHeightPath B n T ω)

/-- (K01) Measurability of the pair path. -/
theorem measurable_forestPairPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    Measurable (forestPairPath B n T) := sorry

/-- The law of the pair path under the iid offspring sequence. -/
noncomputable def forestPairLaw (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    ProbabilityMeasure (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) :=
  (offspringSeqLaw μ).map (forestPairPath B n T)

/-- The walk `(ω i - 1)_i` of `offspringSeqLaw μ` is the iid real walk with step law
`realOffspringStepLaw μ`. -/
theorem map_offspringSeqLaw_realIncrements (μ : PMF ℕ) :
    ((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) : Measure (ℕ → ℕ)).map
        (fun ω i => ((ω i : ℤ) - 1 : ℝ)) =
      ((iidLaw (realOffspringStepLaw μ) : ProbabilityMeasure (ℕ → ℝ)) : Measure (ℕ → ℝ)) :=
  sorry

/-- The first marginal of the forest pair law is the step-path law of the offspring walk. -/
theorem forestPairLaw_fst (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    ((forestPairLaw μ B n T).toMeasure).map Prod.fst =
      ((stepPathLaw (realOffspringStepLaw μ) (T : ℝ) B n :
        ProbabilityMeasure (D (T : ℝ) ℝ)) : Measure (D (T : ℝ) ℝ)) := sorry

/-! ## 2. Deterministic shifted-height identity and stopped iid restart -/

/-- The minimum of the heights `H_m, ..., H_{m+k}`. -/
noncomputable def minHeight (ω : ℕ → ℕ) (m k : ℕ) : ℕ :=
  (Finset.range (k + 1)).inf' ⟨0, by simp⟩ (fun i => forestHeight ω (m + i))

/-- The height seen from time `m`: `H_{m+k} - min_{m≤j≤m+k} H_j` (an integer). -/
noncomputable def shiftedHeight (ω : ℕ → ℕ) (m k : ℕ) : ℤ :=
  (forestHeight ω (m + k) : ℤ) - (minHeight ω m k : ℤ)

/-- The walk of the shifted sequence is the increment of the walk after time `m`. -/
theorem walk_shiftSeq (ω : ℕ → ℕ) (m i : ℕ) :
    walk (shiftSeq m ω) i = walk ω (m + i) - walk ω m := sorry

/-- (Finding 3, deterministic) `H_{m+k} - min_{m≤j≤m+k} H_j = H_k` of the shifted sequence,
for every `ω`, `m`, `k`. -/
theorem shiftedHeight_eq (ω : ℕ → ℕ) (m k : ℕ) :
    shiftedHeight ω m k = (forestHeight (shiftSeq m ω) k : ℤ) := sorry

/-- The shifted path process is a measurable function of the shifted sequence. -/
theorem measurable_shiftSeq (m : ℕ) : Measurable (shiftSeq m) := sorry

/-- The iid sequence law is shift invariant. -/
theorem map_shiftSeq_offspringSeqLaw (μ : PMF ℕ) (m : ℕ) :
    ((offspringSeqLaw μ).toMeasure).map (shiftSeq m) = (offspringSeqLaw μ).toMeasure := sorry

/-- `E` is determined, on `{N = n}`, by the first `n` coordinates, and so is `{N = n}`:
the pre-`N` events of an `ℕ∞`-valued stopping time `N` of the coordinate filtration. -/
def PreStopped (N : (ℕ → ℕ) → ℕ∞) (E : Set (ℕ → ℕ)) : Prop :=
  ∀ (n : ℕ) (ω ω' : ℕ → ℕ), N ω = n → (∀ i < n, ω i = ω' i) → N ω' = n ∧ (ω ∈ E ↔ ω' ∈ E)

/-- A stopping time of the coordinate filtration with values in `ℕ∞`. -/
def IsSeqStoppingTime (N : (ℕ → ℕ) → ℕ∞) : Prop := PreStopped N Set.univ

/-- (Stopped iid restart, finite guard) For an a.s. finite stopping time `N`, a pre-`N`
event `E` and a measurable `A`, the restarted sequence `shiftSeq N ω` is independent of `E`
and has the law `P`.  Consequence of the product law (item 2 of the plan). -/
theorem stoppedRestart (μ : PMF ℕ) (N : (ℕ → ℕ) → ℕ∞) (hN : IsSeqStoppingTime N)
    (hfin : ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure, N ω ≠ ⊤)
    {E : Set (ℕ → ℕ)} (hE : PreStopped N E) {A : Set (ℕ → ℕ)} (hA : MeasurableSet A) :
    (offspringSeqLaw μ).toMeasure
        (E ∩ {ω | ∃ n : ℕ, N ω = n ∧ shiftSeq n ω ∈ A}) =
      (offspringSeqLaw μ).toMeasure E * (offspringSeqLaw μ).toMeasure A := sorry

/-- (Regeneration of the height at a stopping time) For `N` a.s. finite stopping time and `E`
pre-`N`, the height seen from `N` is independent of `E` and has the law of the height. -/
theorem stoppedRestart_height (μ : PMF ℕ) (N : (ℕ → ℕ) → ℕ∞) (hN : IsSeqStoppingTime N)
    (hfin : ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure, N ω ≠ ⊤)
    {E : Set (ℕ → ℕ)} (hE : PreStopped N E) {A : Set (ℕ → ℤ)} (hA : MeasurableSet A) :
    (offspringSeqLaw μ).toMeasure
        (E ∩ {ω | ∃ n : ℕ, N ω = n ∧ (fun k => shiftedHeight ω n k) ∈ A}) =
      (offspringSeqLaw μ).toMeasure E *
        (offspringSeqLaw μ).toMeasure {ω | (fun k => (forestHeight ω k : ℤ)) ∈ A} := sorry

/-! ## 3. Ladder times, blocks, and the tree height on a block -/

/-- Ladder times `L r = inf {k | W_k = -r}` (junk `0` if the set is empty). -/
noncomputable def ladderTime (ω : ℕ → ℕ) (r : ℕ) : ℕ := sInf {k | walk ω k = -(r : ℤ)}

/-- All ladder levels are reached. -/
def LadderFinite (ω : ℕ → ℕ) : Prop := ∀ r : ℕ, ∃ k, walk ω k = -(r : ℤ)

/-- `L 0 = 0`. -/
theorem ladderTime_zero (ω : ℕ → ℕ) : ladderTime ω 0 = 0 := sorry

/-- Critical nondegenerate walks reach every level downward a.s. -/
theorem ae_ladderFinite (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure, LadderFinite ω := sorry

/-- On `LadderFinite`, the walk at `L r` equals `-r`. -/
theorem walk_ladderTime {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ) :
    walk ω (ladderTime ω r) = -(r : ℤ) := sorry

/-- Ladder times are strictly increasing (skip-free descent). -/
theorem ladderTime_lt_succ {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ) :
    ladderTime ω r < ladderTime ω (r + 1) := sorry

/-- Before `L r`, the walk is strictly above `-r`. -/
theorem walk_gt_of_lt_ladderTime {ω : ℕ → ℕ} (hω : LadderFinite ω) {r k : ℕ}
    (hk : k < ladderTime ω r) : -(r : ℤ) < walk ω k := sorry

/-- Block exhaustion: every time lies in exactly one block `[L r, L (r+1))`. -/
theorem exists_ladderTime_le_lt {ω : ℕ → ℕ} (hω : LadderFinite ω) (k : ℕ) :
    ∃ r, ladderTime ω r ≤ k ∧ k < ladderTime ω (r + 1) := sorry

/-- The degree sequence of the `r`-th block `ω_{L r}, ..., ω_{L(r+1)-1}`. -/
noncomputable def blockDegrees (ω : ℕ → ℕ) (r : ℕ) : List ℕ :=
  (List.range (ladderTime ω (r + 1) - ladderTime ω r)).map (fun i => ω (ladderTime ω r + i))

/-- The `r`-th block tree, with a leaf fallback when decoding `blockDegrees` fails. -/
noncomputable def blockTree (ω : ℕ → ℕ) (r : ℕ) : PlaneTree :=
  (PlaneTree.ofDegrees? (blockDegrees ω r)).getD (PlaneTree.node [])

/-- On `LadderFinite`, the block decodes to a tree with the block's degrees. -/
theorem degrees_blockTree {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ) :
    (blockTree ω r).degrees = blockDegrees ω r := sorry

/-- The size of the `r`-th block tree is `L (r+1) - L r`. -/
theorem size_blockTree {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ) :
    (blockTree ω r).size = ladderTime ω (r + 1) - ladderTime ω r := sorry

/-- The record-count height of the forest equals the tree height on each block. -/
theorem forestHeight_eq_treeHeight {ω : ℕ → ℕ} (hω : LadderFinite ω) (r i : ℕ)
    (hi : i < (blockTree ω r).size) :
    forestHeight ω (ladderTime ω r + i) = (blockTree ω r).height ⟨i, hi⟩ := sorry

/-! ## 4. Carriers for tree laws, and iid block identification -/

/-- The block as a point of the locally finite tree space. -/
noncomputable def blockLF (ω : ℕ → ℕ) (r : ℕ) : BGW.LocallyFinite.Tree :=
  (blockTree ω r).toLocallyFinite

/-- Measurability of the sequence of block trees. -/
theorem measurable_blockLF : Measurable (fun ω r => blockLF ω r) := sorry

/-- The BGW law conditioned on size `≥ n` (including the null event of infinite trees);
the Dirac law at the leaf when the conditioning event has mass zero. -/
noncomputable def tailTreeLaw (μ : PMF ℕ) (n : ℕ) : ProbabilityMeasure BGW.LocallyFinite.Tree :=
  if h : BGW.LocallyFinite.bienaymeLaw μ.toMeasure (Attraction.sizeGeEvent n) ≠ 0 then
    ⟨(BGW.LocallyFinite.bienaymeLaw μ.toMeasure)[|Attraction.sizeGeEvent n],
      cond_isProbabilityMeasure h⟩
  else ⟨Measure.dirac BGW.LocallyFinite.leaf, inferInstance⟩

/-- The BGW law conditioned on size exactly `n`; the Dirac leaf if `n` is not admissible. -/
noncomputable def exactTreeLaw (μ : PMF ℕ) (n : ℕ) : ProbabilityMeasure BGW.LocallyFinite.Tree :=
  if h : Admissible μ n then
    ⟨(BGW.LocallyFinite.bienaymeLaw μ.toMeasure)[|BGW.LocallyFinite.sizeEvent n],
      BGW.LocallyFinite.isProbabilityMeasure_cond_sizeEvent μ.toMeasure h⟩
  else ⟨Measure.dirac BGW.LocallyFinite.leaf, inferInstance⟩

/-- Critical nondegenerate trees have arbitrarily large finite sizes: the tail mass is
positive for every `n`. -/
theorem bienaymeLaw_sizeGeEvent_ne_zero (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (n : ℕ) : BGW.LocallyFinite.bienaymeLaw μ.toMeasure (Attraction.sizeGeEvent n) ≠ 0 := sorry

/-- Admissibility is positivity of the forest weight `f_1 (n)`. -/
theorem admissible_iff_forestWeight_pos (μ : PMF ℕ) (n : ℕ) :
    Admissible μ n ↔ 0 < (BGW.forestWeight μ 1 n).toReal := sorry

/-- The blocks of the walk are iid BGW trees:
`(blockLF ω r)_r ~ (bienaymeLaw μ)^{⊗ ℕ}`. (Skip-free strong Markov at `L r` and the
branching/atom product.) -/
theorem blockTrees_law (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ((offspringSeqLaw μ).toMeasure).map (fun ω r => blockLF ω r) =
      Measure.infinitePi (fun _ : ℕ => BGW.LocallyFinite.bienaymeLaw μ.toMeasure) := sorry

/-! ## 5. The first long tree (after block iid identification) -/

/-- The index of the first block of size `≥ n` (junk `0` if there is none). -/
noncomputable def firstLongIndex (n : ℕ) (ω : ℕ → ℕ) : ℕ :=
  sInf {r | n ≤ ladderTime ω (r + 1) - ladderTime ω r}

/-- The first tree among the ladder blocks of size `≥ n`; junk only on a null set. -/
noncomputable def firstLongTree (n : ℕ) (ω : ℕ → ℕ) : BGW.LocallyFinite.Tree :=
  blockLF ω (firstLongIndex n ω)

/-- Measurability of the first long tree. -/
theorem measurable_firstLongTree (n : ℕ) : Measurable (firstLongTree n) := sorry

/-- Existence of a long block a.s. (block sizes are iid with unbounded support). -/
theorem ae_exists_long_block (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) (n : ℕ) :
    ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure, ∃ r, n ≤ ladderTime ω (r + 1) - ladderTime ω r :=
  sorry

/-- The first long block is a BGW tree conditioned on size `≥ n`. -/
theorem firstLongTree_law (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) (n : ℕ) :
    (offspringSeqLaw μ).map (firstLongTree n) = tailTreeLaw μ n := sorry

/-! ## 6. Prefix Radon-Nikodym identities -/

/-- The series `∑ f_j` converges. -/
theorem summable_forestMass (μ : PMF ℕ) (j : ℕ) : Summable (fun r => forestMass μ j r) := sorry

/-- The shifted-sum form of `forestTail` agrees with the indicator form of K03. -/
theorem forestTail_eq_tsum_shift (μ : PMF ℕ) (j r : ℕ) (hs : Summable (forestMass μ j)) :
    forestTail μ j r = ∑' k, forestMass μ j (r + k) := sorry

/-- Product of offspring probabilities along a degree list. -/
noncomputable def degreeWeight (μ : PMF ℕ) (a : List ℕ) : ℝ := ((a.map μ).prod).toReal

/-- A prefix of degrees is surviving if all its partial walk values are `≥ 0`. -/
def IsSurvivingPrefix (a : List ℕ) : Prop :=
  ∀ i ≤ a.length, 0 ≤ ((a.take i).map (fun d => (d : ℤ) - 1)).sum

/-- The number of pending subtrees after exploring `a`: `j = W_m + 1`. -/
def prefixStack (a : List ℕ) : ℕ := (((a.map (fun d => (d : ℤ) - 1)).sum) + 1).toNat

/-- The first `m` DFS degrees of a finite tree (empty list for infinite trees). -/
noncomputable def treePrefix (m : ℕ) (τ : BGW.LocallyFinite.Tree) : List ℕ :=
  if h : BGW.LocallyFinite.FiniteVertices τ then
    ((PlaneTree.equivFiniteVertices.symm ⟨τ, h⟩).degrees).take m
  else []

/-- Finite trees whose first `m` DFS degrees are `a`. -/
def prefixCylinder (m : ℕ) (a : List ℕ) : Set BGW.LocallyFinite.Tree :=
  {τ | BGW.LocallyFinite.FiniteVertices τ ∧ treePrefix m τ = a}

/-- The tail mass is `G_1(n)` (infinite trees are null under criticality and `μ 1 ≠ 1`). -/
theorem tailMass_eq_forestTail (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) (n : ℕ) :
    (BGW.LocallyFinite.bienaymeLaw μ.toMeasure (Attraction.sizeGeEvent n)).toReal =
      forestTail μ 1 n := sorry

/-- Tail law of a surviving prefix: `P(prefix = a | ζ ≥ n) = ∏μ(a_i) G_j(n-m) / G_1(n)`,
with `m = |a| < n`, `j = W_m + 1`, positive denominator. -/
theorem tailPrefixMass (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) {n m : ℕ} {a : List ℕ}
    (ham : a.length = m) (hmn : m < n) (hs : IsSurvivingPrefix a)
    (hG : 0 < forestTail μ 1 n) :
    ((tailTreeLaw μ n).toMeasure).real (prefixCylinder m a) =
      degreeWeight μ a * forestTail μ (prefixStack a) (n - m) / forestTail μ 1 n := sorry

/-- Exact law of a surviving prefix: `P(prefix = a | ζ = n) = ∏μ(a_i) f_j(n-m) / f_1(n)`,
at an admissible size. -/
theorem exactPrefixMass (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) {n m : ℕ}
    {a : List ℕ} (hn : Admissible μ n) (ham : a.length = m) (hmn : m < n)
    (hs : IsSurvivingPrefix a) :
    ((exactTreeLaw μ n).toMeasure).real (prefixCylinder m a) =
      degreeWeight μ a * forestMass μ (prefixStack a) (n - m) / forestMass μ 1 n := sorry

/-- Prefix-atom form of the RN identity: exact mass = `R_n(m,j)` times tail mass, on every
surviving prefix with positive denominators. -/
theorem exactPrefixMass_eq_prefixRN_mul (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {n m : ℕ} {a : List ℕ} (hn : Admissible μ n) (ham : a.length = m) (hmn : m < n)
    (hs : IsSurvivingPrefix a) (hG : 0 < forestTail μ (prefixStack a) (n - m)) :
    ((exactTreeLaw μ n).toMeasure).real (prefixCylinder m a) =
      exactPrefixWeight μ n m (prefixStack a) * ((tailTreeLaw μ n).toMeasure).real (prefixCylinder m a) :=
  sorry

/-- The prefix density, as a function of the first `m` degrees; `0` off surviving prefixes. -/
noncomputable def prefixDensity (μ : PMF ℕ) (n m : ℕ) (a : List ℕ) : ℝ≥0∞ :=
  if a.length = m ∧ IsSurvivingPrefix a then ENNReal.ofReal (exactPrefixWeight μ n m (prefixStack a))
  else 0

/-- Radon-Nikodym identity from the tail to the exact law on the first-`m`-degrees
sigma-field: for every set `S` of degree words,
`P_exact(prefix ∈ S) = ∫_{prefix ∈ S} prefixDensity d P_tail`. -/
theorem exactTreeLaw_prefix_eq_lintegral (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {n m : ℕ} (hn : Admissible μ n) (hmn : m < n) (S : Set (List ℕ)) :
    (exactTreeLaw μ n).toMeasure (treePrefix m ⁻¹' S) =
      ∫⁻ τ in treePrefix m ⁻¹' S, prefixDensity μ n m (treePrefix m τ)
        ∂((tailTreeLaw μ n).toMeasure) := sorry

/-- The tail expectation of the RN density is one. -/
theorem lintegral_prefixDensity_tail (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {n m : ℕ} (hn : Admissible μ n) (hmn : m < n) :
    ∫⁻ τ, prefixDensity μ n m (treePrefix m τ) ∂((tailTreeLaw μ n).toMeasure) = 1 := sorry

/-! ### Bridge prefix -/

/-- The first `m` offspring numbers of `ω`. -/
def seqPrefix (m : ℕ) (ω : ℕ → ℕ) : List ℕ := (List.range m).map ω

/-- The walk value `W_m(a) = ∑ (a_i - 1)` of a degree word. -/
def prefixWalk (a : List ℕ) : ℤ := (a.map (fun d => (d : ℤ) - 1)).sum

/-- Bridge prefix mass:
`P(first m degrees = a, W_n = -1) = ∏μ(a_i) * P(W_{n-m} = -1 - W_m(a))`, for `m ≤ n`. -/
theorem bridgePrefix_mass (μ : PMF ℕ) {n m : ℕ} {a : List ℕ} (ham : a.length = m)
    (hmn : m ≤ n) :
    ((offspringSeqLaw μ).toMeasure).real {ω | seqPrefix m ω = a ∧ walk ω n = -1} =
      degreeWeight μ a * walkProb μ ((n - m : ℕ) : ℤ) (-1 - prefixWalk a) := sorry

/-- Bridge-prefix density: `walkProb μ (n-m) (-1-W_m) / walkProb μ n (-1)`. -/
noncomputable def bridgePrefixDensity (μ : PMF ℕ) (n m : ℕ) (w : ℤ) : ℝ :=
  walkProb μ ((n - m : ℕ) : ℤ) (-1 - w) / walkProb μ n (-1)

/-- Conditional on `W_n = -1`, the prefix mass is `∏μ(a_i)` times the bridge-prefix density
(positive denominator). -/
theorem bridgePrefix_cond_mass (μ : PMF ℕ) {n m : ℕ} {a : List ℕ} (ham : a.length = m)
    (hmn : m ≤ n) (hpos : 0 < walkProb μ n (-1)) :
    (((offspringSeqLaw μ).toMeasure)[|{ω | walk ω n = -1}]).real
        {ω | seqPrefix m ω = a} =
      degreeWeight μ a * bridgePrefixDensity μ n m (prefixWalk a) := sorry

end BGW.StableTrees.DiscreteForest
