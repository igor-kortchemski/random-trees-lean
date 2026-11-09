import BGW.StableTrees.LongExtraction
import BGW.StableTrees.FirstLongMark
import BGW.StableTrees.StableLocalLaw
import BGW.StableTrees.UnitExcursionLaw
import BGW.StableTrees.WalkPathTightness
import BGW.StableTrees.RealAttraction
import BGW.StableTrees.Attraction.Defs
import BGW.ContinuumTrees.ExcursionCarrier
import BGW.Skorokhod.ExitPartition
import BGW.Skorokhod.MeasurableMaps
import BGW.LocallyFinite.SizeConditioning
import BGW.Tree.Decode
import BGW.StableTrees.DiscreteForest

/-! Contract probe for CT8 node K05b (`r5-ct8-blueprint/blueprint.md` K05b and finding 3 of
`.orchestration/sol-audit-k06k08/AUDIT.md`): the tail walk path theorem, the discrete supplier
of K07's `tendsto_tailWalkPrefixLaw`.

TRUTH.  `μ` is critical and in the domain of attraction of the spectrally positive `θ`-stable
law with norming `B` (`StableDomain μ θ B`).  `tailTreeLaw μ n` is the BGW law conditioned on
size `≥ n` (inclusive tail conditioning, K02; meaningful at every `n`, no admissibility).  Its
path on `[0,T]` is `treePrefixPath B n T`: the Łukasiewicz increments of the tree, scaled by the
SAMPLE size `n` (never by the sampled tree size), extended by `0` after the end of the tree.
THEOREMS.  (1) `tendsto_tailWalkLaw`: for `T > 0`, `tailWalkLaw μ B n T` converges weakly to
`tailLevyExcLaw θ T`, the excursion under `N(· | ζ > 1)` restricted to `[0,T]`.  (2)
`tendsto_selectedBlockTripleLaw`: the joint endpoint/cut law of the first long block (K04
`extractionTriple`) converges to the image of the stable local law under `longCutTriple`
(retained for K14).  (3) `tendsto_tailWalkPrefixLaw`: the form K07 consumes, derived from (1)
along an unbounded sequence.

TERMINAL CONVENTION (audit finding 3).  K04 `blockIncrements` replaces the last `-1` of a block
by `0` and is `0` afterwards; the tree sequence `treeIncrementSeq` keeps that step, so its
cumulative value is `-1` after the end.  The two paths differ by at most `|1 / B n|`
(`treePrefixPath_close_error`, with `closedTreeIncrementSeq` the closed version); on arbitrary
horizons the vanishing bound is used, not equality.  For `a < 1` and `n ≥ 1` the two agree on the
tail event, since a tail tree has size `≥ n` and the prefix inspects `⌊a n⌋ < n` steps.  The
infinite-tree branch is junk (empty increments); `StableDomain` gives a.s. extinction and
positive tail mass, hence conditional finite support.

PROOF PLAN.  Localize at a deterministic source horizon `M`, apply K04 (`LongExtraction`: the
deterministic endpoint/cut convergence on good paths) with K05 (`FirstLongMark`:
`aemeasurable_firstLongMark`, `map_firstLongMark`, `ae_goodLongExtractionCutPath`,
`tendsto_measure_firstLongEnd_lt`), remove the localization by the discrete label/end bounds,
transfer the uniform `1 / B n` closing error to J1 with the identity time change, and use the
K02 identification `firstLongTree_law` of the first long ladder block with `tailTreeLaw`.

ACYCLICITY.  Suppliers: K02, K03, K04, K05, CT5.  This node does NOT import K06, K07, K08, C29,
C30 or C35, and no article identification.

BINDER SCOPE (AUDITOR_RULES): no integral or big operator is followed by `+`/`-`. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest (tailTreeLaw)

namespace BGW.StableTrees.PathTail

open BGW BGW.Skorokhod BGW.Probability.RealWalk BGW.StableTrees

/-! ## 1. Shared carriers (K05b owns the path carriers; K02 copies are marked) -/

/-- The DFS increments `(d_i - 1)` of a finite tree (empty list for infinite trees). -/
noncomputable def treeIncrements (τ : BGW.LocallyFinite.Tree) : List ℤ :=
  if h : BGW.LocallyFinite.FiniteVertices τ then
    (PlaneTree.equivFiniteVertices.symm ⟨τ, h⟩).increments
  else []

/-- The increments of a tree as a real sequence, extended by `0` after the end of the tree. -/
noncomputable def treeIncrementSeq (τ : BGW.LocallyFinite.Tree) : ℕ → ℝ :=
  fun i => ((treeIncrements τ).getD i 0 : ℤ)

/-- The path `t ↦ W_{⌊n t⌋}/B n` of a tree on `[0,T]`, with the sample size `n` (not the
size of the tree) as time scale. -/
noncomputable def treePrefixPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0)
    (τ : BGW.LocallyFinite.Tree) :
    D (T : ℝ) ℝ :=
  realStepPath (T : ℝ) n (B n) (treeIncrementSeq τ)

/-- The prefix-path map is measurable. -/
theorem measurable_treePrefixPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    Measurable (treePrefixPath B n T) := sorry

/-- The tail walk law on `[0,a]`: the path of a BGW tree conditioned on size `≥ n`. -/
noncomputable def tailWalkPrefixLaw (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0) :
    ProbabilityMeasure (D (a : ℝ) ℝ) :=
  ProbabilityMeasure.map (tailTreeLaw μ n) (treePrefixPath B n a)

/-- The prefix on `[0,a]` of the excursion under `N(· | ζ > 1)` (limit of the tail walk). -/
noncomputable def tailPrefixLimit (θ : ℝ) (a : ℝ≥0) : ProbabilityMeasure (D (a : ℝ) ℝ) :=
  (tailExcursionLaw θ).map (excursionRestrict a)

/-- The tail walk law on `[0,T]` for all horizons. -/
noncomputable def tailWalkLaw (μ : PMF ℕ) (B : ℕ → ℝ)
    (n : ℕ) (T : ℝ≥0) : ProbabilityMeasure (D (T : ℝ) ℝ) :=
  (tailTreeLaw μ n).map (treePrefixPath B n T)

/-- The tail walk prefix law is the tail walk law (same map). -/
theorem tailWalkPrefixLaw_eq_tailWalkLaw (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0) :
    tailWalkPrefixLaw μ B n a = tailWalkLaw μ B n a := rfl

/-- The tail prefix limit is the sealed `tailLevyExcLaw` (same map). -/
theorem tailPrefixLimit_eq_tailLevyExcLaw (θ : ℝ) (a : ℝ≥0) :
    tailPrefixLimit θ a = tailLevyExcLaw θ a := rfl

/-! ## 2. Terminal convention: closed tree increments -/

/-- The tree increments with the terminal `-1` step replaced by `0` (the K04 `blockIncrements`
convention); `0` after the end of the tree. -/
noncomputable def closedTreeIncrementSeq (τ : BGW.LocallyFinite.Tree) : ℕ → ℝ :=
  fun i => if i + 1 < (treeIncrements τ).length then treeIncrementSeq τ i else 0

/-- Uniform closing error between the tree path and the closed path (transfers to J1 with the
identity time change). -/
theorem treePrefixPath_close_error (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0)
    (τ : BGW.LocallyFinite.Tree) (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    |treePrefixPath B n T τ t -
      realStepPath (T : ℝ) n (B n) (closedTreeIncrementSeq τ) t| ≤
        |1 / B n| := by
  sorry

/-! ## 3. Tail walk path theorems -/

/-- **Tail walk path theorem (K05b main theorem).**  For every `T > 0` the tail-conditioned tree
path on `[0,T]` converges weakly to the excursion under `N(· | ζ > 1)` restricted to `[0,T]`. -/
theorem tendsto_tailWalkLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => tailWalkLaw μ B n T) atTop
      (𝓝 (tailLevyExcLaw θ T)) := by
  sorry

/-- **Form consumed by K07**: along an unbounded sequence, for `a ∈ (0,1)`.  There is
deliberately no admissibility hypothesis: inclusive tail conditioning is not exact-size
conditioning. -/
theorem tendsto_tailWalkPrefixLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop)
    (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    Tendsto (fun k => tailWalkPrefixLaw μ B (q k) a) atTop
      (𝓝 (tailPrefixLimit θ a)) := by
  sorry

/-- The law of the selected first-long-block triple (endpoints and cut) of the iid walk. -/
noncomputable def selectedBlockTripleLaw (μ : PMF ℕ) (B : ℕ → ℝ)
    (n : ℕ) (T : ℝ≥0) : ProbabilityMeasure (ℝ × ℝ × D (T : ℝ) ℝ) :=
  (iidLaw (realOffspringStepLaw μ)).map (extractionTriple (B n) n T)

/-- Measurability (a.e.) of the extraction triple under the iid law. -/
theorem aemeasurable_extractionTriple {μ : PMF ℕ} {θ : ℝ}
    {B : ℕ → ℝ} (h : StableDomain μ θ B) (n : ℕ) (T : ℝ≥0) :
    AEMeasurable (extractionTriple (B n) n T)
      (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)) := by
  sorry

/-- **Joint endpoint/cut convergence of the first long block** (retained for K14). -/
theorem tendsto_selectedBlockTripleLaw {μ : PMF ℕ} {θ : ℝ}
    {B : ℕ → ℝ} (h : StableDomain μ θ B)
    (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => selectedBlockTripleLaw μ B n T) atTop
      (𝓝 ((stableLocalLaw θ).map (longCutTriple T))) := by
  sorry

end BGW.StableTrees.PathTail
