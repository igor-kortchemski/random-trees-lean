import BGW.StableTrees.ForestLocalLimit
import BGW.StableTrees.BridgeProjectiveClose
import BGW.StableTrees.BridgeProjective
import BGW.StableTrees.StableBridgeMinimum
import BGW.StableTrees.WalkPathTightness
import BGW.StableTrees.RealAttraction
import BGW.StableTrees.Scalar.ForestBounds
import BGW.Skorokhod.VervaatStep
import BGW.Skorokhod.VervaatMeasurable
import BGW.Skorokhod.MeasurableMaps
import BGW.LocallyFinite.WalkLaw
import BGW.LocallyFinite.BridgeLaw
import BGW.LocallyFinite.ExcursionLaw
import BGW.LocallyFinite.SizeConditioning
import BGW.Tree.Decode
import BGW.StableTrees.DiscreteForest

/-! Contract probe for CT8 node K06 (`r5-ct8-blueprint/blueprint.md` K06 and finding 6 of
`AUDIT.md`): the ACTUAL walk bridge invariance principle and the cyclic (Vervaat) law of the
discrete bridge.

TRUTH.  `μ` is a critical offspring law in the domain of attraction of the spectrally positive
`θ`-stable law with norming `B` (`StableDomain μ θ B`).  The ONE discrete object is the offspring
vector `ω = (ω_0, ..., ω_{n-1})` with the product law `offspringVec μ n`.  Its Łukasiewicz step
word is `stepWord ω = (ω_i - 1)_i` and its rescaled path is `vecPath B n ω = S.stepPath
(stepWord ω) (B n)` (`t ↦ W_{⌊n t⌋}/B n`, càdlàg on `[0,1]`).  Conditioning on `countBridges n`
(`∑ ω_i = n - 1`, the walk ends at `-1`) gives `walkBridgeLaw μ B n`; conditioning on
`countExcursions n` (all partial sums `≥ 0` before time `n`) gives the exact-size walk law
`exactWalkLaw μ B n`, i.e. the Łukasiewicz path of a BGW tree conditioned on size `n`.  Both
exist exactly at admissible `n` (positive `P(ζ = n)`; Kemperman `P(bridge) = n P(ζ = n)`).
(1) `tendsto_walkBridgeLaw`: along an unbounded admissible sequence the bridge laws converge
weakly in `D[0,1]` to `stableBridgeLaw θ`; the path ends at `-1/B n`, which is a vanishing
terminal jump in J1.  (2) `map_vervaatD_walkBridgeLaw`: the càdlàg Vervaat transform of the
discrete bridge is the exact-size Łukasiewicz path law (cycle lemma: the weights are rotation
invariant and exactly one rotation of each bridge word is a tree excursion).

PROOF PLAN.  (1) Prefix identity (finite-vector adapter `bridgeVecPrefix_cond_mass`, derived
from the K02 statement `bridgePrefix_cond_mass`, which is NOT copied here):
for `a < 1` the law of the path on `[0,a]` under the bridge has density
`walkProb μ (n-m) (-1-W_m) / walkProb μ n (-1)`, `m = ⌊a n⌋`, with respect to the unconditioned
step-path law.  A uniform bound follows from `Scalar.exists_walkProb_le` and
`Scalar.exists_lower_bound_neg_one` (`c/B n ≤ walkProb μ n (-1)` at admissible `n`) and regular
variation of `B`.  The unconditioned prefix laws converge (CT5 `WalkPathTightness`/FCLT) and
the weights converge to the stable bridge weights `p_{1-a}(-x)/p_1(0)` (LLT, K03), so prefix
laws converge to `stableBridgeLaw` prefixes (`map_restrict_stableBridgeLaw`).  Not an
unconditional CMT: the conditioning is singular.  (2) Terminal window: the bridge word reversed
has the same law (exchangeability of the iid increments conditioned on the sum), so the path
near time `1` is controlled by the reversed path near time `0` (càdlàg reverse convention, error
`1/B n`).  (3) Glue tightness in `D[0,1]` (interior + both windows) and identify every
subsequential limit via its prefix laws and `stableBridge` uniqueness.  (4) Cyclic law: for a
word with a negative prefix sum `vervaatD_stepPath` gives `vervaatD (stepPath x B) = stepPath
(x.rotate (vervaatIndex x)) B`; the bridge-word map `ω ↦ rotation` pushes the conditioned
product law to the excursion-conditioned product law since weights are invariant
(`walkWeight_rotate`) and every cyclic class contains exactly one tree excursion
(`exists_unique_rotate_isTreeExcursion`), with multiplicities `n` uniform.

AMBIGUITIES RESOLVED.  The laws take `hn : Admissible μ n` (K03 `Admissible`: exact-size mass
nonzero).  Prefix times are `a : ℝ≥0` with `a ∈ Ioo 0 1`.  `B n` is the norming used at the
sample size `n` (the word length), as in `stepPath`.  The terminal value of the path is
`-1/B n`, not `0`: the discrete paths retain it (K08 uses its vanishing limit and the
independently proved zero terminal coordinates).  The prefix RN identity needs `B n ≠ 0`
(the rounded endpoint `round (x(a) * B n)` recovers the integer walk value only then).  The theorem does not claim that the
bridge limit has prefix laws absolutely continuous beyond what `stableBridgeLaw` provides.

BINDER SCOPE (AUDITOR_RULES): no big operator or integral is followed by `+`/`-`; the only
sums are inside the sealed `countBridges`. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest (degreeWeight prefixWalk exactTreeLaw)

namespace BGW.StableTrees.DiscreteBridge

open BGW BGW.Skorokhod BGW.Probability.RealWalk

/-! ## 1. The offspring vector, its path, and the two conditioned laws -/

/-- The product law of an offspring vector `(ω_0, ..., ω_{n-1})`. -/
noncomputable def offspringVec (μ : PMF ℕ) (n : ℕ) : Measure (Fin n → ℕ) :=
  Measure.pi (fun _ : Fin n => μ.toMeasure)

instance (μ : PMF ℕ) (n : ℕ) : IsProbabilityMeasure (offspringVec μ n) := by
  unfold offspringVec
  infer_instance

/-- The rescaled Łukasiewicz path `t ↦ W_{⌊n t⌋} / B n` of an offspring vector. -/
noncomputable def vecPath (B : ℕ → ℝ) (n : ℕ) (ω : Fin n → ℕ) : D 1 ℝ :=
  stepPath (stepWord ω) (B n)

/-- The path map is measurable (countable discrete source). -/
theorem measurable_vecPath (B : ℕ → ℝ) (n : ℕ) : Measurable (vecPath B n) := sorry

/-- Value at the terminal time of the path of a bridge vector: `-1 / B n`. -/
theorem vecPath_one_of_mem_countBridges {B : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n) {ω : Fin n → ℕ}
    (hω : ω ∈ countBridges n) :
    vecPath B n ω ⟨1, zero_le_one, le_rfl⟩ = -1 / B n := sorry

/-- The offspring vector conditioned on `A`; the Dirac law at `0` when the conditioning event
has mass zero (so that no proof field uses an unproved positivity fact). -/
noncomputable def conditionedVecOrJunk (μ : PMF ℕ) (n : ℕ)
    (A : Set (Fin n → ℕ)) : ProbabilityMeasure (Fin n → ℕ) :=
  if hP : IsProbabilityMeasure ((offspringVec μ n)[|A]) then
    ⟨(offspringVec μ n)[|A], hP⟩
  else
    ⟨Measure.dirac (fun _ => 0), inferInstance⟩

/-- **The walk bridge law**: the offspring vector conditioned on `∑ ω_i = n - 1`, pushed through
`vecPath` (totalized; `hn` excludes the junk branch, see the positivity theorems below). -/
noncomputable def walkBridgeLaw (μ : PMF ℕ) (B : ℕ → ℝ)
    (n : ℕ) (_hn : Admissible μ n) : ProbabilityMeasure (D 1 ℝ) :=
  (conditionedVecOrJunk μ n (countBridges n)).map (vecPath B n)

/-- **The exact-size walk law**: the offspring vector conditioned on being a tree excursion
(Łukasiewicz path of a BGW tree of size `n`), pushed through `vecPath` (totalized). -/
noncomputable def exactWalkLaw (μ : PMF ℕ) (B : ℕ → ℝ)
    (n : ℕ) (_hn : Admissible μ n) : ProbabilityMeasure (D 1 ℝ) :=
  (conditionedVecOrJunk μ n (countExcursions n)).map (vecPath B n)

/-- Admissibility (K03: exact-size mass nonzero) is positivity of the bridge mass
(Kemperman: `P(bridge) = n P(ζ = n)`).  Not used by any definition. -/
theorem offspringVec_countBridges_ne_zero {μ : PMF ℕ} {n : ℕ} (hn : Admissible μ n) :
    offspringVec μ n (countBridges n) ≠ 0 := sorry

/-- Admissibility is positivity of the excursion mass `P(excursion word) = P(ζ = n)`.
Not used by any definition. -/
theorem offspringVec_countExcursions_ne_zero {μ : PMF ℕ} {n : ℕ} (hn : Admissible μ n) :
    offspringVec μ n (countExcursions n) ≠ 0 := sorry

/-- Off the junk branch the totalized law is the conditioned product law. -/
theorem coe_conditionedVecOrJunk (μ : PMF ℕ) (n : ℕ)
    (A : Set (Fin n → ℕ))
    (hA : offspringVec μ n A ≠ 0) :
    (conditionedVecOrJunk μ n A : Measure (Fin n → ℕ)) =
      (offspringVec μ n)[|A] := by
  classical
  have hP := cond_isProbabilityMeasure hA
  simp [conditionedVecOrJunk, hP]

/-- Law of the restriction of a path to `[0, a]`, `a ≤ 1`. -/
noncomputable def restrictLaw (a : ℝ≥0) (ha : a ≤ 1) (P : ProbabilityMeasure (D 1 ℝ)) :
    ProbabilityMeasure (D (a : ℝ) ℝ) :=
  P.map (BGW.Skorokhod.restrict (E := ℝ) (show (a : ℝ) ≤ 1 by exact_mod_cast ha))

/-- The value of a path on `[0, a]` at its last time `a`. -/
noncomputable def endValue (a : ℝ≥0) (x : D (a : ℝ) ℝ) : ℝ :=
  x ⟨(a : ℝ), a.coe_nonneg, le_rfl⟩

/-! ## 2. Prefix density of the bridge and its uniform bound -/

-- Finite-vector ADAPTER derived from K02 `bridgePrefix_cond_mass` (not a copy: K02 states it
-- on the infinite sequence carrier with `bridgePrefixDensity`; this is new work, proved by
-- restriction of the infinite product to `Fin n` and the joint conditioning events).
/-- Conditional on `W_n = -1`, the mass of the first `m` degrees `a` is
`∏ μ(a_i) * walkProb μ (n-m) (-1-W_m(a)) / walkProb μ n (-1)`. -/
theorem bridgeVecPrefix_cond_mass (μ : PMF ℕ) {n m : ℕ} {a : List ℕ} (ham : a.length = m)
    (hmn : m ≤ n) (hpos : 0 < walkProb μ n (-1)) :
    ((offspringVec μ n)[|countBridges n]).real
        {ω | (List.ofFn ω).take m = a} =
      degreeWeight μ a * (walkProb μ ((n - m : ℕ) : ℤ) (-1 - prefixWalk a) /
        walkProb μ n (-1)) := sorry

/-- The bridge prefix density as a function of the path on `[0,a]`:
`walkProb μ (n-m) (-1-W_m) / walkProb μ n (-1)`, `m = ⌊a n⌋`, `W_m = B n * x(a)` rounded. -/
noncomputable def bridgePathDensity (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0)
    (x : D (a : ℝ) ℝ) : ℝ :=
  walkProb μ ((n - ⌊(a : ℝ) * n⌋₊ : ℕ) : ℤ) (-1 - round (endValue a x * B n)) /
    walkProb μ (n : ℤ) (-1)

/-- **Prefix Radon-Nikodym identity**: for `a < 1`, admissible `n` and nonzero norming `B n`
(without it the rounded endpoint loses the walk value: audit finding 1), the bridge path on
`[0,a]` has density `bridgePathDensity` with respect to the unconditioned step-path law. -/
theorem restrictLaw_walkBridgeLaw_eq_withDensity {μ : PMF ℕ} {B : ℕ → ℝ} {n : ℕ}
    (hn : Admissible μ n) (hB : B n ≠ 0) (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    ((restrictLaw a ha.2.le (walkBridgeLaw μ B n hn) : ProbabilityMeasure (D (a : ℝ) ℝ)) :
        Measure (D (a : ℝ) ℝ)) =
      ((stepPathLaw (realOffspringStepLaw μ) (a : ℝ) B n : ProbabilityMeasure (D (a : ℝ) ℝ)) :
          Measure (D (a : ℝ) ℝ)).withDensity
        (fun x => ENNReal.ofReal (bridgePathDensity μ B n a x)) := sorry

/-- **Uniform bound** of the bridge prefix density for a fixed `a < 1`
(`Scalar.exists_walkProb_le`, `Scalar.exists_lower_bound_neg_one`, regular variation of `B`). -/
theorem bridgePathDensity_le {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, Admissible μ n → ∀ x : D (a : ℝ) ℝ,
      0 ≤ bridgePathDensity μ B n a x ∧ bridgePathDensity μ B n a x ≤ C := sorry

/-- **Prefix convergence of the walk bridge**: for every `a ∈ (0,1)` the law of the walk bridge
on `[0,a]` converges to the corresponding prefix of the stable bridge. -/
theorem tendsto_restrictLaw_walkBridgeLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    Tendsto (fun k => restrictLaw a ha.2.le (walkBridgeLaw μ B (q k) (hq k))) atTop
      (𝓝 (restrictLaw a ha.2.le (stableBridgeLaw θ))) := sorry

/-! ## 3. Terminal window and the full convergence in `D[0,1]` -/

/-- **Terminal window** (time reversal of the bridge increments, endpoint error `1/B n`):
the walk bridge is uniformly small near time `1`. -/
theorem walkBridgeLaw_terminal_small {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ᶠ k : ℕ in atTop,
      ((walkBridgeLaw μ B (q k) (hq k) : ProbabilityMeasure (D 1 ℝ)) : Measure (D 1 ℝ))
        {x | ∃ t : Set.Icc (0 : ℝ) 1, 1 - δ ≤ (t : ℝ) ∧ ε ≤ |x t|} ≤ ENNReal.ofReal η :=
  sorry

/-- **Walk bridge invariance principle (K06 main theorem).**  Along an unbounded sequence of
admissible sizes, the walk conditioned to end at `-1` at time `q k`, scaled by `B (q k)`,
converges weakly in `D[0,1]` to the stable bridge `stableBridgeLaw θ`. -/
theorem tendsto_walkBridgeLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, Admissible μ (q k)) :
    Tendsto (fun k => walkBridgeLaw μ B (q k) (hq k)) atTop (𝓝 (stableBridgeLaw θ)) :=
  sorry

/-! ## 4. The cyclic law: Vervaat of the discrete bridge is the exact-size path -/

/-- The rotation of an offspring vector at the Vervaat index of its step word. -/
noncomputable def rotateVec {n : ℕ} (ω : Fin n → ℕ) : Fin n → ℕ :=
  countsOfWord n ((stepWord ω).rotate (vervaatIndex (stepWord ω)))

/-- Rotation is a measurable map of the (countable, discrete) vector space. -/
theorem measurable_rotateVec (n : ℕ) : Measurable (rotateVec (n := n)) := sorry

/-- Deterministic identity: on bridge vectors the càdlàg Vervaat map of the path is the path of
the rotated vector (`vervaatD_stepPath`, `stepWord_countsOfWord`), for positive norming. -/
theorem vervaatD_vecPath {B : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n) (hB : 0 < B n) {ω : Fin n → ℕ}
    (hω : ω ∈ countBridges n) :
    vervaatD (vecPath B n ω) = vecPath B n (rotateVec ω) := sorry

/-- A bridge vector rotated at the Vervaat index is a tree excursion (cycle lemma,
`exists_unique_rotate_isTreeExcursion`). -/
theorem rotateVec_mem_countExcursions {n : ℕ} (hn : 1 ≤ n) {ω : Fin n → ℕ}
    (hω : ω ∈ countBridges n) : rotateVec ω ∈ countExcursions n := sorry

/-- **Cyclic law at the level of vectors**: the bridge-conditioned product law, rotated at the
Vervaat index, is the excursion-conditioned product law. -/
theorem map_rotateVec_cond_countBridges {μ : PMF ℕ} {n : ℕ} (hn : Admissible μ n) :
    ((offspringVec μ n)[|countBridges n]).map rotateVec =
      (offspringVec μ n)[|countExcursions n] := sorry

/-- **Cyclic law at the level of paths (K06 second export)**: the Vervaat image of the discrete
walk bridge is the exact-size Łukasiewicz path law.  Positive norming is explicit. -/
theorem map_vervaatD_walkBridgeLaw {μ : PMF ℕ} {B : ℕ → ℝ} {n : ℕ} (hn : Admissible μ n)
    (hB : 0 < B n) :
    ((walkBridgeLaw μ B n hn : ProbabilityMeasure (D 1 ℝ)) : Measure (D 1 ℝ)).map vervaatD =
      ((exactWalkLaw μ B n hn : ProbabilityMeasure (D 1 ℝ)) : Measure (D 1 ℝ)) := sorry

/-! ### Link of `exactWalkLaw` with the exact-size tree law (library trees) -/

/-- The Łukasiewicz step path `t ↦ W_{⌊n t⌋}/B n` of a finite tree (junk path `0` for infinite
trees), from its DFS increments. -/
noncomputable def treePath (B : ℕ → ℝ) (n : ℕ) (τ : BGW.LocallyFinite.Tree) : D 1 ℝ :=
  open scoped Classical in
  if h : BGW.LocallyFinite.FiniteVertices τ then
    stepPath (PlaneTree.equivFiniteVertices.symm ⟨τ, h⟩).increments (B n)
  else stepPath [] (B n)

/-- The exact-size walk law is the Łukasiewicz path of the exact-size BGW tree: one object. -/
theorem map_treePath_exactTreeLaw {μ : PMF ℕ} {B : ℕ → ℝ} {n : ℕ} (hn : Admissible μ n) :
    ((exactTreeLaw μ n : ProbabilityMeasure BGW.LocallyFinite.Tree) :
        Measure BGW.LocallyFinite.Tree).map (treePath B n) =
      ((exactWalkLaw μ B n hn : ProbabilityMeasure (D 1 ℝ)) : Measure (D 1 ℝ)) := sorry

end BGW.StableTrees.DiscreteBridge
