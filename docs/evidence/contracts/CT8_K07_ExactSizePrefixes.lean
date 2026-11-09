import BGW.StableTrees.ForestLocalLimit
import BGW.StableTrees.UnitExcursionLaw
import BGW.StableTrees.GammaIdentity
import BGW.StableTrees.WalkPathTightness
import BGW.StableTrees.RealAttraction
import BGW.StableTrees.Attraction.Defs
import BGW.ContinuumTrees.ExcursionCarrier
import BGW.Skorokhod.MeasurableMaps
import BGW.Skorokhod.VervaatStep
import BGW.LocallyFinite.WalkLaw
import BGW.LocallyFinite.ExcursionLaw
import BGW.LocallyFinite.SizeConditioning
import BGW.Tree.Decode
import BGW.StableTrees.DiscreteForest
import BGW.StableTrees.PathTail
import BGW.StableTrees.DiscreteBridge

/-! Contract probe for CT8 node K07 (`r5-ct8-blueprint/blueprint.md` K07 and finding 6 of
`AUDIT.md`): prefixes of the exact-size Łukasiewicz path, by the independent TAIL route.

TRUTH.  `μ` is critical, in the domain of attraction of the spectrally positive `θ`-stable law
with norming `B` (`StableDomain μ θ B`); `n` ranges over admissible sizes (`P(ζ = n) > 0`).
The exact-size walk law `exactWalkLaw μ B n hn` is the law of `t ↦ W_{⌊n t⌋}/B n` under the
offspring vector conditioned to be a tree excursion (one carrier, shared with K06).  For
`a ∈ (0,1)` its restriction to `[0,a]` is `exactWalkPrefixLaw`.  The tail walk law is the same
path map applied to a BGW tree conditioned on size `≥ n` (`tailTreeLaw`, the law of the first
long ladder block of the infinite forest by K02/K05; its path on `[0,a]` only uses the first
`⌊a n⌋ < n` increments, so no time rescaling by the tree size occurs; the increments are
extended by `0` after the end of the tree).  With `m = ⌊a n⌋`, `j = W_m + 1 = round(B n x(a)) + 1`
(`prefixStack`) the K03/K02 prefix identity is
`P_exact(prefix ∈ ·) = ∫ 1_· R_n(m,j) dP_tail`, `R_n(m,j) = exactPrefixWeight μ n m j`, and
K03 gives `R_n(m,j) → gammaA θ a (j/B n)` uniformly on compacts of `(0,∞)` of `j/B n`, along
admissible `n` (`d ∣ (n-m)-j` always holds on prefix atoms).  Both the weights and their limit
have mean one, so Scheffé replaces uniform integrability near `x = 0, ∞`.
THEOREM: the exact-size prefix converges to `(unitExcursionLaw θ).map (excursionRestrict a)`.
The terminal window is NOT used (`a < 1`).

PROOF PLAN.  (1) Prefix RN identity (`restrictLaw_exactWalkLaw_eq_withDensity`): K02
`exactPrefixMass_eq_prefixRN_mul` on atoms of the first `m` degrees, plus `prefixDensity`;
positive-denominator guard: where `G_j(n-m) = 0` also `f_j(n-m) = 0` (`f ≤ G`).  (2) Tail
convergence (`tendsto_tailWalkPrefixLaw`): K05b, built from K04 endpoint/cut convergence with
K05; stated here only as the interface it must supply.  (3) A.s. goodness: tail-prefix atoms are
lattice-good and the limit prefix is a.s. continuous at `a` with `x(a) > 0`
(`N_noFixedJump`, `levyExcLaw_noFixedJump`).  (4) Weight convergence along sequences
(`tendsto_prefixWeightFn_continuousConv`) from `exactPrefixWeight_uniform` and the evaluation
`y_k(a) → x(a)` (continuity of `x` at `a`).  (5) Generic helper
`tendsto_integral_mul_weight` (Skorokhod coupling for the separable `D a ℝ`, weights converge
a.s., mass one, `tendsto_integral_abs_sub_of_massOne`).  (6) Conclude with
`ST.levyExcLaw_prefix_eq_withDensity_tail` and `integral_gammaA_tail_eq_one`.

AMBIGUITIES RESOLVED.  The statement is for fixed `a ∈ (0,1)` with `B n` the norming at the
sample size `n` (not at `n - m`).  Not a statement about the tree conditioned exactly on size
`n` through an RN weight of the terminal marginal alone: the weight depends on the whole prefix
only through `x(a)` and the identity is on the whole prefix sigma-field.  The tail interface
`tendsto_tailWalkPrefixLaw` and the path carriers it uses are the contract
`CT8_K05b_PathTail` (drafted and audited separately), copied below, not a K07 result.

BINDER SCOPE (AUDITOR_RULES): integrands `F x * w k x` contain no `+`/`-` after a binder. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteBridge (offspringVec vecPath conditionedVecOrJunk exactWalkLaw offspringVec_countExcursions_ne_zero restrictLaw endValue)
open BGW.StableTrees.DiscreteForest (exactTreeLaw tailTreeLaw)
open BGW.StableTrees.PathTail (treeIncrements treeIncrementSeq treePrefixPath measurable_treePrefixPath tailWalkPrefixLaw tailPrefixLimit tendsto_tailWalkPrefixLaw)

namespace BGW.StableTrees.ExactPrefix

open BGW BGW.Skorokhod BGW.Probability.RealWalk

/-! ## 1. Shared discrete carriers (copied from contract CT8_K06_BridgeInvariance, not part of
this contract) -/

instance (μ : PMF ℕ) (n : ℕ) : IsProbabilityMeasure (offspringVec μ n) := by
  unfold offspringVec
  infer_instance

/-! ## 2. Prefix paths of trees and the exact/tail prefix laws -/

/-- The law of the exact-size walk path on `[0,a]`. -/
noncomputable abbrev exactWalkPrefixLaw (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (hn : Admissible μ n)
    (a : ℝ≥0) (ha : a ≤ 1) : ProbabilityMeasure (D (a : ℝ) ℝ) :=
  restrictLaw a ha (exactWalkLaw μ B n hn)

/-- The exact-size walk prefix is the prefix path of the exact-size BGW tree: one object. -/
theorem exactWalkPrefixLaw_eq_map_exactTreeLaw {μ : PMF ℕ} {B : ℕ → ℝ} {n : ℕ}
    (hn : Admissible μ n) (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    ((exactWalkPrefixLaw μ B n hn a ha.2.le : ProbabilityMeasure (D (a : ℝ) ℝ)) :
        Measure (D (a : ℝ) ℝ)) =
      ((exactTreeLaw μ n : ProbabilityMeasure BGW.LocallyFinite.Tree) :
        Measure BGW.LocallyFinite.Tree).map (treePrefixPath B n a) := sorry

/-! ## 3. The prefix weight and the Radon-Nikodym identity -/

/-- The number of pending subtrees `j = W_m + 1` read off the path value at `a`. -/
noncomputable def prefixStack (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0) (x : D (a : ℝ) ℝ) : ℕ :=
  (round (endValue a x * B n) + 1).toNat

/-- The RN weight `R_n(m,j)` (K03 `exactPrefixWeight`) as a function of the prefix path,
`m = ⌊a n⌋`, `j = prefixStack`. -/
noncomputable def prefixWeightFn (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0)
    (x : D (a : ℝ) ℝ) : ℝ :=
  exactPrefixWeight μ n ⌊(a : ℝ) * n⌋₊ (prefixStack B n a x)

/-- **Prefix RN identity** from the tail to the exact-size walk prefix law (K02
`exactTreeLaw_prefix_eq_lintegral` pushed through the prefix path). -/
theorem exactWalkPrefixLaw_eq_withDensity {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {n : ℕ} (hn : Admissible μ n) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    ((exactWalkPrefixLaw μ B n hn a ha.2.le : ProbabilityMeasure (D (a : ℝ) ℝ)) :
        Measure (D (a : ℝ) ℝ)) =
      ((tailWalkPrefixLaw μ B n a : ProbabilityMeasure (D (a : ℝ) ℝ)) :
          Measure (D (a : ℝ) ℝ)).withDensity
        (fun x => ENNReal.ofReal (prefixWeightFn μ B n a x)) := sorry

/-- The weight is nonnegative and has mean one under the tail walk prefix law
(K02 `lintegral_prefixDensity_tail`). -/
theorem integral_prefixWeightFn_tail {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {n : ℕ} (hn : Admissible μ n) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    (∀ x, 0 ≤ prefixWeightFn μ B n a x) ∧
      ∫ x, prefixWeightFn μ B n a x ∂(tailWalkPrefixLaw μ B n a : Measure (D (a : ℝ) ℝ)) = 1 :=
  sorry

/-- Measurability of the weight (a function of the value at `a` only). -/
theorem measurable_prefixWeightFn (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0) :
    Measurable (prefixWeightFn μ B n a) := sorry

/-- Tail-prefix atoms are lattice-good: `j ≥ 1` and `d ∣ (n - m) - j` (every tree has size
`≡ 1 mod d`, increments are `≡ -1 mod d`). -/
def LatticeGood (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0) (x : D (a : ℝ) ℝ) : Prop :=
  1 ≤ prefixStack B n a x ∧
    ((Scalar.latticeSpan μ : ℤ) ∣ (n : ℤ) - (⌊(a : ℝ) * n⌋₊ : ℕ) - (prefixStack B n a x : ℕ))

/-- Almost surely under the tail walk prefix law the path is lattice-good (`n` admissible). -/
theorem ae_latticeGood_tailWalkPrefixLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {n : ℕ} (hn : Admissible μ n) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    ∀ᵐ x ∂(tailWalkPrefixLaw μ B n a : Measure (D (a : ℝ) ℝ)), LatticeGood μ B n a x := sorry

/-! ## 4. Convergence of the weights and of the tail prefix -/

/-- **Weight convergence along sequences**: if `y_k → x` in `D a ℝ`, `x` is continuous at `a`
with `x(a) > 0`, and each `y_k` is lattice-good at the size `q k`, then
`R_{q k}(m, j(y_k)) → gammaA θ a (x a)` (K03 `exactPrefixWeight_uniform`). -/
theorem tendsto_prefixWeightFn_continuousConv {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1)
    {x : D (a : ℝ) ℝ} (hx : ContinuousAt x ⟨(a : ℝ), a.coe_nonneg, le_rfl⟩)
    (hxpos : 0 < endValue a x) {y : ℕ → D (a : ℝ) ℝ}
    (hy : ∀ k, LatticeGood μ B (q k) a (y k)) (hyx : Tendsto y atTop (𝓝 x)) :
    Tendsto (fun k => prefixWeightFn μ B (q k) a (y k)) atTop
      (𝓝 (gammaA θ a (endValue a x))) := sorry

/-- The tail-excursion prefix is almost surely continuous at `a` with positive value
(`N_noFixedJump`, `tailExcursionLaw ≪ N`, positivity before the end). -/
theorem ae_tailPrefix_continuousAt_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    ∀ᵐ x : D (a : ℝ) ℝ ∂(tailPrefixLimit θ a : Measure (D (a : ℝ) ℝ)),
      ContinuousAt x ⟨(a : ℝ), a.coe_nonneg, le_rfl⟩ ∧ 0 < endValue a x := sorry

/-- **Generic weighted-convergence helper (also for K15).**  If `P_k ⇒ P₀` on a separable metric
space, `w_k, w₀ ≥ 0` have mean one under `P_k, P₀`, and `w_k (y_k) → w₀ (x)` whenever
`y_k → x` with `x ∈ G` (`P₀ G = 1`) and `y_k ∈ S_k` (`P_k S_k = 1`), then the weighted measures
converge weakly: `∫ F w_k dP_k → ∫ F w₀ dP₀` for every bounded continuous `F`.  (Skorokhod
coupling, a.s. convergence of weights, Scheffé.) -/
theorem tendsto_integral_mul_weight {E : Type*} [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] [TopologicalSpace.SeparableSpace E] {P : ℕ → ProbabilityMeasure E} {P₀ : ProbabilityMeasure E}
    (hP : Tendsto P atTop (𝓝 P₀)) {w : ℕ → E → ℝ} {w₀ : E → ℝ}
    (hw : ∀ k, Measurable (w k)) (hw₀ : Measurable w₀)
    (hnn : ∀ k x, 0 ≤ w k x) (hnn₀ : ∀ x, 0 ≤ w₀ x)
    (h1 : ∀ k, ∫ x, w k x ∂(P k : Measure E) = 1) (h10 : ∫ x, w₀ x ∂(P₀ : Measure E) = 1)
    (S : ℕ → Set E) (hS : ∀ k, (P k : Measure E) (S k)ᶜ = 0)
    (G : Set E) (hG : (P₀ : Measure E) Gᶜ = 0)
    (hconv : ∀ x ∈ G, ∀ y : ℕ → E, (∀ k, y k ∈ S k) → Tendsto y atTop (𝓝 x) →
      Tendsto (fun k => w k (y k)) atTop (𝓝 (w₀ x))) (F : BoundedContinuousFunction E ℝ) :
    Tendsto (fun k => ∫ x, F x * w k x ∂(P k : Measure E)) atTop
      (𝓝 (∫ x, F x * w₀ x ∂(P₀ : Measure E))) := sorry

/-! ## 5. K07 main theorem -/

/-- **Exact-size walk prefixes (K07 main theorem).**  Along an unbounded sequence of admissible
sizes the exact-size Łukasiewicz path on `[0,a]`, `a ∈ (0,1)`, scaled by `B (q k)`, converges
weakly to the prefix of the unit excursion law. -/
theorem tendsto_exactWalkLaw_prefix {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, Admissible μ (q k))
    (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    Tendsto (fun k => exactWalkPrefixLaw μ B (q k) (hq k) a ha.2.le) atTop
      (𝓝 ((unitExcursionLaw θ).map (excursionRestrict a))) := sorry

end BGW.StableTrees.ExactPrefix
