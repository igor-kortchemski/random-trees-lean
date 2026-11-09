import BGW.StableTrees.ExactPrefix
import BGW.StableTrees.PathTail
import BGW.StableTrees.DiscreteForest
import BGW.StableTrees.UnitExcursionLaw
import BGW.StableTrees.GammaIdentity
import BGW.StableTrees.StableLocalLaw
import BGW.Tree.ContourBracket
import BGW.Skorokhod.Restrict
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import BGW.StableTrees.HeightProcess
import BGW.StableTrees.HeightBridges
import BGW.StableTrees.HeightContinuity
import BGW.StableTrees.ExcursionHeight
import BGW.StableTrees.JointExcursion
import BGW.StableTrees.TailPair

/-! Contract probe for CT8 node K15 (`r5-ct8-blueprint/blueprint.md` K15; `AUDIT.md` finding 8;
`CLASSICAL_THEORY_INPUTS.md` C29, prefix part): joint (walk, height) prefixes of exact-size
BGW trees on `[0,a]`, `0 < a < 1`, along every unbounded sequence of admissible sizes,
converge to the prefix of the normalized excursion/height law `excLaw θ`.

DEFINITIONS (concrete, no `sorry`).
* `exactPairLaw μ B n hn a = (exactTreeLaw μ n).map (treePairPath B n a)`: the K14 pair map
  (sealed K05b walk path `W_⌊nt⌋ / B n`, K14 height path `(B n / n) H_lin(nt)`, time scale `n`)
  applied to ONE tree of the sealed K02 exact-size law, restricted to `[0,a]`.  The binder `hn`
  is not used by the body (as in the sealed `exactWalkLaw`): `exactTreeLaw` is itself totalized
  (Dirac leaf off `Admissible`), and every export quantifies `hq : ∀ k, Admissible μ (q k)`.
* Copied from contracts (not part of this contract): H04 `IsExcursionHeightVersion`,
  `excursionHeight`; J01 `heightRestrict`, `excursionPair`, `restrictPair`, `excLaw`,
  `tailExcLaw`, `measurable_restrictPair`, `tailExcLaw_map_restrictPair`, `gamma_identity`;
  K14 `treeHeightLin`, `treeHeightPath`, `treePairPath`, `tailPairLaw`,
  `measurable_treePairPath`, `tendsto_tailPairLaw`.

PREFIX-MEASURABILITY REPAIR (blueprint K15, explicit statements).  On `[0,a]`, with
`m = ⌊an⌋`, the walk reads `W_0, ..., W_m`, i.e. the first `m` DFS degrees, but the interpolated
height at time `a` reads `H_{m+1}`, and `H_{m+1}` depends on the degree of vertex `m` (the
`(m+1)`-st degree).  So the pair is NOT a function of the first `m` degrees, on which the sealed
K07 weight `prefixWeightFn μ B n a` is the exact/tail density; weighting the tail pair law by it
is false in general.  Repair: (i) `exists_treePairPath_eq_comp_treePrefix`: the pair on `[0,a]`
is a function of `treePrefix m' τ` (K02) for every `m' ≥ ⌊an⌋ + 1`; (ii)
`exactPairLaw_eq_map_withDensity`: for `a ≤ a' < 1` with `⌊an⌋ + 1 ≤ ⌊a'n⌋` (eventually true
when `a < a'`), the exact pair law on `[0,a]` is the `[0,a]`-restriction of the tail pair law on
`[0,a']` weighted by the sealed walk weight at the LARGER horizon `a'`; this is the K02 prefix RN
identity `exactTreeLaw_prefix_eq_lintegral` at `m' = ⌊a'n⌋ < n`, pushed through (i) and the
projectivity `restrictPair_treePairPath`; (iii) `tendsto_integral_mul_prefixWeightFn_tailPairLaw`:
the weighted tail pair laws at `a'` converge to `(excLaw θ).map (restrictPair _)` at `a'`.

TRUTH CHECK.
(1) Target `(excLaw θ).map (restrictPair ha.2.le)`: path and H04 height of ONE unit excursion,
restricted to `[0,a]`.  Its walk marginal is the sealed K07 target
`(unitExcursionLaw θ).map (excursionRestrict a)` (`map_fst_restrictPair_excLaw`, all `θ`), and the
walk marginal of `exactPairLaw` is the sealed `exactWalkPrefixLaw` (`exactPairLaw_map_fst`), so
the theorem extends the sealed K07 theorem `tendsto_exactWalkLaw_prefix` by the height.
(2) Γ identity (J01 `gamma_identity`, every `0 < a' < 1`): `∫ F d(excLaw prefix) =
∫ F · gammaA θ a' (x(a')) d(tailExcLaw θ 1 prefix)`; the density depends on the walk endpoint
only, which is why the discrete weight `R_n(⌊a'n⌋, W_⌊a'n⌋ + 1)` (sealed K03/K07, periodic span
`d` already cancelled in `exactPrefixWeight_uniform`) suffices once the pair is prefix measurable.
Weights are nonnegative with mean one (sealed `integral_prefixWeightFn_tail`, transported by
`tailPairLaw_map_fst`), the limit weight has mean one (`integral_gammaA_tail_eq_one`).
(3) Scope: `0 < a < 1` (at `a = 1` the exact law is singular w.r.t. the tail law); every
unbounded admissible sequence `q` (no aperiodicity, no restricted filter); `n` as time scale.
(4) Normalization: as K14; at `θ = 2` the height coordinate of the limit equals the path
coordinate (J01 `excLaw_height_eq_path_two`), i.e. `√2 e` restricted to `[0,a]`.
(5) No junk: `treePairPath` is measurable (K14), `restrictPair` is measurable (J01),
`prefixWeightFn` is measurable (sealed); `exactTreeLaw μ (q k)` is never the Dirac branch
(`hq`).

PROOF PLAN (blueprint K15).  (a) (i) by induction on DFS indices (`heightSeq j` reads the first
`j` degrees; the walk at times `≤ a` reads `⌊an⌋` increments; complete trees of size `≤ m'` are
read entirely; `treePrefix m' τ = []` only for infinite `τ` when `m' ≥ 1`).  (b) (ii) from (a),
K02 `exactTreeLaw_prefix_eq_lintegral` and the a.e. identification of `prefixDensity` with
`prefixWeightFn` (as in the sealed proof of `exactWalkPrefixLaw_eq_withDensity`).  (c) (iii):
sealed K07 `tendsto_integral_mul_weight` on `E = D a' ℝ × C([0,a'], ℝ)` (Polish × separable)
with `P_k = tailPairLaw μ B (q k) a'` (K14), `w_k z = prefixWeightFn μ B (q k) a' z.1`,
`w₀ z = max (gammaA θ a' (evalEnd a' z.1)) 0`, `S_k` = lattice-good first coordinate
(`ae_latticeGood_tailWalkPrefixLaw`), `G` = first coordinate continuous at `a'` with positive
endpoint (`ae_tailPrefix_continuousAt_pos`, via `tailExcLaw_map_fst`), weight convergence
`tendsto_prefixWeightFn_continuousConv` composed with `Prod.fst`; identify the limit by J01
`tailExcLaw_map_restrictPair` (`a' ≤ 1`) and `gamma_identity` at `a'`.  (d) Main theorem: take
`a' = (a + 1)/2`; by (ii) the exact pair law is the image under `restrictPair` (`a ≤ a'`) of the
weighted tail pair law, a probability measure converging weakly by (iii); `restrictPair` is
continuous at every pair whose path is continuous at `a`, a full-measure set of the limit (sealed
`levyExcLaw_noFixedJump` through J01 `excLaw_map_fst`); conclude by the a.e.-continuous mapping
theorem (`BGW.Probability.tendsto_map_of_ae_continuousAt`) and `restrictPair` composition.
Size 250-500 lines.  RISK: applying the continuous mapping theorem to the discontinuous height
functional; weighting by the walk density at the same horizon `a` (false, see the repair).

ACYCLICITY.  Sealed suppliers: K02, K03, K05b, K07 (`ExactPrefix*`), K12a, E06/E09/E10.
Contract suppliers (copied statements): K14, J01, H04.  No K16-K19, no C35.

BINDER SCOPE (AUDITOR_RULES).  In (iii) the integral body is `F z * prefixWeightFn ... z.1` (the
whole product, as intended) and nothing follows the integral; the copied J01 `gamma_identity`
is verbatim (left integral parenthesized, bodies the whole products).  `⌊(a : ℝ) * n⌋₊ + 1` is a
floor plus one, no big operator. -/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees

end BGW.StableTrees

namespace BGW.StableTrees.TailPair

open BGW.StableTrees.DiscreteForest BGW.StableTrees.PathTail

end BGW.StableTrees.TailPair

namespace BGW.StableTrees.ExactPair

open BGW.StableTrees.DiscreteForest BGW.StableTrees.PathTail BGW.StableTrees.TailPair
  BGW.StableTrees.ExactPrefix

/-! ### The exact-size pair law -/

/-- **The exact-size pair law on `[0,a]`**: the (walk, height) pair of ONE BGW tree conditioned
on size exactly `n` (sealed K02 `exactTreeLaw`, totalized), at scales `nt`, `1/B n`, `B n / n`. -/
noncomputable def exactPairLaw (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (_hn : Admissible μ n)
    (a : ℝ≥0) : ProbabilityMeasure (D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) (a : ℝ), ℝ)) :=
  (exactTreeLaw μ n).map (treePairPath B n a)

/-- The walk marginal of the exact pair law is the sealed K07 exact walk prefix law. -/
theorem exactPairLaw_map_fst {μ : PMF ℕ} {B : ℕ → ℝ} {n : ℕ} (hn : Admissible μ n) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    (exactPairLaw μ B n hn a).map Prod.fst = exactWalkPrefixLaw μ B n hn a ha.2.le := sorry

/-- The walk marginal of the target is the sealed K07 target (every `θ`). -/
theorem map_fst_restrictPair_excLaw (θ : ℝ) (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    ((excLaw θ).map (restrictPair ha.2.le)).map Prod.fst =
      (unitExcursionLaw θ).map (excursionRestrict a) := sorry

/-! ### Prefix-measurability repair -/

/-- **Projectivity** (deterministic): the pair path of horizon `a'` restricted to `[0,a]` is the
pair path of horizon `a`. -/
theorem restrictPair_treePairPath (B : ℕ → ℝ) (n : ℕ) {a a' : ℝ≥0} (h : a ≤ a')
    (τ : BGW.LocallyFinite.Tree) :
    restrictPair h (treePairPath B n a' τ) = treePairPath B n a τ := sorry

/-- **Prefix measurability of the pair** (deterministic repair): the pair on `[0,a]` reads the
walk up to index `⌊an⌋` and the heights up to index `⌊an⌋ + 1`, hence it is a function of the
first `m` DFS degrees for every `m ≥ ⌊an⌋ + 1` (in general not of the first `⌊an⌋`). -/
theorem exists_treePairPath_eq_comp_treePrefix (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0) {m : ℕ}
    (hm : ⌊(a : ℝ) * n⌋₊ + 1 ≤ m) :
    ∃ G : List ℕ → D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) (a : ℝ), ℝ),
      ∀ τ : BGW.LocallyFinite.Tree, treePairPath B n a τ = G (treePrefix m τ) := sorry

/-- **Weighted identity at a larger horizon** (the repair): for `a ≤ a' < 1` with
`⌊an⌋ + 1 ≤ ⌊a'n⌋`, the exact pair law on `[0,a]` is the `[0,a]`-restriction of the tail pair law
on `[0,a']` weighted by the sealed walk weight at `a'` (a function of the walk value at `a'`). -/
theorem exactPairLaw_eq_map_withDensity {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {n : ℕ} (hn : Admissible μ n) {a a' : ℝ≥0} (haa' : a ≤ a')
    (ha' : a' ∈ Ioo (0 : ℝ≥0) 1) (hm : ⌊(a : ℝ) * n⌋₊ + 1 ≤ ⌊(a' : ℝ) * n⌋₊) :
    ((exactPairLaw μ B n hn a :
        ProbabilityMeasure (D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) (a : ℝ), ℝ))) :
        Measure (D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) (a : ℝ), ℝ))) =
      (((tailPairLaw μ B n a' :
          ProbabilityMeasure (D (a' : ℝ) ℝ × C(Set.Icc (0 : ℝ) (a' : ℝ), ℝ))) :
          Measure (D (a' : ℝ) ℝ × C(Set.Icc (0 : ℝ) (a' : ℝ), ℝ))).withDensity
        (fun z => ENNReal.ofReal (prefixWeightFn μ B n a' z.1))).map (restrictPair haa') :=
  sorry

/-- **Weighted tail convergence at horizon `a'`** (K07's generic helper on the pair space, J01's
joint Γ identity): bounded continuous tests of the tail pair on `[0,a']`, weighted by the sealed
walk weight, converge to the tests of the excursion/height prefix on `[0,a']`. -/
theorem tendsto_integral_mul_prefixWeightFn_tailPairLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) (a' : ℝ≥0) (ha' : a' ∈ Ioo (0 : ℝ≥0) 1)
    (F : BoundedContinuousFunction (D (a' : ℝ) ℝ × C(Set.Icc (0 : ℝ) (a' : ℝ), ℝ)) ℝ) :
    Tendsto (fun k => ∫ z, F z * prefixWeightFn μ B (q k) a' z.1
        ∂(tailPairLaw μ B (q k) a' :
          Measure (D (a' : ℝ) ℝ × C(Set.Icc (0 : ℝ) (a' : ℝ), ℝ)))) atTop
      (𝓝 (∫ z, F z ∂((excLaw θ).map (restrictPair ha'.2.le) :
          Measure (D (a' : ℝ) ℝ × C(Set.Icc (0 : ℝ) (a' : ℝ), ℝ))))) := sorry

/-! ### C29, prefix part -/

/-- **Joint exact-size prefixes** (C29 prefix part): along every unbounded sequence of admissible
sizes, the (walk, height) pair of the exact-size tree on `[0,a]`, `0 < a < 1`, converges jointly
to the excursion/height prefix of `excLaw θ`. -/
theorem tendsto_exactPairLaw_prefix {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, Admissible μ (q k))
    (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    Tendsto (fun k => exactPairLaw μ B (q k) (hq k) a) atTop
      (𝓝 ((excLaw θ).map (restrictPair ha.2.le))) := sorry

end BGW.StableTrees.ExactPair
