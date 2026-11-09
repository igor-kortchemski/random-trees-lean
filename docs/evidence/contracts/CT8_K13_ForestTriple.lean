import BGW.StableTrees.DiscreteForest
import BGW.Tree.ContourBracket
import BGW.StableTrees.StableLocalLaw
import BGW.StableTrees.HeightProcess
import BGW.StableTrees.HeightBridges
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import BGW.StableTrees.HeightContinuity
import BGW.StableTrees.HeightTightness
import BGW.StableTrees.ForestContour

/-! Contract probe for CT8 node K13 (`r5-ct8-blueprint/blueprint.md` §1, §2 item 3, K13;
`CLASSICAL_THEORY_INPUTS.md` C27; `r5-ct8-blueprint/AUDIT.md` finding 8): the Duquesne-Le Gall
forest theorem, joint convergence of the rescaled walk, height and contour of the iid BGW
forest to `(X, H, H)` on every positive horizon, for every norming sequence of the stable domain.

DEFINITIONS.  K02 (sealed): `forestWalkPath B n T ω t = W_{⌊nt⌋}/B_n` in `D T ℝ` (J1),
`forestHeightPath B n T ω t = (B_n/n) H_lin(nt)` in `C([0,T], ℝ)` (uniform), `forestPairPath`,
`forestPairLaw`.  K12b (contract, copied below): the padded forest contour (`contourBlock`,
`forestContour`, `forestContourLin`), `forestContourPath B n T ω t = (B_n/n) C_lin(2nt)`, and
`forestContourHeightError`.  H03 (contract, copied below): `extendConst`, and
`heightPrefix θ T : D T ℝ → C([0,T], ℝ)`, the measurable prefix map of the common continuous
height.  New: `forestTriplePath B n T ω = (walk, height, contour)` in
`D T ℝ × C([0,T], ℝ) × C([0,T], ℝ)` (J1 × uniform × uniform), `forestTripleLaw μ B n T` its law
under `offspringSeqLaw μ`, and `forestTripleLimit θ T`, the law of
`(f|_[0,T], H, H)`, `H = heightPrefix θ T (DLoc.restrict T f)`, under `stableLocalLaw θ`.

TRUTH CHECK.  (1) Joint law: the limit is the pushforward of ONE stable path, with the same height
graph in both continuous coordinates (DLG Theorems 2.3.2, 2.4.1, Corollary 2.5.1; C27(a)); this
is a single weak convergence on the product, not marginal statements.  K11's pair limit is the
H03 graph `(X, H)`; K12b makes the contour coordinate uniformly close to the height coordinate on
the same probability space, so the triple limit duplicates `H`.  (2) Normalization: constants
exactly `1`.  The library `θ = 2` limit has Laplace exponent `λ²` (variance `2`), its height is
`X - I` (H02 `ae_height_two`, K17), and the triple limit is `(X, X - I, X - I)`; with
`B_n = σ√(n/2)` this matches `(W_{nt}/B_n, (B_n/n) H_{nt}, (B_n/n) C_{2nt})`.  (3) Scope: every
`T > 0` (K11 and K12b hold on every positive horizon), every `B` with `StableDomain μ θ B`, no
source inverse-scale hypothesis (scales `(B_n, n/B_n, n)` are used directly, as the blueprint
recommends; DLG's `p`-indexed statement is not ported).  (4) Consistency:
`forestTripleLaw_map_pair` (the first two coordinates have the sealed `forestPairLaw`) and
`forestTripleLimit_eq_map_stableProcessLaw` (the blueprint §2 form, from H03
`map_heightPrefix_pair`; first marginal `stableProcessLaw θ T`).  (5) No junk: the triple path is
measurable (K02, K12b) and the limit map is measurable (H03 `measurable_heightPrefix`,
`DLoc.restrict`); the copied junk branches (`forestContourPath`, `extendConst`, `heightPrefix`)
never occur, resp. occur on null sets (K12b, H03).  NOT EXPORTED: the form on
`D T (ℝ × ℝ × ℝ)`.  The sealed `BGW.Skorokhod.prodCont` pairs a real càdlàg path with ONE real
continuous path (`continuous_prodCont` on `D T ℝ × C([0,T], ℝ)`, values in `D T (ℝ × ℝ)`); no
continuous map `D T ℝ × C([0,T], ℝ) × C([0,T], ℝ) → D T (ℝ × ℝ × ℝ)` exists in `BGW/Skorokhod/`.
A triple form needs that map and its continuity theorem first (a separate Skorokhod node).

PROOF PLAN.  (a) K11 `tendsto_forestPairLaw` on `D T ℝ × C_T`.  (b) K12b: by
`dist_forestContourPath_forestHeightPath`, `dist (contour) (height) = forestContourHeightError`,
which tends to `0` in probability (`contour_height_error_tendstoInMeasure`).  (c) Slutsky
(sealed `BGW.Probability.tendsto_map_prodMk_of_tendsto_of_error`) with `X n = forestPairPath`,
`Y n = forestContourPath - forestHeightPath`, `c = 0` (both spaces second countable: Polish
`D T ℝ`, separable `C_T`).  (d) Continuous mapping
(`ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous`) with
`Φ ((w, h), d) = (w, h, h + d)`; `Φ` of the pair
with `0` is the triple, and `Φ_*` of the pair limit with `δ_0` is `forestTripleLimit θ T`
(`map_map`, measurability from (5)).  Size 150-300 lines.  RISK: proving only horizon `1` or a
`p`-indexed subsequence; replacing the joint law by marginals.

ACYCLICITY.  Suppliers: K02 (sealed), K11 (`tendsto_forestPairLaw`), K12b, H03 (copied
contract declarations), sealed `BGW.Probability` weak-convergence tools and Mathlib.  No
K14-K19 (K14 consumes this node).

BINDER SCOPE (AUDITOR_RULES): no integral, sum or supremum occurs in the new declarations; the
copied `forestContourHeightError` supremum has the absolute value `|a - b|` as body. 
DEFERRED (Sol audit k13k16, finding 1): the vector-path form on `D T (ℝ × ℝ × ℝ)` needs a new Skorokhod
map from `D T ℝ × C × C` with its continuity theorem; it is assigned to a separate follow-up node (K13b),
not claimed here.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees

end BGW.StableTrees

namespace BGW.StableTrees.HeightTightness

open BGW.StableTrees.DiscreteForest

end BGW.StableTrees.HeightTightness

namespace BGW.StableTrees.ForestContour

open BGW.StableTrees.DiscreteForest

end BGW.StableTrees.ForestContour

namespace BGW.StableTrees.ForestTriple

open BGW.StableTrees.DiscreteForest BGW.StableTrees.ForestContour

/-- **Forest triple path** on `[0,T]`: the walk `W_{⌊nt⌋}/B_n`, the interpolated height
`(B_n/n) H_lin(nt)` and the padded contour `(B_n/n) C_lin(2nt)`. -/
noncomputable def forestTriplePath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (ω : ℕ → ℕ) :
    D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) :=
  (forestWalkPath B n T ω, forestHeightPath B n T ω, forestContourPath B n T ω)

/-- The law of the forest triple path under the iid offspring sequence. -/
noncomputable def forestTripleLaw (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    ProbabilityMeasure
      (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) :=
  (offspringSeqLaw μ).map (forestTriplePath B n T)

/-- **The C27 limit** on `[0,T]`: the stable path restricted to `[0,T]` and its continuous
height (H03 prefix map), the height being used for both the height and contour coordinates. -/
noncomputable def forestTripleLimit (θ : ℝ) (T : ℝ≥0) :
    ProbabilityMeasure
      (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) :=
  (stableLocalLaw θ).map (fun f : DLoc =>
    (DLoc.restrict T f, heightPrefix θ T (DLoc.restrict T f),
      heightPrefix θ T (DLoc.restrict T f)))

theorem measurable_forestTriplePath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    Measurable (forestTriplePath B n T) := sorry

/-- The walk/height coordinates of the triple law form the sealed forest pair law. -/
theorem forestTripleLaw_map_pair (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    (forestTripleLaw μ B n T : Measure
        (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ))).map
        (fun x => (x.1, x.2.1)) =
      (forestPairLaw μ B n T : Measure (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ))) :=
  sorry

/-- The limit in the blueprint §2 form: the graph `g ↦ (g, H g, H g)` pushed forward by the
stable process law on `[0,T]` (all `T`). -/
theorem forestTripleLimit_eq_map_stableProcessLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) :
    (forestTripleLimit θ T : Measure
        (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ))) =
      (stableProcessLaw θ (T : ℝ) : Measure (D (T : ℝ) ℝ)).map
        (fun g => (g, heightPrefix θ T g, heightPrefix θ T g)) := sorry

/-- **C27 (Duquesne-Le Gall), every positive horizon**: the rescaled walk, interpolated height
and padded contour of the iid BGW forest converge jointly to `(X, H, H)` on `[0,T]`. -/
theorem tendsto_forestTripleLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {T : ℝ≥0} (hT : 0 < T) :
    Tendsto (fun n : ℕ => forestTripleLaw μ B n T) atTop (𝓝 (forestTripleLimit θ T)) := sorry

end BGW.StableTrees.ForestTriple
