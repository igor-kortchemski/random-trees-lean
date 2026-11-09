import BGW.StableTrees.ExactContour
import BGW.StableTrees.JointExcursion
import BGW.StableTrees.Scalar.FiniteVariance
import BGW.StableTrees.BrownianExcursion
import BGW.ContinuumTrees.VervaatBridge
import BGW.ContinuumTrees.CodingScaling
import BGW.MetricMeasure.RootedScaling

/-! Contract probe for CT8 node K19 = C30 (`r5-ct8-blueprint/blueprint.md` K19;
`sol-audit-k13k16/AUDIT.md` finding 3; `CLASSICAL_THEORY_INPUTS.md` C30; roadmap §8.4 CT8):
the finite-variance normalization of the exact-size contour theorem, Aldous's form
`(σ/(2√n)) C_{2nt} ⇒ e`, jointly with the height, and the deterministic Brownian CRT scaling
`T_{√2 e} = (1/√2) T_{2e}` with unchanged mass.  Suggested maintained module:
`BGW/StableTrees/FiniteVarianceContour.lean` (contour part in `BGW.StableTrees.ExactContour`,
tree-law part in `BGW.StableTrees.BrownianIdentification`).

DEFINITIONS (all sealed; nothing new is defined here).
* `σ := √(∫ z, z² ∂stepLaw μ)`, where `stepLaw μ` is the law of `K - 1` for `K ~ μ`; for a
  critical `μ` this is the offspring standard deviation.  It is introduced by `let`, exactly as
  in AUDIT finding 3, and is positive under the hypotheses (`hne`, finite second moment).
  Lean prints this binder as `have σ := …`; each statement is definitionally its zeta-reduced
  form (a probe closed the `let`-form goal `StableDomain μ 2 (fun n => (σ/√2) * √n)` by
  `exact Scalar.stableDomain_of_finiteVariance hc hne hfinite`).
* K16 paths and laws: `treeContourPath B n T τ = (t ↦ (B n / n) C_τ(2nt))`, where `C_τ` is the
  polygonal contour at original speed, `0` after time `2(z-1)` (and `0` on infinite trees);
  `heightContourPath B n τ` pairs it with the height `t ↦ (B n / n) H_τ(nt)` of the SAME tree.
  `exactHeightContourLaw μ B n hn` and `exactHeightLibContourLaw μ B n hn` are their laws under
  the sealed K02 `exactTreeLaw μ n`, the BGW tree conditioned on size exactly `n`.
* Norming in the C30 statements: `B n = (σ / 2) * √n`, so the amplitude at size `n ≥ 1` is
  `B n / n = σ / (2√n)` (`finiteVarianceNorming_div`).  `hq k` excludes size `0`.
* `VervaatBridge.law` is the law of `e`; `VervaatBridge.treeLaw` is the law of `T_{2e}`, the
  rooted measured isometry class coded by `2 • e` (sealed `treeLaw_eq_map`);
  `Coding.rootedMeasuredGHSpace g` is `T_g` (root at time `0`, Lebesgue-pushforward mass);
  `RootedMeasuredGHSpace.scale c hc` multiplies distances by `c` and keeps root and mass.

CLOCK CONVENTION.  C30 cites `C_{2ζt}` (time `2ζ` for `ζ` vertices): the paper clock.  For a
tree of size `n` the K16 path is exactly `(B n / n) * PlaneTree.paperContourFunction` (sealed
`treeContourPath_eq_paperContourFunction`), the main convention below
(`tendsto_exactContour_finiteVariance`, `tendsto_exactHeightContour_finiteVariance`).  The
library clock `PlaneTree.contourFunction` (`s ↦ C(2(z-1)s)`) has the same limit
(`tendsto_exactHeightLibContour_finiteVariance`).

TRUTH CHECK (normalizations).
(1) Library `θ = 2`: Laplace exponent `λ²`, i.e. `√2 B`, variance `2`.  Sealed
    `Scalar.stableDomain_of_finiteVariance`: `StableDomain μ 2 B₀` with
    `B₀ n = (σ / √2) √n = σ √(n/2)`.  Check: `S_n / (σ√n) ⇒ N(0,1)` (CLT), so
    `S_n / B₀ n ⇒ N(0,2)`, whose Laplace transform `E exp(-λY) = exp λ²` is the required one.
    The Aldous norming `B = (σ/2)√n` is NOT a `StableDomain` norming (limit `N(0,4)`), so it
    enters only through the deterministic identity `B = (1/√2) B₀` (`finiteVarianceNorming_eq`).
(2) K16 at `θ = 2` with `B₀`, and K18c `excLaw_two_map_diag`:
    `(B₀ n / n)(H_{nt}, C_{2nt}) ⇒ (√2 e, √2 e)`
    (`tendsto_exactHeightContour_finiteVariance_stable`; here `B₀ n / n = σ / √(2n)`).
(3) `B n / n = (1/√2) B₀ n / n = σ/(2√n)`, hence `(σ/(2√n))(H_{nt}, C_{2nt}) ⇒ (e, e)` and
    `(σ/(2√n)) C_{2nt} ⇒ e` (Aldous; C30(a) with `ζ = n`).  Sanity check: `E sup e = √(π/2)`,
    so the height of the size-`n` tree is about `(2/σ) √n √(π/2) = √(2πn)/σ`, the classical
    value; the multiplier `σ/√n` would instead give the limit `2e`.
(4) CRT.  `VervaatBridge.treeLaw` codes `2e`.  For every path `e`, `T_{√2 e} = (1/√2) T_{2e}`
    (`rootedMeasuredGHSpace_sqrt_two_smul`: `(1/√2) · 2 = √2` and the sealed measured isometry
    `Coding.rootedMeasuredGHSpace_smul`, which keeps the probability mass UNCHANGED).  With
    `H^exc = √2 e` in law (K18c) the `θ = 2` height-coded tree law is `(1/√2) T_{2e}`
    (`stableTreeLaw_two`).  Graph distances times `σ/√n` give the library `T_{2e}`, times
    `σ/(2√n)` give `T_e`, times `B₀ n / n` give `T_{√2 e}` (CT9 transfers, not redone here).
(5) Scope.  Every unbounded admissible `q` (periodic offspring laws included, through K16);
    height and contour only, no walk coordinate.  Not claimed: mass scaled with distances, or
    any leaf-conditioned theorem.  Remark 4.6 uses a random size `ζ`; this node exports only
    the deterministic coefficient `σ/(2√z)` for every size `z` (`finiteVarianceNorming_div`,
    `treeContourPath_finiteVariance_paper`).  `hpos` is a hypothesis exactly as in the
    blueprint and is proof-irrelevant.

PROOF PLAN (size 250-500 lines).
(a) Deterministic: `treeContourPath_const_mul`, `heightContourPath_const_mul` (unfold, take the
    `dite` branch with `continuous_treeContourLin` / `continuous_treeHeightLin`,
    `ContinuousMap.ext`, `ring`; `n = 0` is harmless since `B 0 / 0 = 0`);
    `finiteVarianceNorming_eq`, `finiteVarianceNorming_div` (`Real.mul_self_sqrt`, `√z > 0`);
    `treeContourPath_finiteVariance_paper` from `treeContourPath_eq_paperContourFunction` at
    `n = t.size` (`PlaneTree.size_pos`).
(b) Stable form: `stableDomain_of_finiteVariance`, K16 `tendsto_exactHeightContourLaw`, and K18c
    `excLaw_two_map_diag`.
(c) Aldous joint form: by (a), `exactHeightContourLaw μ B n hn =
    (exactHeightContourLaw μ B₀ n hn).map ((1/√2) • ·)` (`Measure.map_map`); the continuous
    mapping theorem `ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous`; the limit
    `(law.map (√2 •, √2 •)).map ((1/√2) • ·) = law.map (fun e => (e, e))` by `smul_smul`.
(d) Contour only: push (c) forward by the continuous `Prod.snd`;
    `(heightContourPath B n τ).2 = treeContourPath B n 1 τ` by definition.
(e) Library clock: `heightLibContourPath (fun m => c * B m) n = c • heightLibContourPath B n`, K16
    `tendsto_exactHeightLibContourLaw` at `B₀`, or the deterministic bound
    `abs_treeContourPath_sub_contourFunction_le` (`≤ 2|B n / n| = σ/√n → 0`) with
    `BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability`, as in K16.
(f) `rootedMeasuredGHSpace_sqrt_two_smul`: `rootedMeasuredGHSpace_smul (2 • e) (1/√2) hpos`.
(g) `stableTreeLaw_two`: `Measure.map_map` through `Prod.snd`, K18c `excLaw_two_map_snd`, (f)
    pointwise, `treeLaw_eq_map`; measurability from `continuous_rootedMeasuredGHSpace`,
    `measurable_scale`.
RISK: `T_e` versus `T_{2e}`; scaling mass with distances; using the Aldous norming in a
`StableDomain` hypothesis.

ACYCLICITY.  Sealed suppliers: K16 = C29 (`ExactContour`), J01 (`excLaw`), K02
(`exactTreeLaw`), `Scalar.FiniteVariance`, `ContinuumTrees.VervaatBridge`, `CodingScaling`,
`MetricMeasure.RootedScaling`, K18b.  Contract supplier: K18c (`excLaw_two_map_snd`,
`excLaw_two_map_diag`), used only in proofs; no statement here mentions a K18c name, so there
is no copied block and the maintained file imports K18c's module once it is sealed.  Nothing
here feeds K16, K18 or CT9's transfers.

BINDER SCOPE (AUDITOR_RULES).  The only integral is `∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ`, enclosed
in `Real.sqrt (…)`: its body is `(z : ℝ) ^ 2` and nothing follows it.  Normings are written
with explicit parentheses, `(σ / 2) * Real.sqrt n`, `(σ / Real.sqrt 2) * Real.sqrt n`, and the
coefficient as `σ / (2 * Real.sqrt z)`. -/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace BGW.StableTrees.ExactContour

open BGW.StableTrees.DiscreteForest BGW.StableTrees.TailPair

/-! ### Deterministic norming identities -/

/-- The contour path is linear in the norming sequence. -/
theorem treeContourPath_const_mul (c : ℝ) (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0)
    (τ : LocallyFinite.Tree) :
    treeContourPath (fun m => c * B m) n T τ = c • treeContourPath B n T τ := sorry

/-- The height/contour pair is linear in the norming sequence. -/
theorem heightContourPath_const_mul (c : ℝ) (B : ℕ → ℝ) (n : ℕ) (τ : LocallyFinite.Tree) :
    heightContourPath (fun m => c * B m) n τ = c • heightContourPath B n τ := sorry

/-- The Aldous norming `(σ/2)√n` is `1/√2` times the stable norming `(σ/√2)√n` of
`Scalar.stableDomain_of_finiteVariance`. -/
theorem finiteVarianceNorming_eq (σ : ℝ) :
    (fun n : ℕ => (σ / 2) * Real.sqrt n) =
      fun n : ℕ => (1 / Real.sqrt 2) * ((σ / Real.sqrt 2) * Real.sqrt n) := sorry

/-- **Coefficient identity for every positive size `z`** (deterministic, so usable with a
random size): the Aldous amplitude is `σ / (2√z)`. -/
theorem finiteVarianceNorming_div (σ : ℝ) {z : ℕ} (hz : 0 < z) :
    (σ / 2) * Real.sqrt z / z = σ / (2 * Real.sqrt z) := sorry

/-- For one finite tree of any size `z = t.size`, the Aldous-normed contour path is
`σ / (2√z)` times the sealed paper contour `PlaneTree.paperContourFunction` (`s ↦ C_{2z s}`). -/
theorem treeContourPath_finiteVariance_paper (σ : ℝ) (t : PlaneTree) (s : unitInterval) :
    treeContourPath (fun n => (σ / 2) * Real.sqrt n) t.size 1 t.toLocallyFinite s =
      σ / (2 * Real.sqrt t.size) * t.paperContourFunction s := sorry

/-! ### C30: finite-variance exact-size contours -/

/-- **C30, stable normalization** `B₀ n = σ √(n/2)`: the exact-size height and contour converge
jointly to `(√2 e, √2 e)`. -/
theorem tendsto_exactHeightContour_finiteVariance_stable {μ : PMF ℕ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hfinite : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) :
    let σ := Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ)
    Tendsto (fun k => exactHeightContourLaw μ (fun n => (σ / Real.sqrt 2) * Real.sqrt n)
        (q k) (hq k)) atTop
      (𝓝 (BGW.ContinuumTrees.VervaatBridge.law.map
        (fun e => (Real.sqrt 2 • e, Real.sqrt 2 • e)))) := sorry

/-- **C30, Aldous normalization, joint form**: with amplitude `σ / (2√n)`, the exact-size
height (time `nt`) and contour (time `2nt`) converge jointly to `(e, e)`. -/
theorem tendsto_exactHeightContour_finiteVariance {μ : PMF ℕ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hfinite : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) :
    let σ := Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ)
    Tendsto (fun k => exactHeightContourLaw μ (fun n => (σ / 2) * Real.sqrt n) (q k) (hq k))
      atTop (𝓝 (BGW.ContinuumTrees.VervaatBridge.law.map (fun e => (e, e)))) := sorry

/-- **C30 (Aldous's theorem along admissible sizes)**: `(σ / (2√n)) C_{2nt} ⇒ e`, the normalized
Brownian excursion. -/
theorem tendsto_exactContour_finiteVariance {μ : PMF ℕ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hfinite : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) :
    let σ := Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ)
    Tendsto (fun k => (exactTreeLaw μ (q k)).map
      (treeContourPath (fun n => (σ / 2) * Real.sqrt n) (q k) 1))
      atTop (𝓝 BGW.ContinuumTrees.VervaatBridge.law) := sorry

/-- **C30 in the library contour clock** (`s ↦ C(2(z-1)s)`): the same joint limit `(e, e)`. -/
theorem tendsto_exactHeightLibContour_finiteVariance {μ : PMF ℕ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hfinite : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) :
    let σ := Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ)
    Tendsto (fun k => exactHeightLibContourLaw μ (fun n => (σ / 2) * Real.sqrt n) (q k) (hq k))
      atTop (𝓝 (BGW.ContinuumTrees.VervaatBridge.law.map (fun e => (e, e)))) := sorry

end BGW.StableTrees.ExactContour

namespace BGW.StableTrees.BrownianIdentification

/-! ### Deterministic CRT scaling and the `θ = 2` tree law -/

/-- **Deterministic CRT scaling** `T_{√2 e} = (1/√2) T_{2e}`: spatial scaling by `1/√2`, with
unchanged root and probability mass. -/
theorem rootedMeasuredGHSpace_sqrt_two_smul (hpos : 0 < 1 / Real.sqrt 2)
    (e : C(unitInterval, ℝ)) :
    BGW.ContinuumTrees.Coding.rootedMeasuredGHSpace (Real.sqrt 2 • e) =
      BGW.MetricMeasure.RootedMeasuredGHSpace.scale (1 / Real.sqrt 2) hpos
        (BGW.ContinuumTrees.Coding.rootedMeasuredGHSpace ((2 : ℝ) • e)) := sorry

/-- **The `θ = 2` height-coded tree law**: the tree coded by the excursion height `H^exc` has the
law of Aldous's CRT `T_{2e}` with distances multiplied by `1/√2`. -/
theorem stableTreeLaw_two (hpos : 0 < 1 / Real.sqrt 2) :
    (excLaw 2).map
      (fun p => BGW.ContinuumTrees.Coding.rootedMeasuredGHSpace p.2) =
    BGW.ContinuumTrees.VervaatBridge.treeLaw.map
      (BGW.MetricMeasure.RootedMeasuredGHSpace.scale
        (1 / Real.sqrt 2) hpos) := sorry

end BGW.StableTrees.BrownianIdentification
