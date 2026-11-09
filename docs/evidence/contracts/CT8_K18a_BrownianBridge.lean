import BGW.StableTrees.StableBridgeClosed
import BGW.StableTrees.StableProcessBrownian
import BGW.StableTrees.BridgePrefix
import BGW.ContinuumTrees.BrownianD

/-! Contract probe for CT8 node K18a (`r5-ct8-blueprint/blueprint.md` K18, first export): at
`θ = 2` the stable bridge law is the law of `√2` times the standard Brownian bridge.

NORMALIZATION.  The library's `θ = 2` stable law has Laplace transform `exp(λ²)`, i.e. it is
centered Gaussian of variance `2` (sealed `stableLaw_two : stableLaw 2 = gaussianReal 0 2`), and
`stableProcessLaw_two : stableProcessLaw 2 T = BrownianD.wienerD (√2) T`.  Hence the density at
time `t` is the Gaussian density of variance `2t = (√2)² t = BrownianD.variance (√2) t`, and the
bridge is `√2` times the standard bridge (`BrownianD.bridgeD (√2)`).

TRUTH CHECK.  `Scalar.stableDensity 2` is defined by Fourier inversion of
`exp(-(i t)^2) = exp(-t²)`, the characteristic function of `N(0,2)`; both it and
`gaussianPDFReal 0 2` are continuous, so they agree everywhere (not only a.e.).
`bridgePrefixWeight 2 a ha f = p_{2(1-a)}(-f(a)) / p_2(0)`, which is
`BrownianD.prefixDensity (√2) a (f(a))` by definition of the latter.  The two bridges have the
same prefix laws on every `[0,a]`, `a < 1` (sealed `map_restrict_stableBridgeLaw` and
`BrownianD.map_restrict_bridgeD_eq_withDensity`), and `bridgeD` is continuous and pinned at
`1`, so `stableBridgeLaw_unique_of_endpoints` identifies them.

PROOF PLAN.  (1) `stableDensity_two` from `stableLaw_two`, continuity of both functions and
uniqueness of continuous densities (or directly by the Gaussian Fourier integral).  (2) Scaling
gives `stableDensityAt_two`.  (3) `bridgePrefixWeight_two` by unfolding.  (4) Apply
`stableBridgeLaw_unique_of_endpoints` with `Q = bridgeD (√2)`.  Size 150-400 lines.

ACYCLICITY.  Suppliers: sealed CT5/C15 stable laws and `BrownianD`.  No CT8 node.

BINDER SCOPE (AUDITOR_RULES): no integral or big operator appears in the statements. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace BGW.StableTrees.BrownianIdentification

open BGW.Skorokhod

/-- The `θ = 2` stable density is the centered Gaussian density of variance `2`. -/
theorem stableDensity_two (x : ℝ) : Scalar.stableDensity 2 x = gaussianPDFReal 0 2 x := sorry

/-- At time `t > 0`, the `θ = 2` stable density is the density of `√2 B_t`. -/
theorem stableDensityAt_two {t : ℝ} (ht : 0 < t) (x : ℝ) :
    stableDensityAt 2 t x =
      gaussianPDFReal 0 (BGW.ContinuumTrees.BrownianD.variance (NNReal.sqrt 2) t) x := sorry

/-- The `θ = 2` bridge prefix weight is the Brownian bridge prefix density with `c = √2`. -/
theorem bridgePrefixWeight_two {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (f : D a ℝ) :
    bridgePrefixWeight 2 a ha f =
      BGW.ContinuumTrees.BrownianD.prefixDensity (NNReal.sqrt 2) a (f ⟨a, ha, le_rfl⟩) := sorry

/-- **K18a.**  The `θ = 2` stable bridge is `√2` times the standard Brownian bridge. -/
theorem stableBridgeLaw_two :
    stableBridgeLaw 2 = BGW.ContinuumTrees.BrownianD.bridgeD (NNReal.sqrt 2) := sorry

end BGW.StableTrees.BrownianIdentification
