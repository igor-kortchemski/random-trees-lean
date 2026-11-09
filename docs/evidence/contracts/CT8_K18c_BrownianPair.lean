import BGW.StableTrees.BrownianExcursion
import BGW.StableTrees.JointExcursion
import BGW.StableTrees.ExcursionHeightTwo
import BGW.ContinuumTrees.BrownianD
import BGW.Skorokhod.ContinuousEmbedding

/-! Contract probe for CT8 node K18c (`r5-ct8-blueprint/blueprint.md` K18, third export
`excLaw_two`; `sol-audit-k13k16/AUDIT.md` finding 3; `CLASSICAL_THEORY_INPUTS.md` C30(a)): at
`θ = 2` the JOINT law of the normalized excursion and of its height is the law of the pair
`(√2 e, √2 e)` for ONE Brownian excursion `e`, the Vervaat transform of the standard Brownian
bridge (`ContinuumTrees.VervaatBridge.law`).  Suggested maintained module:
`BGW/StableTrees/BrownianPair.lean`, namespace `BGW.StableTrees.BrownianIdentification`.

DEFINITIONS (all sealed; nothing new is defined here).
* J01 `excLaw θ : ProbabilityMeasure (D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ))`: the image of the
  normalized excursion law `unitExcursionLaw θ` by `excursionPair θ 1`, i.e. the càdlàg path
  restricted to `[0,1]` and the H04 height `excursionHeight θ e` of the SAME excursion.
* `VervaatBridge.law : ProbabilityMeasure C(unitInterval, ℝ)`: the law of the Vervaat transform
  of the anchored standard Brownian bridge.  Mathlib's `unitInterval` is a reducible
  abbreviation of `Set.Icc (0 : ℝ) 1`, so `C(unitInterval, ℝ)` IS the J01 height carrier: no
  transport map is needed.  `ofContinuous (T := 1)` views a continuous path as a càdlàg path.
* The pair map `e ↦ (ofContinuous (√2 • e), √2 • e)` is measurable (`measurable_sqrtTwoPair`),
  so the image law is not a junk pushforward.

TRUTH CHECK (normalizations).
(1) The library `θ = 2` process has Laplace exponent `ψ(λ) = λ²`: it is `√2` times a standard
    Brownian motion, of variance `2` at time `1` (sealed `stableProcessLaw_two`, K18a
    `stableBridgeLaw_two : stableBridgeLaw 2 = bridgeD (√2)`).  Hence its normalized excursion
    is `√2 e` (sealed K18b `levyExcLaw_two`): the factor is `√2`, not `1` or `2`.
(2) For `ψ(λ) = (v/2) λ²` the height is `H = (2/v)(X - I)`; at `v = 2` the factor is `1`, so the
    excursion height EQUALS the excursion path at all times simultaneously, almost surely
    (sealed J01 `excLaw_height_eq_path_two`, from H04 `ae_excursionHeight_two_unit` and K17).
    No `2/σ²` factor: the offspring variance only enters the discrete normings (K19).
(3) Hence `(X^exc, H^exc) = (√2 e, √2 e)` JOINTLY: the height is the same path seen in `C`,
    not an independent copy.  First marginal: `levyExcLaw 2` (K18b, through `excLaw_map_fst`).
    Second marginal: `law.map (√2 • ·)` (`excLaw_two_map_snd`; C30(a) `H^exc = √2 e`).
    Diagonal: `excLaw_two_map_diag` is the K16 (C29) limit `(excLaw 2).map (p ↦ (p.2, p.2))`
    at `θ = 2`.  Numerically `p_1(0) = 1/(2√π)` and `N(ζ > 1) = 1/√π` at `θ = 2` (blueprint).
(4) Itô remark (blueprint K18).  `levyExcLaw 2` is the variance-2 Itô excursion measure
    conditioned on unit lifetime.  For `X = cB` (`c = √2`) the excursions of `X` are `c` times
    those of `B`, with the same lifetimes; since local time is `-I`, the excursion intensities
    satisfy `N_{cB} = c⁻¹ (amplitude c)_* N_B`, and the scalar `c⁻¹` cancels on conditioning
    to unit lifetime.  So `levyExcLaw 2 = law.map (√2 • ·)` is the statement that the
    normalized Itô excursion of standard Brownian motion is the Vervaat image of the bridge
    (C30 characterizations (i) = (ii), C35 at `θ = 2`).  A separately constructed
    standard-Brownian Itô measure is NOT claimed here; the Bessel(3) characterization (iii)
    is not used (roadmap CT10: alternative characterizations are proof-route choices).
(5) These are equalities of LAWS on one carrier, not of random variables living on different
    probability spaces (blueprint flag 6).

PROOF PLAN (size 80-200 lines).
(a) `measurable_sqrtTwoPair`: `measurable_ofContinuous` composed with the continuous map
    `e ↦ √2 • e`, and `Measurable.prodMk`.
(b) From `excLaw_height_eq_path_two` and `D.ext`: almost surely under `excLaw 2`, `z = F z.2`
    with `F g = (ofContinuous g, g)`.  Hence `excLaw 2 = ((excLaw 2).map Prod.snd).map F` and
    `(excLaw 2).map Prod.fst = ((excLaw 2).map Prod.snd).map ofContinuous`
    (`Measure.map_congr_ae`, `Measure.map_map`).
(c) `excLaw_map_fst` and K18b `levyExcLaw_two` give
    `((excLaw 2).map Prod.snd).map ofContinuous = (law.map (√2 • ·)).map ofContinuous`.
    `ofContinuous` is a closed embedding (`isClosedEmbedding_ofContinuous`) between Borel spaces,
    hence a `MeasurableEmbedding`, and pushforward along it is injective: `excLaw_two_map_snd`.
(d) `excLaw_two`: `(law.map (√2 • ·)).map F = law.map (F ∘ (√2 • ·))` (`Measure.map_map`).
(e) `excLaw_two_map_diag`: push `excLaw_two` forward by `p ↦ (p.2, p.2)` and compose.
RISK: pairing `levyExcLaw_two` with an independent height sample.  Only J01's simultaneous
almost-sure diagonal support pins the coupling.

ACYCLICITY.  Sealed suppliers only: K18b (`levyExcLaw_two`; itself from K08 = C35 and K18a),
J01 (`excLaw`, `excLaw_map_fst`, `excLaw_height_eq_path_two`; built on H04 and K17), Skorokhod
(`ofContinuous`, `measurable_ofContinuous`, `isClosedEmbedding_ofContinuous`) and
`ContinuumTrees.VervaatBridge`.  No K16 or K19 input; K19 consumes this node.

BINDER SCOPE (AUDITOR_RULES).  No integral, sum or supremum occurs in these statements; every
scalar action `Real.sqrt 2 • e` acts on a single function argument. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace BGW.StableTrees.BrownianIdentification

open BGW.Skorokhod

/-- Measurability guard: the pair map `e ↦ (√2 e, √2 e)`, with the first coordinate seen as a
càdlàg path, is measurable (so the image law in `excLaw_two` is not a junk pushforward). -/
theorem measurable_sqrtTwoPair :
    Measurable (fun e : C(unitInterval, ℝ) =>
      (ofContinuous (T := 1) (Real.sqrt 2 • e), Real.sqrt 2 • e)) := sorry

/-- **K18c.**  At `θ = 2` the normalized excursion/height pair has the law of `(√2 e, √2 e)` for
one Brownian excursion `e` (Vervaat transform of the Brownian bridge). -/
theorem excLaw_two :
    excLaw 2 = BGW.ContinuumTrees.VervaatBridge.law.map
      (fun e => (BGW.Skorokhod.ofContinuous (T := 1) (Real.sqrt 2 • e),
        Real.sqrt 2 • e)) := sorry

/-- Height marginal at `θ = 2` (C30(a)): the excursion height has the law of `√2 e`. -/
theorem excLaw_two_map_snd :
    (excLaw 2).map Prod.snd =
      BGW.ContinuumTrees.VervaatBridge.law.map (fun e => Real.sqrt 2 • e) := sorry

/-- The C29 (K16) limit at `θ = 2`: the duplicated excursion height has the law of
`(√2 e, √2 e)`. -/
theorem excLaw_two_map_diag :
    (excLaw 2).map (fun p => (p.2, p.2)) =
      BGW.ContinuumTrees.VervaatBridge.law.map
        (fun e => (Real.sqrt 2 • e, Real.sqrt 2 • e)) := sorry

end BGW.StableTrees.BrownianIdentification
