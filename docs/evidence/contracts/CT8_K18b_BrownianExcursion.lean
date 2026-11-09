import BGW.StableTrees.VervaatIto
import BGW.StableTrees.BrownianIdentification
import BGW.ContinuumTrees.VervaatBridge
import BGW.Skorokhod.VervaatComparison

/-! Contract probe for CT8 node K18b (`r5-ct8-blueprint/blueprint.md` K18, second export): at
`θ = 2` the normalized Itô excursion of the library (`levyExcLaw 2`) is the law of `√2` times the
Brownian excursion constructed as the Vervaat transform of the Brownian bridge
(`ContinuumTrees.VervaatBridge.law`).

TRUTH CHECK.  C35 (sealed K08, `map_vervaatD_stableBridgeLaw`): `levyExcLaw θ` is the image of
`stableBridgeLaw θ` by the càdlàg Vervaat map `vervaatD`.  K18a (sealed,
`stableBridgeLaw_two`): `stableBridgeLaw 2 = BrownianD.bridgeD (√2)`, the image of the standard
Brownian bridge law by `g ↦ ofContinuous (√2 • g)`.  For a continuous loop, `vervaatD` agrees with
the continuous Vervaat transform (sealed `vervaatD_ofContinuous`), and positive scaling commutes
with the continuous Vervaat transform: the first minimum of `c • g` is the first minimum of `g`
for `c > 0`, and the circular shift and the subtraction of the minimum are linear
(`vervaat_smul`).  The Brownian bridge is a loop (`path_zero`, `path_one`), and
`VervaatBridge.law` is the image of the Brownian bridge law by the continuous Vervaat transform.
Normalization: the library's `θ = 2` process has variance `2` (`√2` times Brownian motion), so
the factor is `√2`, not `1` or `2`.

PROOF PLAN.  (1) `vervaat_smul` from the definitions of `firstMinimum`, the circular shift and
`intervalMin` in `ContinuumTrees.Vervaat`/`Coding`.  (2) `levyExcLaw_two`: rewrite with C35 and
K18a, compose the pushforwards (`Measure.map_map`), use `vervaatD_ofContinuous` on the loop
`√2 • g`, then `vervaat_smul`, and identify the result with the image of `VervaatBridge.law`.
Size 100-250 lines.

ACYCLICITY.  Suppliers: K08 (C35), K18a, `ContinuumTrees.VervaatBridge`, `Skorokhod.Vervaat*`.

BINDER SCOPE (AUDITOR_RULES): no integral or big operator appears in the statements. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace BGW.StableTrees.BrownianIdentification

open BGW.Skorokhod

/-- Positive scaling commutes with the continuous-loop Vervaat transform. -/
theorem vervaat_smul {c : ℝ} (hc : 0 < c) (g : {g : C(unitInterval, ℝ) // g 0 = g 1}) :
    BGW.ContinuumTrees.Vervaat.vervaat
        ⟨c • g.1, by simp only [ContinuousMap.smul_apply, g.2]⟩ =
      c • BGW.ContinuumTrees.Vervaat.vervaat g := sorry

/-- **K18b.**  At `θ = 2` the normalized Itô excursion is `√2` times the Brownian excursion
(Vervaat transform of the Brownian bridge). -/
theorem levyExcLaw_two :
    (levyExcLaw 2 : Measure (D 1 ℝ)) =
      (BGW.ContinuumTrees.VervaatBridge.law : Measure C(unitInterval, ℝ)).map
        (fun e => ofContinuous (T := 1) (Real.sqrt 2 • e)) := sorry

end BGW.StableTrees.BrownianIdentification
