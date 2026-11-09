import BGW.StableTrees.HeightProcess
import BGW.StableTrees.StableFirstPassagePath
import BGW.StableTrees.StableProcessBrownian
import BGW.StableTrees.ExcursionMeasure
import BGW.StableTrees.UnitExcursionLaw
import BGW.ContinuumTrees.ExcursionCarrier
import BGW.StableTrees.HeightBridges
import BGW.StableTrees.HeightContinuity

/-! Contract probe for CT8 node K17 = C26 (`r5-ct8-blueprint/blueprint.md` K17): at `θ = 2` the
common continuous height of H03 is the reflected process `X - I`, simultaneously for all times.

NORMALIZATION.  The library's `θ = 2` process has Laplace exponent `λ²` (variance `2`,
`stableProcessLaw_two`: `√2` times Brownian motion).  For a driftless Brownian process of variance
rate `v`, `ψ(λ) = (v/2) λ²` and `H = (2/v)(X - I)`; here `v = 2`, so the factor is `1`.  The
offspring variance enters the norming `B_n`, not this identity.

TRUTH CHECK.  H02 `ae_height_two t`: for each fixed `t`, `height 2 f t = f t - futureInf f t 0`
a.s., and `futureInf f t 0 = runningInfLoc f t` (both are `inf_{u ≤ t} f u`).  H03
`ae_heightLoc_eq_height`: `heightLoc 2 f t = height 2 f t` a.s. for each `t`.  Intersect over
rational `t`.  Both sides are continuous a.s.: `heightLoc` by construction, and `X` is continuous
a.s. at `θ = 2` (`ae_mem_range_ofContinuous_stableProcessLaw_two`), hence so is its running
infimum.  Two continuous functions agreeing on the rationals agree everywhere.

PROOF PLAN.  (1) `futureInf_zero_eq_runningInfLoc` (deterministic).  (2) Rational-time a.s.
agreement.  (3) A.s. continuity of `t ↦ f t - runningInfLoc f t` at `θ = 2` on every horizon
(continuity of the path from the Brownian identification on `[0, n]`, all `n`).  (4) Density of the
rationals.  Size 150-400 lines.

ACYCLICITY.  Suppliers: H02, H02b, H03, CT5/CT6 Brownian identification.  No other CT8 node.

BINDER SCOPE (AUDITOR_RULES): the infima are applied to the whole `f.1 u`; nothing follows them. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees

/-- The future infimum from time `0` is the running infimum. -/
theorem futureInf_zero_eq_runningInfLoc (f : DLoc) (t : ℝ≥0) :
    futureInf f t 0 = runningInfLoc f t := sorry

/-- **C26 (K17).**  At `θ = 2`, almost surely, the continuous height is `X - I` at every time. -/
theorem ae_heightLoc_two :
    ∀ᵐ f ∂(stableLocalLaw 2 : Measure DLoc), ∀ t : ℝ≥0,
      heightLoc 2 f t = f.1 t - runningInfLoc f t := sorry

end BGW.StableTrees
