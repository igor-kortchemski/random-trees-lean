import BGW.ContinuumTrees.BrownianBridgeMinimum
import BGW.ContinuumTrees.BrownianBridgeGrid
import BGW.ContinuumTrees.VervaatBridge

/-! Contract probe for CT.C19 pilot / roadmap C3: unique minimum of the Brownian bridge and
strict positivity of its Vervaat transform. Maintained file:
`BGW/ContinuumTrees/BrownianBridgeUniqueMinimum.lean`. -/

open MeasureTheory ProbabilityTheory

namespace BGW.ContinuumTrees.BrownianBridge

/-- Almost surely, the Brownian bridge attains its global minimum at exactly one time. -/
theorem ae_existsUnique_isMin :
    ∀ᵐ f ∂(law : Measure C(unitInterval, ℝ)), ∃! t : unitInterval, ∀ s, f t ≤ f s := sorry

/-- Almost surely, the first (hence unique) minimum time lies in the open interval `(0,1)`. -/
theorem ae_firstMinimum_mem_Ioo :
    ∀ᵐ f ∂(law : Measure C(unitInterval, ℝ)),
      0 < (Vervaat.firstMinimum f : ℝ) ∧ (Vervaat.firstMinimum f : ℝ) < 1 := sorry

end BrownianBridge

namespace VervaatBridge

/-- Almost surely, the Vervaat transform of the anchored bridge is strictly positive on `(0,1)`. -/
theorem ae_path_pos :
    ∀ᵐ ω ∂gaussianLimit, ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < path ω t := sorry

/-- The Vervaat path law is carried by paths strictly positive on `(0,1)`. -/
theorem ae_law_pos :
    ∀ᵐ f ∂(law : Measure C(unitInterval, ℝ)),
      ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < f t := sorry

end BGW.ContinuumTrees.VervaatBridge
