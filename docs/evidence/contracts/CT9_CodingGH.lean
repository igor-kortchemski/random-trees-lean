import BGW.ContinuumTrees.CodingStability
import BGW.MetricMeasure.GHPUnderlyingProjection
import BGW.MetricMeasure.RootedMeasuredGHSpace

/-! Contract probe for CT.C37 items 4–5 (CT9): the Gromov–Hausdorff constant 2 for trees coded
by continuous functions, and the composed forgetful map. Maintained file:
`BGW/ContinuumTrees/CodingGH.lean`. -/

open BGW.MetricMeasure

namespace BGW.ContinuumTrees.Coding

/-- The Gromov–Hausdorff distance between the trees coded by `g` and `h` is at most
`2 ‖g - h‖` (Le Gall 2005, Lemma 2.4; Duquesne–Le Gall 2005, Lemma 2.3) (C37.4). -/
theorem ghDist_le_two_mul_norm (g h : C(unitInterval, ℝ)) :
    GromovHausdorff.ghDist (Space g) (Space h) ≤ 2 * ‖g - h‖ := sorry

/-- The Gromov–Hausdorff class of the coded tree is a 2-Lipschitz function of the coding
function (C37.4). -/
theorem lipschitzWith_two_toGHSpace :
    LipschitzWith 2 (fun g : C(unitInterval, ℝ) => GromovHausdorff.toGHSpace (Space g)) := sorry

end BGW.ContinuumTrees.Coding

namespace BGW.MetricMeasure.RootedMeasuredGHSpace

/-- Forgetting the root and the measure is 1-Lipschitz from rooted measured GHP to GH (C37.5). -/
theorem lipschitzWith_underlyingGH_forgetRoot :
    LipschitzWith 1 (MeasuredGHSpace.underlyingGH.{u} ∘ forgetRoot.{u}) := sorry

end BGW.MetricMeasure.RootedMeasuredGHSpace
