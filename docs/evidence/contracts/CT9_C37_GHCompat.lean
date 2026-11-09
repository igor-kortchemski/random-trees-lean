import BGW.ContinuumTrees

/-! Contract probe for CT.C37 (CT9): GH-level corollaries of the existing coding exports.

Already DONE (not restated): `Coding.ghDist_le_two_mul_norm`, `Coding.lipschitzWith_two_toGHSpace`
(GH constant 2, `CodingGH.lean`), `RootedMeasuredGHSpace.lipschitzWith_underlyingGH_forgetRoot`
(forgetful map 1-Lipschitz), `Coding.lipschitzWith_rootedMeasuredGHSpace` (rooted measured GHP
constant 6). Note the constant 6 for GHP is not 2: the specification's GH constant 2 is the
`CodingGH` one, which is not obtained by composing with the forgetful map (that would give 6).

TRUTH: `underlyingGH (forgetRoot (rootedMeasuredGHSpace g))` is the GH class of the coded tree, so
the two statements below are definitional bridges plus continuous mapping.

PROOF PLAN:
1. `compat`: unfold `rootedMeasuredGHSpace`, `forgetRoot_toRootedMeasuredGHSpace`,
   `underlyingGH_toMeasuredGHSpace`; should be `rfl`.
2. `tendsto_map_forgetToGH`: `ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous` with
   `continuous_forgetToGH` (Borel structure on `GHSpace` as in `measurable_underlyingGH`). -/

open Filter MeasureTheory GromovHausdorff
open scoped Topology
open BGW.MetricMeasure BGW.ContinuumTrees

universe u

namespace BGW.ContinuumTrees.Coding

/-- Local Borel structure on `GHSpace`, as in `measurable_underlyingGH`. -/
noncomputable local instance ghMeasurableSpace : MeasurableSpace GHSpace := borel GHSpace

local instance : BorelSpace GHSpace := ⟨rfl⟩

/-- Forget root and measure: the GH class of a rooted measured class. -/
noncomputable def forgetToGH : RootedMeasuredGHSpace.{u} → GHSpace :=
  MeasuredGHSpace.underlyingGH ∘ RootedMeasuredGHSpace.forgetRoot

theorem continuous_forgetToGH : Continuous forgetToGH.{u} :=
  MeasuredGHSpace.continuous_underlyingGH.comp RootedMeasuredGHSpace.continuous_forgetRoot

/-- The GH class of the coded tree is the forgetful image of its rooted measured class. -/
theorem underlyingGH_forgetRoot_rootedMeasuredGHSpace (g : C(unitInterval, ℝ)) :
    forgetToGH.{0} (Coding.rootedMeasuredGHSpace g) = toGHSpace (Coding.Space g) := sorry

/-- Weak convergence of laws of rooted measured classes gives weak convergence of the laws of
the underlying GH classes.  The laws on `GHSpace` use its Borel σ-algebra (`borel GHSpace`), which
callers must provide locally (`letI := borel GHSpace`), as in `measurable_underlyingGH`. -/
theorem tendsto_map_forgetToGH {ι : Type*} {L : Filter ι}
    (P : ι → ProbabilityMeasure RootedMeasuredGHSpace.{u})
    {Q : ProbabilityMeasure RootedMeasuredGHSpace.{u}} (h : Tendsto P L (𝓝 Q)) :
    Tendsto (fun i => (P i).map forgetToGH.{u})
      L (𝓝 (Q.map forgetToGH.{u})) := sorry

end BGW.ContinuumTrees.Coding
