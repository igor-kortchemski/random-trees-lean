/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.ContinuumTrees.CodingGH
public import BGW.MetricMeasure.RootedUnderlyingGH

/-!
# Gromov--Hausdorff compatibility of the coding maps

The forgetful map from rooted measured classes to GH classes sends the class of a coded tree to
its GH class. The coding-independent continuity and law-transport API lives in
`BGW.MetricMeasure.RootedUnderlyingGH` and is publicly re-exported here.

Reference: D. Burago, Y. Burago and S. Ivanov, *A Course in Metric Geometry*, AMS, 2001,
Chapter 7.
-/

@[expose] public section

open Filter MeasureTheory GromovHausdorff
open scoped Topology
open BGW.MetricMeasure BGW.ContinuumTrees

universe u

namespace BGW.ContinuumTrees.Coding

/-- The GH class of the coded tree is the forgetful image of its rooted measured class. -/
theorem underlyingGH_forgetRoot_rootedMeasuredGHSpace (g : C(unitInterval, ℝ)) :
    forgetToGH.{0} (Coding.rootedMeasuredGHSpace g) = toGHSpace (Coding.Space g) := rfl

end BGW.ContinuumTrees.Coding
