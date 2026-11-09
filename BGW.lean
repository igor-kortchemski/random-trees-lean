/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree
public import BGW.Tree.Finite
public import BGW.Tree.Fringe
public import BGW.Tree.Vertices
public import BGW.Tree.DFS
public import BGW.Tree.Decode
public import BGW.Tree.Excursion
public import BGW.Tree.Forest
public import BGW.Tree.LocallyFinite
public import BGW.Tree.Weight
public import BGW.Tree.WalkWeight
public import BGW.Tree.CycleLemma
public import BGW.Tree.ForestCycle
public import BGW.Tree.FirstPassage
public import BGW.Tree.FringeWalk
public import BGW.Tree.FringeWeight
public import BGW.Tree.Contour
public import BGW.Tree.ContourVertices
public import BGW.Tree.ContourBracket
public import BGW.Tree.ContourMetric
public import BGW.Tree.ContourInterpolation
public import BGW.Tree.Height
public import BGW.Tree.Geometry
public import BGW.Tree.DegreeCount
public import BGW.GeneratingFunction
public import BGW.LocallyFinite.Topology
public import BGW.LocallyFinite.Prune
public import BGW.LocallyFinite.Law
public import BGW.LocallyFinite.Groups
public import BGW.LocallyFinite.Branching
public import BGW.LocallyFinite.Cylinders
public import BGW.LocallyFinite.Unique
public import BGW.LocallyFinite.Atoms
public import BGW.LocallyFinite.Extinction
public import BGW.LocallyFinite.Normalization
public import BGW.LocallyFinite.Supercritical
public import BGW.LocallyFinite.Generation
public import BGW.LocallyFinite.GenerationLaw
public import BGW.LocallyFinite.GenerationField
public import BGW.LocallyFinite.GenerationProcess
public import BGW.LocallyFinite.SizeConditioning
public import BGW.LocallyFinite.WalkLaw
public import BGW.LocallyFinite.ForestWalkLaw
public import BGW.LocallyFinite.FirstPassageLaw
public import BGW.LocallyFinite.BridgeLaw
public import BGW.LocallyFinite.ExcursionLaw
public import BGW.LocallyFinite.Tilting
public import BGW.LocallyFinite.Geometric
public import BGW.LocallyFinite.FringeLaw
public import BGW.LocallyFinite.DegreeConditioning
public import BGW.Probability
public import BGW.Skorokhod
public import BGW.MetricMeasure
public import BGW.ContinuumTrees
public import BGW.StableTrees

/-!
# BGW formalization

Entry point of the library. It imports every area:

* **Discrete trees and BGW laws** (`BGW.Tree`, `BGW.LocallyFinite.*`, `BGW.GeneratingFunction`):
  finite plane trees with their list interface, Łukasiewicz coding and cycle lemmas, locally
  finite trees with the Bienaymé–Galton–Watson law of an arbitrary offspring law, its branching
  property and uniqueness, extinction, generations, size and degree conditioning, Kemperman
  identities, tilting, fringe laws and discrete contours.
* **Probability tools** (`BGW.Probability`): weak convergence, the continuous mapping theorem,
  Slutsky on varying spaces, Prokhorov and Skorokhod representation, convergence in measure.
* **Skorokhod space** (`BGW.Skorokhod`): càdlàg paths `D T E` with the J1 metric and
  Billingsley's complete metric, measurability, tightness criteria, scaling, the Vervaat map,
  jumps, and local paths `DLoc`.
* **Metric-measure geometry** (`BGW.MetricMeasure`): the Gromov–Hausdorff–Prokhorov metric on
  compact metric probability spaces, unrooted and rooted, with Polishness and sampled laws.
* **Continuum trees** (`BGW.ContinuumTrees`): real trees coded by continuous functions, the
  transfer of contour convergence to rooted GHP laws, the Brownian bridge and its Vervaat image,
  and the uniform leaf measure.
* **Stable trees** (`BGW.StableTrees`): the stable law and Lévy process, fluctuation and
  excursion theory, the height process, the Duquesne–Le Gall forest theorem and the limits of
  conditioned BGW trees, stable bridges, and the Marchal growth chain.

`CLASSICAL_THEORY_COVERAGE.md` maps each classical result C1–C39 to its declarations and module.
-/
