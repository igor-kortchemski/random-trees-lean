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
public import BGW.MetricMeasure
public import BGW.ContinuumTrees
public import BGW.StableTrees

/-!
# BGW formalization

Entry point for finite plane trees, fringe subtrees, cut and graft operations,
finite size classes, the tree/excursion correspondence with executable decoding,
first passage at forest component boundaries, and the exact bridge to the finite
part of the canonical locally finite tree carrier. That carrier has its Polish
topology, canonical pruning of offspring fields, and the Bienaymé–Galton–Watson
law for an arbitrary offspring law, with its branching property, its uniqueness
among laws with that property, and the atoms of finite trees as degree-product
weights. Extinction by a finite depth, the iteration of the offspring generating function
and the identification of the probability of finiteness with its smallest fixed point in
`[0, 1]` are proved for every offspring law, and the extinction probability is one for mean at
most one with `μ {1} ≠ 1`. Conditioning on the number of vertices is set up on finite trees, with
admissible sizes and the atoms of the conditioned law. Walk weights of Łukasiewicz words, the
deterministic cycle lemma for bridges and the Kemperman–Dwass identity in weight form are proved
for arbitrary step masses, and give `n * P(|T| = n) = P(S_n = -1)` for the Łukasiewicz walk of
independent offspring counts. The same holds for forests of `ℓ` trees, with the generalized cycle
lemma, and the walk ending at `-ℓ` is decomposed at its first passage time: the unconditional
first-passage convolution `P(S_N = -ℓ) = ∑_{q ≤ N} P(|𝒢_ℓ| = q) P(S_{N-q} = 0)`. The conditional
bridge law is described, and the size-conditioned tree is represented by the uniform cyclic shift
of a bridge, in atom and expectation form. The excursion law is the law of the counts given that
the walk first reaches `-1` at time `n`: it has the mass `P(|T| = n)` and is the law of the code of
the size-conditioned tree, in atom and expectation form. The extinction probability is classified
by the mean: it is one exactly when the mean is at most one and `μ {1} ≠ 1`, and below one when the
mean exceeds one (infinite mean allowed). Generations are finite sets of present addresses, with
measurable sizes, root-conditioned branching, iterated generating functions and extended mean
`m ^ n`. Their next size, conditional on the full finite history, is the sum of iid offspring
counts, with zero absorbing. Exponential tilting preserves size-conditioned laws, and geometric
offspring gives the uniform plane-tree law at each positive size. Conditioning may also prescribe
finitely many degree counts. Exact fringe expectations, discrete contours and vertex graph
metrics are available. The generic GHP core defines compact measured spaces and their Polish
metric quotient by whole-carrier measured isometries, with compactness and tightness transfer
to GH. The represented rooted infimum adds the root distance. Continuous coding functions give
compact metric quotients, and the scalar stable toolkit gives lattice local limits, maximal
tightness, forest estimates and admissible-size bounds.
-/
