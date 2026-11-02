/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Scalar.DensityLaw
public import BGW.StableTrees.Scalar.FiniteVariance
public import BGW.StableTrees.Scalar.MaximalTightness
public import BGW.StableTrees.Scalar.ForestWalkBridge
public import BGW.StableTrees.Scalar.ForestBounds
public import BGW.StableTrees.RegularVariation.Karamata
public import BGW.StableTrees.MarchalWeights

/-!
# Scalar tools for stable random trees

Normalized scalar stable attraction yields a lattice local limit theorem, density
identification, regular variation of the normalizer and tightness of the partial-sum maximum.
The convolution walk is connected to the forest Kemperman identity, which yields uniform local,
tail and bridge-weighted forest bounds, and two-sided size bounds at admissible times.
The finite-variance endpoint is
constructed with index two and normalization `σ * sqrt n / sqrt 2`. These modules do not
construct a stable Lévy process, a height excursion or a continuum stable tree.
Marchal selection weights on a supplied finite graph tree have total mass `n * α - 1`
and give a normalized selection PMF. The growth chain itself is not constructed here.
-/
