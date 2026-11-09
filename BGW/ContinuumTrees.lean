/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.ContinuumTrees.RealTree
public import BGW.ContinuumTrees.CodingQuotient
public import BGW.ContinuumTrees.CodingRealTree
public import BGW.ContinuumTrees.CodingMeasure
public import BGW.ContinuumTrees.CodingStability
public import BGW.ContinuumTrees.CodingGH
public import BGW.ContinuumTrees.ContourAdapters
public import BGW.ContinuumTrees.CodingGHCompat
public import BGW.ContinuumTrees.ContourPaperTransfer
public import BGW.ContinuumTrees.CodingReroot
public import BGW.ContinuumTrees.FiniteTree
public import BGW.ContinuumTrees.ContourEmbedding
public import BGW.ContinuumTrees.ContourDensity
public import BGW.ContinuumTrees.ContourConvergence
public import BGW.ContinuumTrees.ContourLawConvergence
public import BGW.ContinuumTrees.BrownianBridge
public import BGW.ContinuumTrees.BrownianBridgeRegression
public import BGW.ContinuumTrees.BrownianBridgeGrid
public import BGW.ContinuumTrees.BrownianBridgeMinimum
public import BGW.ContinuumTrees.BrownianBridgeUniqueMinimum
public import BGW.ContinuumTrees.Vervaat
public import BGW.ContinuumTrees.VervaatBridge
public import BGW.ContinuumTrees.BrownianD
public import BGW.ContinuumTrees.LeafMeasure
public import BGW.ContinuumTrees.LeafLawConvergence
public import BGW.ContinuumTrees.ExcursionCarrier

/-!
# Real-tree geometry for continuum random trees

The deterministic core proves that complete four-point metric spaces with midpoints are real
trees. Continuous real functions code compact metric real trees through their interval minima;
the four-point and midpoint properties are proved for these quotients. The root is time zero,
and the probability mass is the Lebesgue pushforward. The map to rooted measured isometry
classes is 6-Lipschitz for the uniform norm. Finite plane trees are bundled with their vertex
graph metric, root and uniform probability on all vertices. First contour visits embed these
vertices isometrically in the contour-coded real tree, preserving the root. Deterministic
rerooting is a genuine measured isometry with the chosen new root. Uniform vertex mass is
compared with contour mass, and uniform contour convergence transfers deterministically to
rooted GHP under the explicit size/divisor assumptions, both deterministically and in law
on varying probability spaces with random sizes. A continuous Brownian bridge law is
constructed from the pinned Brownian supplier. Its minimum is strictly negative almost surely,
and the minima on `[0,b]` and `[c,d]` are almost surely unequal when `b < c ≤ d < 1`.
Hence the minimum is almost surely attained at a unique interior time, and the Vervaat
transform of the bridge is almost surely strictly positive on `(0,1)`.
The deterministic Vervaat map is measurable. The identification of the Vervaat image with the
normalized Brownian excursion is proved in the stable layer
(`BGW.StableTrees.BrownianIdentification.levyExcLaw_two`). The uniform leaf measure of large
trees has the same rooted GHP limit in law as the uniform vertex measure.
-/
