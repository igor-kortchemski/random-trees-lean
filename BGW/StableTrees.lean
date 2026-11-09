/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Scalar.DensityLaw
public import BGW.StableTrees.Scalar.StableDensityPos
public import BGW.StableTrees.Scalar.StableDensityBounds
public import BGW.StableTrees.Scalar.FiniteVariance
public import BGW.StableTrees.Scalar.MaximalTightness
public import BGW.StableTrees.Scalar.ForestWalkBridge
public import BGW.StableTrees.Scalar.ForestBounds
public import BGW.StableTrees.RegularVariation.Karamata
public import BGW.StableTrees.MarchalWeights
public import BGW.StableTrees.MarchalChain
public import BGW.StableTrees.MarchalLaw
public import BGW.StableTrees.Attraction.StableDomainTail
public import BGW.StableTrees.StableLaw
public import BGW.StableTrees.RealAttractionBounds
public import BGW.StableTrees.StableLevyLaw
public import BGW.StableTrees.RealWalkTightness
public import BGW.StableTrees.WalkPathTightness
public import BGW.StableTrees.WalkPathFDD
public import BGW.StableTrees.StableDensityAPI
public import BGW.StableTrees.BridgePrefix
public import BGW.StableTrees.StableProcess
public import BGW.StableTrees.StableProcessReversal
public import BGW.StableTrees.StableProcessMarkov
public import BGW.StableTrees.StableProcessBrownian
public import BGW.StableTrees.StableLocalLaw
public import BGW.StableTrees.BridgeProjective
public import BGW.StableTrees.StableUniqueMinimum
public import BGW.StableTrees.StableBridgeClosed
public import BGW.StableTrees.StableLocalMarkov
public import BGW.StableTrees.StableStrongMarkov
public import BGW.StableTrees.StableFirstPassagePath
public import BGW.StableTrees.StableFirstPassage
public import BGW.StableTrees.StableRegularity
public import BGW.StableTrees.StableContinuousMinimum
public import BGW.StableTrees.StableBridgeMinimum
public import BGW.StableTrees.ReflectedRestart
public import BGW.StableTrees.StablePassageSubordinator
public import BGW.StableTrees.StablePassageSubordinatorStieltjes
public import BGW.StableTrees.StablePassageSubordinatorIncrements
public import BGW.StableTrees.StableExcursionSupport
public import BGW.StableTrees.WalkPassage
public import BGW.StableTrees.MarkedExcursions
public import BGW.StableTrees.ExcursionMeasure
public import BGW.StableTrees.ExcursionLifetime
public import BGW.StableTrees.UnitExcursionLaw
public import BGW.StableTrees.ExcursionMarkov
public import BGW.StableTrees.UnitExcursionDensity
public import BGW.StableTrees.GammaIdentity
public import BGW.StableTrees.StraddlingExcursion
public import BGW.StableTrees.StraddlingHeight
public import BGW.StableTrees.StablePositiveJumps
public import BGW.StableTrees.ExcursionJump
public import BGW.StableTrees.ExcursionGaps
public import BGW.StableTrees.AugmentedStrongMarkov
public import BGW.StableTrees.ForestLocalLimit
public import BGW.StableTrees.DiscreteForest
public import BGW.StableTrees.BrownianIdentification
public import BGW.StableTrees.PathTail
public import BGW.StableTrees.DiscreteBridge
public import BGW.StableTrees.ExactPrefix
public import BGW.StableTrees.VervaatIto
public import BGW.StableTrees.BrownianExcursion
public import BGW.StableTrees.Survival
public import BGW.StableTrees.DiscreteHeightApprox
public import BGW.StableTrees.HeightTightness
public import BGW.StableTrees.ForestContour
public import BGW.StableTrees.ForestTriple
public import BGW.StableTrees.ForestTripleVector
public import BGW.StableTrees.UnpaddedContour
public import BGW.StableTrees.TailPair
public import BGW.StableTrees.ExactPair
public import BGW.StableTrees.ExactContour
public import BGW.StableTrees.NonmonotoneNorming
public import BGW.StableTrees.BrownianPair
public import BGW.StableTrees.FiniteVarianceContour
public import BGW.StableTrees.LongExtractionDefs
public import BGW.StableTrees.LongExtraction
public import BGW.StableTrees.FirstLongMark
public import BGW.StableTrees.SupremumReflectedFamily
public import BGW.StableTrees.SupremumFactorization
public import BGW.StableTrees.SupremumDrawdown
public import BGW.StableTrees.SupremumPotential
public import BGW.StableTrees.SupremumCauchy
public import BGW.StableTrees.SupremumAuxLocalTime
public import BGW.StableTrees.SupremumLocalTimeIdent
public import BGW.StableTrees.SupremumLadderRestart
public import BGW.StableTrees.SupremumLadderTransform
public import BGW.StableTrees.SupremumCorrection
public import BGW.StableTrees.SupremumStoppedEnergy
public import BGW.StableTrees.SupremumLocalTimeStopped
public import BGW.StableTrees.SupremumLocalTimePublic
public import BGW.StableTrees.HeightProcess
public import BGW.StableTrees.HeightBridges
public import BGW.StableTrees.HeightContinuity
public import BGW.StableTrees.ExcursionHeight
public import BGW.StableTrees.JointExcursion
public import BGW.StableTrees.BrownianHeight
public import BGW.StableTrees.StablePositivity
public import BGW.StableTrees.StableBridgeUniformMinimum
public import BGW.StableTrees.KendallAdapter
public import BGW.StableTrees.StableKendall

/-!
# Stable random trees

Aggregate of the stable-tree layer, for an index `1 < θ ≤ 2`:

* scalar stable attraction of offspring laws: lattice local limits, density identification,
  regular variation of the normalizer, maximal tightness, forest estimates and admissible-size
  bounds, with the finite-variance instance at index two;
* the spectrally positive θ-stable law and Lévy process (on `D T ℝ` and on `DLoc`), the
  functional limit theorem for walks, fluctuation identities (first passage, Kendall, unique
  minimum) and the Brownian case `X = √2 B`;
* the reflected process `X − I`, its strong Markov property, Itô's excursion theorem, the
  excursion measure `N`, the normalized excursion, the Markov property under `N`, the `Γ_a`
  identity and Chaumont's path construction;
* the height process and its excursion height, the Duquesne–Le Gall forest theorem and the
  limits of trees with at least or exactly `n` vertices, with the identification at θ = 2;
* the stable bridge, its unique minimum, Chaumont's Vervaat identity and the largest jump of
  the normalized excursion;
* Marchal selection weights, the Marchal growth chain and its finite law.

`CLASSICAL_THEORY_COVERAGE.md` names the module of each result (items C15–C36).
-/
