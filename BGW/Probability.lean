/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Probability.NNReal
public import BGW.Probability.Completion
public import BGW.Probability.Rounding
public import BGW.Probability.Stieltjes
public import BGW.Probability.SkorokhodRepresentationLift
public import BGW.Probability.IntegralLimits
public import BGW.Probability.ConvergenceInMeasure
public import BGW.Probability.TailBounds
public import BGW.Probability.MeasurableReconstruction
public import BGW.Probability.IndependentPartialSums
public import BGW.Probability.WeakConvergence
public import BGW.Probability.SkorokhodRepresentation
public import BGW.Probability.RealWalk
public import BGW.Probability.RealWalkMaximal
public import BGW.Probability.RealWalkExitCount
public import BGW.Probability.SeparableRepresentation
public import BGW.Probability.PoissonCharacterization
public import BGW.Probability.DoobL2Resolvent

/-!
# Generic probability tools

Weak convergence of laws on varying probability spaces: the extended continuous mapping
theorem for maps continuous almost everywhere under the limit law, the choice of cut-off
levels with null boundaries, Slutsky's theorem with a constant limit and the approximation
theorem (Billingsley 1999, Theorems 2.7, 3.9 and 3.2), and Skorokhod's representation theorem
on Polish spaces, realized on the unit interval with Lebesgue measure (Theorem 6.7), with a
quantile coupling on the real line. Walks with iid real steps are set up on the canonical
product space, with block independence, the fresh start after a fixed time and the laws and
characteristic functions of block sums, Ottaviani's maximal inequality, and bounds on the number of
restart exits of a walk and on close
pairs of exits. These results do not depend on trees.
-/
