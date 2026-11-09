/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.MeasuredGHMetric
public import BGW.MetricMeasure.GHPCompleteness
public import BGW.MetricMeasure.GHPCompactness
public import BGW.MetricMeasure.GHPTightness
public import BGW.MetricMeasure.RootedCompactMeasuredSpace
public import BGW.MetricMeasure.RootedMeasuredGHSpace
public import BGW.MetricMeasure.RootedScalingContinuity
public import BGW.MetricMeasure.MeasuredScaling
public import BGW.MetricMeasure.RootedUnderlyingGH
public import BGW.MetricMeasure.WeakPerturbation
public import BGW.MetricMeasure.RootedGHPSeparability
public import BGW.MetricMeasure.RootedGHPCompleteness
public import BGW.MetricMeasure.SampledDistanceContinuity

/-!
# Compact metric probability spaces and the Gromov–Hausdorff–Prokhorov metric

The metric uses the sum of Hausdorff and Lévy–Prokhorov distances in a common ambient space.
Its quotient identifies entire carriers by surjective measure-preserving isometries; full
support is not assumed. The quotient is complete and separable, hence Polish, and forgetting
the measure is nonexpansive with compact inverse images of compact GH sets.
The rooted infimum adds the actual distance between embedded roots. Its zero-distance relation
is whole-carrier root- and measure-preserving isometry, and it defines a genuine metric quotient
with 1-Lipschitz forgetting of the root. Positive spatial scaling preserves mass and is jointly
continuous, and the rooted metric is complete and separable, hence Polish. Weak convergence is
stable under errors
vanishing in probability, also on varying source probability spaces. Every finite iid sampled
distance law is GHP-continuous, including repeated samples.
-/
