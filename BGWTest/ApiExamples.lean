/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

import BGW

/-!
# Additive public API examples

Short consumer examples for postcomposition, real scalar time–space scaling, and unrooted measured
GH scaling. These examples intentionally use only the public umbrella import.
-/

open BGW BGW.Skorokhod BGW.MetricMeasure

example (f : D 1 ℝ) : D.postcomp (ContinuousMap.id ℝ) f = f := by
  simp

example (f : D 1 ℝ) :
    D.postcomp ((ContinuousMap.id ℝ).comp (ContinuousMap.id ℝ)) f = f := by
  simp

example : Measurable (D.postcomp (T := 1) (ContinuousMap.id ℝ)) :=
  D.measurable_postcomp _

example {T a : ℝ} (hT : 0 ≤ T) (p : D T ℝ × ℝ × Set.Ioi (0 : ℝ)) :
    timeSpaceScaleSMul a hT p = timeSpaceScale a hT p := by
  simp

example {T : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (hT : 0 ≤ T) : Continuous (timeSpaceScaleSMulC (E := E) a hT) :=
  continuous_timeSpaceScaleSMulC a hT

example (X : MeasuredGHSpace) : MeasuredGHSpace.scale 1 zero_lt_one X = X := by
  simp

example {K : NNReal} {g : C(ℝ, ℝ)} (hg : LipschitzWith K g) :
    LipschitzWith (max K 1) (D.postcomp (T := 1) g) :=
  D.lipschitzWith_postcomp hg
