/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionGapsStrongMarkov
public import BGW.StableTrees.ExcursionGapsIto
public import BGW.StableTrees.StraddlingHeight

/-!
# Excursion soft gaps

This module collects the strong-Markov property of the reflected stable process, the Itô family
indexed by every positive lifetime, and the source-level supremum/infimum descriptions of the
endpoints of the excursion straddling a fixed positive time.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-! ### C25: the source definitions of the straddling endpoints -/

/-- **C25, last zero before `t`.**  O01's `straddleStart t f` is almost surely
`sup {s ≤ t | X_s = I_s}`. -/
theorem ae_straddleStart_eq_sSup {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {t : ℝ≥0} (ht : 0 < t) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), straddleStart t f =
      sSup {s : ℝ≥0 | s ≤ t ∧ f.1 s = runningInfLoc f s} := by
  filter_upwards [ae_straddle_zero_description hθ ht,
    ae_eval_zero_stableLocalLaw hθ] with f h h0
  simpa only [reflectedFrom_zero_apply h0, sub_eq_zero] using h.1

/-- **C25, first zero after `t`.**  O01's `straddleEnd t f` is almost surely
`inf {s > t | X_s = I_s}`. -/
theorem ae_straddleEnd_eq_sInf {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {t : ℝ≥0} (ht : 0 < t) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), straddleEnd t f =
      sInf {s : ℝ≥0 | t < s ∧ f.1 s = runningInfLoc f s} := by
  filter_upwards [ae_straddle_zero_description hθ ht,
    ae_eval_zero_stableLocalLaw hθ] with f h h0
  simpa only [reflectedFrom_zero_apply h0, sub_eq_zero] using h.2

end BGW.StableTrees
