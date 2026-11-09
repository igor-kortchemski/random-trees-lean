/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.AldousCriterionBasic
public import BGW.Skorokhod.Tightness

import BGW.Skorokhod.AldousCriterionModulus
import BGW.Skorokhod.AldousCriterionFixedTimes
import BGW.Skorokhod.AldousCriterionTightness
import BGW.Skorokhod.CompleteMetricCompleteness
import BGW.Skorokhod.Separable

/-!
# Aldous's tightness criterion on Skorokhod space

Aldous's sequence condition and compact containment imply tightness of the path laws.
The proof passes through optional strict exit times, averages deterministic offsets
for the short-gap estimate, bounds the number of exits, and merges a short terminal
block using endpoint control. Fixed-time tightness supplies compact containment via
finitely many deterministic control times and the modulus bound.

## References

* D. Aldous, *Stopping times and tightness*, Ann. Probab. 6 (1978), 335–340.
* P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley, 1999, Section 16.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace BGW.Skorokhod

variable {T : ℝ}

/-- Billingsley 1999, Theorem 16.10 (sufficiency). -/
theorem isTightMeasureSet_of_aldous (hT : 0 < T)
    {Ω : ℕ → Type*} [m : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (𝓕 : ∀ n, Filtration (Set.Icc (0 : ℝ) T) (m n))
    (X : ∀ n, Ω n → D T ℝ) (hX : ∀ n, Measurable (X n))
    (hadapted : ∀ n t, Measurable[𝓕 n t] (fun ω => X n ω t))
    (hsup : ∀ η > 0, ∃ c : ℝ,
      limsup (fun n => P n {ω | ∃ t, c ≤ |X n ω t|}) atTop ≤ ENNReal.ofReal η)
    (hAldous : ∀ (τ : ∀ n, Ω n → Set.Icc (0 : ℝ) T), (∀ n, IsStopTime (𝓕 n) (τ n)) →
      ∀ h : ℕ → ℝ, (∀ n, 0 ≤ h n) → Tendsto h atTop (𝓝 0) →
      ∀ ε > 0, Tendsto
        (fun n => P n {ω | ε ≤ |X n ω (Set.projIcc 0 T hT.le (τ n ω + h n)) - X n ω (τ n ω)|})
        atTop (𝓝 0)) :
    IsTightMeasureSet (Set.range fun n => (P n).map (X n)) := by
  apply isTightMeasureSet_of_source_cadlagModulus_eventually P X hX
    (fun _ => isTightMeasureSet_singleton)
  · intro η hη
    obtain ⟨c, hc⟩ := hsup (η / 2) (half_pos hη)
    have hlt : limsup (fun n => P n {ω | ∃ t, c ≤ |X n ω t|}) atTop <
        ENNReal.ofReal η := hc.trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff hη).mpr (half_lt_self hη))
    obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt hlt)
    refine ⟨Icc (-max c 0) (max c 0), Metric.isBounded_Icc _ _, N, fun n hn => ?_⟩
    apply (measure_mono ?_).trans ((hN n hn).le)
    rintro ω ⟨t, ht⟩
    refine ⟨t, ?_⟩
    by_contra! hsmall
    exact ht (abs_le.mp (hsmall.le.trans (le_max_left c 0)))
  · intro ε hε η hη
    exact exists_uniform_aldous_modulus_bound hT P 𝓕 X hX hadapted hAldous hε hη

/-- Same conclusion with the sup-norm tightness (i) replaced by tightness of `X^n_t` at every fixed
time `t ∈ [0,T]` (Billingsley 1999, Theorem 16.10 with fixed-time tightness).  Tightness of `X^n_0`
alone is NOT enough: `X^n_t = n·1{U ≤ t}` with `U` uniform satisfies Aldous's condition and has
tight `X^n_0 = 0`, but is not tight. -/
theorem isTightMeasureSet_of_aldous_fixedTimes (hT : 0 < T)
    {Ω : ℕ → Type*} [m : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (𝓕 : ∀ n, Filtration (Set.Icc (0 : ℝ) T) (m n))
    (X : ∀ n, Ω n → D T ℝ) (hX : ∀ n, Measurable (X n))
    (hadapted : ∀ n t, Measurable[𝓕 n t] (fun ω => X n ω t))
    (hfixed : ∀ t : Set.Icc (0 : ℝ) T, ∀ η > 0, ∃ c : ℝ,
      limsup (fun n => P n {ω | c ≤ |X n ω t|}) atTop ≤ ENNReal.ofReal η)
    (hAldous : ∀ (τ : ∀ n, Ω n → Set.Icc (0 : ℝ) T), (∀ n, IsStopTime (𝓕 n) (τ n)) →
      ∀ h : ℕ → ℝ, (∀ n, 0 ≤ h n) → Tendsto h atTop (𝓝 0) →
      ∀ ε > 0, Tendsto
        (fun n => P n {ω | ε ≤ |X n ω (Set.projIcc 0 T hT.le (τ n ω + h n)) - X n ω (τ n ω)|})
        atTop (𝓝 0)) :
    IsTightMeasureSet (Set.range fun n => (P n).map (X n)) := by
  have hmod : ∀ ε > 0, ∀ η > 0, ∃ δ, 0 < δ ∧ δ < T ∧ ∃ N : ℕ, ∀ n ≥ N,
      P n {ω | ε < cadlagModulus (X n ω) δ} ≤ ENNReal.ofReal η :=
    fun _ hε _ hη => exists_uniform_aldous_modulus_bound hT P 𝓕 X hX hadapted hAldous hε hη
  exact isTightMeasureSet_of_source_cadlagModulus_eventually P X hX
    (fun _ => isTightMeasureSet_singleton)
    (exists_eventual_value_bound_of_fixedTimes hT P X hfixed
      (fun η hη => hmod 1 (by norm_num) η hη)) hmod

end BGW.Skorokhod
