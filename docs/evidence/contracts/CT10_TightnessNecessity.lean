import BGW.Skorokhod.CompleteMetricSpace
import BGW.Skorokhod.Separable
import BGW.Skorokhod.Measurable
import BGW.Skorokhod.Tightness
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Contract probe for CT.C8 (CT10), remaining directions: necessity in Billingsley 1999,
Theorem 12.3 and the iff form of Theorem 13.2 for a sequence of laws on `D([0,T], E)`, `E`
proper. Every modulus hypothesis keeps `δ < T` (the modulus is `0` for `δ ≥ T` by convention),
and `0 < T` is assumed (for `T ≤ 0` no `δ` with `0 < δ < T` exists).
`cadlagModulus` is the sealed `BGW.Skorokhod.cadlagModulus`. Event measures are outer measures,
so no measurability of `w'` is needed.
Depends only on Mathlib, `BGW.Skorokhod` and `BGW.Probability`. -/

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace BGW.Skorokhod

variable {T : ℝ} {E : Type*}

/-- Billingsley 1999, Theorem 12.3, necessity: a relatively compact set of paths has values in a
bounded set and uniformly vanishing modulus `w'` at thresholds below `T`. (Corollary of
`exists_isBounded_values_of_isCompact` and `exists_uniform_cadlagModulus_of_isCompact` applied to
`closure A`, monotonicity of `f ↦ cadlagModulus f δ` not needed.) -/
theorem bounded_and_modulus_of_isCompact_closure [MetricSpace E] {A : Set (D T E)}
    (hT : 0 < T) (hA : IsCompact (closure A)) :
    (∃ K : Set E, Bornology.IsBounded K ∧ ∀ f ∈ A, ∀ t, f t ∈ K) ∧
    ∀ ε > 0, ∃ δ, 0 < δ ∧ δ < T ∧ ∀ f ∈ A, cadlagModulus f δ ≤ ε := sorry

/-- Billingsley 1999, Theorem 12.3 (iff): `A ⊆ D([0,T], E)`, `E` proper, is relatively compact
iff its values are bounded and `lim_{δ→0} sup_{f ∈ A} w'_f(δ) = 0`. -/
theorem isCompact_closure_iff_bounded_and_modulus [MetricSpace E] [ProperSpace E]
    {A : Set (D T E)} (hT : 0 < T) :
    IsCompact (closure A) ↔
      ((∃ K : Set E, Bornology.IsBounded K ∧ ∀ f ∈ A, ∀ t, f t ∈ K) ∧
        ∀ ε > 0, ∃ δ, 0 < δ ∧ δ < T ∧ ∀ f ∈ A, cadlagModulus f δ ≤ ε) := sorry

/-- Billingsley 1999, Theorem 13.2 (iff, limsup form): a sequence of probability laws on
`D([0,T], E)`, `E` proper (so `D` is Polish and each single law is tight), is tight iff
(i) for each `η > 0` there is a bounded `K ⊆ E` with `limsup_n P_n(∃ t, f t ∉ K) ≤ η`
(the form of `lim_{a→∞} limsup_n P_n(‖f‖ ≥ a) = 0` for a general metric `E`), and
(ii) for all `ε, η > 0` there is `δ ∈ (0,T)` with `limsup_n P_n(w'_f(δ) > ε) ≤ η`
(equivalent to `lim_{δ→0} limsup_n P_n(w'_f(δ) ≥ ε) = 0`, since `w'` is monotone in `δ`). -/
theorem isTightMeasureSet_range_iff_limsup [MetricSpace E] [ProperSpace E]
    (hT : 0 < T) (P : ℕ → ProbabilityMeasure (D T E)) :
    IsTightMeasureSet (Set.range fun n => (P n : Measure (D T E))) ↔
      ((∀ η > 0, ∃ K : Set E, Bornology.IsBounded K ∧
          limsup (fun n => (P n : Measure (D T E)) {f | ∃ t, f t ∉ K}) atTop ≤ ENNReal.ofReal η) ∧
        (∀ ε > 0, ∀ η > 0, ∃ δ, 0 < δ ∧ δ < T ∧
          limsup (fun n => (P n : Measure (D T E)) {f | ε < cadlagModulus f δ}) atTop ≤
            ENNReal.ofReal η)) := sorry

end BGW.Skorokhod
