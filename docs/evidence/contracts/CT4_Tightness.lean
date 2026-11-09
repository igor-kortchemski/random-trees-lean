import BGW.Skorokhod
import Mathlib.MeasureTheory.Measure.Tight

/-! Contract probe for CT.C8 (CT4), sufficiency directions: Billingsley's modulus `w'`,
the Arzelà–Ascoli-type compactness criterion and a tightness criterion in `D`
(Billingsley 1999, Theorems 12.3 and 13.2; Ethier–Kurtz 3.6.3). Maintained file:
`BGW/Skorokhod/Tightness.lean`. -/

open Filter MeasureTheory Set
open scoped Topology

namespace BGW.Skorokhod

variable {T : ℝ} {E : Type*}

/-- Billingsley's càdlàg modulus `w'_f(δ)`: the infimum, over partitions
`0 = t₀ < t₁ < ⋯ < t_r = T` whose steps all exceed `δ`, of the largest oscillation of `f` on the
half-open blocks `[t_{i-1}, t_i)`. (It is `0` by convention when no such partition exists,
e.g. for `δ ≥ T`; only small `δ` matter.) -/
noncomputable def cadlagModulus [PseudoMetricSpace E] (f : D T E) (δ : ℝ) : ℝ :=
  ⨅ (p : Σ r : ℕ, {t : Fin (r + 1) → ℝ // t 0 = 0 ∧ t (Fin.last r) = T ∧ StrictMono t ∧
      ∀ i : Fin r, δ < t i.succ - t i.castSucc}),
    ⨆ (i : Fin p.1) (s : Set.Icc (0 : ℝ) T) (u : Set.Icc (0 : ℝ) T)
      (_ : p.2.1 i.castSucc ≤ s ∧ (s : ℝ) < p.2.1 i.succ ∧
        p.2.1 i.castSucc ≤ u ∧ (u : ℝ) < p.2.1 i.succ),
      dist (f s) (f u)

/-- Every càdlàg path has `w'_f(δ) → 0` as `δ ↓ 0` (Billingsley 1999, (12.7)). -/
theorem tendsto_cadlagModulus [MetricSpace E] (f : D T E) :
    Tendsto (fun δ => cadlagModulus f δ) (𝓝[>] 0) (𝓝 0) := sorry

/-- Arzelà–Ascoli criterion in `D` (sufficiency, Billingsley 1999, Theorem 12.3): a set of paths
with values in a fixed bounded set of a proper space and with uniformly vanishing modulus `w'`
has compact closure. -/
theorem isCompact_closure_of_cadlagModulus [MetricSpace E] [ProperSpace E] {A : Set (D T E)}
    {K : Set E} (hK : Bornology.IsBounded K) (hA : ∀ f ∈ A, ∀ t, f t ∈ K)
    (hmod : ∀ ε > 0, ∃ δ, 0 < δ ∧ δ < T ∧ ∀ f ∈ A, cadlagModulus f δ ≤ ε) :
    IsCompact (closure A) := sorry

/-- Tightness criterion in `D` (sufficiency, uniform form of Billingsley 1999, Theorem 13.2):
if, uniformly in `n`, the paths stay in a bounded set with high probability and the modulus
`w'` is small with high probability, then the laws are tight. Measures of possibly
non-measurable sets are outer measures, so no measurability of `w'` is assumed. -/
theorem isTightMeasureSet_of_cadlagModulus [MetricSpace E] [ProperSpace E]
    [MeasurableSpace (D T E)] [OpensMeasurableSpace (D T E)] {ι : Type*}
    (P : ι → Measure (D T E))
    (hbdd : ∀ η > 0, ∃ K : Set E, Bornology.IsBounded K ∧
      ∀ i, P i {f | ∃ t, f t ∉ K} ≤ ENNReal.ofReal η)
    (hmod : ∀ ε > 0, ∀ η > 0, ∃ δ, 0 < δ ∧ δ < T ∧
      ∀ i, P i {f | ε < cadlagModulus f δ} ≤ ENNReal.ofReal η) :
    IsTightMeasureSet (Set.range P) := sorry

/-- Tightness criterion in `D` in Billingsley's eventual form (Theorem 13.2, sufficiency): the
bounds are only required for large `n`, and each single law is assumed tight (for example the
law of a step path, a continuous image of a law on `ℝⁿ`). -/
theorem isTightMeasureSet_of_cadlagModulus_eventually [MetricSpace E] [ProperSpace E]
    [MeasurableSpace (D T E)] [OpensMeasurableSpace (D T E)] (P : ℕ → Measure (D T E))
    (htight : ∀ n, IsTightMeasureSet {P n})
    (hbdd : ∀ η > 0, ∃ K : Set E, Bornology.IsBounded K ∧
      ∃ N, ∀ n ≥ N, P n {f | ∃ t, f t ∉ K} ≤ ENNReal.ofReal η)
    (hmod : ∀ ε > 0, ∀ η > 0, ∃ δ, 0 < δ ∧ δ < T ∧
      ∃ N, ∀ n ≥ N, P n {f | ε < cadlagModulus f δ} ≤ ENNReal.ofReal η) :
    IsTightMeasureSet (Set.range P) := sorry

end BGW.Skorokhod
