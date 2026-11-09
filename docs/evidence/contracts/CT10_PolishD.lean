import BGW.Skorokhod.CompleteMetricSpace
import BGW.Skorokhod.Separable
import BGW.Skorokhod.Measurable
import BGW.Skorokhod.Tightness
import BGW.Probability.SkorokhodRepresentation
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Contract probe for CT.C3 (Polishness), CT.C13 (converse Prokhorov direction on `D`) and the
`D`-valued case of CT.C14 (CT10). Polishness comes from the sealed
`instIsCompletelyMetrizableSpace` and `instSeparableSpace`; the metric instance on `D` stays the
J1 metric `d`, completeness being via Billingsley's `d°`.
Depends only on Mathlib, `BGW.Skorokhod` and `BGW.Probability`. -/

open Filter MeasureTheory
open scoped Topology

namespace BGW.Skorokhod

variable {T : ℝ} {E : Type*}

/-- `D([0,T], E)` is Polish for complete separable metric `E` (Billingsley 1999, Theorems
12.1-12.2; C3). -/
theorem polishSpace_D [MetricSpace E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E] :
    PolishSpace (D T E) := sorry

/-- `D([0,T], E)` with its Borel σ-algebra is a standard Borel space. -/
theorem standardBorelSpace_D [MetricSpace E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] : StandardBorelSpace (D T E) := sorry

/-- Skorokhod representation on `D` (C14, `D`-valued case): weakly convergent laws on
`D([0,T], E)` are the laws of random variables on `([0,1], Lebesgue)` converging almost surely.
Corollary of `BGW.Probability.exists_tendsto_ae_of_tendsto` and `polishSpace_D`. -/
theorem exists_tendsto_ae_of_tendsto_D [MetricSpace E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    {P : ℕ → ProbabilityMeasure (D T E)} {Q : ProbabilityMeasure (D T E)}
    (h : Tendsto P atTop (𝓝 Q)) :
    ∃ (X : ℕ → unitInterval → D T E) (Y : unitInterval → D T E),
      (∀ n, Measurable (X n)) ∧ Measurable Y ∧
      (∀ n, Measure.map (X n) (volume : Measure unitInterval) = (P n : Measure (D T E))) ∧
      Measure.map Y (volume : Measure unitInterval) = (Q : Measure (D T E)) ∧
      ∀ᵐ ω ∂(volume : Measure unitInterval), Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)) :=
  sorry

/-- Prokhorov's theorem on `D`, both directions (C13's converse specialization): a set of
probability laws on `D([0,T], E)` is tight iff it is relatively compact for the topology of weak
convergence. -/
theorem isTightMeasureSet_iff_isCompact_closure_D [MetricSpace E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] (S : Set (ProbabilityMeasure (D T E))) :
    IsTightMeasureSet {((μ : ProbabilityMeasure (D T E)) : Measure (D T E)) | μ ∈ S} ↔
      IsCompact (closure S) := sorry

end BGW.Skorokhod
