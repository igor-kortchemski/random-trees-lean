import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! Contract probe for CT.C14, general version (CT10): Dudley's 1968 Skorokhod-type
representation. Weakly convergent Borel laws on a separable (pseudo)metric space are the laws of
random variables, on SOME probability space, converging almost surely.
The probability space is NOT claimed to be `[0,1]` with Lebesgue measure (a Bernstein-set
counterexample exists for general separable spaces, cf. the Polish case in
`BGW.Probability.exists_tendsto_ae_of_tendsto`). The universe of `Ω` equals that of `S`.
Depends only on Mathlib. -/

open Filter MeasureTheory
open scoped Topology

universe u

namespace BGW.Probability

/-- Dudley (1968): weak convergence of laws on a separable pseudometric space `S` with its Borel
σ-algebra implies a.s. convergent random variables on some probability space (Billingsley 1999,
Theorem 6.7 is the Polish/[0,1] case). -/
theorem exists_probabilitySpace_tendsto_ae_of_tendsto {S : Type u} [PseudoMetricSpace S]
    [TopologicalSpace.SeparableSpace S] [MeasurableSpace S] [BorelSpace S]
    {P : ℕ → ProbabilityMeasure S} {Q : ProbabilityMeasure S} (h : Tendsto P atTop (𝓝 Q)) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → S) (Y : Ω → S),
      (∀ n, Measurable (X n)) ∧ Measurable Y ∧
      (∀ n, Measure.map (X n) μ = (P n : Measure S)) ∧
      Measure.map Y μ = (Q : Measure S) ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)) := sorry

end BGW.Probability
