import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.GDelta.MetrizableSpace

/-! Contract probe for CT.C9, CT.C10(2) and CT.C11(1): generic weak-convergence tools on
varying probability spaces. The maintained file `BGW/Probability/WeakConvergence.lean`
must prove these exact statements. -/

open Filter MeasureTheory Set
open scoped Topology

namespace BGW.Probability

/-- A map continuous at almost every point is almost everywhere measurable: its set of
continuity points is a `G_δ` (C9, companion 1). -/
theorem aemeasurable_of_ae_continuousAt {S S' : Type*}
    [TopologicalSpace S] [MeasurableSpace S] [OpensMeasurableSpace S]
    [PseudoMetricSpace S'] [MeasurableSpace S'] [BorelSpace S']
    {μ : Measure S} {h : S → S'} (hcont : ∀ᵐ x ∂μ, ContinuousAt h x) :
    AEMeasurable h μ := sorry

/-- Extended continuous mapping theorem (Billingsley 1999, Theorem 2.7): weak convergence
is preserved by a map that is continuous at almost every point of the limit law (C9). -/
theorem tendsto_map_of_ae_continuousAt {S S' : Type*}
    [PseudoMetricSpace S] [MeasurableSpace S] [OpensMeasurableSpace S]
    [PseudoMetricSpace S'] [MeasurableSpace S'] [BorelSpace S']
    {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
    {P : ι → ProbabilityMeasure S} {Q : ProbabilityMeasure S} (hPQ : Tendsto P L (𝓝 Q))
    {h : S → S'} (hmeas : ∀ i, AEMeasurable h (P i))
    (hcont : ∀ᵐ x ∂(Q : Measure S), ContinuousAt h x) :
    Tendsto (fun i => (P i).map h) L (𝓝 (Q.map h)) := sorry

/-- A finite measure gives positive mass to at most countably many sets of a family with
pairwise disjoint frontiers; used to choose cut-off levels with null boundaries
(C9, companion 2; N11). -/
theorem countable_setOf_measure_frontier_ne_zero {S ι : Type*}
    [TopologicalSpace S] [MeasurableSpace S] [OpensMeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ] {A : ι → Set S}
    (hdisj : Pairwise (Function.onFun Disjoint fun i => frontier (A i))) :
    {i | μ (frontier (A i)) ≠ 0}.Countable := sorry

/-- Slutsky on varying probability spaces (Billingsley 1999, Theorem 3.9): if `X n`
converges in law and `Y n` converges in probability to a constant `c`, then the pair
converges in law to the product of the limit law with the Dirac mass at `c` (C10(2)). -/
theorem tendsto_map_prodMk_of_tendsto_of_error {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {S S' : Type*} [PseudoMetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [SecondCountableTopology S]
    [PseudoMetricSpace S'] [MeasurableSpace S'] [BorelSpace S'] [SecondCountableTopology S']
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n)) {X : (n : ℕ) → Ω n → S}
    {Y : (n : ℕ) → Ω n → S'} (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    {P : ProbabilityMeasure S} {c : S'}
    (hlim : Tendsto (fun n => (μ n).map (X n)) atTop (𝓝 P))
    (herr : ∀ ε > 0, Tendsto (fun n =>
      (μ n : Measure (Ω n)).real {ω | ε < dist (Y n ω) c}) atTop (𝓝 0)) :
    Tendsto (fun n => (μ n).map (fun ω => (X n ω, Y n ω))) atTop
      (𝓝 (P.map (fun x => (x, c)))) := sorry

/-- Approximation theorem (Billingsley 1999, Theorem 3.2), on varying probability spaces:
if `X u n ⇒ Z u` as `n → ∞`, `Z u ⇒ ν` as `u → ∞`, and `X u n` approximates `Y n`
uniformly in probability as `u → ∞`, then `Y n ⇒ ν` (C11(1)). -/
theorem tendsto_of_tendsto_approx {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {S : Type*} [PseudoMetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [SecondCountableTopology S]
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n)) {Y : (n : ℕ) → Ω n → S}
    {X : ℕ → (n : ℕ) → Ω n → S} (hY : ∀ n, Measurable (Y n))
    (hX : ∀ u n, Measurable (X u n)) {Z : ℕ → ProbabilityMeasure S}
    {ν : ProbabilityMeasure S}
    (hXZ : ∀ u, Tendsto (fun n => (μ n).map (X u n)) atTop (𝓝 (Z u)))
    (hZ : Tendsto Z atTop (𝓝 ν))
    (herr : ∀ ε > 0, Tendsto (fun u => limsup (fun n =>
      (μ n : Measure (Ω n)).real {ω | ε ≤ dist (X u n ω) (Y n ω)}) atTop) atTop (𝓝 0)) :
    Tendsto (fun n => (μ n).map (Y n)) atTop (𝓝 ν) := sorry

end BGW.Probability
