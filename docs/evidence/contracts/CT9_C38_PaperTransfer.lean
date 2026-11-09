import BGW.ContinuumTrees

/-! Contract probe for CT.C38 (CT9): the composed transfer "paper contour `C_{2ζ s}` + Remark 5.10
divisor + measurable random trees => rooted measured GHP convergence of the vertex-measure trees".

TRUTH: all ingredients exist in `BGW.ContinuumTrees.ContourAdapters` and
`ContourLawConvergence`; this is a one-shot composition, with no new mathematics.
Hypotheses are exactly those of the specification: varying `Ω n`, random trees measurable for the
`⊤` sigma-algebra on `PlaneTree` (discharges `hF`, `hG`), `B n > 0`, `B n -> ∞`, `B n / N n -> 0`,
the vertex-count law of large numbers `P(ζ < c N_n) -> 0` for `0 < c < 1/μ₀`, and weak
convergence of the paper-convention contour `(b_n)⁻¹ C_{2ζ ·}` to `ν`. The divisor is
`remarkDivisor μ₀ θ N B`.

PROOF PLAN:
1. `b := remarkDivisor μ₀ θ N B`, `hb := remarkDivisor_pos`,
   `hbinfty := tendsto_remarkDivisor_atTop`.
2. `hratio := tendsto_ratio_remarkDivisor` (needs `hBinfty`, `hsize`).
3. `hsize' := tendsto_real_size_lt_of_ratio` for the size divergence in probability.
4. Measurability: `measurable_paperContour_of_top`, `measurable_contour_of_top`,
   `measurable_rootedMeasuredGHSpace_of_top`.
5. `tendsto_map_contour_of_tendsto_map_paperContour` converts `hlim`; then
   `tendsto_rooted_laws_of_contour`.
Padding / time convention: handled by `paperTimeChange` (within `1/ζ` of the identity). -/

open Filter MeasureTheory
open scoped Topology
open BGW.MetricMeasure BGW.ContinuumTrees BGW.ContinuumTrees.FiniteTree

namespace BGW.ContinuumTrees.FiniteTree

/-- C38 with the paper's time convention and the deterministic divisor of Remark 5.10. -/
theorem tendsto_rooted_laws_of_paperContour_remarkDivisor
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n))
    (t : (n : ℕ) → Ω n → PlaneTree)
    (ht : ∀ n, @Measurable (Ω n) PlaneTree _ ⊤ (t n))
    {μ₀ θ : ℝ} (hμ₀ : 0 < μ₀) {N : ℕ → ℕ} {B : ℕ → ℝ}
    (hN : ∀ n, 0 < N n) (hB : ∀ n, 0 < B n) (hBinfty : Tendsto B atTop atTop)
    (hNB : Tendsto (fun n => B n / (N n : ℝ)) atTop (𝓝 0))
    (hsize : ∀ c : ℝ, 0 < c → c < 1 / μ₀ → Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | ((t n ω).size : ℝ) < c * (N n : ℝ)}) atTop (𝓝 0))
    {ν : ProbabilityMeasure C(unitInterval, ℝ)}
    (hlim : Tendsto (fun n => (μ n).map
      (fun ω : Ω n => (remarkDivisor μ₀ θ N B n)⁻¹ • (t n ω).paperContourFunction))
      atTop (𝓝 ν)) :
    Tendsto (fun n => (μ n).map (fun ω : Ω n =>
      RootedMeasuredGHSpace.scale (remarkDivisor μ₀ θ N B n)⁻¹
        (inv_pos.mpr (remarkDivisor_pos hμ₀ hN hB n))
        (toRootedMeasuredGHSpace (rootedCompactMeasuredSpace (t n ω)))))
      atTop (𝓝 (ν.map Coding.rootedMeasuredGHSpace)) := sorry

end BGW.ContinuumTrees.FiniteTree
