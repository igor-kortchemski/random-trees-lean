import BGW.ContinuumTrees.ContourLawConvergence

/-! Contract probe for CT.C38 conversions 1 and 2 and the measurability hypotheses of
`FiniteTree.tendsto_rooted_laws_of_contour` (reuse audit items L4, L5, L6).
Intended maintained file: `BGW/ContinuumTrees/ContourAdapters.lean`.

Conventions. The library contour `PlaneTree.contourFunction t` is `s ↦ C_{2(ζ-1) s}` on `[0,1]`
(`ζ = t.size`), the paper uses `s ↦ C_{2ζ s}` with `C_u = 0` for `u ≥ 2(ζ-1)`. Hence
`paperContourFunction t = contourFunction t ∘ (s ↦ min 1 (s ζ/(ζ-1)))`. -/

open Filter MeasureTheory Set
open scoped Topology
open BGW.MetricMeasure

namespace BGW.PlaneTree

/-- The time change `s ↦ min 1 (s ζ/(ζ-1))` turning the library's time scale `2(ζ-1)` into the
paper's `2ζ` (for the singleton tree the factor is `0`, harmless since the contour is `0`). -/
noncomputable def paperTimeChange (t : PlaneTree) : C(unitInterval, unitInterval) where
  toFun s := Set.projIcc 0 1 zero_le_one
    ((s : ℝ) * ((t.size : ℝ) / ((t.size - 1 : ℕ) : ℝ)))
  continuous_toFun := by fun_prop

/-- The contour in the paper's time convention, `s ↦ C_{2ζ s}` (L4). -/
noncomputable def paperContourFunction (t : PlaneTree) : C(unitInterval, ℝ) :=
  t.contourFunction.comp t.paperTimeChange

/-- The time change moves points by at most `1/ζ`. -/
theorem abs_paperTimeChange_sub_le (t : PlaneTree) (s : unitInterval) :
    |((t.paperTimeChange s : unitInterval) : ℝ) - (s : ℝ)| ≤ 1 / (t.size : ℝ) := sorry

/-- The paper contour vanishes on the last `1/ζ` of the time interval. -/
theorem paperContourFunction_eq_zero (t : PlaneTree) (s : unitInterval)
    (hs : ((t.size - 1 : ℕ) : ℝ) / (t.size : ℝ) ≤ (s : ℝ)) :
    t.paperContourFunction s = 0 := sorry

/-- Deterministic uniform bound (L4): if the divided library contour has oscillation `≤ ε` at
scale `1/ζ`, the two conventions are `ε`-close after division by `b`. -/
theorem norm_paperContourFunction_sub_le (t : PlaneTree) (b ε : ℝ)
    (hosc : ∀ s s' : unitInterval, |(s : ℝ) - (s' : ℝ)| ≤ 1 / (t.size : ℝ) →
      |(b⁻¹ • t.contourFunction) s - (b⁻¹ • t.contourFunction) s'| ≤ ε) :
    ‖b⁻¹ • t.paperContourFunction - b⁻¹ • t.contourFunction‖ ≤ ε := sorry

/-- Deterministic form with the modulus of continuity of an arbitrary compact set `K` of
limit-candidate contours: on `K`, scaled contours with `1/ζ ≤ δ` are `ε`-close in the two
conventions. -/
theorem exists_size_bound_norm_paper_sub_le (K : Set C(unitInterval, ℝ)) (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ (t : PlaneTree) (b : ℝ), R ≤ (t.size : ℝ) → b⁻¹ • t.contourFunction ∈ K →
      ‖b⁻¹ • t.paperContourFunction - b⁻¹ • t.contourFunction‖ ≤ ε := sorry

/-- Symmetric form (audit finding): the same bound when the paper contour lies in the compact
set; used by the transfer from the paper convention to the library convention. -/
theorem exists_size_bound_norm_paper_sub_le' (K : Set C(unitInterval, ℝ)) (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ (t : PlaneTree) (b : ℝ), R ≤ (t.size : ℝ) → b⁻¹ • t.paperContourFunction ∈ K →
      ‖b⁻¹ • t.paperContourFunction - b⁻¹ • t.contourFunction‖ ≤ ε := sorry

end BGW.PlaneTree

namespace BGW.ContinuumTrees.FiniteTree

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- Law-level transfer (L4), library convention → paper convention: if the tree sizes tend to
infinity in probability and the divided library contours converge in law to `ν`, so do the
divided paper contours. (The converse, with the roles exchanged, holds by the same proof.) -/
theorem tendsto_map_paperContour_of_tendsto_map_contour
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n))
    (t : (n : ℕ) → Ω n → PlaneTree) (b : ℕ → ℝ) (hb : ∀ n, 0 < b n)
    (hF : ∀ n, Measurable (fun ω : Ω n => (b n)⁻¹ • (t n ω).paperContourFunction))
    (hG : ∀ n, Measurable (fun ω : Ω n => (b n)⁻¹ • (t n ω).contourFunction))
    (hsize : ∀ R : ℝ, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | ((t n ω).size : ℝ) < R}) atTop (𝓝 0))
    {ν : ProbabilityMeasure C(unitInterval, ℝ)}
    (hlim : Tendsto (fun n => (μ n).map
      (fun ω : Ω n => (b n)⁻¹ • (t n ω).contourFunction)) atTop (𝓝 ν)) :
    Tendsto (fun n => (μ n).map
      (fun ω : Ω n => (b n)⁻¹ • (t n ω).paperContourFunction)) atTop (𝓝 ν) := sorry

/-- Law-level transfer (L4), paper convention → library convention: the form consumed by
`tendsto_rooted_laws_of_contour` when the contour input is stated as in the paper. -/
theorem tendsto_map_contour_of_tendsto_map_paperContour
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n))
    (t : (n : ℕ) → Ω n → PlaneTree) (b : ℕ → ℝ) (hb : ∀ n, 0 < b n)
    (hF : ∀ n, Measurable (fun ω : Ω n => (b n)⁻¹ • (t n ω).paperContourFunction))
    (hG : ∀ n, Measurable (fun ω : Ω n => (b n)⁻¹ • (t n ω).contourFunction))
    (hsize : ∀ R : ℝ, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | ((t n ω).size : ℝ) < R}) atTop (𝓝 0))
    {ν : ProbabilityMeasure C(unitInterval, ℝ)}
    (hlim : Tendsto (fun n => (μ n).map
      (fun ω : Ω n => (b n)⁻¹ • (t n ω).paperContourFunction)) atTop (𝓝 ν)) :
    Tendsto (fun n => (μ n).map
      (fun ω : Ω n => (b n)⁻¹ • (t n ω).contourFunction)) atTop (𝓝 ν) := sorry

/-- The size-divergence hypothesis follows from the divisor-to-size tails of
`tendsto_rooted_laws_of_contour` once the divisor tends to infinity. -/
theorem tendsto_real_size_lt_of_ratio
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n))
    (t : (n : ℕ) → Ω n → PlaneTree) (b : ℕ → ℝ) (hb : ∀ n, 0 < b n)
    (hbinfty : Tendsto b atTop atTop)
    (hratio : ∀ r > 0, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | r < b n / ((t n ω).size : ℝ)}) atTop (𝓝 0)) (R : ℝ) :
    Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | ((t n ω).size : ℝ) < R}) atTop (𝓝 0) := sorry

/-! ### L5: measurability hypotheses `hF`, `hG`

`PlaneTree` is countable and carries no global `MeasurableSpace`; random trees are measurable
for the explicit `⊤` σ-algebra, equivalently when every fibre `t ⁻¹' {τ}` is measurable. -/

/-- Measurability for `⊤` on `PlaneTree` is measurability of the fibres of singletons. -/
theorem measurable_top_of_measurableSet_fibre {X : Type*} [MeasurableSpace X]
    (t : X → PlaneTree) (ht : ∀ τ : PlaneTree, MeasurableSet (t ⁻¹' {τ})) :
    @Measurable X PlaneTree _ ⊤ t := sorry

/-- Any function of a `⊤`-measurable random tree is measurable (so `hF`, `hG` hold for every
tree observable). -/
theorem measurable_comp_of_top {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (t : X → PlaneTree) (ht : @Measurable X PlaneTree _ ⊤ t) (f : PlaneTree → Y) :
    Measurable (fun x => f (t x)) := sorry

/-- Hypothesis `hG` of `tendsto_rooted_laws_of_contour`. -/
theorem measurable_contour_of_top (t : Ω n → PlaneTree) (b : ℝ)
    (ht : @Measurable (Ω n) PlaneTree _ ⊤ t) :
    Measurable (fun ω : Ω n => b⁻¹ • (t ω).contourFunction) := sorry

/-- Hypothesis `hG` in the paper's time convention. -/
theorem measurable_paperContour_of_top (t : Ω n → PlaneTree) (b : ℝ)
    (ht : @Measurable (Ω n) PlaneTree _ ⊤ t) :
    Measurable (fun ω : Ω n => b⁻¹ • (t ω).paperContourFunction) := sorry

/-- Hypothesis `hF` of `tendsto_rooted_laws_of_contour`. -/
theorem measurable_rootedMeasuredGHSpace_of_top (t : Ω n → PlaneTree) {b : ℝ} (hb : 0 < b)
    (ht : @Measurable (Ω n) PlaneTree _ ⊤ t) :
    Measurable (fun ω : Ω n =>
      RootedMeasuredGHSpace.scale b⁻¹ (inv_pos.mpr hb)
        (toRootedMeasuredGHSpace (rootedCompactMeasuredSpace (t ω)))) := sorry

/-! ### L6: the deterministic divisor of Remark 5.10

`N n` is the (deterministic) number of leaves, `B n` the stable normalizer, `μ₀ > 0` the offspring
mean parameter of the paper, `θ > 0` the stability index; `b n = N n / (μ₀^(1-1/θ) B n)`. -/

/-- The divisor of Remark 5.10. -/
noncomputable def remarkDivisor (μ₀ θ : ℝ) (N : ℕ → ℕ) (B : ℕ → ℝ) (n : ℕ) : ℝ :=
  (N n : ℝ) / (μ₀ ^ (1 - 1 / θ) * B n)

/-- The divisor is positive. -/
theorem remarkDivisor_pos {μ₀ θ : ℝ} (hμ₀ : 0 < μ₀) {N : ℕ → ℕ} {B : ℕ → ℝ}
    (hN : ∀ n, 0 < N n) (hB : ∀ n, 0 < B n) (n : ℕ) :
    0 < remarkDivisor μ₀ θ N B n := sorry

/-- The divisor tends to infinity when `B n = o(N n)`. -/
theorem tendsto_remarkDivisor_atTop {μ₀ θ : ℝ} (hμ₀ : 0 < μ₀) {N : ℕ → ℕ} {B : ℕ → ℝ}
    (hN : ∀ n, 0 < N n) (hB : ∀ n, 0 < B n) (hNB : Tendsto (fun n => B n / (N n : ℝ)) atTop (𝓝 0)) :
    Tendsto (remarkDivisor μ₀ θ N B) atTop atTop := sorry

/-- The ratio hypothesis of `tendsto_rooted_laws_of_contour` for the divisor of Remark 5.10:
if `B n → ∞` and the number of vertices is at least `c N n` with probability tending to one for
each `c < 1/μ₀` (law of large numbers for the vertex/leaf ratio), then
`P(r < b_n/ζ_n) → 0` for every `r > 0`, because `b_n/ζ ≈ μ₀^{1/θ}/B_n`. -/
theorem tendsto_ratio_remarkDivisor
    {μ₀ θ : ℝ} (hμ₀ : 0 < μ₀) {N : ℕ → ℕ} {B : ℕ → ℝ}
    (hN : ∀ n, 0 < N n) (hB : ∀ n, 0 < B n) (hBinfty : Tendsto B atTop atTop)
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n)) (t : (n : ℕ) → Ω n → PlaneTree)
    (hsize : ∀ c : ℝ, 0 < c → c < 1 / μ₀ → Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | ((t n ω).size : ℝ) < c * (N n : ℝ)}) atTop (𝓝 0)) (r : ℝ) (hr : 0 < r) :
    Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | r < remarkDivisor μ₀ θ N B n / ((t n ω).size : ℝ)}) atTop (𝓝 0) := sorry

end BGW.ContinuumTrees.FiniteTree
