import BGW.StableTrees.Defs
import BGW.LocallyFinite.Extinction
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Contract probe for CT8 node K10 (`r5-ct8-blueprint/blueprint.md` K10): the uniform survival
estimate for critical BGW trees in the stable domain, the discrete extinction condition used by
the height-tightness argument (K11, Duquesne-Le Gall 2002, Ch. 2).

DEFINITIONS.  `realGF μ s = ∑ μ(k) s^k` (used on `[0,1]`).  `survivalProb μ k` is the BGW
probability that the tree has a vertex at depth `≥ k` (the complement of the sealed
`LocallyFinite.extinctBy k`), i.e. generation `k` is nonempty; `survivalProb μ 0 = 1` and
`survivalProb μ 1 = 1 - μ 0`.  `csbpSurvival θ δ = ((θ-1)δ)^(-1/(θ-1))` is the survival function
of the `ψ(λ) = λ^θ` continuous-state branching process (the solution of `v' = -v^θ`,
`v(0+) = ∞`).

TRUTH CHECK.  (1) Recursion: sealed `bienaymeLaw_extinctBy` gives `P(extinctBy k) = g^[k](0)`,
so `s(k+1) = 1 - g(1 - s(k))`.  (2) Expansion: `StableDomain μ θ B` means
`E exp(-λ S_n/B_n) → exp(λ^θ)` along the scalar weak limit; for a critical law with steps
`≥ -1` this yields `n (g(1-λ/B_n) - (1-λ/B_n)) → λ^θ`.  Finite variance `σ²`, `θ = 2`: the
library normalization (`exp(λ²)`, variance 2) gives `B_n = σ √(n/2)` and both sides equal
`n σ² λ² / (2 B_n²) = λ²`.  (3) Survival: with `x_j = B_n s(j)` the recursion reads
`x_{j+1} = x_j - B_n ψ_g(x_j / B_n)`, `ψ_g(u) = g(1-u) - (1-u) ≈ u^θ/n` at `u ≍ 1/B_n`, so over
`k ≈ δ n / B_n` generations `x` follows `dx/dt = -x^θ` from `x_0 = B_n → ∞`: the limit is
`v(δ) = ((θ-1)δ)^(-1/(θ-1))`.  Check `θ = 2`, finite variance: Kolmogorov `s(k) ~ 2/(σ² k)`
gives `B_n s(δ n/B_n) → 2 B_n² / (σ² δ n) = 1/δ = v(δ)`.  (4) Consequences: `⌊a B_n⌋ s(k_n) →
a v(δ)` and `(1 - s(k_n))^⌊a B_n⌋ → exp(-a v(δ))`; with `a = 1` this is DLG's extinction
condition `liminf (g^[⌊δ n/B_n⌋](0))^⌊B_n⌋ > 0`.

PROOF PLAN.  (a) `tendsto_realGF_expansion`: from the scalar attraction, derive the Laplace
asymptotics `n (φ(λ/B_n) - 1) → λ^θ` for the step transform (sealed
`Attraction.LaplaceExpansion`, `Attraction.TransformConvergence`, `Attraction.DomainCriterion`,
`TailTransfer`, `RealAttraction`; bounded-below increments alone do not make the unbounded
exponential tests converge: use the regular-variation suppliers), then compare
`e^u g(e^{-u}) - 1` with `g(1-u) - (1-u)` (difference `o(1/n)` at `u = λ/B_n`, including the
`θ = 2` case with slowly varying truncated second moment).  Prove it locally uniformly in
`λ ∈ [a, b] ⊂ (0, ∞)` as a helper (monotonicity in `λ` + continuity of `λ^θ` gives this from
pointwise convergence, Dini/Pólya).  (b) Compare the recursion with the integral
`∫ du / ψ_g(u)` (Potter bounds on the regularly varying `ψ_g`) to obtain
`tendsto_survivalProb_scaled`; `survivalProb` is antitone, so the floor sequence and general
`k_n` follow from one another.  (c) Elementary corollaries.  This avoids importing Slack's
theorem or a constructed CSBP.  Size 1000-1900 lines.

ACYCLICITY.  Suppliers: sealed scalar attraction (`Defs`, `Attraction/*`, `RealAttraction`) and
`LocallyFinite.Extinction`.  No CT7 or CT8 height node, no K09/K11.

BINDER SCOPE (AUDITOR_RULES): the only big operator is the `∑'` in `realGF`, whose body is the
whole product `(μ k).toReal * s ^ k`; nothing follows it. -/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace BGW.StableTrees.Survival

/-- The real offspring generating function `g(s) = ∑ μ(k) s^k`.  It is used on `[0,1]`, where
the series converges. -/
noncomputable def realGF (μ : PMF ℕ) (s : ℝ) : ℝ := ∑' k : ℕ, (μ k).toReal * s ^ k

/-- Survival to generation `k`: the BGW tree has a vertex at depth `≥ k`, i.e. generation `k`
is nonempty.  `survivalProb μ 0 = 1`. -/
noncomputable def survivalProb (μ : PMF ℕ) (k : ℕ) : ℝ :=
  (BGW.LocallyFinite.bienaymeLaw μ.toMeasure).real (BGW.LocallyFinite.extinctBy k)ᶜ

/-- The survival function `v(δ) = ((θ-1) δ)^(-1/(θ-1))` of the continuous-state branching
process with branching mechanism `λ^θ` (solution of `v' = -v^θ` with `v(0+) = ∞`). -/
noncomputable def csbpSurvival (θ δ : ℝ) : ℝ := ((θ - 1) * δ) ^ (-1 / (θ - 1))

/-! ### Discrete recursion -/

/-- Survival in terms of the iterated generating function. -/
theorem survivalProb_eq_one_sub_iterate (μ : PMF ℕ) (k : ℕ) :
    survivalProb μ k = 1 - ((BGW.offspringGF μ.toMeasure)^[k] 0).toReal := sorry

theorem survivalProb_zero (μ : PMF ℕ) : survivalProb μ 0 = 1 := sorry

/-- The survival recursion `s(k+1) = 1 - g(1 - s(k))`. -/
theorem survivalProb_succ (μ : PMF ℕ) (k : ℕ) :
    survivalProb μ (k + 1) = 1 - realGF μ (1 - survivalProb μ k) := sorry

theorem survivalProb_mem_Icc (μ : PMF ℕ) (k : ℕ) : survivalProb μ k ∈ Set.Icc (0 : ℝ) 1 := sorry

theorem antitone_survivalProb (μ : PMF ℕ) : Antitone (survivalProb μ) := sorry

/-- Critical non-degenerate trees are almost surely finite. -/
theorem tendsto_survivalProb_zero {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    Tendsto (survivalProb μ) atTop (𝓝 0) := sorry

/-! ### Generating-function expansion at the stable scale -/

/-- `n (g(1 - λ/B_n) - (1 - λ/B_n)) → λ^θ` for every `λ > 0`. -/
theorem tendsto_realGF_expansion {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => (n : ℝ) * (realGF μ (1 - lam / B n) - (1 - lam / B n))) atTop
      (𝓝 (lam ^ θ)) := sorry

/-! ### Growth of the norming sequence -/

/-- `B_n / n → 0` (regular variation of index `1/θ < 1`). -/
theorem tendsto_B_div_n {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B) :
    Tendsto (fun n : ℕ => B n / n) atTop (𝓝 0) := sorry

/-- `B_n → ∞`. -/
theorem tendsto_B_atTop {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B) :
    Tendsto B atTop atTop := sorry

/-- The floor index `k_n = ⌊δ n / B_n⌋` satisfies `k_n B_n / n → δ`. -/
theorem tendsto_floor_scale {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => (⌊δ * (n : ℝ) / B n⌋₊ : ℝ) * B n / n) atTop (𝓝 δ) := sorry

/-! ### Survival estimate -/

/-- **Survival at the height scale.**  If `k_n B_n / n → δ > 0`, then
`B_n s(k_n) → ((θ-1) δ)^(-1/(θ-1))`. -/
theorem tendsto_survivalProb_scaled {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {δ : ℝ} (hδ : 0 < δ) {k : ℕ → ℕ}
    (hk : Tendsto (fun n : ℕ => (k n : ℝ) * B n / n) atTop (𝓝 δ)) :
    Tendsto (fun n : ℕ => B n * survivalProb μ (k n)) atTop (𝓝 (csbpSurvival θ δ)) := sorry

/-- The floor form `k_n = ⌊δ n / B_n⌋`. -/
theorem tendsto_survivalProb_floor {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => B n * survivalProb μ ⌊δ * (n : ℝ) / B n⌋₊) atTop
      (𝓝 (csbpSurvival θ δ)) := sorry

/-- The blueprint's uniform bound. -/
theorem survival_bound {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C, 0 < C ∧ ∀ᶠ n in atTop, B n * survivalProb μ ⌊δ * (n : ℝ) / B n⌋₊ ≤ C := sorry

/-- `⌊a B_n⌋` independent trees: expected number reaching height `k_n` tends to `a v(δ)`. -/
theorem tendsto_floor_mul_survivalProb {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {δ : ℝ} (hδ : 0 < δ) {k : ℕ → ℕ}
    (hk : Tendsto (fun n : ℕ => (k n : ℝ) * B n / n) atTop (𝓝 δ)) {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (⌊a * B n⌋₊ : ℝ) * survivalProb μ (k n)) atTop
      (𝓝 (a * csbpSurvival θ δ)) := sorry

/-- **Extinction condition** (DLG): `⌊a B_n⌋` independent trees all die before generation
`k_n` with probability tending to `exp(-a v(δ))`. -/
theorem tendsto_extinction_pow {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {δ : ℝ} (hδ : 0 < δ) {k : ℕ → ℕ}
    (hk : Tendsto (fun n : ℕ => (k n : ℝ) * B n / n) atTop (𝓝 δ)) {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (1 - survivalProb μ (k n)) ^ ⌊a * B n⌋₊) atTop
      (𝓝 (Real.exp (-(a * csbpSurvival θ δ)))) := sorry

/-- Floor form of `tendsto_floor_mul_survivalProb` (the K11 union bound). -/
theorem tendsto_floor_mul_survivalProb_floor {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {δ : ℝ} (hδ : 0 < δ) {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (⌊a * B n⌋₊ : ℝ) * survivalProb μ ⌊δ * (n : ℝ) / B n⌋₊) atTop
      (𝓝 (a * csbpSurvival θ δ)) := sorry

/-- Floor form of `tendsto_extinction_pow`; `a = 1` is DLG's extinction condition. -/
theorem tendsto_extinction_pow_floor {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {δ : ℝ} (hδ : 0 < δ) {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (1 - survivalProb μ ⌊δ * (n : ℝ) / B n⌋₊) ^ ⌊a * B n⌋₊) atTop
      (𝓝 (Real.exp (-(a * csbpSurvival θ δ)))) := sorry

end BGW.StableTrees.Survival
