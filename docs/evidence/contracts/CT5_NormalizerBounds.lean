import BGW.Probability.RealWalk
import BGW.StableTrees.Attraction.Defs
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Contract probe for CT.C16/C17 route, blueprint Node 5 (audit corrections 1 and 7): divergence
of the normalizer, Potter-type bounds and uniformly small index ratios for an arbitrary real
attracted walk, WITHOUT monotonicity of `B` (the proof is the dyadic argument on top of the
uniform ratio theorem of Node 4, by sequential compactness). `B m` is only eventually positive,
so every ratio estimate is stated for `n ≥ N` (where `B n > 0`) and, for the index `m`, with an
absolute value (finitely many small `m` may have `B m ≤ 0`; they are absorbed by `B n → ∞`).
Maintained file: `BGW/StableTrees/RealAttraction.lean` (namespace `BGW.StableTrees`). -/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-! ## Copied declarations (not part of this contract) -/

namespace BGW.StableTrees

open BGW.Probability.RealWalk

-- copied from contract CT4_StableLaw (not part of this contract)
noncomputable def stableLaw (θ : ℝ) : ProbabilityMeasure ℝ :=
  if hθ : 1 < θ ∧ θ ≤ 2 then
    ⟨volume.withDensity (fun x => ENNReal.ofReal (Scalar.stableDensity θ x)), sorry⟩
  else ⟨Measure.dirac 0, inferInstance⟩

-- copied from contract CT5_Normalizer (not part of this contract)
structure IsRealStableAttracted (ν : ProbabilityMeasure ℝ) (θ : ℝ) (B : ℕ → ℝ) : Prop where
  index_mem : 1 < θ ∧ θ ≤ 2
  pos : ∀ᶠ n in atTop, 0 < B n
  converges : Tendsto (fun n => scaledSumLaw ν B n) atTop (𝓝 (stableLaw θ))

-- copied from contract CT5_Normalizer (not part of this contract)
theorem IsRealStableAttracted.tendsto_norming_ratio {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {m q : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hq : Tendsto q atTop atTop)
    (hmq : Tendsto (fun j => (m j : ℝ) / q j) atTop (𝓝 c)) :
    Tendsto (fun j => B (m j) / B (q j)) atTop (𝓝 (c ^ (1 / θ))) := sorry

/-! ## The contract -/

/-- The normalizer diverges: `B n → +∞` (Node 5; dyadic halving with `B_{⌊n/2⌋}/B_n → 2^{-1/θ} < 1`,
since `1/θ > 0`). No monotonicity is used. -/
theorem IsRealStableAttracted.tendsto_norming_atTop {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) : Tendsto B atTop atTop := sorry

/-- Uniform convergence of the ratio on compact index ranges (the uniform form of Node 4,
via sequential compactness): for `0 < a ≤ b` and `ε > 0`, eventually in `n`, all indices
`m ∈ [a n, b n]` satisfy `|B m / B n - (m/n)^{1/θ}| ≤ ε`. -/
theorem IsRealStableAttracted.uniform_ratio {ν : ProbabilityMeasure ℝ} {θ : ℝ} {B : ℕ → ℝ}
    (h : IsRealStableAttracted ν θ B) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ m : ℕ, a * n ≤ m → (m : ℝ) ≤ b * n →
      |B m / B n - ((m : ℝ) / n) ^ (1 / θ)| ≤ ε := sorry

/-- Potter-type upper bound without monotonicity: for every `ε' > 0` and every `A > 1`, for
all large indices `m, n` (both `≥ N`), `B m / B n ≤ A * max ((m/n)^(1/θ + ε')) ((m/n)^(1/θ - ε'))`. -/
theorem IsRealStableAttracted.potter_upper {ν : ProbabilityMeasure ℝ} {θ : ℝ} {B : ℕ → ℝ}
    (h : IsRealStableAttracted ν θ B) {ε' A : ℝ} (hε' : 0 < ε') (hA : 1 < A) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      B m / B n ≤ A * max (((m : ℝ) / n) ^ (1 / θ + ε')) (((m : ℝ) / n) ^ (1 / θ - ε')) := sorry

/-- Potter-type lower bound: same hypotheses, `B m / B n ≥ A⁻¹ * min (…) (…)`. -/
theorem IsRealStableAttracted.potter_lower {ν : ProbabilityMeasure ℝ} {θ : ℝ} {B : ℕ → ℝ}
    (h : IsRealStableAttracted ν θ B) {ε' A : ℝ} (hε' : 0 < ε') (hA : 1 < A) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      A⁻¹ * min (((m : ℝ) / n) ^ (1 / θ + ε')) (((m : ℝ) / n) ^ (1 / θ - ε')) ≤ B m / B n :=
  sorry

/-- Uniformly small ratios for small positive indices (Node 5), in absolute value: the blueprint's
one-sided `B m / B n ≤ ε` is strengthened to `|B m / B n| ≤ ε` (still true: finitely many `m`
with `B m ≤ 0` are bounded and `B n → ∞`). The index `m = 0` is excluded; the additive `2`
absorbs floors. -/
theorem IsRealStableAttracted.small_index_ratio {ν : ProbabilityMeasure ℝ} {θ : ℝ} {B : ℕ → ℝ}
    (h : IsRealStableAttracted ν θ B) :
    ∀ ε > 0, ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ m : ℕ,
      1 ≤ m → (m : ℝ) ≤ δ * n + 2 → |B m / B n| ≤ ε := sorry

/-- Bounded ratios on finite time windows (Node 5), in absolute value. -/
theorem IsRealStableAttracted.bounded_index_ratio {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) (A : ℝ) :
    ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ m : ℕ,
      1 ≤ m → (m : ℝ) ≤ A * n + 2 → |B m / B n| ≤ C := sorry

end BGW.StableTrees
