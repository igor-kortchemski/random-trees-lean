

/-! ## The contract: consequences of attraction -/

namespace BGW.StableTrees

open BGW.Probability.RealWalk

/-- The whole sequence of scaled sum laws is uniformly tight (a convergent sequence in the space
of probability measures on `ℝ` has compact closure; Mathlib's
`isTightMeasureSet_of_isCompact_closure`). This absorbs the finite beginning of the sequence. -/
theorem IsRealStableAttracted.isTightMeasureSet_scaledSumLaw {ν : ProbabilityMeasure ℝ}
    {θ : ℝ} {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) :
    IsTightMeasureSet (Set.range fun n => (scaledSumLaw ν B n : Measure ℝ)) := sorry

/-- Uniform tightness of `S_j / B_n`, `j ≤ n` (audit item 7), quantitative form: the exceedance
probability of the level `K B n` is small, for all `j ≤ n` simultaneously, once `n` is large. -/
theorem IsRealStableAttracted.uniform_tight_partial_sums {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) :
    ∀ η > 0, ∃ K > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ j ≤ n,
      (sumLaw ν j : Measure ℝ).real {x | K * B n < |x|} ≤ η := sorry

/-- The family `{law of S_j / B_n : j ≤ n}` over all `n` is tight (as a set of measures). The
finitely many `n` with small `N` contribute finitely many tight laws; `B n ≤ 0` is harmless
because the division by `B n` is then still a measurable map and each law is a single tight law. -/
theorem IsRealStableAttracted.isTightMeasureSet_scaled_partial_sums {ν : ProbabilityMeasure ℝ}
    {θ : ℝ} {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) :
    IsTightMeasureSet {μ : Measure ℝ | ∃ n j : ℕ, j ≤ n ∧
      μ = (sumLaw ν j : Measure ℝ).map (fun x => x / B n)} := sorry

/-- Small-block maxima (Node 6): maxima over blocks of length `≤ δ n + 2` exceed `ε B n` with
probability at most `η`, uniformly for large `n`. The threshold is `ε * B n` for `B n > 0`
(eventually). Proof: Ottaviani at half the threshold, with the safe-remainder hypothesis from
`small_index_ratio` and tightness of the full scaled sequence. -/
theorem IsRealStableAttracted.small_block_max {ν : ProbabilityMeasure ℝ} {θ : ℝ} {B : ℕ → ℝ}
    (h : IsRealStableAttracted ν θ B) :
    ∀ ε > 0, ∀ η > 0, ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ m : ℕ,
      (m : ℝ) ≤ δ * n + 2 → maxTail ν m (ε * B n) ≤ η := sorry

/-- Compact containment on a finite horizon (Node 6): maxima up to `⌊n T⌋₊` stay below
`K * B n` with probability at least `1 - η`, for all large `n`. -/
theorem IsRealStableAttracted.horizon_max_tight {ν : ProbabilityMeasure ℝ} {θ : ℝ} {B : ℕ → ℝ}
    (h : IsRealStableAttracted ν θ B) {T : ℝ} (hT : 0 < T) :
    ∀ η > 0, ∃ K > 0, ∃ N : ℕ, ∀ n ≥ N, maxTail ν ⌊(n : ℝ) * T⌋₊ (K * B n) ≤ η := sorry

end BGW.StableTrees
