namespace BGW.Probability.RealWalk

/-- The finite-horizon exceedance event `{∃ k ≤ m, r < |S_k|}`. -/
def maxExceed (m : ℕ) (r : ℝ) : Set (ℕ → ℝ) := {ω | ∃ k ≤ m, r < |partialSum ω k|}

theorem measurableSet_maxExceed (m : ℕ) (r : ℝ) : MeasurableSet (maxExceed m r) := sorry

/-- `maxTail ν m r = P(max_{k ≤ m} |S_k| > r)`: the genuine maximum probability, not a supremum
of marginal probabilities. (`k = 0` is included, with `S_0 = 0`; so `maxTail ν m r = 1` for
`r < 0`.) -/
noncomputable def maxTail (ν : ProbabilityMeasure ℝ) (m : ℕ) (r : ℝ) : ℝ :=
  (iidLaw ν : Measure (ℕ → ℝ)).real (maxExceed m r)

theorem maxTail_nonneg (ν : ProbabilityMeasure ℝ) (m : ℕ) (r : ℝ) : 0 ≤ maxTail ν m r := sorry

theorem maxTail_le_one (ν : ProbabilityMeasure ℝ) (m : ℕ) (r : ℝ) : maxTail ν m r ≤ 1 := sorry

/-- Monotone in the length. -/
theorem maxTail_mono_length (ν : ProbabilityMeasure ℝ) {m m' : ℕ} (h : m ≤ m') (r : ℝ) :
    maxTail ν m r ≤ maxTail ν m' r := sorry

/-- Antitone in the threshold. -/
theorem maxTail_anti_threshold (ν : ProbabilityMeasure ℝ) (m : ℕ) {r r' : ℝ} (h : r ≤ r') :
    maxTail ν m r' ≤ maxTail ν m r := sorry

/-- Block translation: the maximum of `|S_{a+k} - S_a|`, `k ≤ m`, has the same exceedance
probability as the walk started at `0` (fresh start at the deterministic index `a`). -/
theorem measureReal_exceed_block (ν : ProbabilityMeasure ℝ) (a m : ℕ) (r : ℝ) :
    (iidLaw ν : Measure (ℕ → ℝ)).real {ω | ∃ k ≤ m, r < |blockSum ω a k|} = maxTail ν m r :=
  sorry

/-- Ottaviani's maximal inequality for real iid sums (Node 6). If every partial sum `S_j`,
`j ≤ m`, lies in `[-r, r]` with probability `≥ 1/2` (the "safe remainder" hypothesis, applied to
the independent remainder `S_m - S_k` of length `m - k ≤ m`), then
`P(max_{k ≤ m} |S_k| > 2 r) ≤ 2 P(|S_m| > r)`. -/
theorem maximal_le_two_mul_tail (ν : ProbabilityMeasure ℝ) (m : ℕ) (r : ℝ)
    (hsafe : ∀ j ≤ m, (1 / 2 : ℝ) ≤ (sumLaw ν j : Measure ℝ).real {x | |x| ≤ r}) :
    maxTail ν m (2 * r) ≤ 2 * (sumLaw ν m : Measure ℝ).real {x | r < |x|} := sorry

end BGW.Probability.RealWalk