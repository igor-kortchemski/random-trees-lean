import BGW.Probability.RealWalk
import BGW.Skorokhod.ExitPartition
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Contract probe for CT.C16/C17 route, blueprint Node 7 split as in audit correction 6.

* **7a** (exit times): the restart exit times `exitTimes M r ω j` of `BGW.Skorokhod.ExitPartition`
  are measurable, strictly increasing while actual, and each event `{exitTimes j = k}` with
  `k ≤ M` is determined by the first `k` coordinates (this is what makes fresh-block independence
  at the deterministic index `k` suffice; no strong Markov theorem is needed).
* **7b** (expected count and close pairs): `E[exitCount] ≤ 2 (M/L + 1)` when
  `maxTail ν L r ≤ 1/2`, and `P(closeExit) ≤ E[exitCount] * maxTail ν l r`.

Existing compiled definitions are imported (`nextExit`, `exitTimes`, `exitCount`, `closeExit`).
Maintained files: `BGW/Probability/RealWalkExits.lean` (7a) and
`BGW/Probability/RealWalkExitCount.lean` (7b), namespace `BGW.Probability.RealWalk`. -/

open MeasureTheory ProbabilityTheory Filter

/-! ## Copied declarations (not part of this contract) -/

namespace BGW.Probability.RealWalk

-- copied from contract CT5_Ottaviani (not part of this contract)
def maxExceed (m : ℕ) (r : ℝ) : Set (ℕ → ℝ) := {ω | ∃ k ≤ m, r < |partialSum ω k|}

-- copied from contract CT5_Ottaviani (not part of this contract)
noncomputable def maxTail (ν : ProbabilityMeasure ℝ) (m : ℕ) (r : ℝ) : ℝ :=
  (iidLaw ν : Measure (ℕ → ℝ)).real (maxExceed m r)

/-! ## 7a: exit times -/

/-- `nextExit M r · a` is measurable (the codomain `ℕ` carries the discrete σ-algebra). -/
theorem measurable_nextExit (M : ℕ) (r : ℝ) (a : ℕ) :
    Measurable fun ω : ℕ → ℝ => nextExit M r ω a := sorry

theorem measurable_exitTimes (M : ℕ) (r : ℝ) (j : ℕ) :
    Measurable fun ω : ℕ → ℝ => exitTimes M r ω j := sorry

theorem measurable_exitCount (M : ℕ) (r : ℝ) :
    Measurable fun ω : ℕ → ℝ => exitCount M r ω := sorry

theorem measurableSet_closeExit (M : ℕ) (r : ℝ) (l : ℕ) :
    MeasurableSet {ω : ℕ → ℝ | closeExit M r l ω} := sorry

/-- Exit times are strictly increasing as long as they are actual exits (`≤ M`). -/
theorem exitTimes_lt_succ {M : ℕ} {r : ℝ} {ω : ℕ → ℝ} {j : ℕ} (h : exitTimes M r ω j ≤ M) :
    exitTimes M r ω j < exitTimes M r ω (j + 1) := sorry

/-- Once the sentinel `M + 1` (or anything `> M`) is reached, all later exit times are
the sentinel. -/
theorem exitTimes_eq_sentinel {M : ℕ} {r : ℝ} {ω : ℕ → ℝ} {j : ℕ} (h : M < exitTimes M r ω j)
    {i : ℕ} (hi : 1 ≤ i) : exitTimes M r ω (j + i) = M + 1 := sorry

/-- The number of actual exits is at most `M`. -/
theorem exitCount_le (M : ℕ) (r : ℝ) (ω : ℕ → ℝ) : exitCount M r ω ≤ M := sorry

/-- The exit event `{nextExit a = k}`, `k ≤ M`, depends only on the coordinates `< k`
(because `S_i` for `i ≤ k` involves the coordinates `0, …, k-1`). -/
theorem nextExit_eq_of_prefix_eq {M : ℕ} {r : ℝ} {ω ω' : ℕ → ℝ} {a k : ℕ} (hk : k ≤ M)
    (hω : ∀ i < k, ω i = ω' i) (h : nextExit M r ω a = k) : nextExit M r ω' a = k := sorry

/-- Prefix-determination of the `j`-th exit time: for `k ≤ M`, the event `{exitTimes j = k}` is the
preimage under `prefixVec k` of a measurable set of `Fin k → ℝ`. Fresh-block independence
(`indep_prefix_shift`, `measure_prefix_inter_shift`) then applies at the deterministic index `k`. -/
theorem exists_prefixSet_exitTimes (M : ℕ) (r : ℝ) (j k : ℕ) (hk : k ≤ M) :
    ∃ A : Set (Fin k → ℝ), MeasurableSet A ∧
      {ω : ℕ → ℝ | exitTimes M r ω j = k} = prefixVec k ⁻¹' A := sorry

/-- If the `j`-th exit is at `k ≤ M`, then the `(j+1)`-st exit is a later exit of the shifted walk:
`exitTimes (j+1) = k + i ≤ M` iff the shifted walk's first exit `nextExit (M - k) r (shift k ω) 0`
(for the same radius) is `i ≤ M - k`; the sentinel corresponds to `M - k + 1`. -/
theorem exitTimes_succ_eq_shift {M : ℕ} {r : ℝ} {ω : ℕ → ℝ} {j k : ℕ} (hk : k ≤ M)
    (h : exitTimes M r ω j = k) :
    exitTimes M r ω (j + 1) = k + nextExit (M - k) r (shift k ω) 0 := sorry

/-! ## 7b: expected count and close pairs -/

/-- Expected number of exits (Node 7b): if the walk exceeds radius `r` within `L` steps with
probability at most `1/2`, then `E[exitCount M r] ≤ 2 (M / L + 1)`. Proof: blocks of length `L`;
within a block each further exit has conditional probability `≤ maxTail ν L r ≤ 1/2`
(fresh start at the previous exit), so the number of exits per block is dominated by a geometric
variable with mean `≤ 2`; at most `⌊M/L⌋ + 1 ≤ M/L + 1` blocks. -/
theorem integral_exitCount_le (ν : ProbabilityMeasure ℝ) {M L : ℕ} {r : ℝ} (hr : 0 < r)
    (hL : 1 ≤ L) (hsafe : maxTail ν L r ≤ (1 / 2 : ℝ)) :
    ∫ ω, (exitCount M r ω : ℝ) ∂(iidLaw ν : Measure (ℕ → ℝ)) ≤ 2 * ((M : ℝ) / L + 1) := sorry

/-- Close-pair bound (Node 7b): the probability that two successive actual exits are at most `l`
indices apart is at most `E[exitCount] * maxTail ν l r` (union over the exit number `j ≥ 1`;
at the `j`-th exit, the walk restarted there exceeds `r` within `l` steps with probability at
most `maxTail ν l r`). It is `E[N] q`, not `M q`. -/
theorem measure_closeExit_le (ν : ProbabilityMeasure ℝ) {M : ℕ} {r : ℝ} (hr : 0 < r) (l : ℕ) :
    (iidLaw ν : Measure (ℕ → ℝ)).real {ω | closeExit M r l ω} ≤
      (∫ ω, (exitCount M r ω : ℝ) ∂(iidLaw ν : Measure (ℕ → ℝ))) * maxTail ν l r := sorry

/-- Combination used by Node 9: with the safe block length `L`, the close-pair probability is at
most `2 (M / L + 1) * maxTail ν l r`. -/
theorem measure_closeExit_le_of_safe (ν : ProbabilityMeasure ℝ) {M L : ℕ} {r : ℝ} (hr : 0 < r)
    (hL : 1 ≤ L) (hsafe : maxTail ν L r ≤ (1 / 2 : ℝ)) (l : ℕ) :
    (iidLaw ν : Measure (ℕ → ℝ)).real {ω | closeExit M r l ω} ≤
      2 * ((M : ℝ) / L + 1) * maxTail ν l r := sorry

end BGW.Probability.RealWalk
