import BGW.Probability.RealWalk
import BGW.StableTrees.Attraction.Defs
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov

/-! Contract probe for CT.C16/C17 route, blueprint Node 6 (audit corrections 1 and 7): the real
Ottaviani (first-exit) maximal inequality for iid real walks, small-block maximum estimates from
scalar attraction and the Node 5 normalizer bounds, compact containment on a finite horizon, and
uniform tightness of `S_j / B_n`, `j ≤ n`, via `isTightMeasureSet_of_isCompact_closure`.
`maxTail ν m r` is the genuine maximum probability `P(max_{k ≤ m} |S_k| > r)`.
Maintained file: `BGW/Probability/RealWalkMaximal.lean` (the Ottaviani part, namespace
`BGW.Probability.RealWalk`) and `BGW/StableTrees/RealAttraction.lean` (the attraction part,
namespace `BGW.StableTrees`). -/

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

-- copied from contract CT5_NormalizerBounds (not part of this contract)
theorem IsRealStableAttracted.tendsto_norming_atTop {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) : Tendsto B atTop atTop := sorry

-- copied from contract CT5_NormalizerBounds (not part of this contract)
theorem IsRealStableAttracted.small_index_ratio {ν : ProbabilityMeasure ℝ} {θ : ℝ} {B : ℕ → ℝ}
    (h : IsRealStableAttracted ν θ B) :
    ∀ ε > 0, ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ m : ℕ,
      1 ≤ m → (m : ℝ) ≤ δ * n + 2 → |B m / B n| ≤ ε := sorry

-- copied from contract CT5_NormalizerBounds (not part of this contract)
theorem IsRealStableAttracted.bounded_index_ratio {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) (A : ℝ) :
    ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ m : ℕ,
      1 ≤ m → (m : ℝ) ≤ A * n + 2 → |B m / B n| ≤ C := sorry

end BGW.StableTrees

/-! ## The contract: Ottaviani for real iid walks -/

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
