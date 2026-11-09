import BGW.StableTrees.WalkPathTightness
import BGW.StableTrees.RealAttraction
import BGW.StableTrees.Scalar.ForestWalkBridge
import BGW.LocallyFinite.ForestWalkLaw
import BGW.StableTrees.ForestLocalLimit
import BGW.Skorokhod.DLoc
import BGW.StableTrees.StableLocalLaw
import BGW.StableTrees.StableProcessLaw
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import BGW.StableTrees.SupremumLocalTimePublic
import BGW.StableTrees.DiscreteForest
import BGW.StableTrees.HeightProcess

/-! Contract probe for CT8 node K09 (discrete height approximation, joint walk/occupation
convergence), following `r5-ct8-blueprint/blueprint.md` K09 and AUDIT finding 2 and the closing
paragraph.  The discrete estimate is stated verbatim as `occupation_error_twoLimit`, with no
renewal-error hypothesis; its suppliers are separate declarations.

TRUTH.  `ω : ℕ → ℕ` is an iid offspring sequence (law `μ`, critical, `μ 1 ≠ 1`), `W_j` its
walk (increments `ω i - 1`), `k = ⌊n t⌋`.  The record-count height is
`H_k = #{j < k | ∀ l ∈ [j,k], W_j ≤ W_l}` (weak records seen from `k`, ties included).
The discrete occupation at mesh `1/n` and level `ε B_n` is
`O^n_ε(t) = (n ε)⁻¹ #{j < k | ∀ l ∈ [j,k], W_j - W_l < ε B_n}`
(`W_j - min_{[j,k]} W < ε B_n`), the exact analogue of `heightApprox ε` (copied below).
Estimate (audit finding 2, blueprint K09):
`lim_{ε↓0} limsup_n P(|(B_n/n) H_k - O^n_ε(t)| > η) = 0`.

NORMALIZATION (constant flagged).  Discrete height is `(B_n / n) · H_{⌊nt⌋}` with no further
constant.  Check at `θ = 2`.  The library variance-2 process is `X = √2 · (Brownian)`
(`ψ(λ)=λ²`, `B_n = σ √(n/2)`, offspring variance `σ²`).  Known: `H_{nt}/√n ⇒ (2/σ)·reflected BM`
and `W_{nt}/√n ⇒ σ·BM`, so `H_k ≈ (2/σ²)(W - I)` and
`(B_n/n) H_k → (σ/√(2n))·(2/σ)√n·R = √2 R = X - I`: constant exactly 1, matching
`ae_height_two` (`H = X - I` at `θ = 2`; blueprint K17: `H = 2(X-I)/v`, `v = 2`).
Occupation side at `θ = 2` (corrected, Sol audit finding 6):
for Brownian Y with quadratic variation v * t, the occupation
normalization at its supremum is (2 / v) * S. Here v = 2, so it is S.
Reversal therefore gives X_t - I_t, consistently with H02 ae_height_two.
The finite-variance example has B_n = σ * sqrt (n / 2);
the θ = 2 contract also covers infinite-variance Gaussian domains.
Discrete-level exact version (the identity the estimate rests
on): reversing at `k`, `H_k` is the number of weak ascending ladder epochs of the walk with
steps `ω-1` (downward skip free) and the occupation count is `#{u ≤ k | M_u - Ŵ_u < a}`
(`M` running maximum).  Per weak-epoch cycle the expected number of visits to each gap level
`y ∈ ℕ` is EXACTLY `1` for every admissible offspring law (Sol audit finding 2).  General
duality argument: the expected visits to gap `y > 0` in the first weak cycle equal
`∑_{n≥1} P(S_n = -y, S_1 < 0, …, S_n < 0)`; reversing the first `n` increments turns the event
into `{S_n = -y, S_n < S_j for all 0 ≤ j < n}`, so the sum is the expected number of strict
descending record epochs at value `-y`.  Downward skip-freeness makes each new strict record
exactly one lower, and criticality plus nondegeneracy give oscillation, so every level `-y` is a
strict descending record exactly once a.s.; for `y = 0` the only visit in `[0, τ)` is time
zero.  Periodic and infinite-variance laws are included; weak (not strict) ascending epochs
are essential; no law-dependent constant.  So the cycle mean is
`⌈a⌉₊` with `a = ε B_n`, giving `count ≈ ⌈ε B_n⌉ H_k`, i.e. `O^n_ε ≈ (B_n/n) H_k`.  Also
consistent with `E[H^w_+] = σ²/2` (Spitzer, `E[H^s_-] = 1`).  FLAG: this exact-mean
statement `clusterLevelMean` is the key normalization supplier; it must be reviewed.

PROOF PLAN.
1. Reversal (deterministic + exchangeability): `H_k = weakLadderCount (revSeq k ω) k`,
   `discreteCount ω k a = bandCount (revSeq k ω) k a`, and `revSeq k` preserves the iid law.
   So all estimates are for the unreversed walk with the weak ascending ladder structure.
2. Cycles: weak epochs `τ_0 = 0 < τ_1 < ...` (finite a.s., critical nondegenerate walk
   oscillates; ties = weak records, time zero = `τ_0`).  Cycle visit counts `V_i(a)` are iid
   (stopped restart at the epochs, as `stoppedRestart` of K02 with `N = τ_i`), with exact mean
   `⌈a⌉₊` (`clusterLevelMean`, then summation over levels).
3. Scale-free second moment (`clusterVisits_secondMoment_scaled`):
   `(B_n/n) E[V(εB_n)²] / (εB_n)² → 0` as `n → ∞` then `ε → 0`.  Green-function/renewal
   argument (Sol audit finding 3; replaces the earlier depth heuristic): the weak ascending
   ladder-height increment `A = S_τ` has `P(A = j) = P(ω_0 ≥ j+1)` (atom at `0` retained, total
   mass one), PGF `φ(s) = (1 - g(s))/(1 - s)`, renewal function
   `W(m) = ∑_{r≥0} P(A_1 + ⋯ + A_r < m)` with generating function `1/(g(s) - s)`.  The killed
   gap walk has Green diagonal `G(y,y) = W(y)` and `G(x,y) ≤ W(y) ≤ W(m)` for `1 ≤ y < m`
   (strong Markov at the first visit to `y`).  With `m = ⌈a⌉₊`, counting ordered pairs of visits
   gives `E[V_0(a)²] ≤ m + 2 (m-1)² W(m)`, which also yields `integrable_clusterVisits_sq`.
   Moreover `W(m) ≤ e / (1 - φ(e^{-1/m})) = e (1 - e^{-1/m}) / (g(e^{-1/m}) - e^{-1/m})`.
   The Laplace bridge `n (g(e^{-λ/B_n}) - e^{-λ/B_n}) → λ^θ` (`norming_offspringPGF_gap`, a
   real obligation from `StableDomain`, not bounded-continuous weak convergence) gives
   `limsup (B_n/n) W(⌈ε B_n⌉) ≤ e ε^{θ-1}` and the scaled second moment `≤ 2 e ε^{θ-1}`, also at
   `θ = 2` with slowly varying factors and no finite-variance hypothesis.
4. Kolmogorov maximal inequality for the iid partial sums over `N ≤ x n/B_n` cycles gives the
   stopped error (`cluster_partialSum_maximal`) uniformly in the cutoff index.
5. Sandwich `Σ_{i<H} V_i - 1 ≤ count ≤ Σ_{i≤H} V_i` (deterministic), the extra cycle controlled by
   the maximal inequality (`max V_i ≤ ...`), and the ceiling error `1/(εB_n)·H_k/n`.
   Reserve one extra cycle explicitly (Sol audit finding 4): in `stopped_bandCount_error` apply
   the maximal supplier with cutoff `2 * x` (`hx' : 0 < 2 * x := mul_pos (by norm_num) hx`),
   reserving `H + 1` via `n / B n → ∞` so that eventually `⌈x n/B_n⌉ + 1 ≤ ⌈2 x n/B_n⌉`.
   Do not apply optional stopping to an unstopped error.
6. Cutoff removal (independent route, finding 4: iid ladder heights `A_i`,
   `E exp(-(A_1+⋯+A_N)/B_n) → e^{-x}`, exponential Markov): tightness of `(B_n/n) H_k`
   (`weakLadderCount_tight`: ladder height
   subordinator of index `θ-1` plus sealed walk-supremum tightness, `P(H_k ≥ N) = P(τ_N ≤ k)`).
7. Fixed-`ε` joint convergence: functional `(path ↦ (path, ε⁻¹ Leb{s ≤ t | gap_s < ε}))` is
   continuous at paths with null boundary level `{gap = ε}`; the level set has positive
   expected measure for at most countably many `ε` (disjoint level sets in `Ω × [0,t]`,
   Fubini); `t` is not a jump time a.s.; the grid endpoint `⌊nt⌋/n` costs `1/(nε)`.
8. Identification: combine 7, the two-limit estimate and H02
   `heightApprox_tendstoInMeasure` (second-limit argument, as in a Billingsley-type
   approximation theorem) to get `tendsto_walk_height_fdd`; `θ = 2` corollary via `ae_height_two`.

AMBIGUITIES.  (a) Gaussian/slowly-varying case: covered by the PGF-gap route (item 3).
(b) `H03` is not needed (fixed times only).  (c) `clusterLevelMean` exactness is
proved in general by duality (see NORMALIZATION).
(d) `weakEpoch` uses `sInf` with junk `0`.  (Sol audit finding 8)
Deterministic epoch characterizations assume EpochsFinite.
Probabilistic cycle statements use ae_epochsFinite under criticality
and nondegeneracy; cycle quantities remain totalized off that null set.
(e) Namespace boundary: the K02 copies live in `BGW.StableTrees.DiscreteHeightApprox`, the
originals in `BGW.StableTrees.DiscreteForest`.  At integration replace them by
`import BGW.StableTrees.DiscreteForest` and, inside namespace
`BGW.StableTrees.DiscreteHeightApprox`, `open BGW.StableTrees.DiscreteForest`; likewise
replace the copied global H02 declarations by the H02 import, never both. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest (offspringSeqLaw walk forestHeight forestWalkPath)

namespace BGW.StableTrees.DiscreteHeightApprox

open BGW.Skorokhod BGW.Probability.RealWalk BGW.StableTrees

/-! ## 0. Copied definitions -/

end BGW.StableTrees.DiscreteHeightApprox

namespace BGW.StableTrees

open BGW.Skorokhod

end BGW.StableTrees

namespace BGW.StableTrees.DiscreteHeightApprox

open BGW.Skorokhod BGW.Probability.RealWalk BGW.StableTrees

/-! ## 1. Discrete occupation and normalization -/

/-- The discrete occupation count at level `a`:
`#{j < k | ∀ l ∈ [j,k], W_j - W_l < a}`, i.e. `W_j - min_{[j,k]} W < a`.  -/
noncomputable def discreteCount (ω : ℕ → ℕ) (k : ℕ) (a : ℝ) : ℕ :=
  ((Finset.range k).filter
    (fun j => ∀ l, j ≤ l → l ≤ k → ((walk ω j : ℝ) - (walk ω l : ℝ)) < a)).card

/-- The discrete `ε`-occupation `(n ε)⁻¹ #{j < ⌊n t⌋ | W_j - min_{[j,⌊nt⌋]} W < ε B_n}`:
mesh `1/n`, level `ε B_n`; the discrete analogue of `heightApprox ε`. -/
noncomputable def discreteOccupation (B : ℕ → ℝ) (n : ℕ) (ε : ℝ) (ω : ℕ → ℕ) (t : ℝ≥0) : ℝ :=
  (1 / ((n : ℝ) * ε)) * (discreteCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ (ε * B n) : ℝ)

/-- The normalized discrete height `(B_n / n) · H_{⌊n t⌋}` (the constant is `1`, see the module
docstring; at `θ = 2` it converges to `X_t - I_t`). -/
noncomputable def scaledHeight (B : ℕ → ℝ) (n : ℕ) (ω : ℕ → ℕ) (t : ℝ≥0) : ℝ :=
  (B n / (n : ℝ)) * (forestHeight ω ⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ)

/-- Measurability of the discrete height and occupation. -/
theorem measurable_scaledHeight (B : ℕ → ℝ) (n : ℕ) (t : ℝ≥0) :
    Measurable (fun ω => scaledHeight B n ω t) := sorry

theorem measurable_discreteOccupation (B : ℕ → ℝ) (n : ℕ) (ε : ℝ) (t : ℝ≥0) :
    Measurable (fun ω => discreteOccupation B n ε ω t) := sorry

/-! ## 2. The two-limit occupation-error estimate (audit finding 2, verbatim) -/

/-- **Two-limit estimate.**  For a stable domain `(μ, θ, B)`, a fixed `t` and `η > 0`:
`limsup_{ε↓0} limsup_n P(|(B_n/n) H_{⌊nt⌋} - discrete ε-occupation| > η) = 0`.
No renewal-error hypothesis; ties are weak records; `t = 0` is trivial. -/
theorem occupation_error_twoLimit {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (t : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun ε : ℝ =>
        limsup (fun n : ℕ => ((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) : Measure (ℕ → ℕ))
          {ω | η < |scaledHeight B n ω t - discreteOccupation B n ε ω t|}) atTop)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := sorry

/-! ## 3. Reversal at time `k`: weak ladder epochs and band counts -/

/-- The sequence reversed at `k`: `i ↦ ω (k-1-i)` for `i < k`, unchanged afterwards. -/
def revSeq (k : ℕ) (ω : ℕ → ℕ) : ℕ → ℕ := fun i => if i < k then ω (k - 1 - i) else ω i

/-- Exchangeability: reversing the first `k` coordinates preserves the iid law. -/
theorem map_revSeq_offspringSeqLaw (μ : PMF ℕ) (k : ℕ) :
    ((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) : Measure (ℕ → ℕ)).map (revSeq k) =
      ((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) : Measure (ℕ → ℕ)) := sorry

/-- `walk (revSeq k ω) u = W_k - W_{k-u}` for `u ≤ k`. -/
theorem walk_revSeq (ω : ℕ → ℕ) {k u : ℕ} (hu : u ≤ k) :
    walk (revSeq k ω) u = walk ω k - walk ω (k - u) := sorry

/-- The reflected gap `M_u - W_u` of the walk, `M_u = max_{v ≤ u} W_v` (an integer, `≥ 0`). -/
noncomputable def reflGap (ω : ℕ → ℕ) (u : ℕ) : ℤ :=
  (Finset.range (u + 1)).sup' ⟨0, by simp⟩ (walk ω) - walk ω u

/-- The number of weak ascending ladder epochs `u ∈ [1,k]` (`W_u ≥ W_v` for all `v ≤ u`). -/
noncomputable def weakLadderCount (ω : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((Finset.Icc 1 k).filter (fun u => reflGap ω u = 0)).card

/-- The number of times `u ∈ [1,k]` with reflected gap `< a`. -/
noncomputable def bandCount (ω : ℕ → ℕ) (k : ℕ) (a : ℝ) : ℕ :=
  ((Finset.Icc 1 k).filter (fun u => (reflGap ω u : ℝ) < a)).card

/-- (Deterministic) the forest height is the weak ladder count of the reversed sequence. -/
theorem forestHeight_eq_weakLadderCount (ω : ℕ → ℕ) (k : ℕ) :
    forestHeight ω k = weakLadderCount (revSeq k ω) k := sorry

/-- (Deterministic) the discrete occupation count is the band count of the reversed sequence. -/
theorem discreteCount_eq_bandCount (ω : ℕ → ℕ) (k : ℕ) (a : ℝ) :
    discreteCount ω k a = bandCount (revSeq k ω) k a := sorry

/-- The next weak ascending epoch after the epoch `s` (junk `0` if none). -/
noncomputable def nextEpoch (ω : ℕ → ℕ) (s : ℕ) : ℕ :=
  sInf {u | s < u ∧ walk ω s ≤ walk ω u}

/-- The weak epochs `τ_0 = 0 < τ_1 < ...`: iterates of `nextEpoch` from `0`. -/
noncomputable def weakEpoch (ω : ℕ → ℕ) (i : ℕ) : ℕ := (nextEpoch ω)^[i] 0

/-- All epochs exist (the walk returns to each running-maximum level or above). -/
def EpochsFinite (ω : ℕ → ℕ) : Prop :=
  ∀ i : ℕ, ∃ u, weakEpoch ω i < u ∧ walk ω (weakEpoch ω i) ≤ walk ω u

/-- Critical nondegenerate walks oscillate: all weak epochs are a.s. finite. -/
theorem ae_epochsFinite (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∀ᵐ ω ∂((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) : Measure (ℕ → ℕ)),
      EpochsFinite ω := sorry

/-- The epochs are strictly increasing when finite. -/
theorem weakEpoch_lt_succ {ω : ℕ → ℕ} (hω : EpochsFinite ω) (i : ℕ) :
    weakEpoch ω i < weakEpoch ω (i + 1) := sorry

/-- At an epoch the running maximum is attained: `reflGap ω (τ_i) = 0` and the epochs are exactly
the zeros of `reflGap` (ties are weak records). -/
theorem reflGap_eq_zero_iff {ω : ℕ → ℕ} (hω : EpochsFinite ω) {u : ℕ} :
    (reflGap ω u = 0 ∧ 0 < u) ↔ ∃ i, 0 < i ∧ weakEpoch ω i = u := sorry

/-- The number of times `u` in the cycle `[τ_i, τ_{i+1})` with gap `< a` below the epoch value:
the cycle visit count `V_i(a)`. -/
noncomputable def clusterVisits (ω : ℕ → ℕ) (a : ℝ) (i : ℕ) : ℕ :=
  ((Finset.Ico (weakEpoch ω i) (weakEpoch ω (i + 1))).filter
    (fun u => (((walk ω (weakEpoch ω i) - walk ω u : ℤ)) : ℝ) < a)).card

/-- The number of epochs `u ∈ [1,k]` is the last cycle index: `τ_H ≤ k < τ_{H+1}`. -/
theorem weakEpoch_bracket {ω : ℕ → ℕ} (hω : EpochsFinite ω) (k : ℕ) :
    weakEpoch ω (weakLadderCount ω k) ≤ k ∧ k < weakEpoch ω (weakLadderCount ω k + 1) := sorry

/-- (Deterministic stopped decomposition) With `H = weakLadderCount ω k` and `a > 0`:
`Σ_{i<H} V_i(a) - 1 ≤ bandCount ω k a ≤ Σ_{i ≤ H} V_i(a)`. -/
theorem bandCount_sandwich {ω : ℕ → ℕ} (hω : EpochsFinite ω) (k : ℕ) {a : ℝ} (ha : 0 < a) :
    ((∑ i ∈ Finset.range (weakLadderCount ω k), clusterVisits ω a i : ℕ) : ℤ) - 1 ≤
        bandCount ω k a ∧
      bandCount ω k a ≤ ∑ i ∈ Finset.range (weakLadderCount ω k + 1), clusterVisits ω a i :=
  sorry

/-! ## 4. Renewal suppliers (probabilistic) -/

/-- (Stopped restart at the epochs) the cycle visit counts are iid under the offspring law. -/
theorem clusterVisits_iid (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) {a : ℝ} (ha : 0 < a) :
    iIndepFun (fun i ω => clusterVisits ω a i)
      ((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) : Measure (ℕ → ℕ)) ∧
    ∀ i, ((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) : Measure (ℕ → ℕ)).map
        (fun ω => clusterVisits ω a i) =
      ((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) : Measure (ℕ → ℕ)).map
        (fun ω => clusterVisits ω a 0) := sorry

/-- **Key normalization supplier (exact mean).**  In the first cycle `[0, τ_1)` the expected
number of times at gap exactly `y` equals `1` for every `y ∈ ℕ` (duality with the strict
descending ladder process, whose heights are `1` by downward skip-freeness). -/
theorem clusterLevelMean (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) (y : ℕ) :
    ∫ ω, (((Finset.Ico 0 (weakEpoch ω 1)).filter (fun u => reflGap ω u = (y : ℤ))).card : ℝ)
      ∂((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) : Measure (ℕ → ℕ)) = 1 := sorry

/-- Cycle mean: `E V_i(a) = ⌈a⌉₊` for `a > 0`. -/
theorem clusterVisits_mean (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) {a : ℝ} (ha : 0 < a)
    (i : ℕ) :
    ∫ ω, (clusterVisits ω a i : ℝ)
      ∂((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) : Measure (ℕ → ℕ)) = (⌈a⌉₊ : ℝ) := sorry

/-- **Square-integrability supplier** (Sol audit finding 1).  Lean's Bochner integral is
totalized to `0` off integrable functions, so finite second moments are supplied explicitly.
Proof: killed-walk Green bound `E[V_0(a)²] ≤ m + 2 (m-1)² W(m)`, `m = ⌈a⌉₊`. -/
theorem integrable_clusterVisits_sq (μ : PMF ℕ)
    (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {a : ℝ} (ha : 0 < a) (i : ℕ) :
    Integrable (fun ω => (clusterVisits ω a i : ℝ) ^ 2)
      ((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) :
        Measure (ℕ → ℕ)) := by
  -- Prove from the killed-walk Green bound described below.
  sorry

/- Prove finite band second moments by the killed-gap Green kernel.
Bound its diagonal by the weak-ladder renewal function, retaining
zero ladder increments. Use the normalized offspring PGF gap to obtain
the two-limit bound, also for the infinite-variance Gaussian domain.
No finite-variance hypothesis is added when θ = 2. -/

/-- Real-variable offspring PGF (internal interface for the Laplace bridge). -/
noncomputable def offspringPGFReal (μ : PMF ℕ) (s : ℝ) : ℝ :=
  ∑' j : ℕ, (μ j).toReal * s ^ j

/-- Laplace bridge from `StableDomain` (finding 3): a real proof obligation. -/
theorem norming_offspringPGF_gap
    {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (offspringPGFReal μ (Real.exp (-lam / B n)) -
        Real.exp (-lam / B n))) atTop (𝓝 (lam ^ θ)) := by
  sorry

/-- **Scale-free second moment** of a cycle at level `a = ε B_n` against `N ≈ n/B_n` cycles:
`limsup_{ε↓0} limsup_n (B_n/n) E[V_0(εB_n)²] / (ε B_n)² = 0`
(rate `ε^{θ-1}` by the renewal bound). -/
theorem clusterVisits_secondMoment_scaled {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) :
    Tendsto (fun ε : ℝ =>
        limsup (fun n : ℕ => ENNReal.ofReal
          ((B n / (n : ℝ)) *
            (∫ ω, (clusterVisits ω (ε * B n) 0 : ℝ) ^ 2
              ∂((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) : Measure (ℕ → ℕ))) /
            (ε * B n) ^ 2)) atTop)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := sorry

/-- **Stopped error, uniform over the cutoff** (Kolmogorov maximal inequality from the three
suppliers above): over `N ≤ x n/B_n` cycles the centered cycle sums stay `o(n ε)` as `n → ∞`,
then `ε → 0`. -/
theorem cluster_partialSum_maximal {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) :
    Tendsto (fun ε : ℝ =>
        limsup (fun n : ℕ => ((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) :
          Measure (ℕ → ℕ))
          {ω | ∃ N ∈ Finset.range (⌈x * (n : ℝ) / B n⌉₊ + 1),
            δ * ((n : ℝ) * ε) <
              |(∑ i ∈ Finset.range N, (clusterVisits ω (ε * B n) i : ℝ)) -
                (N : ℝ) * (⌈ε * B n⌉₊ : ℝ)|}) atTop)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := sorry

/-- **Stopped renewal error for the band count** (cutoff event `H_k ≤ x n/B_n`, `k = ⌊nt⌋`):
`bandCount ω k (ε B_n) ≈ ⌈ε B_n⌉ H_k` up to `δ n ε`, two limits. -/
theorem stopped_bandCount_error {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (t : ℝ≥0) {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) :
    Tendsto (fun ε : ℝ =>
        limsup (fun n : ℕ => ((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) :
          Measure (ℕ → ℕ))
          {ω | (weakLadderCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ) ≤ x * (n : ℝ) / B n ∧
            δ * ((n : ℝ) * ε) <
              |(bandCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ (ε * B n) : ℝ) -
                (⌈ε * B n⌉₊ : ℝ) * (weakLadderCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ)|}) atTop)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := sorry

/-- **Cutoff removal**: the normalized ladder count `(B_n/n) H_{⌊nt⌋}` is tight (ladder-height
subordinator of index `θ-1` and sealed walk-supremum tightness: `{H_k ≥ N} = {τ_N ≤ k}`). -/
theorem weakLadderCount_tight {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (t : ℝ≥0) :
    Tendsto (fun x : ℝ =>
        limsup (fun n : ℕ => ((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) :
          Measure (ℕ → ℕ))
          {ω | x < (B n / (n : ℝ)) * (forestHeight ω ⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ)}) atTop)
      atTop (𝓝 0) := sorry

/-! ## 5. Fixed-`ε` joint convergence of (walk, occupation) -/

/-- The discrete joint object: the rescaled walk path and the `ε`-occupations at times `t`. -/
noncomputable def discreteJoint (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (ε : ℝ) {r : ℕ} (t : Fin r → ℝ≥0)
    (ω : ℕ → ℕ) : D (T : ℝ) ℝ × (Fin r → ℝ) :=
  (forestWalkPath B n T ω, fun i => discreteOccupation B n ε ω (t i))

/-- The continuum joint object: the restricted path and `heightApprox ε` at times `t`. -/
noncomputable def continuumJoint (T : ℝ≥0) (ε : ℝ) {r : ℕ} (t : Fin r → ℝ≥0)
    (f : DLoc) : D (T : ℝ) ℝ × (Fin r → ℝ) :=
  (DLoc.restrict T f, fun i => heightApprox ε f (t i))

theorem measurable_discreteJoint (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (ε : ℝ) {r : ℕ}
    (t : Fin r → ℝ≥0) : Measurable (discreteJoint B n T ε t) := sorry

theorem measurable_continuumJoint (T : ℝ≥0) (ε : ℝ) {r : ℕ} (t : Fin r → ℝ≥0) :
    Measurable (continuumJoint T ε t) := sorry

/-- **Boundary levels are countable** (Fubini): at most countably many `ε > 0` have
`P(Leb{s ≤ t | X_s = I^s_t + ε} > 0) > 0` (the level sets are disjoint in `Ω × [0,t]`). -/
theorem countable_boundaryLevels {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    {ε : ℝ | 0 < ε ∧ 0 < (stableLocalLaw θ : Measure DLoc)
        {f | 0 < volume {s : ℝ | 0 ≤ s ∧ s ≤ (t : ℝ) ∧
          f.1 s.toNNReal = futureInf f t s.toNNReal + ε}}}.Countable := sorry

/-- **Fixed-`ε` joint convergence in law** of (scaled walk, discrete `ε`-occupations) to
(`X`, `heightApprox ε`), for `ε` outside a countable exceptional set (depending on the times). -/
theorem tendsto_joint_occupation {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {T : ℝ≥0} (hT : 0 < T) {r : ℕ} (t : Fin r → ℝ≥0)
    (ht : ∀ i, t i ≤ T) :
    ∃ Exc : Set ℝ, Exc.Countable ∧ ∀ ε : ℝ, 0 < ε → ε ∉ Exc →
      Tendsto (fun n : ℕ => (offspringSeqLaw μ).map (discreteJoint B n T ε t)) atTop
        (𝓝 ((stableLocalLaw θ).map (continuumJoint T ε t))) := sorry

/-! ## 6. Joint walk/height convergence at fixed times -/

/-- The joint object (scaled walk, normalized discrete heights). -/
noncomputable def heightJoint (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) {r : ℕ} (t : Fin r → ℝ≥0)
    (ω : ℕ → ℕ) : D (T : ℝ) ℝ × (Fin r → ℝ) :=
  (forestWalkPath B n T ω, fun i => scaledHeight B n ω (t i))

/-- The limit object (restricted path, continuum height `height θ`) at times `t`. -/
noncomputable def heightLimitJoint (θ : ℝ) (T : ℝ≥0) {r : ℕ} (t : Fin r → ℝ≥0) (f : DLoc) :
    D (T : ℝ) ℝ × (Fin r → ℝ) :=
  (DLoc.restrict T f, fun i => height θ f (t i))

/-- **Joint walk/height finite-dimensional convergence** (the K09 deliverable, fixed times,
no `H03`): `(forestWalkPath, (B_n/n) H_{⌊n t_i⌋}) ⇒ (X, height θ X (t_i))`. -/
theorem tendsto_walk_height_fdd {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {T : ℝ≥0} (hT : 0 < T) {r : ℕ} (t : Fin r → ℝ≥0)
    (ht : ∀ i, t i ≤ T) :
    Tendsto (fun n : ℕ => (offspringSeqLaw μ).map (heightJoint B n T t)) atTop
      (𝓝 ((stableLocalLaw θ).map (heightLimitJoint θ T t))) := sorry

/-- **Normalization at `θ = 2`**: the limit height is `X_t - I_t`, with constant exactly `1`
(`B_n = σ√(n/2)`, library variance-2 process). -/
theorem tendsto_walk_height_fdd_two {μ : PMF ℕ} {B : ℕ → ℝ}
    (h : StableDomain μ 2 B) {T : ℝ≥0} (hT : 0 < T) {r : ℕ} (t : Fin r → ℝ≥0)
    (ht : ∀ i, t i ≤ T) :
    Tendsto (fun n : ℕ => (offspringSeqLaw μ).map (heightJoint B n T t)) atTop
      (𝓝 ((stableLocalLaw 2).map
        (fun f : DLoc => (DLoc.restrict T f, fun i => f.1 (t i) - futureInf f (t i) 0)))) :=
  sorry

end BGW.StableTrees.DiscreteHeightApprox
