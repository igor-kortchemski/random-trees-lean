import BGW.StableTrees.StableLocalLaw

/-! Contract probe for CT10 node C22E3a, the host-level half of `CLASSICAL_THEORY_INPUTS.md` C22
(E3): for `1 < θ < 2` the stable process has, almost surely, a positive jump in EVERY nonempty
open time interval.  Companion of `CT10_C22E3_ExcursionJump.lean`, which transfers this to the
normalized excursion.  Suggested maintained module: `BGW/StableTrees/StablePositiveJumps.lean`,
namespace `BGW.StableTrees`.

SOURCE (C22(a), E3).  "θ < 2: `X^exc` has a jump, so `Δ̄(X^exc) > 0`.  θ = 2: `X^exc = √2 e` is
continuous."  C22(d) lists E3 as optional (used only for the remark after 7.1(i)).

ROUTE CHOICE.  The library has no Lévy–Itô decomposition or Poisson jump measure for `X`
(`stableLocalLaw` is built from finite-dimensional laws, N03).  Four routes were compared.
(a) CHOSEN.  Host jumps from independent stable increments plus one tail lower bound for
    `stableLaw θ`, then transfer to the excursion through the sealed straddling excursion (O01).
    New analytic content: only `frequently_le_rpow_mul_stableLaw_Ioi`, derived from the sealed
    Laplace transform `integral_exp_neg_mul_stableLaw` (`E e^{-λX} = e^{λ^θ}`) and the sealed
    layer-cake identity `Attraction.DomainCriterion.integral_min_sq_eq_integrated_tail`.
(b) FCLT: `maxJump` is 2-Lipschitz (`lipschitzWith_two_maxJump`), so the open-set Portmanteau
    bound along `StableDomain.tendsto_stepPathLaw` would give
    `P(maxJump X < δ) ≤ liminf P(max_k ξ_k < δ a_n + 1)`.  Rejected: it needs
    `n P(ξ > δ a_n) ≳ δ^{-θ}`, a norming/tail relation the library does not state (the Pareto
    witness `existsStableDomain_pareto` hides its norming `a` behind an existential, and
    `DomainCriterion.rightTail_regularlyVarying` gives regular variation of the tail only, not its
    link to `a`), i.e. the same Tauberian work as (a) plus step-path jump bookkeeping.
(b') Vervaat/bridge (C35 `map_vervaatD_stableBridgeLaw`, N14 bridge prefixes): jumps of the
    bridge on `[0, 1/2]` by absolute continuity, then jump bookkeeping through `vervaatD`.
    Rejected: it still needs host jumps on a fixed interval (this file) and adds two transfers.
(c) Density bounds (`exists_abs_mul_stableDensity_le`) are UPPER bounds; a lower bound on
    `p_θ(x) x^{1+θ}` is not in the library.  Not usable.
A zero-one law (`P(no jump on [0,1]) ∈ {0,1}` from i.i.d. scaled blocks) is NOT needed: the grid
argument below gives `P(no jump in (a,b]) ≤ exp(-(b-a) c δ^{-θ}/2)` for every `δ > 0` directly.

TRUTH CHECK.
(1) Tail.  For `1 < θ < 2` the law with `E e^{-λX} = e^{λ^θ}` has Lévy measure
    `θ(θ-1)/Γ(2-θ) x^{-1-θ} dx` on `(0,∞)` and `P(X > x) ~ (θ-1)/Γ(2-θ) x^{-θ}` (e.g. `θ = 3/2`:
    constant `≈ 0.282`).  The contract claims only `limsup x^θ P(X > x) > 0`, in `∃ᶠ` form.  It is
    FALSE at `θ = 2` (Gaussian tail), hence the hypothesis `θ < 2`.  Derivation used by the proof
    (no mean or moment of `X` is needed): `E(1 - e^{-λX})^2 = e^{(2λ)^θ} - 2e^{λ^θ} + 1
    ≥ (2^θ - 2)λ^θ - 2λ^{2θ}` for `λ^θ ≤ 1` (`Real.add_one_le_exp`,
    `Real.abs_exp_sub_one_sub_id_le`).  On `{X < 0}`, `(1 - e^{-λX})^2 ≤ λ^2 X^2 e^{2λ|X|}
    ≤ 2λ^2 e^{-3X}`, total `≤ 2λ^2 e^{3^θ}` for `λ ≤ 1`.  On `{X ≥ 0}`,
    `(1 - e^{-λX})^2 ≤ min((λX⁺)^2, 1)`, and the layer cake gives
    `E min((λX⁺)^2, 1) = ∫_0^1 P(X > √u/λ) du`.  If `P(X > x) ≤ ε x^{-θ}` for `x ≥ x₀`, this is
    `≤ λ^2 x₀^2 + ε λ^θ ∫_0^1 u^{-θ/2} du = λ^2 x₀^2 + 2ελ^θ/(2-θ)` (`θ < 2` makes the integral
    finite).  Dividing by `λ^θ` and letting `λ → 0` (`λ^{2-θ} → 0`) forces
    `ε ≥ (2-θ)(2^θ-2)/2`.  So `c = (2-θ)(2^θ-2)/4` works.
(2) Grid.  `IsStableLevyLaw.increments`: increments over `0 = t_0 < … < t_n` are independent with
    laws `stableLawAt θ (t_{i+1} - t_i)`, and `stableLawAt θ h` is the image of `stableLaw θ`
    under `x ↦ h^{1/θ} x`.  Hence `P(all n increments over a mesh-h grid ≤ δ)
    = stableLaw θ (Iic (δ h^{-1/θ}))^n` EXACTLY (the shift by `a` uses `map_shift_stableLocalLaw`;
    `n = 0` gives `1 = 1`).
(3) No jump in `(a,b]` (with right-continuity at `a`) makes `f` continuous, hence uniformly
    continuous, on `[a,b]`, so grid increments are eventually `≤ δ`.  `Function.leftLim f s` at
    `s > a ≥ 0` is the genuine left limit (`𝓝[<] s ≠ ⊥` in `ℝ≥0`); no junk value is involved.
(4) Combining: with `h = (b-a)/n` and `x` from (1), `n = ⌊(b-a)(x/δ)^θ⌋₊` gives
    `n P(X > δ h^{-1/θ}) ≥ (b-a) c δ^{-θ}/2`, so the grid event has probability
    `≤ exp(-(b-a) c δ^{-θ}/2)` along infinitely many `n`; the no-jump event lies in
    `⋃_N ⋂_{n ≥ N}` of these events, so its outer measure is `≤ exp(-(b-a) c δ^{-θ}/2)` for all
    `δ > 0`, i.e. `0`.
(5) Sign.  (4) gives a jump of either sign; `ae_leftLim_le_stableLocalLaw` (no negative jumps)
    makes it positive.  Rational endpoints and countable intersection give all real `a < b`.
(6) At `θ = 2` the host is continuous (`ae_mem_range_ofContinuous_stableProcessLaw_two`), so
    every statement below with `θ < 2` is false at `θ = 2`: the hypothesis is necessary.

PROOF PLAN (size 400-700 lines in total).
(i) `integrable_exp_neg_mul_stableLaw`: `Integrable.of_integral_ne_zero` with
    `integral_exp_neg_mul_stableLaw hθ hlam` and `Real.exp_pos`.  (3 lines, checked in a
    scratch probe.)
(ii) `integral_one_sub_exp_sq_stableLaw`: expand `(1 - e^{-λx})^2 = 1 - 2e^{-λx} + e^{-2λx}`,
    `integral_add`/`integral_sub` with (i) at `λ` and `2λ`, `integral_exp_neg_mul_stableLaw`,
    `measure_univ`.  (12 lines, checked in a scratch probe.)
(iii) `frequently_le_rpow_mul_stableLaw_Ioi`: by contradiction (`Filter.not_frequently`), as in
    TRUTH CHECK (1).  Upper bound on `{X ≥ 0}` through
    `Attraction.DomainCriterion.integral_min_sq_eq_integrated_tail` (module
    `BGW.StableTrees.Attraction.DomainCriterion`) applied to `X' = λ max X 0`, `y = 1`;
    `integral_rpow` on `[0,1]` with exponent `-θ/2 > -1`.  Negative part bounded by (i) at
    `λ = 3`.  Conclude with `λ → 0` along `λ = 1/(k+1)` (or an explicit small `λ`).
    (~120-200; the main analytic step.)
(iv) `measure_grid_increments_le`: `map_shift_stableLocalLaw hθ a` reduces to `a = 0`;
    `map_restrict_stableLocalLaw hθ (T := n * h)`, `isStableLevyLaw_stableProcessLaw`,
    `IsStableLevyLaw.increments` with `t i = i * h`, then `Measure.pi_pi` on the box
    `Set.pi univ (fun _ => Iic δ)` and `stableLawAt`/`Measure.map_apply` with `x ↦ h^{1/θ} x`
    (`Real.rpow_neg`).  (~80-150)
(v) `eventually_grid_increments_le`: `ContinuousOn f.1 (Icc a b)` from `f.2` (right-continuity)
    and `hf` (left limits equal values: `IsCadlag.tendsto_nhdsLT_leftLim`), then
    `IsCompact.uniformContinuousOn_of_continuous` (`isCompact_Icc`) and mesh `(b-a)/n → 0`.
    (~50-90)
(vi) `ae_exists_jump_Ioc`: TRUTH CHECK (4) with (iii), (iv), (v); `Real.one_sub_le_exp_neg`
    gives `(1-p)^n ≤ e^{-np}`.  The no-jump set lies in the increasing union over `N` of
    `⋂_{n ≥ N} A_n` (`A_n` the grid event of (iv) for `h = (b-a)/n`); each `⋂` has measure
    `≤ μ A_{n_N}` for one frequent `n_N ≥ N` (`measure_mono`), and
    `tendsto_measure_iUnion_atTop` passes to the union.  Finish with `δ → 0`
    (`exp(-(b-a)cδ^{-θ}/2) → 0`).  (~80-150)
(vii) `ae_forall_exists_pos_jump`: `ae_all_iff` over pairs of nonnegative rationals with (vi),
    `ae_leftLim_le_stableLocalLaw hθ`, and `exists_rat_btwn` to place rationals
    `a < q₁ < q₂ < b`.  (~30-60)
RISK: (iii) is the only genuinely analytic step (estimate 150 lines, moderate); (iv) is routine
but bookkeeping-heavy (`Fin` grids, `ℝ≥0` casts).  No deep fact (Lévy–Itô, Lévy's
characterization of continuous Lévy processes) is used or needed.

ACYCLICITY.  Sealed suppliers only: `StableLaw` (`stableLaw`, `stableLawAt`,
`integral_exp_neg_mul_stableLaw`), `StableLevyLaw`/`StableProcessLaw` (`IsStableLevyLaw`,
`isStableLevyLaw_stableProcessLaw`), N03 (`stableLocalLaw`, `map_restrict_stableLocalLaw`,
`ae_leftLim_le_stableLocalLaw`), N04 (`map_shift_stableLocalLaw`, module
`BGW.StableTrees.StableLocalMarkov`), `Attraction.DomainCriterion` (layer cake).  No excursion,
height or K-node input; the companion E3 contract consumes `ae_forall_exists_pos_jump`.

BINDER SCOPE (AUDITOR_RULES).  One integral: `∫ x, (1 - Real.exp (-lam * x)) ^ 2 ∂μ` stands alone
on the left of `=`; the `- 2 * …` and `+ 1` are on the right-hand side, outside any binder.
`x ^ θ * (stableLaw θ : Measure ℝ).real (Set.Ioi x)` is a plain product. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-! ### The stable law: Laplace transform and tail lower bound -/

/-- `x ↦ e^{-λx}` is integrable under the stable law for `λ ≥ 0` (its integral `e^{λ^θ}` is
nonzero). -/
theorem integrable_exp_neg_mul_stableLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {lam : ℝ}
    (hlam : 0 ≤ lam) :
    Integrable (fun x => Real.exp (-lam * x)) (stableLaw θ : Measure ℝ) := sorry

/-- Second difference of the Laplace transform: `E(1 - e^{-λX})^2 = e^{(2λ)^θ} - 2e^{λ^θ} + 1`. -/
theorem integral_one_sub_exp_sq_stableLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {lam : ℝ}
    (hlam : 0 ≤ lam) :
    ∫ x, (1 - Real.exp (-lam * x)) ^ 2 ∂(stableLaw θ : Measure ℝ) =
      Real.exp ((2 * lam) ^ θ) - 2 * Real.exp (lam ^ θ) + 1 := sorry

/-- **Tail lower bound** for `1 < θ < 2`: `limsup_{x→∞} x^θ P(X_1 > x) > 0`. -/
theorem frequently_le_rpow_mul_stableLaw_Ioi {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hθ2 : θ < 2) :
    ∃ c : ℝ, 0 < c ∧
      ∃ᶠ x in atTop, c ≤ x ^ θ * (stableLaw θ : Measure ℝ).real (Set.Ioi x) := sorry

/-! ### Grid increments of the host -/

/-- **Grid increments**: the probability that the `n` increments of the local stable process
over the grid `a, a + h, …, a + n h` are all at most `δ` is
`stableLaw θ (Iic (δ h^{-1/θ}))^n` (independent increments with laws `stableLawAt θ h`). -/
theorem measure_grid_increments_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0) {h : ℝ≥0}
    (hh : 0 < h) (n : ℕ) (δ : ℝ) :
    (stableLocalLaw θ : Measure DLoc)
        {f | ∀ k < n, f.1 (a + ((k : ℝ≥0) + 1) * h) - f.1 (a + (k : ℝ≥0) * h) ≤ δ} =
      (stableLaw θ : Measure ℝ) (Set.Iic (δ * (h : ℝ) ^ (-(1 / θ)))) ^ n := sorry

/-- **Deterministic**: a càdlàg path with no jump in `(a, b]` has uniformly small increments on
fine regular grids of `[a, b]`. -/
theorem eventually_grid_increments_le {f : DLoc} {a b : ℝ≥0} (hab : a < b)
    (hf : ∀ s ∈ Set.Ioc a b, Function.leftLim f.1 s = f.1 s) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ k < n,
      f.1 (a + ((k : ℝ≥0) + 1) * ((b - a) / (n : ℝ≥0))) -
        f.1 (a + (k : ℝ≥0) * ((b - a) / (n : ℝ≥0))) ≤ δ := sorry

/-! ### Jumps of the host -/

/-- For `1 < θ < 2` and a fixed interval `(a, b]`, the stable process jumps in `(a, b]` almost
surely. -/
theorem ae_exists_jump_Ioc {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hθ2 : θ < 2) {a b : ℝ≥0}
    (hab : a < b) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ∃ s ∈ Set.Ioc a b, Function.leftLim f.1 s ≠ f.1 s := sorry

/-- **Host jumps (C22 E3, host level).**  For `1 < θ < 2`, almost surely the stable process has a
positive jump in every nonempty open time interval, simultaneously for all intervals. -/
theorem ae_forall_exists_pos_jump {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hθ2 : θ < 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ a b : ℝ≥0, a < b →
      ∃ s ∈ Set.Ioo a b, Function.leftLim f.1 s < f.1 s := sorry

end BGW.StableTrees
