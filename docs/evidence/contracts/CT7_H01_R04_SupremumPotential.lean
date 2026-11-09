import BGW.StableTrees.SupremumDrawdown
import BGW.StableTrees.SupremumReflectedFamily
import BGW.Probability.DoobL2Resolvent
import BGW.StableTrees.StableLocalLaw
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! Contract probe for H01 node R04 (blueprint R04, plus the resolvent formula and the Markov
hypothesis that the blueprint files under R05; AUDIT items 2, 3, 4, 7): the supremum potential
`h_q`, its explicit density, the reflected-family resolvent of the occupation kernel, and the
potential estimates feeding R05's Cauchy bounds and R10's correction.  Depends on R03.
NOT redefined: `supRunning`, `supReflected`, `supOccupation` (W49), `supReflectedFrom`,
`isStronglyProgressive_supReflectedFrom`, `condExp_supReflectedFromLoc_markov` (R01, sealed),
`discountedOccupation`, `ResolventMarkov`, `integral_sq_discountedOccupation(_le)` (R05a, sealed).
Suppliers consumed by the PROOFS (not restated here): R03 `law_supReflected_expTime`
(`R_{e_q} ~ Exp(q^{1/θ})`), R02a independence of `S_{e_q}`, `R_{e_q}`, and R03
`integral_exp_neg_supRunning_expTime` (`E e^{-λS_{e_q}} = q(Φ-λ)/(Φ(q-λ^θ))`, `λ ≠ Φ`).

Notation. `Φ = q^{1/θ}`; `R^y_t = max y S_t - X_t`; `H_q(x) = P(S_{e_q} ≥ x)` (`1` for `x < 0`);
`h_q = (Φ/q) H_q` (`supPotential`); `W(x) = x^{θ-1}/Γ(θ)` (`stableScale`);
`W_q(x) = Σ_n q^n x^{θ(n+1)-1}/Γ(θ(n+1))` (`stableSeries`); `g_ε(r) = ε⁻¹ 1{r < ε}`
(`supOccKernel`); `u^q_ε(y) = E ∫_0^∞ e^{-qt} g_ε(R^y_t) dt` (`supOccupationResolvent`);
`v_ε` (`supCorrection`).  All functions of the start `y` are on `ℝ` (via `y.toNNReal`), so
`ResolventMarkov` with `E = ℝ` applies with no coercion and `V` is automatically bounded on `ℝ`.

CONSTANT CHECKS (hand computation; all consistent with R03's laws `R_{e_q} ~ Exp(Φ)`,
`F_q(λ) = q(Φ-λ)/(Φ(q-λ^θ))`, `F_q(Φ) = 1/θ`):
 * Transforms: `∫e^{-λx}W_q = 1/(λ^θ-q)` (`λ > Φ`); `W_q(0)=0` since `θ>1`; so
   `∫e^{-λx}(W_q'-ΦW_q) = (λ-Φ)/(λ^θ-q) = (Φ/q)F_q(λ)`.  So `(Φ/q)P(S_{e_q}∈dx) = (W_q'-ΦW_q)dx`.
 * `θ=2`: `W_q = sinh(√q x)/√q`, `W_q'-ΦW_q = e^{-√q x}`, `S ~ Exp(√q)`; `h_q = e^{-√q x}/√q`.
 * `R^y_{e_q} = (y-S)_+ + R` with `S ⟂ R`, `R ~ Exp(Φ)`; `1-e^{-Φ(ε-a)} = ∫_a^ε Φe^{-Φ(ε-r)}dr`
   and `{(y-S)_+ ≤ r} = {S ≥ y-r}` give `u^q_ε(y) = ε⁻¹∫_0^ε e^{-Φ(ε-r)}h_q(y-r)dr` (blueprint
   formula exact).  `u ≤ Φ/q`; antitone in `y`; `Φ h_q(0) = Φ²/q = q^{2/θ-1}`.
 * `q↓0`: `h_q(0)(ε⁻¹(1-e^{-Φε})/Φ - 1) = -Φ²ε/(2q) + O(Φ³ε²/q) → -1_{θ=2}ε/2`; hence
   `v_ε = W - ε⁻¹∫_0^εW((·-r)_+) - 1_{θ=2}ε/2`; `θ=2`: `v_ε = -(ε-y)_+²/(2ε)` (checked both
   ranges `y ≥ ε`, `y < ε`).  `|v_ε| ≤ (1/Γ(θ)+1/2)ε^{θ-1}` for ALL `ε>0` (Hölder:
   `0 ≤ x^a-(x-r)_+^a ≤ r^a`, `a=θ-1 ≤ 1`).
 * `q=1`: `Φ/q = 1`; `q=2`: `Φ/q = 2^{1/θ-1} ≤ 1`, so `E∫e^{-2t}|g_ε-g_η|(R) ≤ 2`, giving the
   blueprint's `E(B_ε-B_η)² ≤ 4‖u¹_ε-u¹_η‖_∞` and `E B_ε² ≤ 2` (AUDIT item 3).
FLAGS (no numerical inconsistency found).  (1) Blueprint lists the resolvent formula, its uniform
convergence and the Markov hypothesis under R05; here they are in R04 because the potential
identities (`E_x(B_ε-B_η)²`, the `V=u¹_ε-u¹_η` bound) are statements about `u` and need the
Markov hypothesis; R05 keeps only Doob/maximal estimates, càdlàg Cauchy and construction of `M^*`.
(2) Blueprint's `h θ q`/`supExpTail`/`stableScale` are `supPotential`/`supExpTail`/`stableScale`.
(3) The density identity is stated on `Ioi 0` (no atom at 0 included), and the sign of
`W_q'-ΦW_q` is a CONSEQUENCE (`stableSeriesDeriv_sub_nonneg`), via signed-measure uniqueness
(AUDIT item 2).  (4) Blueprint §2 contains a typo `{f1}`; irrelevant.  Estimate 900-1700 lines. -/

/- Ownership.  R04 consumes sealed R01 and R05a and the R02a/R03 laws.  R05 consumes R04 for the
compact maximal/Cauchy construction.  R06 supplies the constructed clock's reflected-family
conditional potential.  The arbitrary-positive-rate occupation identity is proved here
(`condExp_reflectedResolvent_tail`).  R10 localizes before taking `q ↓ 0`; R11 proves the stopped
energy estimates.  No R04 proof uses R05/R06/R09/R10/R11 conclusions. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-! ### Definitions -/

/-- `W(x) = x^{θ-1}/Γ(θ)` for `x ≥ 0`, `0` for `x < 0`. -/
noncomputable def stableScale (θ x : ℝ) : ℝ :=
  if 0 ≤ x then x ^ (θ - 1) / Real.Gamma θ else 0

/-- Term `q^n x^{θ(n+1)-1}/Γ(θ(n+1))` of `W_q`. -/
noncomputable def stableSeriesTerm (θ q : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  q ^ n * x ^ (θ * (n + 1) - 1) / Real.Gamma (θ * (n + 1))

/-- Term `q^n x^{θ(n+1)-2}/Γ(θ(n+1)-1)` of `W_q'`. -/
noncomputable def stableSeriesDerivTerm (θ q : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  q ^ n * x ^ (θ * (n + 1) - 2) / Real.Gamma (θ * (n + 1) - 1)

/-- `W_q(x)` for `x ≥ 0`, `0` for `x < 0`. -/
noncomputable def stableSeries (θ q x : ℝ) : ℝ :=
  if 0 ≤ x then ∑' n : ℕ, stableSeriesTerm θ q n x else 0

/-- Termwise derivative of `W_q` on `(0,∞)`, `0` elsewhere. -/
noncomputable def stableSeriesDeriv (θ q x : ℝ) : ℝ :=
  if 0 < x then ∑' n : ℕ, stableSeriesDerivTerm θ q n x else 0

/-- `H_q(x) = P(S_{e_q} ≥ x)` for `x ≥ 0`, extended by `1` for `x < 0`. -/
noncomputable def supExpTail (θ q x : ℝ) : ℝ :=
  if x < 0 then 1 else (expClockLaw θ q {p | x ≤ supRunning p.1 p.2.toNNReal}).toReal

/-- `h_q = (Φ/q) H_q`, `Φ = q^{1/θ}` (blueprint `h θ q`). -/
noncomputable def supPotential (θ q x : ℝ) : ℝ := q ^ (1 / θ) / q * supExpTail θ q x

/-- The occupation kernel `g_ε(r) = ε⁻¹ 1{r < ε}`. -/
noncomputable def supOccKernel (ε r : ℝ) : ℝ := Set.indicator (Set.Iio ε) (fun _ => ε⁻¹) r

/-- `q`-resolvent of the reflected family on a bounded Borel `k`:
`y ↦ E ∫_0^∞ e^{-qt} k(R^y_t) dt` (start `y.toNNReal`). -/
noncomputable def reflectedResolvent (θ q : ℝ) (k : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ f, (∫ t in Set.Ioi (0 : ℝ),
    Real.exp (-q * t) * k (supReflectedFrom y.toNNReal f t.toNNReal))
    ∂(stableLocalLaw θ : Measure DLoc)

/-- `u^q_ε = reflectedResolvent θ q g_ε`. -/
noncomputable def supOccupationResolvent (θ q ε : ℝ) (y : ℝ) : ℝ :=
  reflectedResolvent θ q (supOccKernel ε) y

/-- The zero-resolvent correction `v_ε`. -/
noncomputable def supCorrection (θ ε x : ℝ) : ℝ :=
  stableScale θ x - ε⁻¹ * (∫ r in Set.Ioc 0 ε, stableScale θ (x - r)) -
    (if θ = 2 then ε / 2 else 0)

/-! ### The series `W_q` and the density of `S_{e_q}` -/

theorem stableSeries_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q : ℝ) : stableSeries θ q 0 = 0 := sorry

theorem summable_stableSeriesTerm {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun n : ℕ => stableSeriesTerm θ q n x) := sorry

theorem summable_stableSeriesDerivTerm {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q : ℝ) {x : ℝ}
    (hx : 0 < x) : Summable (fun n : ℕ => stableSeriesDerivTerm θ q n x) := sorry

theorem continuousOn_stableSeries {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q : ℝ) :
    ContinuousOn (stableSeries θ q) (Ici 0) := sorry

/-- Termwise differentiation on `(0,∞)`. -/
theorem hasDerivAt_stableSeries {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (stableSeries θ q) (stableSeriesDeriv θ q x) x := sorry

/-- Local integrability of `W_q'` at `0` (integrable singularity `x^{θ-2}` for `θ < 2`). -/
theorem integrableOn_stableSeriesDeriv {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q : ℝ) (K : ℝ) :
    IntegrableOn (stableSeriesDeriv θ q) (Ioc 0 K) := sorry

/-- `W_q(x) = ∫_0^x W_q'` (absolute continuity at the singular endpoint `0`). -/
theorem integral_stableSeriesDeriv {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    ∫ y in Ioc 0 x, stableSeriesDeriv θ q y = stableSeries θ q x := sorry

/-- Laplace transform of `W_q` after tilting: `∫_0^∞ e^{-λx}W_q(x)dx = 1/(λ^θ-q)`, `λ > Φ`,
with absolute integrability of `W_q` and `W_q'` against `e^{-λx}` (AUDIT item 2). -/
theorem integral_exp_neg_mul_stableSeries {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q)
    {lam : ℝ} (hlam : q ^ (1 / θ) < lam) :
    Integrable (fun x => Real.exp (-lam * x) * stableSeries θ q x) (volume.restrict (Ioi 0)) ∧
    Integrable (fun x => Real.exp (-lam * x) * stableSeriesDeriv θ q x)
      (volume.restrict (Ioi 0)) ∧
    ∫ x in Ioi 0, Real.exp (-lam * x) * stableSeries θ q x = 1 / (lam ^ θ - q) := sorry

/-- Transform of `W_q' - Φ W_q`: `(λ-Φ)/(λ^θ-q) = (Φ/q) F_q(λ)`. -/
theorem integral_exp_neg_mul_stableSeriesDeriv_sub {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ}
    (hq : 0 < q) {lam : ℝ} (hlam : q ^ (1 / θ) < lam) :
    ∫ x in Ioi 0, Real.exp (-lam * x) *
        (stableSeriesDeriv θ q x - q ^ (1 / θ) * stableSeries θ q x) =
      (lam - q ^ (1 / θ)) / (lam ^ θ - q) := sorry

/-- **Density of the supremum at an exponential time** (blueprint R04, exact constants):
`(Φ/q) P(S_{e_q} ∈ dx) = (W_q'(x) - Φ W_q(x)) dx` on `(0,∞)`, no atom anywhere. -/
theorem map_supRunning_expClockLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    (expClockLaw θ q).map (fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal) =
      (volume.restrict (Ioi 0)).withDensity (fun x => ENNReal.ofReal
        (q / q ^ (1 / θ) * (stableSeriesDeriv θ q x - q ^ (1 / θ) * stableSeries θ q x))) := sorry

/-- Positivity of the density (a consequence, not an input). -/
theorem stableSeriesDeriv_sub_nonneg {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q)
    {x : ℝ} (hx : 0 < x) : 0 ≤ stableSeriesDeriv θ q x - q ^ (1 / θ) * stableSeries θ q x := sorry

/-- The supremum at an exponential time has no atoms. -/
theorem expClockLaw_supRunning_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) (x : ℝ) :
    expClockLaw θ q {p | supRunning p.1 p.2.toNNReal = x} = 0 := sorry

/-! ### Properties of `H_q` and `h_q` -/

theorem supExpTail_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    supExpTail θ q 0 = 1 := sorry

theorem supExpTail_mem_Icc {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) (x : ℝ) :
    supExpTail θ q x ∈ Icc (0 : ℝ) 1 := sorry

theorem antitone_supExpTail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    Antitone (supExpTail θ q) := sorry

/-- Continuity on all of `ℝ` (needs the absence of an atom at `0`). -/
theorem continuous_supExpTail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    Continuous (supExpTail θ q) := sorry

theorem uniformContinuous_supExpTail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    UniformContinuous (supExpTail θ q) := sorry

/-- `H_q(x) = (q/Φ) ∫_x^∞ (W_q'-ΦW_q)` for `x ≥ 0`. -/
theorem supExpTail_eq_integral {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) {x : ℝ}
    (hx : 0 ≤ x) :
    supExpTail θ q x = q / q ^ (1 / θ) * ∫ y in Ioi x,
      (stableSeriesDeriv θ q y - q ^ (1 / θ) * stableSeries θ q y) := sorry

theorem supPotential_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    supPotential θ q 0 = q ^ (1 / θ) / q := sorry

theorem supPotential_mem_Icc {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) (x : ℝ) :
    supPotential θ q x ∈ Icc (0 : ℝ) (q ^ (1 / θ) / q) := sorry

/-- `h_q(0) - h_q(x) = W_q(x) - Φ ∫_0^x W_q(y)dy` for `x ≥ 0`. -/
theorem supPotential_zero_sub {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) {x : ℝ}
    (hx : 0 ≤ x) :
    supPotential θ q 0 - supPotential θ q x =
      stableSeries θ q x - q ^ (1 / θ) * ∫ y in Ioc 0 x, stableSeries θ q y := sorry

/-- `Φ h_q(0) = q^{2/θ-1}`: the Brownian correction constant. -/
theorem supPotential_zero_mul {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    q ^ (1 / θ) * supPotential θ q 0 = q ^ (2 / θ - 1) := sorry

/-- `q^{2/θ-1} → 1` if `θ = 2`, `→ 0` if `θ < 2`, as `q ↓ 0`. -/
theorem tendsto_rpow_two_div_sub_one {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    Tendsto (fun q : ℝ => q ^ (2 / θ - 1)) (𝓝[>] 0) (𝓝 (if θ = 2 then 1 else 0)) := sorry

/-- **Zero-resolvent asymptotics (blueprint R04 shape).** Locally uniformly in `x`,
`h_q(0) - h_q(x) → W(x)` as `q ↓ 0` (series `W_q → W` locally uniformly). -/
theorem tendstoUniformlyOn_supPotential_zero_sub {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (K : ℝ) :
    TendstoUniformlyOn (fun q x => supPotential θ q 0 - supPotential θ q x) (stableScale θ)
      (𝓝[>] 0) (Icc 0 K) := sorry

theorem tendstoUniformlyOn_stableSeries_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (K : ℝ) :
    TendstoUniformlyOn (fun q x => stableSeries θ q x) (stableScale θ) (𝓝[>] 0) (Icc 0 K) := sorry

/-! ### The resolvent of the occupation kernel -/

theorem measurable_supOccKernel (ε : ℝ) : Measurable (supOccKernel ε) := sorry

theorem supOccKernel_mem_Icc {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    supOccKernel ε r ∈ Icc (0 : ℝ) ε⁻¹ := sorry

theorem measurable_reflectedResolvent {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q : ℝ) {k : ℝ → ℝ}
    (hk : Measurable k) (hkb : ∃ C, ∀ e, |k e| ≤ C) : Measurable (reflectedResolvent θ q k) := sorry

/-- `|U_q k| ≤ C/q`, on all of `ℝ`. -/
theorem abs_reflectedResolvent_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q)
    {k : ℝ → ℝ} (hk : Measurable k) {C : ℝ} (hC : ∀ e, |k e| ≤ C) (y : ℝ) :
    |reflectedResolvent θ q k y| ≤ C / q := sorry

theorem reflectedResolvent_sub {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q)
    {k₁ k₂ : ℝ → ℝ} (h₁ : Measurable k₁) (h₂ : Measurable k₂) (b₁ : ∃ C, ∀ e, |k₁ e| ≤ C)
    (b₂ : ∃ C, ∀ e, |k₂ e| ≤ C) (y : ℝ) :
    reflectedResolvent θ q (fun r => k₁ r - k₂ r) y =
      reflectedResolvent θ q k₁ y - reflectedResolvent θ q k₂ y := sorry

/-- **Explicit resolvent formula**: `u^q_ε(y) = ε⁻¹ ∫_0^ε e^{-Φ(ε-r)} h_q(y-r) dr`, `y ≥ 0`. -/
theorem supOccupationResolvent_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) {ε : ℝ}
    (hε : 0 < ε) {y : ℝ} (hy : 0 ≤ y) :
    supOccupationResolvent θ q ε y =
      ε⁻¹ * ∫ r in Ioc 0 ε, Real.exp (-(q ^ (1 / θ) * (ε - r))) * supPotential θ q (y - r) := sorry

/-- `0 ≤ u^q_ε ≤ Φ/q`, on all of `ℝ`. -/
theorem supOccupationResolvent_mem_Icc {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q)
    {ε : ℝ} (hε : 0 < ε) (y : ℝ) :
    supOccupationResolvent θ q ε y ∈ Icc (0 : ℝ) (q ^ (1 / θ) / q) := sorry

/-- Monotone (nonincreasing) in the start. -/
theorem antitoneOn_supOccupationResolvent {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q)
    {ε : ℝ} (hε : 0 < ε) : AntitoneOn (supOccupationResolvent θ q ε) (Ici 0) := sorry

theorem continuousOn_supOccupationResolvent {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q)
    {ε : ℝ} (hε : 0 < ε) : ContinuousOn (supOccupationResolvent θ q ε) (Ici 0) := sorry

/-- **Uniform convergence over ALL `y ≥ 0`**: `u^q_ε → h_q` as `ε ↓ 0`. -/
theorem tendstoUniformlyOn_supOccupationResolvent {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ}
    (hq : 0 < q) :
    TendstoUniformlyOn (fun ε y => supOccupationResolvent θ q ε y) (supPotential θ q)
      (𝓝[>] 0) (Ici 0) := sorry

/-- Cauchy form at `q = 1` used by R05: `d_{ε,η} = ‖u¹_ε-u¹_η‖_∞ → 0`. -/
theorem exists_forall_abs_supOccupationResolvent_sub_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ a : ℝ, 0 < a ∧ ∀ ε η : ℝ, 0 < ε → ε < a → 0 < η → η < a → ∀ y : ℝ,
      |supOccupationResolvent θ 1 ε y - supOccupationResolvent θ 1 η y| ≤ δ := sorry

/-! ### Zero-resolvent correction (for R10) -/

/-- Locally uniform in `y ≥ 0`: `u^q_ε - h_q → v_ε` as `q ↓ 0`, for each `ε > 0`. -/
theorem tendstoLocallyUniformlyOn_supOccupationResolvent_sub {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ε : ℝ} (hε : 0 < ε) :
    TendstoLocallyUniformlyOn
      (fun q y => supOccupationResolvent θ q ε y - supPotential θ q y) (supCorrection θ ε)
      (𝓝[>] 0) (Ici 0) := sorry

theorem continuousOn_supCorrection {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (supCorrection θ ε) (Ici 0) := sorry

theorem supCorrection_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ} (hε : 0 < ε) :
    supCorrection θ ε 0 = -(if θ = 2 then ε / 2 else 0) := sorry

/-- `|v_ε| ≤ (1/Γ(θ) + 1/2) ε^{θ-1}` for every `ε > 0`, `y ≥ 0`. -/
theorem abs_supCorrection_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ} (hε : 0 < ε) {y : ℝ}
    (hy : 0 ≤ y) : |supCorrection θ ε y| ≤ (1 / Real.Gamma θ + 1 / 2) * ε ^ (θ - 1) := sorry

/-- Brownian case: `v_ε(y) = -(ε-y)_+² / (2ε)`. -/
theorem supCorrection_two {ε : ℝ} (hε : 0 < ε) {y : ℝ} (hy : 0 ≤ y) :
    supCorrection 2 ε y = -((max (ε - y) 0) ^ 2 / (2 * ε)) := sorry

/-! ### Markov hypothesis and second moments (discharged here, needs R01) -/

/-- **Conditional resolvent identity at every positive rate** (the rate-`q` form of the resolvent
Markov property; specializing `q = 1` gives `ResolventMarkov`).  Used by the zero-rate passage
`q ↓ 0` of the correction martingale; proved here from the R01 restart and Markov identities. -/
theorem condExp_reflectedResolvent_tail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q)
    (x s : ℝ≥0) {k : ℝ → ℝ} (hk : Measurable k) (hkb : ∃ C, ∀ e, |k e| ≤ C) :
    (stableLocalLaw θ : Measure DLoc)[fun f =>
      ∫ t in Ioi (s : ℝ), Real.exp (-q * t) * k (supReflectedFrom x f t.toNNReal) |
        DLoc.filtration s] =ᵐ[(stableLocalLaw θ : Measure DLoc)]
      fun f => Real.exp (-q * (s : ℝ)) * reflectedResolvent θ q k (supReflectedFrom x f s) :=
  sorry

/-- **`ResolventMarkov` for the reflected family**, every start `x ≥ 0`, bounded Borel `k`,
`V = U_1 k` (`q = 1`).  Proof: R01 `condExp_supReflectedFromLoc_markov` after the deterministic
restart, Fubini/Tonelli on the bounded integrand. -/
theorem resolventMarkov_supReflectedFrom {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0) {k : ℝ → ℝ}
    (hk : Measurable k) (hkb : ∃ C, ∀ e, |k e| ≤ C) :
    ResolventMarkov DLoc.filtration (stableLocalLaw θ : Measure DLoc)
      (fun t f => supReflectedFrom x f t) k (reflectedResolvent θ 1 k) := sorry

/-- The difference `k = g_ε - g_η`, `V = u¹_ε - u¹_η` (the R05a instance). -/
theorem resolventMarkov_supReflectedFrom_sub {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ResolventMarkov DLoc.filtration (stableLocalLaw θ : Measure DLoc)
      (fun t f => supReflectedFrom x f t) (fun r => supOccKernel ε r - supOccKernel η r)
      (fun y => supOccupationResolvent θ 1 ε y - supOccupationResolvent θ 1 η y) := sorry

/-- **Blueprint identity** `E_x(B_ε-B_η)² = 2 E_x ∫ e^{-2t}(g_ε-g_η)(R_t)(u¹_ε-u¹_η)(R_t)dt`
(R05a `integral_sq_discountedOccupation` with the instance above). -/
theorem integral_sq_discountedOccupation_supOccupation_sub {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (x : ℝ≥0) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∫ f, (discountedOccupation (fun t f => supReflectedFrom x f t)
        (fun r => supOccKernel ε r - supOccKernel η r) f) ^ 2 ∂(stableLocalLaw θ : Measure DLoc) =
      2 * ∫ f, (∫ t in Ioi (0 : ℝ), Real.exp (-2 * t) *
        ((supOccKernel ε (supReflectedFrom x f t.toNNReal) -
            supOccKernel η (supReflectedFrom x f t.toNNReal)) *
          (supOccupationResolvent θ 1 ε (supReflectedFrom x f t.toNNReal) -
            supOccupationResolvent θ 1 η (supReflectedFrom x f t.toNNReal))))
        ∂(stableLocalLaw θ : Measure DLoc) := sorry

/-- `E_x ∫ e^{-2t}|g_ε(R_t)| dt = u²_ε(x) ≤ Φ/q|_{q=2} = 2^{1/θ-1} ≤ 1`. -/
theorem integral_exp_neg_two_supOccKernel_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0) {ε : ℝ}
    (hε : 0 < ε) :
    ∫ f, (∫ t in Ioi (0 : ℝ), Real.exp (-2 * t) *
        |supOccKernel ε (supReflectedFrom x f t.toNNReal)|) ∂(stableLocalLaw θ : Measure DLoc) ≤
      1 := sorry

/-- **`E_x(B_ε-B_η)² ≤ 4 D`** whenever `‖u¹_ε-u¹_η‖_∞ ≤ D` (blueprint `≤ 4‖u¹_ε-u¹_η‖_∞`). -/
theorem integral_sq_discountedOccupation_supOccupation_sub_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (x : ℝ≥0) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) {D : ℝ}
    (hD : ∀ y : ℝ, |supOccupationResolvent θ 1 ε y - supOccupationResolvent θ 1 η y| ≤ D) :
    ∫ f, (discountedOccupation (fun t f => supReflectedFrom x f t)
        (fun r => supOccKernel ε r - supOccKernel η r) f) ^ 2 ∂(stableLocalLaw θ : Measure DLoc) ≤
      4 * D := sorry

/-- `E_x B_ε² ≤ 2` (AUDIT item 3), uniformly in `x ≥ 0`, `ε > 0`. -/
theorem integral_sq_discountedOccupation_supOccupation_le_two {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (x : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∫ f, (discountedOccupation (fun t f => supReflectedFrom x f t) (supOccKernel ε) f) ^ 2
        ∂(stableLocalLaw θ : Measure DLoc) ≤ 2 := sorry

end BGW.StableTrees
