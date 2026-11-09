import BGW.StableTrees.SupremumDrawdown
import BGW.StableTrees.SupremumReflectedFamily
import BGW.StableTrees.SupremumLocalTime
import BGW.StableTrees.StableLocalLaw
import Mathlib.MeasureTheory.Measure.Stieltjes
import BGW.StableTrees.SupremumPotential
import BGW.StableTrees.SupremumLadderRestart

/-! Contract probe for H01 node R09 (blueprint R09 "Boundary potential and exact joint
transform", §2 "Exact c = 1, including the bivariate exponent"; AUDIT: Sol-audit-r07r08 item 7,
the normalization still to prove): the BOUNDARY POTENTIAL
`E ∫_0^∞ e^{-qt-λS_t} dM_t = (Φ-λ)/(q-λ^θ) = 1/κ(q,λ)` and the EXACT joint ladder transform
`E exp(-q A_z - λ B_z) = exp(-z κ(q,λ))`, `κ = supLadderExponent`, normalization `c = 1`
exactly (nothing is assumed about the constant).  It proves the final-contract theorem
`integral_exp_neg_supLadder` (copied verbatim below as the target of this node).
NOT redefined (sealed, imported): `supRunning`, `supReflected`, `supOccupation`,
`supLadderExponent` and its three sealed lemmas `supLadderExponent_diagonal`
(`κ(q, q^{1/θ}) = θ q^{1-1/θ}`), `supLadderExponent_zero_right` (`κ(q,0) = q^{1-1/θ}`),
`supLadderExponent_zero_left` (`κ(0,λ) = λ^{θ-1}`); `expClockLaw`, R03's
`integral_exp_neg_supRunning_expTime(_diag)`, `expClockLaw_supReflected_gt`,
`indepFun_supRunning_supReflected_expTime`.
Definitions copied verbatim from R07 (`supEps … supLadderHeight`) and R04 (`supOccKernel`).
Suppliers consumed by the PROOFS (not restated): R07 `ae_supLocalTime_spec`,
`ae_tendsto_supOccupation_uniform`, `measurable_supLocalTime_uncurry`,
`measurable_supLadder_uncurry`, `ae_supLadder_spec` (`M(A_z) = z`, `A` monotone, right
continuous), `ae_supLadder_geometry` (`A → ∞`); R08 `iIndepFun_supLadderIncrement`,
`map_supLadderIncrement`, `ae_supLadderPair_zero`, `ae_supLadderPair_path`; R04
`integral_sq_discountedOccupation_supOccupation_le_two` (uniform integrability);
R03 as above.

Proof plan (not statements).  (1) `ε`-level exact identity (`integral_resolvent_…`): by
`E ∫ e^{-qt} G_t dt = q⁻¹ E G(e_q)` and independence of `S_{e_q}`, `R_{e_q}`.  (2) Pass
`ε ↓ 0` along `supEps θ`: `dO_ε → dM` weakly on `[0,T]` (locally uniform convergence of
continuous nondecreasing functions, `M` continuous so `dM` atomless, `t ↦ e^{-qt-λS_t}` has
countably many discontinuities), uniform integrability from `E B_ε² ≤ 2`, then remove the cutoff
`T` by the `e^{-qt}` tail.  (3) pathwise change of variables `t = A_z`, `S_{A_z} = B_z`
(`M` continuous, `M(A_z) = z`, `A_z ≤ t ↔ z ≤ M_t` up to one point).  (4) `φ(z) = E e^{-qA_z-λB_z}`
is multiplicative (R08), measurable, `φ(0) = 1`, right continuous at `0`, so `φ(z) = e^{-zk}` with
`k ∈ [0,∞)`; `∫_0^∞ φ = 1/k` equals the boundary potential `1/κ`; hence `k = κ`.
(5) `q = 0`: bounded convergence as `q ↓ 0` (`A_z < ∞` a.s.), plus continuity of `κ`.

CONSTANT CHECKS (hand computation, `Φ = q^{1/θ}`).
 * `(Φ/q) F_q(λ) = (Φ/q) q(Φ-λ)/(Φ(q-λ^θ)) = (Φ-λ)/(q-λ^θ) = 1/κ(q,λ)` for `λ ≠ Φ`.
 * Diagonal: `(Φ/q)(1/θ) = 1/(θ q^{1-1/θ}) = 1/κ(q,Φ)` (`q/Φ = q^{1-1/θ}`); consistent with
   the removable singularity `d/dλ(q-λ^θ) = -θ λ^{θ-1}`, `Φ^{θ-1} = q^{1-1/θ}`.
 * `κ(q,0) = q/Φ = q^{1-1/θ}`; `κ(0,λ) = λ^θ/λ = λ^{θ-1}`; `κ(0,0) = 0`.
 * `θ = 2`: `κ = (q-λ²)/(√q-λ) = √q + λ`; diagonal `2√q = θ q^{1-1/2}`; `M = S` (not `2S`).
 * `q = 1, λ = 0`: potential `= Φ/q = 1`, the clock is non-trivial; `E[M(A_z)] = z`.
 No numerical inconsistency found in the blueprint.

FLAGS.
(1) Potential is stated in `ℝ≥0∞` (`∫⁻`), so no real-integral junk; the pathwise boundary
integral may be infinite on a null set.  `q > 0` is needed for the potential; `q = 0` is only
reached for the LADDER transform (bounded convergence), as the blueprint says.
(2) Blueprint §2 says `(q,λ) = (0,0)` is "handled separately": it is `φ ≡ 1` since `κ(0,0) = 0`
(`supLadderExponent_zero_right` at `q = 0`); no analytic argument needed.
(3) The semigroup property uses the ladder increments of R08 (stationary, independent) at
deterministic levels `y, z`; it is stated for the pair `(A, B)` at levels `0 ≤ y ≤ z`.
(4) Blueprint's `k(q,λ)` is the contract's `supLadderExponent` (same formula and diagonal).
(5) Estimate 650-1100 lines. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

open scoped Classical in
open scoped Classical in
/-! ### Definitions of this node -/

/-- The boundary potential of the path: `∫_{(0,∞)} e^{-qt-λS_t} dM_t`, `M = supLocalTime`
(Stieltjes measure of the contract's `supLocalTimeStieltjes`), in `ℝ≥0∞` (no junk). -/
noncomputable def supBoundaryPotential (θ q lam : ℝ) (f : DLoc) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ),
    ENNReal.ofReal (Real.exp (-q * t - lam * supRunning f t.toNNReal))
      ∂(supLocalTimeStieltjes θ f).measure

/-- The ladder Laplace transform `φ_{q,λ}(z) = E exp(-q A_z - λ B_z)`. -/
noncomputable def supLadderLaplace (θ q lam : ℝ) (z : ℝ≥0) : ℝ :=
  ∫ f, Real.exp (-q * (supLadderTime θ z f : ℝ) - lam * supLadderHeight θ z f)
    ∂(stableLocalLaw θ : Measure DLoc)

/-! ### The exponent `κ` and the exponential-time transform -/

/-- `κ(q,λ) > 0` for `q > 0`, `λ ≥ 0` (both branches; diagonal `θ q^{1-1/θ} > 0`). -/
theorem supLadderExponent_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ} (hq : 0 < q)
    (hlam : 0 ≤ lam) : 0 < supLadderExponent θ q lam := sorry

/-- **`1/κ` is the mean potential** `(Φ/q) F_q(λ)`, including the diagonal
(`F_q(Φ) = 1/θ`, R03).  Pure algebra from R03; no ladder object enters. -/
theorem inv_supLadderExponent_eq_integral {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ}
    (hq : 0 < q) (hlam : 0 ≤ lam) :
    (supLadderExponent θ q lam)⁻¹ =
      q ^ (1 / θ) / q *
        ∫ p, Real.exp (-lam * supRunning p.1 p.2.toNNReal) ∂expClockLaw θ q := sorry

/-- Off the diagonal: `1/κ = (Φ-λ)/(q-λ^θ)` (blueprint display in §2). -/
theorem inv_supLadderExponent_eq_of_ne {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ}
    (hq : 0 < q) (hlam : 0 ≤ lam) (hne : lam ≠ q ^ (1 / θ)) :
    (supLadderExponent θ q lam)⁻¹ = (q ^ (1 / θ) - lam) / (q - lam ^ θ) := sorry

/-- Continuity of `κ` in `q ↓ 0` at fixed `λ ≥ 0` (to `κ(0,λ) = λ^{θ-1}`; at `λ = 0` the
value is `0`), needed to pass from `q > 0` to `q = 0`. -/
theorem tendsto_supLadderExponent_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {lam : ℝ}
    (hlam : 0 ≤ lam) :
    Tendsto (fun q : ℝ => supLadderExponent θ q lam) (𝓝[>] 0)
      (𝓝 (supLadderExponent θ 0 lam)) := sorry

/-! ### Boundary potential (blueprint §2, first display) -/

/-- **`ε`-level exact identity.**  For `q, ε > 0`, `λ ≥ 0`: with `g_ε` the occupation kernel,
`E ∫_0^∞ e^{-qt} e^{-λ S_t} g_ε(R_t) dt = q⁻¹ ε⁻¹ (1 - e^{-εΦ}) E e^{-λ S_{e_q}}`
(`E ∫ e^{-qt} G_t dt = q⁻¹ E G(e_q)`, independence of `S_{e_q}` and `R_{e_q}`,
`R_{e_q} ~ Exp(Φ)`). -/
theorem integral_resolvent_exp_neg_supRunning {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam ε : ℝ}
    (hq : 0 < q) (hlam : 0 ≤ lam) (hε : 0 < ε) :
    ∫ f, (∫ t in Ioi (0 : ℝ), Real.exp (-q * t) *
        (Real.exp (-lam * supRunning f t.toNNReal) *
          supOccKernel ε (supReflected f t.toNNReal))) ∂(stableLocalLaw θ : Measure DLoc) =
      q⁻¹ * (ε⁻¹ * (1 - Real.exp (-(ε * q ^ (1 / θ))))) *
        ∫ p, Real.exp (-lam * supRunning p.1 p.2.toNNReal) ∂expClockLaw θ q := sorry

/-- **Boundary potential, mean form.** For `q > 0`, `λ ≥ 0`:
`E ∫_0^∞ e^{-qt-λS_t} dM_t = (Φ/q) E e^{-λ S_{e_q}}`
(limit `ε ↓ 0` of the previous identity along `supEps θ`: weak convergence of `dO_ε`,
uniform integrability, tail removal by the `e^{-qt}` factor). -/
theorem lintegral_supBoundaryPotential_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ}
    (hq : 0 < q) (hlam : 0 ≤ lam) :
    ∫⁻ f, supBoundaryPotential θ q lam f ∂(stableLocalLaw θ : Measure DLoc) =
      ENNReal.ofReal (q ^ (1 / θ) / q *
        ∫ p, Real.exp (-lam * supRunning p.1 p.2.toNNReal) ∂expClockLaw θ q) := sorry

/-- **Boundary potential, exact form**: `E ∫_0^∞ e^{-qt-λS_t} dM_t = 1/κ(q,λ)`. -/
theorem lintegral_supBoundaryPotential {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ}
    (hq : 0 < q) (hlam : 0 ≤ lam) :
    ∫⁻ f, supBoundaryPotential θ q lam f ∂(stableLocalLaw θ : Measure DLoc) =
      ENNReal.ofReal (supLadderExponent θ q lam)⁻¹ := sorry

/-- Zero-order case `λ = 0`: `E ∫_0^∞ e^{-qt} dM_t = Φ/q = q^{1/θ - 1}` (`= 1` at `q = 1`). -/
theorem lintegral_supBoundaryPotential_zero_right {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ}
    (hq : 0 < q) :
    ∫⁻ f, supBoundaryPotential θ q 0 f ∂(stableLocalLaw θ : Measure DLoc) =
      ENNReal.ofReal (q ^ (1 / θ) / q) := sorry

/-! ### Change of variables `t = A_z` -/

/-- **Stieltjes substitution** (pathwise, `q, λ ≥ 0`): almost surely
`∫_{(0,∞)} e^{-q A_z - λ B_z} dz = ∫_{(0,∞)} e^{-qt-λS_t} dM_t`
(`M` continuous nondecreasing, `M(A_z) = z`, `B_z = S_{A_z}`; `dM = A_* Leb`). -/
theorem ae_lintegral_supLadder_eq_supBoundaryPotential {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q lam : ℝ} (hq : 0 ≤ q) (hlam : 0 ≤ lam) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ∫⁻ z in Ioi (0 : ℝ),
          ENNReal.ofReal (Real.exp (-q * (supLadderTime θ z.toNNReal f : ℝ) -
            lam * supLadderHeight θ z.toNNReal f)) = supBoundaryPotential θ q lam f := sorry

/-! ### The ladder Laplace transform is a semigroup -/

theorem supLadderLaplace_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q lam : ℝ) :
    supLadderLaplace θ q lam 0 = 1 := sorry

theorem supLadderLaplace_mem_Icc {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ} (hq : 0 ≤ q)
    (hlam : 0 ≤ lam) (z : ℝ≥0) : supLadderLaplace θ q lam z ∈ Icc (0 : ℝ) 1 := sorry

theorem measurable_supLadderLaplace {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q lam : ℝ) :
    Measurable (supLadderLaplace θ q lam) := sorry

/-- **Multiplicativity**: `φ(y + z) = φ(y) φ(z)` (restart at `A_y`, independent stationary
increments, R08). -/
theorem supLadderLaplace_add {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ} (hq : 0 ≤ q)
    (hlam : 0 ≤ lam) (y z : ℝ≥0) :
    supLadderLaplace θ q lam (y + z) = supLadderLaplace θ q lam y * supLadderLaplace θ q lam z :=
  sorry

/-- Right continuity at `0` (right continuity of `(A,B)` and bounded convergence). -/
theorem tendsto_supLadderLaplace_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ} (hq : 0 ≤ q)
    (hlam : 0 ≤ lam) :
    Tendsto (supLadderLaplace θ q lam) (𝓝[>] 0) (𝓝 1) := sorry

/-- **Exponential form** (measurable multiplicative Cauchy equation, positivity from
`φ(z/2ⁿ) → 1`): there is a rate `k ≥ 0` with `φ(z) = e^{-zk}` for all `z`. -/
theorem exists_supLadderLaplace_eq_exp {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ}
    (hq : 0 ≤ q) (hlam : 0 ≤ lam) :
    ∃ k : ℝ, 0 ≤ k ∧ ∀ z : ℝ≥0, supLadderLaplace θ q lam z = Real.exp (-(z : ℝ) * k) := sorry

/-- Tonelli: `∫_0^∞ φ(z) dz = E ∫_0^∞ e^{-qA_z - λB_z} dz = E ∫ e^{-qt-λS_t} dM_t`. -/
theorem lintegral_supLadderLaplace_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ}
    (hq : 0 ≤ q) (hlam : 0 ≤ lam) :
    ∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal (supLadderLaplace θ q lam z.toNNReal) =
      ∫⁻ f, supBoundaryPotential θ q lam f ∂(stableLocalLaw θ : Measure DLoc) := sorry

/-! ### The exact transform -/

/-- **Exact normalization for `q > 0`**: `φ(z) = exp(-z κ(q,λ))`, `c = 1`. -/
theorem supLadderLaplace_eq_of_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ} (hq : 0 < q)
    (hlam : 0 ≤ lam) (z : ℝ≥0) :
    supLadderLaplace θ q lam z = Real.exp (-(z : ℝ) * supLadderExponent θ q lam) := sorry

/-- Bounded convergence in `q ↓ 0` at fixed level (`A_z < ∞` a.s.). -/
theorem tendsto_supLadderLaplace_zero_rate {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {lam : ℝ}
    (hlam : 0 ≤ lam) (z : ℝ≥0) :
    Tendsto (fun q : ℝ => supLadderLaplace θ q lam z) (𝓝[>] 0)
      (𝓝 (supLadderLaplace θ 0 lam z)) := sorry

/-- **Exact transform for all `q, λ ≥ 0`** (including `q = 0` and `(0,0)`). -/
theorem supLadderLaplace_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ} (hq : 0 ≤ q)
    (hlam : 0 ≤ lam) (z : ℝ≥0) :
    supLadderLaplace θ q lam z = Real.exp (-(z : ℝ) * supLadderExponent θ q lam) := sorry

/-- **Diagonal value**: `E exp(-q A_z - q^{1/θ} B_z) = exp(-z θ q^{1-1/θ})`
(from `supLadderExponent_diagonal`). -/
theorem supLadderLaplace_diagonal {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 ≤ q)
    (z : ℝ≥0) :
    supLadderLaplace θ q (q ^ (1 / θ)) z = Real.exp (-(z : ℝ) * (θ * q ^ (1 - 1 / θ))) := sorry

/-- Start at the origin: `A_0 = 0 = B_0` almost surely. -/
theorem ae_supLadder_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      supLadderTime θ 0 f = 0 ∧ supLadderHeight θ 0 f = 0 := sorry

/-- **Joint ladder transform** (final-contract statement, verbatim; normalization `c = 1`)
at every deterministic level `z ≥ 0`, and its two marginals (`κ(q,0) = q^{1-1/θ}`,
`κ(0,λ) = λ^{θ-1}`): `E exp(-q A_z - λ B_z) = exp(-z κ(q, λ))` for `q, λ ≥ 0`. -/
theorem integral_exp_neg_supLadder {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) {q lam : ℝ}
    (hq : 0 ≤ q) (hlam : 0 ≤ lam) :
    (∫ f, Real.exp (-q * (supLadderTime θ z f : ℝ) - lam * supLadderHeight θ z f)
          ∂(stableLocalLaw θ : Measure DLoc) =
        Real.exp (-(z : ℝ) * supLadderExponent θ q lam)) ∧
      (∫ f, Real.exp (-q * (supLadderTime θ z f : ℝ)) ∂(stableLocalLaw θ : Measure DLoc) =
        Real.exp (-(z : ℝ) * q ^ (1 - 1 / θ))) ∧
      (∫ f, Real.exp (-lam * supLadderHeight θ z f) ∂(stableLocalLaw θ : Measure DLoc) =
        Real.exp (-(z : ℝ) * lam ^ (θ - 1))) := sorry

end BGW.StableTrees
