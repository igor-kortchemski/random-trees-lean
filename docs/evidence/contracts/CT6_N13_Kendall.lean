import BGW.StableTrees.WalkPassage
import BGW.StableTrees.StablePassageSubordinator
import BGW.StableTrees.StableDensityAPI
import BGW.StableTrees.Scalar.LocalLimit
import BGW.StableTrees.Scalar.Lattice
import BGW.StableTrees.Scalar.Normalization

/-! Contract probe for CT.C6 blueprint Node 13: **Kendall's identity (F4)** for the spectrally
positive stable process, with the lattice cancellation.

Sealed/built inputs reused (imported, not re-declared): `passageLaw`, `walkPassageLaw`,
`walkHitTime`, `walkHitTime_mass_toReal` (Kemperman), `tendsto_walkPassageLaw` (N12),
`passageLaw_isProbabilityMeasure`, `passageLaw_Iic_zero`, `stableDensityAt`,
`stableDensityAt_jointContinuous`, `Scalar.localLimit`, `Scalar.walkProb_eq_zero_of_not_dvd`,
`Scalar.tendsto_div_of_tendsto_div`, `Scalar.latticeSpan`.

Sign convention (checked). `StableDomain μ θ B` has `E e^{-λ X_1} = e^{λ^θ}`: `X` is spectrally
positive (no negative jumps) and `X_t ~ stableDensityAt θ t`. `T_x = inf{t | X_t < -x}` is the
passage BELOW `-x`, so the density is `(x/t) p_t(-x)` (Kendall / ballot theorem, in the form
`P(T_x ∈ dt)/dt = (x/t) P(X_t ∈ -x)`), matching the discrete Kemperman formula
`P(hit -ℓ at k) = (ℓ/k) P(S_k = -ℓ)`. Sanity: `θ = 2` gives the Brownian-type law
`(x/t) p_t(-x)` with `p_t` the (non-standard-variance) Gaussian density.

Lattice cancellation (checked by hand). Let `d = latticeSpan μ`, `ℓ = ℓ n`, `k = ⌊s n⌋`,
`s = k/n ∈ [a,b]`, `ℓ n / B n → x`. The Fourier LLT (`localLimit`) says, for `d ∣ -ℓ + k`,
`B_k P(S_k = -ℓ) = d p_1(-ℓ/B_k) + o(1)`; off the residue class `P(S_k = -ℓ) = 0`. By
`tendsto_div_of_tendsto_div`, `B_n/B_k → s^{-1/θ}`, so `ℓ/B_k → x s^{-1/θ}`. Kemperman gives
`n P(τ=k) = (ℓ/s)/k · ... = (ℓ/(s B_k)) · B_k P(S_k=-ℓ)`, whence on the residue class
`n P(τ_ℓ = k) → d (x/s) p_s(-x)`, with `p_s(-x) = s^{-1/θ} p_1(-x s^{-1/θ})`.
The residue class `k ≡ ℓ (mod d)` has density `1/d` among integers, so the Riemann sum over it with
mesh `d/n` has total weight `(1/n) Σ_{k ≡ ℓ} d g(k/n) → ∫ g`: the factor `d` cancels exactly.
No `d` survives in `passageLaw`. Maintained file: new `BGW/StableTrees/StableKendall.lean`
(700-1300 lines). -/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open BGW.Skorokhod BGW.StableTrees BGW.Probability.RealWalk

namespace BGW.StableTrees

/-- The Kendall kernel `s ↦ (x/s) p_s(-x)`, `s > 0`, `x > 0` (junk elsewhere). -/
noncomputable def kendallKernel (θ x s : ℝ) : ℝ := x / s * stableDensityAt θ s (-x)

/-- The kernel is nonnegative for `x ≥ 0`, `s > 0`. -/
theorem kendallKernel_nonneg {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {x s : ℝ} (hx : 0 ≤ x) (hs : 0 < s) :
    0 ≤ kendallKernel θ x s := sorry

/-- Continuity of the Kendall density in time (and jointly in the level) for `s > 0`. -/
theorem kendallKernel_continuousOn {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ContinuousOn (fun z : ℝ × ℝ => kendallKernel θ z.1 z.2) {z | 0 < z.2} := sorry

theorem continuousOn_kendallKernel_time {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ) :
    ContinuousOn (kendallKernel θ x) (Ioi 0) := sorry

/-- **Local density limit for the walk passage time, with lattice cancellation.**
Let `d = latticeSpan μ`, `ℓ n / B n → x > 0`, `0 < a ≤ b`. Uniformly over `k ∈ [a n, b n]`
with `d ∣ k - ℓ n`, `n P(first hit of -ℓ n at time k) → d · (x/(k/n)) p_{k/n}(-x)`. -/
theorem tendsto_local_walkHitTime_mass {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {x : ℝ} (hx : 0 < x) {ℓ : ℕ → ℕ} (hℓ : ∀ᶠ n in atTop, 1 ≤ ℓ n)
    (hscale : Tendsto (fun n : ℕ => (ℓ n : ℝ) / B n) atTop (𝓝 x)) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, a * (n : ℝ) ≤ k → (k : ℝ) ≤ b * (n : ℝ) →
      ((Scalar.latticeSpan μ : ℤ) ∣ (k : ℤ) - ℓ n) →
        |(n : ℝ) * (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)).real
              {w | walkHitTime (ℓ n) w = (k : ℕ∞)} -
            Scalar.latticeSpan μ * kendallKernel θ x ((k : ℝ) / n)| ≤ ε := sorry

/-- Off the residue class `k ≡ ℓ (mod d)` the first-hit mass vanishes (Kemperman + LLT support). -/
theorem walkHitTime_mass_eq_zero_of_not_dvd {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {k : ℕ}
    (hk : ¬ (Scalar.latticeSpan μ : ℤ) ∣ (k : ℤ) - ℓ) :
    (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)).real
      {w | walkHitTime ℓ w = (k : ℕ∞)} = 0 := sorry

/-- The mass of the walk passage law as a series over the hitting time (`ℓ ≥ 1`):
`∫ g d(walkPassageLaw) = Σ_k g(k/n) P(hit = k)` for bounded `g` vanishing on `(-∞, 0]`. -/
theorem integral_walkPassageLaw_eq_tsum {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {n : ℕ} (hn : 1 ≤ n) (g : BoundedContinuousFunction ℝ ℝ)
    (hg : ∀ t ≤ 0, g t = 0) :
    ∫ t, g t ∂(walkPassageLaw μ ℓ n) =
      ∑' k : ℕ, g ((k : ℝ) / n) *
        (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)).real
          {w | walkHitTime ℓ w = (k : ℕ∞)} := sorry

/-- **Arithmetic-progression Riemann sum** (the lattice factor cancels): for continuous `g` with
compact support inside `(0, ∞)`, `d ≥ 1`, and any integers `ℓ n`,
`(d/n) Σ_{k ≥ 0, d ∣ k - ℓ n} g(k/n) → ∫ g`. -/
theorem tendsto_progression_riemann_sum {d : ℕ} (hd : 0 < d) (ℓ : ℕ → ℕ) {g : ℝ → ℝ}
    (hg : Continuous g) (hsupp : HasCompactSupport g) (hpos : tsupport g ⊆ Ioi 0) :
    Tendsto (fun n : ℕ => ∑' k : ℕ,
        if (d : ℤ) ∣ (k : ℤ) - ℓ n then (d : ℝ) / n * g ((k : ℝ) / n) else 0)
      atTop (𝓝 (∫ s, g s)) := sorry

/-- **Uniform integrability / tightness near `0`** needed to pass from local densities on compacts
to the full law: no mass of `walkPassageLaw` escapes to `0` or `∞` (follows from N12 weak
convergence and `passageLaw_Iic_zero`; no `walkHitTime` tail bound is assumed). -/
theorem walkPassageLaw_tight {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {x : ℝ≥0} (hx : 0 < x) {ℓ : ℕ → ℕ} (hℓ : ∀ᶠ n in atTop, 1 ≤ ℓ n)
    (hscale : Tendsto (fun n : ℕ => (ℓ n : ℝ) / B n) atTop (𝓝 (x : ℝ))) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ R : ℝ, δ < R ∧ ∀ᶠ n in atTop,
      walkPassageLaw μ (ℓ n) n (Iio δ) + walkPassageLaw μ (ℓ n) n (Ioi R) ≤ ENNReal.ofReal ε :=
  sorry

/-- **Weak limit against compactly supported tests.** The density limit is compared with N12:
`∫ g d(walkPassageLaw (ℓ n) n) → ∫ g(s) (x/s) p_s(-x) ds` for `g` continuous with compact support
in `(0,∞)`. -/
theorem tendsto_integral_walkPassageLaw_kendall {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {x : ℝ} (hx : 0 < x) {ℓ : ℕ → ℕ}
    (hℓ : ∀ᶠ n in atTop, 1 ≤ ℓ n)
    (hscale : Tendsto (fun n : ℕ => (ℓ n : ℝ) / B n) atTop (𝓝 x)) {g : ℝ → ℝ}
    (hg : Continuous g) (hsupp : HasCompactSupport g) (hpos : tsupport g ⊆ Ioi 0) :
    Tendsto (fun n : ℕ => ∫ t, g t ∂(walkPassageLaw μ (ℓ n) n)) atTop
      (𝓝 (∫ s in Ioi 0, g s * kendallKernel θ x s)) := sorry

/-- **Kendall, tested against compactly supported continuous functions.** Combining the previous
statement with N12 (`tendsto_walkPassageLaw`) and uniqueness of weak limits. -/
theorem integral_passageLaw_eq_kendall {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {x : ℝ≥0} (hx : 0 < x)
    {g : ℝ → ℝ} (hg : Continuous g) (hsupp : HasCompactSupport g) (hpos : tsupport g ⊆ Ioi 0) :
    ∫ t, g t ∂(passageLaw θ x) = ∫ s in Ioi 0, g s * kendallKernel θ (x : ℝ) s := sorry

/-- **Kendall's identity (N13, blueprint `kendall`)** for EVERY `x > 0` (not just a.e. `x`):
the law of `T_x = inf{t | X_t < -x}` on real time has density `(x/s) p_s(-x)` on `(0, ∞)`. -/
theorem kendall {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {x : ℝ≥0} (hx : 0 < x) :
    passageLaw θ x =
      (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun s => ENNReal.ofReal (x / s * stableDensityAt θ s (-(x : ℝ)))) := sorry

/-- Corollary: total mass one of the Kendall density. -/
theorem lintegral_kendallKernel {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {x : ℝ≥0} (hx : 0 < x) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (kendallKernel θ (x : ℝ) s) = 1 := sorry

end BGW.StableTrees
