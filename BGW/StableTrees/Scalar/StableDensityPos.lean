/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableLaw
public import BGW.StableTrees.KendallAdapter
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! # Strict positivity of the stable density

The convolution semigroup propagates positivity of `p₁(y)` to `pₙ(n y)` for every
positive integer `n`. Scaling then propagates positivity to every real argument:
`n^(1/θ - 1) x` tends to zero, where the density is continuous and strictly positive.
This also proves strict positivity of the Gamma factor in Kendall's identity.

Reference: V. M. Zolotarev, *One-dimensional Stable Distributions*, AMS, 1986, Section 2.7.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace BGW.StableTrees

private theorem densityAt_continuous {θ t : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    Continuous (stableDensityAt θ t) := by
  unfold stableDensityAt
  exact continuous_const.mul ((Scalar.continuous_stableDensity hθ).comp
    (continuous_const.mul continuous_id))

private theorem densityAt_nonneg {θ t : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ht : 0 < t)
    (x : ℝ) : 0 ≤ stableDensityAt θ t x :=
  mul_nonneg (Real.rpow_nonneg ht.le _) (stableDensity_nonneg hθ _)

private theorem densityAt_integrable {θ t : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ht : 0 < t) :
    Integrable (stableDensityAt θ t) := by
  obtain ⟨μ, a, h⟩ := exists_stableDomain hθ
  have hc : t ^ (-1 / θ) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  exact ((integrable_comp_mul_left_iff _ hc).2
    (Scalar.integrable_stableDensity h)).const_mul _

private theorem densityAt_add_pos {θ s t u v : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (hs : 0 < s) (ht : 0 < t) (hu : 0 < stableDensityAt θ s u)
    (hv : 0 < stableDensityAt θ t v) : 0 < stableDensityAt θ (s + t) (u + v) := by
  rw [← integral_stableDensityAt_mul hθ hs ht]
  have hc : Continuous (fun y => stableDensityAt θ t (u + v - y)) :=
    (densityAt_continuous hθ).comp (continuous_const.sub continuous_id)
  obtain ⟨M, -, hM⟩ := Scalar.exists_stableDensity_le (α := θ)
  have hb (y : ℝ) : ‖stableDensityAt θ t (u + v - y)‖ ≤ t ^ (-1 / θ) * M := by
    rw [Real.norm_eq_abs, abs_of_nonneg (densityAt_nonneg hθ ht _)]
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hM _))
      (Real.rpow_nonneg ht.le _)
  apply integral_pos_of_integrable_nonneg_nonzero
    ((densityAt_continuous hθ).mul hc)
    ((densityAt_integrable hθ hs).mul_bdd hc.aestronglyMeasurable
      (Eventually.of_forall hb))
    (fun y => mul_nonneg (densityAt_nonneg hθ hs y) (densityAt_nonneg hθ ht _))
    (x := u)
  simpa using (mul_pos hu hv).ne'

private theorem densityAt_nat_mul_pos {θ y : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (hy : 0 < Scalar.stableDensity θ y) (n : ℕ) (hn : 0 < n) :
    0 < stableDensityAt θ n (n * y) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      simpa [stableDensityAt] using hy
    · have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
      have h1 : 0 < stableDensityAt θ 1 y := by simpa [stableDensityAt] using hy
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
        densityAt_add_pos hθ hnpos zero_lt_one (ih (Nat.pos_of_ne_zero hn0)) h1

/-- The stable density is strictly positive on all of `ℝ`. -/
theorem stableDensity_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ) :
    0 < Scalar.stableDensity θ x := by
  have hθ0 : 0 < θ := by linarith [hθ.1]
  have he : 0 < 1 - 1 / θ := by
    have := (div_lt_one hθ0).2 hθ.1
    linarith
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / θ - 1) * x) atTop (𝓝 0) := by
    have hpow := (tendsto_rpow_neg_atTop he).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_apply, neg_sub, zero_mul] using hpow.mul_const x
  have hp : ∀ᶠ n : ℕ in atTop,
      0 < Scalar.stableDensity θ ((n : ℝ) ^ (1 / θ - 1) * x) :=
    hlim.eventually ((Scalar.continuous_stableDensity hθ).continuousAt.eventually
      (isOpen_Ioi.mem_nhds (Scalar.stableDensity_zero_pos hθ)))
  obtain ⟨n, hpn, hn⟩ := (hp.and (eventually_gt_atTop 0)).exists
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have h := densityAt_nat_mul_pos hθ hpn n hn
  have hscale : (n : ℝ) ^ (-1 / θ) *
      (n * ((n : ℝ) ^ (1 / θ - 1) * x)) = x := by
    calc
      _ = ((n : ℝ) ^ (-1 / θ) * (n : ℝ) ^ (1 : ℝ) *
          (n : ℝ) ^ (1 / θ - 1)) * x := by rw [Real.rpow_one]; ring
      _ = (n : ℝ) ^ ((-1 / θ + 1) + (1 / θ - 1)) * x := by
        rw [← Real.rpow_add hnpos, ← Real.rpow_add hnpos]
      _ = x := by rw [show (-1 / θ + 1) + (1 / θ - 1) = 0 by ring]; simp
  rw [stableDensityAt, hscale] at h
  exact (mul_pos_iff_of_pos_left (Real.rpow_pos_of_pos hnpos _)).mp h

/-- Strict positivity of the Gamma factor: `Γ_a(x) > 0` for `a < 1`, `x > 0`; with
`continuousOn_gammaA` (sealed) and `gammaA_nonneg` (sealed) this completes the item. -/
theorem gammaA_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {a x : ℝ} (ha : a < 1) (hx : 0 < x) :
    0 < gammaA θ a x := by
  have ht : 0 < 1 - a := sub_pos.mpr ha
  unfold gammaA qKernel stableDensityAt
  exact div_pos (mul_pos (by linarith [hθ.1])
    (mul_pos (div_pos hx ht)
      (mul_pos (Real.rpow_pos_of_pos ht _) (stableDensity_pos hθ _))))
    (sizeTailKernel_pos hθ ht hx)

end BGW.StableTrees
