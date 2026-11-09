import BGW.ContinuumTrees.BrownianD
import BGW.StableTrees.StableProcess
import BGW.StableTrees.Scalar.FiniteVariance

/-! Contract probe for CT5 blueprint Node 20 (P6, identification of index two with Brownian motion)
and its finite-variance corollary (Node 21).

Maintained file (proposed): `BGW/StableTrees/StableProcessBrownian.lean`.

Notes.
* Normalization: `stableLawAt 2 t = gaussianReal 0 (2 t)` (sealed `stableLaw_two`), i.e.
  `E e^{-l X_t} = e^{t l²}`, variance `2 t`. The sealed `wienerD c T` is the law of `c · B` (variance
  `c² t`), so the correct constant is `c = √2` = `NNReal.sqrt 2`. The sealed lemma
  `integral_exp_neg_eval_wienerD_sqrt_two` already records `∫ e^{-l f t} = e^{t l²}`. Not `c = 1`.
* The blueprint's `sqrtTwoBrownianPath` is not introduced: `wienerD (NNReal.sqrt 2) T` is the
  same pushforward (`coe_wienerD`), so the statement is stated against the sealed definition.
* Parameter conventions: `stableProcessLaw θ T` has junk value unless `1 < θ ≤ 2` and `0 < T`;
  here `θ = 2` and `0 < T` are both in range. `θ = 2` is the endpoint of the index range.
* The corollary uses the sealed `StableDomain.tendsto_stepPathLaw` (θ = 2 included) so it is a
  rewriting, plus `exists_stableDomain` for a witness (finite variance, e.g. the critical
  offspring law with variance normalization). No new hypotheses. -/

open MeasureTheory Filter
open scoped Topology

namespace BGW.StableTrees

open BGW.Skorokhod BGW.ContinuumTrees.BrownianD

/-- CT5 P6: at `θ = 2` the stable process law is the law of `√2 · B`. -/
theorem stableProcessLaw_two {T : ℝ} (hT : 0 < T) :
    stableProcessLaw 2 T = wienerD (NNReal.sqrt 2) T := by
  sorry

/-- Measure form of `stableProcessLaw_two`. -/
theorem coe_stableProcessLaw_two {T : ℝ} (hT : 0 < T) :
    (stableProcessLaw 2 T : Measure (D T ℝ)) =
      (wienerD (NNReal.sqrt 2) T : Measure (D T ℝ)) := by
  sorry

/-- The index-two stable law is carried by continuous paths. -/
theorem ae_mem_range_ofContinuous_stableProcessLaw_two {T : ℝ} (hT : 0 < T) :
    ∀ᵐ f ∂(stableProcessLaw 2 T : Measure (D T ℝ)),
      f ∈ Set.range (ofContinuous : C(Set.Icc (0 : ℝ) T, ℝ) → D T ℝ) := by
  sorry

/-- Donsker form: a critical nondegenerate offspring law in the index-2 stable domain with
normalizer `a` has FCLT limit `wienerD (√2) T`. -/
theorem StableDomain.tendsto_stepPathLaw_wienerD {μ : PMF ℕ} {a : ℕ → ℝ}
    (h : StableDomain μ 2 a) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n => stepPathLaw (realOffspringStepLaw μ) T a n) atTop
      (𝓝 (wienerD (NNReal.sqrt 2) T)) := by
  sorry

/-- Donsker's theorem for critical finite-variance offspring laws: with `σ² = E[(ξ - 1)²]`, the
step paths normalized by `σ √n / √2` converge to `wienerD (√2) T`. -/
theorem tendsto_stepPathLaw_wienerD_of_finiteVariance {μ : PMF ℕ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (hfinite : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n => stepPathLaw (realOffspringStepLaw μ) T
        (fun n : ℕ => (Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ) / Real.sqrt 2) *
          Real.sqrt n) n) atTop
      (𝓝 (wienerD (NNReal.sqrt 2) T)) := by
  sorry

end BGW.StableTrees
