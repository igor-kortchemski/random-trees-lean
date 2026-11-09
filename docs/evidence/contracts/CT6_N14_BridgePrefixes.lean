import BGW.Skorokhod.Restrict
import BGW.Skorokhod.MeasurableMaps
import BGW.Skorokhod.Measurable
import BGW.StableTrees.StableLaw
import BGW.StableTrees.Scalar.Density
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Contract probe for CT.C6 blueprint Node 14 (audit correction 6 and wave A) together with the
public density adapters of Node 1 (audit correction 9: they live in N14's module, never in the
sealed `StableLaw.lean`, whose `stableDensityAt_{nonneg,continuous,integrable,integral}` are
private).

Abstract tilted prefixes of the stable bridge. For `0 < a < 1` and ANY probability law `P` on
`D([0,a], ℝ)` with `IsStableLevyLaw θ a P` (copied below from contract CT5_Characterization: `BGW/StableTrees/StableLevyLaw.lean` is not yet
importable), the
prefix law is `Q_a = w_a · P` with `w_a(f) = p_{1-a}(-f(a)) / p_1(0)`. Needs neither strong Markov
nor P5: mass one and consistency use `IsStableLevyLaw.increments` at the times `{0, a, b}`
(or `IsStableLevyLaw.map_increments`), the semigroup identity `integral_stableDensityAt_mul`,
and `IsStableLevyLaw.map_restrict`/`.unique`. Consistency is asserted at the level of measures on
`D a ℝ`, not of scalar marginals. Maintained file: `BGW/StableTrees/BridgePrefixes.lean`
(namespace `BGW.StableTrees`). -/

open MeasureTheory Set
open scoped ENNReal

namespace BGW.StableTrees

open BGW.Skorokhod

/-! ## Copied declarations (not part of this contract) -/

-- copied from contract CT5_Characterization (not part of this contract)
structure IsStableLevyLaw (θ T : ℝ) (P : ProbabilityMeasure (D T ℝ)) : Prop where
  start : ∀ h : 0 ≤ T, ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)), f ⟨0, le_rfl, h⟩ = 0
  increments : ∀ (k : ℕ) (t : Fin (k + 1) → Set.Icc (0 : ℝ) T),
    StrictMono t → (t 0 : ℝ) = 0 →
    Measure.map (fun f : D T ℝ => fun i : Fin k => f (t i.succ) - f (t i.castSucc))
      (P : Measure (D T ℝ)) =
      Measure.pi (fun i : Fin k =>
        (stableLawAt θ ((t i.succ : ℝ) - t i.castSucc) : Measure ℝ))

-- copied from contract CT5_Characterization (not part of this contract)
theorem IsStableLevyLaw.map_increments {θ T : ℝ} {P : ProbabilityMeasure (D T ℝ)}
    (hP : IsStableLevyLaw θ T P) (k : ℕ) (t : Fin (k + 1) → Set.Icc (0 : ℝ) T)
    (ht : StrictMono t) :
    Measure.map (fun f : D T ℝ => fun i : Fin k => f (t i.succ) - f (t i.castSucc))
      (P : Measure (D T ℝ)) =
      Measure.pi (fun i : Fin k =>
        (stableLawAt θ ((t i.succ : ℝ) - t i.castSucc) : Measure ℝ)) := sorry

-- copied from contract CT5_Characterization (not part of this contract)
theorem IsStableLevyLaw.unique {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    {P Q : ProbabilityMeasure (D T ℝ)} (hP : IsStableLevyLaw θ T P)
    (hQ : IsStableLevyLaw θ T Q) : P = Q := sorry

-- copied from contract CT5_Characterization (not part of this contract)
theorem IsStableLevyLaw.map_restrict {θ T a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 < a)
    (haT : a ≤ T) {P : ProbabilityMeasure (D T ℝ)} (hP : IsStableLevyLaw θ T P) :
    IsStableLevyLaw θ a (P.map (restrict haT)) := sorry

/-! ## Public density adapters (N01, density part) -/

/-- `p_t ≥ 0` for `t > 0`. Public version of the private sealed lemma (same name is deliberate:
private declarations of another module do not clash). -/
theorem stableDensityAt_nonneg {θ t : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ht : 0 < t) (x : ℝ) :
    0 ≤ stableDensityAt θ t x := sorry

/-- `x ↦ p_t(x)` is continuous (for every `t`). -/
theorem stableDensityAt_continuous {θ t : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    Continuous (stableDensityAt θ t) := sorry

/-- `p_t` integrates to `1` for `t > 0`. -/
theorem integral_stableDensityAt {θ t : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ht : 0 < t) :
    ∫ x, stableDensityAt θ t x = 1 := sorry

/-- `p_t` is integrable for `t > 0`. -/
theorem integrable_stableDensityAt {θ t : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ht : 0 < t) :
    Integrable (stableDensityAt θ t) := sorry

/-- Uniform bound `p_t ≤ C` for `t ≥ t₀ > 0` (`C = t₀^{-1/θ} sup p_1`). Not claimed as `t → 0`. -/
theorem stableDensityAt_le_of_ge {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∃ C : ℝ, ∀ t, t₀ ≤ t → ∀ x, stableDensityAt θ t x ≤ C := sorry

/-- No atoms: for `t > 0` the law `stableLawAt θ t` has no point masses. -/
theorem stableLawAt_singleton {θ t : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ht : 0 < t) (x : ℝ) :
    (stableLawAt θ t : Measure ℝ) {x} = 0 := sorry

/-- `p_1 = stableDensity` (so `p_1(0)` is `Scalar.stableDensity θ 0 > 0`). -/
theorem stableDensityAt_one (θ x : ℝ) : stableDensityAt θ 1 x = Scalar.stableDensity θ x := sorry

/-- Joint continuity of `(t, x) ↦ p_t(x)` on `t > 0`. -/
theorem stableDensityAt_jointContinuous {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ContinuousOn (fun z : ℝ × ℝ => stableDensityAt θ z.1 z.2) {z | 0 < z.1} := sorry

/-! ## Tilted prefixes -/

/-- The prefix weight `w_a(f) = p_{1-a}(-f(a)) / p_1(0)`, for `0 ≤ a` (horizon `a`). -/
noncomputable def bridgePrefixWeight (θ a : ℝ) (ha : 0 ≤ a) (f : D a ℝ) : ℝ :=
  stableDensityAt θ (1 - a) (-f ⟨a, ha, le_rfl⟩) / Scalar.stableDensity θ 0

/-- The tilted prefix measure `w_a · P` on `D a ℝ` (for a given law `P` on `D a ℝ`). -/
noncomputable def bridgePrefixLaw (θ a : ℝ) (ha : 0 ≤ a) (P : Measure (D a ℝ)) :
    Measure (D a ℝ) :=
  P.withDensity fun f => ENNReal.ofReal (bridgePrefixWeight θ a ha f)

/-- The weight is nonnegative for `a < 1`. -/
theorem bridgePrefixWeight_nonneg {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 ≤ a) (ha1 : a < 1)
    (f : D a ℝ) : 0 ≤ bridgePrefixWeight θ a ha f := sorry

/-- The weight is measurable (`D a ℝ` carries the Borel σ-algebra of J1). -/
theorem measurable_bridgePrefixWeight {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 ≤ a) :
    Measurable (bridgePrefixWeight θ a ha) := sorry

/-- For each fixed `a < 1` the weight is bounded (the bound degenerates as `a → 1`; no uniform
bound is claimed). -/
theorem bridgePrefixWeight_le {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 ≤ a) (ha1 : a < 1) :
    ∃ C : ℝ, ∀ f : D a ℝ, bridgePrefixWeight θ a ha f ≤ C := sorry

/-- **Mass one.** For every stable Lévy law `P` on `[0,a]`, `∫ w_a dP = 1`. -/
theorem bridgePrefix_mass_one {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 < a) (ha1 : a < 1)
    {P : ProbabilityMeasure (D a ℝ)} (hP : IsStableLevyLaw θ a P) :
    ∫⁻ f, ENNReal.ofReal (bridgePrefixWeight θ a ha.le f) ∂(P : Measure (D a ℝ)) = 1 := sorry

/-- Equivalent form: the tilted prefix law is a probability measure. -/
theorem isProbabilityMeasure_bridgePrefixLaw {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 < a)
    (ha1 : a < 1) {P : ProbabilityMeasure (D a ℝ)} (hP : IsStableLevyLaw θ a P) :
    IsProbabilityMeasure (bridgePrefixLaw θ a ha.le (P : Measure (D a ℝ))) := sorry

/-- **Consistency at the level of measures on `D a ℝ`.** For `0 < a ≤ b < 1` and stable Lévy
laws `P_a`, `P_b` on `[0,a]`, `[0,b]`, restricting `w_b · P_b` to `[0,a]` gives `w_a · P_a`. -/
theorem bridgePrefix_consistent {θ a b : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 < a) (hab : a ≤ b)
    (hb : b < 1) {Pa : ProbabilityMeasure (D a ℝ)} {Pb : ProbabilityMeasure (D b ℝ)}
    (hPa : IsStableLevyLaw θ a Pa) (hPb : IsStableLevyLaw θ b Pb) :
    (bridgePrefixLaw θ b (ha.le.trans hab) (Pb : Measure (D b ℝ))).map (restrict hab) =
      bridgePrefixLaw θ a ha.le (Pa : Measure (D a ℝ)) := sorry

/-- The prefix law does not depend on the choice of the stable law `P` (uniqueness). -/
theorem bridgePrefixLaw_unique {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 < a)
    {P Q : ProbabilityMeasure (D a ℝ)} (hP : IsStableLevyLaw θ a P) (hQ : IsStableLevyLaw θ a Q) :
    bridgePrefixLaw θ a ha.le (P : Measure (D a ℝ)) =
      bridgePrefixLaw θ a ha.le (Q : Measure (D a ℝ)) := sorry

/-- Abstract-family form (client form for N15): if `P a` is a stable Lévy law on `[0,a]` for every
`a ∈ (0,1)` then the prefix laws are probability measures that are consistent in `a`. -/
theorem bridgePrefix_family {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (P : ∀ a : ℝ, ProbabilityMeasure (D a ℝ)) (hP : ∀ a, 0 < a → IsStableLevyLaw θ a (P a)) :
    ∀ a b (ha : 0 < a) (hab : a ≤ b) (hb : b < 1),
      IsProbabilityMeasure (bridgePrefixLaw θ a ha.le (P a : Measure (D a ℝ))) ∧
      (bridgePrefixLaw θ b (ha.le.trans hab) (P b : Measure (D b ℝ))).map (restrict hab) =
        bridgePrefixLaw θ a ha.le (P a : Measure (D a ℝ)) := sorry

end BGW.StableTrees
