import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Contract probe for H01 node R05a (AUDIT "Recommended first nodes" 3): the reusable
finite-grid `L²` maximal lemma (Doob) and the signed resolvent moment lemma, isolated from the
stable process and from R01.  Pure Mathlib imports; no BGW definitions.

PART A (Doob `L²`).  Mathlib has only the tail inequality `MeasureTheory.maximal_ineq`; the `L²`
corollary `E max_k Y_k² ≤ 4 E Y_n²` for a nonnegative submartingale is new work.  We state it in
`ℝ≥0∞` (`lintegral`) form so that NO integrability hypothesis is needed: if the right side is
infinite the claim is trivial, otherwise the martingale/submartingale property forces
square-integrability of every `Y_k`.  Three versions: (1) ℕ-indexed nonnegative submartingale,
(2) ℕ-indexed real martingale (via `|M|`), (3) `ℝ≥0`-indexed martingale with right-continuous
paths, supremum over the compact `[0,T]` (reduction to rational grids; the audit's "extend
through rational grids").  FLAG: orthogonal increments alone do NOT give the constant 4 (that
needs the martingale property); for independent centred increments apply (2) to partial sums.

PART B (signed resolvent moments).  For a process `Z` (jointly measurable, with `k∘Z` and `V∘Z` strongly progressive (adaptedness alone would not make
`∫_0^t e^{-s}k(Z_s)ds` `F_t`-measurable)),
a bounded Borel signed function `k`, and a bounded function `V` satisfying the RESOLVENT MARKOV
HYPOTHESIS `E[∫_s^∞ e^{-t} k(Z_t) dt | F_s] = e^{-s} V(Z_s)` (`V = U₁ k`, the `q = 1` resolvent),
with `B = ∫_0^∞ e^{-t} k(Z_t) dt`:
 * `J_t = ∫_0^t e^{-s}k(Z_s)ds + e^{-t}V(Z_t)` is a martingale (`J_t = E[B | F_t]`);
 * `E B² = 2 E ∫_0^∞ e^{-2t} k(Z_t) V(Z_t) dt`  (the blueprint's `E_x(B_ε-B_η)²` identity with
   `k = g_ε - g_η`, `V = u¹_ε - u¹_η`; signed, so Tonelli is NOT used: boundedness gives Fubini);
 * the cheap bound `E B² ≤ 2 D E ∫ e^{-2t}|k(Z_t)| dt` when `|V| ≤ D`.
Time integrals are over `ℝ` with `toNNReal`, matching `supOccupation`.  The Markov hypothesis is
discharged for the reflected process only in the later R05 (it needs R01); not here.
Estimate 250-450 lines. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace BGW.StableTrees

section DoobL2

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]

/-- **Doob `L²` maximal inequality, nonnegative submartingale, finite grid.** -/
theorem lintegral_sq_sup_le_four_mul_of_submartingale {ℱ : Filtration ℕ m} {Y : ℕ → Ω → ℝ}
    (hY : Submartingale Y ℱ μ) (hnn : ∀ k ω, 0 ≤ Y k ω) (n : ℕ) :
    ∫⁻ ω, ((Finset.range (n + 1)).sup fun k => ENNReal.ofReal (Y k ω)) ^ 2 ∂μ ≤
      4 * ∫⁻ ω, ENNReal.ofReal (Y n ω) ^ 2 ∂μ := sorry

/-- **Doob `L²` maximal inequality for a real martingale, finite grid.** -/
theorem lintegral_sq_sup_enorm_le_four_mul_of_martingale {ℱ : Filtration ℕ m} {M : ℕ → Ω → ℝ}
    (hM : Martingale M ℱ μ) (n : ℕ) :
    ∫⁻ ω, ((Finset.range (n + 1)).sup fun k => ‖M k ω‖ₑ) ^ 2 ∂μ ≤
      4 * ∫⁻ ω, ‖M n ω‖ₑ ^ 2 ∂μ := sorry

/-- Real-valued form when `M n ∈ L²`: `E max_{k ≤ n} M_k² ≤ 4 E M_n²`. -/
theorem integral_sq_sup_le_four_mul_of_martingale {ℱ : Filtration ℕ m} {M : ℕ → Ω → ℝ}
    (hM : Martingale M ℱ μ) (n : ℕ) (h2 : MemLp (M n) 2 μ) :
    Integrable (fun ω => ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        fun k => |M k ω|) ^ 2) μ ∧
      ∫ ω, ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => |M k ω|) ^ 2 ∂μ ≤
        4 * ∫ ω, (M n ω) ^ 2 ∂μ := sorry

/-- **Compact-time Doob `L²`, right-continuous martingale.** For an `ℝ≥0`-indexed martingale whose
paths are right-continuous (every `ω`), `E sup_{t ≤ T} |M_t|² ≤ 4 E |M_T|²`; the supremum is a
countable one (rationals and `T`), hence measurable. -/
theorem lintegral_sq_sup_Icc_le_four_mul_of_martingale {ℱ : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ μ) (hrc : ∀ ω t, ContinuousWithinAt (fun s => M s ω) (Ici t) t)
    (T : ℝ≥0) :
    ∫⁻ ω, (⨆ t ∈ Icc (0 : ℝ≥0) T, ‖M t ω‖ₑ) ^ 2 ∂μ ≤ 4 * ∫⁻ ω, ‖M T ω‖ₑ ^ 2 ∂μ := sorry

end DoobL2

section ResolventMoments

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {E : Type*} [MeasurableSpace E]

/-- The discounted occupation `B = ∫_0^∞ e^{-t} k(Z_t) dt`. -/
noncomputable def discountedOccupation (Z : ℝ≥0 → Ω → E) (k : E → ℝ) (ω : Ω) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-t) * k (Z t.toNNReal ω)

/-- **Resolvent Markov hypothesis**: given `F_s`, the discounted future of `k(Z)` after `s` is
`e^{-s} V(Z_s)`. -/
def ResolventMarkov (ℱ : Filtration ℝ≥0 m) (μ : Measure Ω) (Z : ℝ≥0 → Ω → E) (k V : E → ℝ) :
    Prop :=
  ∀ s : ℝ≥0, μ[fun ω => ∫ t in Ioi (s : ℝ), Real.exp (-t) * k (Z t.toNNReal ω) | ℱ s] =ᵐ[μ]
    fun ω => Real.exp (-(s : ℝ)) * V (Z s ω)

/-- **Explicit martingale.** Under the resolvent Markov hypothesis,
`J_t = ∫_0^t e^{-s}k(Z_s)ds + e^{-t}V(Z_t)` is a martingale. -/
theorem martingale_discounted_resolvent {ℱ : Filtration ℝ≥0 m} {Z : ℝ≥0 → Ω → E} {k V : E → ℝ}
    (hZ : Measurable fun p : ℝ≥0 × Ω => Z p.1 p.2) (hk : Measurable k) (hV : Measurable V)
    (hkb : ∃ C, ∀ e, |k e| ≤ C) (hVb : ∃ C, ∀ e, |V e| ≤ C)
    (hprogk : IsStronglyProgressive ℱ fun t ω => k (Z t ω))
    (hprogV : IsStronglyProgressive ℱ fun t ω => V (Z t ω)) (hM : ResolventMarkov ℱ μ Z k V) :
    Martingale (fun (t : ℝ≥0) ω =>
      (∫ s in Ioc (0 : ℝ) t, Real.exp (-s) * k (Z s.toNNReal ω)) +
        Real.exp (-(t : ℝ)) * V (Z t ω)) ℱ μ := sorry

/-- **Signed second-moment identity**: `E B² = 2 E ∫_0^∞ e^{-2t} k(Z_t) V(Z_t) dt`, with
`B = discountedOccupation Z k`; both sides finite. -/
theorem integral_sq_discountedOccupation {ℱ : Filtration ℝ≥0 m} {Z : ℝ≥0 → Ω → E} {k V : E → ℝ}
    (hZ : Measurable fun p : ℝ≥0 × Ω => Z p.1 p.2) (hk : Measurable k) (hV : Measurable V)
    (hkb : ∃ C, ∀ e, |k e| ≤ C) (hVb : ∃ C, ∀ e, |V e| ≤ C)
    (hprogk : IsStronglyProgressive ℱ fun t ω => k (Z t ω))
    (hprogV : IsStronglyProgressive ℱ fun t ω => V (Z t ω)) (hM : ResolventMarkov ℱ μ Z k V) :
    ∫ ω, (discountedOccupation Z k ω) ^ 2 ∂μ =
      2 * ∫ ω, (∫ t in Ioi (0 : ℝ),
        Real.exp (-2 * t) * (k (Z t.toNNReal ω) * V (Z t.toNNReal ω))) ∂μ := sorry

/-- **Cheap bound**: if `|V| ≤ D` then `E B² ≤ 2 D E ∫_0^∞ e^{-2t}|k(Z_t)| dt`. -/
theorem integral_sq_discountedOccupation_le {ℱ : Filtration ℝ≥0 m} {Z : ℝ≥0 → Ω → E}
    {k V : E → ℝ} (hZ : Measurable fun p : ℝ≥0 × Ω => Z p.1 p.2) (hk : Measurable k)
    (hV : Measurable V) (hkb : ∃ C, ∀ e, |k e| ≤ C) {D : ℝ} (hD : ∀ e, |V e| ≤ D)
    (hprogk : IsStronglyProgressive ℱ fun t ω => k (Z t ω))
    (hprogV : IsStronglyProgressive ℱ fun t ω => V (Z t ω)) (hM : ResolventMarkov ℱ μ Z k V) :
    ∫ ω, (discountedOccupation Z k ω) ^ 2 ∂μ ≤
      2 * D * ∫ ω, (∫ t in Ioi (0 : ℝ), Real.exp (-2 * t) * |k (Z t.toNNReal ω)|) ∂μ := sorry

end ResolventMoments

end BGW.StableTrees
