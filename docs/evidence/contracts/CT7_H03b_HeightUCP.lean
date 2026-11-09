import BGW.StableTrees.HeightContinuity

/-! Contract probe for CT7 node H03b (opened 8 Nov 2026 after the H04 route research,
`.orchestration/sol-route-h04/ROUTE.md`, step 2): uniform convergence in probability on compacts
of the occupation approximations `heightApprox ε f t` to the continuous height `heightLoc θ f t`,
along the full cutoff filter `ε ↓ 0`, under the stable law.

WHY.  H04 needs the excursion heights at rational ages to extend continuously `N`-a.e.  With
the exact finite-cutoff cancellation `heightApprox ε host (g + q) - heightApprox ε host g =
heightApprox ε e.path q` at an excursion start `g` (ROUTE step 1), uniform convergence of the HOST
approximations to the continuous `heightLoc` controls all random times `g + q` at once and gives
continuity, endpoint zeros and locality without circularity.  Nothing sealed implies it: H03's
moment bound concerns the limit `height`, not the approximations, and H01's uniform statement
concerns one forward supremum occupation, not the uncountable family of reversals.

STATEMENTS.  `heightApprox_modulus`: an `ε`-uniform modulus in probability of `t ↦ heightApprox ε f
t`
on `[0,T]` (outer measure: no measurability of the uncountable supremum is assumed).
`heightApprox_ucp`: the uniform convergence in probability.  The modulus implies UCP with a finite
time grid, H02 `heightApprox_tendstoInMeasure`, H03 `ae_heightLoc_eq_height` and
`continuous_heightLoc` (allocate the error between the two moduli and the grid errors).

TRUTH AND RISK.  Expected true (finite-cutoff analogue of the height regularity), but NOT verified:
neither a proof nor a counterexample is known.  Suggested route for the modulus: a FINITE-CUTOFF
erasure decomposition at fixed times (`heightApprox ε f (t + s)` is the fresh occupation of the
shifted path plus the surviving part of the cutoff occupation measure at `t`, whose erased part is
the cutoff supremum occupation of the reversed path stopped at its passage above the fresh depth),
with tails `≤ C exp(-v s^(-β))` uniform in `ε ≤ ε₀` from H01's finite-cutoff occupation and
correction estimates (stopped energy and maximal bounds) and the H02b continuation-free comparison;
then an `ε`-uniform increment moment bound with exponent `> 1` and a chaining/Kolmogorov argument
over dyadic times for the cadlag-in-time approximations (separability: right-continuity or a
countable-time reduction).  STOP CONDITION: if the uniform finite-cutoff tail fails, report the
exact obstruction; do not weaken the statements.  No use of H04, excursion continuity or locality.

ACYCLICITY.  Suppliers: H01, H02, H02b, H03.  Consumer: H04.

BINDER SCOPE (AUDITOR_RULES): the set-builder bodies contain the whole conjunctions; no big
operator is followed by `+`/`-`. -/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees

/-- **`ε`-uniform modulus in probability** of the occupation approximations on `[0,T]`. -/
theorem heightApprox_modulus {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0)
    (η κ : ℝ) (hη : 0 < η) (hκ : 0 < κ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        (stableLocalLaw θ : Measure DLoc)
          {f | ∃ s t : ℝ≥0, s ≤ T ∧ t ≤ T ∧ |(s : ℝ) - t| < δ ∧
            η ≤ |heightApprox ε f s - heightApprox ε f t|} < ENNReal.ofReal κ := sorry

/-- **Uniform convergence in probability on compacts** of the approximations to the continuous
height, along the full cutoff filter. -/
theorem heightApprox_ucp {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) (η : ℝ) (hη : 0 < η) :
    Tendsto
      (fun ε : ℝ => (stableLocalLaw θ : Measure DLoc)
        {f | ∃ t : ℝ≥0, t ≤ T ∧ η ≤ |heightApprox ε f t - heightLoc θ f t|})
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := sorry

end BGW.StableTrees
