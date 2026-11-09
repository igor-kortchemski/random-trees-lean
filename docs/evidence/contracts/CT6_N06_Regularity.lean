import BGW.Skorokhod.DLoc
import BGW.StableTrees.StableLocalLaw
import Mathlib.Probability.Process.Stopping

/-! Contract probe for CT.C6 blueprint Node 6 (F2): two-sided regularity of `0` for the local
stable law.

AUDIT item 2: the germ zero-one law is N04 at `s = 0` (`measure_zeroOne_filtration_zero`, in
`CT6_N04_LocalMarkov`), so it is NOT restated here. New content: (i) the germ event
"the path takes negative / positive values at times arbitrarily close to `0`" is `F_0^+`-
measurable (a measurable set of paths, in fact a germ event); (ii) it has probability `1`
for `θ ∈ (1, 2]`, via scaling (probability `≥ c > 0` of a negative/positive value at `ε/2`,
independent of `ε`), decreasing events and N04's zero-one law; (iii) the corollary at stopping
times that N11 (continuity of the minimizer) consumes, from N05 + (ii); (iv) the first-passage
consequence `T_0 = 0` that N08 consumes.

Junk branch: for `θ ∉ (1, 2]` the law is the Dirac mass at the zero path, where regularity is
false, so every probability statement carries `1 < θ ∧ θ ≤ 2`.
Maintained file: a new `BGW/StableTrees/StableRegularity.lean` (namespace `BGW.StableTrees`). -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.Skorokhod.DLoc

-- copied from contract CT6_N05_StrongMarkov (not part of this contract)
noncomputable def shiftAt (τ : DLoc → ℝ≥0∞) (f : DLoc) : DLoc :=
  DLoc.shift (τ f).toNNReal f

/-- `0` is regular for `(-∞, 0)`: the path takes negative values at times in `(0, ε)` for every
`ε > 0`. -/
def RegularBelowAtZero (f : DLoc) : Prop :=
  ∀ ε : ℝ≥0, 0 < ε → ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧ DLoc.eval t f < 0

/-- `0` is regular for `(0, ∞)`. -/
def RegularAboveAtZero (f : DLoc) : Prop :=
  ∀ ε : ℝ≥0, 0 < ε → ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧ 0 < DLoc.eval t f

/-- The two regularity sets are measurable (they depend only on evaluations at positive
(rational) times, not on `f 0`). Needed by N08, N11 to use a.e. statements on
events. -/
theorem measurableSet_regularBelowAtZero : MeasurableSet {f : DLoc | RegularBelowAtZero f} := sorry

/-- The above-zero analogue; likewise only evaluations at positive (rational) times matter, not
`f 0`. -/
theorem measurableSet_regularAboveAtZero : MeasurableSet {f : DLoc | RegularAboveAtZero f} := sorry

/-- Germ-measurability: rational evaluations at times in `(0, 1/n)` for every `n` lie in
`rawFiltration (1/n)`, hence the set is in the right-continuous `filtration 0`. -/
theorem measurableSet_filtration_zero_regularBelowAtZero :
    MeasurableSet[DLoc.filtration 0] {f : DLoc | RegularBelowAtZero f} := sorry

theorem measurableSet_filtration_zero_regularAboveAtZero :
    MeasurableSet[DLoc.filtration 0] {f : DLoc | RegularAboveAtZero f} := sorry

end BGW.Skorokhod.DLoc

namespace BGW.StableTrees

/-- **F2: regularity of `0` for both half-lines.** Almost surely, for every `ε > 0` the path takes
a negative value and a positive value at times in `(0, ε)`. (The path starts at `0` a.s.; this
is the blueprint's `ae_regular_both`.) -/
theorem ae_regular_both_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      DLoc.RegularBelowAtZero f ∧ DLoc.RegularAboveAtZero f := sorry

/-- Separate halves (for consumers that need one side only). -/
theorem ae_regularBelowAtZero_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), DLoc.RegularBelowAtZero f := sorry

theorem ae_regularAboveAtZero_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), DLoc.RegularAboveAtZero f := sorry

/-- **Regularity after a stopping time** (N05 + F2; consumed by N11 at the countably many jump
times of N10, by N09 at fixed levels). Almost surely on `{τ < ⊤}`, immediately after `τ` the path
takes values both strictly below and strictly above its value at `τ`: for every `ε > 0` there are
`t ∈ (0, ε)` with `f (τ + t) < f τ` and `t' ∈ (0, ε)` with `f τ < f (τ + t')`. Here
`DLoc.eval t (shiftAt τ f)` is the genuine increment, and the statement is made through the
regularity predicates of the shifted path. -/
theorem ae_regular_both_shiftAt_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {τ : DLoc → ℝ≥0∞} (hτ : MeasureTheory.IsStoppingTime DLoc.filtration τ) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), τ f < ⊤ →
      DLoc.RegularBelowAtZero (DLoc.shiftAt τ f) ∧ DLoc.RegularAboveAtZero (DLoc.shiftAt τ f) :=
  sorry

/-- **First-passage consequence for N08** (`T_0 = 0`): almost surely the strict passage times
above and below the level `0` both equal `0`. -/
theorem ae_strictPassage_zero_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      DLoc.strictPassageAbove 0 f = 0 ∧ DLoc.strictPassageBelow 0 f = 0 := sorry

end BGW.StableTrees
