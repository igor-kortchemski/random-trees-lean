import BGW.Skorokhod.DLoc
import BGW.StableTrees.StableLocalLaw
import Mathlib.Probability.Process.Stopping

/-! Contract probe for CT.C6 blueprint Node 5 (strong Markov property of `stableLocalLaw θ` at
stopping times of the right-continuous filtration `DLoc.filtration`).

Conventions.
* A stopping time is `τ : DLoc → ℝ≥0∞` with Mathlib's `IsStoppingTime DLoc.filtration τ`
  (`ℝ≥0∞ = WithTop ℝ≥0`; `⊤` is allowed, so `τ` need not be finite).
* The post-`τ` centered shift is the total map `DLoc.shiftAt τ f = DLoc.shift (τ f).toNNReal f`.
  On `{τ = ⊤}` it takes the junk value `DLoc.shift 0 f = f - f 0`. All statements restrict to
  `{τ < ⊤}`, where `shiftAt τ f : u ↦ f (τ f + u) - f (τ f)` is the genuine post-`τ` path.
* `τ ≡ 0` recovers the `s = 0` case of N04 (`DLoc.shift 0 f = f - f 0`); constant `τ ≡ s`
  recovers N04 at `s`.
* All statements carry `1 < θ ∧ θ ≤ 2` (junk branch: `stableLocalLaw θ` is the Dirac mass at the
  zero path, where the law statements are not asserted).
* Bounded tests: `F` Borel with `∃ C, ∀ x, |F x| ≤ C`.
* The stopped σ-algebra is `hτ.measurableSpace` (`MeasureTheory.IsStoppingTime.measurableSpace`);
  note it contains `{τ < ⊤}` and `{τ ≤ c}` events (sets `A` there with `A ⊆ {τ < ⊤}` are allowed).
Plan (blueprint): dyadic approximation `2^{-n}⌈2^n τ⌉ ↓ τ` (countably valued stopping times; finitely valued after bounded localization,
stopped σ-algebras decrease to that of `τ` by right-continuity of the filtration), N04 on each
grid atom, right-continuity of coordinates in bounded continuous finite-dimensional tests, then
monotone class; localise by `τ ∧ m`.
Maintained file: a new `BGW/StableTrees/StableStrongMarkov.lean` (namespace `BGW.StableTrees`),
using `DLoc.shiftAt` which lives in `BGW/StableTrees/StableLocalMarkov.lean` or `DLoc.lean`. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.Skorokhod.DLoc

/-- **Post-`τ` centered shift.** `shiftAt τ f = (u ↦ f (τ f + u) - f (τ f))` when `τ f < ⊤`;
junk value `shift 0 f` when `τ f = ⊤`. -/
noncomputable def shiftAt (τ : DLoc → ℝ≥0∞) (f : DLoc) : DLoc :=
  DLoc.shift (τ f).toNNReal f

/-- Evaluation of the post-`τ` shift on `{τ < ⊤}`. -/
theorem eval_shiftAt (τ : DLoc → ℝ≥0∞) (u : ℝ≥0) {f : DLoc} (hf : τ f < ⊤) :
    DLoc.eval u (shiftAt τ f) = DLoc.eval ((τ f).toNNReal + u) f - DLoc.eval (τ f).toNNReal f :=
  sorry

/-- `shiftAt` at a constant time is the deterministic shift. -/
theorem shiftAt_const (s : ℝ≥0) : shiftAt (fun _ => (s : ℝ≥0∞)) = DLoc.shift s := sorry

/-- A stopping time of the right-continuous filtration is Borel measurable, hence so is
`shiftAt τ` on all of `DLoc` (the junk branch on `{τ = ⊤}` is measurable too); in particular its
restriction to `{τ < ⊤}` is measurable. -/
theorem measurable_shiftAt {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ) :
    Measurable (shiftAt τ) := sorry

/-- `{τ < ⊤}` is an event of the stopped σ-algebra. -/
theorem measurableSet_lt_top_stopped {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ) :
    MeasurableSet[hτ.measurableSpace] {f | τ f < ⊤} := sorry

/-- **Stopped coordinate, everywhere form.** Mathlib's `stoppedValue` (junk value on `{τ = ⊤}`)
of the coordinate process is measurable for the stopped σ-algebra. -/
theorem measurable_stoppedValue_eval {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ) :
    Measurable[hτ.measurableSpace] (stoppedValue (fun t (f : DLoc) => DLoc.eval t f) τ) := sorry

/-- **Stopped coordinate**, for `τ < ⊤` everywhere: `f ↦ f (τ f)` is `hτ.measurableSpace`-
measurable. -/
theorem measurable_eval_toNNReal_stopped {τ : DLoc → ℝ≥0∞}
    (hτ : IsStoppingTime DLoc.filtration τ) (hfin : ∀ f, τ f < ⊤) :
    Measurable[hτ.measurableSpace] (fun f : DLoc => DLoc.eval (τ f).toNNReal f) := sorry

end BGW.Skorokhod.DLoc

namespace BGW.StableTrees

/-- **Strong Markov property, integral form.** For `A` in the stopped σ-algebra of `τ` with
`A ⊆ {τ < ⊤}` and bounded Borel `F` on `DLoc`,
`∫_A F(shiftAt τ f) dP = P(A) · ∫ F dP`. (`A = ∅` and `τ ≡ 0` allowed.) -/
theorem integral_shiftAt_mul_past {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ) {A : Set DLoc}
    (hA : MeasurableSet[hτ.measurableSpace] A) (hAτ : A ⊆ {f | τ f < ⊤})
    {F : DLoc → ℝ} (hF : Measurable F) (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    ∫ f in A, F (DLoc.shiftAt τ f) ∂(stableLocalLaw θ : Measure DLoc) =
      (stableLocalLaw θ : Measure DLoc).real A * ∫ f, F f ∂(stableLocalLaw θ : Measure DLoc) :=
  sorry

/-- **Law of the post-`τ` path.** Conditionally on `{τ < ⊤}` (i.e. under the restriction of `P`
to it), `shiftAt τ` has the law `stableLocalLaw θ`, scaled by the mass of `{τ < ⊤}`. -/
theorem map_shiftAt_restrict_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ) :
    ((stableLocalLaw θ : Measure DLoc).restrict {f | τ f < ⊤}).map (DLoc.shiftAt τ) =
      (stableLocalLaw θ : Measure DLoc) {f | τ f < ⊤} • (stableLocalLaw θ : Measure DLoc) :=
  sorry

/-- **Independence form.** Under the conditional probability given `{τ < ⊤}` (when that event has
positive probability), the stopped σ-algebra restricted to the event is independent of the
post-`τ` path. Stated with the restricted (non-normalised) measure, so that the null case is
vacuous-true and no division is needed: for stopped events `A ⊆ {τ < ⊤}` and Borel `B`,
`P(A ∩ shiftAt τ ⁻¹ B) = P(A) · P(B)`. -/
theorem measure_inter_preimage_shiftAt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ) {A : Set DLoc}
    (hA : MeasurableSet[hτ.measurableSpace] A) (hAτ : A ⊆ {f | τ f < ⊤})
    {B : Set DLoc} (hB : MeasurableSet B) :
    (stableLocalLaw θ : Measure DLoc) (A ∩ DLoc.shiftAt τ ⁻¹' B) =
      (stableLocalLaw θ : Measure DLoc) A * (stableLocalLaw θ : Measure DLoc) B := sorry

/-- **Compact-window form** (blueprint shape): the post-`τ` path cut at horizon `U`. -/
theorem integral_futureSegmentAt_mul_past {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ) (U : ℝ≥0) {A : Set DLoc}
    (hA : MeasurableSet[hτ.measurableSpace] A) (hAτ : A ⊆ {f | τ f < ⊤})
    {F : D (U : ℝ) ℝ → ℝ} (hF : Measurable F) (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    ∫ f in A, F (DLoc.restrict U (DLoc.shiftAt τ f)) ∂(stableLocalLaw θ : Measure DLoc) =
      (stableLocalLaw θ : Measure DLoc).real A *
        ∫ g, F g ∂(stableProcessLaw θ (U : ℝ) : Measure (D (U : ℝ) ℝ)) := sorry

/-- **Almost surely finite stopping time**: when `τ < ⊤` a.s., the post-`τ` path has law
`stableLocalLaw θ` and is independent of the whole stopped σ-algebra. -/
theorem integral_shiftAt_mul_past_of_ae_lt_top {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ)
    (hfin : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), τ f < ⊤) {A : Set DLoc}
    (hA : MeasurableSet[hτ.measurableSpace] A)
    {F : DLoc → ℝ} (hF : Measurable F) (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    ∫ f in A, F (DLoc.shiftAt τ f) ∂(stableLocalLaw θ : Measure DLoc) =
      (stableLocalLaw θ : Measure DLoc).real A * ∫ f, F f ∂(stableLocalLaw θ : Measure DLoc) :=
  sorry

/-- **Strong Markov, conditional-expectation form** (bounded test, on `{τ < ⊤}`): relative to the
stopped σ-algebra, `E[1_{τ<⊤} F(shiftAt τ) | F_τ] = 1_{τ<⊤} E[F]` a.s. -/
theorem condExp_indicator_shiftAt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ)
    {F : DLoc → ℝ} (hF : Measurable F) (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    (stableLocalLaw θ : Measure DLoc)[
        {f | τ f < ⊤}.indicator (fun f => F (DLoc.shiftAt τ f)) | hτ.measurableSpace]
      =ᵐ[(stableLocalLaw θ : Measure DLoc)]
      {f | τ f < ⊤}.indicator (fun _ => ∫ g, F g ∂(stableLocalLaw θ : Measure DLoc)) := sorry

/-- Version without indicators when `τ < ⊤` a.s. -/
theorem condExp_shiftAt_of_ae_lt_top {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ)
    (hfin : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), τ f < ⊤)
    {F : DLoc → ℝ} (hF : Measurable F) (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    (stableLocalLaw θ : Measure DLoc)[(fun f => F (DLoc.shiftAt τ f)) | hτ.measurableSpace]
      =ᵐ[(stableLocalLaw θ : Measure DLoc)]
      fun _ => ∫ g, F g ∂(stableLocalLaw θ : Measure DLoc) := sorry

end BGW.StableTrees
