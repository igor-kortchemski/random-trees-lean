import BGW.Skorokhod.DLoc
import BGW.Skorokhod.ShiftIncrement
import BGW.StableTrees.StableLocalLaw
import BGW.StableTrees.StableProcessMarkov
import BGW.StableTrees.StableLaw

/-! Contract probe for CT.C6 blueprint Node 4 (simple Markov property at a deterministic time,
relative to the RIGHT-CONTINUOUS past `DLoc.filtration s = F_s^+`).

Sealed inputs reused (nothing is re-declared here): `DLoc.shift` (the centered shift
`u ↦ f (s + u) - f s`, already a `DLoc`), `DLoc.filtration`, `stableLocalLaw`,
`eq_stableLocalLaw_iff`, `map_restrict_stableLocalLaw`, `stableProcessLaw_simpleMarkov`,
`stableProcessLaw_zero`.

Plan (AUDIT item 2): the compact simple Markov property `stableProcessLaw_simpleMarkov` plus
restriction gives independence of the future from the raw past `F_s`; the upgrade to `F_s^+`
uses the deterministic fresh starts at `s + 2^{-n}` and right-continuity of coordinates in
bounded-continuous finite-dimensional tests, then a monotone-class extension. Estimate 300–500
lines.

Conventions.
* The "future increment path after `s`" is `DLoc.shift s`; at `s = 0` it is `f ↦ f - f 0`, which
  equals the identity only almost surely (`ae_eval_zero_stableLocalLaw`). The statements below
  hold for `s = 0` and give the germ zero-one law.
* All local statements carry `1 < θ ∧ θ ≤ 2` (junk branch: `stableLocalLaw θ` is the Dirac mass
  at the zero path, for which every statement is trivially true but is not asserted here).
* Bounded tests: `F` Borel with `∃ C, ∀ x, |F x| ≤ C`.
* Compact horizon: the future after `s` on `[0, U]` is `DLoc.restrict U (DLoc.shift s f)`;
  `U = 0` is allowed (the zero-horizon law is the Dirac mass at the zero path,
  `stableProcessLaw_zero`).
Maintained file: a new `BGW/StableTrees/StableLocalMarkov.lean` (namespace `BGW.StableTrees`). -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal
open BGW.Skorokhod

namespace BGW.Skorokhod.DLoc

/-- The centered shift by a fixed time is measurable (restriction of `measurable_shift`). -/
theorem measurable_shift_fixed (s : ℝ≥0) : Measurable (DLoc.shift s) := sorry

/-- Evaluation of the shift: `eval u (shift s f) = eval (s + u) f - eval s f`. -/
theorem eval_shift (s u : ℝ≥0) (f : DLoc) :
    DLoc.eval u (DLoc.shift s f) = DLoc.eval (s + u) f - DLoc.eval s f := sorry

end BGW.Skorokhod.DLoc

namespace BGW.StableTrees

/-! ### The future increment path and its law -/

/-- **Law of the future.** After any deterministic time `s ≥ 0` the centered path has the
original law (`s = 0` included). -/
theorem map_shift_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (s : ℝ≥0) :
    (stableLocalLaw θ : Measure DLoc).map (DLoc.shift s) = (stableLocalLaw θ : Measure DLoc) :=
  sorry

/-- **Simple Markov property, σ-algebra form.** The future increment path after `s` is
independent of the right-continuous past `F_s^+ = DLoc.filtration s`. -/
theorem indep_filtration_shift_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (s : ℝ≥0) :
    Indep (DLoc.filtration s)
      (MeasurableSpace.comap (DLoc.shift s) (inferInstance : MeasurableSpace DLoc))
      (stableLocalLaw θ : Measure DLoc) := sorry

/-- The same independence from the raw past `F_s = DLoc.rawFiltration s` (the first, easier
step; follows from the compact simple Markov property). -/
theorem indep_rawFiltration_shift_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (s : ℝ≥0) :
    Indep (DLoc.rawFiltration s)
      (MeasurableSpace.comap (DLoc.shift s) (inferInstance : MeasurableSpace DLoc))
      (stableLocalLaw θ : Measure DLoc) := sorry

/-- **Bounded-test corollary (whole future).** For `A ∈ F_s^+` and bounded Borel `F` on `DLoc`,
`∫_A F(shift_s f) dP = P(A) · ∫ F dP`. -/
theorem integral_shift_mul_past {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (s : ℝ≥0) {A : Set DLoc}
    (hA : MeasurableSet[DLoc.filtration s] A) {F : DLoc → ℝ} (hF : Measurable F)
    (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    ∫ f in A, F (DLoc.shift s f) ∂(stableLocalLaw θ : Measure DLoc) =
      (stableLocalLaw θ : Measure DLoc).real A * ∫ f, F f ∂(stableLocalLaw θ : Measure DLoc) :=
  sorry

/-- **Bounded-test corollary (compact future window).** The blueprint form: the future after `s`
centered and cut at horizon `U`, tested by bounded Borel `F` on `D U ℝ`. The right side uses
`stableProcessLaw θ U`. -/
theorem integral_futureSegment_mul_past {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (s U : ℝ≥0) {A : Set DLoc}
    (hA : MeasurableSet[DLoc.filtration s] A) {F : D (U : ℝ) ℝ → ℝ} (hF : Measurable F)
    (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    ∫ f in A, F (DLoc.restrict U (DLoc.shift s f)) ∂(stableLocalLaw θ : Measure DLoc) =
      (stableLocalLaw θ : Measure DLoc).real A *
        ∫ g, F g ∂(stableProcessLaw θ (U : ℝ) : Measure (D (U : ℝ) ℝ)) := sorry

/-- Product form: `E[G · F(shift_s)] = E[G] · E[F]` for `G` bounded `F_s^+`-measurable and `F`
bounded Borel. -/
theorem integral_mul_shift_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (s : ℝ≥0)
    {G : DLoc → ℝ} (hG : Measurable[DLoc.filtration s] G) (hGb : ∃ C : ℝ, ∀ x, |G x| ≤ C)
    {F : DLoc → ℝ} (hF : Measurable F) (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    ∫ f, G f * F (DLoc.shift s f) ∂(stableLocalLaw θ : Measure DLoc) =
      (∫ f, G f ∂(stableLocalLaw θ : Measure DLoc)) *
        ∫ f, F f ∂(stableLocalLaw θ : Measure DLoc) := sorry

/-- **Conditional-expectation form.** Given `F_s^+`, a bounded Borel functional of the future
has the constant conditional expectation `∫ F dP`. -/
theorem condExp_shift_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (s : ℝ≥0)
    {F : DLoc → ℝ} (hF : Measurable F) (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    (stableLocalLaw θ : Measure DLoc)[fun f => F (DLoc.shift s f) | DLoc.filtration s] =ᵐ[
      (stableLocalLaw θ : Measure DLoc)]
      fun _ => ∫ f, F f ∂(stableLocalLaw θ : Measure DLoc) := sorry

/-- **Germ zero-one law** (`s = 0`, feeds N06): every event of `F_0^+` has probability `0` or `1`. -/
theorem measure_zeroOne_filtration_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {A : Set DLoc}
    (hA : MeasurableSet[DLoc.filtration 0] A) :
    (stableLocalLaw θ : Measure DLoc) A = 0 ∨ (stableLocalLaw θ : Measure DLoc) A = 1 := sorry

/-- **Martingale export** (AUDIT item 4, feeds N08): for `u ≥ 0` the exponential process
`exp(-u X_t - t u^θ)` is a martingale for the right-continuous filtration. -/
theorem martingale_exp_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {u : ℝ} (hu : 0 ≤ u) :
    Martingale (fun (t : ℝ≥0) (f : DLoc) => Real.exp (-u * DLoc.eval t f - (t : ℝ) * u ^ θ))
      DLoc.filtration (stableLocalLaw θ : Measure DLoc) := sorry

/-! ### Compact horizon (bounded-test form of `stableProcessLaw_simpleMarkov`) -/

/-- Past/future independence in σ-algebra form on `D T ℝ`: the σ-algebra pulled back by
`restrict hsT` (natural past up to `s`) is independent of the σ-algebra of the future increment
path. -/
theorem indep_comap_restrict_shiftIncrement_stableProcessLaw {θ T s : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) (hs : 0 ≤ s) (hsT : s ≤ T) :
    Indep (MeasurableSpace.comap (restrict (E := ℝ) hsT) (inferInstance : MeasurableSpace (D s ℝ)))
      (MeasurableSpace.comap (shiftIncrement hs hsT)
        (inferInstance : MeasurableSpace (D (T - s) ℝ)))
      (stableProcessLaw θ T : Measure (D T ℝ)) := sorry

/-- **Sol's bounded-test corollary.** For every sub-σ-algebra `m ≤ comap (restrict hsT)` of the
natural past, `A` `m`-measurable and bounded Borel `F` on the future path space,
`∫_A F(future) dP = P(A) · ∫ F d(law of the future)`. The measures `P`, `Q` are bound before `m`
(with equations to the stable laws) so that they carry the Borel σ-algebra, not `m`, which would
otherwise become the local `MeasurableSpace (D T ℝ)` instance. -/
theorem integral_shiftIncrement_mul_past_stableProcessLaw {θ T s : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) (hs : 0 ≤ s) (hsT : s ≤ T)
    (P : Measure (D T ℝ)) (hP : P = (stableProcessLaw θ T : Measure (D T ℝ)))
    (Q : Measure (D (T - s) ℝ)) (hQ : Q = (stableProcessLaw θ (T - s) : Measure (D (T - s) ℝ)))
    {m : MeasurableSpace (D T ℝ)}
    (hm : m ≤ MeasurableSpace.comap (restrict (E := ℝ) hsT) (inferInstance : MeasurableSpace (D s ℝ)))
    {A : Set (D T ℝ)} (hA : MeasurableSet[m] A)
    {F : D (T - s) ℝ → ℝ} (hF : Measurable F) (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    ∫ f in A, F (shiftIncrement hs hsT f) ∂P = P.real A * ∫ g, F g ∂Q := sorry

end BGW.StableTrees
