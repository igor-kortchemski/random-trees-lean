import BGW.StableTrees.StableStrongMarkov
import BGW.StableTrees.ReflectedRestart
import BGW.StableTrees.UnitExcursionLawMixture
import BGW.StableTrees.StraddlingHeight

/-! Contract probe for CT10 node G1: the soft gaps left by C20.1, C22's Itô description and
C25 in `CLASSICAL_THEORY_INPUTS.md`.  Suggested maintained module:
`BGW/StableTrees/ExcursionGaps.lean`, namespace `BGW.StableTrees`.  All imports above are sealed.

SOURCE (C20(a), first claim).  "`X − I` is a strong Markov process for `(F_t)` (the canonical
filtration of X, augmented)".  The packaged form below says that on `{τ < ∞}`, conditionally on
the stopped σ-algebra, the post-τ reflected path is reflection of an independent copy of the
centered stable future, started at the reflected value at τ.  Bounded Borel test functions on
`DLoc` express equality of conditional laws.

SOURCE (C22(a), Itô description).  "There is a unique family `(N_(a))_{a>0}` of probability
measures on ℰ such that `N_(a)(ζ = a) = 1`, `S^(λ)_* N_(a) = N_(λa)`, and
`N = ∫_0^∞ N_(a) p₁(0) a^(−1−1/θ) da`."  Here `S^(λ)(ω)_s = λ^(1/θ) ω(s/λ)`.
The library's `excursionAt θ a` is `(excursionScale θ a)_* unitExcursionLaw θ`; the density
`lifetimeDensity θ` is `p₁(0) a^(−1−1/θ)` by `stableDensity_zero_eq_inv_theta_gamma`.

SOURCE (C25(a), endpoint definitions).  "Let `g₁ := sup{s ≤ 1 : X_s = I_s}` and
`d₁ := inf{s > 1 : X_s = I_s}`."  The statements below use every fixed `t > 0`, as in O01 and the
sealed C25 height theorem.  `runningInfLoc f t` is `I_t`; no reflection shorthand replaces the
source equality `X_s = I_s` in the sets whose supremum and infimum are taken.

DEFINITIONS.  `reflectedStateAt τ f` is the `ℝ≥0`-valued reflected state at `(τ f).toNNReal`.
`reflectedFutureAt τ f` restarts `reflectedFrom 0 f` from that state on `DLoc.shiftAt τ f`.  On
`{τ < ∞}`, `reflectedFrom_restart_shiftAt` identifies it pointwise with
`u ↦ (reflectedFrom 0 f).1 ((τ f).toNNReal + u)`.  At `τ = ∞` both use the ordinary `toNNReal`
junk branch; the strong-Markov theorem assumes finiteness a.s. and makes no claim there.
The C25 sets are subsets of `ℝ≥0`, so their `sSup`/`sInf` have the usual conditionally complete
order junk values on exceptional paths.  Almost surely, the greatest/least characterizations
below make those conventions irrelevant.

TRUTH CHECK.
(1) C20 needs `τ < ∞` a.s.; without it, a post-τ path and its value at τ are not defined on the
    infinite-time event.  The zero initial state is not an extra premise: `stableLocalLaw θ` starts
    at zero and `reflectedFrom 0 f = X − I` by `reflectedFrom_zero_apply`.  Restarting from the
    actual nonnegative reflected value, rather than subtracting it and restarting at zero, is
    essential.  The stopped state must be proved `F_τ`-measurable; it is not silently assumed in
    the law statement.
(2) C22 has EVERY positive lifetime and scale, not only lifetime one.  `excursionAt` is a genuine
    probability measure by `isProbabilityMeasure_excursionAt`.  Its mass statement is equivalent
    to the sealed `ae_lifetime_excursionAt`; its scaling statement is exactly the sealed
    `map_excursionScale_excursionAt`, with product order `λa`.
    `excursionMeasure_unique_of_scaling`
    proves uniqueness of the TOTAL measure `N` from its scaling, finite tail and unit shape.  It
    does NOT prove uniqueness of the lifetime disintegration `(N_(a))`; that statement is included.
(3) Family uniqueness needs measurability of `a ↦ ν a A` for measurable `A`, which is implicit in
    the source's measure-valued integral.  Probability mass, exact lifetime support and the full
    weighted mixture are retained; scaling alone or uniqueness of `N` would be a weaker claim.
    The library density already contains the normalization `p₁(0)`, so no second factor is added.
(4) C25 is almost sure for each fixed `t > 0`.  On the common full-measure event,
    `ae_straddle_spec` gives `g_t < t < d_t`, while `ae_isExcursionInterval_of_jump` makes
    `(g_t,d_t)` an excursion interval: both endpoints are zeros and every interior time is
    strictly positive.  Hence `g_t` itself is the greatest zero at most `t`, and `d_t` itself is
    the least zero strictly after `t`.  In particular, no additional closure hypothesis or a
    sequence-of-zeros argument is needed.  This identifies both endpoints simultaneously, so all
    O01 path conclusions and the sealed C25 height conclusions can be rewritten with the spec's
    definitions without changing their normalizations.

PROOF PLAN (estimated 500–950 lines total, including reusable measurability helpers).
(a) `reflectedFutureAt_apply` (5–15 lines): unfold the two new definitions and apply
    `reflectedFrom_restart_shiftAt 0 τ hτfin u` symmetrically.
(b) `condExp_reflectedFutureAt` (250–450 lines): first show progressive measurability of
    `(t,f) ↦ (reflectedFrom 0 f).1 t` from `DLoc.isStronglyProgressive_eval`, the running-infimum
    restriction API and `reflectedFrom_zero_apply`; obtain stopped-state measurability with
    `measurable_stoppedValue`/`DLoc.measurable_stoppedValue_eval`.  Then follow the bounded-kernel
    argument of `condExp_supReflectedFromLoc_markov`: for every stopped set `A`, apply
    `integral_shiftAt_mul_past_of_ae_lt_top` to the centered future and the test
    `(y,g) ↦ G (reflectedFrom y g)`, using `measurable_reflectedFrom`,
    `hG.stronglyMeasurable.integral_prod_right'`, and
    `ae_eq_condExp_of_forall_setIntegral_eq`.  This proves the genuine conditional transition
    law, not merely independence of the centered future.
(c) `measure_lifetime_excursionAt` (10–25 lines): use `ae_lifetime_excursionAt hθ a`, the
    measurable lifetime equation and `isProbabilityMeasure_excursionAt`; equivalently convert the
    a.e. equality to full mass of its truth set.
(d) `excursionAt_scaling` (1–5 lines): exact `map_excursionScale_excursionAt θ c a`.
(e) `excursionAt_unique` (180–350 lines): for each measurable path set `A` and lifetime set `B`,
    use exact lifetime support to restrict the supplied mixture and
    `excursionMeasure_eq_lifetime_mixture hθ` to `B`.  Rewrite these as equality of two
    `volIoi.withDensity` measures and apply `withDensity_eq_iff` (or its sigma-finite variant),
    `measurable_excursionAt_apply`, and positivity of `lifetimeDensity` to obtain a.e. equality of
    `a ↦ ν a A` and `a ↦ excursionAt θ a A`.  Use `measurable_excursionScale θ`,
    `map_excursionScale_excursionAt`, the candidate scaling premise, and `Measure.map_apply` to
    propagate equality from almost every lifetime to every positive lifetime; conclude by
    `Measure.ext`.  A countably generated path-set argument may be factored out if simultaneous
    exceptional sets obstruct the scaling step.  The existing
    `excursionMeasure_unique_of_scaling` is not a valid shortcut for this disintegration claim.
(f) `ae_straddleStart_eq_sSup` and `ae_straddleEnd_eq_sInf` (35–70 lines each): filter
    `ae_straddle_spec hθ ht`, `ae_isExcursionInterval_of_jump hθ`, and
    `ae_eval_zero_stableLocalLaw hθ`.  Rewrite endpoint zeros with `reflectedFrom_zero_apply`.
    Interior positivity rules out every competitor between `g_t` and `t`, respectively between
    `t` and `d_t`.  Package `IsGreatest`/`IsLeast` and finish with `IsGreatest.csSup_eq` and
    `IsLeast.csInf_eq`.
RISK.  C20's main work is stopped-time progressive measurability and the two-variable conditional
kernel, not the restart algebra.  C22 uniqueness requires the explicit measurability premise and
care with lifetime-dependent null sets.  C25 has no known mathematical risk.

ACYCLICITY.  C20 uses only N05 (`StableStrongMarkov`) and E02a (`ReflectedRestart`).  C22 uses only
E06 (`UnitExcursionLaw*`) and its sealed lifetime/scaling inputs.  C25 uses O01, the sealed C25
height module, and their sealed excursion-support dependencies.  No statement depends on this
contract, on K-nodes, or on another soft-gap declaration.

BINDER SCOPE (AUDITOR_RULES).  Every integral body is explicitly parenthesized before any later
arithmetic.  In particular, `∫ g, G (reflectedFrom ... g) ∂P` is enclosed when it
occurs inside another expression.  Mixture integrals have the parenthesized body
`(∫⁻ ... ) * lifetimeDensity ...`; no unparenthesized big-operator body is followed
by `+` or `−`.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-! ### C20.1: strong Markov property of the reflected process -/

/-- Reflected state at a random time, with the standard `toNNReal` junk branch at infinity. -/
noncomputable def reflectedStateAt (τ : DLoc → ℝ≥0∞) (f : DLoc) : ℝ≥0 :=
  ⟨(reflectedFrom 0 f).1 (τ f).toNNReal, reflectedFrom_nonneg 0 f _⟩

/-- Post-`τ` reflected path, restarted from its stopped state on the centered stable future. -/
noncomputable def reflectedFutureAt (τ : DLoc → ℝ≥0∞) (f : DLoc) : DLoc :=
  reflectedFrom (reflectedStateAt τ f) (DLoc.shiftAt τ f)

/-- On `{τ < ∞}`, `reflectedFutureAt` is literally the reflected path after time `τ`. -/
theorem reflectedFutureAt_apply (τ : DLoc → ℝ≥0∞) {f : DLoc} (hτfin : τ f < ⊤)
    (u : ℝ≥0) :
    (reflectedFutureAt τ f).1 u = (reflectedFrom 0 f).1 ((τ f).toNNReal + u) := sorry

/-- **C20.1, strong Markov property.**  Conditionally on `F_τ`, the post-τ reflected path has
the reflected stable transition law started at its stopped reflected value. -/
theorem condExp_reflectedFutureAt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ)
    (hfin : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), τ f < ⊤)
    {G : DLoc → ℝ} (hG : Measurable G) (hGb : ∃ C : ℝ, ∀ p, |G p| ≤ C) :
    (stableLocalLaw θ : Measure DLoc)[fun f => G (reflectedFutureAt τ f) |
        hτ.measurableSpace] =ᵐ[(stableLocalLaw θ : Measure DLoc)]
      fun f => ∫ g, G (reflectedFrom (reflectedStateAt τ f) g)
        ∂(stableLocalLaw θ : Measure DLoc) := sorry

/-! ### C22: Itô's lifetime-indexed family -/

/-- **C22, exact lifetime.**  For every `a > 0`, `N_(a)` assigns mass one to `{ζ = a}`. -/
theorem measure_lifetime_excursionAt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (a : Set.Ioi (0 : ℝ)) :
    excursionAt θ a {e : Excursion | (e.lifetime : ℝ) = (a : ℝ)} = 1 := sorry

/-- **C22, scaling.**  `(S^(λ))_* N_(a) = N_(λa)` for every `λ,a > 0`. -/
theorem excursionAt_scaling (θ : ℝ) (c a : Set.Ioi (0 : ℝ)) :
    (excursionAt θ a).map (excursionScale θ c) =
      excursionAt θ ⟨(c : ℝ) * (a : ℝ), Set.mem_Ioi.2 (mul_pos c.2 a.2)⟩ := sorry

/-- **C22, uniqueness of the Itô family.**  A measurable probability family with exact lifetime
support, the stable scaling law and the lifetime mixture of `N` is `excursionAt θ`. -/
theorem excursionAt_unique {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (ν : Set.Ioi (0 : ℝ) → Measure Excursion)
    (hprob : ∀ a, ν a Set.univ = 1)
    (hlife : ∀ a, ν a {e : Excursion | (e.lifetime : ℝ) = (a : ℝ)} = 1)
    (hscale : ∀ c a, (ν a).map (excursionScale θ c) =
      ν ⟨(c : ℝ) * (a : ℝ), Set.mem_Ioi.2 (mul_pos c.2 a.2)⟩)
    (hmeas : ∀ A : Set Excursion, MeasurableSet A → Measurable (fun a => ν a A))
    (hmix : ∀ A : Set Excursion, MeasurableSet A → excursionMeasure θ A =
      ∫⁻ a, ν a A * lifetimeDensity θ a ∂volIoi) (a : Set.Ioi (0 : ℝ)) :
    ν a = excursionAt θ a := sorry

/-! ### C25: the source definitions of the straddling endpoints -/

/-- **C25, last zero before `t`.**  O01's `straddleStart t f` is almost surely
`sup {s ≤ t | X_s = I_s}`. -/
theorem ae_straddleStart_eq_sSup {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {t : ℝ≥0} (ht : 0 < t) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), straddleStart t f =
      sSup {s : ℝ≥0 | s ≤ t ∧ f.1 s = runningInfLoc f s} := sorry

/-- **C25, first zero after `t`.**  O01's `straddleEnd t f` is almost surely
`inf {s > t | X_s = I_s}`. -/
theorem ae_straddleEnd_eq_sInf {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {t : ℝ≥0} (ht : 0 < t) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), straddleEnd t f =
      sInf {s : ℝ≥0 | t < s ∧ f.1 s = runningInfLoc f s} := sorry

end BGW.StableTrees
