import BGW.StableTrees.ExcursionMeasure
import BGW.StableTrees.MarkedExcursions
import BGW.StableTrees.StableExcursionSupport
import BGW.ContinuumTrees.ExcursionCarrier
import BGW.StableTrees.StableStrongMarkov
import BGW.StableTrees.StableFirstPassage
import BGW.StableTrees.StablePassageSubordinator

/-! Contract probe for CT7 node E07 (killed kernel and the excursion Markov property),
following `r3-ct7-blueprint/blueprint.md` E07, its signature block and AUDIT items 4-5.

CONSTANTS.  `N = excursionMeasure θ`, `P = stableLocalLaw θ`, `T_y = firstPassageBelow y`
(strict passage below `-y`, a stopping time).  For `y ≥ 0` the killed path is
`(K_y)(s) = y + X_{s ∧ T_y}` (UNCENTRED, started at `y`, no `- X_0` correction, frozen at the
passage time; if `T_y = ⊤` it is `y + X_s`).  By creeping (`ae_firstPassageBelow_spec`) the
killed path is `0` at and after `T_y` for `y > 0`, and `T_0 = 0` a.s. (regularity), so the
state `0` is absorbing: `K_0 = δ_{zeroLoc}`.  The future of an excursion after age `t` is
`futureFrom t e = (s ↦ e(t+s))`, again uncentred and started at `e(t)`.

DEFINITIONS (no `sorry`).  `Excursion.valueNN`, `stopLocAt`, `killedPath`, `futureFrom`
(cadlag via `IsCadlag.continuous_comp` of `stopLoc`/`DLoc.shift`), and
`killedStableKernel θ = (δ_id ×ₖ const P).map (fun (y, f) => killedPath y f)` (a `Kernel.map`,
whose measurability side condition is the theorem `measurable_killedPath_uncurry`; if it
failed, the kernel would silently be `0`, hence `killedStableKernel_apply`).

TRUTH.  All theorems bind `hθ : 1 < θ ∧ θ ≤ 2` and `0 < t`.  Integrals are over `{t < ζ}`
w.r.t. `N` (an infinite measure, `σ`-finite on `{t < ζ}` since `N(ζ > t) < ∞`).  `F` tests
the prefix `r_t e` (`excursionRestrict t`, in `D t ℝ`), `G` the whole future.  On `{t < ζ}`
`e(t) > 0` N-a.e. (E04 support), so `K_{e(t)}` is the genuinely killed law; the identity uses
the junk-safe `valueNN e t = (e(t)).toNNReal`.  `N_noFixedJump` is about `leftLim`, no `t < ζ`
restriction needed (at `t = ζ` the left limit and the value are both `0`).

PROOF PLAN.  (1) Jointly measurable killed kernel from `measurable_firstPassageBelow_uncurry`
and `DLoc.measurable_eval₂`.  (2) AUDIT item 5: enumerate in chronological order the excursions
surviving to age `t` through an adapted age process with strict age crossings; the selected
times and the restart times are stopping times (`g + t` is NOT a stopping time for the
non-stopping start `g`).  (3) Apply `measure_inter_preimage_shiftAt` (strong Markov) at those
times, then E04 compensation (`excursion_compensation_*`) to turn the sum over surviving
excursions into `N`; truncate local/physical time and pass to the limit by monotone
convergence.  (4) Remaining lifetime and `N_noFixedJump` (restart at `t/2`; killing creates no
jump since the passage creeps).  Estimate 900-1600 lines. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-! ### Definitions -/

/-- The value of an excursion at time `t`, as a nonnegative real (`(e t).toNNReal`; the path
is nonnegative so nothing is lost). -/
noncomputable def Excursion.valueNN (e : Excursion) (t : ℝ≥0) : ℝ≥0 := (e.path.1 t).toNNReal

/-- Stop a path at an extended time: `⊤` leaves it unchanged, `↑a` is `stopLoc a`. -/
noncomputable def stopLocAt : WithTop ℝ≥0 → DLoc → DLoc
  | ⊤, f => f
  | (a : ℝ≥0), f => stopLoc a f

/-- **The killed path started at `y`**: `s ↦ y + X_{s ∧ T_y}` with `T_y = firstPassageBelow y`
(uncentred, frozen after the first passage below `-y`, where it equals `0` a.s.). -/
noncomputable def killedPath (y : ℝ≥0) (f : DLoc) : DLoc :=
  ⟨fun s => (y : ℝ) + (stopLocAt (firstPassageBelow y f) f).1 s,
    (stopLocAt (firstPassageBelow y f) f).2.continuous_comp (g := fun z : ℝ => (y : ℝ) + z)
      (continuous_const.add continuous_id)⟩

/-- **Uncentred future of an excursion after age `t`**: `s ↦ e(t + s)`. -/
noncomputable def futureFrom (t : ℝ≥0) (e : Excursion) : DLoc :=
  ⟨fun s => e.path.1 t + (DLoc.shift t e.path).1 s,
    (DLoc.shift t e.path).2.continuous_comp (g := fun z : ℝ => e.path.1 t + z)
      (continuous_const.add continuous_id)⟩

/-- **The killed stable kernel** `y ↦ Law_P(killedPath y)`, a kernel `ℝ≥0 → DLoc`, with the
zero path absorbing (`killedStableKernel_zero`). -/
noncomputable def killedStableKernel (θ : ℝ) : Kernel ℝ≥0 DLoc :=
  Kernel.map (Kernel.prod (Kernel.deterministic (id : ℝ≥0 → ℝ≥0) measurable_id)
    (Kernel.const ℝ≥0 (stableLocalLaw θ : Measure DLoc)))
    (fun p : ℝ≥0 × DLoc => killedPath p.1 p.2)

/-- **Last positive time** of a path: `sup {t | g t > 0}` (`⊥ = 0` if none).  Measurable
(`measurable_lastPositiveTime`), unlike weak first hitting of a closed set. -/
noncomputable def lastPositiveTime (g : DLoc) : WithTop ℝ≥0 :=
  ⨆ t : {t : ℝ≥0 // 0 < g.1 t}, ((t.1 : ℝ≥0) : WithTop ℝ≥0)

/-- `lastPositiveTime` is measurable: `{L > s} = ⋃_{q ∈ ℚ, q > s} {g q > 0}` by
right-continuity of `g`. -/
theorem measurable_lastPositiveTime : Measurable lastPositiveTime := sorry

/-! ### Basic facts on the killed path and kernel -/

/-- Evaluation of the future: `(futureFrom t e)(s) = e(t + s)`. -/
theorem futureFrom_apply (t : ℝ≥0) (e : Excursion) (s : ℝ≥0) :
    (futureFrom t e).1 s = e.path.1 (t + s) := by
  change e.path.1 t + (e.path.1 (t + s) - e.path.1 t) = _
  ring

/-- `futureFrom t` is measurable. -/
theorem measurable_futureFrom (t : ℝ≥0) : Measurable (futureFrom t) := sorry

/-- Evaluation of the killed path when the passage time is finite. -/
theorem killedPath_apply_of_lt_top {y : ℝ≥0} {f : DLoc} {τ : ℝ≥0}
    (h : firstPassageBelow y f = (τ : WithTop ℝ≥0)) (s : ℝ≥0) :
    (killedPath y f).1 s = (y : ℝ) + f.1 (min s τ) := by
  simp [killedPath, h, stopLocAt, stopLoc]

/-- Evaluation of the killed path when there is no passage. -/
theorem killedPath_apply_of_eq_top {y : ℝ≥0} {f : DLoc}
    (h : firstPassageBelow y f = ⊤) (s : ℝ≥0) : (killedPath y f).1 s = (y : ℝ) + f.1 s := by
  simp [killedPath, h, stopLocAt]

/-- **Joint measurability** of `(y, f) ↦ killedPath y f` (from
`measurable_firstPassageBelow_uncurry` and `DLoc.measurable_eval₂`). -/
theorem measurable_killedPath_uncurry :
    Measurable (fun p : ℝ≥0 × DLoc => killedPath p.1 p.2) := sorry

/-- The kernel is the law of the killed path: `K_y = P.map (killedPath y)`. -/
theorem killedStableKernel_apply (θ : ℝ) (y : ℝ≥0) :
    killedStableKernel θ y = (stableLocalLaw θ : Measure DLoc).map (killedPath y) := sorry

/-- The killed kernel is a Markov kernel (probability measures). -/
theorem isMarkovKernel_killedStableKernel (θ : ℝ) : IsMarkovKernel (killedStableKernel θ) := sorry

/-- **Killed paths are nonnegative and absorbed at zero**: for each fixed positive starting
level `y`, a.s. under `P` the killed path starts at `y`, is `≥ 0`, positive before `T_y`
and is `0` from the passage time on.  (`y` is fixed BEFORE `∀ᵐ`: simultaneous strict
positivity over all levels is false, at passage-jump levels `X_{T_{y-}} = -y`.) -/
theorem ae_killedPath_spec {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (y : ℝ≥0) (hy : 0 < y) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (killedPath y f).1 0 = (y : ℝ) ∧ (∀ s, 0 ≤ (killedPath y f).1 s) ∧
      (∀ s : ℝ≥0, (s : WithTop ℝ≥0) < firstPassageBelow y f →
        0 < (killedPath y f).1 s) ∧
      ∀ s : ℝ≥0, firstPassageBelow y f ≤ (s : WithTop ℝ≥0) → (killedPath y f).1 s = 0 :=
  sorry

/-- **Simultaneous version** (start, nonnegativity, zero after strict passage; NO strict
pre-passage positivity, which fails simultaneously over levels). -/
theorem ae_killedPath_spec_simultaneous {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ y : ℝ≥0, 0 < y →
      (killedPath y f).1 0 = (y : ℝ) ∧ (∀ s, 0 ≤ (killedPath y f).1 s) ∧
      ∀ s : ℝ≥0, firstPassageBelow y f ≤ (s : WithTop ℝ≥0) → (killedPath y f).1 s = 0 :=
  sorry

/-- `T_0 = 0` a.s.: sealed supplier is `ae_passageTime_eq_firstPassageBelow` (second clause
`passageTime 0 f = 0`, with `firstPassageBelow 0 f` its finite reading), itself from
`ae_strictPassage_zero_stableLocalLaw` (regularity, `StableRegularity.lean`). -/
theorem ae_firstPassageBelow_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), firstPassageBelow 0 f = 0 := by
  filter_upwards [ae_passageTime_eq_firstPassageBelow hθ] with f hf
  rw [hf.1 0, hf.2]
  rfl

/-- **Zero is absorbing**: `K_0 = δ_{zeroLoc}` as measures (`T_0 = 0` a.s. by regularity of `(-∞,0)`
at `0`). -/
theorem killedStableKernel_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    killedStableKernel θ 0 = Measure.dirac zeroLoc := sorry

/-! ### Supporting exports -/

/-- `valueNN` is measurable. -/
theorem measurable_excursion_valueNN (t : ℝ≥0) :
    Measurable (fun e : Excursion => e.valueNN t) :=
  (measurable_excursion_eval t).real_toNNReal

/-- `valueNN` is jointly measurable in `(e, t)`. -/
theorem measurable_excursion_valueNN_uncurry :
    Measurable (fun p : Excursion × ℝ≥0 => p.1.valueNN p.2) :=
  measurable_excursion_eval₂.real_toNNReal

/-- Real-value bridge: the carrier requires nonnegativity, so nothing is truncated. -/
theorem Excursion.coe_valueNN (e : Excursion) (t : ℝ≥0) :
    (e.valueNN t : ℝ) = e.path.1 t :=
  Real.coe_toNNReal _ (e.2.2.1 t)

/-- **Strict positivity of the value before death**: for `0 < t`, `N`-a.e. excursion alive
at age `t` has `e(t) > 0` (E04 support, `ae_excursionMeasure_support`). -/
theorem ae_valueNN_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ e ∂((excursionMeasure θ).restrict {e : Excursion | t < e.lifetime}),
      0 < e.valueNN t := sorry

/-- The survival restriction of `N` is finite (`excursionMeasure_lifetime_slab_lt_top`);
σ-finiteness is `sigmaFinite_excursionMeasure`. -/
theorem isFiniteMeasure_excursionMeasure_survival {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0)
    (ht : 0 < t) :
    IsFiniteMeasure ((excursionMeasure θ).restrict {e : Excursion | t < e.lifetime}) := sorry

/-! ### Lifetime bridge (measurable functional `lastPositiveTime`) -/

/-- Remaining lifetime as a functional of the future: for `0 < t`, on `{t < ζ}` N-a.e.,
`lastPositiveTime (futureFrom t e) = ζ - t`. -/
theorem ae_lastPositiveTime_futureFrom {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ e ∂((excursionMeasure θ).restrict {e : Excursion | t < e.lifetime}),
      lastPositiveTime (futureFrom t e) = ((e.lifetime - t : ℝ≥0) : WithTop ℝ≥0) := sorry

/-- For each fixed `y > 0`, a.s. the last positive time of the killed path is the strict
passage time `T_y` (strict passage of the driving process, not of the killed path). -/
theorem ae_lastPositiveTime_killedPath {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (y : ℝ≥0) (hy : 0 < y) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      lastPositiveTime (killedPath y f) = firstPassageBelow y f := sorry

/-- **Age-clock supplier** (selected age-crossing times `τ n` and restart times `ρ n`, stopping
times of the right-continuous filtration, exact-once coverage of the excursions surviving to
age `t`; strict crossings exclude lifetime exactly `t`). -/
theorem exists_excursionAge_stoppingTimes {θ : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) (ht : 0 < t) :
    ∃ τ ρ : ℕ → DLoc → WithTop ℝ≥0,
      (∀ n, IsStoppingTime DLoc.filtration (τ n)) ∧
      (∀ n, IsStoppingTime DLoc.filtration (ρ n)) ∧
      (∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
        (∀ x ∈ passageJumpSet f,
          t < (jumpExcursion x f).lifetime →
          ∃! n : ℕ,
            τ n f = ((passageTimeMinus x f + t : ℝ≥0) : WithTop ℝ≥0) ∧
            ρ n f = ((passageTime x f : ℝ≥0) : WithTop ℝ≥0)) ∧
        (∀ n, τ n f < ⊤ →
          ∃ x ∈ passageJumpSet f,
            t < (jumpExcursion x f).lifetime ∧
            τ n f = ((passageTimeMinus x f + t : ℝ≥0) : WithTop ℝ≥0) ∧
            ρ n f = ((passageTime x f : ℝ≥0) : WithTop ℝ≥0)) ∧
        (∀ n, τ n f < ⊤ → τ n f < ρ n f) ∧
        (∀ n, ρ n f ≤ τ (n + 1) f)) := sorry

/-! ### The excursion Markov property -/

/-- **Excursion Markov property** (C23), exactly the blueprint signature.  For nonnegative
measurable `F` on the prefix path space `D t ℝ` (through `excursionRestrict t`) and `G` on the
whole future (through the uncentred `futureFrom t`):
`N[1_{ζ>t} F(r_t e) G(e(t+·))] = N[1_{ζ>t} F(r_t e) (K_{e(t)} G)]`. -/
theorem excursion_markov_lintegral {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) (ht : 0 < t)
    (F : D (t : ℝ) ℝ → ℝ≥0∞) (hF : Measurable F) (G : DLoc → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ e in {e : Excursion | t < e.lifetime},
        F (excursionRestrict t e) * G (futureFrom t e) ∂(excursionMeasure θ)) =
      ∫⁻ e in {e : Excursion | t < e.lifetime},
        F (excursionRestrict t e) *
          (∫⁻ f, G f ∂(killedStableKernel θ (e.valueNN t))) ∂(excursionMeasure θ) := sorry

/-- **Remaining-lifetime identity.**  Given the prefix up to age `t`, the remaining lifetime
`ζ - t` has the law of the passage time `T_{e(t)}` of the stable process, i.e.
`passageLaw θ (e(t))` (whose density is `qKernel` by E08).  For measurable `H : ℝ → ℝ≥0∞`.
Proof route: the bridge `ae_lastPositiveTime_futureFrom`/`_killedPath`, not `firstHitBelow`. -/
theorem excursion_remainingLifetime_lintegral {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0)
    (ht : 0 < t) (F : D (t : ℝ) ℝ → ℝ≥0∞) (hF : Measurable F)
    (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ e in {e : Excursion | t < e.lifetime},
        F (excursionRestrict t e) * H ((e.lifetime : ℝ) - (t : ℝ)) ∂(excursionMeasure θ)) =
      ∫⁻ e in {e : Excursion | t < e.lifetime},
        F (excursionRestrict t e) *
          (∫⁻ s, H s ∂(passageLaw θ (e.valueNN t))) ∂(excursionMeasure θ) := sorry

/-- Signed bounded-test version of the Markov property (finite survival measure, Markov
kernel). -/
theorem excursion_markov_integral {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (t : ℝ≥0) (ht : 0 < t)
    (F : D (t : ℝ) ℝ → ℝ) (hF : Measurable F)
    (hFb : ∃ C : ℝ, ∀ p, |F p| ≤ C)
    (G : DLoc → ℝ) (hG : Measurable G)
    (hGb : ∃ C : ℝ, ∀ f, |G f| ≤ C) :
    (∫ e in {e : Excursion | t < e.lifetime},
      F (excursionRestrict t e) * G (futureFrom t e) ∂(excursionMeasure θ)) =
    ∫ e in {e : Excursion | t < e.lifetime},
      F (excursionRestrict t e) *
        (∫ f, G f ∂(killedStableKernel θ (e.valueNN t)))
        ∂(excursionMeasure θ) := sorry

/-- **No fixed jumps under `N`**: for each `t > 0`, `N`-a.e. excursion is left-continuous at
`t` (restart at `t/2`; the killed path creates no jump since the passage creeps). -/
theorem N_noFixedJump {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ e ∂(excursionMeasure θ), Function.leftLim e.path.1 t = e.path.1 t := sorry

end BGW.StableTrees
