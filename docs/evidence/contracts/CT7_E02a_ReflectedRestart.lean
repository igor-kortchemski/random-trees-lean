import BGW.Skorokhod.DLocShiftAt
import BGW.StableTrees.StableFirstPassage
import BGW.StableTrees.StableContinuousMinimum
import BGW.StableTrees.StableLocalMarkov

/-! Contract probe for CT7 node E02a (deterministic reflected restart and rational-window endpoint
adapters; the deterministic part of E02 / C20), following `r3-ct7-blueprint/blueprint.md` E02 and
the AUDIT "first three nodes".  NO probability appears below: the stochastic support theorem
(`ae_excursionInterval_spec`, strong Markov of the reflected process, regular zero set) waits for
N09 sealing.

Conventions.  Spectrally POSITIVE paths (jumps upward only; sealed form
`∀ s, leftLim f s ≤ f s`), excursions of `R = X - I` away from `0` where
`I_t = inf_{u ≤ t} X_u = runningInfLoc f t`.  `reflectedFrom y f` is the Skorokhod reflection of
`y + X` at `0`: `t ↦ y + X_t - min 0 (y + I_t)`; for `X_0 = 0` and `y = 0` it is `X - I`.
Its running-infimum term is antitone and right-continuous (cadlag) for every cadlag `X`, so
`reflectedFrom` is a total `DLoc`-valued map (no junk case).
`IsExcursionCandidate f g d`: `R > 0` on `(g,d)`, `R(g-) = 0`, `R(d) = 0`, WITHOUT `R(g) = 0`
(a jump start out of the infimum is allowed).  `IsExcursionInterval f g d` is a candidate with
moreover `R(g) = 0` (`isExcursionInterval_of_isExcursionCandidate`); the condition `R(g) = 0`
is what makes distinct intervals disjoint (`IsExcursionInterval.eq_of_lt`), while under
`NoNegJumps` the left-limit condition is implied by it
(`leftLim_reflectedFrom_eq_zero_of_noNegJumps`).  Maximal positivity interval of the reflected
path; at `g = 0` the left limit is the value.
JUMP STARTS.  Components of `{R > 0}` that start with a jump out of the infimum are of the form
`[g,d)` (`R g > 0`, `R(g-) = 0`) and are EXCLUDED from `IsExcursionInterval` by design (also
from `cutValid` of E01); for stable `θ ∈ (1,2]` they are a.s. absent, an obligation of the later
stochastic support theorem.  Candidates exist so that the sealed continuity of generalized
minimizers over the countably many rational windows (`isGenMinimizer_shift_restrict_of_isExcursionCandidate`)
can later PROVE `R g = 0`.
All passage statements use the SEALED strict passage `firstPassageBelow x = inf{t | X_t < -x}`,
which is a stopping time but is NOT the first hitting time of `-x`; the endpoint `d` is described
by first zero of `R` (a hitting statement) and is never identified with a strict passage time.

Sealed inputs reused (not re-declared): `runningInfLoc`, `runningInfLoc_antitone`,
`runningInfLoc_continuous`, `firstPassageBelow`, `DLoc.strictPassageBelow`, `DLoc.shift`,
`DLoc.shiftAt`, `DLoc.eval_shiftAt`, `DLoc.restrict`, `ST.IsGenMinimizer`, `ST.genVal`
(StableUniqueMinimum / StableContinuousMinimum: `IsStableLevyLaw.ae_continuousAt_of_isGenMinimizer`
is the stochastic consumer of the rational-window statement).
Estimate 350-600 lines. -/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The reflected path `t ↦ y + X_t - min 0 (y + I_t)` is càdlàg: `I` is monotone, bounded on
compacts and right-continuous. -/
theorem isCadlag_reflectedFrom (y : ℝ≥0) (f : DLoc) :
    IsCadlag (fun t : ℝ≥0 => (y : ℝ) + f.1 t - min 0 ((y : ℝ) + runningInfLoc f t)) := sorry

/-- **Reflection at zero** of `y + X`: `t ↦ y + X_t - min 0 (y + I_t)`. -/
noncomputable def reflectedFrom (y : ℝ≥0) (f : DLoc) : DLoc :=
  ⟨fun t => (y : ℝ) + f.1 t - min 0 ((y : ℝ) + runningInfLoc f t), isCadlag_reflectedFrom y f⟩

/-- Sealed no-negative-jumps hypothesis, as used in `runningInfLoc_continuous`. -/
def NoNegJumps (f : DLoc) : Prop := ∀ s : ℝ≥0, Function.leftLim f.1 s ≤ f.1 s

/-- **Excursion candidate** of the reflected path from `0`: positive on `(g,d)`, `R(g-) = 0`,
`R(d) = 0`; `R(g) = 0` is NOT required (jump starts allowed). -/
def IsExcursionCandidate (f : DLoc) (g d : ℝ≥0) : Prop :=
  g < d ∧ (∀ t : ℝ≥0, g < t → t < d → 0 < (reflectedFrom 0 f).1 t) ∧
    Function.leftLim (reflectedFrom 0 f).1 g = 0 ∧ (reflectedFrom 0 f).1 d = 0

/-- **Excursion interval** of the reflected path from `0`: an excursion candidate with
`R(g) = 0` (continuous start; jump starts are excluded by design). -/
def IsExcursionInterval (f : DLoc) (g d : ℝ≥0) : Prop :=
  g < d ∧ (∀ t : ℝ≥0, g < t → t < d → 0 < (reflectedFrom 0 f).1 t) ∧
    Function.leftLim (reflectedFrom 0 f).1 g = 0 ∧ (reflectedFrom 0 f).1 g = 0 ∧
      (reflectedFrom 0 f).1 d = 0

/-- **(i)** Under `NoNegJumps`, `R g = 0` implies `R(g-) = 0` (`R ≥ 0`, `I` continuous, so
`R(g-) = X(g-) - min 0 I_g ≤ X g - min 0 I_g = R g`). -/
theorem leftLim_reflectedFrom_eq_zero_of_noNegJumps {f : DLoc} (hf : NoNegJumps f) {g : ℝ≥0}
    (hg : (reflectedFrom 0 f).1 g = 0) : Function.leftLim (reflectedFrom 0 f).1 g = 0 := sorry

/-- **(ii)** An excursion candidate with `R g = 0` is an excursion interval. -/
theorem isExcursionInterval_of_isExcursionCandidate {f : DLoc} {g d : ℝ≥0}
    (h : IsExcursionCandidate f g d) (hg : (reflectedFrom 0 f).1 g = 0) :
    IsExcursionInterval f g d :=
  ⟨h.1, h.2.1, h.2.2.1, hg, h.2.2.2⟩

/-- An excursion interval is a candidate. -/
theorem IsExcursionInterval.isExcursionCandidate {f : DLoc} {g d : ℝ≥0}
    (h : IsExcursionInterval f g d) : IsExcursionCandidate f g d :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩

/-- Reflection is nonnegative. -/
theorem reflectedFrom_nonneg (y : ℝ≥0) (f : DLoc) (t : ℝ≥0) : 0 ≤ (reflectedFrom y f).1 t := sorry

/-- For `X_0 = 0` the reflection from `0` is `X - I`. -/
theorem reflectedFrom_zero_apply {f : DLoc} (h0 : f.1 0 = 0) (t : ℝ≥0) :
    (reflectedFrom 0 f).1 t = f.1 t - runningInfLoc f t := sorry

/-- **Deterministic restart.** Reflection from `y` at time `s + u` is the reflection, from the
value `R_s` reached at `s`, of the centered shifted path at time `u`.  No hypothesis on `f`. -/
theorem reflectedFrom_restart (y : ℝ≥0) (f : DLoc) (s u : ℝ≥0) :
    (reflectedFrom y f).1 (s + u) =
      (reflectedFrom (⟨(reflectedFrom y f).1 s, reflectedFrom_nonneg y f s⟩ : ℝ≥0)
        (DLoc.shift s f)).1 u := sorry

/-- **Restart at a random time** (everywhere form; on `{τ f < ⊤}`; junk shift otherwise). -/
theorem reflectedFrom_restart_shiftAt (y : ℝ≥0) (τ : DLoc → ℝ≥0∞) {f : DLoc} (hτ : τ f < ⊤)
    (u : ℝ≥0) :
    (reflectedFrom y f).1 ((τ f).toNNReal + u) =
      (reflectedFrom (⟨(reflectedFrom y f).1 (τ f).toNNReal,
        reflectedFrom_nonneg y f _⟩ : ℝ≥0) (DLoc.shiftAt τ f)).1 u := sorry

/-- Joint measurability of the reflection in `(y, f)`. -/
theorem measurable_reflectedFrom : Measurable (fun p : ℝ≥0 × DLoc => reflectedFrom p.1 p.2) := sorry

/-- Joint measurability of `(y, f, t) ↦ (reflectedFrom y f) t`. -/
theorem measurable_reflectedFrom_eval :
    Measurable (fun p : ℝ≥0 × DLoc × ℝ≥0 => (reflectedFrom p.1 p.2.1).1 p.2.2) := sorry

/-- **First passage as the generalized inverse of the running infimum.** Everywhere (no
hypothesis): `T_x = inf {t | I_t < -x}`. -/
theorem firstPassageBelow_eq_inf_runningInf (x : ℝ≥0) (f : DLoc) :
    firstPassageBelow x f = ⨅ (t : ℝ≥0) (_ : runningInfLoc f t < -(x : ℝ)), (t : WithTop ℝ≥0) :=
  sorry

/-- **Reflection vanishes at the passage time** (creeping): for a spectrally positive path with
`X_0 = 0` and `T_x` finite, `I_{T_x} = -x = X_{T_x}`, hence `R_{T_x} = 0`. -/
theorem reflectedFrom_firstPassageBelow {f : DLoc} (hf : NoNegJumps f) (h0 : f.1 0 = 0)
    {x : ℝ≥0} (hx : 0 < x) (hT : firstPassageBelow x f < ⊤) :
    runningInfLoc f ((firstPassageBelow x f).untopD 0) = -(x : ℝ) ∧
      (reflectedFrom 0 f).1 ((firstPassageBelow x f).untopD 0) = 0 := sorry

/-- **Restart at the passage time**: the reflected path after `T_x` is the reflection from `0`
of the centered post-`T_x` path. -/
theorem reflectedFrom_restart_firstPassageBelow {f : DLoc} (hf : NoNegJumps f) (h0 : f.1 0 = 0)
    {x : ℝ≥0} (hx : 0 < x) (hT : firstPassageBelow x f < ⊤) (u : ℝ≥0) :
    (reflectedFrom 0 f).1 ((firstPassageBelow x f).untopD 0 + u) =
      (reflectedFrom 0 (DLoc.shiftAt (firstPassageBelow x) f)).1 u := sorry

/-- **The running infimum is constant on an excursion interval** (spectrally positive,
`X_0 = 0`): `I_t = I_g` for `g ≤ t ≤ d`. -/
theorem runningInfLoc_const_of_isExcursionInterval {f : DLoc} (hf : NoNegJumps f)
    (h0 : f.1 0 = 0) {g d : ℝ≥0} (h : IsExcursionInterval f g d) {t : ℝ≥0}
    (hgt : g ≤ t) (htd : t ≤ d) : runningInfLoc f t = runningInfLoc f g := sorry

/-- The left limit of `X` at the start of an excursion is the running infimum there. -/
theorem leftLim_eq_runningInf_of_isExcursionInterval {f : DLoc} (hf : NoNegJumps f)
    (h0 : f.1 0 = 0) {g d : ℝ≥0} (h : IsExcursionInterval f g d) :
    Function.leftLim f.1 g = runningInfLoc f g := sorry

/-- **Rational windows around the start `g`.** Every excursion interval with `0 < g` has
nonnegative rationals `r < g < q < d` (for `g = 0` no `r` exists, hence `0 < g`). -/
theorem exists_rat_window_of_isExcursionInterval {f : DLoc} {g d : ℝ≥0}
    (h : IsExcursionInterval f g d) (hg : 0 < g) :
    ∃ r q : ℚ≥0, (r : ℝ≥0) < g ∧ g < (q : ℝ≥0) ∧ (q : ℝ≥0) < d := sorry

/-- **Candidate version of the window infimum**: for an excursion candidate `(g,d)` (no `R g = 0`
needed) under `NoNegJumps`, the infimum of `X` over `[r,q]`, `r < g < q < d`, equals `X(g-)`. -/
theorem iInf_window_eq_leftLim_of_isExcursionCandidate {f : DLoc} (hf : NoNegJumps f)
    (h0 : f.1 0 = 0) {g d r q : ℝ≥0} (h : IsExcursionCandidate f g d) (hrg : r < g) (hgq : g < q)
    (hqd : q < d) :
    (⨅ u : Set.Icc r q, f.1 u) = Function.leftLim f.1 g := sorry

/-- **The window infimum is the left limit at the start.** If `(g,d)` is an excursion interval and
`r < g < q < d`, the infimum of `X` over `[r,q]` equals `X(g-) = I_g`. -/
theorem iInf_window_eq_leftLim_of_isExcursionInterval {f : DLoc} (hf : NoNegJumps f)
    (h0 : f.1 0 = 0) {g d r q : ℝ≥0} (h : IsExcursionInterval f g d) (hrg : r < g) (hgq : g < q)
    (hqd : q < d) :
    (⨅ u : Set.Icc r q, f.1 u) = Function.leftLim f.1 g := sorry

/-- The time `g - r`, as a point of the horizon `[0, q - r]` of the shifted window. -/
noncomputable def shiftedWindowTime (r g q : ℝ≥0) (hrg : r ≤ g) (hgq : g ≤ q) :
    Set.Icc (0 : ℝ) ((q - r : ℝ≥0) : ℝ) :=
  ⟨(g : ℝ) - r, sub_nonneg.2 (by exact_mod_cast hrg), by
    rw [NNReal.coe_sub (hrg.trans hgq)]
    have : (g : ℝ) ≤ q := by exact_mod_cast hgq
    linarith⟩

/-- **Window minimizer adapter** (feeds `IsStableLevyLaw.ae_continuousAt_of_isGenMinimizer`):
for an excursion interval `(g,d)` and `r < g < q < d`, `g - r` is a generalized minimizer of the
centered shift at `r`, restricted to the horizon `[0, q - r]`.  (Here `g` is generalized, through
its left limit.) -/
theorem isGenMinimizer_shift_restrict_of_isExcursionInterval {f : DLoc} (hf : NoNegJumps f)
    (h0 : f.1 0 = 0) {g d r q : ℝ≥0} (h : IsExcursionInterval f g d) (hrg : r < g) (hgq : g < q)
    (hqd : q < d) :
    IsGenMinimizer (DLoc.restrict (q - r) (DLoc.shift r f))
      (shiftedWindowTime r g q hrg.le hgq.le) := sorry

/-- **Window minimizer adapter for candidates**: the same statement for an excursion candidate
`(g,d)` (jump start allowed); the generalized minimum over the rational window is attained at `g`
as a left limit.  Sealed continuity of minimizers on countably many rational windows then gives
`R g = 0` (a.s., stochastic step). -/
theorem isGenMinimizer_shift_restrict_of_isExcursionCandidate {f : DLoc} (hf : NoNegJumps f)
    (h0 : f.1 0 = 0) {g d r q : ℝ≥0} (h : IsExcursionCandidate f g d) (hrg : r < g) (hgq : g < q)
    (hqd : q < d) :
    IsGenMinimizer (DLoc.restrict (q - r) (DLoc.shift r f))
      (shiftedWindowTime r g q hrg.le hgq.le) := sorry

/-- **End of an excursion = first zero of the reflection after any interior rational time**:
`d = inf {t ≥ r | R_t = 0}` for `r ∈ (g,d)`. -/
theorem excursionEnd_eq_sInf_zero {f : DLoc} {g d r : ℝ≥0} (h : IsExcursionInterval f g d)
    (hgr : g < r) (hrd : r < d) :
    d = sInf {t : ℝ≥0 | r ≤ t ∧ (reflectedFrom 0 f).1 t = 0} := sorry

/-- **Excursion intervals are disjoint**: a later start cannot lie inside an earlier interval. -/
theorem IsExcursionInterval.eq_of_lt {f : DLoc} {g d g' d' : ℝ≥0}
    (h : IsExcursionInterval f g d) (h' : IsExcursionInterval f g' d') (hlt : g < g')
    (hover : g' < d) : False := sorry

end BGW.StableTrees
