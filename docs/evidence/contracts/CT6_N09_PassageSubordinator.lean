import BGW.Skorokhod.DLoc
import BGW.Skorokhod.DLocShiftAt
import BGW.StableTrees.StableLocalLaw
import BGW.StableTrees.StableLocalMarkov
import BGW.StableTrees.StableStrongMarkov
import BGW.StableTrees.StableFirstPassage
import Mathlib.MeasureTheory.Measure.Stieltjes

/-! Contract probe for CT.C6 blueprint Node 9 (F3): the passage-time process
`x ↦ T_x = firstPassageBelow x` of the spectrally positive local stable law
`stableLocalLaw θ` is a (strictly right-continuous) stable subordinator of index `1/θ`, and
it is the right-continuous inverse of `L = -runningInf`.

Sealed inputs reused (not re-declared): `firstPassageBelow`, `runningInfLoc`,
`isStoppingTime_firstPassageBelow`, `measurable_firstPassageBelow_uncurry`,
`ae_firstPassageBelow_spec` (N08), `ae_runningInf_continuous_antitone_tendsto`,
`integral_exp_neg_strictPassageBelow` (N08 Laplace), `DLoc.shiftAt` and the strong Markov
integral/independence/law forms (N05).

Conventions.
* `T_x = firstPassageBelow x = inf{t | X_t < -x}` is STRICT passage. For levels `x > 0`
  (N08, simultaneous) it is finite, positive, and `X_{T_x} = -x`. `T_0 = 0` is the second component
  (`.2`) of the sealed `ae_strictPassage_zero_stableLocalLaw` (N06 regularity).
* Strict passage vs first hitting `H_x = inf{t | X_t ≤ -x}`. Deterministically `H_x ≤ T_x` and
  `T_{x-} ≤ H_x`, where `T_{x-} = sup_{y<x} T_y`; at a plateau level of `-runningInf`
  (a level at which `T` jumps) `H_x` and `T_x` can differ (`H_x` is a stopping time for the augmented filtration; nothing
  here depends on that). For each FIXED `x` they agree a.s.; this is NOT claimed
  simultaneously for all `x` (blueprint risk note). `T_x` is always the strict one.
* `passageTime` is the `ℝ≥0`-valued reading (`⊤ ↦ 0`), faithful on the a.s. finite good set.
* `passageLaw θ x` is the law of `T_x` on `ℝ` (pushforward of `stableLocalLaw θ`, a.s.-finite
  reading). Increments are stated as finite-vector product laws, plus independence of
  the stopped σ-algebra `F_{T_x}`; a mere `Subordinator` structure is not used.
* Junk branch: for `θ ∉ (1, 2]` the local law is the Dirac mass at the zero path and all of
  this fails, so every statement carries `1 < θ ∧ θ ≤ 2`.
* "Local time at the minimum" is `L = localTime = -runningInf`; its Stieltjes measure is
  carried by `{X = I}` (stated both as constancy of `L` away from `{X = I}` including left limits,
  and as `dL {X ≠ I} = 0` for the Stieltjes measure `localTimeStieltjes f` on `ℝ`, which is a
  junk zero measure off the a.s. event where `L` is monotone and continuous).
Maintained file: a new `BGW/StableTrees/StablePassageSubordinator.lean`.
Estimate 600–1000 lines. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees

/-- The `ℝ≥0`-valued passage time (junk value `0` on `{T_x = ⊤}`, a null set). -/
noncomputable def passageTime (x : ℝ≥0) (f : DLoc) : ℝ≥0 := (firstPassageBelow x f).untopD 0

/-- First hitting time of `(-∞, -x]`, `H_x = inf{t | X_t ≤ -x}` (weak hitting, NOT strict). -/
noncomputable def firstHitBelow (x : ℝ≥0) (f : DLoc) : WithTop ℝ≥0 :=
  sInf {t : WithTop ℝ≥0 | ∃ u : ℝ≥0, t = u ∧ f.1 u ≤ -(x : ℝ)}

/-- The law of the passage time `T_x` under the local stable law, as a measure on `ℝ`
(finite reading `passageTime`). -/
noncomputable def passageLaw (θ : ℝ) (x : ℝ≥0) : Measure ℝ :=
  Measure.map (fun f : DLoc => ((passageTime x f : ℝ≥0) : ℝ)) (stableLocalLaw θ : Measure DLoc)

/-- `passageTime x` is measurable in the path. -/
theorem measurable_passageTime (x : ℝ≥0) : Measurable (passageTime x) := sorry

/-- Joint measurability of `(x, f) ↦ T_x(f)` (finite reading). -/
theorem measurable_passageTime_uncurry :
    Measurable (fun p : ℝ≥0 × DLoc => passageTime p.1 p.2) := sorry

/-- `passageLaw θ x` is a probability measure (`x = 0` uses `T_0 = 0`). -/
theorem passageLaw_isProbabilityMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0) :
    IsProbabilityMeasure (passageLaw θ x) := sorry

/-! ### Pathwise structure: finiteness, monotonicity, strict right-continuity, `T_0 = 0` -/

/-- Almost surely, for every `x ≥ 0`, `T_x` is finite and equals its finite reading, and `T_0 = 0`. -/
theorem ae_passageTime_eq_firstPassageBelow {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (∀ x : ℝ≥0, firstPassageBelow x f = (passageTime x f : WithTop ℝ≥0)) ∧
        passageTime 0 f = 0 := sorry

/-- **Monotone, càdlàg, starts at `0`** (blueprint `ae_isCadlag_monotone_passage`). Right-continuity
here is the one for the strict passage time `T_x = inf{t | X_t < -x}`. -/
theorem ae_isCadlag_monotone_passage {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      IsCadlag (fun x : ℝ≥0 => ((passageTime x f : ℝ≥0) : ℝ)) ∧
        Monotone (fun x : ℝ≥0 => passageTime x f) ∧ passageTime 0 f = 0 := sorry

/-- Almost surely `T` is unbounded: `T_x → ∞` as `x → ∞`. -/
theorem ae_tendsto_passageTime_atTop {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      Tendsto (fun x : ℝ≥0 => passageTime x f) atTop atTop := sorry

/-! ### Inverse relation with the running infimum (`L = -runningInf` is the local time) -/

/-- **`T` is the strict right inverse of `L = -runningInf`** (blueprint
`firstPassage_eq_inverseLocalTime`): `T_x = inf{t | L_t > x}`. This is a deterministic identity,
valid for every path (bounded-below on compacts), every `x ≥ 0`, and the `inf` over the empty set
is `⊤`. -/
theorem firstPassageBelow_eq_inverseLocalTime (x : ℝ≥0) (f : DLoc) :
    firstPassageBelow x f =
      sInf {t : WithTop ℝ≥0 | ∃ u : ℝ≥0, t = u ∧ (x : ℝ) < -runningInfLoc f u} := sorry

/-- **Event sandwich for the running infimum, strict side.** For every path, level and time:
`{T_x < t} ⊆ {I_t < -x} ⊆ {T_x ≤ t}`. -/
theorem runningInf_lt_sandwich (x : ℝ≥0) (t : ℝ≥0) (f : DLoc) :
    (firstPassageBelow x f < (t : WithTop ℝ≥0) → runningInfLoc f t < -(x : ℝ)) ∧
      (runningInfLoc f t < -(x : ℝ) → firstPassageBelow x f ≤ (t : WithTop ℝ≥0)) := sorry

/-- **Weak side of the sandwich.** For every path, `H_x ≤ t → I_t ≤ -x`; also
`T_x ≤ t → I_t ≤ -x` (deterministic; stated a.s. for uniformity with the other items). The converses are NOT claimed: at a plateau level
`x` of `L` (an excursion from the minimum straddling `t`) one has `I_t = -x` but `T_x > t`. -/
theorem runningInf_le_of_firstHitBelow_le (x t : ℝ≥0) (f : DLoc)
    (h : firstHitBelow x f ≤ (t : WithTop ℝ≥0)) : runningInfLoc f t ≤ -(x : ℝ) := sorry

theorem ae_runningInf_le_of_firstPassageBelow_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ (x t : ℝ≥0),
      firstPassageBelow x f ≤ (t : WithTop ℝ≥0) → runningInfLoc f t ≤ -(x : ℝ) := sorry

/-- **Strict passage versus first hitting (deterministic sandwich).** For every path and level
`x > 0`, `sup_{y<x} T_y ≤ H_x ≤ T_x`. The left limit `T_{x-}` of the passage process is
at most the first hitting time of `-x`; a plateau of `-runningInf` at level `x` is exactly where
these are `<`. -/
theorem iSup_firstPassageBelow_le_firstHitBelow_le (f : DLoc) {x : ℝ≥0} (hx : 0 < x) :
    (⨆ y : Set.Iio x, firstPassageBelow y f) ≤ firstHitBelow x f ∧
      firstHitBelow x f ≤ firstPassageBelow x f := sorry

/-- **First hitting agrees with strict passage at each FIXED level** (a.s., NOT simultaneously
for all levels). -/
theorem ae_firstHitBelow_eq_firstPassageBelow {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), firstHitBelow x f = firstPassageBelow x f := sorry

/-- **Stieltjes measure of `L = -I` is carried by `{X = I}`**: a.s., on any interval `[s, t]`
on which both the path and its left limit stay strictly above the running infimum, `L` is constant. -/
theorem ae_runningInf_const_off_zeroSet {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ s t : ℝ≥0, s ≤ t →
      (∀ u : ℝ≥0, s ≤ u → u ≤ t →
        runningInfLoc f u < f.1 u ∧ runningInfLoc f u < Function.leftLim f.1 u) →
      runningInfLoc f t = runningInfLoc f s := sorry

/-! ### Local time `L = -I`: measurability, adaptedness, Stieltjes concentration, straddling -/

/-- The local time at the minimum, `L_t = -I_t`. -/
noncomputable def localTime (f : DLoc) (t : ℝ≥0) : ℝ := -runningInfLoc f t

/-- `L` is jointly measurable in `(t, f)`. -/
theorem measurable_localTime_uncurry :
    Measurable (fun p : ℝ≥0 × DLoc => localTime p.2 p.1) := sorry

/-- `L` is adapted to the right-continuous filtration of `DLoc`. -/
theorem stronglyAdapted_localTime :
    StronglyAdapted DLoc.filtration (fun t (f : DLoc) => localTime f t) := sorry

/-- Almost surely `L_0 = 0` (from `f 0 = 0`), `L` is monotone, continuous, and unbounded. -/
theorem ae_localTime_spec {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      localTime f 0 = 0 ∧ Monotone (localTime f) ∧ Continuous (localTime f) ∧
        Tendsto (localTime f) atTop atTop := sorry

open scoped Classical in
/-- The Stieltjes function `s ↦ L_{s⁺}` on `ℝ` (`s⁺ = max s 0`) when `L` is monotone and
continuous; junk value the zero function otherwise (a null set of paths). -/
noncomputable def localTimeStieltjes (f : DLoc) : StieltjesFunction ℝ :=
  if h : Monotone (localTime f) ∧ Continuous (localTime f) then
    { toFun := fun s => localTime f s.toNNReal
      mono' := h.1.comp (fun _ _ hab => Real.toNNReal_mono hab)
      right_continuous' := fun _ =>
        ((h.2.comp continuous_real_toNNReal).continuousAt).continuousWithinAt }
  else
    { toFun := fun _ => 0
      mono' := monotone_const
      right_continuous' := fun _ => continuousWithinAt_const }

/-- **Stieltjes measure of `L` is carried by `{X = I}`**: almost surely `dL {t | X_t ≠ I_t} = 0`
(`{X > I}` is the union of an open set on which `L` is constant and the countable set of jump
times; `L` is continuous so has no atoms). Negative `s` are harmless: `X_0 = I_0 = 0`. -/
theorem ae_localTimeStieltjes_measure_ne_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (localTimeStieltjes f).measure {s : ℝ | f.1 s.toNNReal ≠ runningInfLoc f s.toNNReal} = 0 :=
  sorry

/-- The `ℝ≥0`-valued left limit `T_{x-} = sup_{y<x} T_y` of the passage process, with `T_{0-} = 0`;
junk `0` where some `T_y = ⊤` (null set). -/
noncomputable def passageTimeMinus (x : ℝ≥0) (f : DLoc) : ℝ≥0 :=
  (⨆ y : Set.Iio x, firstPassageBelow y f).untopD 0

/-- `L_t` as a level in `ℝ≥0` (`L_t ≥ 0` almost surely). -/
noncomputable def localTimeNN (f : DLoc) (t : ℝ≥0) : ℝ≥0 := (localTime f t).toNNReal

/-- `passageTimeMinus x` is measurable in the path. -/
theorem measurable_passageTimeMinus (x : ℝ≥0) : Measurable (passageTimeMinus x) := sorry

/-- Joint measurability of `(x, f) ↦ T_{x-}(f)`. -/
theorem measurable_passageTimeMinus_uncurry :
    Measurable (fun p : ℝ≥0 × DLoc => passageTimeMinus p.1 p.2) := sorry

/-- **Straddling.** Almost surely for all `t`: `T_{L_t -} ≤ t ≤ T_{L_t}`. -/
theorem ae_passageTimeMinus_le_le_firstPassageBelow {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      passageTimeMinus (localTimeNN f t) f ≤ t ∧
        (t : WithTop ℝ≥0) ≤ firstPassageBelow (localTimeNN f t) f := sorry

/-- **Generalized inverse identities.** Almost surely for all `x ≥ 0`:
`L (T_x) = x` and `L (T_{x-}) = x`. -/
theorem ae_localTime_passageTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x : ℝ≥0,
      localTime f (passageTime x f) = x ∧ localTime f (passageTimeMinus x f) = x := sorry

/-! ### Strong Markov at `T_x` and independent stationary increments -/

/-- **Additivity from creeping** (deterministic given N08's spec): a.s., for all `x y ≥ 0`,
`T_{x+y}(f) = T_x(f) + T_y(shiftAt T_x f)`. -/
theorem ae_firstPassageBelow_add {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x y : ℝ≥0,
      firstPassageBelow (x + y) f =
        firstPassageBelow x f + firstPassageBelow y (DLoc.shiftAt (firstPassageBelow x) f) := sorry

/-- **Reflected process after `T_x`** (CT7 handoff, AUDIT item 8): on the creeping event,
`X_{T_x + t} - I_{T_x + t} = X'_t - I'_t` for the centered shift `X' = shiftAt T_x`. -/
theorem ae_reflected_shiftAt_passage {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ (x : ℝ≥0) (t : ℝ≥0),
      f.1 (passageTime x f + t) - runningInfLoc f (passageTime x f + t) =
        (DLoc.shiftAt (firstPassageBelow x) f).1 t -
          runningInfLoc (DLoc.shiftAt (firstPassageBelow x) f) t := sorry

/-- **Fresh increment: independence of `F_{T_x}` and law.** For `x, y ≥ 0`, any event `A` of the
stopped σ-algebra `F_{T_x}` and Borel `S ⊆ ℝ`:
`P(A ∩ {T_{x+y} - T_x ∈ S}) = P(A) · P(T_y ∈ S)`. -/
theorem measure_inter_passageIncrement {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x y : ℝ≥0)
    {A : Set DLoc} (hA : MeasurableSet[(isStoppingTime_firstPassageBelow x).measurableSpace] A)
    {S : Set ℝ} (hS : MeasurableSet S) :
    (stableLocalLaw θ : Measure DLoc)
        (A ∩ {f | ((passageTime (x + y) f : ℝ≥0) : ℝ) - (passageTime x f : ℝ) ∈ S}) =
      (stableLocalLaw θ : Measure DLoc) A * passageLaw θ y S := sorry

/-- **Stationary increments.** `T_{x+y} - T_x` has the law of `T_y`. -/
theorem map_passageIncrement {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x y : ℝ≥0) :
    Measure.map (fun f : DLoc => ((passageTime (x + y) f : ℝ≥0) : ℝ) - (passageTime x f : ℝ))
        (stableLocalLaw θ : Measure DLoc) = passageLaw θ y := sorry

/-- **Independent increments** over a strictly increasing level grid (blueprint
`firstPassage_map_increments`). -/
theorem firstPassage_map_increments {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (k : ℕ)
    (x : Fin (k + 1) → ℝ≥0) (hx : StrictMono x) :
    Measure.map (fun f : DLoc => fun i : Fin k =>
        ((passageTime (x i.succ) f : ℝ≥0) : ℝ) - (passageTime (x i.castSucc) f : ℝ))
        (stableLocalLaw θ : Measure DLoc) =
      Measure.pi (fun i : Fin k => passageLaw θ (x i.succ - x i.castSucc)) := sorry

/-! ### One-dimensional law: Laplace transform, positivity, scaling -/

/-- **Laplace transform** (N08 transferred to the law): `∫ e^{-q t} d passageLaw θ x = e^{-x q^{1/θ}}`
for `x ≥ 0`, `q ≥ 0` (blueprint `laplace_firstPassage`; `λ` renamed `q`). -/
theorem integral_exp_neg_passageLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0) {q : ℝ} (hq : 0 ≤ q) :
    ∫ t, Real.exp (-q * t) ∂passageLaw θ x = Real.exp (-(x : ℝ) * q ^ (1 / θ)) := sorry

/-- For `x > 0` the law of `T_x` lives on `(0, ∞)`. -/
theorem passageLaw_Iic_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {x : ℝ≥0} (hx : 0 < x) :
    passageLaw θ x (Iic 0) = 0 := sorry

/-- **Scaling.** `T_{c x} =d c^θ T_x`, for `c > 0`. -/
theorem passageLaw_scaling {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0) {c : ℝ≥0} (hc : 0 < c) :
    passageLaw θ (c * x) = (passageLaw θ x).map (fun t : ℝ => (c : ℝ) ^ θ * t) := sorry

/-- **Identification of the law by its Laplace transform**: any probability law on `ℝ` with the
transform `e^{-x q^{1/θ}}` is `passageLaw θ x` (the positive `(1/θ)`-stable law). -/
theorem eq_passageLaw_of_integral_exp_neg {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ] (h0 : ρ (Iio 0) = 0)
    (hρ : ∀ q : ℝ, 0 < q → ∫ t, Real.exp (-q * t) ∂ρ = Real.exp (-(x : ℝ) * q ^ (1 / θ))) :
    ρ = passageLaw θ x := sorry

end BGW.StableTrees
