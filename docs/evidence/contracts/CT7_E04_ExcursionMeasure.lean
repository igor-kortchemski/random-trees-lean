import BGW.Skorokhod.DLocShiftAt
import BGW.StableTrees.ReflectedRestart
import BGW.StableTrees.StablePassageSubordinator
import BGW.StableTrees.StablePassageSubordinatorStieltjes
import BGW.StableTrees.StablePassageSubordinatorIncrements
import BGW.StableTrees.StableContinuousMinimum
import BGW.StableTrees.StableStrongMarkov
import BGW.StableTrees.StableRegularity
import BGW.StableTrees.StableLocalLaw
import BGW.StableTrees.StableExcursionSupport
import BGW.ContinuumTrees.ExcursionCarrier
import BGW.Probability.PoissonCharacterization

/-! Contract probe for CT7 node E04 (Poisson excursion theorem, intensity `N`, compensation,
support), following `r3-ct7-blueprint/blueprint.md` E04 and `AUDIT.md` item 4.

DEFINITION (flagged).  `excursionMeasure θ` is defined with no choice of modification and no
`sorry`: it is `Measure.join` of the law of the random measure
`f ↦ (μ f ↾ (0,1] × univ).map Prod.snd` under `P = stableLocalLaw θ`.  `Measure.join` evaluates a
measurable set `A` as `∫⁻ ρ, ρ A ∂(P.map ν)`, so `excursionMeasure_apply` states
`N A = ∫⁻ f, μ f ((0,1] × A) ∂P` (the junk value `0` of `P.map` for a non-AE-measurable map is
excluded by E03's `aemeasurable_excursionPointMeasure`).

NOT claimed: continuity of the *reflected path before* `T_{x-}` is a property of the point
measure (E03 `ae_jumpExcursion_support`), not of the `Excursion` mark, so it is not transferred to
`N`; the transferred support facts are positivity on `(0,ζ)`, tag = `sup {e > 0}`, `e 0 = 0`,
right-continuity at `0` (automatic from càdlàg), left limit `0` at `ζ`.

COMPENSATION (flagged).  Relative to `G_a = F_{T_a}` = `(isStoppingTime_firstPassageBelow a).measurableSpace`.
`excursion_compensation_step`: `Y` `G_a`-measurable, window `(a,b]`.
`excursion_compensation_predictable`: `H x ·` is `G_x`-measurable and `x ↦ H x f` is left-continuous
on `(0,∞)` (hence predictable); it is the blueprint's `G`-predictable version.  Right-hand side is
`E ∫_0^K H dx · ∫ G dN` (the outer expectation of the time integral, times the mark integral),
all in `ℝ≥0∞` (`0 * ∞ = 0`).
Estimate 1200-2200 lines. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

-- copied from contract CT7_E03_MarkedExcursions (not part of this contract)
/-- The excursion attached to the jump level `x`: the E01 cut of `f` on `(T_{x-}, T_x)`. -/
noncomputable def jumpExcursion (x : ℝ≥0) (f : DLoc) : Excursion :=
  excursionCut (passageTimeMinus x f) (passageTime x f) f

-- copied from contract CT7_E03_MarkedExcursions (not part of this contract)
open scoped Classical in
/-- **The marked excursion point measure** on `ℝ≥0 × Excursion`:
`∑_{x ∈ J f} δ_{(x, jumpExcursion x f)}` (zero measure when `J f` is not countable). -/
noncomputable def excursionPointMeasure (f : DLoc) : Measure (ℝ≥0 × Excursion) :=
  if (passageJumpSet f).Countable then
    Measure.sum (fun x : passageJumpSet f => Measure.dirac ((x : ℝ≥0), jumpExcursion x f))
  else 0

-- copied from contract CT7_E03_MarkedExcursions (not part of this contract)
/-- **Random-measure measurability**: the map `f ↦ excursionPointMeasure f` is `AEMeasurable`
(into `Measure (ℝ≥0 × Excursion)` with its Giry/evaluation `σ`-algebra). -/
theorem aemeasurable_excursionPointMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    AEMeasurable excursionPointMeasure (stableLocalLaw θ : Measure DLoc) := sorry

-- copied from contract CT7_E03_MarkedExcursions (not part of this contract)
/-- **Measurable modification** (what E04a's `measurable` field consumes): there is a measurable
map `ξ : DLoc → Measure (ℝ≥0 × Excursion)` a.s. equal to `excursionPointMeasure`. -/
theorem exists_measurable_modification_excursionPointMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ ξ : DLoc → Measure (ℝ≥0 × Excursion), Measurable ξ ∧
      ξ =ᵐ[(stableLocalLaw θ : Measure DLoc)] excursionPointMeasure := sorry

-- copied from contract CT7_E03_MarkedExcursions (not part of this contract)
/-- **E04a adapter**: every measurable modification of the excursion point measure is a
time-simple Lévy point measure, and every `{ε < lifetime}` has finite rate. -/
theorem isTimeSimpleLevy_of_ae_eq_excursionPointMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ξ : DLoc → Measure (ℝ≥0 × Excursion)} (hξ : Measurable ξ)
    (hae : ξ =ᵐ[(stableLocalLaw θ : Measure DLoc)] excursionPointMeasure) :
    IsTimeSimpleLevy (stableLocalLaw θ : Measure DLoc) ξ ∧
      ∀ ε : ℝ≥0, 0 < ε →
        MeasurableSet {e : Excursion | ε < e.lifetime} ∧
        IsFiniteRate (stableLocalLaw θ : Measure DLoc) ξ {e : Excursion | ε < e.lifetime} :=
  sorry

-- copied from contract CT7_E03_MarkedExcursions (not part of this contract)
/-- **Independence of the future point measure from `F_{T_a}`** (whole-path strong Markov at `T_a`
plus the shift identity; scalar passage-increment independence is not enough). -/
theorem measure_inter_excursionPointMeasure_shiftAt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    {A : Set DLoc} (hA : MeasurableSet[(isStoppingTime_firstPassageBelow a).measurableSpace] A)
    {B : Set (Measure (ℝ≥0 × Excursion))} (hB : MeasurableSet B) :
    (stableLocalLaw θ : Measure DLoc)
        (A ∩ (fun f => excursionPointMeasure (DLoc.shiftAt (firstPassageBelow a) f)) ⁻¹' B) =
      (stableLocalLaw θ : Measure DLoc) A *
        (stableLocalLaw θ : Measure DLoc) (excursionPointMeasure ⁻¹' B) := sorry

-- copied from contract CT7_E03_MarkedExcursions (not part of this contract)
/-- **Law of the future point measure**: the post-`T_a` point measure has the same law as the
whole point measure. -/
theorem map_excursionPointMeasure_shiftAt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0) :
    (stableLocalLaw θ : Measure DLoc).map
        (fun f => excursionPointMeasure (DLoc.shiftAt (firstPassageBelow a) f)) =
      (stableLocalLaw θ : Measure DLoc).map excursionPointMeasure := sorry

-- copied from contract CT7_E03_MarkedExcursions (not part of this contract)
/-- **Support properties of the excursions**: a.s., for every jump level `x`, the excursion is
positive on `(0, ζ)`, its tag is the actual lifetime `sup {t | 0 < e t}`, it starts at `0` with the
reflected path continuous at `T_{x-}` (no jump start), and its left limit at `ζ` is `0`. -/
theorem ae_jumpExcursion_support {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f,
      (∀ t : ℝ≥0, 0 < t → t < (jumpExcursion x f).lifetime → 0 < (jumpExcursion x f).path.1 t) ∧
        (jumpExcursion x f).lifetime = sSup {t : ℝ≥0 | 0 < (jumpExcursion x f).path.1 t} ∧
        (jumpExcursion x f).path.1 0 = 0 ∧
        ContinuousAt (reflectedFrom 0 f).1 (passageTimeMinus x f) ∧
        Tendsto (jumpExcursion x f).path.1 (𝓝[<] (jumpExcursion x f).lifetime) (𝓝 0) := sorry

/-! ### The excursion measure `N` -/

/-- **The excursion measure** `N A = ∫⁻ f, μ f ((0,1] × A) ∂P`, `P = stableLocalLaw θ`, as the
`Measure.join` of the law of `f ↦ ((μ f) ↾ (0,1] × univ).map Prod.snd`. -/
noncomputable def excursionMeasure (θ : ℝ) : Measure Excursion :=
  Measure.join ((stableLocalLaw θ : Measure DLoc).map
    (fun f => ((excursionPointMeasure f).restrict (Ioc 0 1 ×ˢ univ)).map Prod.snd))

/-- **Defining formula**: `N A = ∫⁻ f, μ f ((0,1] × A) ∂P`. -/
theorem excursionMeasure_apply {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {A : Set Excursion}
    (hA : MeasurableSet A) :
    excursionMeasure θ A =
      ∫⁻ f, excursionPointMeasure f (Ioc 0 1 ×ˢ A) ∂(stableLocalLaw θ : Measure DLoc) := sorry

/-- **Independence of the modification**: for every measurable modification `ξ`,
`N A = ∫⁻ ξ ((0,1] × A) ∂P`, which is E04a's `markRate`. -/
theorem excursionMeasure_apply_of_ae_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ξ : DLoc → Measure (ℝ≥0 × Excursion)} (hξ : Measurable ξ)
    (hae : ξ =ᵐ[(stableLocalLaw θ : Measure DLoc)] excursionPointMeasure)
    {A : Set Excursion} (hA : MeasurableSet A) :
    excursionMeasure θ A =
        ∫⁻ f, ξ f (Ioc 0 1 ×ˢ A) ∂(stableLocalLaw θ : Measure DLoc) ∧
      excursionMeasure θ A = markRate (stableLocalLaw θ : Measure DLoc) ξ A := sorry

/-- **Finite lifetime slabs**: `N {ε < ζ} < ∞` for every `ε > 0`. -/
theorem excursionMeasure_lifetime_slab_lt_top {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ≥0}
    (hε : 0 < ε) : excursionMeasure θ {e : Excursion | ε < e.lifetime} < ⊤ := sorry

/-- **σ-finiteness** of `N` (exhaustion by `{1/(n+1) < ζ}`; every lifetime is positive). -/
theorem sigmaFinite_excursionMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    SigmaFinite (excursionMeasure θ) := sorry

/-! ### The Poisson theorem -/

/-- Lebesgue measure on `ℝ≥0` (flagged: Mathlib has no `MeasureSpace ℝ≥0`; this is the pullback of
`volume` on `ℝ` under the coercion, so `lebNN (Ioc a b) = b - a`). -/
noncomputable def lebNN : Measure ℝ≥0 := Measure.comap ((↑) : ℝ≥0 → ℝ) volume

/-- Lebesgue measure of an interval. -/
theorem lebNN_Ioc (a b : ℝ≥0) : lebNN (Ioc a b) = ((b - a : ℝ≥0) : ℝ≥0∞) := sorry

/-- **Mean measure of windows**: for a measurable modification `ξ`, `a ≤ b` and measurable `A`
(finite or infinite rate), `E ξ((a,b] × A) = (b - a) N(A)`. -/
theorem lintegral_windowMark_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ξ : DLoc → Measure (ℝ≥0 × Excursion)} (hξ : Measurable ξ)
    (hae : ξ =ᵐ[(stableLocalLaw θ : Measure DLoc)] excursionPointMeasure)
    {a b : ℝ≥0} (hab : a ≤ b) {A : Set Excursion} (hA : MeasurableSet A) :
    ∫⁻ f, ξ f (Ioc a b ×ˢ A) ∂(stableLocalLaw θ : Measure DLoc) =
      ((b - a : ℝ≥0) : ℝ≥0∞) * excursionMeasure θ A := sorry

/-- **Intensity measure** is `Leb ⊗ N`: `E ξ(B) = (lebNN.prod N)(B)` for measurable `B`. -/
theorem lintegral_pointMeasure_eq_prod {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ξ : DLoc → Measure (ℝ≥0 × Excursion)} (hξ : Measurable ξ)
    (hae : ξ =ᵐ[(stableLocalLaw θ : Measure DLoc)] excursionPointMeasure)
    {B : Set (ℝ≥0 × Excursion)} (hB : MeasurableSet B) :
    ∫⁻ f, ξ f B ∂(stableLocalLaw θ : Measure DLoc) =
      (lebNN.prod (excursionMeasure θ)) B := sorry

/-- **Poisson theorem** (counts): for every measurable modification `ξ`, counts of boxes
`(s i, t i] × A i` with `N (A i) < ∞` and pairwise disjoint boxes are independent Poisson with means
`(t i - s i) * N (A i)`. -/
theorem excursionCounts_poisson_independent {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ξ : DLoc → Measure (ℝ≥0 × Excursion)} (hξ : Measurable ξ)
    (hae : ξ =ᵐ[(stableLocalLaw θ : Measure DLoc)] excursionPointMeasure)
    {k : ℕ} (A : Fin k → Set Excursion) (hA : ∀ i, MeasurableSet (A i))
    (hfin : ∀ i, excursionMeasure θ (A i) < ⊤) (s t : Fin k → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (hdisj : Pairwise (Function.onFun Disjoint fun i => Ioc (s i) (t i) ×ˢ A i)) :
    (stableLocalLaw θ : Measure DLoc).map
        (fun f i => natCount (ξ f) (Ioc (s i) (t i) ×ˢ A i)) =
      Measure.pi (fun i => poissonMeasure ((t i - s i) * (excursionMeasure θ (A i)).toNNReal)) :=
  sorry

/-- The same law for the unmodified `excursionPointMeasure` (the map is a.e. equal to the one of
`ξ`, so no measurable modification needs to be named). -/
theorem excursionCounts_poisson_independent_pointMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {k : ℕ} (A : Fin k → Set Excursion) (hA : ∀ i, MeasurableSet (A i))
    (hfin : ∀ i, excursionMeasure θ (A i) < ⊤) (s t : Fin k → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (hdisj : Pairwise (Function.onFun Disjoint fun i => Ioc (s i) (t i) ×ˢ A i)) :
    (stableLocalLaw θ : Measure DLoc).map
        (fun f i => natCount (excursionPointMeasure f) (Ioc (s i) (t i) ×ˢ A i)) =
      Measure.pi (fun i => poissonMeasure ((t i - s i) * (excursionMeasure θ (A i)).toNNReal)) :=
  sorry

/-- `exp (-x)` on `ℝ≥0∞`, with `exp (-∞) = 0`. -/
noncomputable def expNeg (x : ℝ≥0∞) : ℝ≥0∞ :=
  if x = ⊤ then 0 else ENNReal.ofReal (Real.exp (-x.toReal))

/-- **Laplace functional** of the point measure, for every measurable `ℝ≥0∞`-valued test `g`
(Campbell formula; `exp (-∞) = 0` on both sides):
`E exp (-∫ g dξ) = exp (-∫ (1 - exp (-g)) d(Leb ⊗ N))`. -/
theorem excursion_laplaceFunctional {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ξ : DLoc → Measure (ℝ≥0 × Excursion)} (hξ : Measurable ξ)
    (hae : ξ =ᵐ[(stableLocalLaw θ : Measure DLoc)] excursionPointMeasure)
    {g : ℝ≥0 × Excursion → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ f, expNeg (∫⁻ p, g p ∂ξ f) ∂(stableLocalLaw θ : Measure DLoc) =
      expNeg (∫⁻ p, 1 - expNeg (g p) ∂(lebNN.prod (excursionMeasure θ))) :=
  sorry

/-! ### Compensation relative to `F_{T_a}` -/

/-- **Step compensation** relative to `F_{T_a}`: for `Y` measurable in the stopped σ-algebra of
`T_a` (not merely the natural history of the point measure), `a ≤ b`, measurable `A`:
`E[Y · μ((a,b] × A)] = E[Y] (b - a) N(A)`. -/
theorem excursion_compensation_step {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {a b : ℝ≥0} (hab : a ≤ b)
    {A : Set Excursion} (hA : MeasurableSet A) {Y : DLoc → ℝ≥0∞}
    (hY : Measurable[(isStoppingTime_firstPassageBelow a).measurableSpace] Y) :
    ∫⁻ f, Y f * excursionPointMeasure f (Ioc a b ×ˢ A) ∂(stableLocalLaw θ : Measure DLoc) =
      (∫⁻ f, Y f ∂(stableLocalLaw θ : Measure DLoc)) *
        (((b - a : ℝ≥0) : ℝ≥0∞) * excursionMeasure θ A) := sorry

/-- **Predictable compensation formula**: `H x ·` is `F_{T_x}`-measurable and `x ↦ H x f` is
left-continuous on `(0,∞)` (a left-continuous adapted, hence predictable, integrand), `G ≥ 0`
measurable on excursions, `K ≥ 0`:
`E ∑_{x ∈ J, x ≤ K} H(x,f) G(e_x) = E[∫_0^K H(x,f) dx] · ∫ G dN`. -/
theorem excursion_compensation_predictable {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (K : ℝ≥0)
    {H : ℝ≥0 → DLoc → ℝ≥0∞}
    (hadapted : ∀ x, Measurable[(isStoppingTime_firstPassageBelow x).measurableSpace] (H x))
    (hleft : ∀ f x, 0 < x → ContinuousWithinAt (fun y => H y f) (Iio x) x)
    {G : Excursion → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ f, ∫⁻ p in Ioc 0 K ×ˢ univ, H p.1 f * G p.2 ∂(excursionPointMeasure f)
        ∂(stableLocalLaw θ : Measure DLoc) =
      (∫⁻ f, ∫⁻ x in Ioc 0 K, H x f ∂lebNN
          ∂(stableLocalLaw θ : Measure DLoc)) *
        ∫⁻ e, G e ∂(excursionMeasure θ) := sorry

set_option warn.classDefReducibility false in
/-- **The predictable `σ`-algebra** on `ℝ≥0 × DLoc` of the filtration `G_x = F_{T_x}`
(`(isStoppingTime_firstPassageBelow x).measurableSpace`): generated by the rectangles
`(a,b] × F` with `a ≤ b`, `F ∈ G_a`, and `{0} × F` with `F ∈ G_0`.  (Not packaged as a Mathlib
`Filtration`, to avoid proving monotonicity/`≤ m` of `G` just for the statement.) -/
def predictableSigma : MeasurableSpace (ℝ≥0 × DLoc) :=
  MeasurableSpace.generateFrom
      {S | ∃ (a b : ℝ≥0) (F : Set DLoc), a ≤ b ∧
        MeasurableSet[(isStoppingTime_firstPassageBelow a).measurableSpace] F ∧
        S = Ioc a b ×ˢ F} ⊔
    MeasurableSpace.generateFrom
      {S | ∃ F : Set DLoc,
        MeasurableSet[(isStoppingTime_firstPassageBelow 0).measurableSpace] F ∧
        S = ({0} : Set ℝ≥0) ×ˢ F}

/-- **General predictable compensation formula.**  For every `H : (ℝ≥0 × DLoc) × Excursion → ℝ≥0∞`
measurable for `predictableSigma ⊗ Borel(Excursion)`, with `μ_f = excursionPointMeasure f`:
`E ∫ H((x,f),e) μ_f(dx,de) = E ∫_0^∞ ∫ H((x,f),e) N(de) dx`.
Proof route: `π`-`λ` argument on the generating rectangles `(a,b] × F × A` using
`excursion_compensation_step` (with `Y = 1_F`), then monotone class; no pointwise approximation
is needed. -/
theorem excursion_compensation_predictable_general {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {H : (ℝ≥0 × DLoc) × Excursion → ℝ≥0∞}
    (hH : @Measurable _ _ (predictableSigma.prod inferInstance) _ H) :
    ∫⁻ f, ∫⁻ p, H ((p.1, f), p.2) ∂(excursionPointMeasure f)
        ∂(stableLocalLaw θ : Measure DLoc) =
      ∫⁻ f, ∫⁻ x, ∫⁻ e, H ((x, f), e) ∂(excursionMeasure θ) ∂lebNN
        ∂(stableLocalLaw θ : Measure DLoc) := sorry

/-! ### Support properties of `N` -/

/-- **Support of `N`**: `N`-a.e. excursion is positive on `(0, ζ)`, its tag is
`sup {t | 0 < e t}`, `e 0 = 0`, `e` is continuous (right-continuous) at `0`, and `e t → 0` as
`t ↑ ζ`. (The carrier only supplies a positive *tag*; this support theorem identifies the tag with the
actual lifetime `sup {t | 0 < e t}`.) -/
theorem ae_excursionMeasure_support {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(excursionMeasure θ),
      (∀ t : ℝ≥0, 0 < t → t < e.lifetime → 0 < e.path.1 t) ∧
        e.lifetime = sSup {t : ℝ≥0 | 0 < e.path.1 t} ∧
        e.path.1 0 = 0 ∧ ContinuousAt e.path.1 0 ∧
        Tendsto e.path.1 (𝓝[<] e.lifetime) (𝓝 0) := sorry

end BGW.StableTrees
