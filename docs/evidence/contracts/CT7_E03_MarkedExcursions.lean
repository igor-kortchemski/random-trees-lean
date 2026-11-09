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
import BGW.Probability.PoissonCharacterizationBasic

/-! Contract probe for CT7 node E03 (measurable marked excursion point measure of the original
process, C21), following `r3-ct7-blueprint/blueprint.md` E03; the support facts are those of
`CT7_E02b_ExcursionSupport.lean`, now the sealed module `BGW.StableTrees.StableExcursionSupport`
(which defines `passageJumpSet`, imported here).

DEFINITION.  `excursionPointMeasure f = ∑_{x ∈ J f} δ_{(x, excursionCut T_{x-} T_x f)}` with
`J f = passageJumpSet f = {x > 0 | T_{x-} < T_x}`.  TOTAL: if `J f` is not countable (a null set
of paths) the value is the zero measure (junk), never a dummy atom; invalid cuts (also null) are
cut with E01's `junkExcursion`, as `excursionCut` already prescribes.

MEASURABILITY CHOICE (flagged).  Because of the junk conventions the map `f ↦ excursionPointMeasure f`
is only claimed `AEMeasurable` for `stableLocalLaw θ` (equivalently: it has a genuinely `Measurable`
modification `ξ`, as required by the field `measurable` of E04a's `IsTimeSimpleLevy`; the
modification is the rational first-large-jump enumeration of the blueprint).  Box counts are then
AE-measurable.  Everything about laws (stationarity, independence) is stated either with `P.map`
(well-defined for `AEMeasurable` maps) or for an ARBITRARY measurable modification `ξ`, so it can be
fed to E04a verbatim.

STATIONARITY / INDEPENDENCE relative to `F_{T_a}` (not scalar passage increments only):
`excursionPointMeasure_shift` is the deterministic-on-a-good-event identity
`μ(shiftAt T_a f) = (labels > a of μ f, shifted by a)`, then strong Markov at `T_a` (sealed) gives
independence from `F_{T_a}` and equality of laws.  The window objects `windowRestrict`,
`windowShift` and the structure `IsTimeSimpleLevy` are imported from
`BGW.Probability.PoissonCharacterizationBasic`.
Estimate 700-1100 lines. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The excursion attached to the jump level `x`: the E01 cut of `f` on `(T_{x-}, T_x)`. -/
noncomputable def jumpExcursion (x : ℝ≥0) (f : DLoc) : Excursion :=
  excursionCut (passageTimeMinus x f) (passageTime x f) f

open scoped Classical in
/-- **The marked excursion point measure** on `ℝ≥0 × Excursion`:
`∑_{x ∈ J f} δ_{(x, jumpExcursion x f)}` (zero measure when `J f` is not countable). -/
noncomputable def excursionPointMeasure (f : DLoc) : Measure (ℝ≥0 × Excursion) :=
  if (passageJumpSet f).Countable then
    Measure.sum (fun x : passageJumpSet f => Measure.dirac ((x : ℝ≥0), jumpExcursion x f))
  else 0

/-! ### Deterministic counting form -/

/-- **Counting-measure form** (deterministic): when `J f` is countable, the mass of a measurable
set is the number of jump levels whose marked point lies in it. -/
theorem excursionPointMeasure_apply {f : DLoc} (hf : (passageJumpSet f).Countable)
    {s : Set (ℝ≥0 × Excursion)} (hs : MeasurableSet s) :
    excursionPointMeasure f s =
      ((({x ∈ passageJumpSet f | ((x : ℝ≥0), jumpExcursion x f) ∈ s}).encard : ℕ∞) : ℝ≥0∞) :=
  sorry

/-- **Counting measure** (the hypothesis `counting` of E04a): a.s. the point measure is the sum of
unit Dirac masses at the points of a countable set, namely the marked points. -/
theorem ae_excursionPointMeasure_counting {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∃ S : Set (ℝ≥0 × Excursion), S.Countable ∧
      excursionPointMeasure f = Measure.sum (fun p : S => Measure.dirac (p : ℝ≥0 × Excursion)) :=
  sorry

/-! ### Measurability as a random measure -/

/-- **Random-measure measurability**: the map `f ↦ excursionPointMeasure f` is `AEMeasurable`
(into `Measure (ℝ≥0 × Excursion)` with its Giry/evaluation `σ`-algebra). -/
theorem aemeasurable_excursionPointMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    AEMeasurable excursionPointMeasure (stableLocalLaw θ : Measure DLoc) := sorry

/-- **Measurable modification** (what E04a's `measurable` field consumes): there is a measurable
map `ξ : DLoc → Measure (ℝ≥0 × Excursion)` a.s. equal to `excursionPointMeasure`. -/
theorem exists_measurable_modification_excursionPointMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ ξ : DLoc → Measure (ℝ≥0 × Excursion), Measurable ξ ∧
      ξ =ᵐ[(stableLocalLaw θ : Measure DLoc)] excursionPointMeasure := sorry

/-- **Box counts are AE-measurable** (all measurable boxes/sets). -/
theorem aemeasurable_excursionPointMeasure_apply {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {s : Set (ℝ≥0 × Excursion)} (hs : MeasurableSet s) :
    AEMeasurable (fun f => excursionPointMeasure f s) (stableLocalLaw θ : Measure DLoc) := sorry

/-! ### Time-simplicity, atoms, lifetimes, finiteness -/

/-- **No mass at label `0`** (jump levels are positive). -/
theorem excursionPointMeasure_atZero (f : DLoc) :
    excursionPointMeasure f ({0} ×ˢ univ) = 0 := sorry

/-- **Time-simplicity** (the hypothesis `timeSimple` of E04a): a.s. at most one excursion per
label (the labels are distinct points `x`, each carrying a single cut). -/
theorem ae_excursionPointMeasure_timeSimple {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ s : ℝ≥0,
      excursionPointMeasure f ({s} ×ˢ univ) ≤ 1 := sorry

open scoped Classical in
/-- **Atoms**: a.s., the label-`x` slice of a measurable mark set `A` has mass one iff `x` is a jump
level whose excursion lies in `A`, and zero otherwise. -/
theorem ae_excursionPointMeasure_singleton_prod {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ (x : ℝ≥0) (A : Set Excursion),
      MeasurableSet A →
        excursionPointMeasure f ({x} ×ˢ A) =
          if x ∈ passageJumpSet f ∧ jumpExcursion x f ∈ A then 1 else 0 := sorry

/-- **Lifetime identity and cut validity** (a.s., all jump levels at once; uses E02b): the cut of
`(T_{x-}, T_x)` is valid, its tag is the true lifetime `T_x - T_{x-}`, and its path is the
reflected path run from `T_{x-}` and stopped at `T_x`. -/
theorem ae_jumpExcursion_spec {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f,
      cutValid (passageTimeMinus x f) (passageTime x f) f ∧
        (jumpExcursion x f).lifetime = passageTime x f - passageTimeMinus x f ∧
        ∀ t : ℝ≥0, (jumpExcursion x f).path.1 t =
          (reflectedFrom 0 f).1 (min (passageTimeMinus x f + t) (passageTime x f)) := sorry

/-- **Finite counts of long excursions** and the passage-time bound `ε * count ≤ T_K`:
for all `K, ε > 0` simultaneously. -/
theorem ae_finite_excursionCount {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ K ε : ℝ≥0, 0 < K → 0 < ε →
      (ε : ℝ≥0∞) * excursionPointMeasure f (Ioc 0 K ×ˢ {e : Excursion | ε < e.lifetime}) ≤
          (passageTime K f : ℝ≥0∞) ∧
        excursionPointMeasure f (Ioc 0 K ×ˢ {e : Excursion | ε < e.lifetime}) < ⊤ := sorry

/-! ### Shift identity and structure relative to `F_{T_a}` -/

/-- **Shift identity** (deterministic on a good event, simultaneously in all levels `a`): the
excursion point measure of the post-`T_a` centered path is the translate by `a` of the restriction
of `μ f` to labels `> a` (same cuts, since `T_{(x-a)-}(f') = T_{x-}(f) - T_a`). -/
theorem ae_excursionPointMeasure_shift {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ a : ℝ≥0,
      excursionPointMeasure (DLoc.shiftAt (firstPassageBelow a) f) =
        Measure.map (fun p : ℝ≥0 × Excursion => (p.1 - a, p.2))
          ((excursionPointMeasure f).restrict (Ioi a ×ˢ univ)) := sorry

/-- **Past labels are `F_{T_a}`-measurable** (up to a null set): the restriction of `μ` to labels
`≤ a` agrees a.s. with an `F_{T_a}`-measurable random measure (all those excursions end by `T_a`). -/
theorem exists_stopped_measurable_restrict_Iic {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0) :
    ∃ G : DLoc → Measure (ℝ≥0 × Excursion),
      Measurable[(isStoppingTime_firstPassageBelow a).measurableSpace] G ∧
        (fun f => (excursionPointMeasure f).restrict (Iic a ×ˢ univ)) =ᵐ[
          (stableLocalLaw θ : Measure DLoc)] G := sorry

/-- **Law of the future point measure**: the post-`T_a` point measure has the same law as the
whole point measure. -/
theorem map_excursionPointMeasure_shiftAt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0) :
    (stableLocalLaw θ : Measure DLoc).map
        (fun f => excursionPointMeasure (DLoc.shiftAt (firstPassageBelow a) f)) =
      (stableLocalLaw θ : Measure DLoc).map excursionPointMeasure := sorry

/-- **Independence of the future point measure from `F_{T_a}`** (whole-path strong Markov at `T_a`
plus the shift identity; scalar passage-increment independence is not enough). -/
theorem measure_inter_excursionPointMeasure_shiftAt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    {A : Set DLoc} (hA : MeasurableSet[(isStoppingTime_firstPassageBelow a).measurableSpace] A)
    {B : Set (Measure (ℝ≥0 × Excursion))} (hB : MeasurableSet B) :
    (stableLocalLaw θ : Measure DLoc)
        (A ∩ (fun f => excursionPointMeasure (DLoc.shiftAt (firstPassageBelow a) f)) ⁻¹' B) =
      (stableLocalLaw θ : Measure DLoc) A *
        (stableLocalLaw θ : Measure DLoc) (excursionPointMeasure ⁻¹' B) := sorry

/-- **Stationarity of window restrictions** (hypothesis `stationary` of E04a; for the AE-measurable
`μ`, through `P.map`). -/
theorem map_windowShift_excursionPointMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a h : ℝ≥0) :
    (stableLocalLaw θ : Measure DLoc).map
        (fun f => windowShift a (a + h) (excursionPointMeasure f)) =
      (stableLocalLaw θ : Measure DLoc).map
        (fun f => windowShift 0 h (excursionPointMeasure f)) := sorry

/-- **Independence of consecutive window restrictions** (hypothesis `indep` of E04a), for any
measurable modification `ξ` of the point measure (so that the `σ`-algebras involved are honest). -/
theorem iIndepFun_windowRestrict_excursionPointMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ξ : DLoc → Measure (ℝ≥0 × Excursion)} (hξ : Measurable ξ)
    (hae : ξ =ᵐ[(stableLocalLaw θ : Measure DLoc)] excursionPointMeasure)
    (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t) :
    iIndepFun (fun i : Fin n => fun f : DLoc =>
      windowRestrict (t i.castSucc) (t i.succ) (ξ f)) (stableLocalLaw θ : Measure DLoc) := sorry

/-! ### E04a adapter -/

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

/-! ### Support bridges for E05-E06 -/

/-- **Pure-jump passage time**: a.s., simultaneously for all `K`, `T_K` is the sum of the
lifetimes of the excursions at jump levels `x ≤ K` (no drift). -/
theorem ae_passageTime_eq_tsum_lifetime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ K : ℝ≥0,
      passageTime K f =
        ∑' x : {x ∈ passageJumpSet f | x ≤ K}, (jumpExcursion x f).lifetime := sorry

/-- **Marked scaling** (convention `scaleLoc θ c f t = c^{1/θ} f (t/c)`, `excursionScale θ c e t =
c^{1/θ} e (t/c)`): for each `c > 0`, a.s. the point measure of `scaleLoc θ c f` is the image of that
of `f` under `(x, e) ↦ (c^{1/θ} x, S_c e)`.  (Taking `c = 1/c'` gives the path `c'^{-1/θ} X_{c' ·}`
and the map `(c'^{-1/θ} x, S_{1/c'} e)`.) -/
theorem ae_excursionPointMeasure_scaleLoc {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (c : Set.Ioi (0 : ℝ)) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      excursionPointMeasure (scaleLoc θ c f) =
        Measure.map (fun p : ℝ≥0 × Excursion =>
            ((c : ℝ).toNNReal ^ (1 / θ) * p.1, excursionScale θ c p.2))
          (excursionPointMeasure f) := sorry

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

end BGW.StableTrees
