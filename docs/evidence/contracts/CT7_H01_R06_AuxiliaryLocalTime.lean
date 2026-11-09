import BGW.StableTrees.SupremumDrawdown
import BGW.StableTrees.SupremumReflectedFamily
import BGW.StableTrees.SupremumLocalTime
import BGW.Probability.DoobL2Resolvent
import BGW.StableTrees.StableLocalLaw
import Mathlib.MeasureTheory.Measure.Stieltjes
import BGW.StableTrees.SupremumCauchy
import BGW.StableTrees.SupremumPotential

/-! Contract probe for H01 node R06 (blueprint R06; AUDIT items 4, 5; Sol-audit finding 8):
the auxiliary continuous local time `L^aux = M^*` (the limit constructed in R05), its a.s.
recurrence, support in the contact set `{R = 0}`, immediate increase, the right-continuous
inverse `A^*`, the ladder height `B^* = S_{A^*}`, and the CONDITIONAL POTENTIAL of the reflected
family for the constructed clock (`E[∫_{(s,∞)} e^{-qt} dM^*_t | F_s] = e^{-qs} h_q(R_s)`), which
R10 needs.  Depends on R05 (and R04 for `supPotential`).
NOT redefined: `supRunning`, `supReflected`, `supOccupation` (W49), `supReflectedFrom`,
`supContact`, `mem_supContact_iff` (R01, sealed).  Suppliers consumed by the PROOFS: R05
(`ae_supAuxLimit_spec`, full-filter `L²` convergence), R04 (`supOccupationResolvent`,
`supOccupationResolvent_eq`, `tendstoUniformlyOn_supOccupationResolvent`,
`condExp_reflectedResolvent_tail`, `supPotential`), R01 (contact-set closedness, restart),
sealed `ST.stableProcessLaw_scaling`, `DLoc.measure_ext_of_restrict`,
`ST.measure_zeroOne_filtration_zero`, `StieltjesFunction.measure`.

Proof plan reminders (not statements).  Support: an interval separated from the closed contact
set has zero limiting occupation `O_ε` (for ε below the separation), countable cover.  Immediate
increase and recurrence: scaling `M^*_{ct} =d c^β M^*_t` (`β = 1-1/θ`; lifted from the sealed
finite-horizon scaling by restriction-law uniqueness; the scaling statement is a PROOF HELPER and
is deliberately not stated here: it needs a `DLoc` dilation map that the contract does not
introduce), `P(M^*_t = 0)` independent of `t>0`, the germ zero-one law, and non-triviality
`E ∫ e^{-t} dM^* = h_1(0) = 1` (`integral_supAuxDiscountedTail_zero` at `q = 1`).  Conditional
potential: the compact-convergence/uniform-in-start R05+R04 bridge (AUDIT item 4), the
positive-rate resolvent identity of R04, then discount tail control with rate `q/2`.

FLAGS. (1) The blueprint's `Mstar` is `supAuxLimit` (R05); `supAuxLocalTime` below is just its
public alias.  (2) `∫ e^{-qt} dM^*_t` is stated with the Stieltjes measure of `s ↦ M^*_{s⁺}`
(`pathStieltjes`, junk zero off the good event, the same dite pattern as H01's
`supLocalTimeStieltjes`); no integration-by-parts surrogate is used.  (3) The inverse `A^*` is
the raw `sInf` of the H01 contract.  Since `supAuxLimit` is a real limsup it is only a.s.
monotone, so everywhere-measurability of `A^*` is NOT claimed here (it is R07's
extended-limsup totalization); here: `AEMeasurable` for each fixed level, and the pathwise a.s.
inverse spec for ALL levels simultaneously.  (4) Contact is stated as `supContact f`
(`supReflected f t = 0`), i.e. `X = S`, matching `{R = 0}`.  (5) The conditional potential is
for the clock started at `0` evaluated at the random reflected state `R^0_s`; AUDIT item 4 allows
this form ("or at random reflected states").  (6) Estimate 800-1400 lines. -/

/- R06 defines the ENNReal occupation-limsup germ helper locally, using R05.  Its monotonicity and
prefix measurability precede the zero-one argument.  No R07 identification, inverse-measurability,
or stopping-time theorem is used to prove recurrence or immediate positivity here.  R07 later
reuses or reconstructs this helper for the public sequence.  The mean discounted potential is
proved from R04/R05 before it is used to exclude the zero clock. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

open scoped Classical in
/-! ### Definitions -/

/-- The auxiliary continuous local time `L^aux = M^*` (public name of R05's `supAuxLimit`). -/
noncomputable def supAuxLocalTime (θ : ℝ) (f : DLoc) (t : ℝ≥0) : ℝ := supAuxLimit θ f t

open scoped Classical in
/-- The Stieltjes function `s ↦ m(s⁺)` of a path `m`; junk zero unless `m` is monotone and
continuous (same pattern as H01's `supLocalTimeStieltjes`). -/
noncomputable def pathStieltjes (m : ℝ≥0 → ℝ) : StieltjesFunction ℝ :=
  if h : Monotone m ∧ Continuous m then
    { toFun := fun s => m s.toNNReal
      mono' := h.1.comp (fun _ _ hab => Real.toNNReal_mono hab)
      right_continuous' := fun _ =>
        ((h.2.comp continuous_real_toNNReal).continuousAt).continuousWithinAt }
  else
    { toFun := fun _ => 0
      mono' := monotone_const
      right_continuous' := fun _ => continuousWithinAt_const }

/-- Stieltjes function of the auxiliary local time. -/
noncomputable def supAuxStieltjes (θ : ℝ) (f : DLoc) : StieltjesFunction ℝ :=
  pathStieltjes (supAuxLocalTime θ f)

/-- Discounted future clock `∫_{(s,∞)} e^{-qt} dL^aux_t`. -/
noncomputable def supAuxDiscountedTail (θ q : ℝ) (s : ℝ≥0) (f : DLoc) : ℝ :=
  ∫ t in Ioi (s : ℝ), Real.exp (-q * t) ∂(supAuxStieltjes θ f).measure

/-- Inverse `A^*_z = inf{t | L^aux_t > z}` (raw, as in H01). -/
noncomputable def supAuxInverse (θ : ℝ) (f : DLoc) (z : ℝ≥0) : WithTop ℝ≥0 :=
  sInf {t : WithTop ℝ≥0 | ∃ u : ℝ≥0, t = u ∧ (z : ℝ) < supAuxLocalTime θ f u}

/-- `A^*_z` (finite reading, junk `0` on `⊤`). -/
noncomputable def supAuxLadderTime (θ : ℝ) (z : ℝ≥0) (f : DLoc) : ℝ≥0 :=
  (supAuxInverse θ f z).untopD 0

/-- `B^*_z = S_{A^*_z}`. -/
noncomputable def supAuxLadderHeight (θ : ℝ) (z : ℝ≥0) (f : DLoc) : ℝ :=
  supRunning f (supAuxLadderTime θ z f)

/-! ### Pathwise structure of `L^aux` -/

/-- **Recurrence**: `L^aux_0 = 0`, monotone, continuous, `L^aux_t → ∞` (almost surely). -/
theorem ae_supAuxLocalTime_spec {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      supAuxLocalTime θ f 0 = 0 ∧ Monotone (supAuxLocalTime θ f) ∧
        Continuous (supAuxLocalTime θ f) ∧ Tendsto (supAuxLocalTime θ f) atTop atTop := sorry

/-- **Immediate increase**: `L^aux_t > 0` for every `t > 0`, almost surely. -/
theorem ae_supAuxLocalTime_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0, 0 < t → 0 < supAuxLocalTime θ f t :=
  sorry

/-- **Support in the contact set** `{R = 0}`: `dL^aux` charges no time outside it. -/
theorem ae_supAuxStieltjes_support {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (supAuxStieltjes θ f).measure {s : ℝ | 0 ≤ s ∧ s.toNNReal ∉ supContact f} = 0 := sorry

/-- **Increase only on the contact set**: constant on any `[s,t]` strictly below the running
supremum (also in left limits), for all `s < t` simultaneously. -/
theorem ae_supAuxLocalTime_const_of_lt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ s t : ℝ≥0, s < t →
      (∀ u ∈ Icc s t, f.1 u < supRunning f u ∧ Function.leftLim f.1 u < supRunning f u) →
        supAuxLocalTime θ f t = supAuxLocalTime θ f s := sorry

/-! ### Conditional potential of the constructed clock (for R10) -/

theorem integrable_supAuxDiscountedTail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q)
    (s : ℝ≥0) : Integrable (supAuxDiscountedTail θ q s) (stableLocalLaw θ : Measure DLoc) := sorry

/-- Almost-everywhere measurability of the discounted tail (everywhere measurability of the
Stieltjes totalization of a raw `limsup` clock is not needed downstream; exact measurability, if
required later, comes from the totalized clock of the identification step). -/
theorem aemeasurable_supAuxDiscountedTail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q)
    (s : ℝ≥0) : AEMeasurable (supAuxDiscountedTail θ q s) (stableLocalLaw θ : Measure DLoc) :=
  sorry

/-- **Mean potential** `E ∫_0^∞ e^{-qt} dL^aux_t = h_q(0) = Φ/q` (`= 1` at `q = 1`: the clock is
non-trivial; the normalization `c = 1`). -/
theorem integral_supAuxDiscountedTail_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    ∫ f, supAuxDiscountedTail θ q 0 f ∂(stableLocalLaw θ : Measure DLoc) =
      supPotential θ q 0 := sorry

/-- **Conditional potential of the reflected family**: for every `q > 0` and `s`,
`E[∫_{(s,∞)} e^{-qt} dL^aux_t | F_s] = e^{-qs} h_q(R^0_s)`. -/
theorem condExp_supAuxDiscountedTail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q)
    (s : ℝ≥0) :
    (stableLocalLaw θ : Measure DLoc)[supAuxDiscountedTail θ q s | DLoc.filtration s]
      =ᵐ[(stableLocalLaw θ : Measure DLoc)]
      fun f => Real.exp (-q * (s : ℝ)) * supPotential θ q (supReflectedFrom 0 f s) := sorry

/-! ### Inverse clock -/

/-- The inverse at each fixed level is a.e.-measurable (everywhere measurability of the
totalized inverse is R07). -/
theorem aemeasurable_supAuxLadder {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    AEMeasurable (supAuxLadderTime θ z) (stableLocalLaw θ : Measure DLoc) ∧
      AEMeasurable (supAuxLadderHeight θ z) (stableLocalLaw θ : Measure DLoc) := sorry

/-- **Inverse geometry, simultaneously for all levels `z`**: `A^*` is finite and agrees with
`supAuxInverse`, `A^*_0 = 0`, monotone, right continuous, unbounded; `B^*` monotone;
`L^aux(A^*_z) = z`; and `R_{A^*_z} = 0` (`A^*_z ∈ {S = X}`, so `B^*_z = X_{A^*_z}`). -/
theorem ae_supAuxLadder_spec {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (∀ z : ℝ≥0, supAuxInverse θ f z = (supAuxLadderTime θ z f : WithTop ℝ≥0)) ∧
        supAuxLadderTime θ 0 f = 0 ∧ Monotone (fun z => supAuxLadderTime θ z f) ∧
        (∀ z, ContinuousWithinAt (fun z => supAuxLadderTime θ z f) (Ici z) z) ∧
        Tendsto (fun z => supAuxLadderTime θ z f) atTop atTop ∧
        Monotone (fun z => supAuxLadderHeight θ z f) ∧
        (∀ z : ℝ≥0, supAuxLocalTime θ f (supAuxLadderTime θ z f) = z) ∧
        (∀ z : ℝ≥0, supAuxLadderTime θ z f ∈ supContact f) ∧
        ∀ z : ℝ≥0, supAuxLadderHeight θ z f = f.1 (supAuxLadderTime θ z f) := sorry

/-- Bundled blueprint interface `exists_auxSupLocalTime`: the raw process `supAuxLocalTime` is
jointly measurable, adapted, a.s. `0`-started monotone continuous unbounded, and is the full
filter compact-time `L²` limit of the occupations. -/
theorem exists_auxSupLocalTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ Mstar : DLoc → ℝ≥0 → ℝ,
      Measurable (fun p : ℝ≥0 × DLoc => Mstar p.2 p.1) ∧
      StronglyAdapted DLoc.filtration (fun t f => Mstar f t) ∧
      (∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), Mstar f 0 = 0 ∧ Monotone (Mstar f) ∧
        Continuous (Mstar f) ∧ Tendsto (Mstar f) atTop atTop) ∧
      (∀ T : ℝ≥0, Tendsto (fun ε : ℝ =>
        ∫ f, (⨆ t : Set.Iic T, |supOccupation ε f t - Mstar f t|) ^ 2
          ∂(stableLocalLaw θ : Measure DLoc)) (𝓝[>] (0 : ℝ)) (𝓝 0)) := sorry

end BGW.StableTrees
