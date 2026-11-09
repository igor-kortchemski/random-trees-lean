import BGW.Skorokhod.DLoc
import BGW.Skorokhod.ReverseIncrements
import BGW.StableTrees.StableLocalLaw
import BGW.StableTrees.StableProcessReversal
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import BGW.StableTrees.SupremumLocalTimePublic

/-! Contract probe for CT7 blueprint node H02 (height approximation and minimal exploration
measure, C26 H1/H3), following `r3-ct7-blueprint/blueprint.md` H02 and AUDIT items 2-3.

DEFINITIONS (no `sorry`).
* `futureInf f t s = inf_{[s ∧ t, t]} X`, the interval infimum `I^s_t`.
* `heightApprox ε f t = ε⁻¹ Leb{s ∈ [0,t] | X_s < I^s_t + ε}` (blueprint formula).
* `reversedPath t f u = X_t - X_{(t - u ∧ t)-}`, the reversed process (junk constant extension
  after `t`); `reversedAt t f : DLoc` is that path (junk `DLoc.zero` if not càdlàg; the theorem
  `isCadlag_reversedPath` shows this never happens).
* `height θ f t = M_t(reversedAt t f)`: the H01 supremum local time of the reversed process at
  time `t` (REAL valued; finiteness is built into the carrier, positivity is
  `ae_supLocalTime_spec`).  `heightRaw` is the extended-real liminf of `heightApprox` along the
  H01 sequence `supEps θ` (blueprint "raw", retained until finiteness).
* `exploration θ f t`: Stieltjes measure of `x ↦ I^x_t` on `(0,t]` (atom at `t` kept, none at
  `0`), pushed forward by the ANCESTRAL height `s ↦ H_s` (heights of the ORIGINAL path `f`,
  not of its reversal at `t`).  Total mass `X_t - I_t`.
* `eraseMass m ρ` removes the top `m` units of mass (cut level `eraseCut`, partial atom there);
  `concatAbove ρ ν = ρ + ν` shifted up by the top of the support of `ρ`.

TRUTH / SCOPE.  Everything is for each FIXED `t` (a.s. or in probability) EXCEPT the explicitly
ancestral exports `ae_heightApprox_ancestral`, `ae_heightRaw_eq_stieltjes`,
`ae_exploration_no_root_atom`, `ae_support_gapfree`, `ae_topHeight_ancestral`.  No continuity.
Theorems bind `hθ : 1 < θ ∧ θ ≤ 2`.

AMBIGUITIES / FLAGS.
1. DEPENDENCE ON UNPROVED H01: `supEps`, `ae_tendsto_supOccupation`,
   `supOccupation_tendstoInMeasure`, `ae_supLocalTime_spec`, `measurable_supLocalTime_uncurry`
   are copied `sorry` statements of the H01 contract.  H02 introduces NO new subsequence: since
   the reversed prefix has the law of the original prefix, the H01 sequence `supEps θ` serves
   every fixed `t` (blueprint "one deterministic subsequence" is therefore `supEps θ`).
2. The blueprint states `heightApprox_tendstoInMeasure` with `θ < 2` and a θ=2 direct
   definition; here `height` is defined for all `θ ∈ (1,2]` through H01 (which covers `θ = 2`),
   and `ae_height_two` records the θ=2 identification `H = X - I`, which relies on the H01
   normalization `c = 1` (at θ=2, `M = S`, `ψ(λ) = λ²`).  Flagged for audit.
3. `reversedAt_identification` holds only almost surely (the left limits in `reverseIncrements`
   versus values differ at jump times; needs no jump at `t`).
4. `ae_height_zero_iff` is the FIXED-`t` version of `height_zero_iff_reflected_zero`; the
   all-`t` version needs ancestral local-time regularity (H03).
5. `exploration` uses `Measure.map`; for a NONZERO source measure and a non-a.e.-measurable map
   the pinned Mathlib fallback is `Measure.dirac Classical.ofNonempty` (NOT zero; see
   `Measure.map_of_not_aemeasurable_of_ne_zero`), so a mass-only test misses it.
   `measurable_height_section` and `measurable_exploration_heightMap` rule this out.
   `explorationStieltjes` is a junk-fallback `dite`; `explorationStieltjes_spec` shows the condition holds for every path.
6. `eraseCut` is `sInf` in `ℝ≥0` (junk `0` if the set is empty).  For finite `ρ` and `m > 0` the
   set is nonempty; for `m = 0` it needs BOUNDED support, hence the `m = 0` branch of `eraseMass`.
   `concatAbove` and any characterization lemma represent the source operation only when the
   first measure has bounded support (`topHeight` is `sSup`, junk `0` if unbounded).
7. Audit H02 (Sol, 7 Nov 2026) items 1-3, 6 applied here; items 4-5 live in the bridge contract
   `CT7_H02b_HeightBridges.lean`.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees

-- The local time at the supremum: `BGW.StableTrees.SupremumLocalTimePublic` (sealed).


/-! ### H02 definitions -/

/-- The interval infimum `I^s_t = inf_{[s ∧ t, t]} X`. -/
noncomputable def futureInf (f : DLoc) (t s : ℝ≥0) : ℝ := ⨅ u : Set.Icc (min s t) t, f.1 u

/-- Minimal-exploration occupation approximation `ε⁻¹ Leb{s ≤ t | X_s < I^s_t + ε}`. -/
noncomputable def heightApprox (ε : ℝ) (f : DLoc) (t : ℝ≥0) : ℝ :=
  ε⁻¹ * (volume {s : ℝ | 0 ≤ s ∧ s ≤ (t : ℝ) ∧
    f.1 s.toNNReal < futureInf f t s.toNNReal + ε}).toReal

/-- The time-reversed process at `t`: `u ↦ X_t - X_{(t - u ∧ t)-}` (constant after `t`). -/
noncomputable def reversedPath (t : ℝ≥0) (f : DLoc) : ℝ≥0 → ℝ :=
  fun u => f.1 t - Function.leftLim f.1 (t - min u t)

/-- The reversed path is càdlàg (so `reversedAt` is never junk). -/
theorem isCadlag_reversedPath (t : ℝ≥0) (f : DLoc) : IsCadlag (reversedPath t f) := sorry

open scoped Classical in
/-- The reversed process at `t` as a `DLoc` element (junk `DLoc.zero` never occurs). -/
noncomputable def reversedAt (t : ℝ≥0) (f : DLoc) : DLoc :=
  if h : IsCadlag (reversedPath t f) then ⟨reversedPath t f, h⟩ else DLoc.zero

/-- On `[0,t]` the reversed path is the sealed `reverseIncrements` of the restriction. -/
theorem restrict_reversedAt (t : ℝ≥0) (f : DLoc) :
    DLoc.restrict t (reversedAt t f) = reverseIncrements t.2 (DLoc.restrict t f) := sorry

/-- `(t, f) ↦ reversedAt t f` is jointly measurable. -/
theorem measurable_reversedAt_uncurry :
    Measurable (fun p : ℝ≥0 × DLoc => reversedAt p.1 p.2) := sorry

/-- **The height** `H_t = M_t(reversed process at t)`: the H01 supremum local time of the
time-reversed process. -/
noncomputable def height (θ : ℝ) (f : DLoc) (t : ℝ≥0) : ℝ :=
  supLocalTime θ (reversedAt t f) t

/-- The raw (extended-real) height: liminf of the approximations along `supEps θ`. -/
noncomputable def heightRaw (θ : ℝ) (f : DLoc) (t : ℝ≥0) : ℝ≥0∞ :=
  liminf (fun k => ENNReal.ofReal (heightApprox (supEps θ k) f t)) atTop

/-! ### Reversal identification (fixed `t`) -/

/-- **Law of the reversed prefix**: for each `t > 0`, reversal at `t` preserves the law of the
prefix `[0,t]` (sealed `map_reverseIncrements_stableProcessLaw`, transferred to `DLoc`). -/
theorem map_restrict_reversedAt_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0}
    (ht : 0 < t) :
    (stableLocalLaw θ : Measure DLoc).map (fun f => DLoc.restrict t (reversedAt t f)) =
      (stableLocalLaw θ : Measure DLoc).map (DLoc.restrict t) := sorry

/-- **Identification** (a.s. for each fixed `t`, all `ε > 0` at once): the interval-infimum
approximation is the H01 occupation approximation of the reversed process. -/
theorem ae_heightApprox_eq_supOccupation_reversed {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ ε : ℝ, 0 < ε →
      heightApprox ε f t = supOccupation ε (reversedAt t f) t := sorry

/-! ### Convergence of the approximation (each fixed `t`) -/

/-- **Convergence in probability** for each fixed `t` along the full filter `ε ↓ 0`. -/
theorem heightApprox_tendstoInMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    TendstoInMeasure (stableLocalLaw θ : Measure DLoc)
      (fun (ε : ℝ) (f : DLoc) => heightApprox ε f t) (𝓝[>] (0 : ℝ))
      (fun f => height θ f t) := sorry

/-- **A.s. convergence along the deterministic sequence `supEps θ`**, for each fixed `t`
(the null set depends on `t`). -/
theorem ae_tendsto_heightApprox_supEps {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      Tendsto (fun k => heightApprox (supEps θ k) f t) atTop (𝓝 (height θ f t)) := sorry

/-- The raw height is a.s. the finite nonnegative height, for each fixed `t`. -/
theorem ae_heightRaw_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      0 ≤ height θ f t ∧ heightRaw θ f t = ENNReal.ofReal (height θ f t) := sorry

/-- **Ancestral convergence** (one null set; all `t` and all ancestral `s ≤ t` at once): at an
ancestral time `s` (`X_{s-} ≤ I^s_t` with `s < t`, or an upward jump of `X` at `s = t`) the
approximations along `supEps θ` converge to the finite nonnegative `H_s`, and the raw height is
the genuine finite `ofReal`. -/
theorem ae_heightApprox_ancestral {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t s : ℝ≥0,
      ((s < t ∧ Function.leftLim f.1 s ≤ futureInf f t s) ∨
        (s = t ∧ Function.leftLim f.1 t < f.1 t)) →
      Tendsto (fun k => heightApprox (supEps θ k) f s) atTop (𝓝 (height θ f s)) ∧
      0 ≤ height θ f s ∧ heightRaw θ f s = ENNReal.ofReal (height θ f s) := sorry

/-- **θ = 2**: `H_t = X_t - I_t` a.s. for each fixed `t` (uses the H01 normalization). -/
theorem ae_height_two (t : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw 2 : Measure DLoc), height 2 f t = f.1 t - futureInf f t 0 := sorry

/-! ### Measurability -/

/-- Joint measurability of the approximation in `(ε, t, f)`. -/
theorem measurable_heightApprox_uncurry :
    Measurable (fun p : ℝ × ℝ≥0 × DLoc => heightApprox p.1 p.2.2 p.2.1) := sorry

/-- Joint measurability of the chosen version `(t, f) ↦ H_t(f)`. -/
theorem measurable_height_uncurry (θ : ℝ) :
    Measurable (fun p : ℝ≥0 × DLoc => height θ p.2 p.1) := sorry

/-- Raw-prefix measurability: `H_t` is measurable for the σ-algebra generated by
`DLoc.restrict t`. -/
theorem measurable_height_prefix (θ : ℝ) (t : ℝ≥0) :
    Measurable[MeasurableSpace.comap (DLoc.restrict t) inferInstance]
      (fun f : DLoc => height θ f t) := sorry

/-- For every fixed path `f`, `s ↦ H_s(f)` is measurable (so `exploration` is not junk). -/
theorem measurable_height_section (θ : ℝ) (f : DLoc) :
    Measurable (fun s : ℝ≥0 => height θ f s) := sorry

/-- `heightRaw` is measurable in `f` for each `t`. -/
theorem measurable_heightRaw (θ : ℝ) (t : ℝ≥0) :
    Measurable (fun f : DLoc => heightRaw θ f t) := sorry

/-! ### The minimal exploration measure -/

/-- `x ↦ I^{x⁺}_t` as a function on `ℝ`. -/
noncomputable def futureInfFun (f : DLoc) (t : ℝ≥0) (x : ℝ) : ℝ := futureInf f t x.toNNReal

/-- For every path, `x ↦ I^x_t` is monotone and right-continuous. -/
theorem explorationStieltjes_spec (f : DLoc) (t : ℝ≥0) :
    Monotone (futureInfFun f t) ∧ ∀ x, ContinuousWithinAt (futureInfFun f t) (Ici x) x := sorry

open scoped Classical in
/-- The Stieltjes function of `x ↦ I^{x⁺}_t` (junk zero only if the spec failed). -/
noncomputable def explorationStieltjes (f : DLoc) (t : ℝ≥0) : StieltjesFunction ℝ :=
  if h : Monotone (futureInfFun f t) ∧ ∀ x, ContinuousWithinAt (futureInfFun f t) (Ici x) x then
    { toFun := futureInfFun f t
      mono' := h.1
      right_continuous' := h.2 }
  else
    { toFun := fun _ => 0
      mono' := monotone_const
      right_continuous' := fun _ => continuousWithinAt_const }

/-- **The minimal exploration measure** `ρ_t = ∫_{(0,t]} 1{H_s ∈ ·} d_s I^s_t`, a measure on
heights (`(·).toNNReal` of the real height; heights are a.s. nonnegative). -/
noncomputable def exploration (θ : ℝ) (f : DLoc) (t : ℝ≥0) : Measure ℝ≥0 :=
  Measure.map (fun s : ℝ => (height θ f s.toNNReal).toNNReal)
    ((explorationStieltjes f t).measure.restrict (Ioc 0 (t : ℝ)))

/-- **Total mass** `ρ_t(ℝ≥0) = X_t - I_t` for every path (the atom at `s = t` is kept). -/
theorem exploration_univ (θ : ℝ) (f : DLoc) (t : ℝ≥0) :
    exploration θ f t univ = ENNReal.ofReal (f.1 t - futureInf f t 0) := sorry

/-- **Measure-level bridge** (endpoint atoms retained): a.s., for every `t`, the random Stieltjes
measure of `x ↦ I^x_t` on `(0,t]` is carried by times where `H` is finite, nonnegative and equal
to the raw height.  Must be proved by Stieltjes ancestral concentration, NOT by Fubini against
Lebesgue measure from `ae_heightRaw_eq`. -/
theorem ae_heightRaw_eq_stieltjes {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      ∀ᵐ s ∂((explorationStieltjes f t).measure.restrict (Ioc 0 (t : ℝ))),
        0 ≤ height θ f s.toNNReal ∧
          heightRaw θ f s.toNNReal = ENNReal.ofReal (height θ f s.toNNReal) := sorry

/-- Guard against the `Measure.map` fallback: the height section is measurable on `ℝ`. -/
theorem measurable_exploration_heightMap (θ : ℝ) (f : DLoc) :
    Measurable (fun s : ℝ => (height θ f s.toNNReal).toNNReal) := sorry

/-- `(t, f) ↦ ρ_t(B)` is measurable for measurable `B`. -/
theorem measurable_exploration_apply (θ : ℝ) {B : Set ℝ≥0} (hB : MeasurableSet B) :
    Measurable (fun p : ℝ≥0 × DLoc => exploration θ p.2 p.1 B) := sorry

/-- Top of the support of a measure on heights (junk `0` for the zero measure). -/
noncomputable def topHeight (ρ : Measure ℝ≥0) : ℝ≥0 :=
  sSup {h : ℝ≥0 | ∀ ε : ℝ, 0 < ε → 0 < ρ (Metric.ball h ε)}

/-- **Support reaches the height**, fixed `t`: a.s. the top of the support of `ρ_t` is `H_t`. -/
theorem ae_topHeight_exploration {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (topHeight (exploration θ f t) : ℝ) = height θ f t := sorry

/-- **Upper support bound** (fixed `t`): a.s. `ρ_t` puts no mass above `H_t` (excludes the
unbounded-support junk of `topHeight`). -/
theorem ae_exploration_above_height {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      exploration θ f t (Ioi (height θ f t).toNNReal) = 0 := sorry

/-- **No root atom**: a.s., simultaneously for all `t`, `ρ_t` has no atom at height `0`. -/
theorem ae_exploration_no_root_atom {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0, exploration θ f t {0} = 0 := sorry

/-- **No gaps, fixed-time version** (`∀ t` outside the a.e. binder; kept for reference). -/
theorem ae_support_gapfree_fixed {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ h : ℝ≥0, (h : ℝ) < height θ f t →
      ∀ ε : ℝ, 0 < ε → 0 < exploration θ f t (Metric.ball h ε) := sorry

-- REMOVED 7 Nov 2026 (coordinator): the simultaneous `ae_support_gapfree` (all `t` inside the
-- a.e. binder, with the RAW height).  No downstream contract consumes it (H02b, H03, H04, K09,
-- K11 use only fixed-time support facts), and at exceptional random times the raw limsup height
-- need not be the support top, so the raw simultaneous form is at risk of being false.  A
-- simultaneous version, if ever needed, belongs after H03 with the continuous `heightLoc`.

/-- **Ancestral top identification**: a.s., for every `t` and ancestral `s` (same antecedent as
`ae_heightApprox_ancestral`), the top of the support of `ρ_s` is `H_s`. -/
theorem ae_topHeight_ancestral {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t s : ℝ≥0,
      ((s < t ∧ Function.leftLim f.1 s ≤ futureInf f t s) ∨
        (s = t ∧ Function.leftLim f.1 t < f.1 t)) →
      (topHeight (exploration θ f s) : ℝ) = height θ f s := sorry

/-- **Height zero iff reflected zero** (fixed `t` only): a.s. `H_t = 0 ↔ X_t = I_t`, i.e.
`ρ_t = 0`.  The all-`t` version needs ancestral local-time regularity (H03). -/
theorem ae_height_zero_iff {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (height θ f t = 0 ↔ f.1 t = futureInf f t 0) := sorry

/-! ### Erasure and concatenation (deterministic restart identity) -/

/-- Cut level for removing the top `m` units of mass of `ρ`. -/
noncomputable def eraseCut (m : ℝ≥0∞) (ρ : Measure ℝ≥0) : ℝ≥0 :=
  sInf {h : ℝ≥0 | ρ (Ioi h) ≤ m}

/-- Remove the top `m` units of mass: for `m = 0` nothing is removed; otherwise keep `ρ`
strictly below the cut, and put the remaining part of the mass of `ρ(Ici cut)` as an atom at the
cut.  (For `m > 0` and finite `ρ` the cut set is nonempty; without the `m = 0` branch an
unbounded support would give junk cut `0`.) -/
noncomputable def eraseMass (m : ℝ≥0∞) (ρ : Measure ℝ≥0) : Measure ℝ≥0 :=
  if m = 0 then ρ else
    ρ.restrict (Iio (eraseCut m ρ)) + (ρ (Ici (eraseCut m ρ)) - m) • Measure.dirac (eraseCut m ρ)

/-- Append `ν` above the support of `ρ`: heights of `ν` are shifted by `topHeight ρ`.
PRECONDITION: this represents the source concatenation only when `ρ` has BOUNDED support
(`topHeight` is an `sSup` in `ℝ≥0`, junk `0` for unbounded support); characterization lemmas
must carry that hypothesis. -/
noncomputable def concatAbove (ρ ν : Measure ℝ≥0) : Measure ℝ≥0 :=
  ρ + ν.map (fun x => x + topHeight ρ)

/-- Erasing at most the total (finite) mass removes exactly that mass. -/
theorem eraseMass_univ {ρ : Measure ℝ≥0} [IsFiniteMeasure ρ] {m : ℝ≥0∞} (hm : m ≤ ρ univ) :
    eraseMass m ρ univ = ρ univ - m := sorry

theorem eraseMass_zero (ρ : Measure ℝ≥0) : eraseMass 0 ρ = ρ := sorry

/-- Distribution-function characterization of erasure (includes `m ≥ ρ univ` and `m = ⊤`). -/
theorem eraseMass_Iic {ρ : Measure ℝ≥0} [IsFiniteMeasure ρ] (m : ℝ≥0∞) (h : ℝ≥0) :
    eraseMass m ρ (Iic h) = min (ρ (Iic h)) (ρ univ - m) := sorry

/-- **Restart identity** (a.s., for fixed `t` and `r`): with `f' = shift t f` the centered
future, `ρ_{t+r}(f)` is `ρ_t(f)` with the top `-inf_{[0,r]} f'` units of mass erased and the
fresh exploration `ρ_r(f')` appended above the remaining support height. -/
theorem ae_exploration_restart {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t r : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      exploration θ f (t + r) =
        concatAbove
          (eraseMass (ENNReal.ofReal (-(futureInf (DLoc.shift t f) r 0))) (exploration θ f t))
          (exploration θ (DLoc.shift t f) r) := sorry

end BGW.StableTrees
