import BGW.Skorokhod.DLoc
import BGW.StableTrees.StableProcessLaw
import BGW.StableTrees.StableProcessNoNegativeJumps
import BGW.StableTrees.StableLevyLaw
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Contract probe for CT.C6 blueprint Node 3 (stable instance; deterministic carrier `DLoc` is
the sealed `BGW/Skorokhod/DLoc.lean`, audit correction 1: the compatible-family subtype stays
internal behind `DLoc.measurableEquivCompatible`).

Contents: the local stable law `stableLocalLaw θ : ProbabilityMeasure DLoc`, built by the N02
construction (`exists_unique_compatiblePathLaw` at the horizons `n + 1` with marginals
`stableProcessLaw θ (n + 1)`) transported along `DLoc.measurableEquivCompatible.symm`; its
characterization by compact restrictions (every positive horizon `T`, not only the integers),
and the coordinate facts used downstream: start at `0`, fixed-time marginals, no fixed
discontinuities, and `∀ t, leftLim ≤ value` almost surely (quantifier order `∀ᵐ f, ∀ t`, proved
through the countable family of integer horizons and `ae_leftLim_le_stableProcessLaw`, NOT through
fixed-time continuity).

Junk value: for `θ ∉ (1, 2]` the law is the Dirac mass at the zero path. Every characterization
below carries the hypothesis `1 < θ ∧ θ ≤ 2`, except `stableLocalLaw_of_not` which documents the
junk branch. At horizon zero the stable law is the Dirac mass at the zero path; this follows from
the almost-sure initial value (`map_restrict_zero_stableLocalLaw`).
Maintained file: `BGW/StableTrees/StableLocalLaw.lean` (namespace `BGW.StableTrees`). -/

open MeasureTheory Set Filter Topology
open scoped NNReal
open BGW.Skorokhod

/-- The zero local path. -/
def BGW.Skorokhod.DLoc.zero : DLoc := ⟨fun _ => 0, IsCadlag.const⟩

namespace BGW.StableTrees

/-- At horizon zero, the stable process law is the Dirac mass at the zero path. -/
theorem stableProcessLaw_zero (θ : ℝ) :
    (stableProcessLaw θ 0 : Measure (D 0 ℝ)) =
      Measure.dirac (Skorokhod.ofContinuous (ContinuousMap.const _ 0)) := sorry

/-- Compatibility of the integer-horizon stable process laws under restriction (feeds N02). -/
theorem stableProcessLaw_succ_restrict {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (n : ℕ) :
    (stableProcessLaw θ (((n + 1 : ℕ) : ℝ) + 1)).map
        (restrict (strictMono_succHorizon.monotone (Nat.le_succ n))) =
      stableProcessLaw θ ((n : ℝ) + 1) := sorry

/-- **The local stable law.** For `1 < θ ≤ 2`: the unique law on `DLoc` whose integer-horizon
restrictions are `stableProcessLaw θ (n + 1)`, obtained from N02 and transported along
`measurableEquivCompatible.symm`. Junk value (Dirac at the zero path) otherwise. -/
noncomputable def stableLocalLaw (θ : ℝ) : ProbabilityMeasure DLoc :=
  if hθ : 1 < θ ∧ θ ≤ 2 then
    (Classical.choose
        (exists_unique_compatiblePathLaw (fun n : ℕ => (n : ℝ) + 1) strictMono_succHorizon
          (fun n => by positivity) (fun n => stableProcessLaw θ ((n : ℝ) + 1))
          (fun n => stableProcessLaw_succ_restrict hθ n)).exists).map
      DLoc.measurableEquivCompatible.symm
  else ⟨Measure.dirac DLoc.zero, inferInstance⟩

/-- Junk branch of the definition. -/
theorem stableLocalLaw_of_not {θ : ℝ} (hθ : ¬ (1 < θ ∧ θ ≤ 2)) :
    stableLocalLaw θ = ⟨Measure.dirac DLoc.zero, inferInstance⟩ := sorry

/-- **N03, restriction.** The restriction of the local stable law to every positive real horizon
`T` is the compact stable process law `P_T`. -/
theorem map_restrict_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {T : ℝ≥0} (hT : 0 < T) :
    (stableLocalLaw θ : Measure DLoc).map (DLoc.restrict T) =
      (stableProcessLaw θ (T : ℝ) : Measure (D (T : ℝ) ℝ)) := sorry

/-- Restriction to horizon zero: the zero-path Dirac mass, i.e. `stableProcessLaw θ 0`. -/
theorem map_restrict_zero_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (stableLocalLaw θ : Measure DLoc).map (DLoc.restrict 0) =
      (stableProcessLaw θ 0 : Measure (D 0 ℝ)) := sorry

/-- The same statement in `ProbabilityMeasure` form (`ProbabilityMeasure.map` is total at this
Mathlib pin, no measurability witness; the value is the pushforward measure regardless). -/
theorem stableLocalLaw_restrict {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {T : ℝ≥0} (hT : 0 < T) :
    (stableLocalLaw θ).map (DLoc.restrict T) =
      stableProcessLaw θ (T : ℝ) := sorry

/-- **N03, characterization / uniqueness.** A law on `DLoc` is the local stable law iff its
restriction to every positive horizon is the stable process law. The `←` direction is the
"determined by compact restrictions" statement (via `DLoc.measure_ext_of_restrict` at the integer
horizons and `map_restrict_stableProcessLaw`). -/
theorem eq_stableLocalLaw_iff {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {Q : ProbabilityMeasure DLoc} :
    Q = stableLocalLaw θ ↔
      ∀ T : ℝ≥0, 0 < T →
        (Q : Measure DLoc).map (DLoc.restrict T) =
          (stableProcessLaw θ (T : ℝ) : Measure (D (T : ℝ) ℝ)) := sorry

/-- Uniqueness, restricted to the integer horizons (the form N02 consumes). -/
theorem eq_stableLocalLaw_of_forall_nat {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {Q : ProbabilityMeasure DLoc}
    (h : ∀ n : ℕ, (Q : Measure DLoc).map (DLoc.restrict ((n : ℝ≥0) + 1)) =
      (stableProcessLaw θ (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ) : Measure (D (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ) ℝ))) :
    Q = stableLocalLaw θ := sorry

/-! ### Coordinate facts -/

/-- The local stable process starts at `0` almost surely. -/
theorem ae_eval_zero_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : DLoc ∂(stableLocalLaw θ : Measure DLoc), f.1 0 = 0 := sorry

/-- Fixed-time marginals: `X_t ∼ stableLawAt θ t` for `t > 0`. -/
theorem map_eval_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0} (ht : 0 < t) :
    (stableLocalLaw θ : Measure DLoc).map (DLoc.eval t) =
      (stableLawAt θ (t : ℝ) : Measure ℝ) := sorry

/-- No fixed discontinuities: for each deterministic time `t`, a.s. the path is continuous at `t`
(at `t = 0` this is right-continuity in `ℝ≥0`). The quantifier is `∀ t, ∀ᵐ f`, NOT `∀ᵐ f, ∀ t`. -/
theorem ae_continuousAt_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    ∀ᵐ f : DLoc ∂(stableLocalLaw θ : Measure DLoc), ContinuousAt f.1 t := sorry

/-- Spectral positivity, simultaneously at all times: almost surely, for every `t : ℝ≥0` the left
limit does not exceed the value (no negative jump; at `t = 0` the left limit is the value by the
`leftLim` convention). Quantifier order is `∀ᵐ f, ∀ t`. -/
theorem ae_leftLim_le_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : DLoc ∂(stableLocalLaw θ : Measure DLoc),
      ∀ t : ℝ≥0, Function.leftLim f.1 t ≤ f.1 t := sorry

end BGW.StableTrees
