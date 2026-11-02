/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.ContinuumTrees.BrownianBridgeRegression
public import BGW.ContinuumTrees.Coding
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Separation of Brownian bridge minima

The minimum on a prefix and the minimum on a later closed interval ending
strictly before one are almost surely different. Regression on the increment
between the intervals leaves an independent continuous residual path. For
each residual, equality of the two minima holds for at most one value of the
nondegenerate Gaussian increment.

This is the one-dimensional Gaussian regression argument of Kim and Pollard,
*Cube Root Asymptotics* (1990), Lemma 2.6, pp. 197–198, specialized to the
explicit Brownian bridge covariance. No excursion-law identification is used.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace BGW.ContinuumTrees.BrownianBridge

private theorem continuous_minimumOn (a b : unitInterval) :
    Continuous (fun f : C(unitInterval, ℝ) => Coding.intervalMin f a b) :=
  (isCompact_uIcc : IsCompact (uIcc a b)).continuous_sInf
    (f := fun g : C(unitInterval, ℝ) => fun t => g t) continuous_eval

private theorem strictAnti_regressionMinimumDifference (b c d : unitInterval)
    (hbc : b < c) (hcd : c ≤ d) (hd : d < 1) (r : C(unitInterval, ℝ)) :
    StrictAnti (fun z : ℝ =>
      Coding.intervalMin (r + z • regressionProfile b c) 0 b -
        Coding.intervalMin (r + z • regressionProfile b c) c d) := by
  have hb0 := unitInterval.nonneg b
  have hcR : (c : ℝ) ≤ (d : ℝ) := hcd
  have hdR : (d : ℝ) < 1 := hd
  have hshort : (c : ℝ) - (b : ℝ) < 1 := by linarith
  have hden : 0 < 1 - ((c : ℝ) - (b : ℝ)) := by linarith
  intro z₁ z₂ hz
  obtain ⟨u, hu, hleft⟩ :=
    Coding.exists_intervalMin (r + z₁ • regressionProfile b c) 0 b
  obtain ⟨v, hv, hright⟩ :=
    Coding.exists_intervalMin (r + z₂ • regressionProfile b c) c d
  have hu' : u ≤ b := by
    have huI : (0 : unitInterval) ≤ u ∧ u ≤ b := by
      simpa only [uIcc_of_le (show (0 : unitInterval) ≤ b from bot_le), mem_Icc] using hu
    exact huI.2
  have hv' : c ≤ v ∧ v ≤ d := by simpa only [uIcc_of_le hcd, mem_Icc] using hv
  have hpu : regressionProfile b c u ≤ 0 := by
    rw [regressionProfile_of_le b c u hbc hshort hu']
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (unitInterval.nonneg u)) hden.le
  have hpv : 0 < regressionProfile b c v := by
    rw [regressionProfile_of_ge b c v hbc hshort hv'.1]
    exact div_pos (sub_pos.mpr (lt_of_le_of_lt (show (v : ℝ) ≤ (d : ℝ) from hv'.2)
      hdR)) hden
  have hleft' := Coding.intervalMin_le (r + z₂ • regressionProfile b c) 0 b hu
  have hright' := Coding.intervalMin_le (r + z₁ • regressionProfile b c) c d hv
  have hmulLeft := mul_le_mul_of_nonpos_right hz.le hpu
  have hmulRight := mul_lt_mul_of_pos_right hz hpv
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply,
    smul_eq_mul] at hleft hright hleft' hright'
  linarith

/-- Minima on `[0,b]` and `[c,d]` are almost surely unequal when `b < c ≤ d < 1`.
The second interval ends strictly before one, so its regression profile is strictly positive. -/
theorem measure_prefixMin_eq_intervalMin (b c d : unitInterval)
    (hbc : b < c) (hcd : c ≤ d) (hd : d < 1) :
    (law : Measure C(unitInterval, ℝ))
      {f | Coding.intervalMin f 0 b = Coding.intervalMin f c d} = 0 := by
  have hbcR : (b : ℝ) < (c : ℝ) := hbc
  have hcdR : (c : ℝ) ≤ (d : ℝ) := hcd
  have hdR : (d : ℝ) < 1 := hd
  have hb0 := unitInterval.nonneg b
  have hpos : 0 < (c : ℝ) - (b : ℝ) := sub_pos.mpr hbcR
  have hshort : (c : ℝ) - (b : ℝ) < 1 := by linarith
  let P := (law : Measure C(unitInterval, ℝ))
  let R := regressionResidual b c
  let Z := fun f : C(unitInterval, ℝ) => f c - f b
  have hmR : Measurable R := (continuous_regressionResidual b c).measurable
  have hmZ : Measurable Z := (ContinuousMap.measurable_eval c).sub
    (ContinuousMap.measurable_eval b)
  let : NullSingletonClass (P.map Z) := ⟨fun a => by
    rw [Measure.map_apply hmZ (measurableSet_singleton a)]
    exact measure_eval_sub_eq_zero c b
      (by rw [abs_of_pos hpos]; exact hpos)
      (by rw [abs_of_pos hpos]; exact hshort) a⟩
  let E : Set (C(unitInterval, ℝ) × ℝ) :=
    {p | Coding.intervalMin (p.1 + p.2 • regressionProfile b c) 0 b =
      Coding.intervalMin (p.1 + p.2 • regressionProfile b c) c d}
  have hmE : MeasurableSet E := by
    have hcont : Continuous (fun p : C(unitInterval, ℝ) × ℝ =>
        p.1 + p.2 • regressionProfile b c) :=
      continuous_fst.add (continuous_snd.smul continuous_const)
    exact (isClosed_eq ((continuous_minimumOn 0 b).comp hcont)
      ((continuous_minimumOn c d).comp hcont)).measurableSet
  have hprod : (P.map R).prod (P.map Z) E = 0 := by
    apply Measure.measure_prod_null_of_ae_null hmE
    apply ae_of_all
    intro r
    apply Set.Subsingleton.measure_zero
    intro z₁ hz₁ z₂ hz₂
    apply (strictAnti_regressionMinimumDifference b c d hbc hcd hd r).injective
    change Coding.intervalMin (r + z₁ • regressionProfile b c) 0 b =
      Coding.intervalMin (r + z₁ • regressionProfile b c) c d at hz₁
    change Coding.intervalMin (r + z₂ • regressionProfile b c) 0 b =
      Coding.intervalMin (r + z₂ • regressionProfile b c) c d at hz₂
    exact (sub_eq_zero.mpr hz₁).trans (sub_eq_zero.mpr hz₂).symm
  have hmap : P.map (fun f => (R f, Z f)) = (P.map R).prod (P.map Z) :=
    (indepFun_regressionResidual_increment b c hbc hshort).map_prod_eq_prod_map_map
      hmR.aemeasurable hmZ.aemeasurable
  have hpreimage : (fun f => (R f, Z f)) ⁻¹' E =
      {f | Coding.intervalMin f 0 b = Coding.intervalMin f c d} := by
    ext f
    change (Coding.intervalMin (regressionResidual b c f + (f c - f b) •
      regressionProfile b c) 0 b = Coding.intervalMin
      (regressionResidual b c f + (f c - f b) • regressionProfile b c) c d) ↔
        Coding.intervalMin f 0 b = Coding.intervalMin f c d
    rw [regressionResidual, sub_add_cancel]
  have h := congrArg (fun μ : Measure (C(unitInterval, ℝ) × ℝ) => μ E) hmap
  rw [Measure.map_apply (hmR.prodMk hmZ) hmE, hpreimage, hprod] at h
  exact h

end BGW.ContinuumTrees.BrownianBridge
