/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.ContinuumTrees.BrownianBridgeIncrements
public import BGW.ContinuumTrees.Coding
import Mathlib.Data.Fintype.Lattice
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.IdentDistrib
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Finite grids of the Brownian bridge

The grid has `n + 1` times `i / (n + 1)`, including zero and excluding one.
Its centered cyclic rotations have the same law, as proved directly from the
Gaussian finite-dimensional distributions. Distinct grid values are almost
surely unequal. Thus the probability that all grid values are nonnegative is
`1 / (n + 1)`, which proves that the continuous bridge has negative minimum.

No assertion about uniqueness of the continuous minimum, or identification of
the Vervaat image with the classical excursion law, is used here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace BGW.ContinuumTrees.BrownianBridge

/-- An equally spaced grid including zero and excluding the duplicate endpoint one. -/
noncomputable def gridTime (n : ℕ) (i : Fin (n + 1)) : unitInterval :=
  ⟨(i : ℝ) / (n + 1 : ℕ), div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    (div_le_one (by positivity)).mpr (by exact_mod_cast i.isLt.le)⟩

@[simp] theorem coe_gridTime (n : ℕ) (i : Fin (n + 1)) :
    (gridTime n i : ℝ) = (i : ℝ) / (n + 1 : ℕ) := rfl

@[simp] theorem gridTime_zero (n : ℕ) : gridTime n 0 = 0 := by
  apply Subtype.ext
  simp [gridTime]

theorem gridTime_lt_one (n : ℕ) (i : Fin (n + 1)) : (gridTime n i : ℝ) < 1 := by
  rw [coe_gridTime, div_lt_one (by positivity)]
  exact_mod_cast i.isLt

theorem gridTime_injective (n : ℕ) : Function.Injective (gridTime n) := by
  intro i j hij
  have h := congrArg (fun t : unitInterval => (t : ℝ)) hij
  simp only [coe_gridTime] at h
  have hval : (i : ℝ) = (j : ℝ) := (div_left_inj' (by positivity)).mp h
  apply Fin.ext
  exact_mod_cast hval

/-- Evaluation of a continuous path on the finite grid. -/
noncomputable def gridValues (n : ℕ) (f : C(unitInterval, ℝ)) (i : Fin (n + 1)) : ℝ :=
  f (gridTime n i)

@[fun_prop] theorem measurable_gridValues (n : ℕ) : Measurable (gridValues n) :=
  Measurable.of_eval fun i => ContinuousMap.measurable_eval (gridTime n i)

private theorem gridTime_add (n : ℕ) (i k : Fin (n + 1)) :
    (gridTime n (i + k) : ℝ) =
      if (gridTime n i : ℝ) + (gridTime n k : ℝ) < 1 then
        (gridTime n i : ℝ) + (gridTime n k : ℝ)
      else (gridTime n i : ℝ) + (gridTime n k : ℝ) - 1 := by
  have hm : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hlt : (gridTime n i : ℝ) + (gridTime n k : ℝ) < 1 ↔
      i.val + k.val < n + 1 := by
    rw [coe_gridTime, coe_gridTime, ← add_div, div_lt_one hm]
    exact_mod_cast (Iff.rfl : i.val + k.val < n + 1 ↔ i.val + k.val < n + 1)
  by_cases h : i.val + k.val < n + 1
  · rw [ite_eq_left (hlt.mpr h)]
    simp only [coe_gridTime, Fin.val_add_eq_ite, ite_eq_right (not_le.mpr h),
      Nat.cast_add, add_div]
  · have hge : n + 1 ≤ i.val + k.val := le_of_not_gt h
    rw [ite_eq_right (mt hlt.mp h)]
    simp only [coe_gridTime, Fin.val_add_eq_ite, ite_eq_left hge, Nat.cast_sub hge,
      Nat.cast_add]
    field_simp

private def bridgeKernel (s t : ℝ) : ℝ := min s t - s * t

private theorem bridgeKernel_comm (s t : ℝ) : bridgeKernel s t = bridgeKernel t s := by
  simp only [bridgeKernel, min_comm, mul_comm]

private theorem bridgeKernel_shift_of_le {s t r : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t < 1) (_hr : 0 ≤ r) (_hr1 : r < 1) :
    let x := if s + r < 1 then s + r else s + r - 1
    let y := if t + r < 1 then t + r else t + r - 1
    bridgeKernel x y - bridgeKernel x r - bridgeKernel r y + bridgeKernel r r =
      bridgeKernel s t := by
  dsimp only
  by_cases htr : t + r < 1
  · have hsr : s + r < 1 := by linarith
    rw [ite_eq_left hsr, ite_eq_left htr]
    simp only [bridgeKernel, min_eq_left (show s + r ≤ t + r by linarith),
      min_eq_right (show r ≤ s + r by linarith),
      min_eq_left (show r ≤ t + r by linarith), min_self, min_eq_left hst]
    ring
  · by_cases hsr : s + r < 1
    · rw [ite_eq_left hsr, ite_eq_right htr]
      simp only [bridgeKernel, min_eq_right (show t + r - 1 ≤ s + r by linarith),
        min_eq_right (show r ≤ s + r by linarith),
        min_eq_right (show t + r - 1 ≤ r by linarith), min_self, min_eq_left hst]
      ring
    · rw [ite_eq_right hsr, ite_eq_right htr]
      simp only [bridgeKernel, min_eq_left (show s + r - 1 ≤ t + r - 1 by linarith),
        min_eq_left (show s + r - 1 ≤ r by linarith),
        min_eq_right (show t + r - 1 ≤ r by linarith), min_self, min_eq_left hst]
      ring

private theorem bridgeKernel_shift {s t r : ℝ} (hs : 0 ≤ s) (hs1 : s < 1)
    (ht : 0 ≤ t) (ht1 : t < 1) (hr : 0 ≤ r) (hr1 : r < 1) :
    let x := if s + r < 1 then s + r else s + r - 1
    let y := if t + r < 1 then t + r else t + r - 1
    bridgeKernel x y - bridgeKernel x r - bridgeKernel r y + bridgeKernel r r =
      bridgeKernel s t := by
  rcases le_total s t with h | h
  · exact bridgeKernel_shift_of_le hs h ht1 hr hr1
  · have heq := bridgeKernel_shift_of_le ht h hs1 hr hr1
    dsimp only at heq ⊢
    rw [bridgeKernel_comm (if t + r < 1 then t + r else t + r - 1),
      bridgeKernel_comm (if t + r < 1 then t + r else t + r - 1) r,
      bridgeKernel_comm r (if s + r < 1 then s + r else s + r - 1),
      bridgeKernel_comm t s] at heq
    linarith

private theorem covariance_grid_rotation (n : ℕ) (k i j : Fin (n + 1)) :
    cov[fun f => gridValues n f (i + k) - gridValues n f k,
      fun f => gridValues n f (j + k) - gridValues n f k;
      (law : Measure C(unitInterval, ℝ))] =
      cov[fun f => gridValues n f i, fun f => gridValues n f j;
        (law : Measure C(unitInterval, ℝ))] := by
  have hmem (a : Fin (n + 1)) :=
    (isGaussianProcess_eval.hasGaussianLaw_eval (gridTime n a)).memLp_two
  unfold gridValues
  rw [covariance_fun_sub_fun_sub (hmem _) (hmem _) (hmem _) (hmem _)]
  simp only [covariance_eval]
  change bridgeKernel _ _ - bridgeKernel _ _ - bridgeKernel _ _ + bridgeKernel _ _ =
    bridgeKernel _ _
  rw [gridTime_add, gridTime_add]
  have h := bridgeKernel_shift (unitInterval.nonneg (gridTime n i)) (gridTime_lt_one n i)
    (unitInterval.nonneg (gridTime n j)) (gridTime_lt_one n j)
    (unitInterval.nonneg (gridTime n k)) (gridTime_lt_one n k)
  dsimp only at h
  linarith

private theorem hasGaussianLaw_gridValues (n : ℕ) :
    HasGaussianLaw (gridValues n) (law : Measure C(unitInterval, ℝ)) := by
  classical
  let J := Finset.univ.image (gridTime n)
  let L : (J → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
    { toFun x i := x ⟨gridTime n i, by simp [J]⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact (isGaussianProcess_eval.hasGaussianLaw J).map L

/-- Centered cyclic rotations of the grid have the same law. This invariance is derived
from Gaussian means and covariances; it is not an assumption on the bridge. -/
theorem identDistrib_grid_rotation (n : ℕ) (k : Fin (n + 1)) :
    IdentDistrib (fun f i => gridValues n f (i + k) - gridValues n f k) (gridValues n)
      (law : Measure C(unitInterval, ℝ)) (law : Measure C(unitInterval, ℝ)) := by
  classical
  let X := fun (f : C(unitInterval, ℝ)) (i : Fin (n + 1)) =>
    gridValues n f (i + k) - gridValues n f k
  let Y := gridValues n
  have hY := hasGaussianLaw_gridValues n
  let L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
    { toFun x i := x (i + k) - x k
      map_add' := by intros; ext; simp; ring
      map_smul' := by intros; ext; simp; ring }
  have hX : HasGaussianLaw X (law : Measure C(unitInterval, ℝ)) := hY.map L
  refine ⟨hX.aemeasurable, hY.aemeasurable, ?_⟩
  apply (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).map_measurableEquiv_injective
  rw [MeasurableEquiv.coe_toLp, ← PiLp.coe_symm_continuousLinearEquiv 2 ℝ]
  have := hX.isGaussian_map
  have := hY.isGaussian_map
  apply IsGaussian.ext
  · rw [integral_map, integral_map, integral_map, integral_map]
    · simp only [id_eq]
      rw [ContinuousLinearEquiv.integral_comp_comm,
        ContinuousLinearEquiv.integral_comp_comm]
      congr 1
      ext i
      rw [eval_integral, eval_integral]
      · exact (integral_eval_sub _ _).trans (integral_eval _).symm
      · exact fun i => (isGaussianProcess_eval.hasGaussianLaw_eval (gridTime n i)).integrable
      · exact fun i => (hasGaussianLaw_eval_sub (gridTime n (i + k)) (gridTime n k)).integrable
    any_goals fun_prop
  · rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_of_isSymm isPosSemidef_covarianceBilin.isSymm
      isPosSemidef_covarianceBilin.isSymm fun x => ?_
    simp only [ContinuousLinearMap.toBilinForm_apply]
    rw [PiLp.coe_symm_continuousLinearEquiv, covarianceBilin_apply_pi,
      covarianceBilin_apply_pi]
    · congrm ∑ i, ∑ j, _ * ?_
      rw [covariance_map (measurable_pi_apply i).aestronglyMeasurable
          (measurable_pi_apply j).aestronglyMeasurable hX.aemeasurable,
        covariance_map (measurable_pi_apply i).aestronglyMeasurable
          (measurable_pi_apply j).aestronglyMeasurable hY.aemeasurable]
      exact covariance_grid_rotation n k i j
    · intro i
      exact (memLp_map_measure_iff (measurable_pi_apply i).aestronglyMeasurable
        hY.aemeasurable).mpr
        (isGaussianProcess_eval.hasGaussianLaw_eval (gridTime n i)).memLp_two
    · intro i
      exact (memLp_map_measure_iff (measurable_pi_apply i).aestronglyMeasurable
        hX.aemeasurable).mpr
        (hasGaussianLaw_eval_sub (gridTime n (i + k)) (gridTime n k)).memLp_two

/-- All distinct values on the grid are almost surely unequal. -/
theorem ae_gridValues_injective (n : ℕ) :
    ∀ᵐ f ∂(law : Measure C(unitInterval, ℝ)), Function.Injective (gridValues n f) := by
  have hp (i j : Fin (n + 1)) (hij : i ≠ j) :
      ∀ᵐ f ∂(law : Measure C(unitInterval, ℝ)), gridValues n f i ≠ gridValues n f j := by
    apply ae_eval_ne
    · apply abs_pos.mpr
      intro h
      apply hij
      exact gridTime_injective n (Subtype.ext (sub_eq_zero.mp h))
    · rw [abs_lt]
      have hi := gridTime_lt_one n i
      have hj := gridTime_lt_one n j
      have hi0 := unitInterval.nonneg (gridTime n i)
      have hj0 := unitInterval.nonneg (gridTime n j)
      constructor <;> linarith
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr fun j =>
    ae_all_iff.mpr (hp i j)] with f hf
  intro i j heq
  by_contra hij
  exact hf i j hij heq

/-- The grid has a unique minimizing index almost surely, including the one-point grid. -/
theorem ae_existsUnique_gridMinimum (n : ℕ) :
    ∀ᵐ f ∂(law : Measure C(unitInterval, ℝ)),
      ∃! k, ∀ i, gridValues n f k ≤ gridValues n f i := by
  filter_upwards [ae_gridValues_injective n] with f hf
  obtain ⟨k, hk⟩ := Finite.exists_min (gridValues n f)
  refine ⟨k, hk, fun j hj => hf ?_⟩
  exact le_antisymm (hj k) (hk j)

private def gridMinimumEvent (n : ℕ) (k : Fin (n + 1)) : Set C(unitInterval, ℝ) :=
  {f | ∀ i, gridValues n f k ≤ gridValues n f i}

private theorem measurableSet_gridMinimumEvent (n : ℕ) (k : Fin (n + 1)) :
    MeasurableSet (gridMinimumEvent n k) := by
  simp only [gridMinimumEvent, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le (ContinuousMap.measurable_eval _) (ContinuousMap.measurable_eval _)

private theorem measure_gridMinimumEvent (n : ℕ) (k : Fin (n + 1)) :
    (law : Measure C(unitInterval, ℝ)) (gridMinimumEvent n k) =
      (law : Measure C(unitInterval, ℝ)) {f | ∀ i, 0 ≤ gridValues n f i} := by
  have h := (identDistrib_grid_rotation n k).measure_mem_eq
    (s := {x : Fin (n + 1) → ℝ | ∀ i, 0 ≤ x i})
    (by simpa only [Set.ofPred_forall] using
      MeasurableSet.iInter fun i : Fin (n + 1) =>
        measurableSet_le (measurable_const : Measurable (fun _ : Fin (n + 1) → ℝ => (0 : ℝ)))
          (measurable_pi_apply i))
  convert h using 2
  · ext f
    constructor
    · intro hf i
      exact sub_nonneg.mpr (hf (i + k))
    · intro hf i
      have hfi := hf (i - k)
      simpa only [sub_add_cancel, sub_nonneg] using hfi
  · rfl

/-- Exact finite-grid positivity probability; the duplicate value at time one is excluded. -/
theorem measure_grid_nonnegative (n : ℕ) :
    (law : Measure C(unitInterval, ℝ)) {f | ∀ i, 0 ≤ gridValues n f i} =
      ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
  have hdis : Pairwise (fun i j => AEDisjoint (law : Measure C(unitInterval, ℝ))
      (gridMinimumEvent n i) (gridMinimumEvent n j)) := by
    intro i j hij
    rw [AEDisjoint, measure_eq_zero_iff_ae_notMem]
    filter_upwards [ae_gridValues_injective n] with f hf hmem
    exact hij (hf (le_antisymm (hmem.1 j) (hmem.2 i)))
  have hcover : (⋃ k, gridMinimumEvent n k) = Set.univ := by
    ext f
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact Finite.exists_min (gridValues n f)
  have hsum := measure_iUnion₀ hdis
    (fun k => (measurableSet_gridMinimumEvent n k).nullMeasurableSet)
  rw [hcover, measure_univ] at hsum
  simp only [measure_gridMinimumEvent, tsum_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have hmul := congrArg (fun x : ℝ≥0∞ => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * x) hsum
  simpa only [mul_one, ← mul_assoc,
    ENNReal.inv_mul_cancel (by positivity : ((n + 1 : ℕ) : ℝ≥0∞) ≠ 0)
      (by simp : ((n + 1 : ℕ) : ℝ≥0∞) ≠ ∞), one_mul] using hmul.symm

/-- The continuous bridge has a strictly negative global minimum almost surely.
The conclusion excludes both deterministic zero endpoints as minimizers. -/
theorem ae_intervalMin_neg :
    ∀ᵐ f ∂(law : Measure C(unitInterval, ℝ)), Coding.intervalMin f 0 1 < 0 := by
  have hle (n : ℕ) :
      (law : Measure C(unitInterval, ℝ)) {f | 0 ≤ Coding.intervalMin f 0 1} ≤
        ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [← measure_grid_nonnegative]
    apply measure_mono
    intro f hf i
    exact hf.trans (Coding.intervalMin_le f 0 1
      (by simp only [Set.uIcc_of_le (show (0 : unitInterval) ≤ 1 from zero_le_one),
        Set.mem_Icc]; exact ⟨bot_le, le_top⟩))
  have hz : (law : Measure C(unitInterval, ℝ)) {f | 0 ≤ Coding.intervalMin f 0 1} = 0 := by
    apply le_antisymm _ bot_le
    exact ge_of_tendsto
      (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1))
      (Filter.Eventually.of_forall hle)
  rw [ae_iff]
  simpa only [not_lt] using hz

end BGW.ContinuumTrees.BrownianBridge
