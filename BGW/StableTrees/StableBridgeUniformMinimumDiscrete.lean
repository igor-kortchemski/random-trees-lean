/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableBridgeUniformMinimumGrid
import BGW.StableTrees.StableProcessMarkovAux

/-!
# Uniform finite-grid minimum indices of the stable bridge

Strict-prefix absolute continuity excludes equal values at distinct grid times.
Cyclic increment exchangeability then makes the unique grid minimum index uniform.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter VIII (Vervaat's
transformation and the uniform law of the minimum time); L. Chaumont, *Excursion normalisée,
méandre et pont pour les processus de Lévy stables*, Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The bridge has unequal values at two distinct deterministic strict-prefix times. -/
theorem stableBridgeLaw_ae_eval_ne {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (s t : Set.Icc (0 : ℝ) 1) (hst : s < t) (ht1 : (t : ℝ) < 1) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)), f t ≠ f s := by
  let a : ℝ := ((t : ℝ) + 1) / 2
  have ha : 0 < a := by dsimp [a]; linarith [t.2.1]
  have ha1 : a < 1 := by dsimp [a]; linarith
  have hta : (t : ℝ) ≤ a := by dsimp [a]; linarith
  let s' : Set.Icc (0 : ℝ) a := ⟨s, s.2.1, (show (s : ℝ) ≤ t from hst.le).trans hta⟩
  let t' : Set.Icc (0 : ℝ) a := ⟨t, t.2.1, hta⟩
  have hP := isStableLevyLaw_stableProcessLaw hθ ha
  have hpair : ∀ᵐ g : D a ℝ ∂(stableProcessLaw θ a : Measure (D a ℝ)), g t' ≠ g s' := by
    have hlaw := hP.map_sub_eval s' t' hst
    have hm : Measurable (fun g : D a ℝ => g t' - g s') :=
      (measurable_sub : Measurable (fun p : ℝ × ℝ => p.1 - p.2)).comp
        ((measurable_eval t').prodMk (measurable_eval s'))
    have hz : (stableProcessLaw θ a : Measure (D a ℝ)) {g | g t' - g s' = 0} = 0 := by
      change (stableProcessLaw θ a : Measure (D a ℝ))
        ((fun g : D a ℝ => g t' - g s') ⁻¹' {0}) = 0
      rw [← Measure.map_apply hm (measurableSet_singleton 0), hlaw]
      exact stableLawAt_singleton hθ (sub_pos.mpr hst) 0
    rw [ae_iff]
    simpa only [not_not, sub_eq_zero] using hz
  have hpre := ae_of_ae_map (measurable_restrict ha1.le).aemeasurable
    ((map_restrict_stableBridgeLaw_absolutelyContinuous hθ ha ha1).ae_le hpair)
  exact hpre

/-- Distinct times in the grid excluding time one are strictly ordered. -/
theorem strictMono_bridgeGridTime (M : ℕ) :
    StrictMono (fun i : Fin (M + 1) => gridTime M i) := by
  intro i j hij
  change (gridTime M i : ℝ) < (gridTime M j : ℝ)
  rw [gridTime_coe M i (by omega), gridTime_coe M j (by omega)]
  exact div_lt_div_of_pos_right (by exact_mod_cast hij) (by positivity)

/-- Grid values excluding the duplicate terminal endpoint are almost surely distinct. -/
theorem stableBridgeLaw_ae_bridgeGridValues_injective {θ : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (M : ℕ) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)),
      Function.Injective (bridgeGridValues M f) := by
  have hpair (i j : Fin (M + 1)) (hij : i < j) :
      ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)),
        bridgeGridValues M f j ≠ bridgeGridValues M f i := by
    apply stableBridgeLaw_ae_eval_ne hθ _ _ (strictMono_bridgeGridTime M hij)
    rw [gridTime_coe M j (by omega)]
    exact (div_lt_one (by positivity)).mpr (by exact_mod_cast j.isLt)
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr fun j =>
    ae_all_iff.mpr (hpair i j)] with f hf
  intro i j heq
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (hf i j hij heq.symm).elim
  · exact hij
  · exact (hf j i hij heq).elim

/-- The first minimum index on the finite bridge grid. -/
noncomputable def bridgeGridMinIndex (M : ℕ) (f : D 1 ℝ) : Fin (M + 1) :=
  finiteMinIndex M (bridgeGridValues M f)

/-- The finite-grid minimum index is measurable, including paths with ties. -/
theorem measurable_bridgeGridMinIndex (M : ℕ) : Measurable (bridgeGridMinIndex M) :=
  (measurable_finiteMinIndex M).comp (measurable_bridgeGridValues M)

/-- Centered cyclic relabeling preserves the law of the grid values. -/
theorem bridgeGridValues_centered_shift {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (M : ℕ) (k : Fin (M + 1)) :
    (stableBridgeLaw θ : Measure (D 1 ℝ)).map
        (fun f i => bridgeGridValues M f (i + k) - bridgeGridValues M f k) =
      (stableBridgeLaw θ : Measure (D 1 ℝ)).map
        (fun f i => bridgeGridValues M f i - bridgeGridValues M f 0) := by
  have h := congrArg (Measure.map (cyclicPrimitive M)) (bridge_gridIncr_cyclic hθ M k)
  have hs : Measurable (fun (f : D 1 ℝ) i => gridIncr M f (i + k)) :=
    Measurable.of_eval fun i => (measurable_pi_apply (i + k)).comp (measurable_gridIncr M)
  rw [Measure.map_map (measurable_cyclicPrimitive M) hs,
    Measure.map_map (measurable_cyclicPrimitive M) (measurable_gridIncr M)] at h
  have he (f : D 1 ℝ) (hf : f ⟨1, zero_le_one, le_rfl⟩ = f ⟨0, le_rfl, zero_le_one⟩) :
      gridIncr M f = cyclicDiff M (bridgeGridValues M f) := gridIncr_eq_cyclicDiff hf
  have hleft : (cyclicPrimitive M ∘ (fun f i => gridIncr M f (i + k))) =ᵐ[
      (stableBridgeLaw θ : Measure (D 1 ℝ))]
      (fun f i => bridgeGridValues M f (i + k) - bridgeGridValues M f k) := by
    filter_upwards [stableBridgeLaw_endpoints hθ] with f hf
    funext i
    simp only [Function.comp_apply, he f (hf.2.1.trans hf.1.symm)]
    exact cyclicPrimitive_shift_diff M _ k i
  have hright : cyclicPrimitive M ∘ gridIncr M =ᵐ[
      (stableBridgeLaw θ : Measure (D 1 ℝ))]
      (fun f i => bridgeGridValues M f i - bridgeGridValues M f 0) := by
    filter_upwards [stableBridgeLaw_endpoints hθ] with f hf
    funext i
    simp only [Function.comp_apply, he f (hf.2.1.trans hf.1.symm)]
    exact cyclicPrimitive_diff M _ i
  rwa [Measure.map_congr hleft, Measure.map_congr hright] at h

/-- Translating the minimum index cyclically preserves its law. -/
theorem bridgeGridMinIndex_sub_invariant {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (M : ℕ) (k : Fin (M + 1)) :
    (stableBridgeLaw θ : Measure (D 1 ℝ)).map (fun f => bridgeGridMinIndex M f - k) =
      (stableBridgeLaw θ : Measure (D 1 ℝ)).map (bridgeGridMinIndex M) := by
  have h := congrArg (Measure.map (finiteMinIndex M)) (bridgeGridValues_centered_shift hθ M k)
  have hl : Measurable (fun (f : D 1 ℝ) i =>
      bridgeGridValues M f (i + k) - bridgeGridValues M f k) :=
    Measurable.of_eval fun i => (measurable_eval _).sub (measurable_eval _)
  have hr : Measurable (fun (f : D 1 ℝ) i =>
      bridgeGridValues M f i - bridgeGridValues M f 0) :=
    Measurable.of_eval fun i => (measurable_eval _).sub (measurable_eval _)
  rw [Measure.map_map (measurable_finiteMinIndex M) hl,
    Measure.map_map (measurable_finiteMinIndex M) hr] at h
  simp only [Function.comp_def, finiteMinIndex_sub_const] at h
  have heq : (fun f => finiteMinIndex M (fun i => bridgeGridValues M f (i + k))) =ᵐ[
      (stableBridgeLaw θ : Measure (D 1 ℝ))] (fun f => bridgeGridMinIndex M f - k) := by
    filter_upwards [stableBridgeLaw_ae_bridgeGridValues_injective hθ M] with f hf
    exact finiteMinIndex_shift M hf k
  rwa [Measure.map_congr heq] at h

/-- Every index has probability exactly the reciprocal of the grid size. -/
theorem stableBridgeLaw_bridgeGridMinIndex_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (M : ℕ) (k : Fin (M + 1)) :
    (stableBridgeLaw θ : Measure (D 1 ℝ)) {f | bridgeGridMinIndex M f = k} =
      ((M + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
  let μ := (stableBridgeLaw θ : Measure (D 1 ℝ))
  have heq (j : Fin (M + 1)) : μ {f | bridgeGridMinIndex M f = j} =
      μ {f | bridgeGridMinIndex M f = 0} := by
    have h := congrArg (fun ν : Measure (Fin (M + 1)) => ν {0})
      (bridgeGridMinIndex_sub_invariant hθ M j)
    have hm : Measurable (fun f => bridgeGridMinIndex M f - j) :=
      (measurable_of_countable (fun i : Fin (M + 1) => i - j)).comp
        (measurable_bridgeGridMinIndex M)
    rw [Measure.map_apply hm
      (measurableSet_singleton 0), Measure.map_apply (measurable_bridgeGridMinIndex M)
      (measurableSet_singleton 0)] at h
    simpa only [preimage, mem_singleton_iff, sub_eq_zero] using h
  have hsum := sum_measure_preimage_singleton (μ := μ) (Finset.univ : Finset (Fin (M + 1)))
    (f := bridgeGridMinIndex M) (fun _ _ => (measurable_bridgeGridMinIndex M)
      (measurableSet_singleton _))
  simp only [Finset.coe_univ, preimage_univ, measure_univ] at hsum
  change (∑ b : Fin (M + 1), μ {f | bridgeGridMinIndex M f = b}) = 1 at hsum
  simp only [heq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  have hmul := congrArg (fun x : ℝ≥0∞ => ((M + 1 : ℕ) : ℝ≥0∞)⁻¹ * x) hsum
  rw [heq k]
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel (by positivity : ((M + 1 : ℕ) : ℝ≥0∞) ≠ 0)
    (by simp : ((M + 1 : ℕ) : ℝ≥0∞) ≠ ∞), one_mul, mul_one] using hmul

end BGW.StableTrees
