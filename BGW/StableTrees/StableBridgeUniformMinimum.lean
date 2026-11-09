/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableBridgeUniformMinimumDistribution
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The uniform minimum time of the stable bridge

The proof uses cyclically exchangeable finite grids and convergence of their minimum times.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter VIII (Vervaat's
transformation and the uniform law of the minimum time); L. Chaumont, *Excursion normalisée,
méandre et pont pour les processus de Lévy stables*, Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace BGW.StableTrees

open BGW.Skorokhod

/-- Distribution-function form. -/
theorem stableBridgeLaw_vervaatTime_le {θ x : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (stableBridgeLaw θ : Measure (D 1 ℝ)) {f | (vervaatTime f : ℝ) ≤ x} =
      ENNReal.ofReal x := by
  by_cases hx1 : x = 1
  · subst x
    have hevent : {f : D 1 ℝ | (vervaatTime f : ℝ) ≤ 1} = univ := by
      ext f
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact (vervaatTime f).2.2
    rw [hevent, measure_univ]
    norm_num
  · exact tendsto_nhds_unique (tendsto_bridgeGridMinTime_event hθ x)
      (tendsto_stableBridgeLaw_bridgeGridMinTime_le hθ hx.1 (lt_of_le_of_ne hx.2 hx1))

/-- The minimum time of the stable bridge is uniform on `[0,1]`. -/
theorem map_vervaatTime_stableBridgeLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (stableBridgeLaw θ : Measure (D 1 ℝ)).map (fun f => (vervaatTime f : ℝ)) =
      volume.restrict (Set.Icc (0 : ℝ) 1) := by
  have hm : Measurable (fun f : D 1 ℝ => (vervaatTime f : ℝ)) := by
    simpa only [Function.comp_def] using measurable_subtype_coe.comp measurable_vervaatTime
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply hm measurableSet_Iic,
    Measure.restrict_apply measurableSet_Iic]
  change (stableBridgeLaw θ : Measure (D 1 ℝ)) {f | (vervaatTime f : ℝ) ≤ x} =
    volume (Iic x ∩ Icc (0 : ℝ) 1)
  by_cases hx0 : x < 0
  · have hevent : {f : D 1 ℝ | (vervaatTime f : ℝ) ≤ x} = ∅ := by
      ext f
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact not_le_of_gt (hx0.trans_le (vervaatTime f).2.1)
    have hI : Iic x ∩ Icc (0 : ℝ) 1 = ∅ := by
      ext t
      simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false]
      rintro ⟨ht, ht0, -⟩
      linarith
    simp [hevent, hI]
  · by_cases hx1 : 1 ≤ x
    · have hevent : {f : D 1 ℝ | (vervaatTime f : ℝ) ≤ x} = univ := by
        ext f
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        exact (vervaatTime f).2.2.trans hx1
      have hI : Iic x ∩ Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := by
        apply inter_eq_right.mpr
        intro t ht
        exact ht.2.trans hx1
      rw [hevent, hI, measure_univ, Real.volume_Icc]
      norm_num
    · have hx : x ∈ Icc (0 : ℝ) 1 := ⟨le_of_not_gt hx0, (lt_of_not_ge hx1).le⟩
      rw [stableBridgeLaw_vervaatTime_le hθ hx]
      have hI : Iic x ∩ Icc (0 : ℝ) 1 = Icc (0 : ℝ) x := by
        ext t
        simp only [mem_inter_iff, mem_Iic, mem_Icc]
        constructor
        · rintro ⟨htx, ht0, -⟩
          exact ⟨ht0, htx⟩
        · rintro ⟨ht0, htx⟩
          exact ⟨htx, ht0, htx.trans hx.2⟩
      rw [hI, Real.volume_Icc, sub_zero]

end BGW.StableTrees
