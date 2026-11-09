/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.AldousCriterionOptional
public import BGW.Skorokhod.MeasurableCylinders
public import BGW.Skorokhod.Restrict

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Adapted evaluations at optional times

Stopping a path at a deterministic time gives a path-valued random variable
measurable for that time's σ-algebra, by the cylinder characterization. Joint
evaluation then gives measurability of evaluation at an optional time capped at
that deterministic time. No regularity of the filtration is required.
-/

@[expose] public section

open MeasureTheory Set

namespace BGW.Skorokhod

variable {T : ℝ} {Ω : Type*} {m : MeasurableSpace Ω}

/-- A path stopped at `t` is measurable for `𝓕 t` when its coordinates are adapted.

Reference: Billingsley 1999, Section 16. -/
private theorem measurable_stop_of_adapted (𝓕 : Filtration (Icc (0 : ℝ) T) m)
    (X : Ω → D T ℝ) (hadapted : ∀ t, Measurable[𝓕 t] (fun ω => X ω t))
    (t : Icc (0 : ℝ) T) : Measurable[𝓕 t] (fun ω => stop (t : ℝ) (X ω)) := by
  have hEval (s : Icc (0 : ℝ) T) :
      Measurable[𝓕 t] (fun ω => (stop (t : ℝ) (X ω)) s) := by
    let u : Icc (0 : ℝ) T := ⟨max 0 (min (s : ℝ) t), le_max_left _ _,
      max_le (t.2.1.trans t.2.2) ((min_le_right _ _).trans t.2.2)⟩
    have hut : u ≤ t := max_le t.2.1 (min_le_right _ _)
    exact (hadapted u).mono (𝓕.mono hut) le_rfl
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap (fun ω => stop (t : ℝ) (X ω))
      (inferInstance : MeasurableSpace (D T ℝ)) ≤ 𝓕 t
  rw [measurableSpace_eq_iSup_comap_eval (T := T) (E := ℝ) (S := univ)
    dense_univ (t.2.1.trans t.2.2) (mem_univ _)]
  simp only [MeasurableSpace.comap_iSup, iSup_le_iff, MeasurableSpace.comap_comp,
    Function.comp_def]
  intro s _
  exact (hEval s).comap_le

/-- An optional time capped at `t` is measurable for `𝓕 t`.

Reference: Billingsley 1999, Section 16. -/
private theorem IsOptionalTime.measurable_min {𝓕 : Filtration (Icc (0 : ℝ) T) m}
    {σ : Ω → Icc (0 : ℝ) T} (hσ : IsOptionalTime 𝓕 σ) (t : Icc (0 : ℝ) T) :
    Measurable[𝓕 t] (fun ω => min (σ ω) t) := by
  apply measurable_of_Iio
  intro s
  by_cases hts : t < s
  · have hall : ∀ ω, min (σ ω) t < s := fun ω => (min_le_right _ _).trans_lt hts
    simp only [preimage, mem_Iio, hall, ofPred_true, MeasurableSet.univ]
  · have hst : s ≤ t := le_of_not_gt hts
    simpa only [preimage, mem_Iio, min_lt_iff, hts, or_false] using
      𝓕.mono hst _ (hσ s)

/-- Evaluation at an optional time capped at `t` is measurable for `𝓕 t`.

Reference: Billingsley 1999, Section 16. -/
private theorem IsOptionalTime.measurable_eval_min {𝓕 : Filtration (Icc (0 : ℝ) T) m}
    {σ : Ω → Icc (0 : ℝ) T} (hσ : IsOptionalTime 𝓕 σ)
    (X : Ω → D T ℝ) (hadapted : ∀ t, Measurable[𝓕 t] (fun ω => X ω t))
    (t : Icc (0 : ℝ) T) : Measurable[𝓕 t] (fun ω => X ω (min (σ ω) t)) := by
  have hmeas := measurable_eval₂.comp
    ((measurable_stop_of_adapted 𝓕 X hadapted t).prodMk (hσ.measurable_min t))
  convert hmeas using 1
  funext ω
  change X ω (min (σ ω) t) = (stop (t : ℝ) (X ω)) (min (σ ω) t)
  apply congrArg (X ω)
  apply Subtype.ext
  change ((min (σ ω) t : Icc (0 : ℝ) T) : ℝ) =
    max 0 (min ((min (σ ω) t : Icc (0 : ℝ) T) : ℝ) (t : ℝ))
  have hmin : (((min (σ ω) t : Icc (0 : ℝ) T) : ℝ)) ≤ (t : ℝ) := min_le_right (σ ω) t
  rw [min_eq_left hmin, max_eq_right (min (σ ω) t).2.1]

/-- A strict displacement at a deterministic time after an optional time is an adapted event.

Reference: Billingsley 1999, Section 16. -/
theorem IsOptionalTime.measurableSet_displacement {𝓕 : Filtration (Icc (0 : ℝ) T) m}
    {σ : Ω → Icc (0 : ℝ) T} (hσ : IsOptionalTime 𝓕 σ)
    (X : Ω → D T ℝ) (hadapted : ∀ t, Measurable[𝓕 t] (fun ω => X ω t))
    (t : Icc (0 : ℝ) T) (ε : ℝ) :
    MeasurableSet[𝓕 t] {ω | σ ω < t ∧ ε < |X ω t - X ω (σ ω)|} := by
  have heq : {ω | σ ω < t ∧ ε < |X ω t - X ω (σ ω)|} =
      {ω | σ ω < t} ∩ {ω | ε < |X ω t - X ω (min (σ ω) t)|} := by
    ext ω
    by_cases hω : σ ω < t
    · simp only [mem_ofPred_eq, mem_inter_iff, hω, true_and, min_eq_left hω.le]
    · simp only [mem_ofPred_eq, mem_inter_iff, hω, false_and]
  rw [heq]
  exact (hσ t).inter (measurableSet_lt measurable_const
    (continuous_abs.measurable.comp ((hadapted t).sub (hσ.measurable_eval_min X hadapted t))))

end BGW.Skorokhod
