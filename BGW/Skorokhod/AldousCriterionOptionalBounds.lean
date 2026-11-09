/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.AldousCriterionOptional

import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Topology.Order.ProjIcc

/-!
# Transfer of Aldous bounds to optional times

Right continuity transfers uniform bounds at strictly rounded stopping times to
optional times. Continuity from below applies to outer measures of increasing sets,
so this step does not require a separate measurability argument for the events.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace BGW.Skorokhod

variable {T : ℝ}

/-- Evaluation at a capped fixed offset after rounded times converges from the right.

Reference: Billingsley 1999, Section 16. -/
private theorem tendsto_eval_aldousRoundTime_add (hT : 0 ≤ T) (f : D T ℝ)
    (t : Icc (0 : ℝ) T) (h : ℝ) :
    Tendsto (fun j => f (projIcc 0 T hT ((aldousRoundTime hT j t : ℝ) + h)))
      atTop (𝓝 (f (projIcc 0 T hT ((t : ℝ) + h)))) := by
  let u := projIcc 0 T hT ((t : ℝ) + h)
  have hc : ContinuousWithinAt f (Ici u) u := by
    have heq : Ici u = insert u (Ioi u) := by
      ext v
      simp only [mem_Ici, mem_insert_iff, mem_Ioi, le_iff_lt_or_eq]
      simp only [eq_comm, or_comm]
    rw [heq]
    exact ((isCadlag f).isRightContinuous u).insert
  apply hc.tendsto.comp
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact continuous_projIcc.continuousAt.tendsto.comp
      (((continuous_subtype_val.tendsto t).comp (tendsto_aldousRoundTime hT t)).add_const h)
  · apply Eventually.of_forall
    intro j
    apply monotone_projIcc hT
    have hle : (t : ℝ) ≤ (aldousRoundTime hT j t : ℝ) := le_aldousRoundTime hT j t
    linarith

/-- Uniform bounds for closed threshold events pass to a strict threshold event at a
pointwise limit, even when the events are measured by outer measure.

Reference: Billingsley 1999, Section 16. -/
private theorem measure_lt_le_of_tendsto {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {Y : ℕ → Ω → ℝ} {Z : Ω → ℝ} {ε : ℝ} {η : ℝ≥0∞}
    (hlim : ∀ ω, Tendsto (fun j => Y j ω) atTop (𝓝 (Z ω)))
    (hbound : ∀ j, P {ω | ε ≤ Y j ω} ≤ η) : P {ω | ε < Z ω} ≤ η := by
  let A (N : ℕ) : Set Ω := ⋂ j ≥ N, {ω | ε ≤ Y j ω}
  have hmono : Monotone A := by
    intro N M hNM ω hω
    simp only [A, mem_iInter, mem_ofPred_eq] at hω ⊢
    exact fun j hj => hω j (hNM.trans hj)
  have hsub : {ω | ε < Z ω} ⊆ ⋃ N, A N := by
    intro ω hω
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((hlim ω).eventually (lt_mem_nhds hω))
    exact mem_iUnion.mpr ⟨N, mem_iInter.mpr fun j => mem_iInter.mpr fun hj => (hN j hj).le⟩
  apply (measure_mono hsub).trans
  rw [hmono.measure_iUnion]
  apply iSup_le
  intro N
  apply le_trans (measure_mono ?_) (hbound N)
  intro ω hω
  exact mem_iInter.mp (mem_iInter.mp hω N) le_rfl

/-- Aldous's sequence condition gives a uniform strict-increment bound at optional times.

Reference: Billingsley 1999, Section 16. -/
theorem exists_uniform_aldous_optional_bound (hT : 0 < T)
    {Ω : ℕ → Type*} [m : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    (𝓕 : ∀ n, Filtration (Icc (0 : ℝ) T) (m n))
    (X : ∀ n, Ω n → D T ℝ)
    (hAldous : ∀ (τ : ∀ n, Ω n → Icc (0 : ℝ) T), (∀ n, IsStopTime (𝓕 n) (τ n)) →
      ∀ h : ℕ → ℝ, (∀ n, 0 ≤ h n) → Tendsto h atTop (𝓝 0) →
      ∀ ε > 0, Tendsto
        (fun n => P n {ω | ε ≤ |X n ω (projIcc 0 T hT.le (τ n ω + h n)) - X n ω (τ n ω)|})
        atTop (𝓝 0))
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ σ : Ω n → Icc (0 : ℝ) T,
      IsOptionalTime (𝓕 n) σ → ∀ h : ℝ, 0 ≤ h → h ≤ δ →
        P n {ω | ε < |X n ω (projIcc 0 T hT.le (σ ω + h)) - X n ω (σ ω)|} ≤
          ENNReal.ofReal η := by
  obtain ⟨δ, hδ, N, hbound⟩ := exists_uniform_aldous_bound hT P 𝓕 X hAldous hε hη
  refine ⟨δ, hδ, N, fun n hn σ hσ h hh hhd => ?_⟩
  apply measure_lt_le_of_tendsto (P n)
    (Y := fun j ω => |X n ω (projIcc 0 T hT.le
      ((aldousRoundTime hT.le j (σ ω) : ℝ) + h)) -
        X n ω (aldousRoundTime hT.le j (σ ω))|)
  · intro ω
    exact ((tendsto_eval_aldousRoundTime_add hT.le (X n ω) (σ ω) h).sub
      (tendsto_eval_aldousRoundTime hT.le (X n ω) (σ ω))).abs
  · intro j
    exact hbound n hn _ (hσ.isStopTime_aldousRoundTime hT.le j) h hh hhd

end BGW.Skorokhod
