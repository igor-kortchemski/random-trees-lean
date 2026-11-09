/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.AldousCriterionGapBound

/-!
# Control of the terminal window

A strict exit after the left endpoint of the terminal window detects any large
oscillation there, including a terminal jump. The nearby-optional-times estimate
then supplies the endpoint control needed for merging a short final block.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace BGW.Skorokhod

variable {T : ℝ}

/-- Uniform Aldous increment bounds control oscillation in a deterministic terminal window.

Reference: Billingsley 1999, Section 16. -/
theorem measure_aldous_terminal_oscillation_le {Ω : Type*} [m : MeasurableSpace Ω]
    (hT : 0 ≤ T) (P : Measure Ω) [IsFiniteMeasure P]
    (𝓕 : Filtration (Icc (0 : ℝ) T) m) (X : Ω → D T ℝ) (hX : Measurable X)
    (hadapted : ∀ t, Measurable[𝓕 t] (fun ω => X ω t))
    (a : Icc (0 : ℝ) T) {ε δ : ℝ} {η : ℝ≥0∞} (hε : 0 < ε) (hδ : 0 < δ)
    (hwindow : T - a ≤ δ)
    (hbound : ∀ ρ : Ω → Icc (0 : ℝ) T, IsOptionalTime 𝓕 ρ →
      ∀ u : ℝ, 0 ≤ u → u ≤ 2 * δ →
        P {ω | ε / 3 < |X ω (projIcc 0 T hT (ρ ω + u)) - X ω (ρ ω)|} ≤ η) :
    P {ω | ∃ t : Icc (0 : ℝ) T, a ≤ t ∧ ε < |X ω t - X ω a|} ≤ 4 * η := by
  let τ : Ω → Icc (0 : ℝ) T := fun _ => a
  let σ (ω : Ω) := aldousExitTime (X ω) ε a
  have hτ : IsOptionalTime 𝓕 τ := by
    intro t
    change MeasurableSet[𝓕 t] {ω : Ω | a < t}
    exact MeasurableSet.const _
  have hσ : IsOptionalTime 𝓕 σ := hτ.aldousExitTime X hadapted ε
  have hpair := measure_short_aldous_pair_le hT P 𝓕 X hX τ σ hτ hσ hδ hbound
  apply (measure_mono ?_).trans hpair
  intro ω hω
  have hinc : ε ≤ |X ω (σ ω) - X ω a| :=
    le_abs_sub_aldousExitTime_of_exists (X ω) hε.le a hω
  refine ⟨le_aldousExitTime (X ω) ε a, ?_, by dsimp [τ]; linarith⟩
  have hσT := (σ ω).2.2
  dsimp [τ]
  linarith

end BGW.Skorokhod
