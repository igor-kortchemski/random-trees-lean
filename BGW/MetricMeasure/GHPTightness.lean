/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.GHPCompactness
public import Mathlib.MeasureTheory.Measure.Tight

/-!
# Tightness under forgetting the internal measure

The underlying GH projection is continuous and has compact inverse images of compact sets.
Thus a family of measures on GHP space is tight exactly when its underlying GH image is tight.
These outer measures may be arbitrary; the compact spaces represented by points of GHP space
still carry Borel probability measures on their whole carriers.
-/

@[expose] public section

open MeasureTheory GromovHausdorff

universe u

namespace BGW.MetricMeasure.MeasuredGHSpace

/-- Tightness of random compact measured spaces is equivalent to tightness after forgetting
their internal probability measures. No full-support hypothesis is imposed. -/
theorem isTightMeasureSet_map_underlyingGH_iff (S : Set (Measure MeasuredGHSpace.{u})) :
    letI : MeasurableSpace GHSpace := borel GHSpace
    IsTightMeasureSet (Measure.map underlyingGH '' S) ↔ IsTightMeasureSet S := by
  let : MeasurableSpace GHSpace := borel GHSpace
  let : BorelSpace GHSpace := ⟨rfl⟩
  constructor
  · intro h
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at h ⊢
    intro ε hε
    obtain ⟨K, hK, hbound⟩ := h ε hε
    refine ⟨underlyingGH ⁻¹' K, isCompact_preimage_underlyingGH hK, fun μ hμ => ?_⟩
    have hb := hbound (μ.map underlyingGH) ⟨μ, hμ, rfl⟩
    rwa [Measure.map_apply measurable_underlyingGH hK.measurableSet.compl,
      Set.preimage_compl] at hb
  · intro h
    exact h.map continuous_underlyingGH

end BGW.MetricMeasure.MeasuredGHSpace
