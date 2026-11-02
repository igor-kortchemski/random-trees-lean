/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree.Tilting
public import BGW.LocallyFinite.SizeConditioning

/-!
# Exponential tilting preserves size-conditioned Bienaymé laws

If two offspring probability measures satisfy `ν {k} = a * b ^ k * μ {k}`, their tree laws
restricted to size `n` differ by the constant `a ^ n * b ^ (n - 1)`. For finite nonzero `a`
and `b`, this factor cancels on conditioning. The equality holds at every size: at a null
size event, including size zero, both conditioned measures are zero. No hypothesis on the
offspring mean or on a lattice span is used.

This proves Proposition `prop:tilting` (Kennedy) of
`papers/arXiv-2503.07530v2 (1)/subcritical_cauchy_final_arxiv.tex`, with the two offspring laws
interchanged in the displayed tilting relation. It does not construct a tilt with a prescribed
mean or assert that such a tilt exists.
-/

@[expose] public section

namespace BGW.LocallyFinite

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- On a fixed size class, exponential tilting scales the entire restricted tree law. -/
theorem bienaymeLaw_restrict_sizeEvent_tilt (μ ν : Measure ℕ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (a b : ℝ≥0∞)
    (htilt : ∀ k, ν {k} = a * b ^ k * μ {k}) (n : ℕ) :
    (bienaymeLaw ν).restrict (sizeEvent n) =
      (a ^ n * b ^ (n - 1)) • (bienaymeLaw μ).restrict (sizeEvent n) := by
  have hsub : sizeEvent n ⊆ {T : Tree | FiniteVertices T} := fun _ h => h.1
  have hν := (Measure.restrict_restrict_of_subset (μ := bienaymeLaw ν) hsub).symm
  have hμ := (Measure.restrict_restrict_of_subset (μ := bienaymeLaw μ) hsub).symm
  rw [hν, bienaymeLaw_restrict_finiteVertices, hμ, bienaymeLaw_restrict_finiteVertices]
  ext A hA
  have hAs : MeasurableSet (A ∩ sizeEvent n) := hA.inter (measurableSet_sizeEvent n)
  rw [Measure.restrict_apply hA, Measure.sum_apply _ hAs, Measure.smul_apply,
    Measure.restrict_apply hA, Measure.sum_apply _ hAs, smul_eq_mul, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun t => ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  by_cases ht : t.size = n
  · have hw : PlaneTree.weight (fun d => ν {d}) t =
        (a ^ n * b ^ (n - 1)) * PlaneTree.weight (fun d => μ {d}) t := by
      simp_rw [htilt]
      rw [PlaneTree.weight_tilt, ht]
    rw [hw, mul_assoc]
  · have hnot : t.toLocallyFinite ∉ A ∩ sizeEvent n := fun h =>
      ht ((toLocallyFinite_mem_sizeEvent_iff t n).mp h.2)
    rw [Measure.dirac_apply' _ hAs]
    simp [hnot]

/-- The mass of a fixed size class changes by its common tree-weight factor. -/
theorem bienaymeLaw_sizeEvent_tilt (μ ν : Measure ℕ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (a b : ℝ≥0∞)
    (htilt : ∀ k, ν {k} = a * b ^ k * μ {k}) (n : ℕ) :
    bienaymeLaw ν (sizeEvent n) =
      (a ^ n * b ^ (n - 1)) * bienaymeLaw μ (sizeEvent n) := by
  have h := congrArg (fun ρ : Measure Tree => ρ Set.univ)
    (bienaymeLaw_restrict_sizeEvent_tilt μ ν a b htilt n)
  simpa only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Measure.smul_apply, smul_eq_mul] using h

/-- Nonzero tilt parameters preserve the set of admissible sizes. -/
theorem bienaymeLaw_sizeEvent_ne_zero_iff_tilt (μ ν : Measure ℕ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (a b : ℝ≥0∞)
    (htilt : ∀ k, ν {k} = a * b ^ k * μ {k}) (ha : a ≠ 0) (hb : b ≠ 0) (n : ℕ) :
    bienaymeLaw ν (sizeEvent n) ≠ 0 ↔ bienaymeLaw μ (sizeEvent n) ≠ 0 := by
  rw [bienaymeLaw_sizeEvent_tilt μ ν a b htilt n]
  have hc : a ^ n * b ^ (n - 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero n ha) (pow_ne_zero (n - 1) hb)
  exact mul_ne_zero_iff.trans (and_iff_right hc)

/-- Finite positive exponential tilting preserves size-conditioned tree measures.
At inadmissible sizes, including zero, both sides are the zero measure. -/
theorem cond_sizeEvent_eq_of_tilt (μ ν : Measure ℕ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (a b : ℝ≥0∞)
    (htilt : ∀ k, ν {k} = a * b ^ k * μ {k})
    (ha : a ≠ 0) (ha_top : a ≠ ∞) (hb : b ≠ 0) (hb_top : b ≠ ∞) (n : ℕ) :
    (bienaymeLaw ν)[|sizeEvent n] = (bienaymeLaw μ)[|sizeEvent n] := by
  let c := a ^ n * b ^ (n - 1)
  have hc : c ≠ 0 := mul_ne_zero (pow_ne_zero n ha) (pow_ne_zero (n - 1) hb)
  have hc_top : c ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ha_top) (ENNReal.pow_ne_top hb_top)
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond,
    bienaymeLaw_sizeEvent_tilt μ ν a b htilt n,
    bienaymeLaw_restrict_sizeEvent_tilt μ ν a b htilt n, smul_smul]
  change ((c * bienaymeLaw μ (sizeEvent n))⁻¹ * c) •
      (bienaymeLaw μ).restrict (sizeEvent n) = _
  congr 1
  rw [ENNReal.mul_inv (Or.inl hc) (Or.inl hc_top), mul_right_comm,
    ENNReal.inv_mul_cancel hc hc_top, one_mul]

end BGW.LocallyFinite
