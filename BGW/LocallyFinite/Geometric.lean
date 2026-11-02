/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree.Tilting
public import BGW.Tree.Finite
public import BGW.LocallyFinite.SizeConditioning
public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.Probability.Distributions.Uniform

/-!
# Geometric offspring and uniform plane trees

Mathlib's `geometricMeasure p` uses the success parameter `p`: its masses are
`p * (1 - p) ^ k` when `p ≠ 0`. A finite tree of size `n` therefore has weight
`p ^ n * (1 - p) ^ (n - 1)`. For `0 < p < 1`, conditioning on size gives the uniform
measure on that finite size class, independently of `p` and of the offspring mean.

This is the geometric/uniform specialization of the BGW roadmap. Its parameter `α` equals
`1 - p`. The endpoint `p = 0` is excluded: Mathlib defines
`geometricMeasure 0` to be `dirac 0`, rather than the zero sequence suggested by the formula.
At size zero both the conditioned and the uniform measures are zero; positive sizes are
admissible when `p` is strictly between zero and one.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BGW.PlaneTree

/-- Under geometric offspring, the weight of a finite tree depends only on its size. -/
theorem weight_geometric (p : unitInterval) (hp : p ≠ 0) (t : PlaneTree) :
    weight (fun k => geometricMeasure p {k}) t =
      ENNReal.ofReal (p : ℝ) ^ t.size *
        ENNReal.ofReal (1 - (p : ℝ)) ^ (t.size - 1) := by
  have hq : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.2.2
  have hweights : (fun k => geometricMeasure p {k}) =
      (fun k => ENNReal.ofReal (p : ℝ) * ENNReal.ofReal (1 - (p : ℝ)) ^ k * 1) := by
    funext k
    rw [geometricMeasure_singleton hp, ENNReal.ofReal_mul (pow_nonneg hq k),
      ENNReal.ofReal_pow hq]
    simp only [mul_one]
    ac_rfl
  rw [hweights, weight_tilt]
  simp [weight]

end BGW.PlaneTree

namespace BGW.LocallyFinite

/-- A fixed finite size class contains only finitely many locally finite trees. -/
theorem finite_sizeEvent (n : ℕ) : (sizeEvent n).Finite := by
  rw [sizeEvent_eq_image]
  exact (PlaneTree.finite_size_eq n).image PlaneTree.toLocallyFinite

/-- For an interior geometric parameter, exactly the positive sizes are admissible. -/
theorem bienaymeLaw_sizeEvent_geometric_ne_zero_iff (p : unitInterval)
    (hp0 : p ≠ 0) (hp1 : p ≠ 1) (n : ℕ) :
    bienaymeLaw (geometricMeasure p) (sizeEvent n) ≠ 0 ↔ 0 < n := by
  rw [bienaymeLaw_sizeEvent_ne_zero_iff]
  constructor
  · rintro ⟨t, ht, -⟩
    rw [← ht]
    exact t.size_pos
  · intro hn
    refine ⟨PlaneTree.node (List.replicate (n - 1) PlaneTree.leaf), ?_, ?_⟩
    · simp only [PlaneTree.size_node, List.map_replicate, PlaneTree.size_leaf,
        List.sum_replicate, smul_eq_mul, mul_one]
      omega
    · rw [PlaneTree.weight_ne_zero_iff]
      intro d _
      rw [geometricMeasure_singleton hp0]
      exact ENNReal.ofReal_ne_zero_iff.mpr (geometricMeasure_pos hp0 hp1 d)

/-- A geometric BGW tree conditioned on size is uniform on that size class.
This is an equality of zero measures when `n = 0`, and of probability measures otherwise. -/
theorem cond_sizeEvent_geometric_eq_uniform (p : unitInterval)
    (hp0 : p ≠ 0) (hp1 : p ≠ 1) (n : ℕ) :
    (bienaymeLaw (geometricMeasure p))[|sizeEvent n] =
      Measure.uniformOfFinset (finite_sizeEvent n).toFinset := by
  classical
  let s := (finite_sizeEvent n).toFinset
  let c := ENNReal.ofReal (p : ℝ) ^ n * ENNReal.ofReal (1 - (p : ℝ)) ^ (n - 1)
  have hp_pos : 0 < (p : ℝ) :=
    unitInterval.coe_pos.mpr (unitInterval.pos_iff_ne_zero.mpr hp0)
  have hq_pos : 0 < 1 - (p : ℝ) :=
    sub_pos.mpr (unitInterval.coe_lt_one.mpr (unitInterval.lt_one_iff_ne_one.mpr hp1))
  have hc : c ≠ 0 := mul_ne_zero
    (pow_ne_zero n (ENNReal.ofReal_ne_zero_iff.mpr hp_pos))
    (pow_ne_zero (n - 1) (ENNReal.ofReal_ne_zero_iff.mpr hq_pos))
  have hc_top : c ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hatom : ∀ T ∈ s, bienaymeLaw (geometricMeasure p) {T} = c := by
    intro T hT
    have hT' : T ∈ sizeEvent n := by simpa [s] using hT
    rw [sizeEvent_eq_image] at hT'
    obtain ⟨t, ht, rfl⟩ := hT'
    change t.size = n at ht
    rw [bienaymeLaw_toLocallyFinite, PlaneTree.weight_geometric p hp0, ht]
  have hmass (A : Set Tree) :
      bienaymeLaw (geometricMeasure p) (sizeEvent n ∩ A) =
        ((s.filter (fun T => T ∈ A)).card : ℝ≥0∞) * c := by
    have hset : sizeEvent n ∩ A = (↑(s.filter (fun T => T ∈ A)) : Set Tree) := by
      ext T
      simp [s]
    rw [hset, ← sum_measure_singleton]
    calc
      ∑ T ∈ s.filter (fun T => T ∈ A), bienaymeLaw (geometricMeasure p) {T} =
          ∑ _T ∈ s.filter (fun T => T ∈ A), c :=
        Finset.sum_congr rfl fun T hT => hatom T (Finset.mem_filter.mp hT).1
      _ = _ := by simp
  have htotal : bienaymeLaw (geometricMeasure p) (sizeEvent n) = (s.card : ℝ≥0∞) * c := by
    simpa using hmass Set.univ
  change (bienaymeLaw (geometricMeasure p))[|sizeEvent n] = Measure.uniformOfFinset s
  ext A _hA
  rw [cond_apply (measurableSet_sizeEvent n), htotal, hmass,
    Measure.uniformOfFinset_apply, ← ENNReal.div_eq_inv_mul]
  exact ENNReal.mul_div_mul_right _ _ hc hc_top

end BGW.LocallyFinite
