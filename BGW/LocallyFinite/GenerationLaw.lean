/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.LocallyFinite.Generation
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.Independence.Integration

/-!
# Laws of generation sizes

The root-conditioned child generation sizes are independent copies of the corresponding
generation size. Root decomposition gives the iterated offspring generating function and the
extended first moment. These marginal statements do not assert the Markov property conditional
on the entire generation history. All offspring probability measures are allowed.
-/

@[expose] public section

namespace BGW.LocallyFinite

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem measurable_generationSize (n : ℕ) : Measurable (fun T => generationSize T n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : Measurable (fun p : ℕ × Tree =>
        ∑ j ∈ Finset.range p.1, generationSize (child p.2 (j + 1)) n) :=
      measurable_from_prod_countable_right fun k =>
        (Finset.range k).measurable_sum fun j _ => ih.comp (continuous_child (j + 1)).measurable
    simpa only [Function.comp_def, id_eq, generationSize_succ] using
      h.comp (continuous_degree.measurable.prodMk measurable_id)

/-- Given the root degree `k` of positive probability, child generation sizes are iid. -/
theorem cond_map_children_generationSize (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n k : ℕ) (hk : μ {k} ≠ 0) :
    ((bienaymeLaw μ)[|{T | degree T = k}]).map
        (fun T (i : Fin k) => generationSize (child T (i.val + 1)) n) =
      Measure.pi (fun _ : Fin k => (bienaymeLaw μ).map (fun T => generationSize T n)) := by
  have hd : bienaymeLaw μ {T | degree T = k} = μ {k} := by
    have h := congrArg (fun ν : Measure ℕ => ν {k}) (bienaymeLaw_map_degree μ)
    rwa [Measure.map_apply continuous_degree.measurable (measurableSet_singleton k)] at h
  have hb := (isBienayme_bienaymeLaw μ).2 k (by rwa [hd])
  have hm : Measurable (fun ts : Fin k → Tree => fun i => generationSize (ts i) n) :=
    Measurable.of_eval fun i => (measurable_generationSize n).comp (measurable_pi_apply i)
  rw [← Measure.pi_map_pi (fun _ : Fin k => (measurable_generationSize n).aemeasurable),
    ← hb, Measure.map_map hm (Measurable.of_eval fun i =>
      (continuous_child (i.val + 1)).measurable)]
  rfl

/-- Integral form of root branching, also valid when the root-degree event is null. -/
theorem lintegral_children_of_degree (μ : Measure ℕ) [IsProbabilityMeasure μ] (k : ℕ)
    {g : (Fin k → Tree) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ T in {T | degree T = k}, g (fun i => child T (i.val + 1)) ∂bienaymeLaw μ =
      μ {k} * ∫⁻ ts, g ts ∂Measure.pi (fun _ : Fin k => bienaymeLaw μ) := by
  have hd : bienaymeLaw μ {T | degree T = k} = μ {k} := by
    have h := congrArg (fun ν : Measure ℕ => ν {k}) (bienaymeLaw_map_degree μ)
    rwa [Measure.map_apply continuous_degree.measurable (measurableSet_singleton k)] at h
  by_cases hk : μ {k} = 0
  · rw [Measure.restrict_eq_zero.mpr (hd.trans hk), lintegral_zero_measure, hk, zero_mul]
  · have hr : (bienaymeLaw μ).restrict {T | degree T = k} =
        μ {k} • (bienaymeLaw μ)[|{T | degree T = k}] := by
      rw [ProbabilityTheory.cond, hd, smul_smul,
        ENNReal.mul_inv_cancel hk (measure_ne_top _ _), one_smul]
    rw [hr, lintegral_smul_measure]
    congr 1
    rw [← (isBienayme_bienaymeLaw μ).2 k (by rwa [hd]),
      lintegral_map hg (Measurable.of_eval fun i => (continuous_child (i.val + 1)).measurable)]

private theorem lintegral_eq_tsum_degree (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (g : Tree → ℝ≥0∞) :
    ∫⁻ T, g T ∂bienaymeLaw μ =
      ∑' k : ℕ, ∫⁻ T in {T | degree T = k}, g T ∂bienaymeLaw μ := by
  have hu : ⋃ k : ℕ, {T : Tree | degree T = k} = Set.univ := by ext T; simp
  have h := lintegral_iUnion (μ := bienaymeLaw μ) (s := fun k : ℕ => {T : Tree | degree T = k})
    (fun k => continuous_degree.measurable (measurableSet_singleton k))
    (fun i j hij => Set.disjoint_left.mpr fun T hi hj => hij (hi.symm.trans hj)) g
  simpa only [hu, Measure.restrict_univ] using h

/-- Root branching gives one composition by the offspring generating function. -/
theorem lintegral_pow_generationSize_succ (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) (s : ℝ≥0∞) :
    (∫⁻ T, s ^ generationSize T (n + 1) ∂bienaymeLaw μ) =
      offspringGF μ (∫⁻ T, s ^ generationSize T n ∂bienaymeLaw μ) := by
  have hf : Measurable (fun T : Tree => s ^ generationSize T n) :=
    (measurable_of_countable _).comp (measurable_generationSize n)
  rw [lintegral_eq_tsum_degree, offspringGF]
  apply tsum_congr
  intro k
  have he : (∫⁻ T in {T | degree T = k}, s ^ generationSize T (n + 1) ∂bienaymeLaw μ) =
      ∫⁻ T in {T | degree T = k},
        ∏ i : Fin k, s ^ generationSize (child T (i.val + 1)) n ∂bienaymeLaw μ := by
    apply setLIntegral_congr_fun (continuous_degree.measurable (measurableSet_singleton k))
    intro T hT
    change degree T = k at hT
    change s ^ generationSize T (n + 1) = ∏ i : Fin k, s ^ generationSize (child T (i.val + 1)) n
    rw [generationSize_succ_eq_sum, hT, Finset.prod_pow_eq_pow_sum]
  rw [he, lintegral_children_of_degree μ k
    (g := fun ts => ∏ i : Fin k, s ^ generationSize (ts i) n)
    (Finset.univ.measurable_prod fun i _ => hf.comp (measurable_pi_apply i))]
  congr 1
  have hind : iIndepFun (fun (i : Fin k) (ts : Fin k → Tree) => s ^ generationSize (ts i) n)
      (Measure.pi fun _ : Fin k => bienaymeLaw μ) := iIndepFun_pi (fun _ => hf.aemeasurable)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    (fun i => hf.comp (measurable_pi_apply i))]
  simp_rw [(measurePreserving_eval (fun _ : Fin k => bienaymeLaw μ) _).lintegral_comp hf]
  simp

/-- The generating function of the `n`th generation is the `n`fold iterate of the offspring
generating function. This holds throughout `ℝ≥0∞`, including `s = 0` and `s = ∞`. -/
theorem lintegral_pow_generationSize (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) (s : ℝ≥0∞) :
    (∫⁻ T, s ^ generationSize T n ∂bienaymeLaw μ) = (offspringGF μ)^[n] s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [lintegral_pow_generationSize_succ, ih, Function.iterate_succ_apply']

/-- The expected next-generation size is the offspring mean times the current expectation,
with extended nonnegative expectations and no moment assumption. -/
theorem lintegral_generationSize_succ (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    (∫⁻ T, (generationSize T (n + 1) : ℝ≥0∞) ∂bienaymeLaw μ) =
      (∫⁻ k : ℕ, (k : ℝ≥0∞) ∂μ) *
        ∫⁻ T, (generationSize T n : ℝ≥0∞) ∂bienaymeLaw μ := by
  have hf : Measurable (fun T : Tree => (generationSize T n : ℝ≥0∞)) :=
    (measurable_of_countable _).comp (measurable_generationSize n)
  rw [lintegral_eq_tsum_degree, lintegral_countable', ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro k
  have he : (∫⁻ T in {T | degree T = k},
      (generationSize T (n + 1) : ℝ≥0∞) ∂bienaymeLaw μ) =
      ∫⁻ T in {T | degree T = k},
        ∑ i : Fin k, (generationSize (child T (i.val + 1)) n : ℝ≥0∞) ∂bienaymeLaw μ := by
    apply setLIntegral_congr_fun (continuous_degree.measurable (measurableSet_singleton k))
    intro T hT
    change degree T = k at hT
    change (generationSize T (n + 1) : ℝ≥0∞) =
      ∑ i : Fin k, (generationSize (child T (i.val + 1)) n : ℝ≥0∞)
    rw [generationSize_succ_eq_sum, hT, Nat.cast_sum]
  rw [he, lintegral_children_of_degree μ k
    (g := fun ts => ∑ i : Fin k, (generationSize (ts i) n : ℝ≥0∞))
    (Finset.univ.measurable_sum fun i _ => hf.comp (measurable_pi_apply i)),
    lintegral_finsetSum (f := fun (i : Fin k) (ts : Fin k → Tree) =>
      (generationSize (ts i) n : ℝ≥0∞)) _ (fun i _ => hf.comp (measurable_pi_apply i))]
  simp_rw [(measurePreserving_eval (fun _ : Fin k => bienaymeLaw μ) _).lintegral_comp hf]
  simp [mul_assoc, mul_left_comm]

/-- The `n`th generation has mean `m ^ n`, where `m` is the possibly infinite offspring mean. -/
theorem lintegral_generationSize (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    (∫⁻ T, (generationSize T n : ℝ≥0∞) ∂bienaymeLaw μ) =
      (∫⁻ k : ℕ, (k : ℝ≥0∞) ∂μ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [lintegral_generationSize_succ, ih, pow_succ']

end BGW.LocallyFinite
