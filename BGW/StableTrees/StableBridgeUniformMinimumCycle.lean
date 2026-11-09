/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.BigOperators.Fin

/-!
# A finite cyclic-invariance criterion

On the zero-sum hyperplane, reversal of all coordinates and reversal of the
initial coordinates generate cyclic shifts.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter VIII (Vervaat's
transformation and the uniform law of the minimum time); L. Chaumont, *Excursion normalisée,
méandre et pont pour les processus de Lévy stables*, Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory

namespace BGW.StableTrees

private def completeIncrements (M : ℕ) (x : Fin M → ℝ) : Fin (M + 1) → ℝ :=
  Fin.lastCases (-∑ i, x i) x

private theorem measurable_completeIncrements (M : ℕ) : Measurable (completeIncrements M) := by
  apply Measurable.of_eval
  intro i
  cases i using Fin.lastCases with
  | last =>
    simp only [completeIncrements, Fin.lastCases_last]
    exact (measurable_neg : Measurable (fun x : ℝ => -x)).comp
      (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
  | cast i =>
    simpa only [completeIncrements, Fin.lastCases_castSucc] using measurable_pi_apply i

private theorem completeIncrements_first {M : ℕ} {x : Fin (M + 1) → ℝ}
    (hx : ∑ i, x i = 0) : completeIncrements M (fun i => x i.castSucc) = x := by
  funext i
  cases i using Fin.lastCases with
  | last =>
    simp only [completeIncrements, Fin.lastCases_last]
    rw [Fin.sum_univ_castSucc] at hx
    linarith
  | cast i => simp only [completeIncrements, Fin.lastCases_castSucc]

/-- Full reversal and reversal of the strict prefix imply cyclic invariance for
a measure supported on zero-sum vectors. -/
theorem map_cyclic_of_reverse_of_prefix_reverse (M : ℕ)
    (μ : Measure (Fin (M + 1) → ℝ))
    (hsum : ∀ᵐ x ∂μ, ∑ i, x i = 0)
    (hrev : μ.map (fun x i => x i.rev) = μ)
    (hprefix : (μ.map (fun x (i : Fin M) => x i.castSucc)).map
      (fun x i => x i.rev) = μ.map (fun x (i : Fin M) => x i.castSucc))
    (k : Fin (M + 1)) : μ.map (fun x i => x (i + k)) = μ := by
  let first : (Fin (M + 1) → ℝ) → (Fin M → ℝ) := fun x i => x i.castSucc
  let rev : (Fin (M + 1) → ℝ) → (Fin (M + 1) → ℝ) := fun x i => x i.rev
  let r : (Fin M → ℝ) → (Fin M → ℝ) := fun x i => x i.rev
  have hf : Measurable first := Measurable.of_eval fun i => measurable_pi_apply i.castSucc
  have hr : Measurable r := Measurable.of_eval fun i => measurable_pi_apply i.rev
  have hrevM : Measurable rev := Measurable.of_eval fun i => measurable_pi_apply i.rev
  have hrecover : (μ.map first).map (completeIncrements M) = μ := by
    rw [Measure.map_map (measurable_completeIncrements M) hf]
    calc
      _ = μ.map id := Measure.map_congr (hsum.mono fun x hx => completeIncrements_first hx)
      _ = μ := Measure.map_id
  let A := (completeIncrements M) ∘ r ∘ first
  have hA : Measurable A := (measurable_completeIncrements M).comp (hr.comp hf)
  have hmapA : μ.map A = μ := by
    change μ.map ((completeIncrements M) ∘ (r ∘ first)) = μ
    rw [← Measure.map_map (measurable_completeIncrements M) (hr.comp hf),
      ← Measure.map_map hr hf, hprefix, hrecover]
  have hshift : μ.map (fun x i => x (i + 1)) = μ := by
    have heq : (fun x i => x (i + 1)) =ᵐ[μ] A ∘ rev := by
      filter_upwards [hsum] with x hx
      funext i
      cases i using Fin.lastCases with
      | last =>
        simp only [Function.comp_apply, A, completeIncrements, r, first, rev,
          Fin.lastCases_last]
        simp only [Fin.rev_castSucc, Fin.rev_rev]
        have hz : (Fin.last M : Fin (M + 1)) + 1 = 0 := by
          apply Fin.ext
          simp
        rw [hz, Fin.sum_univ_succ] at *
        linarith
      | cast i =>
        simp only [Function.comp_apply, A, completeIncrements, r, first, rev,
          Fin.lastCases_castSucc]
        simp only [Fin.rev_castSucc, Fin.rev_rev]
        congr 1
        apply Fin.ext
        simp
    rw [Measure.map_congr heq, ← Measure.map_map hA hrevM, hrev, hmapA]
  have hstep : Measurable (fun (x : Fin (M + 1) → ℝ) i => x (i + 1)) :=
    Measurable.of_eval fun i => measurable_pi_apply (i + 1)
  induction k using Fin.induction with
  | zero =>
    simp only [add_zero]
    exact Measure.map_id
  | succ k ih =>
    have hk : Measurable (fun (x : Fin (M + 1) → ℝ) i => x (i + k.castSucc)) :=
      Measurable.of_eval fun i => measurable_pi_apply (i + k.castSucc)
    have hcomp : (fun (x : Fin (M + 1) → ℝ) i => x (i + k.succ)) =
        (fun x i => x (i + k.castSucc)) ∘ (fun x i => x (i + 1)) := by
      funext x i
      change x (i + k.succ) = x (i + k.castSucc + 1)
      congr 1
      have he : k.succ = k.castSucc + 1 := by
        apply Fin.ext
        simp
      rw [he, add_assoc]
    rw [hcomp, ← Measure.map_map hk hstep, hshift, ih]

end BGW.StableTrees
