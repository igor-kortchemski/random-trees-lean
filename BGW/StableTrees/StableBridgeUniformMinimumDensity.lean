/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableBridgeClosed
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Finite-dimensional increment laws of bridge prefixes

The increments on a strict prefix have the product stable law tilted by the density
of the missing terminal increment. This supplies the finite-dimensional measure for
the cyclic-invariance problem.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter VIII (Vervaat's
transformation and the uniform law of the minimum time); L. Chaumont, *Excursion normalisée,
méandre et pont pour les processus de Lévy stables*, Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem map_withDensity_comp_aux {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) {f : α → β}
    (hf : Measurable f) {w : β → ℝ≥0∞} (hw : Measurable w) :
    (μ.withDensity (w ∘ f)).map f = (μ.map f).withDensity w := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hf hA, withDensity_apply _ (hf hA), withDensity_apply _ hA,
    ← lintegral_indicator (hf hA), ← lintegral_indicator hA,
    lintegral_map (hw.indicator hA) hf]
  apply lintegral_congr
  intro x
  by_cases hx : f x ∈ A <;> simp [hx]

private theorem sum_fin_increments (n : ℕ) (v : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, (v i.succ - v i.castSucc)) = v (Fin.last n) - v 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have hi := ih (fun i => v i.castSucc)
    simp only [Fin.castSucc_succ] at hi
    rw [hi]
    simp only [Fin.succ_last, Fin.castSucc_zero]
    ring

/-- A strict-prefix increment vector has the independent increment law tilted by
the transition density of the remaining increment to zero. -/
theorem map_increments_bridgePrefixLaw {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (ha : 0 < a) {P : ProbabilityMeasure (D a ℝ)} (hP : IsStableLevyLaw θ a P)
    (n : ℕ) (t : Fin (n + 1) → Set.Icc (0 : ℝ) a) (ht : StrictMono t)
    (ht0 : (t 0 : ℝ) = 0) (htn : (t (Fin.last n) : ℝ) = a) :
    (bridgePrefixLaw θ a ha.le (P : Measure (D a ℝ))).map
        (fun f i => f (t i.succ) - f (t i.castSucc)) =
      (Measure.pi (fun i : Fin n =>
        (stableLawAt θ ((t i.succ : ℝ) - t i.castSucc) : Measure ℝ))).withDensity
          (fun x => ENNReal.ofReal
            (stableDensityAt θ (1 - a) (-(∑ i, x i)) / Scalar.stableDensity θ 0)) := by
  let inc : D a ℝ → (Fin n → ℝ) := fun f i => f (t i.succ) - f (t i.castSucc)
  let w : (Fin n → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal
    (stableDensityAt θ (1 - a) (-(∑ i, x i)) / Scalar.stableDensity θ 0)
  have hi : Measurable inc := Measurable.of_eval fun i =>
    (measurable_eval _).sub (measurable_eval _)
  have hw : Measurable w :=
    (((stableDensityAt_continuous hθ).measurable.comp
      ((Finset.measurable_sum _ fun i _ => measurable_pi_apply i).neg)).div_const
        (Scalar.stableDensity θ 0)).ennreal_ofReal
  have heq : (fun f : D a ℝ => ENNReal.ofReal (bridgePrefixWeight θ a ha.le f))
      =ᵐ[(P : Measure (D a ℝ))] w ∘ inc := by
    filter_upwards [hP.start ha.le] with f hf
    have hsum : (∑ i, inc f i) = f ⟨a, ha.le, le_rfl⟩ := by
      rw [sum_fin_increments n (fun i => f (t i))]
      have hz : t 0 = ⟨0, le_rfl, ha.le⟩ := Subtype.ext ht0
      have hn : t (Fin.last n) = ⟨a, ha.le, le_rfl⟩ := Subtype.ext htn
      rw [hz, hn, hf, sub_zero]
    simp only [Function.comp_apply, w, bridgePrefixWeight, hsum]
  change ((P : Measure (D a ℝ)).withDensity _).map inc = _
  rw [withDensity_congr_ae heq, map_withDensity_comp_aux _ hi hw,
    hP.map_increments n t ht]

/-- A product of identical increment laws tilted by a function of their sum is
invariant under every coordinate permutation. -/
theorem map_pi_withDensity_sum_perm {ι : Type*} [Fintype ι]
    (μ : Measure ℝ) [SigmaFinite μ] {w : ℝ → ℝ≥0∞} (hw : Measurable w)
    (e : Equiv.Perm ι) :
    ((Measure.pi fun _ : ι => μ).withDensity (fun x => w (∑ i, x i))).map
        (fun x i => x (e i)) =
      (Measure.pi fun _ : ι => μ).withDensity (fun x => w (∑ i, x i)) := by
  let r : (ι → ℝ) → (ι → ℝ) := fun x i => x (e i)
  have hr : Measurable r := Measurable.of_eval fun i => measurable_pi_apply (e i)
  have hs : Measurable (fun x : ι → ℝ => w (∑ i, x i)) :=
    hw.comp (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
  have hmap : (Measure.pi fun _ : ι => μ).map r = Measure.pi (fun _ : ι => μ) := by
    have hr' : r = MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e.symm := by
      funext x i
      have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι => ℝ)
        e.symm x (e i)
      simpa only [Equiv.symm_apply_apply] using h.symm
    rw [hr']
    exact Measure.pi_map_piCongrLeft e.symm (fun _ : ι => μ)
  have heq : (fun x : ι → ℝ => w (∑ i, x i)) = (fun x => w (∑ i, x i)) ∘ r := by
    funext x
    exact congrArg w (Equiv.sum_comp e x).symm
  change ((Measure.pi fun _ : ι => μ).withDensity _).map r = _
  calc
    _ = ((Measure.pi fun _ : ι => μ).withDensity
        ((fun x => w (∑ i, x i)) ∘ r)).map r := by conv_lhs => rw [heq]
    _ = ((Measure.pi fun _ : ι => μ).map r).withDensity
        (fun x => w (∑ i, x i)) := map_withDensity_comp_aux _ hr hs
    _ = _ := by rw [hmap]

/-- The finite-dimensional bridge increment density on a strict initial grid. -/
theorem map_increments_stableBridgeLaw {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (ha : 0 < a) (ha1 : a < 1) (n : ℕ)
    (t : Fin (n + 1) → Set.Icc (0 : ℝ) a) (ht : StrictMono t)
    (ht0 : (t 0 : ℝ) = 0) (htn : (t (Fin.last n) : ℝ) = a) :
    (stableBridgeLaw θ : Measure (D 1 ℝ)).map
        (fun f i =>
          f ⟨t i.succ, (t i.succ).2.1, (t i.succ).2.2.trans ha1.le⟩ -
          f ⟨t i.castSucc, (t i.castSucc).2.1, (t i.castSucc).2.2.trans ha1.le⟩) =
      (Measure.pi (fun i : Fin n =>
        (stableLawAt θ ((t i.succ : ℝ) - t i.castSucc) : Measure ℝ))).withDensity
          (fun x => ENNReal.ofReal
            (stableDensityAt θ (1 - a) (-(∑ i, x i)) / Scalar.stableDensity θ 0)) := by
  let inc : D a ℝ → (Fin n → ℝ) := fun f i => f (t i.succ) - f (t i.castSucc)
  have hi : Measurable inc := Measurable.of_eval fun i =>
    (measurable_eval _).sub (measurable_eval _)
  change (stableBridgeLaw θ : Measure (D 1 ℝ)).map (inc ∘ restrict ha1.le) = _
  rw [← Measure.map_map hi (measurable_restrict _),
    map_restrict_stableBridgeLaw hθ ha ha1]
  exact map_increments_bridgePrefixLaw hθ ha
    (isStableLevyLaw_stableProcessLaw hθ ha) n t ht ht0 htn

end BGW.StableTrees
