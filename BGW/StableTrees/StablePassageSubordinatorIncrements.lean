/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StablePassageSubordinator

/-!
# Independent increments of the passage subordinator

This module upgrades the strong-Markov factorization at one level to arbitrary finite
strictly increasing level grids (J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996,
Chapter VII, Theorem 1).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees

private lemma measurable_passageTime_stopped_of_le {a b : ℝ≥0} (hab : a ≤ b) :
    Measurable[(isStoppingTime_firstPassageBelow b).measurableSpace] (passageTime a) := by
  have hm := (isStoppingTime_firstPassageBelow a).measurable.untopD 0
  exact hm.mono (IsStoppingTime.measurableSpace_mono (isStoppingTime_firstPassageBelow a)
    (isStoppingTime_firstPassageBelow b) (fun f => firstPassageBelow_mono f hab)) le_rfl

/-- **Independent increments** over a strictly increasing level grid. -/
theorem firstPassage_map_increments {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (k : ℕ)
    (x : Fin (k + 1) → ℝ≥0) (hx : StrictMono x) :
    Measure.map (fun f : DLoc => fun i : Fin k =>
        ((passageTime (x i.succ) f : ℝ≥0) : ℝ) - (passageTime (x i.castSucc) f : ℝ))
        (stableLocalLaw θ : Measure DLoc) =
      Measure.pi (fun i : Fin k => passageLaw θ (x i.succ - x i.castSucc)) := by
  induction k with
  | zero =>
      rw [Measure.pi_of_empty]
      have hc : (fun f : DLoc => fun i : Fin 0 =>
          ((passageTime (x i.succ) f : ℝ≥0) : ℝ) -
            (passageTime (x i.castSucc) f : ℝ)) =
          fun _ => (isEmptyElim : Fin 0 → ℝ) := by
        funext f i
        exact Fin.elim0 i
      rw [hc, Measure.map_const, measure_univ, one_smul]
  | succ k ih =>
      let a : ℝ≥0 := x (Fin.last k).castSucc
      let b : ℝ≥0 := x (Fin.last k).succ
      let d : ℝ≥0 := b - a
      have hab : a ≤ b := hx.monotone (Fin.le_last _)
      have had : a + d = b := add_tsub_cancel_of_le hab
      let z : Fin (k + 1) → ℝ≥0 := fun i => x i.castSucc
      have hz : StrictMono z := hx.comp Fin.strictMono_castSucc
      let F : DLoc → (Fin (k + 1) → ℝ) := fun f i =>
        ((passageTime (x i.succ) f : ℝ≥0) : ℝ) - (passageTime (x i.castSucc) f : ℝ)
      let G : DLoc → (Fin k → ℝ) := fun f i =>
        ((passageTime (z i.succ) f : ℝ≥0) : ℝ) - (passageTime (z i.castSucc) f : ℝ)
      have hFm : Measurable F := Measurable.of_eval fun i =>
        (measurable_passageTime _).coe_nnreal_real.sub (measurable_passageTime _).coe_nnreal_real
      have hGm : Measurable G := Measurable.of_eval fun i =>
        (measurable_passageTime _).coe_nnreal_real.sub (measurable_passageTime _).coe_nnreal_real
      let _ (i : Fin (k + 1)) : IsProbabilityMeasure (passageLaw θ (x i.succ - x i.castSucc)) :=
        passageLaw_isProbabilityMeasure hθ _
      refine (Measure.pi_eq fun S hS => ?_).symm
      let A : Set DLoc := ⋂ i : Fin k, {f : DLoc | G f i ∈ S i.castSucc}
      have hGm_stop (u : Fin (k + 1)) : Measurable[
          (isStoppingTime_firstPassageBelow a).measurableSpace] (passageTime (z u)) := by
        apply measurable_passageTime_stopped_of_le
        apply hx.monotone
        exact Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last _)
      have hA : MeasurableSet[(isStoppingTime_firstPassageBelow a).measurableSpace] A := by
        apply MeasurableSet.iInter
        intro i
        exact ((hGm_stop i.succ).coe_nnreal_real.sub
          (hGm_stop i.castSucc).coe_nnreal_real) (hS i.castSucc)
      have hlastS : MeasurableSet (S (Fin.last k)) := hS _
      have hfactor := measure_inter_passageIncrement hθ a d hA hlastS
      let _ (i : Fin k) : IsProbabilityMeasure (passageLaw θ (z i.succ - z i.castSucc)) :=
        passageLaw_isProbabilityMeasure hθ _
      have hi := ih z hz
      have hAG := congrArg (fun μ : Measure (Fin k → ℝ) =>
        μ (Set.univ.pi fun i : Fin k => S i.castSucc)) hi
      rw [Measure.map_apply hGm (MeasurableSet.univ_pi fun i => hS i.castSucc),
        Measure.pi_pi (fun i : Fin k => passageLaw θ (z i.succ - z i.castSucc))
          (fun i => S i.castSucc)] at hAG
      have hmap : Measure.map F (stableLocalLaw θ : Measure DLoc) (Set.univ.pi S) =
          (stableLocalLaw θ : Measure DLoc)
            (A ∩ {f | ((passageTime (a + d) f : ℝ≥0) : ℝ) - (passageTime a f : ℝ) ∈
              S (Fin.last k)}) := by
        rw [Measure.map_apply hFm (MeasurableSet.univ_pi hS)]
        apply measure_congr
        filter_upwards [] with f
        apply propext
        simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
          Set.mem_inter_iff, A, Set.mem_iInter, Set.mem_ofPred_eq]
        constructor
        · intro hf
          constructor
          · intro i
            have hi := hf i.castSucc
            simpa only [F, G, z, Fin.succ_castSucc] using hi
          · have hl := hf (Fin.last k)
            simpa only [F, a, b, d, had] using hl
        · rintro ⟨hf, hl⟩ i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa only [F, a, b, d, had] using hl
          · have hj := hf j
            simpa only [F, G, z, Fin.succ_castSucc] using hj
      rw [hmap, hfactor]
      have hset : G ⁻¹' (Set.univ.pi fun i : Fin k => S i.castSucc) = A := by
        ext f
        simp [A]
      rw [hset] at hAG
      have hA' : (stableLocalLaw θ : Measure DLoc) A =
          ∏ i : Fin k, passageLaw θ (x i.succ.castSucc - x i.castSucc.castSucc) (S i.castSucc) := by
        simpa only [z, Fin.succ_castSucc] using hAG
      rw [hA', Fin.prod_univ_castSucc]
      simp only [Fin.succ_castSucc]
      rfl

end BGW.StableTrees
