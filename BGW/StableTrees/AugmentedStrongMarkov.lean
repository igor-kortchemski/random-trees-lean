/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableStrongMarkov
public import BGW.StableTrees.ReflectedRestart
public import BGW.StableTrees.ExcursionGapsStrongMarkov
import BGW.Probability.Completion

/-!
# Strong Markov property of the reflected process for the augmented filtration

The usual augmentation of the canonical filtration under the stable law: the raw
right-continuous filtration joined with the null sets of the law, then regularized on the
right, on the completed space. Every augmented event differs from a raw event by a null set,
every augmented stopping time is almost surely equal to a raw one, and every event of an
augmented stopped σ-algebra differs from a raw stopped event by a null set (through the
stopping time equal to `τ` on the event and infinite off it). With integrals under the
completed law, this transfers the strong Markov property of the reflected process `X − I` to
stopping times of the augmented filtration (`condExp_reflectedFutureAt_augmented`, C20).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

/-- The canonical space with the completion σ-algebra of the stable law. -/
abbrev StableCompletedSpace (θ : ℝ) :=
  NullMeasurableSpace DLoc (stableLocalLaw θ : Measure DLoc)

/-- The raw right-continuous filtration joined with the null sets of the stable law. -/
noncomputable def stableAugmentedBase (θ : ℝ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (StableCompletedSpace θ)) where
  seq t := DLoc.filtration t ⊔
    MeasurableSpace.generateFrom {A : Set DLoc | (stableLocalLaw θ : Measure DLoc) A = 0}
  mono' _ _ hst := sup_le_sup (DLoc.filtration.mono hst) le_rfl
  le' t := sup_le
    (fun A hA => ((DLoc.filtration.le t) A hA).nullMeasurableSet)
    (MeasurableSpace.generateFrom_le fun _ hA => NullMeasurableSet.of_null hA)

/-- The usual augmentation of the canonical filtration under the stable law. -/
noncomputable def stableAugmentedFiltration (θ : ℝ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (StableCompletedSpace θ)) :=
  (stableAugmentedBase θ).rightCont

/-- Every null event belongs to every stage of the augmented filtration. -/
theorem measurableSet_stableAugmentedFiltration_of_null {θ : ℝ} (t : ℝ≥0) {A : Set DLoc}
    (hA : (stableLocalLaw θ : Measure DLoc) A = 0) :
    MeasurableSet[stableAugmentedFiltration θ t] A := by
  apply (stableAugmentedBase θ).le_rightCont t
  exact (show MeasurableSpace.generateFrom {N : Set DLoc |
    (stableLocalLaw θ : Measure DLoc) N = 0} ≤ stableAugmentedBase θ t from le_sup_right) A
    (MeasurableSpace.measurableSet_generateFrom hA)

/-- The raw right-continuous filtration is contained in its usual augmentation. -/
theorem stableAugmentedFiltration_le_completion (θ : ℝ) (t : ℝ≥0) :
    DLoc.filtration t ≤ stableAugmentedFiltration θ t := by
  intro A hA
  apply (stableAugmentedBase θ).le_rightCont t
  exact (show DLoc.filtration t ≤ stableAugmentedBase θ t from le_sup_left) A hA

private theorem exists_raw_ae_eq_aug {θ : ℝ} (t : ℝ≥0) {A : Set DLoc}
    (hA : MeasurableSet[stableAugmentedFiltration θ t] A) :
    ∃ B, MeasurableSet[DLoc.filtration t] B ∧
      A =ᵐ[(stableLocalLaw θ : Measure DLoc)] B := by
  let u : ℕ → ℝ≥0 := fun n => t + (n + 1 : ℝ≥0)⁻¹
  have hu (n : ℕ) : t < u n := by
    dsimp [u]
    exact lt_add_of_pos_right _ (inv_pos.mpr (by positivity))
  have hAu (n : ℕ) : MeasurableSet[stableAugmentedBase θ (u n)] A := by
    have hle : stableAugmentedFiltration θ t ≤ stableAugmentedBase θ (u n) := by
      rw [stableAugmentedFiltration, Filtration.rightCont_eq]
      exact iInf₂_le_of_le (u n) (hu n) le_rfl
    exact hle A hA
  choose B hB hAB using fun n => exists_raw_ae_eq_of_mem_sup (m := DLoc.filtration (u n))
    (stableLocalLaw θ : Measure DLoc) (A := A) (by
      exact hAu n)
  let L := Filter.limsup B atTop
  have hLv (v : ℝ≥0) (htv : t < v) : MeasurableSet[DLoc.rawFiltration v] L := by
    have hle {r : ℝ≥0} (hrv : r < v) : DLoc.filtration r ≤ DLoc.rawFiltration v := by
      rw [DLoc.filtration, Filtration.rightCont_eq]
      exact iInf₂_le_of_le v hrv le_rfl
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt
      (show 0 < (v : ℝ) - (t : ℝ) by exact sub_pos.mpr htv)
    have huN : u N < v := by
      rw [← NNReal.coe_lt_coe]
      dsimp [u]
      push_cast
      have hN' : 1 / (N + 1 : ℝ) < (v : ℝ) - (t : ℝ) := by
        simpa [one_div] using hN
      rw [one_div] at hN'
      linarith
    have hun (n : ℕ) (hn : N ≤ n) : u n ≤ u N := by
      rw [← NNReal.coe_le_coe]
      dsimp [u]
      push_cast
      gcongr
    have htail : MeasurableSet[DLoc.rawFiltration v]
        (Filter.blimsup B atTop (fun n => N ≤ n)) :=
      by
        apply @MeasurableSet.measurableSet_blimsup _ (DLoc.rawFiltration v)
        intro n hn
        exact hle ((hun n hn).trans_lt huN) _ (hB n)
    have heq : Filter.blimsup B atTop (fun n => N ≤ n) = L := by
      rw [Filter.blimsup_eq_iInf_biSup_of_nat]
      change (⋂ i, ⋃ j, ⋃ (_ : N ≤ j ∧ i ≤ j), B j) = Filter.limsup B atTop
      rw [Filter.limsup_eq_iInf_iSup_of_nat]
      simp only [iInf_eq_iInter, iSup_eq_iUnion]
      ext f
      simp only [mem_iInter, mem_iUnion]
      constructor
      · intro h m
        obtain ⟨n, ⟨hnN, hnm⟩, hf⟩ := h (max m N)
        exact ⟨n, (le_max_left _ _).trans hnm, hf⟩
      · intro h m
        obtain ⟨n, hmn, hf⟩ := h (m + N)
        exact ⟨n, ⟨by omega, by omega⟩, hf⟩
    rwa [heq] at htail
  refine ⟨L, ?_, ?_⟩
  · rw [DLoc.filtration, Filtration.rightCont_eq, MeasurableSpace.measurableSet_iInf]
    exact fun v => MeasurableSpace.measurableSet_iInf.mpr (hLv v)
  · dsimp [L]
    simp only [Filter.limsup_eq_iInf_iSup_of_nat, iInf_eq_iInter, iSup_eq_iUnion]
    have hgood : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ n, f ∈ A ↔ f ∈ B n :=
      eventually_countable_forall.2 (fun n => (hAB n).mem_iff)
    filter_upwards [hgood] with f hf
    simp only [mem_iInter, mem_iUnion]
    apply propext
    constructor
    · intro hfA m
      exact ⟨m, ⟨le_rfl, (hf m).mp hfA⟩⟩
    · intro hlim
      obtain ⟨n, ⟨-, hfB⟩⟩ := hlim 0
      exact (hf n).mpr hfB

private theorem exists_raw_stoppingTime_ae_eq {θ : ℝ}
    {τ : StableCompletedSpace θ → ℝ≥0∞}
    (hτ : IsStoppingTime (stableAugmentedFiltration θ) τ) :
    ∃ τ' : DLoc → ℝ≥0∞, IsStoppingTime DLoc.filtration τ' ∧
      τ =ᵐ[(stableLocalLaw θ : Measure DLoc)] τ' := by
  classical
  let Q := {q : ℚ // 0 ≤ q}
  let tq : Q → ℝ≥0 := fun q => Real.toNNReal q.1
  let E : Q → Set DLoc := fun q => {f | τ f < (tq q : ℝ≥0∞)}
  have hE (q : Q) : MeasurableSet[stableAugmentedFiltration θ (tq q)] (E q) :=
    hτ.measurableSet_lt (tq q)
  choose B hB hEB using fun q => exists_raw_ae_eq_aug (tq q) (hE q)
  let σ : Q → DLoc → ℝ≥0∞ := fun q f => if f ∈ B q then (tq q : ℝ≥0∞) else ⊤
  have hσ (q : Q) : IsStoppingTime DLoc.filtration (σ q) := by
    intro t
    change MeasurableSet[DLoc.filtration t] {f | σ q f ≤ (t : ℝ≥0∞)}
    by_cases hqt : tq q ≤ t
    · have heq : {f | σ q f ≤ t} = B q := by
        ext f
        by_cases hf : f ∈ B q <;> simp [σ, hqt, hf]
      rw [heq]
      exact DLoc.filtration.mono hqt _ (hB q)
    · have heq : {f | σ q f ≤ t} = ∅ := by
        ext f
        by_cases hf : f ∈ B q <;> simp [σ, hqt, hf]
      rw [heq]
      exact @MeasurableSet.empty _ (DLoc.filtration t)
  let τ' : DLoc → ℝ≥0∞ := fun f => ⨅ q, σ q f
  have hτ' : IsStoppingTime DLoc.filtration τ' := IsStoppingTime.iInf hσ
  refine ⟨τ', hτ', ?_⟩
  have hEB' (q : Q) : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (f ∈ E q ↔ f ∈ B q) := (hEB q).mem_iff
  have hgood : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ q, f ∈ E q ↔ f ∈ B q :=
    eventually_countable_forall.2 hEB'
  filter_upwards [hgood] with f hf
  apply le_antisymm
  · refine le_iInf fun q => ?_
    by_cases hfB : f ∈ B q
    · rw [show σ q f = (tq q : ℝ≥0∞) from ite_eq_left hfB]
      exact ((hf q).mpr hfB).le
    · rw [show σ q f = ⊤ from ite_eq_right hfB]
      exact le_top
  · refine le_of_forall_gt fun a ha => ?_
    obtain ⟨q, hq0, hτq, hqa⟩ := ENNReal.lt_iff_exists_rat_btwn.mp ha
    let q' : Q := ⟨q, hq0⟩
    change τ f < (tq q' : ℝ≥0∞) at hτq
    change (tq q' : ℝ≥0∞) < a at hqa
    have hfB : f ∈ B q' := (hf q').mp hτq
    calc
      τ' f ≤ σ q' f := iInf_le _ q'
      _ = (tq q' : ℝ≥0∞) := ite_eq_left hfB
      _ < a := hqa

private theorem aug_congr_of_ae_eq {θ : ℝ} (t : ℝ≥0) {A B : Set DLoc}
    (hB : MeasurableSet[stableAugmentedFiltration θ t] B)
    (hAB : A =ᵐ[(stableLocalLaw θ : Measure DLoc)] B) :
    MeasurableSet[stableAugmentedFiltration θ t] A := by
  obtain ⟨hAB', hBA'⟩ := ae_eq_set.mp hAB
  have hBA : MeasurableSet[stableAugmentedFiltration θ t] (B \ A) :=
    measurableSet_stableAugmentedFiltration_of_null t hBA'
  have hAB : MeasurableSet[stableAugmentedFiltration θ t] (A \ B) :=
    measurableSet_stableAugmentedFiltration_of_null t hAB'
  have hset : B \ (B \ A) ∪ (A \ B) = A := by
    ext f
    simp only [Set.mem_union, Set.mem_sdiff]
    tauto
  rw [← hset]
  exact (hB.diff hBA).union hAB

private theorem raw_stopped_le_aug_stopped {θ : ℝ}
    {τ : StableCompletedSpace θ → ℝ≥0∞}
    (hτ : IsStoppingTime (stableAugmentedFiltration θ) τ)
    {τ' : DLoc → ℝ≥0∞} (hτ' : IsStoppingTime DLoc.filtration τ')
    (hτeq : τ =ᵐ[(stableLocalLaw θ : Measure DLoc)] τ') :
    hτ'.measurableSpace ≤ hτ.measurableSpace := by
  intro A hA
  have htime (t : ℝ≥0) : {f | τ f ≤ t} =ᵐ[(stableLocalLaw θ : Measure DLoc)]
      {f | τ' f ≤ t} := by
    filter_upwards [hτeq] with f hf
    change (τ f ≤ (t : ℝ≥0∞)) = (τ' f ≤ (t : ℝ≥0∞))
    rw [hf]
  refine ⟨?_, fun t => aug_congr_of_ae_eq t
    (stableAugmentedFiltration_le_completion θ t _ (hA.2 t)) ?_⟩
  · exact (iSup_mono fun t => stableAugmentedFiltration_le_completion θ t) _ hA.1
  · exact ae_eq_set_inter EventuallyEq.rfl (htime t)

private theorem exists_raw_stopped_ae_eq {θ : ℝ}
    {τ : StableCompletedSpace θ → ℝ≥0∞}
    (hτ : IsStoppingTime (stableAugmentedFiltration θ) τ)
    (hfin : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), τ f < ⊤)
    {τ' : DLoc → ℝ≥0∞} (hτ' : IsStoppingTime DLoc.filtration τ')
    (hτeq : τ =ᵐ[(stableLocalLaw θ : Measure DLoc)] τ')
    {A : Set DLoc} (hA : MeasurableSet[hτ.measurableSpace] A) :
    ∃ A' : Set DLoc, MeasurableSet[hτ'.measurableSpace] A' ∧
      A =ᵐ[(stableLocalLaw θ : Measure DLoc)] A' := by
  classical
  let τA : StableCompletedSpace θ → ℝ≥0∞ := A.piecewise τ (fun _ => ⊤)
  have hτA : IsStoppingTime (stableAugmentedFiltration θ) τA := by
    intro t
    convert hA.2 t using 1
    ext f
    change ((if f ∈ A then τ f else ⊤) ≤ (t : ℝ≥0∞)) ↔
      (f ∈ A ∧ τ f ≤ (t : ℝ≥0∞))
    by_cases hf : f ∈ A <;> simp [hf]
  obtain ⟨τA', hτA', hτAeq⟩ := exists_raw_stoppingTime_ae_eq hτA
  let A' : Set DLoc := {f | τA' f = τ' f} ∩ {f | τ' f < ⊤}
  have heq : MeasurableSet[hτ'.measurableSpace] {f | τA' f = τ' f} := by
    rw [show {f | τA' f = τ' f} = {f | τ' f = τA' f} from Set.ext fun _ => eq_comm]
    exact IsStoppingTime.measurableSet_eq_stopping_time hτ' hτA'
  have hA' : MeasurableSet[hτ'.measurableSpace] A' :=
    heq.inter (DLoc.measurableSet_lt_top_stopped hτ')
  refine ⟨A', hA', ?_⟩
  filter_upwards [hτeq, hτAeq, hfin] with f hfeq hAeq hf
  apply propext
  by_cases hfA : f ∈ A
  · have hτA : τA f = τ f := by simp [τA, Set.piecewise, hfA]
    have hfin' : τ' f < ⊤ := by rwa [← hfeq]
    simp only [mem_inter_iff, mem_ofPred_eq, hfA, true_iff, A']
    exact ⟨(hAeq.symm.trans (hτA.trans hfeq)), hfin'⟩
  · have hτA : τA f = ⊤ := by simp [τA, Set.piecewise, hfA]
    simp only [mem_inter_iff, mem_ofPred_eq, hfA, false_iff, A', not_and]
    intro heq
    have htop : τ' f = ⊤ := heq.symm.trans (hAeq.symm.trans hτA)
    have hfin' : τ' f < ⊤ := by rwa [← hfeq]
    rw [htop] at hfin'
    exact (lt_irrefl _ hfin').elim

/-- **C20.1, strong Markov property for the augmented filtration.**  For a stopping time of the
usual augmentation, conditionally on its stopped σ-algebra, the post-τ reflected path has the
reflected stable transition law started at its stopped reflected value. -/
theorem condExp_reflectedFutureAt_augmented {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {τ : StableCompletedSpace θ → ℝ≥0∞}
    (hτ : IsStoppingTime (stableAugmentedFiltration θ) τ)
    (hfin : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc).completion, τ f < ⊤)
    {G : DLoc → ℝ} (hG : Measurable G) (hGb : ∃ C : ℝ, ∀ p, |G p| ≤ C) :
    (stableLocalLaw θ : Measure DLoc).completion[
        fun f => G (reflectedFutureAt τ f) | hτ.measurableSpace]
      =ᵐ[(stableLocalLaw θ : Measure DLoc).completion]
      fun f => ∫ g, G (reflectedFrom (reflectedStateAt τ f) g)
        ∂(stableLocalLaw θ : Measure DLoc) := by
  let P : Measure DLoc := stableLocalLaw θ
  let Y : StableCompletedSpace θ → ℝ := fun f => G (reflectedFutureAt τ f)
  let _ : IsProbabilityMeasure P.completion :=
    ⟨(Measure.completion_apply P Set.univ).trans measure_univ⟩
  obtain ⟨τ', hτ', hτeq⟩ := exists_raw_stoppingTime_ae_eq hτ
  let Y' : DLoc → ℝ := fun f => G (reflectedFutureAt τ' f)
  let K : StableCompletedSpace θ → ℝ := fun f => ∫ g, G (reflectedFrom (reflectedStateAt τ f) g) ∂P
  let K' : DLoc → ℝ := fun f => ∫ g, G (reflectedFrom (reflectedStateAt τ' f) g) ∂P
  have hτeqc : τ =ᵐ[P.completion] τ' := hτeq
  have hfinP : ∀ᵐ f ∂P, τ f < ⊤ := hfin
  have hfin' : ∀ᵐ f ∂P, τ' f < ⊤ := by
    filter_upwards [hfinP, hτeq] with f hf heq
    rwa [← heq]
  have hYeq : Y =ᵐ[P.completion] Y' := by
    filter_upwards [hτeqc] with f hf
    exact congrArg G (congrArg
      (fun s : ℝ≥0∞ => reflectedFutureAt (fun _ : DLoc => s) f) hf)
  have hKeq : K =ᵐ[P.completion] K' := by
    filter_upwards [hτeqc] with f hf
    exact congrArg
      (fun s : ℝ≥0∞ => ∫ g, G (reflectedFrom
        (reflectedStateAt (fun _ : DLoc => s) f) g) ∂P) hf
  have hstate : Measurable (reflectedStateAt τ') := by
    apply Measurable.subtype_mk
    exact measurable_reflectedFrom_eval.comp
      (measurable_const.prodMk (measurable_id.prodMk hτ'.measurable'.ennreal_toNNReal))
  have hY'm : Measurable Y' := by
    exact hG.comp (measurable_reflectedFrom.comp
      (hstate.prodMk (DLoc.measurable_shiftAt hτ')))
  have hK : StronglyMeasurable (fun y : ℝ≥0 => ∫ g, G (reflectedFrom y g) ∂P) :=
    (hG.comp measurable_reflectedFrom).stronglyMeasurable.integral_prod_right'
  have hK'm : Measurable K' := (hK.comp_measurable hstate).measurable
  obtain ⟨C, hC⟩ := hGb
  have hKb (y : ℝ≥0) : ‖∫ g, G (reflectedFrom y g) ∂P‖ ≤ C := by
    simpa using (norm_integral_le_of_norm_le_const (μ := P)
      (Eventually.of_forall fun g => (show ‖G (reflectedFrom y g)‖ ≤ C by
        simpa only [Real.norm_eq_abs] using hC _)))
  have hraw_le : DLoc.instMeasurableSpace ≤
      (inferInstance : MeasurableSpace (StableCompletedSpace θ)) :=
    fun _ hA => hA.nullMeasurableSet
  have hY'c : AEStronglyMeasurable (fun f : StableCompletedSpace θ => Y' f) P.completion :=
    (hY'm.mono hraw_le le_rfl).aestronglyMeasurable
  have hK'c : AEStronglyMeasurable (fun f : StableCompletedSpace θ => K' f) P.completion :=
    (hK'm.mono hraw_le le_rfl).aestronglyMeasurable
  have hY'intP : Integrable Y' P :=
    Integrable.of_bound hY'm.aestronglyMeasurable C
      (Eventually.of_forall fun f => by simpa only [Real.norm_eq_abs, Y'] using hC _)
  have hY'intc : Integrable (fun f : StableCompletedSpace θ => Y' f) P.completion :=
    Integrable.of_bound hY'c C (Eventually.of_forall fun f => by
      simpa only [Real.norm_eq_abs, Y'] using hC _)
  have hK'intc : Integrable (fun f : StableCompletedSpace θ => K' f) P.completion :=
    Integrable.of_bound hK'c C (Eventually.of_forall fun f => hKb (reflectedStateAt τ' f))
  have hYint : Integrable Y P.completion := hY'intc.congr hYeq.symm
  have hKint : Integrable K P.completion := hK'intc.congr hKeq.symm
  have hG1 := condExp_reflectedFutureAt hθ hτ' hfin' hG ⟨C, hC⟩
  have hK'stop : AEStronglyMeasurable[hτ'.measurableSpace] K' P :=
    stronglyMeasurable_condExp.aestronglyMeasurable.congr hG1
  have hK'aug : AEStronglyMeasurable[hτ.measurableSpace]
      (fun f : StableCompletedSpace θ => K' f) P.completion := by
    let hmono := hK'stop.mono (raw_stopped_le_aug_stopped hτ hτ' hτeq)
    exact ⟨hmono.mk K', hmono.stronglyMeasurable_mk, hmono.ae_eq_mk⟩
  have hKmeas : AEStronglyMeasurable[hτ.measurableSpace] K P.completion :=
    hK'aug.congr hKeq.symm
  apply (ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le hYint
    (fun _ _ _ => hKint.integrableOn) (fun A hA _ => ?_) hKmeas).symm
  symm
  obtain ⟨A', hA', hAA'⟩ := exists_raw_stopped_ae_eq hτ hfinP hτ' hτeq hA
  have hA'g : MeasurableSet A' := hτ'.measurableSpace_le _ hA'
  have hAg : MeasurableSet A := hτ.measurableSpace_le _ hA
  have hAA'c : A =ᵐ[P.completion] A' := hAA'
  calc
    _ = ∫ f in A', Y f ∂P.completion := setIntegral_congr_set hAA'c
    _ = ∫ f in A', Y' f ∂P.completion := setIntegral_congr_ae hA'g.nullMeasurableSet
      (hYeq.mono fun _ hf _ => hf)
    _ = ∫ f in A', Y' f ∂P := setIntegral_completion P hA'g hY'm.aestronglyMeasurable
    _ = ∫ f in A', (P[Y' | hτ'.measurableSpace]) f ∂P :=
      (setIntegral_condExp hτ'.measurableSpace_le hY'intP hA').symm
    _ = ∫ f in A', K' f ∂P := setIntegral_congr_ae hA'g (hG1.mono fun _ hf _ => hf)
    _ = ∫ f in A', K' f ∂P.completion :=
      (setIntegral_completion P hA'g hK'm.aestronglyMeasurable).symm
    _ = ∫ f in A, K' f ∂P.completion := setIntegral_congr_set hAA'c.symm
    _ = _ := setIntegral_congr_ae hAg (hKeq.symm.mono fun _ hf _ => hf)

end BGW.StableTrees
