/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Measurable
public import Mathlib.Probability.Process.Filtration
public import Mathlib.Probability.Process.Stopping

import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Basic tools for Aldous's tightness criterion

Bounded stopping times and the diagonal argument converting the sequence condition
into a bound uniform over stopping times and small deterministic time increments.
The remaining modules build the exit estimates and tightness criterion from these tools.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace BGW.Skorokhod

variable {T : ℝ}

/-- `τ : Ω → [0,T]` is a stopping time for `𝓕`.

Reference: Billingsley 1999, Section 16. -/
def IsStopTime {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration (Set.Icc (0 : ℝ) T) m)
    (τ : Ω → Set.Icc (0 : ℝ) T) : Prop :=
  ∀ t, MeasurableSet[𝓕 t] {ω | τ ω ≤ t}

/-- A deterministic bounded time is a stopping time.

Reference: Billingsley 1999, Section 16. -/
theorem isStopTime_const {Ω : Type*} {m : MeasurableSpace Ω}
    (𝓕 : Filtration (Set.Icc (0 : ℝ) T) m) (t : Set.Icc (0 : ℝ) T) :
    IsStopTime 𝓕 (fun _ => t) := by
  intro s
  exact MeasurableSet.const _

/-- Bounded stopping times agree with Mathlib's stopping times after coercion to `WithTop`.

Reference: Billingsley 1999, Section 16. -/
theorem isStopTime_iff_isStoppingTime {Ω : Type*} {m : MeasurableSpace Ω}
    (𝓕 : Filtration (Set.Icc (0 : ℝ) T) m) (τ : Ω → Set.Icc (0 : ℝ) T) :
    IsStopTime 𝓕 τ ↔ IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop (Set.Icc (0 : ℝ) T))) := by
  simp only [IsStopTime, IsStoppingTime, WithTop.coe_le_coe]

private theorem uniform_of_sequence {A : Type*} (a₀ : A)
    (q : ℕ → A → ℝ → ℝ≥0∞)
    (hq : ∀ a : ℕ → A, ∀ h : ℕ → ℝ, (∀ n, 0 ≤ h n) →
      Tendsto h atTop (𝓝 0) → Tendsto (fun n => q n (a n) (h n)) atTop (𝓝 0))
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ a, ∀ h : ℝ,
      0 ≤ h → h ≤ δ → q n a h ≤ η := by
  classical
  by_contra hnot
  push Not at hnot
  let d (k : ℕ) : ℝ := 1 / (k + 1)
  have hd (k : ℕ) : 0 < d k := by dsimp [d]; positivity
  have hbad : ∀ k, ∃ᶠ n in atTop, ∃ a h,
      0 ≤ h ∧ h ≤ d k ∧ η < q n a h := by
    intro k
    apply frequently_atTop.mpr
    intro N
    obtain ⟨n, hn, a, h, hh, hhd, hq⟩ := hnot (d k) (hd k) N
    exact ⟨n, hn, a, h, hh, hhd, hq⟩
  obtain ⟨v, hv, hbad⟩ := extraction_forall_of_frequently hbad
  choose a h hh hhd hlarge using hbad
  let a' := Function.extend v a (fun _ => a₀)
  let h' := Function.extend v h (fun _ => (0 : ℝ))
  have ha' (k) : a' (v k) = a k := hv.injective.extend_apply _ _ k
  have hh' (k) : h' (v k) = h k := hv.injective.extend_apply _ _ k
  have hzero (n) (hn : ¬ ∃ k, v k = n) : h' n = 0 :=
    Function.extend_apply' _ _ n hn
  have hnonneg (n) : 0 ≤ h' n := by
    by_cases hn : ∃ k, v k = n
    · obtain ⟨k, rfl⟩ := hn
      rw [hh']
      exact hh k
    · rw [hzero n hn]
  have hlim : Tendsto h' atTop (𝓝 0) := by
    refine tendsto_order.mpr ⟨?_, ?_⟩
    · intro b hb
      exact Eventually.of_forall fun n => hb.trans_le (hnonneg n)
    · intro b hb
      have hdlim : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      obtain ⟨K, hK⟩ := eventually_atTop.mp (hdlim.eventually (gt_mem_nhds hb))
      filter_upwards [eventually_ge_atTop (v K)] with n hn
      by_cases hnv : ∃ k, v k = n
      · obtain ⟨k, rfl⟩ := hnv
        rw [hh']
        exact (hhd k).trans_lt (hK k (hv.le_iff_le.mp hn))
      · rw [hzero n hnv]
        exact hb
  have hsmall := ((hq a' h' hnonneg hlim).comp hv.tendsto_atTop).eventually
    (gt_mem_nhds hη)
  obtain ⟨k, hk⟩ := hsmall.exists
  change q (v k) (a' (v k)) (h' (v k)) < η at hk
  rw [ha', hh'] at hk
  exact (not_lt_of_gt (hlarge k)) hk

/-- The sequence form of Aldous's condition gives an eventual bound uniform over
bounded stopping times and sufficiently small nonnegative deterministic increments.

Reference: Billingsley 1999, Section 16. -/
theorem exists_uniform_aldous_bound (hT : 0 < T)
    {Ω : ℕ → Type*} [m : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    (𝓕 : ∀ n, Filtration (Set.Icc (0 : ℝ) T) (m n))
    (X : ∀ n, Ω n → D T ℝ)
    (hAldous : ∀ (τ : ∀ n, Ω n → Set.Icc (0 : ℝ) T), (∀ n, IsStopTime (𝓕 n) (τ n)) →
      ∀ h : ℕ → ℝ, (∀ n, 0 ≤ h n) → Tendsto h atTop (𝓝 0) →
      ∀ ε > 0, Tendsto
        (fun n => P n {ω | ε ≤ |X n ω (Set.projIcc 0 T hT.le (τ n ω + h n)) - X n ω (τ n ω)|})
        atTop (𝓝 0))
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ τ : Ω n → Set.Icc (0 : ℝ) T,
      IsStopTime (𝓕 n) τ → ∀ h : ℝ, 0 ≤ h → h ≤ δ →
        P n {ω | ε ≤ |X n ω (Set.projIcc 0 T hT.le (τ ω + h)) - X n ω (τ ω)|} ≤
          ENNReal.ofReal η := by
  classical
  let A := {τ : ∀ n, Ω n → Set.Icc (0 : ℝ) T // ∀ n, IsStopTime (𝓕 n) (τ n)}
  let a₀ : A := ⟨fun _ _ => ⟨0, le_rfl, hT.le⟩, fun n => isStopTime_const (𝓕 n) _⟩
  let q (n : ℕ) (a : A) (h : ℝ) : ℝ≥0∞ :=
    P n {ω | ε ≤ |X n ω (Set.projIcc 0 T hT.le (a.1 n ω + h)) - X n ω (a.1 n ω)|}
  have hq : ∀ a : ℕ → A, ∀ h : ℕ → ℝ, (∀ n, 0 ≤ h n) →
      Tendsto h atTop (𝓝 0) → Tendsto (fun n => q n (a n) (h n)) atTop (𝓝 0) := by
    intro a h hh hlim
    exact hAldous (fun n => (a n).1 n) (fun n => (a n).2 n) h hh hlim ε hε
  obtain ⟨δ, hδ, N, hbound⟩ := uniform_of_sequence a₀ q hq (ENNReal.ofReal_pos.mpr hη)
  refine ⟨δ, hδ, N, fun n hn τ hτ h hh hhd => ?_⟩
  let a : A := ⟨Function.update a₀.1 n τ, by
    intro k
    by_cases hk : k = n
    · subst k
      simpa using hτ
    · simpa [Function.update_of_ne hk] using a₀.2 k⟩
  simpa [q, a] using hbound n hn a h hh hhd

end BGW.Skorokhod
