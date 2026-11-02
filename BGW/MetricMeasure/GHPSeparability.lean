/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.MeasuredGHMetric
public import BGW.MetricMeasure.GHPFiniteApproximation
public import BGW.MetricMeasure.GHPFiniteCoding

/-!
# Separability of the whole-space GHP metric

Each measured isometry class has a representative, a finite net covering its
entire carrier, and the exact pushforward of its measure to that net. Rounded
distance and atomic-weight arrays form countably many codes. Equal codes
control the finite measured spaces and hence the original classes. This
constructs a countable basis for the existing GHP topology without discarding
zero-mass points or assuming a Polish-space result.

Adapted from `Freezing2/Geometry/GHPSeparability.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
-/

@[expose] public section

open MeasureTheory Metric TopologicalSpace

universe u

namespace BGW.MetricMeasure.MeasuredGHSpace

/-- Countable finite data reconstruct a compact measured isometry class to
any prescribed GHP accuracy. -/
theorem exists_countable_discretization (δ : ℝ) (hδ : 0 < δ) :
    ∃ (β : Type) (_ : Encodable β) (F : MeasuredGHSpace.{u} → β),
      ∀ p q, F p = F q → dist p q ≤ δ := by
  classical
  let ε : ℝ := δ / 7
  have hε : 0 < ε := div_pos hδ (by norm_num)
  let R : MeasuredGHSpace.{u} → CompactMeasuredSpace.{u} := fun p ↦ Quotient.out p
  have hR (p : MeasuredGHSpace.{u}) : toMeasuredGHSpace (R p) = p := Quotient.out_eq p
  have hnet (p : MeasuredGHSpace.{u}) := exists_finite_measurable_net (X := R p) hε
  choose s hs q hq hclose using hnet
  let (p : MeasuredGHSpace.{u}) : Nonempty ↥(s p) :=
    ⟨⟨(hs p).choose, (hs p).choose_spec⟩⟩
  let ν (p : MeasuredGHSpace.{u}) : Measure ↥(s p) := ((R p).law : Measure (R p)).map (q p)
  let E (p : MeasuredGHSpace.{u}) : ↥(s p) ≃ Fin (Fintype.card ↥(s p)) := Fintype.equivFin _
  let F : MeasuredGHSpace.{u} → Σ n : ℕ, (Fin n → Fin n → ℤ) × (Fin n → ℤ) :=
    fun p ↦ ⟨Fintype.card ↥(s p), finiteMeasuredCode (ν p) (E p) ε⟩
  refine ⟨_, inferInstance, F, ?_⟩
  intro p p' hpp'
  have hnear (z : MeasuredGHSpace.{u}) :
      ghpDistance ((R z).law : Measure (R z)) (ν z) ≤ 2 * ε :=
    ghpDistance_finite_projection_le _ (s z) (q z) (hq z) hε.le
      (fun x ↦ (hclose z x).le)
  have hmid : ghpDistance (ν p) (ν p') ≤ 3 * ε :=
    ghpDistance_le_of_sigma_finiteMeasuredCode_eq (ν p) (ν p') (E p) (E p') hε hpp'
  have hlast : ghpDistance (ν p') ((R p').law : Measure (R p')) ≤ 2 * ε := by
    rw [ghpDistance_comm]
    exact hnear p'
  have htri := ghpDistance_triangle ((R p).law : Measure (R p)) (ν p)
    ((R p').law : Measure (R p'))
  have htri' := ghpDistance_triangle (ν p) (ν p') ((R p').law : Measure (R p'))
  have hd : dist p p' =
      ghpDistance ((R p).law : Measure (R p)) ((R p').law : Measure (R p')) := by
    calc
      dist p p' = dist (toMeasuredGHSpace (R p)) (toMeasuredGHSpace (R p')) := by
        rw [hR p, hR p']
      _ = _ := rfl
  rw [hd]
  have hn := hnear p
  dsimp [ε] at hn hmid hlast htri htri'
  linarith

/-- The exact GHP topology on the source's whole-space measured-isometry
quotient is second countable. -/
noncomputable instance : SecondCountableTopology MeasuredGHSpace.{u} :=
  secondCountable_of_countable_discretization exists_countable_discretization

/-- In particular, the genuine GHP metric has a countable dense subset. -/
theorem separableSpace : SeparableSpace MeasuredGHSpace.{u} := inferInstance

end BGW.MetricMeasure.MeasuredGHSpace
