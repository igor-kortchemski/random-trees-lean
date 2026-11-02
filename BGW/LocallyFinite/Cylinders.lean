/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.LocallyFinite.Topology
public import Mathlib.Data.Finset.Preimage
public import Mathlib.MeasureTheory.Constructions.Cylinders
import Lean.Elab.Tactic.Omega

/-!
# Finite offspring cylinders and their root decomposition

After fixing the root offspring count, a finite cylinder splits into the cylinders of the children
and deterministic zero constraints at absent addresses. This is the finite-coordinate input to
the uniqueness of a branching law. Adapted from `Freezing1/PlaneTreeOffspringCylinders.lean`.
-/

@[expose] public section

namespace BGW.LocallyFinite

open MeasureTheory

/-- The cylinder fixing the offspring coordinates at the finitely many addresses of `F`. -/
def offspringCylinder (F : Finset Address) (E : Address → Set ℕ) : Set Tree :=
  {T | ∀ u ∈ F, T.val u ∈ E u}

theorem measurableSet_offspringCylinder (F : Finset Address) (E : Address → Set ℕ) :
    MeasurableSet (offspringCylinder F E) := by
  have he : offspringCylinder F E = ⋂ u : Address, ⋂ (_ : u ∈ F),
      (fun T : Tree => T.val u) ⁻¹' E u := by
    ext T
    simp [offspringCylinder]
  rw [he]
  exact MeasurableSet.iInter fun u => MeasurableSet.iInter fun _ =>
    (continuous_offspring u).measurable (by trivial)

/-- The addresses of `F` below the child `j`, with the leading `j` removed. -/
noncomputable def childIndices (F : Finset Address) (j : ℕ) : Finset Address :=
  F.preimage (List.cons j) (by intro u _ v _ h; exact (List.cons.inj h).2)

@[simp] theorem mem_childIndices (F : Finset Address) (j : ℕ) (u : Address) :
    u ∈ childIndices F j ↔ j :: u ∈ F := Finset.mem_preimage

/-- Compatibility of a root degree `k` with the root and absent-child constraints of a cylinder:
the root coordinate must be allowed, and a coordinate below an invalid child, which is zero, must
be allowed too. -/
def rootCompatible (F : Finset Address) (E : Address → Set ℕ) (k : ℕ) : Prop :=
  ∀ u ∈ F, match u with
    | [] => k ∈ E []
    | j :: v => ¬(1 ≤ j ∧ j ≤ k) → 0 ∈ E (j :: v)

theorem mem_offspringCylinder_iff_root (F : Finset Address) (E : Address → Set ℕ)
    (T : Tree) (k : ℕ) (hd : degree T = k) :
    T ∈ offspringCylinder F E ↔ rootCompatible F E k ∧
      ∀ i : Fin k, child T (i.val + 1) ∈
        offspringCylinder (childIndices F (i.val + 1)) (fun u => E ((i.val + 1) :: u)) := by
  have hd' : T.val [] = k := hd
  constructor
  · intro hT
    constructor
    · intro u hu
      cases u with
      | nil => simpa only [hd'] using hT [] hu
      | cons j u =>
          intro hj
          have hz : T.val (j :: u) = 0 :=
            T.property.zero_of_absent_child [] j (by simpa only [hd'] using hj) u
          have hh := hT (j :: u) hu
          simpa only [List.nil_append, hz] using hh
    · intro i u hu
      exact hT ((i.val + 1) :: u) ((mem_childIndices _ _ _).mp hu)
  · rintro ⟨hc, hchildren⟩ u hu
    cases u with
    | nil =>
        change degree T ∈ E []
        rw [hd]
        exact hc [] hu
    | cons j u =>
        by_cases hj : 1 ≤ j ∧ j ≤ k
        · let i : Fin k := ⟨j - 1, by omega⟩
          have he : i.val + 1 = j := by dsimp [i]; omega
          have hh := hchildren i u ((mem_childIndices _ _ _).mpr (by simpa [he] using hu))
          simpa only [child_offspring, he] using hh
        · have hz : T.val (j :: u) = 0 :=
            T.property.zero_of_absent_child [] j (by simpa only [hd'] using hj) u
          rw [show T.val (j :: u) = 0 from hz]
          exact hc (j :: u) hu hj

theorem childIndices_length_le (F : Finset Address) (n j : ℕ)
    (hF : ∀ u ∈ F, u.length ≤ n + 1) :
    ∀ u ∈ childIndices F j, u.length ≤ n := by
  intro u hu
  have hh := hF (j :: u) ((mem_childIndices _ _ _).mp hu)
  simp only [List.length_cons] at hh
  omega

end BGW.LocallyFinite
