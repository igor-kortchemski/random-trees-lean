/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteForest
public import BGW.Tree.ContourBracket
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import BGW.StableTrees.HeightContinuity
public import BGW.StableTrees.ForestContour

import BGW.StableTrees.ExactContourClock

/-!
# The unpadded forest contour clock

The ordinary forest contour removes the two zero time units inserted after each
tree by the padded contour.  This file identifies the two clocks and proves
their normalized contours agree asymptotically.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.StableTrees

namespace BGW.StableTrees.ForestContour

open BGW.StableTrees.DiscreteForest BGW.PlaneTree

/-- Start of tree `r` on the unpadded clock: `2 (L r - r)`, each earlier tree of size `z`
contributing `2 (z - 1)` (zero for a singleton). -/
noncomputable def unpaddedStart (ω : ℕ → ℕ) (r : ℕ) : ℕ := 2 * (ladderTime ω r - r)

/-- The block whose unpadded interval `[2 (L r - r), 2 (L (r+1) - r - 1))` contains `m`
(singletons have empty intervals and are skipped; junk `0` when no block does). -/
noncomputable def unpaddedBlock (ω : ℕ → ℕ) (m : ℕ) : ℕ :=
  sInf {r | m < unpaddedStart ω (r + 1)}

/-- **Unpadded forest contour** at integer time `m`: the plain concatenation of the tree
contours (junk `0` off `LadderFinite`). -/
noncomputable def forestContourUnpadded (ω : ℕ → ℕ) (m : ℕ) : ℕ :=
  if LadderFinite ω then
    (blockTree ω (unpaddedBlock ω m)).contourAt (m - unpaddedStart ω (unpaddedBlock ω m))
  else 0

/-- Linear interpolation of the unpadded forest contour at integer times. -/
noncomputable def forestContourUnpaddedLin (ω : ℕ → ℕ) (s : ℝ) : ℝ :=
  (1 - (s - ⌊s⌋₊)) * (forestContourUnpadded ω ⌊s⌋₊ : ℝ) +
    (s - ⌊s⌋₊) * (forestContourUnpadded ω (⌊s⌋₊ + 1) : ℝ)

/-- The uniform distance on `[0,T]` between the normalized unpadded and padded contours, both
at time `2nt`. -/
noncomputable def forestContourUnpaddedError (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (ω : ℕ → ℕ) : ℝ :=
  ⨆ t : Set.Icc (0 : ℝ) (T : ℝ),
    |B n / n * forestContourUnpaddedLin ω (2 * (n : ℝ) * (t : ℝ)) -
      B n / n * forestContourLin ω (2 * (n : ℝ) * (t : ℝ))|

/-- The padded and unpadded starts differ by exactly `2r`. -/
theorem two_mul_ladderTime_eq_unpaddedStart {ω : ℕ → ℕ} (hω : LadderFinite ω)
    (r : ℕ) : 2 * ladderTime ω r = unpaddedStart ω r + 2 * r := by
  have h := le_ladderTime hω r
  unfold unpaddedStart
  omega

/-- The unpadded clock: tree `r` lasts `2 (z_r - 1)`, zero for a singleton. -/
theorem unpaddedStart_succ {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ) :
    unpaddedStart ω (r + 1) = unpaddedStart ω r + 2 * ((blockTree ω r).size - 1) := by
  rw [size_blockTree hω]
  have hlt := ladderTime_lt_succ hω r
  have hle := le_ladderTime hω r
  have hles := le_ladderTime hω (r + 1)
  unfold unpaddedStart
  omega

/-- The unpadded start time is monotone. -/
theorem monotone_unpaddedStart {ω : ℕ → ℕ} (hω : LadderFinite ω) :
    Monotone (unpaddedStart ω) := by
  apply monotone_nat_of_le_succ
  intro r
  rw [unpaddedStart_succ hω]
  omega

private theorem exists_unpaddedBlock_bound {ω : ℕ → ℕ}
    (hdiv : Tendsto (unpaddedStart ω) atTop atTop) (m : ℕ) :
    ∃ r, m < unpaddedStart ω (r + 1) := by
  obtain ⟨a, ha⟩ := (tendsto_atTop.1 hdiv (m + 1)).exists
  have ha0 : a ≠ 0 := by
    intro hz
    subst a
    simp [unpaddedStart, ladderTime_zero] at ha
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha0
  change m + 1 ≤ unpaddedStart ω (r + 1) at ha
  exact ⟨r, ha⟩

private theorem unpaddedBlock_end {ω : ℕ → ℕ}
    (hdiv : Tendsto (unpaddedStart ω) atTop atTop) (m : ℕ) :
    m < unpaddedStart ω (unpaddedBlock ω m + 1) := by
  exact Nat.sInf_mem (exists_unpaddedBlock_bound hdiv m)

/-- The selected unpadded block has started by the given time. -/
theorem unpaddedBlock_start {ω : ℕ → ℕ} (m : ℕ) :
    unpaddedStart ω (unpaddedBlock ω m) ≤ m := by
  by_cases hr : unpaddedBlock ω m = 0
  · simp [hr, unpaddedStart, ladderTime_zero]
  · apply Nat.le_of_not_gt
    intro hm
    have hnot : ¬m < unpaddedStart ω (unpaddedBlock ω m - 1 + 1) := by
      apply Nat.notMem_of_lt_sInf (s := {r | m < unpaddedStart ω (r + 1)})
      exact Nat.sub_lt (Nat.pos_of_ne_zero hr) Nat.zero_lt_one
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hr)] at hnot
    exact hnot hm

private theorem unpaddedBlock_eq_of_lt {ω : ℕ → ℕ} (hω : LadderFinite ω)
    (hdiv : Tendsto (unpaddedStart ω) atTop atTop) {m r : ℕ}
    (hr : unpaddedStart ω r ≤ m) (hm : m < unpaddedStart ω (r + 1)) :
    unpaddedBlock ω m = r := by
  apply le_antisymm
  · exact Nat.sInf_le hm
  · apply Nat.le_of_not_gt
    intro hqr
    have hmem := unpaddedBlock_end hdiv m
    have hmono := monotone_unpaddedStart hω
      (show unpaddedBlock ω m + 1 ≤ r by omega)
    omega

private theorem forestContourUnpadded_eq_padded {ω : ℕ → ℕ} (hω : LadderFinite ω)
    (hdiv : Tendsto (unpaddedStart ω) atTop atTop) (m : ℕ) :
    forestContourUnpadded ω m = forestContour ω (m + 2 * unpaddedBlock ω m) := by
  let r := unpaddedBlock ω m
  have hstart := unpaddedBlock_start (ω := ω) m
  have hend := unpaddedBlock_end hdiv m
  change unpaddedStart ω r ≤ m at hstart
  change m < unpaddedStart ω (r + 1) at hend
  have hclock := two_mul_ladderTime_eq_unpaddedStart hω r
  have hsucc := unpaddedStart_succ hω r
  have hsize := size_pos (blockTree ω r)
  simp only [forestContourUnpadded, hω, ↓reduceIte]
  change (blockTree ω r).contourAt (m - unpaddedStart ω r) = _
  rw [show m + 2 * r = 2 * ladderTime ω r + (m - unpaddedStart ω r) by omega,
    forestContour_two_mul_ladderTime_add hω r (by omega)]

private theorem forestContourUnpadded_succ_eq_padded {ω : ℕ → ℕ} (hω : LadderFinite ω)
    (hdiv : Tendsto (unpaddedStart ω) atTop atTop) (m : ℕ) :
    forestContourUnpadded ω (m + 1) =
      forestContour ω (m + 1 + 2 * unpaddedBlock ω m) := by
  let r := unpaddedBlock ω m
  have hstart := unpaddedBlock_start (ω := ω) m
  have hend := unpaddedBlock_end hdiv m
  change unpaddedStart ω r ≤ m at hstart
  change m < unpaddedStart ω (r + 1) at hend
  have hclock := two_mul_ladderTime_eq_unpaddedStart hω r
  have hclockSucc := two_mul_ladderTime_eq_unpaddedStart hω (r + 1)
  have hsucc := unpaddedStart_succ hω r
  have hsize := size_pos (blockTree ω r)
  by_cases hnext : m + 1 < unpaddedStart ω (r + 1)
  · have hblock : unpaddedBlock ω (m + 1) = r :=
      unpaddedBlock_eq_of_lt hω hdiv (by omega) hnext
    rw [forestContourUnpadded_eq_padded hω hdiv, hblock]
  · have heq : m + 1 = unpaddedStart ω (r + 1) := by omega
    have hstartNext := unpaddedBlock_start (ω := ω) (m + 1)
    have hendNext := unpaddedBlock_end hdiv (m + 1)
    have hrnext : r + 1 ≤ unpaddedBlock ω (m + 1) := by
      apply Nat.le_of_not_gt
      intro hlt
      by_cases hqr : unpaddedBlock ω (m + 1) = r
      · rw [hqr, heq] at hendNext
        exact (lt_irrefl _ hendNext)
      · have hle : unpaddedBlock ω (m + 1) + 1 ≤ r := by omega
        have hm := monotone_unpaddedStart hω hle
        have hbefore : ¬m < unpaddedStart ω (unpaddedBlock ω (m + 1) + 1) := by
          apply Nat.notMem_of_lt_sInf (s := {q | m < unpaddedStart ω (q + 1)})
          change unpaddedBlock ω (m + 1) < unpaddedBlock ω m
          omega
        exact hbefore (by omega)
    have hstartEq : unpaddedStart ω (unpaddedBlock ω (m + 1)) = m + 1 := by
      have hm := monotone_unpaddedStart hω hrnext
      omega
    have hunpadded : forestContourUnpadded ω (m + 1) = 0 := by
      simp only [forestContourUnpadded, hω, ↓reduceIte, hstartEq, Nat.sub_self]
      exact contourAt_zero _
    rw [hunpadded]
    have hlocal : m + 1 + 2 * r = 2 * ladderTime ω r + 2 * ((blockTree ω r).size - 1) := by
      omega
    rw [hlocal, forestContour_two_mul_ladderTime_add hω r (by omega)]
    exact (contourAt_end _).symm

/-- The total unpadded contour duration is infinite almost surely. -/
theorem ae_tendsto_unpaddedStart (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∀ᵐ ω ∂(offspringSeqLaw μ : Measure (ℕ → ℕ)), Tendsto (unpaddedStart ω) atTop atTop := by
  have hall : ∀ᵐ ω ∂(offspringSeqLaw μ : Measure (ℕ → ℕ)),
      ∀ n : ℕ, ∃ r, n ≤ (blockTree ω r).size := by
    simp_rw [ae_all_iff]
    intro n
    filter_upwards [ae_ladderFinite μ hc hne, ae_exists_long_block μ hc hne n]
      with ω hω hlong
    obtain ⟨r, hr⟩ := hlong
    exact ⟨r, by rwa [size_blockTree hω]⟩
  filter_upwards [hall, ae_ladderFinite μ hc hne] with ω hsize hω
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨r, hr⟩ := hsize (b + 1)
  refine eventually_atTop.mpr ⟨r + 1, fun q hq => ?_⟩
  have hmono := monotone_unpaddedStart hω hq
  rw [unpaddedStart_succ hω] at hmono
  have hpos := size_pos (blockTree ω r)
  change b ≤ unpaddedStart ω q
  omega

/-- **Padded/unpadded identity**: when the unpadded clock diverges, the unpadded contour at time
`s` is the padded contour at time `s + 2r`, `r = unpaddedBlock ω ⌊s⌋` the number of earlier
trees. -/
theorem forestContourUnpaddedLin_eq {ω : ℕ → ℕ} (hω : LadderFinite ω)
    (hdiv : Tendsto (unpaddedStart ω) atTop atTop) {s : ℝ} (hs : 0 ≤ s) :
    forestContourUnpaddedLin ω s =
      forestContourLin ω (s + 2 * (unpaddedBlock ω ⌊s⌋₊ : ℝ)) := by
  let r := unpaddedBlock ω ⌊s⌋₊
  have hstart := unpaddedBlock_start (ω := ω) ⌊s⌋₊
  have hend := unpaddedBlock_end hdiv ⌊s⌋₊
  change unpaddedStart ω r ≤ ⌊s⌋₊ at hstart
  change ⌊s⌋₊ < unpaddedStart ω (r + 1) at hend
  have hclock := two_mul_ladderTime_eq_unpaddedStart hω r
  have hsucc := unpaddedStart_succ hω r
  have hsize := size_pos (blockTree ω r)
  have hlocal0 : 0 ≤ s - (unpaddedStart ω r : ℝ) := by
    exact sub_nonneg.mpr ((Nat.cast_le.mpr hstart).trans (Nat.floor_le hs))
  have hlocal : forestContourLin ω (s + 2 * (r : ℝ)) =
      (blockTree ω r).contourLin (s - (unpaddedStart ω r : ℝ)) := by
    have hclockR : 2 * (ladderTime ω r : ℝ) =
        (unpaddedStart ω r : ℝ) + 2 * (r : ℝ) := by exact_mod_cast hclock
    rw [← forestContourLin_two_mul_ladderTime_add hω r hlocal0]
    · congr 1
      linarith
    · have hflt : (⌊s⌋₊ : ℝ) ≤ s := Nat.floor_le hs
      have hflts : s < (⌊s⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one s
      have hendR : (⌊s⌋₊ : ℝ) < unpaddedStart ω (r + 1) := by exact_mod_cast hend
      have hsuccR : (unpaddedStart ω (r + 1) : ℝ) = (unpaddedStart ω r : ℝ) +
          2 * ((blockTree ω r).size : ℝ) - 2 := by
        rw [hsucc]
        push_cast [Nat.cast_sub (show 1 ≤ (blockTree ω r).size by omega)]
        ring
      have hstartR : (unpaddedStart ω r : ℝ) ≤ (⌊s⌋₊ : ℝ) := by exact_mod_cast hstart
      nlinarith
  have hvalue0 : forestContourUnpadded ω ⌊s⌋₊ =
      (blockTree ω r).contourAt (⌊s⌋₊ - unpaddedStart ω r) := by
    simp only [forestContourUnpadded, hω, ↓reduceIte]
    rfl
  have hvalue1 : forestContourUnpadded ω (⌊s⌋₊ + 1) =
      (blockTree ω r).contourAt (⌊s⌋₊ + 1 - unpaddedStart ω r) := by
    rw [forestContourUnpadded_succ_eq_padded hω hdiv,
      show ⌊s⌋₊ + 1 + 2 * r = 2 * ladderTime ω r +
        (⌊s⌋₊ + 1 - unpaddedStart ω r) by omega,
      forestContour_two_mul_ladderTime_add hω r (by omega)]
  have hfloor : ⌊s - (unpaddedStart ω r : ℝ)⌋₊ = ⌊s⌋₊ - unpaddedStart ω r :=
    Nat.floor_sub_natCast s (unpaddedStart ω r)
  rw [hlocal, forestContourUnpaddedLin, contourLin, hvalue0, hvalue1, hfloor]
  have hsuccfloor : ⌊s⌋₊ + 1 - unpaddedStart ω r =
      (⌊s⌋₊ - unpaddedStart ω r) + 1 := by omega
  rw [hsuccfloor]
  have hfrac : s - (unpaddedStart ω r : ℝ) - ((⌊s⌋₊ - unpaddedStart ω r : ℕ) : ℝ) =
      s - (⌊s⌋₊ : ℝ) := by
    rw [Nat.cast_sub hstart]
    ring
  rw [hfrac]

end BGW.StableTrees.ForestContour
