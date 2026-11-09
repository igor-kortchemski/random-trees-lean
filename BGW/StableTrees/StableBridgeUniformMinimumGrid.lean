/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableBridgeMinimum
public import BGW.StableTrees.StableBridgeClosed
public import BGW.Skorokhod.VervaatMeasurable
public import BGW.StableTrees.StableBridgeUniformMinimumDensity
public import BGW.StableTrees.StableBridgeUniformMinimumFinite
public import BGW.StableTrees.StableBridgeUniformMinimumCycle

/-!
# Finite grids for the minimum time of the stable bridge

The closed stable bridge has cyclically invariant grid increments and an atomless
minimum time. Cyclic invariance follows by composing full reversal with reversal
of the strict prefix. These are the finite-grid inputs to the uniform minimum-time law.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter VIII (Vervaat's
transformation and the uniform law of the minimum time); L. Chaumont, *Excursion normalisée,
méandre et pont pour les processus de Lévy stables*, Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace BGW.StableTrees

open BGW.Skorokhod

/-- The grid time `i/N` in `[0,1]` (`N = M + 1`, `i ≤ N` as a natural number). -/
noncomputable def gridTime (M i : ℕ) : Set.Icc (0 : ℝ) 1 :=
  Set.projIcc 0 1 zero_le_one ((i : ℝ) / (M + 1))

/-- Grid increments `f((i+1)/N) - f(i/N)`, `i < N`. -/
noncomputable def gridIncr (M : ℕ) (f : D 1 ℝ) (i : Fin (M + 1)) : ℝ :=
  f (gridTime M (i + 1)) - f (gridTime M i)

/-- Grid times have the prescribed coordinates before clipping becomes necessary. -/
theorem gridTime_coe (M i : ℕ) (hi : i ≤ M + 1) :
    (gridTime M i : ℝ) = (i : ℝ) / (M + 1) := by
  have hden : (0 : ℝ) < M + 1 := by positivity
  exact congrArg Subtype.val (projIcc_of_mem zero_le_one
    ⟨div_nonneg (Nat.cast_nonneg _) hden.le, (div_le_one hden).mpr (by exact_mod_cast hi)⟩)

/-- The first grid time is zero. -/
@[simp] theorem gridTime_zero (M : ℕ) :
    gridTime M 0 = ⟨0, le_rfl, zero_le_one⟩ := by
  apply Subtype.ext
  simp [gridTime]

/-- The terminal grid time is one. -/
@[simp] theorem gridTime_last (M : ℕ) :
    gridTime M (M + 1) = ⟨1, zero_le_one, le_rfl⟩ := by
  apply Subtype.ext
  rw [gridTime_coe M (M + 1) le_rfl]
  push_cast
  exact div_self (by positivity)

/-- Evaluation of the complete grid-increment vector is measurable. -/
theorem measurable_gridIncr (M : ℕ) : Measurable (gridIncr M) :=
  Measurable.of_eval fun i =>
    (measurable_eval (gridTime M (i + 1))).sub (measurable_eval (gridTime M i))

/-- The sum of the grid increments is the terminal displacement. -/
theorem sum_gridIncr (M : ℕ) (f : D 1 ℝ) :
    ∑ i, gridIncr M f i = f ⟨1, zero_le_one, le_rfl⟩ - f ⟨0, le_rfl, zero_le_one⟩ := by
  have htel (n : ℕ) :
      (∑ i : Fin n, (f (gridTime M (i + 1)) - f (gridTime M i))) =
        f (gridTime M n) - f (gridTime M 0) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      ring
  simpa [gridIncr] using htel (M + 1)

/-- The bridge increment vector lies on the zero-sum hyperplane almost surely. -/
theorem stableBridgeLaw_ae_sum_gridIncr {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (M : ℕ) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)), ∑ i, gridIncr M f i = 0 := by
  filter_upwards [stableBridgeLaw_endpoints hθ] with f hf
  rw [sum_gridIncr, hf.1, hf.2.1, sub_self]

private theorem gridTime_reflect (M j : ℕ) (hj : j ≤ M + 1) :
    (⟨1 - (gridTime M j : ℝ), by
      constructor <;> linarith [(gridTime M j).2.1, (gridTime M j).2.2]⟩ :
        Set.Icc (0 : ℝ) 1) = gridTime M (M + 1 - j) := by
  apply Subtype.ext
  simp only [gridTime_coe M j hj, gridTime_coe M _ (Nat.sub_le _ _)]
  rw [Nat.cast_sub hj, Nat.cast_add, Nat.cast_one]
  field_simp

/-- Reversing all coordinates preserves the bridge grid-increment law. -/
theorem bridge_gridIncr_reverse {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (M : ℕ) :
    (stableBridgeLaw θ : Measure (D 1 ℝ)).map (fun f i => gridIncr M f i.rev) =
      (stableBridgeLaw θ : Measure (D 1 ℝ)).map (gridIncr M) := by
  have hc : ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)),
      ∀ i : Fin (M + 2), Function.leftLim f (gridTime M i) = f (gridTime M i) :=
    ae_all_iff.mpr fun i => stableBridgeLaw_ae_leftLim_eq hθ _
  have heq : (fun f i => gridIncr M f i.rev) =ᵐ[
      (stableBridgeLaw θ : Measure (D 1 ℝ))] (gridIncr M) ∘ reverseBridge := by
    filter_upwards [hc] with f hf
    funext i
    change f (gridTime M (i.rev + 1)) - f (gridTime M i.rev) =
      reverseBridge f (gridTime M (i + 1)) - reverseBridge f (gridTime M i)
    rw [reverseBridge_apply, reverseBridge_apply, gridTime_reflect M _ (by omega),
      gridTime_reflect M _ (by omega)]
    have h₁ : M + 1 - (i.val + 1) = i.rev.val := by simp [Fin.val_rev]
    have h₂ : M + 1 - i.val = i.rev.val + 1 := by simp [Fin.val_rev]; omega
    rw [h₁, h₂, hf ⟨i.rev, by omega⟩, hf ⟨i.rev + 1, by omega⟩]
    ring
  rw [Measure.map_congr heq, ← Measure.map_map (measurable_gridIncr M)
    measurable_reverseBridge, map_reverseBridge_stableBridgeLaw hθ]

/-- The increments preceding the terminal grid interval are exchangeable. -/
theorem bridge_first_gridIncr_perm {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (M : ℕ)
    (hM : 0 < M) (e : Equiv.Perm (Fin M)) :
    (stableBridgeLaw θ : Measure (D 1 ℝ)).map
        (fun f i => gridIncr M f (e i).castSucc) =
      (stableBridgeLaw θ : Measure (D 1 ℝ)).map
        (fun f (i : Fin M) => gridIncr M f i.castSucc) := by
  let d : ℝ := M + 1
  have hd : 0 < d := by dsimp [d]; positivity
  let a : ℝ := M / d
  have ha : 0 < a := div_pos (Nat.cast_pos.mpr hM) hd
  have ha1 : a < 1 := (div_lt_one hd).mpr (by dsimp [d]; linarith)
  let t : Fin (M + 1) → Set.Icc (0 : ℝ) a := fun i =>
    ⟨(i : ℝ) / d, div_nonneg (Nat.cast_nonneg _) hd.le,
      div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_of_lt_succ i.isLt) hd.le⟩
  have ht : StrictMono t := fun i j hij =>
    div_lt_div_of_pos_right (by exact_mod_cast hij) hd
  have ht0 : (t 0 : ℝ) = 0 := by simp [t]
  have htn : (t (Fin.last M) : ℝ) = a := by simp [t, a]
  have hdt (i : Fin M) : (t i.succ : ℝ) - t i.castSucc = 1 / d := by
    simp only [t, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    ring
  have htime (i : Fin (M + 1)) :
      (⟨t i, (t i).2.1, (t i).2.2.trans ha1.le⟩ : Set.Icc (0 : ℝ) 1) =
        gridTime M i := by
    apply Subtype.ext
    exact (gridTime_coe M i (by omega)).symm
  have hv : (fun (f : D 1 ℝ) (i : Fin M) =>
        f ⟨t i.succ, (t i.succ).2.1, (t i.succ).2.2.trans ha1.le⟩ -
        f ⟨t i.castSucc, (t i.castSucc).2.1, (t i.castSucc).2.2.trans ha1.le⟩) =
      fun f i => gridIncr M f i.castSucc := by
    funext f i
    rw [htime, htime]
    rfl
  have hfdd := map_increments_stableBridgeLaw hθ ha ha1 M t ht ht0 htn
  rw [hv] at hfdd
  simp_rw [hdt] at hfdd
  let w : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal
    (stableDensityAt θ (1 - a) (-s) / Scalar.stableDensity θ 0)
  have hw : Measurable w :=
    (((stableDensityAt_continuous hθ).measurable.comp measurable_neg).div_const _).ennreal_ofReal
  have hfirst : Measurable (fun (f : D 1 ℝ) (i : Fin M) => gridIncr M f i.castSucc) :=
    Measurable.of_eval fun i => (measurable_pi_apply i.castSucc).comp (measurable_gridIncr M)
  have he : Measurable (fun (x : Fin M → ℝ) i => x (e i)) :=
    Measurable.of_eval fun i => measurable_pi_apply (e i)
  change (stableBridgeLaw θ : Measure (D 1 ℝ)).map
    ((fun (x : Fin M → ℝ) i => x (e i)) ∘
      (fun f i => gridIncr M f i.castSucc)) = _
  rw [← Measure.map_map he hfirst, hfdd]
  exact map_pi_withDensity_sum_perm (stableLawAt θ (1 / d) : Measure ℝ) hw e

/-- Exchangeability of the bridge increments under cyclic shifts of the grid. -/
theorem bridge_gridIncr_cyclic {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (M : ℕ) (k : Fin (M + 1)) :
    (stableBridgeLaw θ : Measure (D 1 ℝ)).map (fun f i => gridIncr M f (i + k)) =
      (stableBridgeLaw θ : Measure (D 1 ℝ)).map (fun f i => gridIncr M f i) := by
  let μ := (stableBridgeLaw θ : Measure (D 1 ℝ)).map (gridIncr M)
  have hi := measurable_gridIncr M
  have hsum : ∀ᵐ x ∂μ, ∑ i, x i = 0 := by
    apply (ae_map_iff hi.aemeasurable ?_).mpr (stableBridgeLaw_ae_sum_gridIncr hθ M)
    exact (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
      (measurableSet_singleton 0)
  have hr : μ.map (fun x i => x i.rev) = μ := by
    dsimp only [μ]
    rw [Measure.map_map (Measurable.of_eval
      fun i : Fin (M + 1) => measurable_pi_apply i.rev) hi]
    exact bridge_gridIncr_reverse hθ M
  have hp : (μ.map (fun x (i : Fin M) => x i.castSucc)).map
      (fun x i => x i.rev) = μ.map (fun x (i : Fin M) => x i.castSucc) := by
    by_cases hM : M = 0
    · subst M
      have hz : (fun (x : Fin 0 → ℝ) i => x i.rev) = id := by
        funext x i
        exact Fin.elim0 i
      rw [hz, Measure.map_id]
    · have hf : Measurable (fun (x : Fin (M + 1) → ℝ) (i : Fin M) => x i.castSucc) :=
        Measurable.of_eval fun i => measurable_pi_apply i.castSucc
      have hrev : Measurable (fun (x : Fin M → ℝ) (i : Fin M) => x i.rev) :=
        Measurable.of_eval fun i : Fin M => measurable_pi_apply i.rev
      dsimp only [μ]
      rw [Measure.map_map hf hi, Measure.map_map hrev (hf.comp hi)]
      exact bridge_first_gridIncr_perm hθ M (Nat.pos_of_ne_zero hM) Fin.revPerm
  have hshift : Measurable (fun (x : Fin (M + 1) → ℝ) i => x (i + k)) :=
    Measurable.of_eval fun i => measurable_pi_apply (i + k)
  have h := map_cyclic_of_reverse_of_prefix_reverse M μ hsum hr hp k
  dsimp only [μ] at h
  rw [Measure.map_map hshift hi] at h
  exact h

/-- No deterministic time can be the minimum time of the stable bridge. -/
theorem stableBridgeLaw_ae_vervaatTime_ne {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)), (vervaatTime f : ℝ) ≠ x := by
  by_cases hx : 0 < x ∧ x < 1
  · filter_upwards [stableBridgeLaw_ae_prefix_unique_continuous_minimum hθ hx.1 hx.2]
      with f hf heq
    obtain ⟨g, -, hg1, -, -, huniq⟩ := hf
    have hv := min_leftLim_vervaatTime f
    have hmin := iInf_restrict_eq_of_genMin hx.1.le hx.2.le f hv heq.le
    let t : Set.Icc (0 : ℝ) x := ⟨x, hx.1.le, le_rfl⟩
    have ht : min (Function.leftLim (restrict (E := ℝ) hx.2.le f) t)
        (restrict (E := ℝ) hx.2.le f t) = ⨅ s, restrict (E := ℝ) hx.2.le f s := by
      rw [leftLim_restrict_eq hx.1.le hx.2.le, hmin]
      have hu : (⟨t, t.2.1, t.2.2.trans hx.2.le⟩ : Set.Icc (0 : ℝ) 1) =
          vervaatTime f := Subtype.ext heq.symm
      change min (Function.leftLim f _) (f _) = _
      rw [hu]
      exact hv
    have htg := congrArg Subtype.val (huniq t ht)
    change x = (g : ℝ) at htg
    linarith
  · filter_upwards [stableBridgeLaw_ae_minimum hθ] with f hf heq
    exact hx (heq ▸ hf.2.1)

/-- Values on the grid excluding the duplicate terminal endpoint. -/
noncomputable def bridgeGridValues (M : ℕ) (f : D 1 ℝ) (i : Fin (M + 1)) : ℝ :=
  f (gridTime M i)

/-- The finite-grid values are measurable. -/
theorem measurable_bridgeGridValues (M : ℕ) : Measurable (bridgeGridValues M) :=
  Measurable.of_eval fun i => measurable_eval (gridTime M i)

/-- On a loop the final grid increment wraps back to the initial value. -/
theorem gridIncr_eq_cyclicDiff {M : ℕ} {f : D 1 ℝ}
    (hf : f ⟨1, zero_le_one, le_rfl⟩ = f ⟨0, le_rfl, zero_le_one⟩) :
    gridIncr M f = cyclicDiff M (bridgeGridValues M f) := by
  funext i
  cases i using Fin.lastCases with
  | last => simp [gridIncr, cyclicDiff, bridgeGridValues, hf]
  | cast i => simp [gridIncr, cyclicDiff, bridgeGridValues]

end BGW.StableTrees
