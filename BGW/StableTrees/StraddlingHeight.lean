/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StraddlingExcursion
public import BGW.StableTrees.JointExcursion

/-!
# Height of the straddling excursion

The continuous height of the normalized excursion straddling a fixed positive time is the
normalized host height. The joint law of the normalized path and height is `excLaw`, and it is
independent of the age and lifetime of the straddling excursion.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-! ### Definition -/

/-- **Normalized host height of the straddling excursion** (C25, height part): the continuous
function `s ↦ ζ_t^{1/θ-1} H_{g_t + ζ_t s}` on `[0,1]`, with `H = heightLoc θ f` the continuous
height of the host path. -/
noncomputable def straddleHeightPath (θ : ℝ) (t : ℝ≥0) (f : DLoc) :
    C(Set.Icc (0 : ℝ) 1, ℝ) :=
  (⟨fun u : ℝ≥0 => straddleLife t f ^ (1 / θ - 1) *
      heightLoc θ f (straddleStart t f + (straddleEnd t f - straddleStart t f) * u),
    continuous_const.mul ((continuous_heightLoc θ f).comp
      (continuous_const.add (continuous_const.mul continuous_id)))⟩ : C(ℝ≥0, ℝ)).comp
    ⟨fun s => ⟨s.1, s.2.1⟩, continuous_subtype_val.subtype_mk fun s => s.2.1⟩

/-! ### Almost-sure identification -/

/-- **Locality at the straddling level**: almost surely, the host height on `[g_t, d_t]` is the
height of the straddling excursion, `H_{g_t + u} = H(e_t)(u)` for `u ≤ d_t - g_t`. -/
theorem ae_heightLoc_straddling {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0} (ht : 0 < t) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ u : ℝ≥0,
      u ≤ straddleEnd t f - straddleStart t f →
        heightLoc θ f (straddleStart t f + u) =
          excursionHeight θ (straddlingExcursion t f) u := by
  filter_upwards [ae_straddle_spec hθ ht, ae_heightLoc_jumpExcursion hθ] with f hs hl
  exact hl _ hs.1

/-- The host height vanishes at both ends `g_t` and `d_t` of the straddling excursion. -/
theorem ae_heightLoc_straddle_endpoints {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      heightLoc θ f (straddleStart t f) = 0 ∧ heightLoc θ f (straddleEnd t f) = 0 := by
  filter_upwards [ae_heightLoc_passageEndpoints_all hθ] with f h
  exact h (localTimeNN f t)

/-- **Scaling of the straddling excursion's height** (the H04 normalization identity at the
random lifetime `ζ_t`): `H(e_t)(ζ s) = ζ^{1-1/θ} H(normalizeExc e_t)(s)` for all `s`, a.s. -/
theorem ae_excursionHeight_straddling_scale {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0}
    (ht : 0 < t) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ s : ℝ≥0,
      excursionHeight θ (straddlingExcursion t f)
          ((straddlingExcursion t f).lifetime * s) =
        ((straddlingExcursion t f).lifetime : ℝ) ^ (1 - 1 / θ) *
          excursionHeight θ (normalizeExc θ (straddlingExcursion t f)) s := by
  let c : ℝ → Set.Ioi (0 : ℝ) := fun z =>
    ⟨if 0 < z then z else 1, by split_ifs with hz; exact hz; exact (zero_lt_one : (0 : ℝ) < 1)⟩
  have hc : Measurable c := by
    apply Measurable.subtype_mk
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
      measurable_id measurable_const
  let q : (ℝ × ℝ) × Excursion → Set.Ioi (0 : ℝ) × Excursion :=
    fun p => (c p.1.2, p.2)
  have hq : Measurable q :=
    (hc.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd
  have hset : MeasurableSet {p : (ℝ × ℝ) × Excursion | ∀ s : ℝ≥0,
      excursionHeight θ (excursionScale θ (q p).1 (q p).2)
          (((q p).1 : ℝ).toNNReal * s) =
        ((q p).1 : ℝ) ^ (1 - 1 / θ) * excursionHeight θ (q p).2 s} :=
    (measurableSet_excursionHeight_scale θ).preimage hq
  have hp : ∀ᵐ p ∂((straddleLaw θ t).prod (unitExcursionLaw θ : Measure Excursion)),
      ∀ s : ℝ≥0, excursionHeight θ (excursionScale θ (q p).1 (q p).2)
          (((q p).1 : ℝ).toNNReal * s) =
        ((q p).1 : ℝ) ^ (1 - 1 / θ) * excursionHeight θ (q p).2 s :=
    (MeasureTheory.Measure.ae_prod_iff_ae_ae hset).mpr
      (ae_of_all _ (fun p => ae_excursionHeight_scale_unit hθ (c p.2)))
  rw [← map_straddleData_eq_prod hθ ht] at hp
  have ha := ae_of_ae_map (aemeasurable_straddleData hθ t) hp
  filter_upwards [ha, ae_straddle_spec hθ ht] with f he hs
  let e := straddlingExcursion t f
  have hpos : 0 < straddleLife t f := by
    change 0 < (straddleEnd t f : ℝ) - (straddleStart t f : ℝ)
    exact sub_pos.mpr (by exact_mod_cast hs.2.1.trans hs.2.2.1)
  have hceq : c (straddleLife t f) = e.lifetimePos := by
    apply Subtype.ext
    change (if 0 < straddleLife t f then straddleLife t f else 1) = (e.lifetime : ℝ)
    simp only [hpos, ↓reduceIte]
    exact hs.2.2.2.2.2.1.symm
  change ∀ s : ℝ≥0, excursionHeight θ
    (excursionScale θ (c (straddleLife t f)) (normalizeExc θ e))
    (((c (straddleLife t f) : ℝ).toNNReal) * s) =
      (c (straddleLife t f) : ℝ) ^ (1 - 1 / θ) *
        excursionHeight θ (normalizeExc θ e) s at he
  rw [hceq] at he
  have hrecon : excursionScale θ e.lifetimePos (normalizeExc θ e) = e :=
    fromShapeLifetime_shapeLifetime θ e
  rw [hrecon] at he
  simpa only [Excursion.lifetimePos, Real.toNNReal_coe, e] using he

/-- **Duquesne's `pathHexc` identity** (C25, height part, pointwise form): almost surely, for
all `s ∈ [0,1]`, the height of the normalized straddling excursion is
`ζ_t^{1/θ-1} H_{g_t + ζ_t s}`. -/
theorem ae_excursionHeight_normalize_straddling {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0}
    (ht : 0 < t) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ s : ℝ≥0, s ≤ 1 →
      excursionHeight θ (normalizeExc θ (straddlingExcursion t f)) s =
        straddleLife t f ^ (1 / θ - 1) *
          heightLoc θ f (straddleStart t f + (straddleEnd t f - straddleStart t f) * s) := by
  filter_upwards [ae_heightLoc_straddling hθ ht,
    ae_excursionHeight_straddling_scale hθ ht, ae_straddle_spec hθ ht] with f hl hsc hs s hs1
  let e := straddlingExcursion t f
  have hcut : e.lifetime = straddleEnd t f - straddleStart t f :=
    excursionCut_lifetime hs.2.2.2.2.1
  have hlocal := hl ((straddleEnd t f - straddleStart t f) * s)
    (mul_le_of_le_one_right (by positivity) hs1)
  rw [← hcut] at hlocal
  have hscale := hsc s
  rw [← hlocal] at hscale
  have hpos : 0 < (e.lifetime : ℝ) := by exact_mod_cast e.lifetime_pos
  rw [← hs.2.2.2.2.2.1, ← hcut, hscale, ← mul_assoc, ← Real.rpow_add hpos]
  have hexp : (1 / θ - 1) + (1 - 1 / θ) = 0 := by ring
  rw [hexp, Real.rpow_zero, one_mul]

/-- **Pair identity**: almost surely, the J01 pair of the normalized straddling excursion is
(normalized straddling path on `[0,1]`, normalized host height). -/
theorem ae_excursionPair_normalize_straddling {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0}
    (ht : 0 < t) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      excursionPair θ 1 (normalizeExc θ (straddlingExcursion t f)) =
        (excursionRestrict 1 (normalizeExc θ (straddlingExcursion t f)),
          straddleHeightPath θ t f) := by
  filter_upwards [ae_excursionHeight_normalize_straddling hθ ht] with f h
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro s
    exact h ⟨s.1, s.2.1⟩ s.2.2

/-! ### Laws -/

/-- **C25 (height part), joint law.**  The normalized straddling path on `[0,1]` and the
normalized host height `s ↦ ζ_t^{1/θ-1} H_{g_t + ζ_t s}` have JOINTLY the law `excLaw θ` of
`(X^exc, H^exc)`. -/
theorem map_straddleHeight_eq_excLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0} (ht : 0 < t) :
    Measure.map (fun f => (excursionRestrict 1 (normalizeExc θ (straddlingExcursion t f)),
        straddleHeightPath θ t f)) (stableLocalLaw θ : Measure DLoc) =
      (excLaw θ : Measure (D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ))) := by
  have hmap :
      Measure.map (fun f => (excursionRestrict 1 (normalizeExc θ (straddlingExcursion t f)),
          straddleHeightPath θ t f)) (stableLocalLaw θ : Measure DLoc) =
        Measure.map (fun f => excursionPair θ 1 (normalizeExc θ (straddlingExcursion t f)))
          (stableLocalLaw θ : Measure DLoc) :=
    Measure.map_congr ((ae_excursionPair_normalize_straddling hθ ht).mono fun _ h => h.symm)
  have hcomp :
      Measure.map (fun f => excursionPair θ 1 (normalizeExc θ (straddlingExcursion t f)))
          (stableLocalLaw θ : Measure DLoc) =
        Measure.map (excursionPair θ 1) (Measure.map
          (fun f => normalizeExc θ (straddlingExcursion t f))
          (stableLocalLaw θ : Measure DLoc)) :=
    ((measurable_excursionPair θ 1).aemeasurable.map_map_of_aemeasurable
      (aemeasurable_straddleData hθ t).snd).symm
  have hunit :
      Measure.map (excursionPair θ 1) (Measure.map
          (fun f => normalizeExc θ (straddlingExcursion t f))
          (stableLocalLaw θ : Measure DLoc)) =
        Measure.map (excursionPair θ 1) (unitExcursionLaw θ : Measure Excursion) :=
    congrArg (Measure.map (excursionPair θ 1))
      (map_normalize_straddling_eq_unitExcursionLaw hθ ht)
  have hexc :
      Measure.map (excursionPair θ 1) (unitExcursionLaw θ : Measure Excursion) =
        (excLaw θ : Measure (D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ))) :=
    (ProbabilityMeasure.toMeasure_map (unitExcursionLaw θ)
      (f := excursionPair θ 1)).symm
  exact hmap.trans (hcomp.trans (hunit.trans hexc))

/-- Height marginal: `s ↦ ζ_t^{1/θ-1} H_{g_t + ζ_t s}` has the law of `H^exc`. -/
theorem map_straddleHeightPath_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0} (ht : 0 < t) :
    Measure.map (straddleHeightPath θ t) (stableLocalLaw θ : Measure DLoc) =
      (excLaw θ : Measure (D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ))).map Prod.snd := by
  have hp : AEMeasurable
      (fun f => excursionPair θ 1 (normalizeExc θ (straddlingExcursion t f)))
      (stableLocalLaw θ : Measure DLoc) :=
    (measurable_excursionPair θ 1).comp_aemeasurable (aemeasurable_straddleData hθ t).snd
  have hq : AEMeasurable (fun f =>
      (excursionRestrict 1 (normalizeExc θ (straddlingExcursion t f)),
        straddleHeightPath θ t f)) (stableLocalLaw θ : Measure DLoc) :=
    hp.congr (ae_excursionPair_normalize_straddling hθ ht)
  refine (measurable_snd.aemeasurable.map_map_of_aemeasurable hq).symm.trans ?_
  exact congrArg (Measure.map Prod.snd) (map_straddleHeight_eq_excLaw hθ ht)

/-- **Joint law with the age and lifetime**: `((g_t, ζ_t), (path, height))` has the product law
`straddleLaw θ t ⊗ excLaw θ` (independence of `(g_t, ζ_t)` and the normalized pair). -/
theorem map_straddleHeightData_eq_prod {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0}
    (ht : 0 < t) :
    Measure.map (fun f => (((straddleStart t f : ℝ), straddleLife t f),
        (excursionRestrict 1 (normalizeExc θ (straddlingExcursion t f)),
          straddleHeightPath θ t f))) (stableLocalLaw θ : Measure DLoc) =
      (straddleLaw θ t).prod (excLaw θ : Measure (D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ))) := by
  let k : (ℝ × ℝ) × Excursion →
      (ℝ × ℝ) × (D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ)) :=
    fun p => (p.1, excursionPair θ 1 p.2)
  have hk : Measurable k :=
    measurable_fst.prodMk ((measurable_excursionPair θ 1).comp measurable_snd)
  have hae : (fun f => (((straddleStart t f : ℝ), straddleLife t f),
      (excursionRestrict 1 (normalizeExc θ (straddlingExcursion t f)),
        straddleHeightPath θ t f))) =ᵐ[(stableLocalLaw θ : Measure DLoc)]
      (k ∘ straddleData θ t) := by
    filter_upwards [ae_excursionPair_normalize_straddling hθ ht] with f h
    exact congrArg (((straddleStart t f : ℝ), straddleLife t f), ·) h.symm
  refine (Measure.map_congr hae).trans ?_
  refine (hk.aemeasurable.map_map_of_aemeasurable
    (aemeasurable_straddleData hθ t)).symm.trans ?_
  rw [map_straddleData_eq_prod hθ ht]
  refine (Measure.map_prod_map (straddleLaw θ t) (unitExcursionLaw θ : Measure Excursion)
    measurable_id (measurable_excursionPair θ 1)).symm.trans ?_
  simp only [Measure.map_id, excLaw]
  exact congrArg (fun μ => (straddleLaw θ t).prod μ)
    (ProbabilityMeasure.toMeasure_map (unitExcursionLaw θ)
      (f := excursionPair θ 1)).symm

end BGW.StableTrees
