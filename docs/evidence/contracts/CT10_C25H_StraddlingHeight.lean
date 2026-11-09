import BGW.StableTrees.StraddlingExcursion
import BGW.StableTrees.JointExcursion

/-! Contract probe for CT10 node C25H (`CLASSICAL_THEORY_INPUTS.md` C25, height part; the item
deferred by CT7 O01 `.orchestration/contracts/CT7_O01_StraddlingExcursion.lean`, "DEFERRED (height
part, waits for H02-H04)").  Suggested maintained module: `BGW/StableTrees/StraddlingHeight.lean`,
namespace `BGW.StableTrees` (the namespace of O01, H03, H04 and J01).

SOURCE (C25(a)).  "Let `g_1 := sup{s ≤ 1 : X_s = I_s}`, `d_1 := inf{s > 1 : X_s = I_s}` and
`ζ_1 := d_1 − g_1`.  Then `(ζ_1^{−1/θ}(X_{g_1+ζ_1 s} − X_{g_1}))_{s∈[0,1]}` has the law of
`X^exc`.  Similarly, by Duquesne 2003 (pathHexc), `H^exc = (ζ_1^{1/θ−1} H_{g_1+ζ_1 s})_s`."
The path part is sealed (O01: `map_normalize_straddling_eq_unitExcursionLaw`,
`map_straddling_restrict_eq_levyExcLaw`, `indepFun_straddle_age_shape`); a fixed `t > 0`
replaces `1` as in O01.  "Similarly" is read JOINTLY: the pair (normalized path, normalized host
height) has the law `excLaw θ` of `(X^exc, H^exc)` (C22(f)), not merely each marginal.

DEFINITIONS.  Sealed: `straddleStart t f = g_t`, `straddleEnd t f = d_t`,
`straddleLife t f = d_t - g_t` (real), `straddlingExcursion t f = jumpExcursion (L_t) f
= excursionCut g_t d_t f` (all O01, definitionally), `heightLoc θ f` (H03: the continuous host
height `H`, every path continuous), `excursionHeight θ e` (H04), `excLaw θ =
(unitExcursionLaw θ).map (excursionPair θ 1)` and `excursionPair θ 1 e = (excursionRestrict 1 e,
heightRestrict 1 (excursionHeight θ e))` (J01).  New:
* `straddleHeightPath θ t f : C([0,1], ℝ)`, `s ↦ ζ_t^{1/θ-1} * H_{g_t + ζ_t s}`, with the time
  `g_t + (d_t - g_t) * s` computed in `ℝ≥0` exactly as in O01's `ae_normalize_straddling_path`,
  built as `(u ↦ …) ∘ (s ↦ ⟨s.1, s.2.1⟩ : [0,1] → ℝ≥0)`, the pattern of J01's `heightRestrict`,
  so its value at `s` unfolds by `rfl`.  Continuity is proved in the definition (no junk
  branch).  On the null event `d_t < g_t` the factor `ζ_t^{1/θ-1}` is a
  real power of a negative number; this never matters (a.s. `g_t < t < d_t`, `ae_straddle_spec`).

TRUTH CHECK (normalizations).
(1) H04 scaling: `H(S_c e)(c s) = c^{1-1/θ} H(e)(s)` (`ae_excursionHeight_scale_unit`), hence
    for an excursion of lifetime `ζ`, `H(normalizeExc e)(s) = ζ^{1/θ-1} H(e)(ζ s)`
    (`ae_excursionHeight_normalize`, under `N`).  So the exponent is `1/θ - 1 < 0` (long
    excursions are shrunk), the source's `ζ_1^{1/θ-1}`; space for the path is `ζ^{-1/θ}`.
(2) H04 locality (`ae_heightLoc_jumpExcursion`): a.s., for EVERY jump level `x` and every
    `u ≤ T_x - T_{x-}`, `H_{T_{x-} + u} = H(jumpExcursion x f)(u)`.  The straddling excursion is
    the jump excursion at the level `x = L_t`, and `L_t ∈ passageJumpSet f` a.s. (O01
    `ae_straddle_spec`), so locality applies at the random level `L_t` without any new null set.
    Hence `H_{g_t} = 0 = H_{d_t}` and `H^exc_1 = 0` match (`ae_heightLoc_straddle_endpoints`).
(3) The scaling identity of (1) holds `N`-a.e. and unit-law-a.e. for each FIXED `c`; for the
    straddling excursion `c = ζ_t` is random.  It transfers because O01 gives the PRODUCT law
    `((g_t, ζ_t), normalizeExc e_t) ~ straddleLaw θ t ⊗ unitExcursionLaw θ`
    (`map_straddleData_eq_prod`): Fubini over the jointly Borel scaling event
    (`measurableSet_excursionHeight_scale`).  This is the only probabilistic input beyond O01.
(4) `θ = 2` sanity: `H = X - I` (K17), and on `[g_t, d_t]` `I = X_{g_t}`, so
    `ζ^{-1/2} H_{g+ζ s} = ζ^{-1/2}(X_{g+ζ s} - X_g)` is the normalized path; this matches J01
    `excLaw_height_eq_path_two` (height = path at `θ = 2`).  No extra constant appears.
(5) Joint statement with `(g_t, ζ_t)`: `((g_t, ζ_t), (path, height)) ~ straddleLaw θ t ⊗ excLaw θ`
    (the O01 product law pushed by `id × excursionPair θ 1`).  This is the "joint law of the
    straddling excursion's height process with `(g, ζ)`" listed as deferred in O01.

PROOF PLAN (size 100-180 lines; (a), (b), (d), (e), (f) were proved in a scratch probe from a
`sorry`ed (c), so the only open content is (c), plus the routine (g), (h)).
(a) `ae_heightLoc_straddling`: filter `ae_straddle_spec hθ ht` (first conjunct) and
    `ae_heightLoc_jumpExcursion hθ`, apply the latter at `x = localTimeNN f t`; `straddleStart`,
    `straddleEnd`, `straddlingExcursion` unfold definitionally.  (2 lines, checked in a scratch
    probe: `filter_upwards [ae_straddle_spec hθ ht, ae_heightLoc_jumpExcursion hθ] with f hs hl;
    exact hl _ hs.1`.)
(b) `ae_heightLoc_straddle_endpoints`: `ae_heightLoc_passageEndpoints_all hθ` at `L_t`.  (2
    lines, checked in a scratch probe.)
(c) `ae_excursionHeight_straddling_scale`: as the proof of `ae_excursionHeight_normalize`, with
    `map_straddleData_eq_prod hθ ht` in place of `shapeLifetime_map_excursionMeasure`.  Pull
    `measurableSet_excursionHeight_scale θ` back along the measurable map
    `p ↦ (c p.1.2, p.2)`, `c ζ = if 0 < ζ then ⟨ζ, _⟩ else ⟨1, one_pos⟩ : Ioi (0:ℝ)`; for each
    fixed `p.1` the event holds `unitExcursionLaw`-a.e. (`ae_excursionHeight_scale_unit hθ`), so
    `Measure.ae_prod_iff_ae_ae` gives it a.e. under the product law; `ae_of_ae_map`
    (`aemeasurable_straddleData hθ t`).  Then `fromShapeLifetime_shapeLifetime θ e`
    (`excursionScale θ e.lifetimePos (normalizeExc θ e) = e`) and `ae_straddle_spec` (lifetime
    tag `= straddleLife t f > 0`) identify `c ζ_t = e_t.lifetimePos`.  (~40-80 lines)
(d) `ae_excursionHeight_normalize_straddling`: (a) at `u = (d_t - g_t) * s`
    (`mul_le_of_le_one_right`), (c) with `e_t.lifetime = d_t - g_t` (`excursionCut_lifetime`
    of the valid cut in `ae_straddle_spec`), and `ζ^{1/θ-1} ζ^{1-1/θ} = 1` (`Real.rpow_add`,
    `ζ > 0`).  (~15 lines, checked in a scratch probe from (a) and (c).)
(e) `ae_excursionPair_normalize_straddling`: `Prod.ext rfl`, `ContinuousMap.ext`, (d) at
    `⟨s.1, s.2.1⟩` with `s.2.2`.  (4 lines, checked in a scratch probe from (d).)
(f) `map_straddleHeight_eq_excLaw`: `Measure.map_congr` with (e), then
    `AEMeasurable.map_map_of_aemeasurable` (`measurable_excursionPair θ 1`,
    `(aemeasurable_straddleData hθ t).snd`), `map_normalize_straddling_eq_unitExcursionLaw hθ ht`,
    and `ProbabilityMeasure.toMeasure_map` for `excLaw`.  (~20; checked in a scratch probe
    from (d): chain with `Eq.trans`, since `rw` trips on `D ↑(1 : ℝ≥0) ℝ` vs `D 1 ℝ`.)
(g) `map_straddleHeightPath_eq`: (f) pushed by `Prod.snd` (`Measure.map_map`).  (~10)
(h) `map_straddleHeightData_eq_prod`: `Measure.map_congr` with (e) on the second component,
    `map_straddleData_eq_prod hθ ht`, `Measure.map_prod_map` with `measurable_id` and
    `measurable_excursionPair θ 1` (`isProbabilityMeasure_straddleLaw` for `SFinite`).  (~30)
RISK: none known; every step is an a.s. identity on top of sealed laws.  The height map is NOT a
continuous (or everywhere-defined measurable) functional of the host path (C26 pitfall); the
statements use only a.s. identities and `Measure.map_congr`, never measurability of
`straddleHeightPath` itself (its a.e.-measurability follows from (f)).

ACYCLICITY.  Sealed suppliers only: O01 (`StraddlingExcursion*`), H03 (`heightLoc`,
`continuous_heightLoc`), H04 (`ae_heightLoc_jumpExcursion`, `ae_heightLoc_passageEndpoints_all`,
`ae_excursionHeight_scale_unit`, `measurableSet_excursionHeight_scale`), J01 (`excLaw`,
`excursionPair`, `measurable_excursionPair`), the carrier (`fromShapeLifetime_shapeLifetime`,
`excursionCut_lifetime`).  No K-node and no E3 input.

BINDER SCOPE (AUDITOR_RULES).  No integral, sum or supremum occurs.  Products are explicit:
`straddleLife t f ^ (1 / θ - 1) * heightLoc θ f (…)` and the time `g + (d - g) * s` are
parenthesized as displayed. -/

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
          excursionHeight θ (straddlingExcursion t f) u := sorry

/-- The host height vanishes at both ends `g_t` and `d_t` of the straddling excursion. -/
theorem ae_heightLoc_straddle_endpoints {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      heightLoc θ f (straddleStart t f) = 0 ∧ heightLoc θ f (straddleEnd t f) = 0 := sorry

/-- **Scaling of the straddling excursion's height** (the H04 normalization identity at the
random lifetime `ζ_t`): `H(e_t)(ζ s) = ζ^{1-1/θ} H(normalizeExc e_t)(s)` for all `s`, a.s. -/
theorem ae_excursionHeight_straddling_scale {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0}
    (ht : 0 < t) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ s : ℝ≥0,
      excursionHeight θ (straddlingExcursion t f)
          ((straddlingExcursion t f).lifetime * s) =
        ((straddlingExcursion t f).lifetime : ℝ) ^ (1 - 1 / θ) *
          excursionHeight θ (normalizeExc θ (straddlingExcursion t f)) s := sorry

/-- **Duquesne's `pathHexc` identity** (C25, height part, pointwise form): almost surely, for
all `s ∈ [0,1]`, the height of the normalized straddling excursion is
`ζ_t^{1/θ-1} H_{g_t + ζ_t s}`. -/
theorem ae_excursionHeight_normalize_straddling {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0}
    (ht : 0 < t) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ s : ℝ≥0, s ≤ 1 →
      excursionHeight θ (normalizeExc θ (straddlingExcursion t f)) s =
        straddleLife t f ^ (1 / θ - 1) *
          heightLoc θ f (straddleStart t f + (straddleEnd t f - straddleStart t f) * s) :=
  sorry

/-- **Pair identity**: almost surely, the J01 pair of the normalized straddling excursion is
(normalized straddling path on `[0,1]`, normalized host height). -/
theorem ae_excursionPair_normalize_straddling {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0}
    (ht : 0 < t) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      excursionPair θ 1 (normalizeExc θ (straddlingExcursion t f)) =
        (excursionRestrict 1 (normalizeExc θ (straddlingExcursion t f)),
          straddleHeightPath θ t f) := sorry

/-! ### Laws -/

/-- **C25 (height part), joint law.**  The normalized straddling path on `[0,1]` and the
normalized host height `s ↦ ζ_t^{1/θ-1} H_{g_t + ζ_t s}` have JOINTLY the law `excLaw θ` of
`(X^exc, H^exc)`. -/
theorem map_straddleHeight_eq_excLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0} (ht : 0 < t) :
    Measure.map (fun f => (excursionRestrict 1 (normalizeExc θ (straddlingExcursion t f)),
        straddleHeightPath θ t f)) (stableLocalLaw θ : Measure DLoc) =
      (excLaw θ : Measure (D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ))) := sorry

/-- Height marginal: `s ↦ ζ_t^{1/θ-1} H_{g_t + ζ_t s}` has the law of `H^exc`. -/
theorem map_straddleHeightPath_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0} (ht : 0 < t) :
    Measure.map (straddleHeightPath θ t) (stableLocalLaw θ : Measure DLoc) =
      (excLaw θ : Measure (D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ))).map Prod.snd := sorry

/-- **Joint law with the age and lifetime**: `((g_t, ζ_t), (path, height))` has the product law
`straddleLaw θ t ⊗ excLaw θ` (independence of `(g_t, ζ_t)` and the normalized pair). -/
theorem map_straddleHeightData_eq_prod {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0}
    (ht : 0 < t) :
    Measure.map (fun f => (((straddleStart t f : ℝ), straddleLife t f),
        (excursionRestrict 1 (normalizeExc θ (straddlingExcursion t f)),
          straddleHeightPath θ t f))) (stableLocalLaw θ : Measure DLoc) =
      (straddleLaw θ t).prod (excLaw θ : Measure (D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ))) :=
  sorry

end BGW.StableTrees
