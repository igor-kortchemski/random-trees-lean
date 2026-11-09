import BGW.StableTrees.ExcursionLifetime
import BGW.StableTrees.ExcursionMeasure
import BGW.StableTrees.MarkedExcursions
import BGW.StableTrees.StableExcursionSupport
import BGW.StableTrees.UnitExcursionLaw
import BGW.ContinuumTrees.ExcursionCarrier

/-! Contract probe for CT7 node O01 (C25, optional CT10): the excursion of `X - I` straddling a
fixed time `t > 0`, PATH PART ONLY.  Follows `r3-ct7-blueprint/blueprint.md` §2/§4 O01/§5
(`map_normalize_straddling_eq_unitExcursionLaw`) and `CLASSICAL_THEORY_INPUTS.md` C25(a), with
the fixed time `t` of the task in place of the blueprint's `t = 1` (take `t = 1` for the blueprint).

DEFINITIONS (no new probability objects).  `L_t = localTimeNN f t`, `g_t = T_{L_t -}`,
`d_t = T_{L_t}`, `straddlingExcursion t f = jumpExcursion L_t f` (the sealed cut of `f` on
`(T_{x-}, T_x)` at `x = L_t`); junk `junkExcursion` off the good event (a null set).
`straddleAgeDensity θ g = g^{1/θ-1}/Γ(1/θ)` on `g > 0`, `straddleDensity θ t` is the claimed
density of `(g_t, ζ_t)`, `ζ_t = d_t - g_t`, on `{0 < g < t < g + ζ}`:
`straddleAgeDensity θ g * lifetimeDensity θ ζ` (sealed `lifetimeDensity`).

CONSTANTS CHECK (`α = 1/θ`).  `T` has Laplace exponent `q^α` (`E e^{-qT_x} = e^{-x q^α}`),
so its potential measure `U(ds) = ∫_0^∞ P(T_x ∈ ds) dx` has Laplace transform `q^{-α}`,
i.e. density
`s^{α-1}/Γ(α)` = `straddleAgeDensity`.  The Lévy measure of `T` is `ζ_* N` with density
`α t^{-1-α}/Γ(1-α) = p0 t^{-1-α}` (`p0 = d_θ(0) = 1/(θ Γ(1-α))`, sealed E05/E06), which is
`lifetimeDensity`.  Total mass: `∫_0^t g^{α-1}/Γ(α) * N(ζ > t-g) dg
= ∫_0^t g^{α-1} (t-g)^{-α} dg /(Γ(α)Γ(1-α)) = B(α,1-α)/(Γ(α)Γ(1-α)) = 1`.
Marginal of `g_t`:
`t^{-1} Beta(α, 1-α)(g/t)`; `θ = 2` gives the arcsine law `1/(π sqrt(g(t-g)))`.  Scaling:
`g_t/t ~ Beta(α,1-α)` independent of `t`, consistent with `(g_c t, ζ_{ct}) = c (g_t, ζ_t)`.

PROOF PLAN.  (1) a.s. facts: `L_t` is a jump level with `T_{L_t -} < t < T_{L_t}` (from
`ae_pos_set_eq_iUnion_jump_intervals`, `R_t > 0` a.s. since the zero set is null; `R = X - I`
via `reflectedFrom 0`), and the excursion intervals are disjoint (`ae_jump_intervals_disjoint`),
so the straddling level is unique.  (2) Compensation formula (sealed
`excursion_compensation_predictable_general`) applied to the predictable functional
`x ↦ 1{T_{x-} < t < T_{x-} + ζ} F(T_{x-}, ζ, shape)`, then Fubini with `P(T_{x-} = T_x) = 1` for
fixed `x`: `E F(data) = ∫dx ∫ P(T_x ∈ ds) ∫ N(de) 1{s < t < s + ζ(e)} F(s, ζ, shape e)`.
(3) `passage_potential_measure` for the `x`-integral, then the sealed joint identity
`shapeLifetime_map_excursionMeasure` (`N = lifetimeLaw ⊗ unitExcursionLaw` in shape/lifetime
coordinates) factors the shape.  (4) Corollaries.  Not used: strong Markov at `g_t`, bridge
minimum N17, C35, or any conditioning on a null event.

DEFERRED (height part, waits for H02-H04): the joint law of the straddling excursion's height
process `H^exc = (ζ^{1/θ-1} H_{g + ζ s})_s` with `(g, ζ)` (needs H04 scaling and `H_g = 0`),
and Duquesne's `pathHexc` identity.  No height declaration is stated here.

AMBIGUITIES (flagged).  (a) Blueprint writes `straddlingExcursion f` for `t = 1`; here `t > 0` is
explicit (the task asked for a fixed time).  (b) Blueprint lists no meander or first-passage
statement for O01: none is included beyond `passage_potential_measure` (the identity the proof
needs; classical, but not in the blueprint).  (c) Measurability of `straddlingExcursion t` is
claimed only as `AEMeasurable` (junk branch of `excursionCut`/`passageTimeMinus`), which is what
`Measure.map` needs; a `Measurable` modification is not claimed.  (d) The statement of
independence is for `(g_t, ζ_t)` versus the shape, not for `(g_t, d_t)` pairs of `ℝ≥0`
(equivalent by the bimeasurable bijection `(g, ζ) ↦ (g, g + ζ)`). -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-! ### Definitions -/

/-- Start `g_t = T_{L_t -}` of the excursion straddling `t`. -/
noncomputable def straddleStart (t : ℝ≥0) (f : DLoc) : ℝ≥0 :=
  passageTimeMinus (localTimeNN f t) f

/-- End `d_t = T_{L_t}` of the excursion straddling `t`. -/
noncomputable def straddleEnd (t : ℝ≥0) (f : DLoc) : ℝ≥0 :=
  passageTime (localTimeNN f t) f

/-- Lifetime `ζ_t = d_t - g_t` as a real number. -/
noncomputable def straddleLife (t : ℝ≥0) (f : DLoc) : ℝ :=
  (straddleEnd t f : ℝ) - (straddleStart t f : ℝ)

/-- The excursion of `X - I` straddling `t`: the cut of `f` at the jump level `L_t`. -/
noncomputable def straddlingExcursion (t : ℝ≥0) (f : DLoc) : Excursion :=
  jumpExcursion (localTimeNN f t) f

/-- Potential density `s^{1/θ-1}/Γ(1/θ)` of the passage subordinator, on `s > 0`. -/
noncomputable def straddleAgeDensity (θ : ℝ) (s : ℝ) : ℝ≥0∞ :=
  (Ioi (0 : ℝ)).indicator
    (fun s => ENNReal.ofReal (s ^ (1 / θ - 1) / Real.Gamma (1 / θ))) s

/-- Claimed density of `(g_t, ζ_t)` on `ℝ × ℝ`:
`straddleAgeDensity g * lifetimeDensity ζ` on `{0 < g < t < g + ζ}`. -/
noncomputable def straddleDensity (θ : ℝ) (t : ℝ≥0) (p : ℝ × ℝ) : ℝ≥0∞ :=
  {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < (t : ℝ) ∧ (t : ℝ) < p.1 + p.2}.indicator
    (fun p => straddleAgeDensity θ p.1 * lifetimeDensity θ p.2) p

/-- The claimed law of `(g_t, ζ_t)`. -/
noncomputable def straddleLaw (θ : ℝ) (t : ℝ≥0) : Measure (ℝ × ℝ) :=
  volume.withDensity (straddleDensity θ t)

/-- Claimed density of `g_t` on `ℝ`: `g^{α-1} (t-g)^{-α} / (Γ(α) Γ(1-α))` on `(0, t)`. -/
noncomputable def straddleStartDensity (θ : ℝ) (t : ℝ≥0) (g : ℝ) : ℝ≥0∞ :=
  (Ioo (0 : ℝ) (t : ℝ)).indicator
    (fun g => ENNReal.ofReal (g ^ (1 / θ - 1) * ((t : ℝ) - g) ^ (-(1 / θ)) /
      (Real.Gamma (1 / θ) * Real.Gamma (1 - 1 / θ)))) g

/-- Joint data: `((g_t, ζ_t), normalized straddling excursion)`. -/
noncomputable def straddleData (θ : ℝ) (t : ℝ≥0) (f : DLoc) : (ℝ × ℝ) × Excursion :=
  (((straddleStart t f : ℝ), straddleLife t f), normalizeExc θ (straddlingExcursion t f))

/-! ### Almost-sure path facts -/

/-- **Straddling excursion, a.s. facts** (`g_t < t < d_t`, unique straddling jump level, valid
cut, lifetime tag `d_t - g_t`, and `R_t > 0` for `R = X - I`). -/
theorem ae_straddle_spec {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0} (ht : 0 < t) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      localTimeNN f t ∈ passageJumpSet f ∧
      straddleStart t f < t ∧ t < straddleEnd t f ∧
      0 < (reflectedFrom 0 f).1 t ∧
      cutValid (straddleStart t f) (straddleEnd t f) f ∧
      ((straddlingExcursion t f).lifetime : ℝ) = straddleLife t f ∧
      ∀ x ∈ passageJumpSet f,
        t ∈ Ioo (passageTimeMinus x f) (passageTime x f) → x = localTimeNN f t := sorry

/-- **`g_t` and `d_t` as last/first zero of the reflected process** around `t`
(`R = X - I = reflectedFrom 0 f`; `g_t = sup{s ≤ t : R_s = 0}`, `d_t = inf{s > t : R_s = 0}`). -/
theorem ae_straddle_zero_description {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0}
    (ht : 0 < t) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      straddleStart t f = sSup {s : ℝ≥0 | s ≤ t ∧ (reflectedFrom 0 f).1 s = 0} ∧
      straddleEnd t f = sInf {s : ℝ≥0 | t < s ∧ (reflectedFrom 0 f).1 s = 0} := sorry

/-- **Chaumont's path formula** (C25(a), unnormalized `X`): a.s. the normalized straddling
excursion is `s ↦ ζ_t^{-1/θ} (X_{min(g_t + ζ_t s, d_t)} - X_{g_t})`. -/
theorem ae_normalize_straddling_path {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0}
    (ht : 0 < t) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ s : ℝ≥0,
      (normalizeExc θ (straddlingExcursion t f)).path.1 s =
        (straddleLife t f) ^ (-(1 / θ)) *
          (f.1 (min (straddleStart t f + (straddleEnd t f - straddleStart t f) * s)
              (straddleEnd t f)) - f.1 (straddleStart t f)) := sorry

/-! ### Measurable extraction -/

/-- The joint data of the straddling excursion is `AEMeasurable` (needed for `Measure.map`). -/
theorem aemeasurable_straddleData {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    AEMeasurable (straddleData θ t) (stableLocalLaw θ : Measure DLoc) := sorry

/-- The straddling excursion itself is `AEMeasurable`. -/
theorem aemeasurable_straddlingExcursion {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    AEMeasurable (straddlingExcursion t) (stableLocalLaw θ : Measure DLoc) := sorry

/-! ### Potential measure and joint law -/

/-- **Potential measure of the passage subordinator**: for measurable `B ⊆ ℝ`,
`∫_0^∞ P(T_x ∈ B) dx = ∫_B s^{1/θ-1}/Γ(1/θ) ds` (Laplace transform `q^{-1/θ}`). -/
theorem passage_potential_measure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {B : Set ℝ}
    (hB : MeasurableSet B) :
    ∫⁻ x in Ioi (0 : ℝ),
        (stableLocalLaw θ : Measure DLoc) {f | (passageTime x.toNNReal f : ℝ) ∈ B} =
      ∫⁻ s in B, straddleAgeDensity θ s := sorry

/-- The claimed law of `(g_t, ζ_t)` is a probability measure (Beta integral). -/
theorem isProbabilityMeasure_straddleLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0}
    (ht : 0 < t) :
    IsProbabilityMeasure (straddleLaw θ t) := sorry

/-- **Joint law** (C25 path part): `((g_t, d_t - g_t), normalized straddling excursion)` has
the product law `straddleLaw ⊗ unitExcursionLaw`: the normalized excursion is independent of
`(g_t, d_t)` with the unit excursion law, and `(g_t, ζ_t)` has the explicit density from
compensation and the lifetime density. -/
theorem map_straddleData_eq_prod {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0} (ht : 0 < t) :
    Measure.map (straddleData θ t) (stableLocalLaw θ : Measure DLoc) =
      (straddleLaw θ t).prod (unitExcursionLaw θ : Measure Excursion) := sorry

/-- **Blueprint statement**: `normalizeExc` of the straddling excursion has the unit law. -/
theorem map_normalize_straddling_eq_unitExcursionLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {t : ℝ≥0} (ht : 0 < t) :
    Measure.map (fun f => normalizeExc θ (straddlingExcursion t f))
        (stableLocalLaw θ : Measure DLoc) =
      (unitExcursionLaw θ : Measure Excursion) := sorry

/-- **Independence** of `(g_t, ζ_t)` and the normalized straddling excursion. -/
theorem indepFun_straddle_age_shape {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0}
    (ht : 0 < t) :
    IndepFun (fun f => ((straddleStart t f : ℝ), straddleLife t f))
      (fun f => normalizeExc θ (straddlingExcursion t f))
      (stableLocalLaw θ : Measure DLoc) := sorry

/-- **Law of `(g_t, ζ_t)`** is `straddleLaw`. -/
theorem map_straddleAgeLife_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0} (ht : 0 < t) :
    Measure.map (fun f => ((straddleStart t f : ℝ), straddleLife t f))
        (stableLocalLaw θ : Measure DLoc) = straddleLaw θ t := sorry

/-- **Generalized arcsine law of `g_t`**: `g_t/t ~ Beta(1/θ, 1-1/θ)`. -/
theorem map_straddleStart_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0} (ht : 0 < t) :
    Measure.map (fun f => (straddleStart t f : ℝ)) (stableLocalLaw θ : Measure DLoc) =
      volume.withDensity (straddleStartDensity θ t) := sorry

/-- **Path version (C25(a))**: the normalized straddling excursion restricted to `[0,1]` has law
`levyExcLaw θ`. -/
theorem map_straddling_restrict_eq_levyExcLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0}
    (ht : 0 < t) :
    Measure.map (fun f => excursionRestrict 1 (normalizeExc θ (straddlingExcursion t f)))
        (stableLocalLaw θ : Measure DLoc) = (levyExcLaw θ : Measure (D 1 ℝ)) := sorry

end BGW.StableTrees
