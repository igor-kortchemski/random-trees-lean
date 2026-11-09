import BGW.StableTrees.ExcursionLifetime
import BGW.StableTrees.ExcursionMeasure
import BGW.StableTrees.MarkedExcursions
import BGW.ContinuumTrees.ExcursionCarrier

/-! Contract probe for CT7 node E06 (unit law, path-only mixture and E1), following
`r3-ct7-blueprint/blueprint.md` §2 and E06.

CONSTANTS.  `α = 1/θ`, `c_θ = 1/Γ(1-α)`, `N(ζ > t) = c_θ t^{-α}` (E05), so
`N(ζ > 1) = c_θ` and the normalized restriction of `N` to `{ζ > 1}` has coefficient
`c_θ⁻¹ = Γ(1-α)`.  The lifetime density is `α c_θ u^{-1-α} = p0 u^{-1-α}` (`p0 = d_θ(0)`, E05
`stableDensity_zero_eq_inv_theta_gamma`).  Under `N(· | ζ > 1)` the lifetime has density
`α u^{-1-α}` on `u > 1` (the constant `c_θ` cancels).

DEFINITIONS (no choice of conditional distribution).
* `unitExcursionMeasure θ = Γ(1-1/θ) • (normalizeExc θ)_* (N ↾ {ζ > 1})`, a plain `Measure`.
* `unitExcursionLaw θ : ProbabilityMeasure Excursion` is that measure when it is a probability
  measure and `dirac junkExcursion` otherwise (JUNK: only for `θ ∉ (1,2]`; the theorem
  `isProbabilityMeasure_unitExcursionMeasure` shows the junk branch is never taken for valid θ,
  and `coe_unitExcursionLaw` records the identification).  Same pattern for `tailExcursionLaw`.
* `levyExcLaw θ` = image of `unitExcursionLaw θ` under `excursionRestrict 1` (lifetime 1, so the
  restriction to `[0,1]` loses nothing); `tailLevyExcLaw θ T` = image of `tailExcursionLaw θ`
  (law of `N(· | ζ > 1)`) under `excursionRestrict T`, with `T : ℝ≥0` (the horizon is `(T : ℝ)`;
  theorems bind `0 < T`).  The whole path is kept for all horizons, not only `T ≤ 1`.
* `excursionAt θ u = (S_u)_* unitExcursionLaw θ`, `u > 0` (`S_u` = `excursionScale`).
* `lifetimeLaw θ`: the Lévy measure `ζ_* N` as a measure on `Set.Ioi 0`, namely
  `volIoi.withDensity (lifetimeDensity θ)` (E05 `excursionMeasure_lifetime_density`).

TRUTH.  Everything is exact for `1 < θ ≤ 2`.  Statements about the junk branch are avoided; all
theorems bind `hθ`.  `excursionMeasure_eq_lifetime_mixture` is an identity of measures on
measurable sets, and `shapeLifetime_map_excursionMeasure` is the joint (lifetime, shape) product
identity, first proved on tail rectangles via scaling (`N(shape ∈ A, ζ > t) = t^{-α} ...`).

PROOF PLAN.  (1) `N(normalize ∈ A, ζ > t) = N(S_{1/t}^{-1}...)`: scaling `(S_c)_* N = c^α N`
(E05) and `normalizeExc ∘ S_c = normalizeExc` give the rectangle formula.  (2) Rectangles
`(t,∞) × A` form a π-system generating `Ioi 0 × Excursion` and `N` is finite on each, so the product
identity.  (3) Pushing back by the measurable inverse `fromShapeLifetime` gives the mixture and
uniqueness (any scaling-consistent finite-tail family has the same product form).  (4) E1 from
E04 `ae_excursionMeasure_support` transferred by normalization.  Estimate 550-1000 lines. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-! ### Definitions -/

/-- The tail `N ↾ {ζ > a}` of the excursion measure. -/
noncomputable def excursionTail (θ : ℝ) (a : ℝ) : Measure Excursion :=
  (excursionMeasure θ).restrict {e : Excursion | a < (e.lifetime : ℝ)}

/-- Explicit normalized unit measure: `Γ(1-1/θ) • (normalizeExc θ)_* (N ↾ {ζ > 1})`.  The
coefficient is `N(ζ > 1)⁻¹`; this is a normalized restriction, not a conditioning on `{ζ = 1}`. -/
noncomputable def unitExcursionMeasure (θ : ℝ) : Measure Excursion :=
  ENNReal.ofReal (Real.Gamma (1 - 1 / θ)) • (excursionTail θ 1).map (normalizeExc θ)

/-- The tail law `N(· | ζ > 1) = Γ(1-1/θ) • N ↾ {ζ > 1}` as a plain measure. -/
noncomputable def tailExcursionMeasure (θ : ℝ) : Measure Excursion :=
  ENNReal.ofReal (Real.Gamma (1 - 1 / θ)) • excursionTail θ 1

open scoped Classical in
/-- Probability-measure packaging with a junk `dirac junkExcursion` branch. -/
noncomputable def toProbOrJunk (μ : Measure Excursion) : ProbabilityMeasure Excursion :=
  if h : IsProbabilityMeasure μ then ⟨μ, h⟩
  else ⟨Measure.dirac junkExcursion, inferInstance⟩

/-- **Unit excursion law**; agrees with `unitExcursionMeasure` for `1 < θ ≤ 2`.  Outside that
range it is only a totalized probability measure. -/
noncomputable def unitExcursionLaw (θ : ℝ) : ProbabilityMeasure Excursion :=
  toProbOrJunk (unitExcursionMeasure θ)

/-- Law of the excursion under `N(· | ζ > 1)`; agrees with `tailExcursionMeasure` for
`1 < θ ≤ 2`.  Outside that range it is only a totalized probability measure. -/
noncomputable def tailExcursionLaw (θ : ℝ) : ProbabilityMeasure Excursion :=
  toProbOrJunk (tailExcursionMeasure θ)

/-- **Unit-lifetime excursion as a path on `[0,1]`**. -/
noncomputable def levyExcLaw (θ : ℝ) : ProbabilityMeasure (D 1 ℝ) :=
  (unitExcursionLaw θ).map (excursionRestrict 1)

/-- **Whole excursion under `N(· | ζ > 1)`, restricted to `[0,T]`**. -/
noncomputable def tailLevyExcLaw (θ : ℝ) (T : ℝ≥0) : ProbabilityMeasure (D (T : ℝ) ℝ) :=
  (tailExcursionLaw θ).map (excursionRestrict T)

/-- The scaled unit excursion `(S_u)_* unitExcursionLaw`, `u > 0`: the `N_{(u)}` of the
blueprint. -/
noncomputable def excursionAt (θ : ℝ) (u : Set.Ioi (0 : ℝ)) : Measure Excursion :=
  ((unitExcursionLaw θ : Measure Excursion)).map (excursionScale θ u)

/-- The lifetime density `(1/θ)/Γ(1-1/θ) · u^{-1-1/θ}`. -/
noncomputable def lifetimeDensity (θ : ℝ) (u : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 / θ) / Real.Gamma (1 - 1 / θ) * u ^ (-1 - 1 / θ))

/-- Lebesgue measure on `Set.Ioi 0` (comap of `volume`). -/
noncomputable def volIoi : Measure (Set.Ioi (0 : ℝ)) := Measure.comap Subtype.val volume

/-- The Lévy measure `ζ_* N` on `Set.Ioi 0`. -/
noncomputable def lifetimeLaw (θ : ℝ) : Measure (Set.Ioi (0 : ℝ)) :=
  volIoi.withDensity (fun u => lifetimeDensity θ u)

/-! ### Unit law -/

/-- The unnormalized unit measure is a probability measure. -/
theorem isProbabilityMeasure_unitExcursionMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    IsProbabilityMeasure (unitExcursionMeasure θ) := sorry

/-- The tail measure is a probability measure. -/
theorem isProbabilityMeasure_tailExcursionMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    IsProbabilityMeasure (tailExcursionMeasure θ) := sorry

/-- Unfolding: the law is the explicit normalized restriction. -/
theorem coe_unitExcursionLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (unitExcursionLaw θ : Measure Excursion) = unitExcursionMeasure θ := sorry

/-- Unfolding for the tail law. -/
theorem coe_tailExcursionLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (tailExcursionLaw θ : Measure Excursion) = tailExcursionMeasure θ := sorry

/-- Unit excursions have lifetime one almost surely (indeed surely on the support). -/
theorem ae_lifetime_unitExcursionLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion), e.lifetime = 1 := sorry

/-- **Threshold independence**: for every `a > 0`, the normalized restriction of `N` to
`{ζ > a}`, pushed by `normalizeExc`, is the unit law. -/
theorem normalize_tail_independent_of_threshold {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ)
    (ha : 0 < a) :
    (excursionMeasure θ {e : Excursion | a < (e.lifetime : ℝ)})⁻¹ •
        (excursionTail θ a).map (normalizeExc θ) =
      (unitExcursionLaw θ : Measure Excursion) := sorry

/-- **Shape rectangles**: `N(normalizeExc ∈ A, ζ > t) = t^{-α} N(normalizeExc ∈ A, ζ > 1)
= (t^{-α}/Γ(1-α)) · unitExcursionLaw(A)`. -/
theorem excursionMeasure_shape_tail_rectangle {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {A : Set Excursion}
    (hA : MeasurableSet A) (t : ℝ) (ht : 0 < t) :
    excursionMeasure θ ({e : Excursion | normalizeExc θ e ∈ A} ∩
        {e : Excursion | t < (e.lifetime : ℝ)}) =
      ENNReal.ofReal (t ^ (-(1 / θ)) / Real.Gamma (1 - 1 / θ)) *
        (unitExcursionLaw θ : Measure Excursion) A := sorry

/-- **Tail support**: under `N(· | ζ > 1)`, almost surely the lifetime exceeds `1`, the path is
positive on `(0, ζ)`, the tag is the actual lifetime and the terminal left limit is `0`. -/
theorem ae_tailExcursionLaw_support {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(tailExcursionLaw θ : Measure Excursion),
      1 < e.lifetime ∧
      (∀ t : ℝ≥0, 0 < t → t < e.lifetime → 0 < e.path.1 t) ∧
      e.lifetime = sSup {t : ℝ≥0 | 0 < e.path.1 t} ∧
      Function.leftLim e.path.1 e.lifetime = 0 := sorry

/-- **Mass of the unit tail**: `N(ζ > 1) = 1/Γ(1-1/θ) = θ d_θ(0)`. -/
theorem excursionMeasure_lifetime_gt_one {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    excursionMeasure θ {e : Excursion | 1 < (e.lifetime : ℝ)} =
      ENNReal.ofReal (1 / Real.Gamma (1 - 1 / θ)) := sorry

/-- The same mass through the stable density at `0`. -/
theorem excursionMeasure_lifetime_gt_one_eq_density {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    excursionMeasure θ {e : Excursion | 1 < (e.lifetime : ℝ)} =
      ENNReal.ofReal (θ * Scalar.stableDensity θ 0) := sorry

/-- No positive lifetime is charged by `N`. -/
theorem excursionMeasure_lifetime_eq_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ) (ha : 0 < a) :
    excursionMeasure θ {e : Excursion | (e.lifetime : ℝ) = a} = 0 := sorry

/-- No lifetime is charged by the tail law. -/
theorem tailExcursionLaw_lifetime_eq_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ) :
    (tailExcursionLaw θ : Measure Excursion) {e : Excursion | (e.lifetime : ℝ) = a} = 0 := sorry

/-- **Lifetime marginal on the positive half-line**: `(lifetimePos)_* N = lifetimeLaw`. -/
theorem map_lifetimePos_excursionMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (excursionMeasure θ).map Excursion.lifetimePos = lifetimeLaw θ := sorry

/-! ### The every-lifetime family `N_{(u)}` -/

/-- Each `excursionAt θ u` is a probability measure (for every `θ`). -/
theorem isProbabilityMeasure_excursionAt (θ : ℝ) (u : Set.Ioi (0 : ℝ)) :
    IsProbabilityMeasure (excursionAt θ u) := sorry

/-- Measurability of `u ↦ N_{(u)}(A)`. -/
theorem measurable_excursionAt_apply (θ : ℝ) {A : Set Excursion} (hA : MeasurableSet A) :
    Measurable (fun u : Set.Ioi (0 : ℝ) => excursionAt θ u A) := sorry

/-- `N_{(u)}`-almost every excursion has lifetime `u`. -/
theorem ae_lifetime_excursionAt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (u : Set.Ioi (0 : ℝ)) :
    ∀ᵐ e ∂(excursionAt θ u), (e.lifetime : ℝ) = (u : ℝ) := sorry

/-- Exact scaling of the family at every lifetime: `(S_c)_* N_{(u)} = N_{(cu)}`. -/
theorem map_excursionScale_excursionAt (θ : ℝ) (c u : Set.Ioi (0 : ℝ)) :
    (excursionAt θ u).map (excursionScale θ c) =
      excursionAt θ ⟨(c : ℝ) * (u : ℝ), Set.mem_Ioi.2 (mul_pos c.2 u.2)⟩ := sorry

/-- The family at lifetime one is the unit law. -/
theorem excursionAt_one (θ : ℝ) :
    excursionAt θ ⟨1, Set.mem_Ioi.2 one_pos⟩ = (unitExcursionLaw θ : Measure Excursion) := sorry

/-! ### Joint identity and mixture -/

/-- **Joint identity on tail rectangles**: for `a > 0`,
`(ζ, normalizeExc)_* (N ↾ {ζ > a}) = (lifetime law ↾ {u > a}) ⊗ unitExcursionLaw`. -/
theorem shapeLifetime_map_excursionTail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ) (ha : 0 < a) :
    (excursionTail θ a).map (shapeLifetime θ) =
      ((lifetimeLaw θ).restrict {u : Set.Ioi (0 : ℝ) | a < (u : ℝ)}).prod
        (unitExcursionLaw θ : Measure Excursion) := sorry

/-- **Joint identity**: `(ζ, normalizeExc)_* N = lifetimeLaw ⊗ unitExcursionLaw`. -/
theorem shapeLifetime_map_excursionMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (excursionMeasure θ).map (shapeLifetime θ) =
      (lifetimeLaw θ).prod (unitExcursionLaw θ : Measure Excursion) := sorry

/-- **Path-only mixture**: for measurable `A`,
`N(A) = ∫⁻ u>0, (S_u)_* unitExcursionLaw (A) · (1/θ)/Γ(1-1/θ) u^{-1-1/θ} du`. -/
theorem excursionMeasure_eq_lifetime_mixture {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {A : Set Excursion}
    (hA : MeasurableSet A) :
    excursionMeasure θ A =
      ∫⁻ u, excursionAt θ u A * lifetimeDensity θ u ∂volIoi := sorry

/-- **Nonnegative mixture**: `∫⁻ F dN = ∫⁻ u>0, (∫⁻ F dN_{(u)}) · density(u) du` for measurable
`F : Excursion → ℝ≥0∞`. -/
theorem lintegral_excursionMeasure_eq_mixture {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {F : Excursion → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ e, F e ∂(excursionMeasure θ) =
      ∫⁻ u, (∫⁻ e, F e ∂(excursionAt θ u)) * lifetimeDensity θ u ∂volIoi := sorry

/-- **Restricted nonnegative mixture** over long excursions `{ζ > a}`, `a ≥ 0`. -/
theorem setLIntegral_excursionMeasure_eq_mixture {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {F : Excursion → ℝ≥0∞} (hF : Measurable F) (a : ℝ) (ha : 0 ≤ a) :
    ∫⁻ e in {e : Excursion | a < (e.lifetime : ℝ)}, F e ∂(excursionMeasure θ) =
      ∫⁻ u in {u : Set.Ioi (0 : ℝ) | a < (u : ℝ)},
        (∫⁻ e, F e ∂(excursionAt θ u)) * lifetimeDensity θ u ∂volIoi := sorry

/-- **Mixture for the tail law**: under `N(· | ζ > 1)` the lifetime has density
`α u^{-1-α}` on `u > 1`; for measurable `A ⊆ Excursion`. -/
theorem tailExcursionLaw_eq_mixture {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {A : Set Excursion}
    (hA : MeasurableSet A) :
    (tailExcursionLaw θ : Measure Excursion) A =
      ∫⁻ u, excursionAt θ u A *
        ({u : Set.Ioi (0 : ℝ) | 1 < (u : ℝ)}.indicator
          (fun u => ENNReal.ofReal ((1 / θ) * (u : ℝ) ^ (-1 - 1 / θ))) u) ∂volIoi := sorry

/-- **Tail path mixture** (C28), every horizon `T > 0` (zero continuation after `u` is built into
`excursionRestrict`): for measurable `B ⊆ D T ℝ`. -/
theorem tailLevyExcLaw_eq_mixture {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) (hT : 0 < T)
    {B : Set (D (T : ℝ) ℝ)} (hB : MeasurableSet B) :
    (tailLevyExcLaw θ T : Measure (D (T : ℝ) ℝ)) B =
      ∫⁻ u, excursionAt θ u (excursionRestrict T ⁻¹' B) *
        ({u : Set.Ioi (0 : ℝ) | 1 < (u : ℝ)}.indicator
          (fun u => ENNReal.ofReal ((1 / θ) * (u : ℝ) ^ (-1 - 1 / θ))) u) ∂volIoi := sorry

/-- **Uniqueness of scaling-consistent families**: a measure `ν` with
`(S_c)_* ν = c^{1/θ} • ν` for all `c > 0` and `ν {ζ > 1} < ∞` is determined by its unit shape
measure `(normalizeExc)_* (ν ↾ {ζ > 1})`: `(ζ, normalizeExc)_* ν =
Γ(1-1/θ) • lifetimeLaw ⊗ (normalizeExc)_* (ν ↾ {ζ > 1})`. -/
theorem shapeLifetime_map_of_scaling {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ν : Measure Excursion)
    (hν : ∀ c : Set.Ioi (0 : ℝ),
      ν.map (excursionScale θ c) = ENNReal.ofReal ((c : ℝ) ^ (1 / θ)) • ν)
    (hfin : ν {e : Excursion | 1 < (e.lifetime : ℝ)} < ⊤) :
    ν.map (shapeLifetime θ) =
      ENNReal.ofReal (Real.Gamma (1 - 1 / θ)) • (lifetimeLaw θ).prod
        ((ν.restrict {e : Excursion | 1 < (e.lifetime : ℝ)}).map (normalizeExc θ)) := sorry

/-- **Characterization of `N`**: a scaling-consistent `ν` with `ν {ζ > 1} < ∞` and the same
unit shape measure as `N` equals `N`. -/
theorem excursionMeasure_unique_of_scaling {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ν : Measure Excursion)
    (hν : ∀ c : Set.Ioi (0 : ℝ),
      ν.map (excursionScale θ c) = ENNReal.ofReal ((c : ℝ) ^ (1 / θ)) • ν)
    (hfin : ν {e : Excursion | 1 < (e.lifetime : ℝ)} < ⊤)
    (hshape : (ν.restrict {e : Excursion | 1 < (e.lifetime : ℝ)}).map (normalizeExc θ) =
      (excursionTail θ 1).map (normalizeExc θ)) :
    ν = excursionMeasure θ := sorry

/-! ### E1: endpoints and positivity -/

/-- **E1 for the unit excursion**: almost surely `e 0 = 0`, `e t > 0` on `(0,1)`, `e 1 = 0` and the
left limit at `1` is `0`. -/
theorem levyExcLaw_endpoints_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ x ∂(levyExcLaw θ).toMeasure,
      (x : D 1 ℝ) ⟨0, by norm_num, zero_le_one⟩ = 0 ∧
      (∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < x t) ∧
      x ⟨1, zero_le_one, le_rfl⟩ = 0 ∧
      Function.leftLim (x : Set.Icc (0 : ℝ) 1 → ℝ) ⟨1, zero_le_one, le_rfl⟩ = 0 := sorry

/-- E1 at the level of `Excursion`: the same properties for `unitExcursionLaw`, in terms of
the path on `ℝ≥0`. -/
theorem ae_unitExcursionLaw_positive {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion),
      e.path.1 0 = 0 ∧ (∀ t : ℝ≥0, 0 < t → t < 1 → 0 < e.path.1 t) ∧
      Function.leftLim e.path.1 1 = 0 := sorry

end BGW.StableTrees
