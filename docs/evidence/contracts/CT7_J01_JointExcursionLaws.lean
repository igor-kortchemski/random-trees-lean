import BGW.Skorokhod.DLoc
import BGW.Skorokhod.Restrict
import BGW.StableTrees.StableLocalLaw
import BGW.StableTrees.SupremumLocalTimePublic
import BGW.StableTrees.MarkedExcursionsBasic
import BGW.StableTrees.UnitExcursionLaw
import BGW.StableTrees.GammaIdentity
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import BGW.StableTrees.HeightProcess
import BGW.StableTrees.HeightBridges
import BGW.StableTrees.HeightContinuity
import BGW.StableTrees.ExcursionHeight

/-! Contract probe for CT7 node J01 (`r3-ct7-blueprint/blueprint.md` J01, CT7d), written
against the acceptance criteria of `r5-ct8-blueprint/blueprint.md` §2 item 5 (consumers K14,
K15, K16, K18, K19): the joint laws of an excursion path and its height, their path marginals,
the common-lifetime mixture on every horizon, the joint Γ identity and the Brownian (`θ = 2`)
specialization `height = path`.

REDESIGN (7 Nov 2026; previous text in `*.preAE.bak`).  H04 now reconstructs `excursionHeight`
at Lebesgue-a.e. age (instead of at rational ages) and supplies the a.e.-time prefix map
`heightPrefixAE` (instead of H03's rational-time `heightPrefix`, whose non-junk branch under the
excursion laws was the blocked rational-age statement).  Here `heightPrefix` is replaced by
`heightPrefixAE` in the two graph-image statements (the second is renamed
`tailExcLaw_eq_map_heightPrefixAE`) and in the Γ argument; the copies of H04 definitions are
refreshed; every other statement is unchanged.

DEFINITIONS (concrete, no `sorry`; all laws are pushforwards of the SEALED totalized laws, so
no conditioning on a null set occurs).
* `heightRestrict T g`: restriction of `g : C(ℝ≥0, ℝ)` to `[0,T]`.
* `excursionPair θ T e = (excursionRestrict T e, heightRestrict T (excursionHeight θ e))`: path
  and height of the SAME excursion (H04's `excursionHeight`), never independently sampled.
* `excLaw θ = (unitExcursionLaw θ).map (excursionPair θ 1)` on `D 1 ℝ × C([0,1], ℝ)` and
  `tailExcLaw θ T = (tailExcursionLaw θ).map (excursionPair θ T)` on the horizon-`T` pair space
  (`T : ℝ≥0`, as the sealed `tailLevyExcLaw θ T`).  `ProbabilityMeasure.map` needs no proof in the
  pinned Mathlib; `measurable_excursionPair` guards against its junk branch.
* `restrictPair h` (`a ≤ T`): restriction of both coordinates (the sealed
  `BGW.Skorokhod.restrict` on paths).  It is the map of CT8 K15's `(excLaw θ).map (restrictPair _)`.
* `pairStretch θ T u (x, h)`: the unit pair stretched to lifetime `u` on horizon `T`, with ONE
  common `u`: path `t ↦ u^(1/θ) x((t/u) ∧ 1)` (sealed `scaleLoc` of H03's `extendConst 1 x`),
  height `t ↦ u^(1-1/θ) h((t/u) ∧ 1)` (`scaleHeight` of `extendHeight h`).  Both are stopped at
  time `1` of the unit pair; under `excLaw θ` both terminal values are `0` a.s., so they are
  stopped at zero after `u`, which keeps the formula valid for `T > u` (in particular `T > 1`).
  Stopping (rather than a literal zero extension) keeps the path càdlàg for EVERY argument, so
  no junk branch is needed.
* Copied verbatim from contract H04, not part of this contract: `IsExcursionHeightVersion`,
  `excursionHeight`, `IsPrefixHeightVersion`, `heightPrefixAE`.  Sealed and imported: H02
  (`HeightProcess`), H02b (`heightUniv`), H03 (`extendConst`).

TRUTH CHECK.
* Marginals and projectivity: `Prod.fst ∘ excursionPair θ T = excursionRestrict T` and
  `restrictPair h ∘ excursionPair θ T = excursionPair θ a` pointwise; with measurability and the
  definitions `levyExcLaw θ = (unitExcursionLaw θ).map (excursionRestrict 1)`,
  `tailLevyExcLaw θ T = (tailExcursionLaw θ).map (excursionRestrict T)`, these hold for EVERY
  `θ` (totalized laws), hence no `hθ`.
* Graph identities: H04 `ae_heightPrefixAE_unitExcursionLaw` (unit law, `a < 1 = ζ` a.s.) and
  `ae_heightPrefixAE_tailExcursionLaw` (tail law, `a ≤ 1 < ζ` a.s.) give
  `excursionPair θ a e = (excursionRestrict a e, heightPrefixAE θ a (excursionRestrict a e))`
  a.e., hence the pair prefix laws are the graph images of the sealed `unitPrefix θ a`,
  `tailPrefix θ a` under ONE Borel map (H04 `measurable_heightPrefixAE`).  At `a = 0` (allowed
  in the tail statement) H04's condition `c 0 = 0` makes `heightPrefixAE θ 0` the zero map,
  matching the sure zero `excursionHeight θ e 0 = 0`.
* Mixture: the sealed `tailExcursionLaw_eq_mixture` applied to `excursionPair θ T ⁻¹' B`
  (measurable), then for every `u`, `excursionAt θ u = (S_u)_* unitExcursionLaw θ` and, for
  unit-a.e. `s`, `excursionPair θ T (S_u s) = pairStretch θ T u (excursionPair θ 1 s)`: the path
  because `ζ(s) = 1` a.s. (`ae_lifetime_unitExcursionLaw`) so `s.path` is constant `0` from time
  `1` on and equals `extendConst 1 (excursionRestrict 1 s)`; the height because
  `excursionHeight θ s` vanishes on `[1, ∞)` surely (H04 `excursionHeight_eq_zero_of_lifetime_le`)
  and H04 `ae_excursionHeight_scale_unit` at the fixed `u` (or, for `volIoi`-a.e. `u`, H04
  `ae_prod_excursionHeight_scale_unit`, which suffices inside the `∫⁻ u`).  The common `u` and its
  independence of the unit pair are the product structure of the sealed mixture.  Density
  `(1/θ) u^(-1-1/θ)` on `(1, ∞)`, exactly as in the sealed path-only `tailLevyExcLaw_eq_mixture`.
* Γ identity: compose `F` with the graph map `x ↦ (x, heightPrefixAE θ a x)` (measurable, H04
  `measurable_heightPrefixAE`), use the two graph identities, and apply the sealed E10
  `lintegral_gamma_identity_path` / `gamma_identity_path`; `evalEnd a (restrictPair _ z).1` is the
  path value at `a`.  Integrability: `|F| ≤ C` on a probability space, and `gammaA θ a ∘ evalEnd a`
  is integrable under `tailPrefix θ a` (sealed `integral_gammaA_tail_eq_one`).
* Endpoints/positivity: H04 sure zeros at `0` and on `[ζ, ∞)`, `ζ = 1` a.s., H04
  `ae_excursionHeight_pos_unit`.
* `θ = 2`: the library process has Laplace exponent `λ²` (variance `2`); H04
  `ae_excursionHeight_two_unit` gives `H(e) = e.path` at all times under the unit law, hence
  `z.2 t = z.1 t` for all `t ∈ [0,1]` under `excLaw 2`.  The comparison with the existing
  Brownian excursion law (`√2 e`) is CT8 K18, not claimed here.

PROOF PLAN (CT7 blueprint J01).  Pointwise identities plus `Measure.map_map`; the graph
identities as above; the mixture by `tailExcursionLaw_eq_mixture`, `map_excursionScale_excursionAt`
and H04 unit scaling; Γ by composing with the graph of `heightPrefixAE` and E10; `θ = 2` by H04
`ae_excursionHeight_two_unit`.  Prove the nonnegative and the bounded signed Γ forms.  Size
350-650 lines; medium.  Risks: substituting a law-specific height version into the other side of
Γ; independent sampling of the path, the height or their lifetimes.

ACYCLICITY.  Suppliers: H04 (contract: `excursionHeight`, `heightPrefixAE` and their
statements), sealed H03 (`extendConst`), sealed E06/E09/E10 (`UnitExcursionLaw*`,
`UnitExcursionDensity*`, `GammaIdentity`).  No CT8 node.

BINDER SCOPE (AUDITOR_RULES).  Each `∫`/`∫⁻` body runs to its `∂`: in the Γ identities the body is
`F (restrictPair _ z) * gammaA θ a (evalEnd a (restrictPair _ z).1)` (the whole product, as
intended); the left-hand integral is parenthesized.  In the mixture the `∫⁻ u` body is the product
of the excLaw mass and the indicator density, as in the sealed `tailLevyExcLaw_eq_mixture`.  No `+`
or `-` follows an integral; `(1 / θ) * (u : ℝ) ^ (-1 - 1 / θ)` is inside `ENNReal.ofReal (...)`.
In the copied H04 definitions the `∀ᵐ` is the last conjunct, its body the displayed equation. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees

/-! ### Pair maps -/

/-- Restriction of a continuous function on `ℝ≥0` to `[0,T]`. -/
noncomputable def heightRestrict (T : ℝ≥0) (g : C(ℝ≥0, ℝ)) : C(Set.Icc (0 : ℝ) T, ℝ) :=
  g.comp ⟨fun t => ⟨t.1, t.2.1⟩, continuous_subtype_val.subtype_mk fun t => t.2.1⟩

/-- **The excursion/height pair on `[0,T]`**: the restricted path and the restricted height of
the same excursion. -/
noncomputable def excursionPair (θ : ℝ) (T : ℝ≥0) (e : Excursion) :
    D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ) :=
  (excursionRestrict T e, heightRestrict T (excursionHeight θ e))

/-- Restriction of a pair on `[0,T]` to `[0,a]`, for `a ≤ T`. -/
noncomputable def restrictPair {a T : ℝ≥0} (h : a ≤ T)
    (z : D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ)) : D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) a, ℝ) :=
  (BGW.Skorokhod.restrict (NNReal.coe_le_coe.2 h) z.1,
    z.2.comp ⟨Set.inclusion (Set.Icc_subset_Icc_right (NNReal.coe_le_coe.2 h)),
      continuous_inclusion _⟩)

/-- Extension of a continuous function on `[0,1]` to `ℝ≥0` by its terminal value. -/
noncomputable def extendHeight (h : C(Set.Icc (0 : ℝ) 1, ℝ)) : C(ℝ≥0, ℝ) :=
  h.comp ⟨fun t => Set.projIcc (0 : ℝ) 1 zero_le_one t,
    continuous_projIcc.comp NNReal.continuous_coe⟩

/-- Height scaling `t ↦ c^(1-1/θ) g(t/c)`, with the time convention of the sealed `scaleLoc`. -/
noncomputable def scaleHeight (θ : ℝ) (c : Set.Ioi (0 : ℝ)) (g : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) :=
  ⟨fun t => (c : ℝ) ^ (1 - 1 / θ) * g (t / (c : ℝ).toNNReal),
    continuous_const.mul (g.continuous.comp (continuous_id.div_const _))⟩

/-- **A unit pair stretched to lifetime `u`** on the horizon `[0,T]`, with one common `u`:
path `t ↦ u^(1/θ) x((t/u) ∧ 1)` and height `t ↦ u^(1-1/θ) h((t/u) ∧ 1)` (both stopped at time
`1` of the unit pair, whose terminal values vanish a.s. under `excLaw θ`). -/
noncomputable def pairStretch (θ : ℝ) (T : ℝ≥0) (u : Set.Ioi (0 : ℝ))
    (z : D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ)) : D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ) :=
  (DLoc.restrict T (scaleLoc θ u (BGW.StableTrees.extendConst 1 z.1)),
    heightRestrict T (scaleHeight θ u (extendHeight z.2)))

/-! ### Joint laws -/

/-- **The normalized excursion/height law** on `D 1 ℝ × C([0,1], ℝ)`: the image of the unit
excursion law under the pair map (path and height of the same excursion). -/
noncomputable def excLaw (θ : ℝ) : ProbabilityMeasure (D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ)) :=
  (unitExcursionLaw θ).map (excursionPair θ 1)

/-- **The tail excursion/height law** on the horizon `[0,T]`: the image of `N(· | ζ > 1)` under
the pair map (the whole excursion, stopped at zero after its lifetime). -/
noncomputable def tailExcLaw (θ : ℝ) (T : ℝ≥0) :
    ProbabilityMeasure (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ)) :=
  (tailExcursionLaw θ).map (excursionPair θ T)

/-! ### Measurability guards -/

/-- The pair map is measurable (so `excLaw` and `tailExcLaw` are not junk images). -/
theorem measurable_excursionPair (θ : ℝ) (T : ℝ≥0) : Measurable (excursionPair θ T) := sorry

/-- Restriction of pairs is measurable. -/
theorem measurable_restrictPair {a T : ℝ≥0} (h : a ≤ T) : Measurable (restrictPair h) := sorry

/-- Stretching of pairs is measurable, for each lifetime `u`. -/
theorem measurable_pairStretch (θ : ℝ) (T : ℝ≥0) (u : Set.Ioi (0 : ℝ)) :
    Measurable (pairStretch θ T u) := sorry

/-! ### Marginals and projectivity -/

/-- **First marginal of `excLaw`**: exactly the sealed `levyExcLaw θ` (every `θ`). -/
theorem excLaw_map_fst (θ : ℝ) : (excLaw θ).map Prod.fst = levyExcLaw θ := sorry

/-- **First marginal of `tailExcLaw`**: exactly the sealed `tailLevyExcLaw θ T` (every `θ`,
every horizon). -/
theorem tailExcLaw_map_fst (θ : ℝ) (T : ℝ≥0) :
    (tailExcLaw θ T).map Prod.fst = tailLevyExcLaw θ T := sorry

/-- **Projectivity** of the tail pair laws in the horizon. -/
theorem tailExcLaw_map_restrictPair (θ : ℝ) {a T : ℝ≥0} (h : a ≤ T) :
    (tailExcLaw θ T).map (restrictPair h) = tailExcLaw θ a := sorry

/-! ### Common graph -/

/-- **Joint unit prefix** on `[0,a]`, `0 < a < 1`: the graph image of the unit path prefix under
the H04 a.e.-time prefix map. -/
theorem map_restrictPair_excLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    ((excLaw θ).map (restrictPair ha.2.le)).toMeasure =
      (unitPrefix θ a).map (fun x => (x, heightPrefixAE θ a x)) := sorry

/-- **Joint tail prefix** on `[0,a]`, `a ≤ 1`: the graph image of the tail path prefix under the
same H04 a.e.-time prefix map. -/
theorem tailExcLaw_eq_map_heightPrefixAE {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0) (ha : a ≤ 1) :
    (tailExcLaw θ a).toMeasure = (tailPrefix θ a).map (fun x => (x, heightPrefixAE θ a x)) :=
  sorry

/-! ### Common-lifetime mixture -/

/-- **Joint tail mixture** (C28), every horizon `T > 0` (including `T > 1`): under
`N(· | ζ > 1)` the pair is a unit pair stretched to an independent common lifetime `u` with
density `(1/θ) u^(-1-1/θ)` on `(1, ∞)`, path by `u^(1/θ)`, height by `u^(1-1/θ)`. -/
theorem tailExcLaw_eq_mixture {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) (hT : 0 < T)
    {B : Set (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ))} (hB : MeasurableSet B) :
    (tailExcLaw θ T).toMeasure B =
      ∫⁻ u, (excLaw θ).toMeasure (pairStretch θ T u ⁻¹' B) *
        ({u : Set.Ioi (0 : ℝ) | 1 < (u : ℝ)}.indicator
          (fun u => ENNReal.ofReal ((1 / θ) * (u : ℝ) ^ (-1 - 1 / θ))) u) ∂volIoi := sorry

/-! ### Joint Γ identity -/

/-- **Joint Γ identity**, nonnegative measurable tests of the pair prefix on `[0,a]`,
`0 < a < 1`. -/
theorem lintegral_gamma_identity {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) (F : D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) a, ℝ) → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ z, F (restrictPair ha.2.le z) ∂(excLaw θ).toMeasure =
      ∫⁻ z, F (restrictPair ha.2.le z) *
          ENNReal.ofReal (gammaA θ a (evalEnd a (restrictPair ha.2.le z).1))
        ∂(tailExcLaw θ 1).toMeasure := sorry

/-- **Joint Γ identity** (source-facing form), bounded measurable signed tests of the pair
prefix on `[0,a]`, `0 < a < 1`, with both integrands integrable. -/
theorem gamma_identity {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1)
    (F : D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) a, ℝ) → ℝ) (hF : Measurable F)
    (hb : ∃ C : ℝ, ∀ z, |F z| ≤ C) :
    Integrable (fun z => F (restrictPair ha.2.le z)) (excLaw θ).toMeasure ∧
    Integrable (fun z => F (restrictPair ha.2.le z) *
        gammaA θ a (evalEnd a (restrictPair ha.2.le z).1)) (tailExcLaw θ 1).toMeasure ∧
    (∫ z, F (restrictPair ha.2.le z) ∂(excLaw θ).toMeasure) =
      ∫ z, F (restrictPair ha.2.le z) * gammaA θ a (evalEnd a (restrictPair ha.2.le z).1)
        ∂(tailExcLaw θ 1).toMeasure := sorry

/-! ### Endpoints and the Brownian case -/

/-- Under `excLaw θ` the height vanishes at `0` and `1` and is positive on `(0,1)`, all times
at once. -/
theorem excLaw_height_endpoints_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ z ∂(excLaw θ).toMeasure,
      z.2 ⟨0, le_rfl, zero_le_one⟩ = 0 ∧ z.2 ⟨1, zero_le_one, le_rfl⟩ = 0 ∧
        ∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < z.2 t := sorry

/-- **Brownian specialization** (`θ = 2`, Laplace exponent `λ²`): under `excLaw 2` the height
equals the path at every time, almost surely. -/
theorem excLaw_height_eq_path_two :
    ∀ᵐ z ∂(excLaw 2).toMeasure, ∀ t : Set.Icc (0 : ℝ) 1, z.2 t = z.1 t := sorry

end BGW.StableTrees
