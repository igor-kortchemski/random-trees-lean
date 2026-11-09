import BGW.StableTrees.ExcursionLifetime
import BGW.StableTrees.ExcursionMeasure
import BGW.StableTrees.StableKendall
import BGW.ContinuumTrees.ExcursionCarrier
import BGW.StableTrees.UnitExcursionLaw
import BGW.StableTrees.ExcursionMarkov
import BGW.StableTrees.KendallAdapter

/-! Contract probe for CT7 node E09 (density of the unit excursion at prefix times and no
fixed jumps of the unit law), following `r3-ct7-blueprint/blueprint.md` E09, its signature
block, AUDIT items 7-8 and `duquesne_revised.tex` lines 700-722 (equations (markov), (itodescr),
(N1)).

CONSTANTS.  `α = 1/θ`, `N = excursionMeasure θ`, `p0 = d_θ(0) = α/Γ(1-α)`
(`stableDensity_zero_eq_inv_theta_gamma`), `N(ζ>t) = t^{-α}/Γ(1-α)`, so `N(ζ>1) = θ p0`.
The lifetime density of `N` is `p0 u^{-1-α}` (`lifetimeDensity`); source (itodescr) writes it
`1/(θ Γ(1-1/θ) u^{1/θ+1})`, the same number.  `q_s(x) = (x/s) p_s(-x)` (`qKernel`, time first;
Kendall: `passageLaw θ x = withDensity (x/s · p_s(-x))`).  Source (N1):
`N(f(X_r) q_{1-a}(X_a) 1{ζ>a}) = (θ Γ(1-α))⁻¹ N_(1)(f(X_r)) = p0 N_(1)(f(X_r))`, which is the
displayed `p0⁻¹` in `levyExcLaw_prefix_density`.  Total mass (F = 1): `N(q_{1-a}(e a); ζ>a) = p0`
(`lintegral_prefix_density_mass`).  CONSTANTS CHECKED CONSISTENT: blueprint, source, E06, E08.

DEFINITIONS.  Copied (verbatim) from E06/E08: `excursionTail`, `unitExcursionMeasure`,
`toProbOrJunk`, `unitExcursionLaw`, `volIoi`, `lifetimeDensity`, `excursionAt`, `qKernel`.  New:
`unitPrefix θ a = (unitExcursionLaw θ).map (excursionRestrict a)` (law on `D a ℝ` of the unit
excursion restricted to `[0,a]`; equals the further restriction of `levyExcLaw θ`).

CONVENTIONS / AMBIGUITIES.  The blueprint sketch takes `a : ℝ` with `ra : Excursion → D a ℝ`; the
carrier API `excursionRestrict` takes `T : ℝ≥0`, so here `a : ℝ≥0`, `a ∈ Ioo 0 1`, horizon `(a:ℝ)`.
`qKernel θ (1-a) x` is junk for `x ≤ 0`; it is only used at `x = e a > 0`, N-a.e. on `{ζ>a}`
(E04 support, `ae_valueNN_pos` of E07).  No fixed jump is stated for `t ∈ Ioo 0 1` as
`leftLim e t = e t` (cadlag: continuity at `t`); `t = 0` is trivial and `t = 1` is E06 E1.

TRUTH.  All theorems bind `hθ : 1 < θ ∧ θ ≤ 2`.  The unit law is only known to charge a path's
jump times through `N`'s no-fixed-jump property for the random lifetime (the cycle of
blueprint E09): the density identity is first proved for a.e. lifetime `u > a`
(`prefix_density_ae_lifetime`), then evaluated AT `u = 1` using finite-dimensional tests at
"good" times (no fixed jump under the unit law) with endpoint cutoffs `χ`, whose two sides are
continuous at `u = 1` (`excursionAt_finiteDim_continuousAt_one`,
`excursionTail_density_continuousAt_one`), giving `integral_goodTimes_eq_density_at_one`;
then `S.ext_of_finiteDimensional` (dense good times containing the terminal time `b`).

PROOF PLAN.  (1) E07 (`excursion_markov_lintegral`, `excursion_remainingLifetime_lintegral`) +
E08 (`passageLaw_eq_qKernel`) give
`N(F(r_a e) g(ζ); ζ>a) = ∫_{u>a} g(u) N(F(r_a e) q_{u-a}(e a); ζ>a) du`; E06
(`setLIntegral_excursionMeasure_eq_mixture`) gives `∫_{u>a} g(u) p0 u^{-1-α} N_(u)(F(r_a ·)) du`;
comparing over all `g` yields the a.e.-`u` identity.  (2) Good dense times from countability of
jumps (Fubini).  (3) Continuity at `u = 1`: `S_u e(t_i) = u^α e(t_i/u)` with `t_i/u → t_i` and
`e` continuous at the good `t_i` a.s., bounded convergence; on the `N` side
`q_{u-b}(x) χ(x)` is bounded for `u - b ≥ δ > 0`, `x ≤ 2M`
(`stableDensityAt_le_of_ge`), `N ↾ {ζ>b}` is finite.  (4) Equality a.e. + continuity at 1
gives equality at 1; monotone convergence in `χ ↑ 1`.  (5) Normalize and apply
`ext_of_finiteDimensional`.  (6) Transfer no fixed jump from `N` (E07 `N_noFixedJump`).
Estimate 650-1100 lines. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-! ### Copied declarations (not part of this contract) -/

open scoped Classical in
/-! ### New definitions -/

/-- **Law of the unit excursion on `[0,a]`**: `(r_a)_* unitExcursionLaw`, a measure on the
compact path space `D a ℝ` (horizon `(a : ℝ)`).  For `a < 1` it is the restriction of
`levyExcLaw θ` to `[0,a]`; for `a ≥ 1` the lifetime is already reached. -/
noncomputable def unitPrefix (θ : ℝ) (a : ℝ≥0) : Measure (D (a : ℝ) ℝ) :=
  (unitExcursionLaw θ : Measure Excursion).map (excursionRestrict a)

/-- **Good time** for the unit law: no fixed jump at `t` (cadlag, so continuity at `t`). -/
def NoFixedJumpUnit (θ : ℝ) (t : ℝ≥0) : Prop :=
  ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion), Function.leftLim e.path.1 t = e.path.1 t

/-! ### Step 1: the identity for almost every lifetime -/

/-- **Identity at a.e. lifetime `u > a`** (source (N1) before specialization to `u = 1`).  For
measurable `F : D a ℝ → ℝ≥0∞`: for `volIoi`-a.e. `u > a`,
`p0 u^{-1-α} N_(u)(F(r_a ·)) = N(F(r_a e) q_{u-a}(e a); ζ>a)`.  Derived from E07
(`excursion_markov_lintegral`, `excursion_remainingLifetime_lintegral`), E08
(`passageLaw_eq_qKernel`) and E06 (`setLIntegral_excursionMeasure_eq_mixture`); the exceptional
`u`-null set depends on `F`. -/
theorem prefix_density_ae_lifetime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0) (ha : 0 < a)
    (F : D (a : ℝ) ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∀ᵐ u : Set.Ioi (0 : ℝ) ∂(volIoi.restrict {u : Set.Ioi (0 : ℝ) | (a : ℝ) < (u : ℝ)}),
      lifetimeDensity θ (u : ℝ) * ∫⁻ e, F (excursionRestrict a e) ∂(excursionAt θ u) =
        ∫⁻ e in {e : Excursion | (a : ℝ) < (e.lifetime : ℝ)},
          F (excursionRestrict a e) *
            ENNReal.ofReal (qKernel θ ((u : ℝ) - a) (e.path.1 a)) ∂(excursionMeasure θ) := sorry

/-! ### Step 2-3: good times and continuity at lifetime one -/

/-- **Countable dense set of good times**: `G ⊆ (0,1)` countable, dense in `[0,1]`
(every nonempty open subinterval of `Ioo 0 1` meets it), each a no-fixed-jump time of the unit
law (Fubini plus countability of the jumps of a cadlag path; `G` need not be rational). -/
theorem exists_goodTimes_unit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ G : Set ℝ≥0, G.Countable ∧ G ⊆ Ioo 0 1 ∧
      (∀ x y : ℝ≥0, x < y → y ≤ 1 → ∃ t ∈ G, x < t ∧ t < y) ∧
      ∀ t ∈ G, NoFixedJumpUnit θ t := sorry

/-- **Continuity at lifetime one, unit side**: for finitely many good times `t i ∈ [0,1]` and a
bounded continuous `φ`, `u ↦ N_(u)(φ(e(t_1),…,e(t_n)))` is continuous at `u = 1`
(`S_u e(t) = u^α e(t/u)` and a.s. continuity of `e` at each `t i`, bounded convergence). -/
theorem excursionAt_finiteDim_continuousAt_one {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {n : ℕ}
    (t : Fin n → ℝ≥0) (ht : ∀ i, t i ≤ 1) (hgood : ∀ i, NoFixedJumpUnit θ (t i))
    (φ : (Fin n → ℝ) → ℝ) (hφ : Continuous φ) (hφb : ∃ C : ℝ, ∀ x, |φ x| ≤ C) :
    ContinuousAt
      (fun u : Set.Ioi (0 : ℝ) => ∫ e, φ (fun i => e.path.1 (t i)) ∂(excursionAt θ u))
      ⟨1, Set.mem_Ioi.2 one_pos⟩ := sorry

/-- **Continuity at lifetime one, `N` side**: for `0 < b < 1`, times `t i ≤ b`, bounded
continuous `φ` and a compactly supported continuous cutoff `χ` of the endpoint value,
`u ↦ N(φ(e(t_i)) χ(e(b)) q_{u-b}(e(b)); ζ>b)` is continuous at `u = 1`.  Domination:
`u - b ≥ δ > 0`, `e(b) ∈ supp χ` bounded (`qKernel_le_of_ge`) and `N ↾ {ζ>b}` finite. -/
theorem excursionTail_density_continuousAt_one {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (b : ℝ≥0)
    (hb : b ∈ Ioo (0 : ℝ≥0) 1) {n : ℕ} (t : Fin n → ℝ≥0) (ht : ∀ i, t i ≤ b)
    (φ : (Fin n → ℝ) → ℝ) (hφ : Continuous φ) (hφb : ∃ C : ℝ, ∀ x, |φ x| ≤ C)
    (χ : ℝ → ℝ) (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    ContinuousAt
      (fun u : ℝ => ∫ e in {e : Excursion | (b : ℝ) < (e.lifetime : ℝ)},
        φ (fun i => e.path.1 (t i)) * χ (e.path.1 b) *
          qKernel θ (u - b) (e.path.1 b) ∂(excursionMeasure θ)) 1 := sorry

/-- **Evaluation at lifetime one for good-time cylinder tests with endpoint cutoff**: for a good
`b ∈ (0,1)`, good times `t i ≤ b`, bounded continuous `φ`, compactly supported continuous `χ`,
`∫ φ(e(t_i)) χ(e b) dN_(1) = p0⁻¹ N(φ(e(t_i)) χ(e b) q_{1-b}(e b); ζ>b)`. -/
theorem integral_goodTimes_eq_density_at_one {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (b : ℝ≥0)
    (hb : b ∈ Ioo (0 : ℝ≥0) 1) (hbgood : NoFixedJumpUnit θ b) {n : ℕ} (t : Fin n → ℝ≥0)
    (ht : ∀ i, t i ≤ b) (hgood : ∀ i, NoFixedJumpUnit θ (t i))
    (φ : (Fin n → ℝ) → ℝ) (hφ : Continuous φ) (hφb : ∃ C : ℝ, ∀ x, |φ x| ≤ C)
    (χ : ℝ → ℝ) (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    (∫ e, φ (fun i => e.path.1 (t i)) * χ (e.path.1 b) ∂(unitExcursionLaw θ : Measure Excursion)) =
      (Scalar.stableDensity θ 0)⁻¹ *
        ∫ e in {e : Excursion | (b : ℝ) < (e.lifetime : ℝ)},
          φ (fun i => e.path.1 (t i)) * χ (e.path.1 b) *
            qKernel θ (1 - b) (e.path.1 b) ∂(excursionMeasure θ) := sorry

/-! ### Main statements -/

/-- **Mass of the density side** (`F = 1`): `N(q_{1-a}(e a); ζ>a) = p0`, so the right side of
`levyExcLaw_prefix_density` is a probability measure.  `N`-a.e. positivity of `e a` is used
only to read `qKernel` away from its junk region. -/
theorem lintegral_prefix_density_mass {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    ∫⁻ e in {e : Excursion | (a : ℝ) < (e.lifetime : ℝ)},
      ENNReal.ofReal (qKernel θ (1 - a) (e.path.1 a)) ∂(excursionMeasure θ) =
        ENNReal.ofReal (Scalar.stableDensity θ 0) := sorry

/-- **Density of the unit excursion at prefix times** (E2, source (N1)): for `0 < a < 1`,
`(r_a)_* N_(1) = p0⁻¹ • (r_a)_* ( (N ↾ {ζ>a}).withDensity (e ↦ q_{1-a}(e a)) )`
as finite measures on `D a ℝ`.  Junk: `qKernel` at `e a ≤ 0` (a null set), `ofReal` truncation. -/
theorem levyExcLaw_prefix_density {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    unitPrefix θ a =
      (ENNReal.ofReal (Scalar.stableDensity θ 0))⁻¹ •
        ((excursionTail θ a).withDensity
          (fun e => ENNReal.ofReal (qKernel θ (1 - a) (e.path.1 a)))).map
            (excursionRestrict a) := sorry

/-- **Integral form** of the density identity for nonnegative measurable tests on `D a ℝ`. -/
theorem lintegral_unitPrefix_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) (F : D (a : ℝ) ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x ∂(unitPrefix θ a) =
      (ENNReal.ofReal (Scalar.stableDensity θ 0))⁻¹ *
        ∫⁻ e in {e : Excursion | (a : ℝ) < (e.lifetime : ℝ)},
          F (excursionRestrict a e) *
            ENNReal.ofReal (qKernel θ (1 - a) (e.path.1 a)) ∂(excursionMeasure θ) := sorry

/-- **No fixed jump of the unit law** at every deterministic `t ∈ (0,1)`
(transfers `N_noFixedJump` of E07 through the density identity at a good `b > t`; the endpoints
`t = 0, 1` are E06 E1). -/
theorem levyExcLaw_noFixedJump {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0)
    (ht : t ∈ Ioo (0 : ℝ≥0) 1) : NoFixedJumpUnit θ t := sorry

end BGW.StableTrees
