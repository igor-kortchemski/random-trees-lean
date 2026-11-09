import BGW.Skorokhod.DLoc
import BGW.StableTrees.StableLocalLaw
import BGW.StableTrees.SupremumLocalTimePublic
import BGW.StableTrees.MarkedExcursionsBasic
import BGW.StableTrees.UnitExcursionLaw
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import BGW.StableTrees.HeightProcess
import BGW.StableTrees.HeightBridges
import BGW.StableTrees.HeightContinuity

/-! Contract probe for CT7 node H04 (`r3-ct7-blueprint/blueprint.md` H04, C26 H1-H5), written
against the acceptance criteria of `r5-ct8-blueprint/blueprint.md` §2 item 4 (consumers K14,
K15, K16, K18): the continuous height of ONE excursion, its simultaneous locality inside the
continuous height of the stable process, its scaling, and the common prefix graph
(`heightPrefixAE`) under the excursion measure, the unit law and the tail law.

REDESIGN (7 Nov 2026, Lebesgue-a.e.-age reconstruction; previous text in `*.preAE.bak`).  The
previous version reconstructed `excursionHeight` from `heightUniv` at RATIONAL ages.  Its core
`ae_exists_continuous_excursionRawHeight` was blocked: rational ages of an excursion are random
irrational host times, where the host's raw heights are not controlled, and the uniform
convergence route (`sol-route-h04/ROUTE.md`) failed at its suggested estimate
(`w93-h03b/attempt-1/result.md`, counterexample at `θ = 2`).  An a.e.-age reconstruction needs
host control only at Lebesgue-a.e. host time, a Fubini consequence of sealed fixed-time facts,
and a Lebesgue-null set of host times stays null after translation by ANY start `T(x-)`, random
or not: no independence, Palm or compensation argument is needed for that step.

DEFINITIONS (concrete, no `sorry`; all suppliers are sealed and imported, nothing is copied).
* `IsExcursionHeightVersion θ e g`: `g : C(ℝ≥0, ℝ)` vanishes at `0` and on `[ζ(e), ∞)` and equals
  `heightUniv θ e.path` (H02b) at Lebesgue-a.e. age `s ∈ (0, ζ(e))` (ages are reals read through
  `toNNReal`, as in H02b's a.e.-age statements).
* `excursionHeight θ e`: `Classical.choose` of such a `g` when one exists, the zero function
  otherwise.  The version is unique (`excursionHeight_eq_of_isExcursionHeightVersion`): two
  versions are continuous and agree a.e. on the nonempty open interval `(0, ζ)` (`ζ > 0` for
  every excursion), so the relatively open set where they differ is Lebesgue-null, hence empty;
  both vanish at `0` and on `[ζ, ∞)`.  The raw height is consulted only on `(0, ζ)`: after the
  lifetime the path is identically `0`, every `s ∈ [ζ, t]` satisfies `X_s < I^s_t + ε`, and the
  approximation of the path is `≥ (t - ζ)/ε`, so the explicit zero condition replaces the old
  cut-off `excursionRawHeight`.  `excursionHeight θ e` is a function of `e` ALONE
  (`excursionMeasure` is a join over host paths, so a host-based definition would not be a
  function on `Excursion`).  Sure consequences for EVERY excursion: continuity, `H 0 = 0`,
  `H = 0` on `[ζ, ∞)`, and `H ≥ 0` (a version is `≥ 0` a.e. on `(0, ζ)` by `heightUniv_nonneg`,
  hence on `[0, ζ]` by continuity, an a.e.-full subset of an interval being dense in it).
* `IsPrefixHeightVersion θ T g c` and `heightPrefixAE θ T g`: the same on a compact horizon:
  `c : C([0,T], ℝ)` with `c 0 = 0` agreeing at a.e. time of `(0, T)` with
  `heightUniv θ (extendConst T g)` (H03's sealed constant extension; `heightUniv` reads only
  `[0, t]`, so this is a function of the prefix `g`), and `0` when no such `c` exists.  The
  condition `c 0 = 0` makes the version unique also at `T = 0`, where the a.e. clause is vacuous;
  for `T > 0` it is forced by continuity on every non-junk branch used below
  (`heightLoc θ f 0 = 0` and `excursionHeight θ e 0 = 0` surely).

DESIGN CHOICES.
1. Graph identities are deterministic consequences of the non-junk branch
   (`heightPrefixAE_excursionRestrict_of_exists`, for `a < ζ(e)`): ONE Borel map
   `heightPrefixAE θ a` serves `N`, the unit law and the tail law, and under the stable law it
   equals H03's `heightPrefix` on one event for all horizons (`ae_heightPrefixAE_eq_heightPrefix`),
   so CT8's stable pair law (H03 `map_heightPrefix_pair`) and the excursion graphs use the same
   map up to null sets.  H03's rational-time `heightPrefix` is not used under `N`: its non-junk
   branch there is exactly the blocked rational-age statement.
2. Positivity is simultaneous: `∀ t, 0 < t → t < ζ → 0 < H t` inside the a.e. binder.
3. Scaling, with `S_c = excursionScale θ c` (path `c^(1/θ) e(t/c)`, lifetime `c ζ`): the
   CT8-literal pointwise form `H(S_c e)(c t) = c^(1-1/θ) H(e)(t)` for all `t`, (a) for each fixed
   `c`, `N`-a.e.; (b) for each fixed `c`, a.e. under the UNIT law (not implied by (a): the unit
   law is carried by the `N`-null set `{ζ = 1}`); (c) `(volIoi ⊗ N)`- and `(volIoi ⊗ unit)`-a.e.
   in `(c, e)` (J01's common-lifetime mixture can use either (b) or the unit product form);
   (d) normalization `H(e)(ζ t) = ζ^(1-1/θ) H(normalizeExc θ e)(t)`, `N`-a.e.  "`N`-a.e., for all
   `c` at once" is NOT claimed.
4. Locality uses the sealed `passageJumpSet`, `passageTimeMinus`, `passageTime`, `jumpExcursion`
   (strict passage `T_x = inf {t | X_t < -x}`, `g = T(x-)`) and H03's `heightLoc`, on ONE event
   for all jump levels and all ages: `ae_jumpExcursion_heightVersion` states non-junk and
   locality together (`H(e_x)(t) = heightLoc θ f (g + t)` on `[0, ζ]`, `0` after);
   `ae_heightLoc_jumpExcursion` keeps the previous export's form for K14.
5. The host chain is exported as separate statements so that the proof order is checkable:
   a.e.-time identity `ae_heightLoc_eq_heightUniv_ae`, exact cancellation
   `heightApprox_jumpExcursion_add` and its limsup form `heightUniv_jumpExcursion_eq`, pre-start
   vanishing `ae_tendsto_heightApprox_passageTimeMinus`, endpoint zeros
   `ae_heightLoc_passageEndpoints`.
6. `heightApprox_tendstoInMeasure_excursionHeight` (each fixed `t > 0`, under `N ↾ {t < ζ}`)
   and its unit version identify the continuous version as the in-measure limit of
   `heightApprox` at EVERY fixed age: the height is characterized, not merely a.e. in the age.
7. Measurability guards: `measurable_excursionHeight` (Borel structure of the compact-open
   topology, Mathlib `ContinuousMap.measurableSpace`), `measurable_heightPrefixAE`, and
   `measurableSet_exists_isExcursionHeightVersion` (the event the compensation transfer needs),
   so J01's `Measure.map` never takes the junk branch of a non-measurable map.

REMOVED (obsolete after the redesign).  `excursionRawHeight` (the cut-off is replaced by the
a.e. clause on `(0, ζ)` and the explicit zero condition); `excursionHeight_eq_of_rational_agreement`
(replaced by `excursionHeight_eq_of_isExcursionHeightVersion`);
`ae_exists_continuous_excursionRawHeight` and `..._unit` (rational-age non-junk, blocked;
replaced by `ae_exists_isExcursionHeightVersion` and `..._unit`);
`ae_age_heightUniv_eq_excursionHeight` (the rational-to-a.e.-age bridge of Sol audit height-r1
finding 2; it is now the non-junk branch of the definition plus Fubini).  RENAMED with the new
map: `ae_heightPrefix_excursionRestrict`, `ae_restrict_heightPrefix_excursionRestrict`,
`ae_heightPrefix_unitExcursionLaw`, `ae_heightPrefix_tailExcursionLaw` become the
`heightPrefixAE` versions.  All other exports keep their statements, now about the new
`excursionHeight`.

TRUTH CHECK.  `α = 1/θ`, `β = 1 - 1/θ ∈ (0, 1/2]`; `g = T(x-)`, `d = T(x)`, `e_x = jumpExcursion`.
(T1) Deterministic block.  Measurability: `r(s, e) = heightUniv θ e.path s` is jointly
measurable (`measurable_heightUniv_uncurry`), so for rational intervals `J` the maps
`e ↦ Leb {s ∈ J ∩ (0, ζ) | r(s, e) > q}` are measurable (Fubini) and so are essential sups and
infs of `r(·, e)` on `J ∩ (0, ζ)`; the non-junk event is the countable condition "essential
oscillation of `r(·, e)` tends to `0` locally uniformly on `(0, ζ)` and the essential sup on
`(0, δ)` and on `(ζ - δ, ζ)` tends to `0`"; on it `H(e)(t)` at rational `t < ζ` is the limit of
essential sups over shrinking rational intervals, and continuity plus the Borel structure of
`C(ℝ≥0, ℝ)` generated by rational evaluations (as H03 `measurable_heightLoc`) give
`measurable_excursionHeight`; the same for `heightPrefixAE`.  Uniqueness and sure properties as
in DEFINITIONS.  Graph lemma: for `a < ζ` the restriction of a version to `[0, a]` vanishes at
`0` and agrees a.e. on `(0, a)` with `heightUniv θ e.path = heightUniv θ (extendConst a
(excursionRestrict a e))` there (H02b `heightUniv_eq_of_restrict_eq`, H03 `restrict_extendConst`).
(T2) Cancellation (checked against the sealed `heightApprox`, `futureInf`, `excursionCut`).  For
`s < g`: `inf_{[s, g+u]} f = inf_{[s, g]} f` because `inf_{[s,g]} f ≤ f g ≤ inf_{[g, g+u]} f`
(cut validity, `u ≤ d - g`), so the pre-`g` integrands at `g + u` and at `g` coincide EXACTLY: no
pre-start correction term remains.  For `s = g + r ∈ [g, g + u]`: H02 `futureInf_shift_window`
and `excursionCut_eval` (`min (g + r) d = g + r`) turn the condition into that of `e_x` at age
`u`; the point `s = g` is null (the split is H02b `heightApprox_sub_shift_eq`).  Every `ε`, all
measures finite.  Limsup form: `heightEps θ k > 0` and `→ 0` for EVERY `θ` (both branches of the
choice), and `limsup (a_k - b_k) = limsup a_k` when `b_k → 0` also in Mathlib's junk case (`a_k`
is eventually bounded above iff `a_k - b_k` is; otherwise both real limsups are `0`).
(T3) Host a.e. time.  H02b `ae_age_heightUniv_eq_height` (`∀ᵐ s ∈ (0, S), ∀ᵐ f`) and H03
`ae_heightLoc_eq_height` (`∀ s, ∀ᵐ f`), joint measurability (`measurable_heightLoc_uncurry`,
`measurable_heightUniv_uncurry`), Fubini on `(0, S) × stable`, `S ∈ ℕ`.  Then on H03's graph event
(`ae_heightPrefix_restrict_all`) the restriction of `heightLoc θ f` to `[0, T]` is a prefix
version (`heightLoc_zero`, prefix locality), so both prefix maps equal it, for all `T` at once.
(T4) Pre-start vanishing.  On the sealed events (`ae_continuousAt_jumpStart`: `f g = -x`;
`f ≥ -x` before the strict passage `d > g`; `f ≥ -(x - ε)` before `T(x - ε)`) one has
`futureInf f g s = -x` for `s ≤ g`, hence `0 ≤ A_ε(f, g) ≤ (T(x-) - T(x - ε))/ε` for
`0 < ε < x`.  Fixed level: `T(x) - T(x - ε)` has the law of `T(ε)`, which is that of
`ε^θ T(1)` (`map_passageIncrement`, `passageLaw_scaling`), and `P(T(1) > y) = O(y^(-1/θ))`, so
`P(T(ε)/ε > δ) = O(δ^(-1/θ) ε^(1 - 1/θ))` is summable along `ε = 2^(-n)`; Borel-Cantelli and
monotonicity in `ε` give `→ 0` a.s. (zero derivative of a driftless subordinator at a fixed
level).  All jump atoms at once: the bad
left-slope event at level `x` reads the passage process strictly before `x`; use
`excursion_compensation_predictable_general` (NOT the left-continuous-integrand version) after
proving the bad set `{(x, f) | ¬ Tendsto (n ↦ (L x f - L (x - 2^(-n)) f) / 2^(-n)) (𝓝 0)}` is
`predictableSigma`-measurable, with `L x f = ⨆ y < x, firstPassageBelow y f` the infinity-valued
left passage process (do not assume left continuity of the totalized `passageTimeMinus`);
compensate on levels `≤ K` and lifetime slabs `{ζ > δ}` (expected number of bad atoms
`∫_0^K P(bad at x) N(ζ > δ) dx = 0`), countable unions in `K`, `δ`; interpolate between dyadic
cutoffs with the monotone numerator and a factor-two denominator bound; the fixed-level dyadic
tail also follows from `integral_exp_neg_passageLaw` via `P(Z > y) ≤ (1 - E e^{-Z/y})/(1 - e^{-1})`
(Sol audit h04-ae finding 1; height-r1 finding 3).
(T5) Endpoint zeros.  For rational `q`, `τ = T(q)` is a stopping time
(`isStoppingTime_firstPassageBelow`), `f τ = -q ≤ f s` for `s ≤ τ` (creeping, strict passage),
and the fresh path `f' = shiftAt τ f` has the stable law (`map_shiftAt_restrict_stableLocalLaw`)
with `inf_{[0,u]} f' < 0` for all `u > 0` (regularity).  By `heightApprox_sub_shift_eq` the
pre-`τ` occupation at `τ + u` is EMPTY for `0 < ε ≤ -inf_{[0,u]} f'`, so
`heightUniv θ f (τ + u) = heightUniv θ f' u` for all `u > 0`.  (T3) for `f` (translated by `τ`)
and for `f'` gives `heightLoc θ f (τ + ·) = heightLoc θ f'` a.e. on `(0, ∞)`, hence everywhere
by continuity, and `heightLoc θ f τ = heightLoc θ f' 0 = 0`.  Countably many `q`; then
`T(x) = lim_{q ↓ x} T(q)` (`ae_isCadlag_monotone_passage`), `T(x-) = lim_{q ↑ x} T(q)`
(definition as a supremum) and continuity of `heightLoc`.
(T6) Locality and non-junk, pathwise.  On the intersection of (T3), (T4), (T5) and
`ae_jumpExcursion_spec` (cut validity, `ζ(e_x) = d - g`), for every `x ∈ J`:
`G u = heightLoc θ f (min (g + u) d)` is continuous, `G 0 = 0`, `G = 0` on `[ζ, ∞)` (T5), and
for a.e. `u ∈ (0, ζ)`: `G u = heightLoc θ f (g + u) = heightUniv θ f (g + u)` ((T3): `{u | g + u ∈
B}` is null for the host's null set `B`, whatever `g`) `= heightUniv θ e_x.path u` ((T2) with
(T4)).  So `G` is a version and `excursionHeight θ e_x = G` by uniqueness.
(T7) `N` non-junk: sealed `ae_excursionMeasure_of_ae_jumpExcursion` with the measurable event
of (T1).  Positivity: host zero-set property (Duquesne-Le Gall; previous H04 plan): on
`(g, d)`, `X > I` (`ae_isExcursionInterval_of_jump`); for `t₀ ∈ (g, d)` pick rational
`s ∈ (g, t₀)` with `inf_{[s, t₀]} X < X_{t₀}` (right continuity at `g`, `X_g = -x`); the
left-limit minimizer `m` of `X` on `[s, t₀]` is an ancestor of every rational horizon `v`
slightly after `t₀`, its raw height is positive (`ae_zero_height_ancestor_inf_all`: a
zero-height ancestor has the root infimum level, impossible inside `(g, d)`) and bounds
`heightLoc θ f v = height θ f v` from below (`ae_height_ancestor_fixed`, clock difference);
let `v ↓ t₀`.  Then (T6) and the transfer (measurable by continuity).
(T8) Scaling under `N`, fixed `c`.  `A_ε(S_c e, c s) = c^β A_{ε c^(-α)}(e, s)` (change of
variables in `heightApprox`).  H02b's joint in-measure limit `L` on survival-restricted age
windows (`exists_heightApprox_tendstoInMeasure_excursion_ages`) holds along the full filter, hence
along `heightEps θ k` and along `c^(-α) heightEps θ k`; `A` converges a.s. along `heightEps θ`
at a.e. age for `N`-a.e. `e` (`ae_age_tendsto_heightUniv_excursion`, Fubini) and, since
`(S_c)_* N = c^(1/θ) N` preserves null sets (`map_excursionScale_excursionMeasure`), also for
`S_c e`, i.e. along `c^(-α) heightEps θ` for `e`; all these limits equal `L` a.e.  Hence
`heightUniv θ (S_c e).path (c s) = c^β heightUniv θ e.path s` for a.e. `s < ζ`, `N`-a.e., and
`t ↦ c^β H(e)(t/c)` (zero at `0` and on `[c ζ, ∞)`) is a version for `S_c e`; uniqueness.
(T9) Unit law, raw identity (no unit non-junk used): for fixed `c` and a.e. `r ∈ (0, 1)`,
convergence along `heightEps θ` for `S_c s` at age `c r` is a prefix event of `s` on `[0, r]`,
`N ↾ {ζ > r}`-a.s. by H02b and the scaling of `N`, hence unit-a.s. by E09
(`levyExcLaw_prefix_density`, `r < 1`); the limits equal the unit joint in-measure limit
(`exists_heightApprox_tendstoInMeasure_unit_ages`), which is `heightUniv θ s.path`
(`ae_age_tendsto_heightUniv_unit`).  So `heightUniv θ (S_c s).path (c r) = c^β heightUniv θ
s.path r` for a.e. `r ∈ (0, 1)`, unit-a.s. (Sol audit height-r1 finding 5).
(T10) Unit non-junk.  On `[0, a]`, `a < 1`: the prefix-version event is a measurable prefix
event, `N ↾ {ζ > a}`-a.s. (`N` non-junk and the graph lemma), hence unit-a.s. by E09 (unit prefix
≪ tail prefix ≪ `N` prefix); consistent prefix versions glue on `[0, 1)`.  The endpoint `t ↑ 1`
is a SEPARATE obligation, not a prefix event: by the shape/lifetime product law
(`shapeLifetime_map_excursionMeasure`, `fromShapeLifetime_shapeLifetime`) and `N` non-junk there
is ONE deterministic scale `u₀` with `S_{u₀} s` non-junk unit-a.s.; with (T9) at `c = u₀`,
`r ↦ u₀^(-β) H(S_{u₀} s)(u₀ r)` is a version for `s` (it vanishes on `[1, ∞)` since `ζ(s) = 1`
a.s., `ae_lifetime_unitExcursionLaw`).  Then unit scaling (b) as in (T8) from (T9) and
uniqueness.
(T11) Product forms: Fubini in `(c, e)` (`sigmaFinite_excursionMeasure` installed locally), the
failure set being measurable (continuity reduces `∀ t` to rational `t`;
`measurable_excursionScale_joint`, `measurable_excursionHeight_uncurry`).  Normalization: under
`N`, `(ζ, normalizeExc θ e)` has law `lifetimeLaw ⊗ unit` with `lifetimeLaw ≪ volIoi`, and
`e = S_ζ (normalizeExc θ e)`, so the unit product form gives (d); substituting `c = 1/ζ(e)` into
the fixed-`c` statement would be invalid.
(T12) Graph identities: the graph lemma and non-junk under `N`, the unit law, and the tail law
`Γ(1-1/θ) • N ↾ {ζ > 1}` (`coe_tailExcursionLaw`, absolutely continuous w.r.t. `N`).
(T13) Fixed-age identification.  H02b gives at every `t > 0` an in-measure limit `L_t`
(`exists_heightApprox_tendstoInMeasure_excursion`), and `L_t = H(·)(t)` `N ↾ {t < ζ}`-a.e. for
a.e. `t` ((T8)'s identification with `heightUniv` and `N` non-junk).  The set of good ages is
invariant under every dilation: by `(S_c)_* N = c^(1/θ) N`, (a) at the fixed `c` and the change of
variables, convergence at age `t` gives convergence at age `c t` (`ε c^(-α) → 0⁺` along the
full filter).  A nonempty dilation-invariant subset of `(0, ∞)` is everything.  Unit version at
`t ∈ (0, 1)`: `A_ε(e, t)` and `heightPrefixAE θ t (excursionRestrict t e) t` are prefix
functionals and the latter is `H(e)(t)` under `N ↾ {t < ζ}` and the unit law (graph identities);
convergence in measure transfers along the finite absolutely continuous E09 prefix law.
(T14) Unit positivity: the `N` statement through the shape/lifetime product law and the unit
product scaling.  `θ = 2`: the library process has `E exp(-λ X_t) = exp(t λ²)` (variance `2`),
so `height = X - I` at fixed times (H02 `ae_height_two`); at rational times
`heightLoc = heightUniv = height` (H02b `ae_heightUniv_eq_height`), continuity of `heightLoc` and
of the Brownian path (`stableProcessLaw_two`) give `heightLoc 2 f = X - I` at all times, (T6)
gives `H(e_x)(t) = X_{g+t} - I_{g+t} = X_{g+t} + x = e_x(t)` on `[0, ζ]` (both `0` after), the
transfer gives `N`, and the shape/lifetime law with `α = β = 1/2` gives the unit law.

PROOF PLAN (noncircular order).  (1) Deterministic block (T1), (T2).  (2) Host a.e.-time
identity and `ae_heightPrefixAE_eq_heightPrefix` (T3).  (3) Pre-start vanishing (T4).
(4) Endpoint zeros (T5).  (5) Locality with non-junk on the host (T6) and the old-form locality.
(6) `N` non-junk and positivity (T7).  (7) `N` scaling (T8) and the `N` product form.  (8) Unit
raw identity (T9), unit non-junk (T10), unit scaling and unit product form, normalization (T11).
(9) Graph identities (T12).  (10) Fixed-age identification (T13).  (11) Unit positivity and
`θ = 2` (T14).  Steps (1)-(5) use no excursion-measure statement, no fixed-age identification
and no unit statement; the unit statements use `N` statements and E09, never conversely; the
host locality is never used to prove its own inputs.  Size 1500-2600 lines; very high.  Risks:
measurability of the a.e.-age reconstruction; predictable compensation of the left-slope event;
the strong Markov transfer at `T(q)`; E09 transfers of prefix events along a rescaled sequence.

ACYCLICITY.  Suppliers, all sealed: H02 (`HeightProcess*`), H02b (`HeightBridges*`), H03
(`HeightContinuity*`), E01-E10 (`ExcursionCarrier`, `ExcursionMeasure*`, `MarkedExcursions*`,
`StableExcursionSupport*`, `ExcursionMarkov*`, `UnitExcursionLaw*`, `UnitExcursionDensity*`),
N05 (`StableStrongMarkov`), N06 (`StableRegularity`), N09 (`StablePassageSubordinator*`),
`StableLocalLaw`, H01 (`SupremumLocalTimePublic`).  No contract supplier and no CT8 node;
J01, O01 and CT8 K14-K18 consume H04.

BINDER SCOPE (AUDITOR_RULES).  No integral, `∫⁻`, sum or `⨆` occurs in these statements or
definitions.  Every `∀ᵐ` body extends to the end of its statement (in `IsExcursionHeightVersion`
and `IsPrefixHeightVersion` the `∀ᵐ` is the last conjunct, its body the displayed equation).  In
`ae_jumpExcursion_heightVersion` the `if ... then ... else 0` is the whole right-hand side.
Exponents are parenthesized: `(c : ℝ) ^ (1 - 1 / θ) * excursionHeight θ e t` is `c^(1-1/θ)`
times the height.  In `heightApprox_jumpExcursion_add` the right-hand side is the sum of two
approximations. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees

/-! ### Definitions -/

/-- `g` is an **a.e.-age height version** of the excursion `e`: it vanishes at time `0` and at
and after the lifetime, and agrees with `heightUniv θ e.path` at Lebesgue-almost every age of
`(0, ζ(e))`. -/
def IsExcursionHeightVersion (θ : ℝ) (e : Excursion) (g : C(ℝ≥0, ℝ)) : Prop :=
  g 0 = 0 ∧ (∀ t : ℝ≥0, e.lifetime ≤ t → g t = 0) ∧
    ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) (e.lifetime : ℝ))),
      g s.toNNReal = heightUniv θ e.path s.toNNReal

/-- **The excursion height**: the a.e.-age height version of `e` when one exists (it is then
unique), the zero function otherwise. -/
noncomputable def excursionHeight (θ : ℝ) (e : Excursion) : C(ℝ≥0, ℝ) :=
  if h : ∃ g : C(ℝ≥0, ℝ), IsExcursionHeightVersion θ e g then Classical.choose h else 0

/-- `c` is an **a.e.-time prefix height version** of `g : D T ℝ`: it vanishes at time `0` and
agrees with `heightUniv θ (extendConst T g)` at Lebesgue-almost every time of `(0, T)`. -/
def IsPrefixHeightVersion (θ : ℝ) (T : ℝ≥0) (g : D (T : ℝ) ℝ)
    (c : C(Set.Icc (0 : ℝ) T, ℝ)) : Prop :=
  c ⟨0, le_rfl, T.2⟩ = 0 ∧
    ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) (T : ℝ))),
      c (Set.projIcc 0 (T : ℝ) T.2 s) = heightUniv θ (extendConst T g) s.toNNReal

/-- **A.e.-time prefix height map** on `[0,T]`: the a.e.-time prefix height version of `g` when
one exists (it is then unique), `0` otherwise. -/
noncomputable def heightPrefixAE (θ : ℝ) (T : ℝ≥0) (g : D (T : ℝ) ℝ) :
    C(Set.Icc (0 : ℝ) T, ℝ) :=
  if h : ∃ c : C(Set.Icc (0 : ℝ) T, ℝ), IsPrefixHeightVersion θ T g c then
    Classical.choose h else 0

/-! ### Deterministic properties -/

/-- The non-junk event of `excursionHeight` is Borel (the compensation transfer needs it). -/
theorem measurableSet_exists_isExcursionHeightVersion (θ : ℝ) :
    MeasurableSet {e : Excursion | ∃ g : C(ℝ≥0, ℝ), IsExcursionHeightVersion θ e g} := sorry

/-- The excursion height is a Borel measurable function of the excursion. -/
theorem measurable_excursionHeight (θ : ℝ) : Measurable (excursionHeight θ) := sorry

/-- Joint measurability of `(t, e) ↦ excursionHeight θ e t` (Fubini arguments in J01). -/
theorem measurable_excursionHeight_uncurry (θ : ℝ) :
    Measurable (fun p : ℝ≥0 × Excursion => excursionHeight θ p.2 p.1) := sorry

/-- **Deterministic characterization**: an a.e.-age height version is the excursion height. -/
theorem excursionHeight_eq_of_isExcursionHeightVersion (θ : ℝ) (e : Excursion)
    (g : C(ℝ≥0, ℝ)) (hg : IsExcursionHeightVersion θ e g) : excursionHeight θ e = g := sorry

/-- On the non-junk branch the excursion height is itself a version. -/
theorem isExcursionHeightVersion_excursionHeight (θ : ℝ) (e : Excursion)
    (h : ∃ g : C(ℝ≥0, ℝ), IsExcursionHeightVersion θ e g) :
    IsExcursionHeightVersion θ e (excursionHeight θ e) := sorry

/-- The excursion height starts at `0`, for every excursion. -/
theorem excursionHeight_zero (θ : ℝ) (e : Excursion) : excursionHeight θ e 0 = 0 := sorry

/-- The excursion height vanishes at and after the lifetime, for every excursion. -/
theorem excursionHeight_eq_zero_of_lifetime_le (θ : ℝ) (e : Excursion) {t : ℝ≥0}
    (ht : e.lifetime ≤ t) : excursionHeight θ e t = 0 := sorry

/-- The excursion height is nonnegative, for every excursion. -/
theorem excursionHeight_nonneg (θ : ℝ) (e : Excursion) (t : ℝ≥0) :
    0 ≤ excursionHeight θ e t := sorry

/-- The a.e.-time prefix height map is Borel measurable. -/
theorem measurable_heightPrefixAE (θ : ℝ) (T : ℝ≥0) : Measurable (heightPrefixAE θ T) := sorry

/-- **Deterministic characterization** of the prefix map: an a.e.-time prefix height version is
the value of `heightPrefixAE`. -/
theorem heightPrefixAE_eq_of_isPrefixHeightVersion (θ : ℝ) (T : ℝ≥0) (g : D (T : ℝ) ℝ)
    (c : C(Set.Icc (0 : ℝ) T, ℝ)) (hc : IsPrefixHeightVersion θ T g c) :
    heightPrefixAE θ T g = c := sorry

/-- **Deterministic graph identity**: on the non-junk branch, for every horizon `a < ζ(e)`, the
prefix map applied to the restricted excursion is the excursion height on `[0,a]`. -/
theorem heightPrefixAE_excursionRestrict_of_exists (θ : ℝ) (e : Excursion)
    (he : ∃ g : C(ℝ≥0, ℝ), IsExcursionHeightVersion θ e g) {a : ℝ≥0} (ha : a < e.lifetime)
    (t : Set.Icc (0 : ℝ) a) :
    heightPrefixAE θ a (excursionRestrict a e) t = excursionHeight θ e ⟨t, t.2.1⟩ := sorry

/-- **Exact finite-cutoff cancellation** (deterministic): if the cut of `(T(x-), T(x))` is valid,
then for every cutoff `ε` and every age `u ≤ T(x) - T(x-)`, the host approximation at
`T(x-) + u` is the host approximation at `T(x-)` plus the approximation of the jump excursion at
age `u` (no correction term: the pre-start integrands coincide). -/
theorem heightApprox_jumpExcursion_add (ε : ℝ) (x : ℝ≥0) (f : DLoc)
    (hcut : cutValid (passageTimeMinus x f) (passageTime x f) f) {u : ℝ≥0}
    (hu : u ≤ passageTime x f - passageTimeMinus x f) :
    heightApprox ε f (passageTimeMinus x f + u) =
      heightApprox ε f (passageTimeMinus x f) + heightApprox ε (jumpExcursion x f).path u :=
  sorry

/-- **Raw height of a jump excursion** (deterministic): with a valid cut and a vanishing
pre-start approximation at `T(x-)`, the universal raw height of the excursion at age
`u ≤ T(x) - T(x-)` is the host's universal raw height at `T(x-) + u`. -/
theorem heightUniv_jumpExcursion_eq (θ : ℝ) (x : ℝ≥0) (f : DLoc)
    (hcut : cutValid (passageTimeMinus x f) (passageTime x f) f)
    (hpre : Tendsto (fun ε : ℝ => heightApprox ε f (passageTimeMinus x f)) (𝓝[>] (0 : ℝ))
      (𝓝 0))
    {u : ℝ≥0} (hu : u ≤ passageTime x f - passageTimeMinus x f) :
    heightUniv θ (jumpExcursion x f).path u = heightUniv θ f (passageTimeMinus x f + u) := sorry

/-! ### Host facts under the stable law -/

/-- **A.e.-time identity on the host**: almost surely, the continuous height equals the
universal raw height at Lebesgue-almost every time. -/
theorem ae_heightLoc_eq_heightUniv_ae {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      heightLoc θ f s.toNNReal = heightUniv θ f s.toNNReal := sorry

/-- Under the stable law, the a.e.-time prefix map and H03's rational-time prefix map agree on
the restricted path, simultaneously for all horizons. -/
theorem ae_heightPrefixAE_eq_heightPrefix {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ T : ℝ≥0,
      heightPrefixAE θ T (DLoc.restrict T f) = heightPrefix θ T (DLoc.restrict T f) := sorry

/-- **Pre-start vanishing**: almost surely, at every passage jump level `x`, the host
approximation at the excursion start `T(x-)` tends to `0` along the full filter `ε → 0⁺`. -/
theorem ae_tendsto_heightApprox_passageTimeMinus {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f,
      Tendsto (fun ε : ℝ => heightApprox ε f (passageTimeMinus x f)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  sorry

/-- The host height vanishes at both ends of every excursion interval (K14). -/
theorem ae_heightLoc_passageEndpoints {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f,
      heightLoc θ f (passageTimeMinus x f) = 0 ∧ heightLoc θ f (passageTime x f) = 0 := sorry

/-! ### Simultaneous locality and non-junk -/

/-- **Locality and non-junk on one event**: almost surely, for every passage jump level `x`, the
attached excursion has an a.e.-age height version, and its height is the continuous host height
`t ↦ heightLoc θ f (T(x-) + t)` on `[0, T(x) - T(x-)]`, zero after. -/
theorem ae_jumpExcursion_heightVersion {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f,
      (∃ g : C(ℝ≥0, ℝ), IsExcursionHeightVersion θ (jumpExcursion x f) g) ∧
        ∀ t : ℝ≥0, excursionHeight θ (jumpExcursion x f) t =
          if t ≤ passageTime x f - passageTimeMinus x f then
            heightLoc θ f (passageTimeMinus x f + t) else 0 := sorry

/-- **Simultaneous excursion locality**: almost surely, for every passage jump level `x` and
every `0 ≤ t ≤ T(x) - T(x-)`, the continuous height of the stable process at `T(x-) + t` is the
height of the excursion attached to `x` at time `t`. -/
theorem ae_heightLoc_jumpExcursion {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f, ∀ t : ℝ≥0,
      t ≤ passageTime x f - passageTimeMinus x f →
        heightLoc θ f (passageTimeMinus x f + t) = excursionHeight θ (jumpExcursion x f) t :=
  sorry

/-! ### Non-junk branch and fixed-age identification -/

/-- Under the excursion measure every excursion has an a.e.-age height version (the non-junk
branch of `excursionHeight`). -/
theorem ae_exists_isExcursionHeightVersion {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(excursionMeasure θ), ∃ g : C(ℝ≥0, ℝ), IsExcursionHeightVersion θ e g := sorry

/-- Under the unit excursion law (singular w.r.t. `N`) every excursion has an a.e.-age height
version, including the vanishing at the lifetime `1`. -/
theorem ae_exists_isExcursionHeightVersion_unit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion),
      ∃ g : C(ℝ≥0, ℝ), IsExcursionHeightVersion θ e g := sorry

/-- **Identification under `N`**: for each fixed age `t > 0`, on `{t < ζ}` the approximations
converge in `N`-measure to the excursion height. -/
theorem heightApprox_tendstoInMeasure_excursionHeight {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0)
    (ht : 0 < t) :
    TendstoInMeasure ((excursionMeasure θ).restrict {e : Excursion | t < e.lifetime})
      (fun (ε : ℝ) (e : Excursion) => heightApprox ε e.path t) (𝓝[>] (0 : ℝ))
      (fun e => excursionHeight θ e t) := sorry

/-- **Identification under the unit law** at ages `0 < t < 1`. -/
theorem heightApprox_tendstoInMeasure_excursionHeight_unit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (t : ℝ≥0) (ht0 : 0 < t) (ht1 : t < 1) :
    TendstoInMeasure (unitExcursionLaw θ : Measure Excursion)
      (fun (ε : ℝ) (e : Excursion) => heightApprox ε e.path t) (𝓝[>] (0 : ℝ))
      (fun e => excursionHeight θ e t) := sorry

/-! ### Simultaneous positivity -/

/-- **Positivity inside**, simultaneously for all times of `(0, ζ)`, under `N`. -/
theorem ae_excursionHeight_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(excursionMeasure θ), ∀ t : ℝ≥0, 0 < t → t < e.lifetime →
      0 < excursionHeight θ e t := sorry

/-- **Positivity inside**, simultaneously for all times of `(0, ζ)`, under the unit law. -/
theorem ae_excursionHeight_pos_unit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion), ∀ t : ℝ≥0, 0 < t → t < e.lifetime →
      0 < excursionHeight θ e t := sorry

/-! ### Scaling -/

/-- **Scaling under `N`**, for each fixed `c > 0`:
`H(S_c e)(c t) = c^(1-1/θ) H(e)(t)` for all `t`, `N`-a.e. -/
theorem ae_excursionHeight_scale {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (c : Set.Ioi (0 : ℝ)) :
    ∀ᵐ e ∂(excursionMeasure θ), ∀ t : ℝ≥0,
      excursionHeight θ (excursionScale θ c e) ((c : ℝ).toNNReal * t) =
        (c : ℝ) ^ (1 - 1 / θ) * excursionHeight θ e t := sorry

/-- **Scaling under the unit law**, for each fixed `c > 0` (not implied by the `N` version: the
unit law lives on the `N`-null set `{ζ = 1}`). -/
theorem ae_excursionHeight_scale_unit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (c : Set.Ioi (0 : ℝ)) :
    ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion), ∀ t : ℝ≥0,
      excursionHeight θ (excursionScale θ c e) ((c : ℝ).toNNReal * t) =
        (c : ℝ) ^ (1 - 1 / θ) * excursionHeight θ e t := sorry

/-- **Scaling with a measurable parameter**: `(Lebesgue ⊗ N)`-a.e. in `(c, e)`. -/
theorem ae_prod_excursionHeight_scale {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ p ∂(volIoi.prod (excursionMeasure θ)), ∀ t : ℝ≥0,
      excursionHeight θ (excursionScale θ p.1 p.2) ((p.1 : ℝ).toNNReal * t) =
        (p.1 : ℝ) ^ (1 - 1 / θ) * excursionHeight θ p.2 t := sorry

/-- **Scaling with a measurable parameter** under the unit law: `(Lebesgue ⊗ unit)`-a.e. in
`(c, e)` (a form J01's common-lifetime mixture can use). -/
theorem ae_prod_excursionHeight_scale_unit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ p ∂(volIoi.prod (unitExcursionLaw θ : Measure Excursion)), ∀ t : ℝ≥0,
      excursionHeight θ (excursionScale θ p.1 p.2) ((p.1 : ℝ).toNNReal * t) =
        (p.1 : ℝ) ^ (1 - 1 / θ) * excursionHeight θ p.2 t := sorry

/-- **Normalization of the pair** under `N`: `H(e)(ζ t) = ζ^(1-1/θ) H(normalizeExc θ e)(t)`. -/
theorem ae_excursionHeight_normalize {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(excursionMeasure θ), ∀ t : ℝ≥0,
      excursionHeight θ e (e.lifetime * t) =
        (e.lifetime : ℝ) ^ (1 - 1 / θ) * excursionHeight θ (normalizeExc θ e) t := sorry

/-! ### Common prefix graph -/

/-- **Graph identity under `N`**, simultaneously for all horizons `a < ζ`: the a.e.-time prefix
map applied to the restricted excursion is the excursion height on `[0,a]`. -/
theorem ae_heightPrefixAE_excursionRestrict {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(excursionMeasure θ), ∀ a : ℝ≥0, a < e.lifetime → ∀ t : Set.Icc (0 : ℝ) a,
      heightPrefixAE θ a (excursionRestrict a e) t = excursionHeight θ e ⟨t, t.2.1⟩ := sorry

/-- **Graph identity under `N ↾ {a < ζ}`** for a fixed horizon `a`. -/
theorem ae_restrict_heightPrefixAE_excursionRestrict {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0) :
    ∀ᵐ e ∂((excursionMeasure θ).restrict {e : Excursion | a < e.lifetime}),
      ∀ t : Set.Icc (0 : ℝ) a,
        heightPrefixAE θ a (excursionRestrict a e) t = excursionHeight θ e ⟨t, t.2.1⟩ := sorry

/-- **Graph identity under the unit law**, simultaneously for all horizons `a < ζ` (`ζ = 1`
a.s.), with the same Borel map `heightPrefixAE θ a`. -/
theorem ae_heightPrefixAE_unitExcursionLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion), ∀ a : ℝ≥0, a < e.lifetime →
      ∀ t : Set.Icc (0 : ℝ) a,
        heightPrefixAE θ a (excursionRestrict a e) t = excursionHeight θ e ⟨t, t.2.1⟩ := sorry

/-- **Graph identity under the tail law** `N(· | ζ > 1)`, simultaneously for all horizons
`a < ζ` (in particular every `a ≤ 1`), with the same Borel map `heightPrefixAE θ a`. -/
theorem ae_heightPrefixAE_tailExcursionLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(tailExcursionLaw θ : Measure Excursion), ∀ a : ℝ≥0, a < e.lifetime →
      ∀ t : Set.Icc (0 : ℝ) a,
        heightPrefixAE θ a (excursionRestrict a e) t = excursionHeight θ e ⟨t, t.2.1⟩ := sorry

/-! ### Brownian case -/

/-- At `θ = 2` (variance-2 library process, `H = X - I`) the excursion height is the excursion
path, `N`-a.e. -/
theorem ae_excursionHeight_two :
    ∀ᵐ e ∂(excursionMeasure 2), ∀ t : ℝ≥0, excursionHeight 2 e t = e.path.1 t := sorry

/-- At `θ = 2` the excursion height is the excursion path under the unit law (K18). -/
theorem ae_excursionHeight_two_unit :
    ∀ᵐ e ∂(unitExcursionLaw 2 : Measure Excursion), ∀ t : ℝ≥0,
      excursionHeight 2 e t = e.path.1 t := sorry

end BGW.StableTrees
