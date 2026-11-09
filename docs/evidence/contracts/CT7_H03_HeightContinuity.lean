import BGW.Skorokhod.DLoc
import BGW.Skorokhod.ReverseIncrements
import BGW.StableTrees.StableLocalLaw
import BGW.StableTrees.SupremumLocalTimePublic
import BGW.StableTrees.ExcursionMeasure
import BGW.StableTrees.UnitExcursionLaw
import BGW.ContinuumTrees.ExcursionCarrier
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import BGW.StableTrees.HeightProcess
import BGW.StableTrees.HeightBridges

/-! Contract probe for CT7 node H03 (`r3-ct7-blueprint/blueprint.md` H03, `r5-ct8-blueprint`
§2 item 3): moment bounds for the height process of the `θ`-stable process and ONE common
continuous version, with a measurable prefix map on every horizon.

DEFINITIONS.  `height θ f t` is H02's fixed-time height (H02 sealed, imported); `heightUniv`
and `heightEps` are copied from the H02b contract.
`heightLoc θ f` is the unique continuous function on `ℝ≥0` agreeing with `height θ f` at every
rational time when one exists, and `0` otherwise, where the rational-time values are
`heightUniv θ f q`, the approximations read along H02b's universal sequence `heightEps θ`
(redesign of 7 Nov 2026: one sequence that converges a.s. under the stable law, under `N` and
under the unit law, so the same Borel prefix map serves every law; under the stable law
`heightUniv` is H02's `height` at every rational time a.s., `ae_heightUniv_eq_height`).  It is
continuous for EVERY path, and the
content of H03 is that the first branch occurs a.s. and that the version has the right
marginals.  `extendConst T g` extends a path on `[0,T]` by its terminal value;
`heightPrefix θ T g` is the analogous continuous reconstruction on `[0,T]` from rational
heights of `extendConst T g`.  `height θ f q` reads `f` only on `[0,q]` (`reversedAt q` uses
left limits at times `≤ q`, and the sealed `supLocalTime` is a limsup of occupations of
`[0,q]`), so on `[0,T]` the prefix map of `DLoc.restrict T f` reconstructs `heightLoc θ f`.

TRUTH CHECK.  `β = 1 - 1/θ ∈ (0, 1/2]`.  (1) Moments: by scaling `H_{cs} =ᵈ c^β H_s`; the
fixed-time decomposition of the route below gives tails `P(|H_{t+s} - H_t| > v) ≤
2e exp(-v s^(-β))`, uniformly in `t`, so every moment is finite and
`E|H_{t+s} - H_t|^p ≤ C(θ,p) s^(pβ)` with one constant for all `t, s`.  The integrability
conjunct prevents the vacuous reading of a Bochner integral of a non-integrable function.
(2) Kolmogorov-Chentsov with `pβ > 1` gives a continuous modification, locally `γ`-Hölder for
every `γ < β` (taking `p > 1/(β - γ)`); it agrees with `height` at all rationals a.s., so the
`∃ g` branch of `heightLoc` holds a.s. and `heightLoc θ f t = height θ f t` a.s. for each `t`.
(3) `H_0 = 0` and `H ≥ 0` (limsup of nonnegative occupations).  (4) Measurability: the
existence event and the reconstruction are countable operations on measurable rational
evaluations (H02 `measurable_height_uncurry`); `C(Icc 0 T, ℝ)` carries the Mathlib Borel
structure of the uniform topology.  (5) At `θ = 2` (`H = X - I`, H02 `ae_height_two`) all
statements are consistent with Brownian reflection, Hölder exponents `< 1/2`.

PROOF PLAN (CT7 blueprint H03; avoid any continuity premise).  Consume the H02b bridges
`ae_height_erasure_decomposition` and `erased_height_tail_le` (contract
`CT7_H02b_HeightBridges.lean`; obligations of H02b, not of H02): for fixed `t, s`, with `K` the
support height of `eraseMass (-I'_s) ρ_t`, `H_{t+s} = K + H'_s`, `0 ≤ K ≤ H_t`, and the tail of
`H_t - K`.  Write `H_{t+s} - H_t = A - B`, `A = H_s(shift t f) ≥ 0`, `B = H_t - K ≥ 0`, and bound
both tails by `e exp(-v s^(-β))`: `P(M_s > v) ≤ e exp(-v s^(-β))` (H01 ladder transform) for `A`;
for `B`, the event forces a reversed ladder height `B_v` below the independent depth `-I'_s`
(`P(-I_s ≥ b) ≤ e exp(-b s^(-α))`, N09), giving `e E exp(-s^(-α) B_v) = e exp(-v s^(-β))`.
CAUTION (Sol audit h03, finding 1): `reversedAt t f` is constant after `t`, so its unrestricted
ladder process does not have the stable ladder transform; use an independent continuation of the
reversed prefix (independent of the fresh depth) with the stopped-time comparison, as H02b
requires.  No premise may use `heightLoc`, height continuity, minima of a height path,
Ray-Knight continuity, or CT8.  Tail integration gives `C = 2e Γ(p+1)`.  Then the vendored
Kolmogorov-Chentsov theorem
(`vendor/brownian-motion`, `exists_modification_holder_iSup`) on the horizons `[0,n]`, rational
agreement for a common version, and the Borel reconstruction for `heightPrefix`.  If removing
the continuity premise fails, report: the alternative (Ray-Knight and the extinction ODE) adds
2500-5000 lines and needs a new decision.  Size 1000-2000 lines; very high difficulty.

ACYCLICITY.  Suppliers: H01 (`SupremumLocalTimePublic`), H02, H02b, N09, sealed stable process laws,
the vendored Kolmogorov-Chentsov theorem.  No CT8 node.

BINDER SCOPE (AUDITOR_RULES): the Bochner integral body `|height θ f (t + s) - height θ f t| ^ p`
is delimited by `∂`; the subtraction is inside the absolute value. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees

/-! ### Moment bound -/

/-- **Increment moments** with one constant for all `t` and `s`:
`E|H_{t+s} - H_t|^p ≤ C s^(p (1 - 1/θ))`, the integrand being integrable. -/
theorem height_increment_moment_bound {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t s : ℝ≥0, 0 < s →
      Integrable (fun f : DLoc => |height θ f (t + s) - height θ f t| ^ p)
        (stableLocalLaw θ : Measure DLoc) ∧
      ∫ f, |height θ f (t + s) - height θ f t| ^ p ∂(stableLocalLaw θ : Measure DLoc) ≤
        C * (s : ℝ) ^ (p * (1 - 1 / θ)) := sorry

/-! ### The continuous version on `ℝ≥0` -/

/-- `t` is a rational time. -/
def IsRationalTime (t : ℝ≥0) : Prop := ∃ q : ℚ, (q : ℝ) = t

/-- **The continuous height process**: the continuous function agreeing with `heightUniv θ f` at
every rational time when one exists (it is then unique), the zero function otherwise. -/
noncomputable def heightLoc (θ : ℝ) (f : DLoc) : ℝ≥0 → ℝ :=
  if h : ∃ g : C(ℝ≥0, ℝ), ∀ t : ℝ≥0, IsRationalTime t → g t = heightUniv θ f t then
    ⇑(Classical.choose h) else fun _ => 0

/-- Every path of `heightLoc` is continuous. -/
theorem continuous_heightLoc (θ : ℝ) (f : DLoc) : Continuous (heightLoc θ f) := sorry

theorem measurable_heightLoc_uncurry (θ : ℝ) :
    Measurable (fun p : ℝ≥0 × DLoc => heightLoc θ p.2 p.1) := sorry

/-- Almost surely the rational heights (read along `heightEps θ`) extend continuously. -/
theorem ae_exists_continuous_height {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ∃ g : C(ℝ≥0, ℝ), ∀ t : ℝ≥0, IsRationalTime t → g t = heightUniv θ f t := sorry

/-- **Modification**: for each fixed time, `heightLoc` agrees a.s. with H02's height. -/
theorem ae_heightLoc_eq_height {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), heightLoc θ f t = height θ f t := sorry

/-- The continuous height starts at `0` for every path (`height θ f 0 = 0` surely). -/
theorem heightLoc_zero (θ : ℝ) (f : DLoc) : heightLoc θ f 0 = 0 := sorry

/-- The continuous height is nonnegative for every path. -/
theorem heightLoc_nonneg (θ : ℝ) (f : DLoc) (t : ℝ≥0) : 0 ≤ heightLoc θ f t := sorry

/-- Almost surely the continuous height is locally `γ`-Hölder for every `γ < 1 - 1/θ`. -/
theorem ae_heightLoc_locallyHolder {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ : γ < 1 - 1 / θ) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ T : ℝ≥0, ∃ C : ℝ, ∀ s t : ℝ≥0, s ≤ T → t ≤ T →
      |heightLoc θ f s - heightLoc θ f t| ≤ C * |(s : ℝ) - t| ^ γ := sorry

/-! ### Prefix map on a finite horizon -/

/-- Extension of a path on `[0,T]` by its terminal value (the junk branch never occurs). -/
noncomputable def extendConst (T : ℝ≥0) (g : D (T : ℝ) ℝ) : DLoc :=
  if h : IsCadlag (fun u : ℝ≥0 => g (Set.projIcc 0 (T : ℝ) T.2 u)) then
    ⟨fun u => g (Set.projIcc 0 (T : ℝ) T.2 u), h⟩ else DLoc.zero

/-- **Prefix height map** on `[0,T]`: the continuous function on `[0,T]` agreeing with
`heightUniv` of `extendConst T g` at the rational times of `[0,T]` when one exists, `0`
otherwise. -/
noncomputable def heightPrefix (θ : ℝ) (T : ℝ≥0) (g : D (T : ℝ) ℝ) :
    C(Set.Icc (0 : ℝ) T, ℝ) :=
  if h : ∃ c : C(Set.Icc (0 : ℝ) T, ℝ), ∀ t : Set.Icc (0 : ℝ) T, (∃ q : ℚ, (q : ℝ) = t) →
      c t = heightUniv θ (extendConst T g) ⟨t, t.2.1⟩ then Classical.choose h else 0

theorem isCadlag_extendConst_fun (T : ℝ≥0) (g : D (T : ℝ) ℝ) :
    IsCadlag (fun u : ℝ≥0 => g (Set.projIcc 0 (T : ℝ) T.2 u)) := sorry

theorem restrict_extendConst (T : ℝ≥0) (g : D (T : ℝ) ℝ) :
    DLoc.restrict T (extendConst T g) = g := sorry

theorem measurable_extendConst (T : ℝ≥0) : Measurable (extendConst T) := sorry

/-- **Literal prefix locality** of the raw height: `height θ f t` reads `f` only on `[0,t]`. -/
theorem height_eq_of_restrict_eq (θ : ℝ) (T : ℝ≥0) (f g : DLoc)
    (hfg : DLoc.restrict T f = DLoc.restrict T g) (t : ℝ≥0) (ht : t ≤ T) :
    height θ f t = height θ g t := sorry

theorem measurable_heightPrefix (θ : ℝ) (T : ℝ≥0) : Measurable (heightPrefix θ T) := sorry

/-- **Deterministic reconstruction**: a continuous function on `[0,T]` agreeing with
`heightUniv θ f` at the rational times of `[0,T]` is the prefix height of `f` (no law
involved; used by H04 under the excursion measures). -/
theorem heightPrefix_eq_of_rational_agreement (θ : ℝ) (T : ℝ≥0) (f : DLoc)
    (c : C(Set.Icc (0 : ℝ) T, ℝ))
    (hc : ∀ t : Set.Icc (0 : ℝ) T, IsRationalTime ⟨t, t.2.1⟩ →
      c t = heightUniv θ f ⟨t, t.2.1⟩) :
    heightPrefix θ T (DLoc.restrict T f) = c := sorry

/-- **Graph identity**: almost surely, on every time of `[0,T]`, the prefix map applied to the
restriction of the path is the continuous height. -/
theorem ae_heightPrefix_restrict {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : Set.Icc (0 : ℝ) T,
      heightPrefix θ T (DLoc.restrict T f) t = heightLoc θ f ⟨t, t.2.1⟩ := sorry

/-- **Graph identity on one event for all horizons** (CT8 blueprint §2 item 3). -/
theorem ae_heightPrefix_restrict_all {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ T : ℝ≥0, ∀ t : Set.Icc (0 : ℝ) T,
      heightPrefix θ T (DLoc.restrict T f) t = heightLoc θ f ⟨t, t.2.1⟩ := sorry

/-- Fixed-time evaluation of the prefix map is H02's height a.s. -/
theorem ae_heightPrefix_eval {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) (t : Set.Icc (0 : ℝ) T) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      heightPrefix θ T (DLoc.restrict T f) t = height θ f ⟨t, t.2.1⟩ := sorry

/-- **Pair law**: the walk/height pair on `[0,T]` is the graph pushforward of the stable process
law on `[0,T]` (all `T`, including `T = 0`). -/
theorem map_heightPrefix_pair {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) :
    (stableLocalLaw θ : Measure DLoc).map
        (fun f => (DLoc.restrict T f, heightPrefix θ T (DLoc.restrict T f))) =
      (stableProcessLaw θ (T : ℝ) : Measure (D (T : ℝ) ℝ)).map
        (fun g => (g, heightPrefix θ T g)) := sorry

end BGW.StableTrees
