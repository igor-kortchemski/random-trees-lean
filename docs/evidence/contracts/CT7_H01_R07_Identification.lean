import BGW.StableTrees.SupremumDrawdown
import BGW.StableTrees.SupremumReflectedFamily
import BGW.StableTrees.SupremumLocalTime
import BGW.Probability.DoobL2Resolvent
import BGW.StableTrees.StableLocalLaw
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import BGW.StableTrees.SupremumAuxLocalTime
import BGW.StableTrees.SupremumCauchy
import BGW.StableTrees.SupremumPotential

/-! Contract probe for H01 node R07 (blueprint R07; AUDIT: Sol-audit-r05r06 item 8, r04 item 8):
IDENTIFICATION of the public occupation limit with the auxiliary clock of R05/R06, and the
TOTALIZED measurable versions of the public local time, inverse, ladder processes.  It produces
exactly the objects of the final contract `CT7_H01_SupremumLocalTime`: `supEps`, `supLocalTime`,
`supLocalTimeStieltjes`, `supLocalTimeInverse`, `supLadderTime`, `supLadderHeight` (definitions
verbatim) and their sealed-interface statements (R12 re-exports them).
NOT redefined (sealed, imported): `supRunning`, `supReflected`, `supOccupation`,
`IsSupOccupationSeq`, `supLadderExponent` (SupremumLocalTime.lean), `supContact` (R01).
Suppliers consumed by the PROOFS: R05 (`supOccupation_compact_L2_tendsto_supAuxLimit`,
`ae_supAuxLimit_spec`), R06 (`ae_supAuxLocalTime_spec`, `ae_supAuxLocalTime_pos`,
`ae_supAuxStieltjes_support`, `ae_supAuxLocalTime_const_of_lt`, `ae_supAuxLadder_spec`),
sealed `measurable_supOccupation_uncurry`, `IsSupOccupationSeq.ae_tendsto_limsup`,
`DLoc.filtration` (right-continuous).

Proof plan reminders (not statements).  Identification: for ANY `IsSupOccupationSeq θ ε`, the
full-filter `L²` convergence of R05 gives, at each rational `t`, convergence in probability of
`O_{ε_k}(t)` to `M^*_t`; the sequence's own a.s. convergence at every `t` then forces the limit to
equal `M^*_t` a.s.; intersect over rationals, squeeze real `t` by monotonicity of `O_ε` in `t` and
continuity of `M^*`; Dini/monotone approximants give locally uniform convergence.

FLAGS.
(1) Totalization.  The public `supLocalTime` is a REAL `limsup`, which is `0` (junk) when the
occupations are unbounded, so it is NOT everywhere monotone.  Everything is routed through the
ENNReal limsup `supLocalTimeENN` (everywhere nondecreasing in `t`, `supLocalTime = toReal` of it).
The raw public inverse `supLocalTimeInverse` (sInf over `{u | z < M_u}`, `M_u = 0` where the
ENNReal limsup is `⊤`) is shown EVERYWHERE (not a.e.) equal to the explicit extended-valued
measurable representative `supInverseRep` (blueprint's `a < b`, or `a = b < ⊤` with `z < p(a) < ⊤`).
Hence `supLocalTimeInverse`, `supLadderTime`, `supLadderHeight` are everywhere jointly measurable.
(2) The inverse is a stopping time only through `supHitting` (strict hitting time of the ENNReal
limsup; the blueprint's `a`); it equals the public inverse a.s., not everywhere, since the raw
filtration is not completed.  Statements about `shiftAt` in R08 use `supHitting`.
(3) A measurable space on `WithTop ℝ≥0` is not assumed; inverse measurability is stated for the
`ℝ≥0∞` cast `(supLocalTimeInverse θ f z : ℝ≥0∞)`.
(4) Identification is stated for an ARBITRARY occupation sequence (not only `supEps θ`), as the
blueprint requires, so no choice-dependence enters R10/R11.
(5) `ae_supLadder_geometry` records the extra facts R08 needs (unboundedness of `A`, zero
drawdown at `A_z`, `B_z = X_{A_z}`, finiteness of `supHitting`) which are not in the final
contract's `ae_supLadder_spec`.
(6) Estimate 650-1200 lines. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

open scoped Classical in
/-! ### The public occupation sequence (definitions verbatim from the final contract) -/

/-- **Existence.** A single deterministic simultaneous occupation sequence exists (R06's
witness `supAuxEps θ` is NOT claimed to be one; existence follows from identification). -/
theorem exists_isSupOccupationSeq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ ε : ℕ → ℝ, IsSupOccupationSeq θ ε := sorry

open scoped Classical in
/-- The chosen sequence `ε_k ↓ 0`. -/
noncomputable def supEps (θ : ℝ) : ℕ → ℝ :=
  if h : 1 < θ ∧ θ ≤ 2 then Classical.choose (exists_isSupOccupationSeq h)
  else fun k => 1 / ((k : ℝ) + 1)

theorem isSupOccupationSeq_supEps {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    IsSupOccupationSeq θ (supEps θ) := by
  simp only [supEps, hθ, and_self, dite_true]
  exact Classical.choose_spec (exists_isSupOccupationSeq hθ)

/-- The supremum local time `L^S = M`, the limsup of the occupation approximations along
`supEps θ` (real-valued, junk `0` where the occupations are unbounded). -/
noncomputable def supLocalTime (θ : ℝ) (f : DLoc) (t : ℝ≥0) : ℝ :=
  limsup (fun k => supOccupation (supEps θ k) f t) atTop

/-- The ENNReal limsup `p(t)` of the nonnegative occupations along `supEps θ`: the totalized
local time, everywhere nondecreasing in `t`. -/
noncomputable def supLocalTimeENN (θ : ℝ) (f : DLoc) (t : ℝ≥0) : ℝ≥0∞ :=
  limsup (fun k => ENNReal.ofReal (supOccupation (supEps θ k) f t)) atTop

/-- `supLocalTime = (supLocalTimeENN).toReal` for every path and time (both are `0` when
unbounded). -/
theorem supLocalTime_eq_toReal (θ : ℝ) (f : DLoc) (t : ℝ≥0) :
    supLocalTime θ f t = (supLocalTimeENN θ f t).toReal := sorry

/-- `p` is nondecreasing in `t`, for EVERY path and EVERY `θ`. -/
theorem monotone_supLocalTimeENN (θ : ℝ) (f : DLoc) : Monotone (supLocalTimeENN θ f) := sorry

theorem measurable_supLocalTimeENN_uncurry (θ : ℝ) :
    Measurable (fun p : ℝ≥0 × DLoc => supLocalTimeENN θ p.2 p.1) := sorry

/-- Prefix measurability: `p(t)` depends on `f|[0,t]` (raw filtration, no completion). -/
theorem measurable_supLocalTimeENN_filtration (θ : ℝ) (t : ℝ≥0) :
    Measurable[DLoc.filtration t] (fun f : DLoc => supLocalTimeENN θ f t) := sorry

/-- `(t, f) ↦ M_t(f)` is jointly measurable. -/
theorem measurable_supLocalTime_uncurry (θ : ℝ) :
    Measurable (fun p : ℝ≥0 × DLoc => supLocalTime θ p.2 p.1) := sorry

/-- `M` is adapted to the right-continuous filtration (pathwise, no modification needed). -/
theorem stronglyAdapted_supLocalTime (θ : ℝ) :
    StronglyAdapted DLoc.filtration (fun t (f : DLoc) => supLocalTime θ f t) := sorry

theorem measurable_supLocalTime (θ : ℝ) (t : ℝ≥0) :
    Measurable (fun f : DLoc => supLocalTime θ f t) := sorry

/-! ### Identification with the auxiliary clock, for ANY occupation sequence -/

/-- **Identification (arbitrary sequence).** For every simultaneous occupation sequence `ε`,
almost surely, at every time `t` simultaneously, `O_{ε_k}(t) → M^*_t`. -/
theorem ae_tendsto_supOccupation_aux {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℕ → ℝ}
    (hε : IsSupOccupationSeq θ ε) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      Tendsto (fun k => supOccupation (ε k) f t) atTop (𝓝 (supAuxLocalTime θ f t)) := sorry

/-- Locally uniform version for an arbitrary occupation sequence, same event. -/
theorem ae_tendsto_supOccupation_uniform_aux {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℕ → ℝ}
    (hε : IsSupOccupationSeq θ ε) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ T : ℝ≥0,
      Tendsto (fun k => ⨆ t : Set.Iic T, |supOccupation (ε k) f t - supAuxLocalTime θ f t|)
        atTop (𝓝 0) := sorry

/-- The public local time is the auxiliary one, at all times simultaneously. -/
theorem ae_supLocalTime_eq_aux {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      supLocalTime θ f t = supAuxLocalTime θ f t := sorry

/-- The ENNReal totalization agrees with the auxiliary clock on the good event. -/
theorem ae_supLocalTimeENN_eq_aux {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      supLocalTimeENN θ f t = ENNReal.ofReal (supAuxLocalTime θ f t) := sorry

/-- **Simultaneous convergence** on one full-probability event: for every `t`, the approximations
along `supEps θ` converge to `M_t`. -/
theorem ae_tendsto_supOccupation {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      Tendsto (fun k => supOccupation (supEps θ k) f t) atTop (𝓝 (supLocalTime θ f t)) := sorry

/-- **Locally uniform simultaneous convergence** on the same event. -/
theorem ae_tendsto_supOccupation_uniform {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ T : ℝ≥0,
      Tendsto (fun k => ⨆ t : Set.Iic T, |supOccupation (supEps θ k) f t - supLocalTime θ f t|)
        atTop (𝓝 0) := sorry

/-- **Full-filter normalization**: for each fixed `t`, `O_ε(t) → M_t` in probability as `ε ↓ 0`
(not only along `supEps θ`). -/
theorem supOccupation_tendstoInMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    TendstoInMeasure (stableLocalLaw θ : Measure DLoc)
      (fun (ε : ℝ) (f : DLoc) => supOccupation ε f t) (𝓝[>] (0 : ℝ))
      (fun f => supLocalTime θ f t) := sorry

/-! ### Pathwise structure of `M = L^S` (transport of R06) -/

/-- `M_0 = 0`; `M` is monotone, continuous, unbounded (almost surely). -/
theorem ae_supLocalTime_spec {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      supLocalTime θ f 0 = 0 ∧ Monotone (supLocalTime θ f) ∧ Continuous (supLocalTime θ f) ∧
        Tendsto (supLocalTime θ f) atTop atTop := sorry

/-- Immediate increase: `M_t > 0` for `t > 0` (almost surely). -/
theorem ae_supLocalTime_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0, 0 < t → 0 < supLocalTime θ f t :=
  sorry

open scoped Classical in
/-- The Stieltjes function `s ↦ M_{s⁺}` on `ℝ`; junk zero where `M` is not monotone and
continuous (a null set). -/
noncomputable def supLocalTimeStieltjes (θ : ℝ) (f : DLoc) : StieltjesFunction ℝ :=
  if h : Monotone (supLocalTime θ f) ∧ Continuous (supLocalTime θ f) then
    { toFun := fun s => supLocalTime θ f s.toNNReal
      mono' := h.1.comp (fun _ _ hab => Real.toNNReal_mono hab)
      right_continuous' := fun _ =>
        ((h.2.comp continuous_real_toNNReal).continuousAt).continuousWithinAt }
  else
    { toFun := fun _ => 0
      mono' := monotone_const
      right_continuous' := fun _ => continuousWithinAt_const }

/-- **Support on `{S = X}`** (almost surely): `dM` charges no time at which `X < S`. -/
theorem ae_supLocalTimeStieltjes_support {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (supLocalTimeStieltjes θ f).measure
        {s : ℝ | 0 ≤ s ∧ supRunning f s.toNNReal ≠ f.1 s.toNNReal} = 0 := sorry

/-- **Constancy off the zero set**, with left limits, for all `s < t` simultaneously. -/
theorem ae_supLocalTime_const_of_lt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ s t : ℝ≥0, s < t →
      (∀ u ∈ Icc s t, f.1 u < supRunning f u ∧ Function.leftLim f.1 u < supRunning f u) →
        supLocalTime θ f t = supLocalTime θ f s := sorry

/-! ### Inverse local time and ladder processes (definitions verbatim from the final contract) -/

/-- Inverse local time `A_z = inf{t | M_t > z}`. -/
noncomputable def supLocalTimeInverse (θ : ℝ) (f : DLoc) (z : ℝ≥0) : WithTop ℝ≥0 :=
  sInf {t : WithTop ℝ≥0 | ∃ u : ℝ≥0, t = u ∧ (z : ℝ) < supLocalTime θ f u}

/-- Ladder time `A_z` (finite reading, junk `0` on `⊤`). -/
noncomputable def supLadderTime (θ : ℝ) (z : ℝ≥0) (f : DLoc) : ℝ≥0 :=
  (supLocalTimeInverse θ f z).untopD 0

/-- Ladder height `B_z = S_{A_z}`. -/
noncomputable def supLadderHeight (θ : ℝ) (z : ℝ≥0) (f : DLoc) : ℝ :=
  supRunning f (supLadderTime θ z f)

/-- Strict hitting time `a_z = inf{t | p(t) > z}` of the ENNReal clock (the stopping-time
representative of the inverse; `⊤` if never). -/
noncomputable def supHitting (θ : ℝ) (z : ℝ≥0) (f : DLoc) : ℝ≥0∞ :=
  ⨅ t : ℝ≥0, if (z : ℝ≥0∞) < supLocalTimeENN θ f t then (t : ℝ≥0∞) else ⊤

/-- Blow-up time `b = inf{t | p(t) = ⊤}` (`⊤` if never; `b = ⊤` almost surely). -/
noncomputable def supBlowup (θ : ℝ) (f : DLoc) : ℝ≥0∞ :=
  ⨅ t : ℝ≥0, if supLocalTimeENN θ f t = ⊤ then (t : ℝ≥0∞) else ⊤

open scoped Classical in
/-- The explicit measurable representative of the public inverse: `a` if `a < b`, or if
`a = b < ⊤` and `z < p(a) < ⊤` (isolated finite crossing at blow-up); `⊤` otherwise. -/
noncomputable def supInverseRep (θ : ℝ) (z : ℝ≥0) (f : DLoc) : ℝ≥0∞ :=
  if supHitting θ z f < supBlowup θ f ∨
      (supHitting θ z f = supBlowup θ f ∧ supHitting θ z f < ⊤ ∧
        (z : ℝ≥0∞) < supLocalTimeENN θ f (supHitting θ z f).toNNReal ∧
        supLocalTimeENN θ f (supHitting θ z f).toNNReal < ⊤)
  then supHitting θ z f else ⊤

/-- **Junk-safe totalization**: for EVERY `θ`, path and level, the raw public inverse is the
explicit representative. -/
theorem supLocalTimeInverse_eq_rep (θ : ℝ) (f : DLoc) (z : ℝ≥0) :
    (supLocalTimeInverse θ f z : ℝ≥0∞) = supInverseRep θ z f := sorry

theorem measurable_supInverseRep_uncurry (θ : ℝ) :
    Measurable (fun p : ℝ≥0 × DLoc => supInverseRep θ p.1 p.2) := sorry

/-- Everywhere joint measurability of the public inverse (`ℝ≥0∞` cast), for every `θ`. -/
theorem measurable_supLocalTimeInverse_uncurry (θ : ℝ) :
    Measurable (fun p : ℝ≥0 × DLoc => (supLocalTimeInverse θ p.2 p.1 : ℝ≥0∞)) := sorry

/-- Joint measurability of `(z, f) ↦ A_z`, `B_z`, everywhere, for every `θ`. -/
theorem measurable_supLadder_uncurry (θ : ℝ) :
    Measurable (fun p : ℝ≥0 × DLoc => supLadderTime θ p.1 p.2) ∧
      Measurable (fun p : ℝ≥0 × DLoc => supLadderHeight θ p.1 p.2) := sorry

/-- **Stopping time** at every level, for every `θ`: the strict hitting time of the
right-continuous filtration. -/
theorem isStoppingTime_supHitting (θ : ℝ) (z : ℝ≥0) :
    IsStoppingTime DLoc.filtration (supHitting θ z) := sorry

/-- The stopping representative is the public inverse, almost surely, for each level. -/
theorem ae_supHitting_eq_inverse {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      supHitting θ z f = (supLocalTimeInverse θ f z : ℝ≥0∞) := sorry

/-- **Stopping-time property of the inverse local time** (final-contract form). -/
theorem exists_isStoppingTime_supLocalTimeInverse {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    ∃ τ : DLoc → ℝ≥0∞, IsStoppingTime DLoc.filtration τ ∧
      ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), τ f = (supLocalTimeInverse θ f z : ℝ≥0∞) :=
  sorry

/-- Almost surely: `A` finite everywhere, monotone and right-continuous, `A_0 = 0`, `B`
monotone and `M(A_z) = z` for all `z` simultaneously (final-contract form). -/
theorem ae_supLadder_spec {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (∀ z : ℝ≥0, supLocalTimeInverse θ f z = (supLadderTime θ z f : WithTop ℝ≥0)) ∧
        supLadderTime θ 0 f = 0 ∧ Monotone (fun z => supLadderTime θ z f) ∧
        (∀ z, ContinuousWithinAt (fun z => supLadderTime θ z f) (Ici z) z) ∧
        Monotone (fun z => supLadderHeight θ z f) ∧
        ∀ z : ℝ≥0, supLocalTime θ f (supLadderTime θ z f) = z := sorry

/-- The public ladder processes are the auxiliary ones (R06), at all levels simultaneously. -/
theorem ae_supLadder_eq_aux {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ z : ℝ≥0,
      supLadderTime θ z f = supAuxLadderTime θ z f ∧
        supLadderHeight θ z f = supAuxLadderHeight θ z f := sorry

/-- **Extra geometry for R08** (not in the final contract), simultaneously for all levels:
`A` unbounded; `supHitting θ z = A_z` finite; zero drawdown at `A_z` (`A_z ∈ {S = X}`), so
`B_z = X_{A_z}`; `B` right-continuous. -/
theorem ae_supLadder_geometry {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      Tendsto (fun z => supLadderTime θ z f) atTop atTop ∧
      (∀ z : ℝ≥0, supHitting θ z f = (supLadderTime θ z f : ℝ≥0∞)) ∧
      (∀ z : ℝ≥0, supReflected f (supLadderTime θ z f) = 0) ∧
      (∀ z : ℝ≥0, supLadderHeight θ z f = f.1 (supLadderTime θ z f)) ∧
      ∀ z : ℝ≥0, ContinuousWithinAt (fun z => supLadderHeight θ z f) (Ici z) z := sorry

end BGW.StableTrees
