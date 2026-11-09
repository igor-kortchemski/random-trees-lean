import BGW.Skorokhod.DLoc
import BGW.Skorokhod.ReverseIncrements
import BGW.StableTrees.StableLocalLaw
import BGW.StableTrees.StableLocalMarkov
import BGW.StableTrees.StableStrongMarkov
import BGW.StableTrees.StableRegularity
import BGW.StableTrees.StableFirstPassage
import BGW.StableTrees.StablePassageSubordinator
import BGW.StableTrees.StableProcessReversal
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Contract probe for CT7 blueprint node H01 (C26 foundation): the local time at `0` of the
reflected-at-supremum process `S - X` of the spectrally positive stable process
`stableLocalLaw θ`, its inverse (ladder time process), the ladder height process, and the
joint ladder transform.

Conventions.
* Laplace exponent: sealed `integral_exp_neg_passageLaw` gives `E e^{-q T_x} = e^{-x q^{1/θ}}`,
  i.e. `E e^{-λ X_t} = e^{t λ^θ}`. So `ψ(λ) = λ^θ`.
* `supRunning f t = sup_{u ≤ t} f u` (real-valued; `f` is càdlàg so the sup is bounded).
  `S - X ≥ 0` always. The ascending ladder set `{S = X}` is entered by upward jumps that land at
  or above the previous supremum (an arbitrary upward jump of `X` need not reach the running
  supremum), and by creeping-free returns; it is the mirror of the infimum side, where
  `localTime = -runningInf` and the process creeps downward.
* AUDIT item 2: ONE deterministic sequence `supEps θ k ↓ 0` (not one per path), whose occupation
  approximations converge for ALL `t` simultaneously on one full-probability event.
  `supLocalTime θ` is defined as the limsup along that sequence; `supEps θ` is chosen from the
  existence theorem `exists_isSupOccupationSeq` (junk `1/(k+1)` for `θ ∉ (1, 2]`).
* NORMALIZATION (c = 1, audited): the occupation normalization pins the constant. By duality,
  `S - X` at an independent exponential time of rate `q` is `Exp(q^{1/θ})`, so
  `E exp(-q A_z - λ B_z) = exp(-z κ(q,λ))` with `κ = supLadderExponent θ q λ` exactly, and the
  marginals are `exp(-z q^{1-1/θ})`, `exp(-z λ^{θ-1})`. Consistently `M(A_z) = z` and
  `E[occupation up to A_z] = z`.
* The deterministic subsequence `supEps θ` is selected AFTER the stopped Cauchy / `L²`-convergence
  estimates below (`supOccupation_stopped_L2_bound`, `supOccupation_stopped_L2_tendsto`), which
  do not use it; this avoids circularity with `exists_isSupOccupationSeq`.
* H01 convergence does not by itself hold simultaneously for every reversed prefix; convergence
  along ancestral times is H02's separate obligation.
* Adaptedness holds pathwise for `supLocalTime θ · t` (it depends on `f|[0,t]` through a limsup of
  measurable maps). The inverse `A_z` is a stopping time only up to a null set (the raw filtration
  is not completed and `M` is monotone only a.s.), so that statement is for an a.s. modification.
* `supLocalTimeInverse θ f z = inf{t | M_t > z}` (`WithTop ℝ≥0`); `A_z`, `B_z` are its finite
  reading and `S_{A_z}`; finiteness is almost sure.
* The time-reversal identity (`H_t` = supremum local time of the reversed process) is H02. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees

/-- Running supremum `S_t = sup_{u ≤ t} X_u`. -/
noncomputable def supRunning (f : DLoc) (t : ℝ≥0) : ℝ := ⨆ u : Set.Iic t, f.1 u

/-- The reflected-at-supremum process `S_t - X_t`. -/
noncomputable def supReflected (f : DLoc) (t : ℝ≥0) : ℝ := supRunning f t - f.1 t

/-- Occupation approximation `ε⁻¹ · Leb{s ≤ t | S_s - X_s < ε}`. -/
noncomputable def supOccupation (ε : ℝ) (f : DLoc) (t : ℝ≥0) : ℝ :=
  ε⁻¹ * (volume {s : ℝ | 0 ≤ s ∧ s ≤ (t : ℝ) ∧ supReflected f s.toNNReal < ε}).toReal

/-- A deterministic sequence is a *simultaneous occupation sequence*: positive, strictly decreasing
to `0`, and almost surely the approximations converge at every time at once. -/
def IsSupOccupationSeq (θ : ℝ) (ε : ℕ → ℝ) : Prop :=
  (∀ k, 0 < ε k) ∧ StrictAnti ε ∧ Tendsto ε atTop (𝓝 0) ∧
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      ∃ ℓ : ℝ, Tendsto (fun k => supOccupation (ε k) f t) atTop (𝓝 ℓ)

/-- **Audit item 2 (existence).** A single deterministic simultaneous occupation sequence exists. -/
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
`supEps θ`. -/
noncomputable def supLocalTime (θ : ℝ) (f : DLoc) (t : ℝ≥0) : ℝ :=
  limsup (fun k => supOccupation (supEps θ k) f t) atTop

/-- `(t, f) ↦ M_t(f)` is jointly measurable. -/
theorem measurable_supLocalTime_uncurry (θ : ℝ) :
    Measurable (fun p : ℝ≥0 × DLoc => supLocalTime θ p.2 p.1) := sorry

/-- **Simultaneous convergence** on one full-probability event: for every `t`, the approximations
along `supEps θ` converge to `M_t`. -/
theorem ae_tendsto_supOccupation {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      Tendsto (fun k => supOccupation (supEps θ k) f t) atTop (𝓝 (supLocalTime θ f t)) := sorry

/-- **Locally uniform simultaneous convergence** on the same event: for every `T`,
`sup_{t ≤ T} |ε_k⁻¹ Leb{S-X<ε_k, s ≤ t} - M_t| → 0`. -/
theorem ae_tendsto_supOccupation_uniform {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ T : ℝ≥0,
      Tendsto (fun k => ⨆ t : Set.Iic T, |supOccupation (supEps θ k) f t - supLocalTime θ f t|)
        atTop (𝓝 0) := sorry

/-- **Blueprint normalization**: for each fixed `t`, the FULL (not only subsequential)
approximation converges to `M_t` in probability as `ε ↓ 0`. -/
theorem supOccupation_tendstoInMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    TendstoInMeasure (stableLocalLaw θ : Measure DLoc)
      (fun (ε : ℝ) (f : DLoc) => supOccupation ε f t) (𝓝[>] (0 : ℝ))
      (fun f => supLocalTime θ f t) := sorry

/-! ### Pathwise structure of `M = L^S` -/

/-- `M_0 = 0`; `M` is monotone, continuous, unbounded (almost surely). -/
theorem ae_supLocalTime_spec {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      supLocalTime θ f 0 = 0 ∧ Monotone (supLocalTime θ f) ∧ Continuous (supLocalTime θ f) ∧
        Tendsto (supLocalTime θ f) atTop atTop := sorry

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

/-- **Constancy off the zero set**, with left limits: if on `[s, t]` the process stays strictly
below its running supremum (also in left limits), `M` is constant there. Almost surely, for all
`s < t` simultaneously. -/
theorem ae_supLocalTime_const_of_lt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ s t : ℝ≥0, s < t →
      (∀ u ∈ Icc s t, f.1 u < supRunning f u ∧ Function.leftLim f.1 u < supRunning f u) →
        supLocalTime θ f t = supLocalTime θ f s := sorry

/-- `M` is adapted to the right-continuous filtration (pathwise, no modification needed). -/
theorem stronglyAdapted_supLocalTime (θ : ℝ) :
    StronglyAdapted DLoc.filtration (fun t (f : DLoc) => supLocalTime θ f t) := sorry

/-- `M` is adapted-measurable at each fixed time (path measurability of `M_t`). -/
theorem measurable_supLocalTime (θ : ℝ) (t : ℝ≥0) :
    Measurable (fun f : DLoc => supLocalTime θ f t) := sorry

/-! ### Inverse local time and ladder processes -/

/-- Inverse local time `A_z = inf{t | M_t > z}`. -/
noncomputable def supLocalTimeInverse (θ : ℝ) (f : DLoc) (z : ℝ≥0) : WithTop ℝ≥0 :=
  sInf {t : WithTop ℝ≥0 | ∃ u : ℝ≥0, t = u ∧ (z : ℝ) < supLocalTime θ f u}

/-- Ladder time `A_z` (finite reading, junk `0` on `⊤`). -/
noncomputable def supLadderTime (θ : ℝ) (z : ℝ≥0) (f : DLoc) : ℝ≥0 :=
  (supLocalTimeInverse θ f z).untopD 0

/-- Ladder height `B_z = S_{A_z}`. -/
noncomputable def supLadderHeight (θ : ℝ) (z : ℝ≥0) (f : DLoc) : ℝ :=
  supRunning f (supLadderTime θ z f)

/-- Joint measurability of `(z, f) ↦ A_z`, `B_z`. -/
theorem measurable_supLadder_uncurry (θ : ℝ) :
    Measurable (fun p : ℝ≥0 × DLoc => supLadderTime θ p.1 p.2) ∧
      Measurable (fun p : ℝ≥0 × DLoc => supLadderHeight θ p.1 p.2) := sorry

/-- Almost surely: `A` is finite everywhere, monotone and right-continuous, `A_0 = 0`, and `B` is
monotone and `M(A_z) = z` for all `z` simultaneously (`A_z` is the right-continuous inverse). -/
theorem ae_supLadder_spec {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (∀ z : ℝ≥0, supLocalTimeInverse θ f z = (supLadderTime θ z f : WithTop ℝ≥0)) ∧
        supLadderTime θ 0 f = 0 ∧ Monotone (fun z => supLadderTime θ z f) ∧
        (∀ z, ContinuousWithinAt (fun z => supLadderTime θ z f) (Ici z) z) ∧
        Monotone (fun z => supLadderHeight θ z f) ∧
        ∀ z : ℝ≥0, supLocalTime θ f (supLadderTime θ z f) = z := sorry

/-- The blueprint's ladder exponent `κ(q, λ) = (q - λ^θ) / (q^{1/θ} - λ)`, extended continuously
at `λ = q^{1/θ}` by `θ q^{1 - 1/θ}`. -/
noncomputable def supLadderExponent (θ q lam : ℝ) : ℝ :=
  if lam = q ^ (1 / θ) then θ * q ^ (1 - 1 / θ) else (q - lam ^ θ) / (q ^ (1 / θ) - lam)

/-- **Joint ladder transform** (normalization `c = 1`) at every deterministic level `z ≥ 0`, and
its two marginals (`κ(q,0) = q^{1-1/θ}`, `κ(0,λ) = λ^{θ-1}`):
`E exp(-q A_z - λ B_z) = exp(-z κ(q, λ))` for `q, λ ≥ 0`. -/
theorem integral_exp_neg_supLadder {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) {q lam : ℝ}
    (hq : 0 ≤ q) (hlam : 0 ≤ lam) :
    (∫ f, Real.exp (-q * (supLadderTime θ z f : ℝ) - lam * supLadderHeight θ z f)
          ∂(stableLocalLaw θ : Measure DLoc) =
        Real.exp (-(z : ℝ) * supLadderExponent θ q lam)) ∧
      (∫ f, Real.exp (-q * (supLadderTime θ z f : ℝ)) ∂(stableLocalLaw θ : Measure DLoc) =
        Real.exp (-(z : ℝ) * q ^ (1 - 1 / θ))) ∧
      (∫ f, Real.exp (-lam * supLadderHeight θ z f) ∂(stableLocalLaw θ : Measure DLoc) =
        Real.exp (-(z : ℝ) * lam ^ (θ - 1))) := sorry

/-- **Stopping-time property of the inverse local time**, for the right-continuous filtration,
up to a null set: there is a stopping time `τ` of `DLoc.filtration` almost surely equal to
`A_z = supLocalTimeInverse θ · z` (the filtration is not completed). -/
theorem exists_isStoppingTime_supLocalTimeInverse {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    ∃ τ : DLoc → ℝ≥0∞, IsStoppingTime DLoc.filtration τ ∧
      ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), τ f = (supLocalTimeInverse θ f z : ℝ≥0∞) := sorry

/-- **Restart identity at `A_z`.** Let `f' = shiftAt A_z f` be the post-`A_z` centered path. Almost
surely `X_{A_z} = S_{A_z} = B_z` (so there is no overshoot at `A_z` itself: it is a right-accumulation
point of `{S = X}`), the reflected process restarts, `S_{A_z+t} = B_z + S'_t`, and
`M(A_z + t) = z + M'(t)` for all `t`, where `S', M'` are computed from `f'`. -/
theorem ae_supRestart_at_ladderTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      supLadderHeight θ z f = f.1 (supLadderTime θ z f) ∧
      ∀ t : ℝ≥0,
        supReflected f (supLadderTime θ z f + t) =
            supReflected (DLoc.shiftAt (fun g => (supLadderTime θ z g : ℝ≥0∞)) f) t ∧
        supRunning f (supLadderTime θ z f + t) =
            supLadderHeight θ z f +
              supRunning (DLoc.shiftAt (fun g => (supLadderTime θ z g : ℝ≥0∞)) f) t ∧
        supLocalTime θ f (supLadderTime θ z f + t) =
            (z : ℝ) + supLocalTime θ (DLoc.shiftAt (fun g => (supLadderTime θ z g : ℝ≥0∞)) f) t :=
  sorry

/-! ### Stopped inverse-local-time bounds (the construction estimates) -/

/-- **Stopped second-moment bound**: for each level `z` there is `C` bounding, uniformly in
`ε ∈ (0, 1]`, the second moment of the approximation stopped at the ladder time `A_z`; the
squared approximation is integrable. -/
theorem supOccupation_stopped_L2_bound {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Integrable (fun f => (supOccupation ε f (supLadderTime θ z f)) ^ 2)
          (stableLocalLaw θ : Measure DLoc) ∧
      ∫ f, (supOccupation ε f (supLadderTime θ z f)) ^ 2 ∂(stableLocalLaw θ : Measure DLoc) ≤ C :=
  sorry

/-- **Stopped `L²` convergence**: `E[(supOccupation ε f (A_z) - z)²] → 0` as `ε ↓ 0`
(consistent with `M(A_z) = z`). Not circular: it precedes the choice of `supEps`. -/
theorem supOccupation_stopped_L2_tendsto {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Integrable (fun f => (supOccupation ε f (supLadderTime θ z f) - (z : ℝ)) ^ 2)
        (stableLocalLaw θ : Measure DLoc)) ∧
    Tendsto (fun ε : ℝ =>
        ∫ f, (supOccupation ε f (supLadderTime θ z f) - (z : ℝ)) ^ 2
          ∂(stableLocalLaw θ : Measure DLoc)) (𝓝[>] (0 : ℝ)) (𝓝 0) := sorry

/-- **Stopped Cauchy bound**: the approximations stopped at `A_z` converge to `M(A_z) = z`
uniformly over the stopped time interval, in probability, as `ε ↓ 0` along the full filter. -/
theorem supOccupation_stopped_uniform_tendstoInMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0)
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun ε : ℝ =>
        (stableLocalLaw θ : Measure DLoc)
          {f | δ ≤ ⨆ t : Set.Iic (supLadderTime θ z f),
              |supOccupation ε f t - supLocalTime θ f t|})
      (𝓝[>] (0 : ℝ)) (𝓝 0) := sorry

end BGW.StableTrees
