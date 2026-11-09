import BGW.StableTrees.SupremumDrawdown
import BGW.StableTrees.SupremumReflectedFamily
import BGW.StableTrees.SupremumLocalTime
import BGW.Probability.DoobL2Resolvent
import BGW.StableTrees.StableLocalLaw
import BGW.StableTrees.SupremumPotential

/-! Contract probe for H01 node R05 (blueprint R05, plus the construction half of R06 that is
pure convergence: summable-error subsequence, uniform limit, continuity and monotonicity of
`M^*`; AUDIT items 3, 8): the martingale `J^{ε,η}_t = E[B_ε - B_η | F_t]` of the discounted
occupation difference, the Doob `L²` maximal bound on compacts, the compact-time Cauchy estimate
`E sup_{t ≤ T} |O_ε(t) - O_η(t)|² ≤ C_T (D + D²)` with explicit constant, the fast
subsequence, and the limit process `M^*` (`supAuxLimit`).  Depends on R04.
NOT redefined: `supRunning`, `supReflected`, `supOccupation` (W49), `supReflectedFrom` (R01,
sealed), `discountedOccupation`, `ResolventMarkov`, `martingale_discounted_resolvent`,
`lintegral_sq_sup_Icc_le_four_mul_of_martingale` (R05a, sealed).  Suppliers consumed by the
PROOFS: R04 (`supOccupationResolvent`, `resolventMarkov_supReflectedFrom_sub`,
`exists_forall_abs_supOccupationResolvent_sub_le`, `integral_sq_discountedOccupation_..._le`,
`continuousOn_supOccupationResolvent`), R01 (`continuous_supOccupation`, càdlàg reflection).

Notation. `P = stableLocalLaw θ`; `R^0_t = supReflectedFrom 0 f t` (equals `supReflected f t`
whenever `f.1 0 = 0`, a.s.); `g_ε = supOccKernel ε`; `u^1_ε = supOccupationResolvent θ 1 ε`;
`k = g_ε - g_η`, `V = u¹_ε - u¹_η`; `O_ε = supOccupation ε`;
`J_t = ∫_0^t e^{-s} k(R_s) ds + e^{-t} V(R_t)`; `K_t = J_t - e^{-t}V(R_t) = ∫_0^t e^{-s}dC_s`,
`C = O_ε - O_η`; `D` a bound for `‖V‖_∞`.

DERIVATION OF THE CONSTANT (mine; the blueprint writes `C_T (d + d²)` without `C_T`).
`C_t = e^t K_t - ∫_0^t e^s K_s ds`, so `sup_{t≤T}|C_t| ≤ 2e^T sup_{t≤T}|K_t|` and
`|K_t| ≤ |J_t| + D`.  Doob: `E sup|J|² ≤ 4E J_T² ≤ 4E(B_ε-B_η)² ≤ 16D` (Jensen, R04 bound `4D`).
Hence `E sup|K|² ≤ 2·16D + 2D²` and `E sup|C|² ≤ 4e^{2T}(32D+2D²) ≤ 128 e^{2T}(D+D²)`.
FLAGS. (1) `C_T = 128 e^{2T}` is a safe explicit choice, independent of θ, ε, η; only its
dependence on `T` matters downstream.  (2) The blueprint's `Tendsto`-form `M^*` is built here by a
deterministic sequence `supAuxEps` (not `supEps`, which is H01's final choice) via R07's `IsSup..`
pattern; `supAuxLimit` is the REAL `limsup`, hence only a.s. monotone/continuous (the totalization
to an everywhere-monotone ENNReal limsup is R07's problem).  (3) The a.s. statements are over
`P` and quantify `∀ t`/`∀ T` inside, so the null set is independent of `t`.  (4) Estimate
1100-2000 lines. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-! ### Definitions -/

/-- `sup_{t ≤ T} |O_ε(t) - O_η(t)|` (blueprint `compactError`). -/
noncomputable def compactError (ε η : ℝ) (T : ℝ≥0) (f : DLoc) : ℝ :=
  ⨆ t : Set.Iic T, |supOccupation ε f t - supOccupation η f t|

/-- The martingale `J_t = ∫_0^t e^{-s}(g_ε-g_η)(R^0_s)ds + e^{-t}(u¹_ε-u¹_η)(R^0_t)`
(`= E[B_ε - B_η | F_t]`; the explicit version of R05a `martingale_discounted_resolvent`). -/
noncomputable def occupationDiffMartingale (θ ε η : ℝ) (t : ℝ≥0) (f : DLoc) : ℝ :=
  (∫ s in Ioc (0 : ℝ) t, Real.exp (-s) *
      (supOccKernel ε (supReflectedFrom 0 f s.toNNReal) -
        supOccKernel η (supReflectedFrom 0 f s.toNNReal))) +
    Real.exp (-(t : ℝ)) * (supOccupationResolvent θ 1 ε (supReflectedFrom 0 f t) -
      supOccupationResolvent θ 1 η (supReflectedFrom 0 f t))

/-- A fast sequence: positive, strictly decreasing to `0`, and for every `k` and every
`η ∈ (0, ε_k]` the squared compact error on `[0,k]` is integrable with mean `≤ 16⁻ᵏ`
(summable errors on integer horizons; Borel–Cantelli with thresholds `2⁻ᵏ`). -/
def IsSupAuxEpsSeq (θ : ℝ) (ε : ℕ → ℝ) : Prop :=
  (∀ k, 0 < ε k) ∧ StrictAnti ε ∧ Tendsto ε atTop (𝓝 0) ∧
    ∀ k : ℕ, ∀ η : ℝ, 0 < η → η ≤ ε k →
      Integrable (fun f => (compactError (ε k) η k f) ^ 2) (stableLocalLaw θ : Measure DLoc) ∧
      ∫ f, (compactError (ε k) η k f) ^ 2 ∂(stableLocalLaw θ : Measure DLoc) ≤ (1 / 16 : ℝ) ^ k

/-! ### Occupation as a reflected functional and the martingale -/

theorem measurable_compactError {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (T : ℝ≥0) :
    Measurable (compactError ε η T) := sorry

/-- `O_ε(t) = ∫_0^t g_ε(R^0_s) ds` for all `t` simultaneously, almost surely. -/
theorem ae_supOccupation_eq_integral_supOccKernel {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      supOccupation ε f t =
        ∫ s in Ioc (0 : ℝ) t, supOccKernel ε (supReflectedFrom 0 f s.toNNReal) := sorry

theorem martingale_occupationDiffMartingale {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) :
    Martingale (fun t f => occupationDiffMartingale θ ε η t f) DLoc.filtration
      (stableLocalLaw θ : Measure DLoc) := sorry

/-- Every path of `J` is right continuous (càdlàg reflection, `u¹_ε - u¹_η` continuous on
`[0,∞)`), as the compact-time Doob inequality needs for ALL `f`. -/
theorem rightContinuous_occupationDiffMartingale {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (f : DLoc) (t : ℝ≥0) :
    ContinuousWithinAt (fun s : ℝ≥0 => occupationDiffMartingale θ ε η s f) (Ici t) t := sorry

/-! ### Maximal and Cauchy estimates -/

/-- **Doob `L²` on compacts**: if `‖u¹_ε - u¹_η‖_∞ ≤ D` then
`E sup_{t≤T}|J_t|² ≤ 4 E J_T² ≤ 16 D`, with integrability (start `0`, any `T`). -/
theorem integral_sq_sup_occupationDiffMartingale_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) {D : ℝ}
    (hD : ∀ y : ℝ, |supOccupationResolvent θ 1 ε y - supOccupationResolvent θ 1 η y| ≤ D)
    (T : ℝ≥0) :
    Integrable (fun f => (⨆ t : Set.Iic T, |occupationDiffMartingale θ ε η t f|) ^ 2)
        (stableLocalLaw θ : Measure DLoc) ∧
      ∫ f, (⨆ t : Set.Iic T, |occupationDiffMartingale θ ε η t f|) ^ 2
        ∂(stableLocalLaw θ : Measure DLoc) ≤ 16 * D := sorry

/-- Deterministic integration by parts to remove the discount (almost surely, all `T`):
`sup_{t≤T}|O_ε - O_η| ≤ 2 e^T (sup_{t≤T}|J_t| + D)`. -/
theorem ae_compactError_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η)
    {D : ℝ}
    (hD : ∀ y : ℝ, |supOccupationResolvent θ 1 ε y - supOccupationResolvent θ 1 η y| ≤ D) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ T : ℝ≥0,
      compactError ε η T f ≤
        2 * Real.exp (T : ℝ) * ((⨆ t : Set.Iic T, |occupationDiffMartingale θ ε η t f|) + D) :=
  sorry

/-- **Explicit compact `L²` estimate** (blueprint §1):
`E sup_{t≤T}|O_ε-O_η|² ≤ 128 e^{2T}(D + D²)` whenever `‖u¹_ε-u¹_η‖_∞ ≤ D`,
uniformly in the initial state `0`, with integrability. -/
theorem integral_sq_compactError_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε η : ℝ} (hε : 0 < ε)
    (hη : 0 < η) {D : ℝ}
    (hD : ∀ y : ℝ, |supOccupationResolvent θ 1 ε y - supOccupationResolvent θ 1 η y| ≤ D)
    (T : ℝ≥0) :
    Integrable (fun f => (compactError ε η T f) ^ 2) (stableLocalLaw θ : Measure DLoc) ∧
      ∫ f, (compactError ε η T f) ^ 2 ∂(stableLocalLaw θ : Measure DLoc) ≤
        128 * Real.exp (2 * (T : ℝ)) * (D + D ^ 2) := sorry

/-- **Compact-time Cauchy estimate** (blueprint R05 target shape). -/
theorem supOccupation_compact_L2_cauchy {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) :
    ∀ δ : ℝ, 0 < δ → ∃ a : ℝ, 0 < a ∧
      ∀ ε η : ℝ, 0 < ε → ε < a → 0 < η → η < a →
        Integrable (fun f => (compactError ε η T f) ^ 2) (stableLocalLaw θ : Measure DLoc) ∧
        (∫ f, (compactError ε η T f) ^ 2 ∂(stableLocalLaw θ : Measure DLoc)) ≤ δ := sorry

/-! ### Fast subsequence and the limit process `M^*` -/

theorem exists_isSupAuxEpsSeq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) : ∃ ε : ℕ → ℝ, IsSupAuxEpsSeq θ ε :=
  sorry

open scoped Classical in
/-- The chosen fast sequence (junk `1/(k+1)` for `θ ∉ (1,2]`). -/
noncomputable def supAuxEps (θ : ℝ) : ℕ → ℝ :=
  if h : 1 < θ ∧ θ ≤ 2 then Classical.choose (exists_isSupAuxEpsSeq h)
  else fun k => 1 / ((k : ℝ) + 1)

theorem isSupAuxEpsSeq_supAuxEps {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    IsSupAuxEpsSeq θ (supAuxEps θ) := by
  simp only [supAuxEps, hθ, and_self, dite_true]
  exact Classical.choose_spec (exists_isSupAuxEpsSeq hθ)

/-- The auxiliary limit `M^*_t = limsup_k O_{ε_k}(t)` along `supAuxEps θ` (raw, real-valued,
adapted; the `limsup` is the retained-adaptedness definition of the blueprint). -/
noncomputable def supAuxLimit (θ : ℝ) (f : DLoc) (t : ℝ≥0) : ℝ :=
  limsup (fun k => supOccupation (supAuxEps θ k) f t) atTop

/-- A.s. locally uniform convergence along the fast subsequence, for all `T` simultaneously
(Borel–Cantelli on integer horizons). -/
theorem ae_tendsto_supOccupation_supAuxEps_uniform {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ T : ℝ≥0,
      Tendsto (fun k => ⨆ t : Set.Iic T, |supOccupation (supAuxEps θ k) f t - supAuxLimit θ f t|)
        atTop (𝓝 0) := sorry

theorem measurable_supAuxLimit_uncurry (θ : ℝ) :
    Measurable (fun p : ℝ≥0 × DLoc => supAuxLimit θ p.2 p.1) := sorry

theorem stronglyAdapted_supAuxLimit (θ : ℝ) :
    StronglyAdapted DLoc.filtration (fun t (f : DLoc) => supAuxLimit θ f t) := sorry

/-- `M^*_0 = 0`, nondecreasing and continuous, almost surely (uniform limit of continuous
nondecreasing occupations; recurrence is R06). -/
theorem ae_supAuxLimit_spec {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      supAuxLimit θ f 0 = 0 ∧ Monotone (supAuxLimit θ f) ∧ Continuous (supAuxLimit θ f) := sorry

theorem integrable_sq_supAuxLimit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) :
    Integrable (fun f => (supAuxLimit θ f T) ^ 2) (stableLocalLaw θ : Measure DLoc) := sorry

/-- **Full-filter compact `L²` convergence** `O_ε → M^*` as `ε ↓ 0` (not only along
`supAuxEps`): Cauchy estimate plus Fatou along the fast subsequence. -/
theorem supOccupation_compact_L2_tendsto_supAuxLimit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) :
    (∀ ε : ℝ, 0 < ε →
      Integrable (fun f => (⨆ t : Set.Iic T, |supOccupation ε f t - supAuxLimit θ f t|) ^ 2)
        (stableLocalLaw θ : Measure DLoc)) ∧
    Tendsto (fun ε : ℝ =>
        ∫ f, (⨆ t : Set.Iic T, |supOccupation ε f t - supAuxLimit θ f t|) ^ 2
          ∂(stableLocalLaw θ : Measure DLoc)) (𝓝[>] (0 : ℝ)) (𝓝 0) := sorry

end BGW.StableTrees
