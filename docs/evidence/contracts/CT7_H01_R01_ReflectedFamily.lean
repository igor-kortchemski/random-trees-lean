import BGW.StableTrees.SupremumLocalTime
import BGW.StableTrees.StableStrongMarkov
import BGW.StableTrees.StableLocalLaw

/-! Contract probe for H01 node R01 (reflection at the supremum as a measurable Markov family),
following `r4-h01-blueprint/blueprint.md` R01 and AUDIT item 5 / "Recommended first nodes" 1.
Imports the FINAL (unsealed) `BGW.StableTrees.SupremumLocalTime`; `supRunning`, `supReflected`,
`supOccupation` are NOT redefined.

Conventions.  `R^x_t = max x S_t - X_t` (`supReflectedFrom x f t`), `S = supRunning f`; for
`f 0 = 0` and `x = 0` this is `supReflected f t`.  The deterministic restart is EXACT and holds for
EVERY path: with `y = R^x_s ≥ 0` and `f' = DLoc.shift s f`,
`R^x_{s+u}(f) = max y (S_u f') - f'_u = R^y_u(f')`.  Hence the stochastic Markov statements are
transfers of the sealed independence of `F_s⁺` and the shifted path (sealed
`condExp_shift_stableLocalLaw`-style) and the sealed strong Markov law of `shiftAt`.
Nothing here is almost-sure except what genuinely needs the stable law: spectral positivity
(`ae_leftLim_le_stableLocalLaw`), and the Markov identities themselves.
`R` has NO POSITIVE JUMPS under `NoNegJumps X` (in the sense `R t ≤ leftLim R t`); `X_0` need not
be `0` anywhere except where stated.
Contact set `{t | S_t = X_t}`: closed from the right for every path; CLOSED under `NoNegJumps`;
its complement in `[0,∞)` (when `f 0 = 0`) is a union of maximal open excursion intervals `(g,d)`
with `g` in the set and `d` in the set or infinite.  `d` is an extended time (`ℝ≥0∞`).
RAW PREFIX DEPENDENCE (AUDIT item 5): `supReflectedFrom x f t` and `supOccupation ε f t` depend
only on `f` restricted to `[0,t]`, for EVERY path (no a.s. clause), and are measurable w.r.t. the
RAW (not completed, not right-continuous) filtration.  Downstream raw limsup versions rely on this.
Estimate 450-800 lines. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **Reflected-at-supremum process started from `x ≥ 0`**: `t ↦ max x S_t - X_t`. -/
noncomputable def supReflectedFrom (x : ℝ≥0) (f : DLoc) (t : ℝ≥0) : ℝ :=
  max (x : ℝ) (supRunning f t) - f.1 t

/-- Càdlàg-ness of the reflected path for every càdlàg `f` and every start `x`. -/
theorem isCadlag_supReflectedFrom (x : ℝ≥0) (f : DLoc) :
    IsCadlag (supReflectedFrom x f) := sorry

/-- The reflected path as a total `DLoc`-valued map (no junk case). -/
noncomputable def supReflectedFromLoc (x : ℝ≥0) (f : DLoc) : DLoc :=
  ⟨supReflectedFrom x f, isCadlag_supReflectedFrom x f⟩

/-- The contact set `{t | S_t = X_t}` (equivalently `{R = 0}`, `R ≥ 0`). -/
def supContact (f : DLoc) : Set ℝ≥0 := {t | supReflected f t = 0}

/-- Start from `0` with `f 0 = 0` is the contract's `supReflected`. -/
theorem supReflectedFrom_zero_apply {f : DLoc} (h0 : f.1 0 = 0) (t : ℝ≥0) :
    supReflectedFrom 0 f t = supReflected f t := sorry

/-- The reflection is nonnegative, and `≥ x - X_t`. -/
theorem supReflectedFrom_nonneg (x : ℝ≥0) (f : DLoc) (t : ℝ≥0) : 0 ≤ supReflectedFrom x f t := sorry

/-- **Deterministic restart (everywhere, no hypothesis).** The reflected path at time `s + u` is the
reflected path of the centered shifted path, started from the value `R^x_s`. -/
theorem supReflectedFrom_restart (x : ℝ≥0) (f : DLoc) (s u : ℝ≥0) :
    supReflectedFrom x f (s + u) =
      supReflectedFrom (supReflectedFrom x f s).toNNReal (DLoc.shift s f) u := sorry

/-- **Restart at a random time** (on `{τ f < ⊤}`; junk `shift 0` elsewhere). -/
theorem supReflectedFrom_restart_shiftAt (x : ℝ≥0) (τ : DLoc → ℝ≥0∞) {f : DLoc} (hτ : τ f < ⊤)
    (u : ℝ≥0) :
    supReflectedFrom x f ((τ f).toNNReal + u) =
      supReflectedFrom (supReflectedFrom x f (τ f).toNNReal).toNNReal (DLoc.shiftAt τ f) u := sorry

/-- **Joint measurability** of `(x, f, t) ↦ R^x_t(f)`. -/
theorem measurable_supReflectedFrom_uncurry :
    Measurable (fun p : ℝ≥0 × DLoc × ℝ≥0 => supReflectedFrom p.1 p.2.1 p.2.2) := sorry

/-- Joint measurability of the `DLoc`-valued reflection in `(x, f)`. -/
theorem measurable_supReflectedFromLoc :
    Measurable (fun p : ℝ≥0 × DLoc => supReflectedFromLoc p.1 p.2) := sorry

/-- **No positive jumps** (under spectral positivity of `X`): `R t ≤ leftLim R t`, every `x ≥ 0`. -/
theorem supReflectedFrom_le_leftLim {f : DLoc} (hf : ∀ s, Function.leftLim f.1 s ≤ f.1 s)
    (x : ℝ≥0) (t : ℝ≥0) :
    supReflectedFrom x f t ≤ Function.leftLim (supReflectedFrom x f) t := sorry

/-- Almost-sure form for the stable law, simultaneously in `x` and `t`. -/
theorem ae_supReflectedFrom_le_leftLim {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : DLoc ∂(stableLocalLaw θ : Measure DLoc), ∀ (x t : ℝ≥0),
      supReflectedFrom x f t ≤ Function.leftLim (supReflectedFrom x f) t := sorry

/-- **Markov property (deterministic time).** For bounded Borel `G` on path space, the conditional
expectation given `F_s⁺` of `G` of the post-`s` reflected path (as the reflected path of the shifted
path from the current value) is the kernel `y ↦ ∫ G(R^y) dP` evaluated at `R^x_s`. -/
theorem condExp_supReflectedFromLoc_markov {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x s : ℝ≥0)
    {G : DLoc → ℝ} (hG : Measurable G) (hGb : ∃ C : ℝ, ∀ p, |G p| ≤ C) :
    (stableLocalLaw θ : Measure DLoc)[fun f =>
        G (supReflectedFromLoc (supReflectedFrom x f s).toNNReal (DLoc.shift s f)) |
        DLoc.filtration s] =ᵐ[(stableLocalLaw θ : Measure DLoc)]
      fun f => ∫ g, G (supReflectedFromLoc (supReflectedFrom x f s).toNNReal g)
        ∂(stableLocalLaw θ : Measure DLoc) := sorry

/-- **Strong Markov property at a stopping time** of the right-continuous filtration, in product
form over events `A` of the stopped σ-algebra contained in `{τ < ⊤}`. -/
theorem integral_supReflectedFromLoc_strongMarkov {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0)
    {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ)
    {A : Set DLoc} (hA : MeasurableSet[hτ.measurableSpace] A) (hAτ : A ⊆ {f | τ f < ⊤})
    {G : DLoc → ℝ} (hG : Measurable G) (hGb : ∃ C : ℝ, ∀ p, |G p| ≤ C) :
    ∫ f in A, G (supReflectedFromLoc (supReflectedFrom x f (τ f).toNNReal).toNNReal
        (DLoc.shiftAt τ f)) ∂(stableLocalLaw θ : Measure DLoc) =
      ∫ f in A, (∫ g, G (supReflectedFromLoc (supReflectedFrom x f (τ f).toNNReal).toNNReal g)
        ∂(stableLocalLaw θ : Measure DLoc)) ∂(stableLocalLaw θ : Measure DLoc) := sorry

/-! ### Occupation continuity (every path, every `ε > 0`) -/

/-- Increment bounds: monotone and `ε⁻¹`-Lipschitz increments. -/
theorem supOccupation_sub_mem {ε : ℝ} (hε : 0 < ε) (f : DLoc) {s t : ℝ≥0} (hst : s ≤ t) :
    0 ≤ supOccupation ε f t - supOccupation ε f s ∧
      supOccupation ε f t - supOccupation ε f s ≤ ε⁻¹ * ((t : ℝ) - s) := sorry

/-- `t ↦ supOccupation ε f t` is `ε⁻¹`-Lipschitz. -/
theorem lipschitzWith_supOccupation {ε : ℝ} (hε : 0 < ε) (f : DLoc) :
    LipschitzWith (Real.toNNReal ε⁻¹) (fun t : ℝ≥0 => supOccupation ε f t) := sorry

/-- Continuity (hence continuity and monotonicity together with `monotone_supOccupation`). -/
theorem continuous_supOccupation {ε : ℝ} (hε : 0 < ε) (f : DLoc) :
    Continuous (fun t : ℝ≥0 => supOccupation ε f t) := sorry

/-! ### Contact geometry -/

/-- `supContact` is `{t | f t = S_t}`. -/
theorem mem_supContact_iff {f : DLoc} {t : ℝ≥0} : t ∈ supContact f ↔ f.1 t = supRunning f t := sorry

/-- Closed from the right, for EVERY path: a right accumulation point of the contact set belongs
to it (right-continuity of `R`). -/
theorem supContact_rightClosed (f : DLoc) {t : ℝ≥0}
    (h : ∀ δ : ℝ≥0, 0 < δ → ∃ u ∈ supContact f, t < u ∧ u < t + δ) : t ∈ supContact f := sorry

/-- Closed under spectral positivity of `X` (`R` has no positive jumps). -/
theorem isClosed_supContact {f : DLoc} (hf : ∀ s, Function.leftLim f.1 s ≤ f.1 s) :
    IsClosed (supContact f) := sorry

/-- **Structure of the complement.** If `f 0 = 0` and `X` has no negative jumps, every `t` with
`R_t > 0` lies in a maximal excursion interval `(g, d)`: `g` in the contact set, `R > 0` on `(g,d)`,
and `d` (extended) is infinite or a contact time. -/
theorem exists_excursionInterval_of_supReflected_pos {f : DLoc} (h0 : f.1 0 = 0)
    (hf : ∀ s, Function.leftLim f.1 s ≤ f.1 s) {t : ℝ≥0} (ht : 0 < supReflected f t) :
    ∃ (g : ℝ≥0) (d : ℝ≥0∞), g < t ∧ (t : ℝ≥0∞) < d ∧ supReflected f g = 0 ∧
      (∀ u : ℝ≥0, g < u → (u : ℝ≥0∞) < d → 0 < supReflected f u) ∧
      ∀ d' : ℝ≥0, d = d' → supReflected f d' = 0 := sorry

/-! ### Raw prefix dependence (every path, no almost-sure clause) -/

/-- The running supremum depends only on the path on `[0,t]`. -/
theorem supRunning_congr_prefix {f g : DLoc} {t : ℝ≥0} (h : ∀ u ≤ t, f.1 u = g.1 u) :
    supRunning f t = supRunning g t := sorry

/-- The reflected value at `t` depends only on the prefix up to `t`. -/
theorem supReflectedFrom_congr_prefix (x : ℝ≥0) {f g : DLoc} {t : ℝ≥0}
    (h : ∀ u ≤ t, f.1 u = g.1 u) : supReflectedFrom x f t = supReflectedFrom x g t := sorry

/-- The occupation functional at time `t` depends only on the prefix up to `t`, for every `ε`. -/
theorem supOccupation_congr_prefix (ε : ℝ) {f g : DLoc} {t : ℝ≥0}
    (h : ∀ u ≤ t, f.1 u = g.1 u) : supOccupation ε f t = supOccupation ε g t := sorry

/-- Raw adaptedness: `R^x_t` is measurable for the raw filtration `σ(X_u, u ≤ t)`. -/
theorem measurable_rawFiltration_supReflectedFrom (x t : ℝ≥0) :
    Measurable[DLoc.rawFiltration t] (fun f => supReflectedFrom x f t) := sorry

/-- Raw adaptedness of the occupation functional, every `ε`. -/
theorem measurable_rawFiltration_supOccupation (ε : ℝ) (t : ℝ≥0) :
    Measurable[DLoc.rawFiltration t] (fun f => supOccupation ε f t) := sorry

end BGW.StableTrees
