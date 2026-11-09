import BGW.Skorokhod.DLoc
import BGW.Skorokhod.ReverseIncrements
import BGW.StableTrees.StableLocalLaw
import BGW.StableTrees.StableProcessReversal
import BGW.StableTrees.ExcursionMeasure
import BGW.StableTrees.UnitExcursionLaw
import BGW.StableTrees.ExcursionMarkov
import BGW.ContinuumTrees.ExcursionCarrier
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import BGW.StableTrees.SupremumLocalTimePublic
import BGW.StableTrees.HeightProcess

/-! Contract probe for CT7 bridge node H02b (H02 to H03/H04 bridges), following the Sol audit of
H02 (`sol-audit-h02/AUDIT.md`) items 4 and 5.  H01 and H02 are SEALED and imported
(`SupremumLocalTimePublic`, `HeightProcess`); the exports are the theorems and definitions below.

ITEM 4 (erased-height decomposition and tail).
* `ae_height_erasure_decomposition`: with `m = -inf_{[0,r]} X'` (`X' = shift t f`) and
  `K = top of the support of eraseMass m ρ_t`, a.s. `0 ≤ K ≤ H_t` and `H_{t+r} = K + H'_r`
  (the fresh exploration may vanish: then its top is `0`).  Needs bounded support, the upper
  support bound and the corrected `eraseMass` of H02.
* `erased_height_tail_le`: the tail of `H_t - K`.  PROOF REQUIREMENT: it must use an independent
  fresh depth and a stopped/full ladder bound WITHOUT height continuity.  The reversal at `t`
  is constant after `t`, so its unrestricted ladder height is NOT an independent full stable
  process; use the auxiliary independent continuation or the stopped-ladder bound of the earlier
  audit.

ITEM 5 (`heightApprox_tendstoInMeasure_excursion`): approximation in probability under the
excursion measure `N`, on `{t < lifetime}`.  The following are SUPPLIERS belonging to this
bridge (to be stated, proved and reviewed here), NOT hypotheses of the endpoint:
1. localized Campbell/Cauchy estimates for the approximation family under `N` on
   `{t < lifetime}`, producing some measurable in-measure limit (no identification with H02's
   fixed-sequence height under `N` is required, see REDESIGN);
2. stopped approximation estimate: convergence in probability of the approximation for the
   stable process stopped at a (random) excursion start, from the fixed-time statements of H02;
3. simultaneous marked-excursion locality: for the extracted marks, the excursion height at
   time `t` agrees with the ancestral height of the host path (no deterministic-`t` restart is
   applied at a random start; `g = T(x-)` is not a stopping time);
4. endpoint extension and lifetime-normalization identities needed to transfer the statement
   from `P` to `N` and later to the unit and tail laws (H04; `measurable_height_prefix` is only
   a scalar raw-prefix claim, not the continuous graph).

REDESIGN (7 Nov 2026, after the W84 hand-off).  Item 5 originally asserted convergence in
`N`-measure to the `supEps` version `height θ e.path t`.  Identifying that fixed-sequence
version under `N` needs almost-sure vanishing, along the fixed sequence `supEps θ` (chosen by
`Classical.choose`, with no usable spacing), of the occupation near the excursion start; the
reversed excursion prefix is singular to the stable law near its end.  Standard proofs never
need this.  Item 5 now asserts convergence in measure to SOME measurable limit, under `N` on
`{t < ζ}` and under the unit law at ages `t < 1` (unit prefixes on `[0,a]`, `a < 1`, are
absolutely continuous with respect to tail prefixes, E09, and the tail law is `N` restricted
to `{ζ > 1}` and normalized).  A diagonal extraction then gives ONE sequence `heightEps θ`
along which the approximations converge almost surely at every rational time under the stable
law (to H02's `height`), under `N` and under the unit law; `heightUniv` is the limsup along
it.  H03 reconstructs its continuous height and its prefix map from `heightUniv`, and H04 its
excursion height, so all graph identities hold with one Borel map under every law.  The
absolute continuity of the reversed prefix on `[0, t - δ]` (from the excursion Markov property
at `δ`, `ExcursionMarkov*`, and reversal of the shifted increments) remains a useful supplier.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees


/-! ### Item 4: erasure decomposition and erased-height tail -/

/-- **Erasure decomposition** (fixed `t`, `r`): with `m` the mass erased by the future infimum
and `K` the height of what survives erasure, a.s. `0 ≤ K ≤ H_t` and `H_{t+r} = K + H'_r`. -/
theorem ae_height_erasure_decomposition {θ : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (t r : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      let m := ENNReal.ofReal (-(futureInf (DLoc.shift t f) r 0))
      let K := (topHeight (eraseMass m (exploration θ f t)) : ℝ)
      0 ≤ K ∧ K ≤ height θ f t ∧
        height θ f (t + r) = K + height θ (DLoc.shift t f) r := sorry

/-- **Erased-height tail.**  PROOF REQUIREMENT: use an independent fresh depth and a
stopped/full ladder bound, without height continuity; reversal is constant after `t`, so its
unrestricted ladder height is not an independent full stable process. -/
theorem erased_height_tail_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (t r : ℝ≥0) (hr : 0 < r) (v : ℝ) (hv : 0 ≤ v) :
    (stableLocalLaw θ : Measure DLoc)
      {f | v < height θ f t -
        (topHeight (eraseMass
          (ENNReal.ofReal (-(futureInf (DLoc.shift t f) r 0)))
          (exploration θ f t)) : ℝ)} ≤
    ENNReal.ofReal (Real.exp 1 *
      Real.exp (-(v * (r : ℝ) ^ (-(1 - 1 / θ))))) := sorry

/-! ### Item 5: approximation in probability under the excursion measure -/

/-- **Approximation under `N`** on the survival event `{t < lifetime}`: convergence in `N`-measure
to some measurable limit. -/
theorem exists_heightApprox_tendstoInMeasure_excursion {θ : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) (ht : 0 < t) :
    ∃ L : Excursion → ℝ, Measurable L ∧ TendstoInMeasure
      ((excursionMeasure θ).restrict {e : Excursion | t < e.lifetime})
      (fun (ε : ℝ) (e : Excursion) => heightApprox ε e.path t) (𝓝[>] (0 : ℝ)) L := sorry

/-- **Approximation under the unit law** at ages `t < 1`. -/
theorem exists_heightApprox_tendstoInMeasure_unit {θ : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ L : Excursion → ℝ, Measurable L ∧ TendstoInMeasure
      (unitExcursionLaw θ : Measure Excursion)
      (fun (ε : ℝ) (e : Excursion) => heightApprox ε e.path t) (𝓝[>] (0 : ℝ)) L := sorry

/-! ### One sequence for every law -/

/-- `ε` is positive, strictly decreasing to `0`, and along it the approximations converge almost
surely at every rational time: to H02's height under the stable law, and to some limit under
`N` on `{q < ζ}` and under the unit law at ages `q < 1`; the same holds at Lebesgue-almost every
age (needed by H04's locality at the random ages `q - g`). -/
def IsUniversalHeightSeq (θ : ℝ) (ε : ℕ → ℝ) : Prop :=
  (∀ k, 0 < ε k) ∧ StrictAnti ε ∧ Tendsto ε atTop (𝓝 0) ∧
  (∀ q : ℚ, 0 ≤ q → ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
    Tendsto (fun k => heightApprox (ε k) f (q : ℝ).toNNReal) atTop
      (𝓝 (height θ f (q : ℝ).toNNReal))) ∧
  (∀ q : ℚ, 0 < q →
    ∀ᵐ e ∂((excursionMeasure θ).restrict {e : Excursion | (q : ℝ).toNNReal < e.lifetime}),
      ∃ L : ℝ, Tendsto (fun k => heightApprox (ε k) e.path (q : ℝ).toNNReal) atTop (𝓝 L)) ∧
  (∀ q : ℚ, 0 < q → q < 1 → ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion),
    ∃ L : ℝ, Tendsto (fun k => heightApprox (ε k) e.path (q : ℝ).toNNReal) atTop (𝓝 L)) ∧
  (∀ S : ℝ≥0, ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo 0 (S : ℝ))),
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      Tendsto (fun k => heightApprox (ε k) f s.toNNReal) atTop (𝓝 (height θ f s.toNNReal))) ∧
  (∀ S : ℝ≥0, ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo 0 (S : ℝ))),
    ∀ᵐ e ∂((excursionMeasure θ).restrict {e : Excursion | s.toNNReal < e.lifetime}),
      ∃ L : ℝ, Tendsto (fun k => heightApprox (ε k) e.path s.toNNReal) atTop (𝓝 L)) ∧
  (∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)), ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion),
    ∃ L : ℝ, Tendsto (fun k => heightApprox (ε k) e.path s.toNNReal) atTop (𝓝 L))

/-- A universal sequence exists (diagonal extraction from the in-measure statements).  For the
Lebesgue-a.e. ages use, on each bounded age window, the FINITE measure `volume ⊗ N` restricted to
survival `{(s, e) | s < ζ(e)}` (mass `∫_0^S N(ζ > s) ds < ∞`; the unrestricted product is
infinite), the jointly measurable approximations and their Cauchy-in-measure property there
(dominated by `N(ζ > s)`), so the product limit is jointly measurable without choosing fixed-age
limits by `Classical.choose`; then Borel-Cantelli over countably many windows and laws, and
Fubini.  (Sol audit height-r1, finding 1.) -/
theorem exists_isUniversalHeightSeq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ ε : ℕ → ℝ, IsUniversalHeightSeq θ ε := sorry

open scoped Classical in
/-- The chosen universal sequence (junk `1/(k+1)` only if none exists). -/
noncomputable def heightEps (θ : ℝ) : ℕ → ℝ :=
  if h : ∃ ε : ℕ → ℝ, IsUniversalHeightSeq θ ε then Classical.choose h
  else fun k => 1 / ((k : ℝ) + 1)

theorem isUniversalHeightSeq_heightEps {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    IsUniversalHeightSeq θ (heightEps θ) := sorry

/-- **The height read along the universal sequence** (a real limsup; junk where it diverges). -/
noncomputable def heightUniv (θ : ℝ) (f : DLoc) (t : ℝ≥0) : ℝ :=
  limsup (fun k => heightApprox (heightEps θ k) f t) atTop

theorem measurable_heightUniv_uncurry (θ : ℝ) :
    Measurable (fun p : ℝ≥0 × DLoc => heightUniv θ p.2 p.1) := sorry

/-- `heightUniv θ f 0 = 0` for every path. -/
theorem heightUniv_zero (θ : ℝ) (f : DLoc) : heightUniv θ f 0 = 0 := sorry

/-- `heightUniv` is nonnegative for every path. -/
theorem heightUniv_nonneg (θ : ℝ) (f : DLoc) (t : ℝ≥0) : 0 ≤ heightUniv θ f t := sorry

/-- **Literal prefix locality**: `heightUniv θ f t` reads `f` only on `[0,t]`. -/
theorem heightUniv_eq_of_restrict_eq (θ : ℝ) (T : ℝ≥0) (f g : DLoc)
    (hfg : DLoc.restrict T f = DLoc.restrict T g) (t : ℝ≥0) (ht : t ≤ T) :
    heightUniv θ f t = heightUniv θ g t := sorry

/-- Under the stable law, `heightUniv` is H02's height at every rational time, a.s. -/
theorem ae_heightUniv_eq_height {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ q : ℚ, 0 ≤ q →
      heightUniv θ f (q : ℝ).toNNReal = height θ f (q : ℝ).toNNReal := sorry

/-- Under `N`, the approximations converge along `heightEps θ` to `heightUniv` at every rational
age before the lifetime. -/
theorem ae_tendsto_heightUniv_excursion {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(excursionMeasure θ), ∀ q : ℚ, 0 < q → (q : ℝ).toNNReal < e.lifetime →
      Tendsto (fun k => heightApprox (heightEps θ k) e.path (q : ℝ).toNNReal) atTop
        (𝓝 (heightUniv θ e.path (q : ℝ).toNNReal)) := sorry

/-- Under the unit law, the same at every rational age `q < 1`. -/
theorem ae_tendsto_heightUniv_unit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion), ∀ q : ℚ, 0 < q → q < 1 →
      Tendsto (fun k => heightApprox (heightEps θ k) e.path (q : ℝ).toNNReal) atTop
        (𝓝 (heightUniv θ e.path (q : ℝ).toNNReal)) := sorry

/-- At Lebesgue-a.e. age, `heightUniv` is H02's height under the stable law. -/
theorem ae_age_heightUniv_eq_height {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (S : ℝ≥0) :
    ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo 0 (S : ℝ))), ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      heightUniv θ f s.toNNReal = height θ f s.toNNReal := sorry

/-- At Lebesgue-a.e. age, the approximations converge along `heightEps θ` to `heightUniv` under
`N` on `{s < ζ}`. -/
theorem ae_age_tendsto_heightUniv_excursion {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (S : ℝ≥0) :
    ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo 0 (S : ℝ))),
      ∀ᵐ e ∂((excursionMeasure θ).restrict {e : Excursion | s.toNNReal < e.lifetime}),
        Tendsto (fun k => heightApprox (heightEps θ k) e.path s.toNNReal) atTop
          (𝓝 (heightUniv θ e.path s.toNNReal)) := sorry

/-- At Lebesgue-a.e. age `s < 1`, the same under the unit law. -/
theorem ae_age_tendsto_heightUniv_unit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
      ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion),
        Tendsto (fun k => heightApprox (heightEps θ k) e.path s.toNNReal) atTop
          (𝓝 (heightUniv θ e.path s.toNNReal)) := sorry

end BGW.StableTrees
