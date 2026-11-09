import BGW.StableTrees.ForestTripleVector
import BGW.StableTrees.TailPair
import BGW.StableTrees.ExactContourJoint
import BGW.StableTrees.RealAttraction

/-! Contract probe for node W115: C27, C28 and C29 for an arbitrary admissible norming.

SOURCE (`CLASSICAL_THEORY_INPUTS.md` §1.3 and items C27-C29; audit `LEAN_LIBRARY_AUDIT.md` P2-1). The
specification allows any positive norming `B_n` for which `S_n / B_n` converges to the stable law, and says
monotonicity of `B` is never essential. The sealed exports `ForestTriple.tendsto_forestTripleLaw`,
`ForestTriple.tendsto_forestTripleVecLaw` (C27), `TailPair.tendsto_tailPairLaw` (C28),
`ExactContour.tendsto_exactHeightContourLaw` and `ExactContour.tendsto_exactHeightLibContourLaw` (C29) take
`StableDomain μ θ B`, which bundles `Monotone B`. These wrappers take instead the general predicate
`IsRealStableAttracted (realOffspringStepLaw μ) θ B` (eventually positive `B`, scaled sums converging to
`stableLaw θ`), plus criticality and non-degeneracy. The conclusions are the sealed ones, verbatim.

TRUTH CHECK. Let `B'` be a monotone norming with `StableDomain μ θ B'` (it exists, see the plan). Both
`S_n / B_n` and `S_n / B'_n` converge to the same non-degenerate law `stableLaw θ`, so `B_n / B'_n → 1`
(convergence of types). Each law in the conclusions depends on `B n` only through the space scaling of the
walk (`1 / B n`) and of the height and contour (`B n / n`), so it is the image of the law with `B'` under a
scaling map with factors tending to `1`, and the limits agree by continuity of scaling and converging
together. Values of `B n` at finitely many `n` (where `B n ≤ 0` is allowed) do not matter.

PROOF PLAN (revised after the Sonnet audit, 8 Nov 2026). (0) Converse bridge, new, about 60 lines:
`IsRealStableAttracted (realOffspringStepLaw μ) θ B → Attraction.IsStableAttracted (stepLaw μ) θ 0 B` (the
forward direction is `Attraction.IsStableAttracted.isRealStableAttracted`, `RealAttraction.lean:301`; use
`sumLaw_castLaw` (`:283`), the Laplace characterization of `stableLaw`, and criticality for the zero centering).
(1) Canonical monotone norming: `Norming.LocalLimit.locallimit_i` / `locallimit_ii` (`Attraction/Norming.lean`)
give an attracted, monotone `norming`; then `Attraction.IsStableAttracted.exists_stableDomain`
(`Attraction/Defs.lean:271`, needs `hc`, `hne`, `Monotone`, centering 0 from `mean_stepLaw hc`) gives `B'` with
`StableDomain μ θ B'` and `B' = norming` eventually. (2) `B n / B' n → 1`:
`Attraction.TransformConvergence.norming_ratio_tendsto_one` (`TransformConvergence.lean:613`), no monotonicity
needed. (3) Space scaling: the laws with `B` are images of the laws with `B'` under multiplication of the walk
coordinate by `B' n / B n` and of the height/contour coordinates by `B n / B' n` (exact path identities from
`realStepPath` (`ExitPartition.lean:80`) and the `B n / n` amplitudes (`DiscreteForestPaths.lean:88`,
`ForestContour.lean:66`, `ExactContourPaths.lean:51`, `TailPairBasic.lean:114`)). Joint continuity of
`(c, f) ↦ c • f` at `c = 1` on `D T ℝ` (J1 distance scales by `|c|`, and `dist (c • f) f ≤ |c - 1| sup |f|`)
and on `C(Icc 0 T, ℝ)`; reuse `Skorokhod/ScalingMultiplication.lean` or `timeSpaceScale` with time factor 1 if they
already give it. (4) Transfer: continuous mapping on the product with the scalar sequence (`(c_n, X_n) ⇒ (1, X)`)
or an ε-closeness / converging-together lemma from `BGW/Probability` (C10, `WeakPerturbation`). Size 300-500
lines.

ACYCLICITY. Consumes the sealed C27-C29 modules and the attraction development; nothing imports it.

BINDER SCOPE: nothing follows the laws in the conclusions. -/

open MeasureTheory Filter Topology
open scoped NNReal

namespace BGW.StableTrees

/-- **C27 for an arbitrary admissible norming.** -/
theorem ForestTriple.tendsto_forestTripleLaw_of_attracted {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) {T : ℝ≥0} (hT : 0 < T) :
    Tendsto (fun n : ℕ => ForestTriple.forestTripleLaw μ B n T) atTop
      (𝓝 (ForestTriple.forestTripleLimit θ T)) := sorry

/-- **C27, vector-path form, for an arbitrary admissible norming.** -/
theorem ForestTriple.tendsto_forestTripleVecLaw_of_attracted {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) {T : ℝ≥0} (hT : 0 < T) :
    Tendsto (fun n : ℕ => ForestTriple.forestTripleVecLaw μ B n T) atTop
      (𝓝 (ForestTriple.forestTripleVecLimit θ T)) := sorry

/-- **C28 for an arbitrary admissible norming.** -/
theorem TailPair.tendsto_tailPairLaw_of_attracted {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) {T : ℝ≥0} (hT : 0 < T) :
    Tendsto (fun n : ℕ => TailPair.tailPairLaw μ B n T) atTop (𝓝 (tailExcLaw θ T)) := sorry

/-- **C29 for an arbitrary admissible norming.** -/
theorem ExactContour.tendsto_exactHeightContourLaw_of_attracted {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, Admissible μ (q k)) :
    Tendsto (fun k => ExactContour.exactHeightContourLaw μ B (q k) (hq k)) atTop
      (𝓝 ((excLaw θ).map (fun p => (p.2, p.2)))) := sorry

/-- **C29 in the library contour convention, for an arbitrary admissible norming.** -/
theorem ExactContour.tendsto_exactHeightLibContourLaw_of_attracted {μ : PMF ℕ} {θ : ℝ}
    {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, Admissible μ (q k)) :
    Tendsto (fun k => ExactContour.exactHeightLibContourLaw μ B (q k) (hq k)) atTop
      (𝓝 ((excLaw θ).map (fun p => (p.2, p.2)))) := sorry

end BGW.StableTrees
