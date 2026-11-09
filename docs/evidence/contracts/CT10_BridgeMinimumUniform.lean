import BGW.StableTrees.StableBridgeMinimum
import BGW.StableTrees.StableBridgeClosed
import BGW.Skorokhod.VervaatMeasurable

/-! Contract probe for CT.C32, "Moreover `g` is uniform on `(0,1)`" (CT10).

TRUTH. Under the closed stable bridge law, the unique minimum time `g = vervaatTime f`
(`stableBridgeLaw_ae_minimum` gives uniqueness, interiority, continuity) is uniform on `[0,1]`
(Duquesne 2003 §4; Vervaat; Chaumont 1997). Checks: `θ = 2` is Brownian bridge, minimum time
uniform (Vervaat). The bridge has exchangeable increments (for `θ` any stable index), which is the
only input; the law of `g` is then rotation-equivariant: `g(R_u f) = g(f) - u mod 1`.

PROOF PLAN. (1) `bridge_gridIncr_cyclic`: for each `N = M+1` the increment vector at the grid
`i/N` has law invariant under cyclic shift (projective bridge densities `∏ p_{1/N}(Δ_i)/p_1(0)`,
`stableBridgeLaw_unique`-style fdd on the grid, symmetric function of the increments).
(2) Dyadic rotation `R_u f(t) = f(u+t mod 1) - f(u)` (`isCadlag_rotate` in `VervaatRotate` is the
building block; bridges have `f 1 = f 0 = 0`): its law is the bridge law for `u = k/2^n`:
cylinders at dyadic times of order `≥ n` are cyclic grid permutations, and a Borel law on `D` is
determined by dyadic cylinders (needs the `D`-measure uniqueness lemma, available through
`stableBridgeLaw_unique`-type arguments or `MeasurableCylinders`). (3) A.s. unique minimizer
gives `vervaatTime (R_u f) = vervaatTime f - u mod 1`. (4) So `law(g)` is invariant under
dyadic rotations of the circle, hence gives mass `2^{-n}` to every dyadic arc, hence is Lebesgue
(`Measure.ext_of_Ioc`/`Ioc_pi_system`). Size 600-1000 lines; (2) is the heavy part.
Note `P(g ∈ {0,1}) = 0` so `Icc` vs `Ioo` is immaterial; the Lean statement uses `Icc`. -/

open MeasureTheory Set
open scoped ENNReal

namespace BGW.StableTrees

open BGW.Skorokhod

/-- The grid time `i/N` in `[0,1]` (`N = M + 1`, `i ≤ N` as a natural number). -/
noncomputable def gridTime (M i : ℕ) : Set.Icc (0 : ℝ) 1 :=
  Set.projIcc 0 1 zero_le_one ((i : ℝ) / (M + 1))

/-- Grid increments `f((i+1)/N) - f(i/N)`, `i < N`. -/
noncomputable def gridIncr (M : ℕ) (f : D 1 ℝ) (i : Fin (M + 1)) : ℝ :=
  f (gridTime M (i + 1)) - f (gridTime M i)

/-- Exchangeability of the bridge increments under cyclic shifts of the grid. -/
theorem bridge_gridIncr_cyclic {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (M : ℕ) (k : Fin (M + 1)) :
    (stableBridgeLaw θ : Measure (D 1 ℝ)).map (fun f i => gridIncr M f (i + k)) =
      (stableBridgeLaw θ : Measure (D 1 ℝ)).map (fun f i => gridIncr M f i) := sorry

/-- CT.C32, uniformity: the minimum time of the stable bridge is uniform on `[0,1]`. -/
theorem map_vervaatTime_stableBridgeLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (stableBridgeLaw θ : Measure (D 1 ℝ)).map (fun f => (vervaatTime f : ℝ)) =
      volume.restrict (Set.Icc (0 : ℝ) 1) := sorry

/-- Distribution-function form. -/
theorem stableBridgeLaw_vervaatTime_le {θ x : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (stableBridgeLaw θ : Measure (D 1 ℝ)) {f | (vervaatTime f : ℝ) ≤ x} =
      ENNReal.ofReal x := sorry

end BGW.StableTrees
