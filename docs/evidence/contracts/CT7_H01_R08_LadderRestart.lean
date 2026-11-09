import BGW.StableTrees.SupremumDrawdown
import BGW.StableTrees.SupremumReflectedFamily
import BGW.StableTrees.SupremumLocalTime
import BGW.Skorokhod.DLocShiftAt
import BGW.StableTrees.StableStrongMarkov
import BGW.StableTrees.StableLocalLaw
import BGW.StableTrees.SupremumLocalTimeIdent

/-! Contract probe for H01 node R08 (blueprint R08 "Restart and ladder independent increments";
Sol-audit-r05r06 item 8): restart of the stable process at the inverse local time `A_z`, and the
ladder process `z ↦ (A_z, B_z)` as a subordinator (independent stationary increments).
Depends on R07 (identification, stopping representative `supHitting`, ladder geometry) and, through
it, R06.  NOT redefined: `supRunning`, `supReflected`, `supOccupation` (sealed), `DLoc.shiftAt`
(sealed).  Suppliers consumed by the PROOFS: R07 (`isStoppingTime_supHitting`,
`ae_supHitting_eq_inverse`, `ae_supLadder_spec`, `ae_supLadder_geometry`,
`ae_tendsto_supOccupation`, `ae_tendsto_supOccupation_uniform`, `ae_supLocalTime_spec`),
sealed `ST.measure_inter_preimage_shiftAt`, `ST.map_shiftAt_restrict_stableLocalLaw`,
`ST.integral_shiftAt_mul_past_of_ae_lt_top`, `DLoc.measurable_shiftAt`,
`DLoc.measurableSet_lt_top_stopped`, `DLoc.eval_shiftAt`.

Proof plan reminders (not statements).  At `A_z`, `X = S` (zero drawdown, R07 geometry), so
`S_{A_z+t} = B_z + S'_t` and `R_{A_z+t} = R'_t`; the shifted path lies on the a.s. event of
simultaneous occupation convergence (strong Markov law of `f'` is `P`, null sets transported by
`map_shiftAt_restrict_stableLocalLaw`), hence the occupation integrals split at `A_z` and
`M(A_z+t) = z + M'(t)`.  The inverse then satisfies `A_{z+u} = A_z + A'_u` by strict
generalized inversion.  Independence/stationarity: apply the sealed independence form with the
stopping time `supHitting θ z` and A in its stopped σ-algebra; increments over disjoint level
intervals are functions of the successive restarts (induction on the chain).

FLAGS.
(1) The restart and its independence are for the stopping representative `τ_z = supHitting θ z`
(an everywhere stopping time, R07), because `shiftAt` is only measurable for stopping times and the
raw `supLadderTime` is a stopping time only up to a null set.  The final contract's
`ae_supRestart_at_ladderTime` (shift by the raw `supLadderTime`) is restated verbatim; the two
shifts agree a.s., so both are stated.
(2) Independence is stated against the stopped σ-algebra of `τ_z` (so against `F_{A_z}`), and as
a statement about the whole post-`A_z` path `shiftAt τ_z`, not only its ladder functionals.
(3) The ladder-process increments are independent only as random variables on the canonical
space (via `iIndepFun` along any finite monotone chain of levels); no completion of the filtration
is claimed for `A_u`, `u ≤ z`, to be `F_{A_z}`-measurable pointwise.
(4) No claim that `B` is continuous or that `ΔB_z = 0`: ladder heights jump (overshoots).
(5) Estimate 500-900 lines. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

open scoped Classical in
/-! ### Restart at `A_z` -/

/-- **Restart identity at `A_z`** (final-contract statement, verbatim).  Let `f' = shiftAt A_z f`
be the post-`A_z` centered path.  Almost surely `X_{A_z} = S_{A_z} = B_z` (zero drawdown at `A_z`,
not zero overshoot), the reflected process restarts, `S_{A_z+t} = B_z + S'_t`, and
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

/-- The same restart with the stopping representative `supHitting θ z` (everywhere a stopping
time): the two shifts coincide almost surely. -/
theorem ae_shiftAt_supHitting_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      DLoc.shiftAt (supHitting θ z) f =
        DLoc.shiftAt (fun g => (supLadderTime θ z g : ℝ≥0∞)) f := sorry

/-- **Ladder process restarts**: with `f' = shiftAt A_z f`, for all `u ≥ 0` simultaneously,
`A_{z+u}(f) = A_z(f) + A_u(f')` and `B_{z+u}(f) = B_z(f) + B_u(f')`. -/
theorem ae_supLadder_restart {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ u : ℝ≥0,
      supLadderTime θ (z + u) f =
          supLadderTime θ z f +
            supLadderTime θ u (DLoc.shiftAt (fun g => (supLadderTime θ z g : ℝ≥0∞)) f) ∧
      supLadderHeight θ (z + u) f =
          supLadderHeight θ z f +
            supLadderHeight θ u (DLoc.shiftAt (fun g => (supLadderTime θ z g : ℝ≥0∞)) f) :=
  sorry

/-- `A_z < ⊤` almost surely (for the stopping representative), so restart is a.s. defined. -/
theorem ae_supHitting_lt_top {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), supHitting θ z f < ⊤ := sorry

/-- **Independence of the post-`A_z` path from `F_{A_z}`** (stopped σ-algebra of the stopping
representative, event inside `{A_z < ⊤}`, as in the sealed strong Markov form). -/
theorem measure_inter_preimage_shiftAt_supHitting {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0)
    {A : Set DLoc} (hA : MeasurableSet[(isStoppingTime_supHitting θ z).measurableSpace] A)
    (hAτ : A ⊆ {f | supHitting θ z f < ⊤}) {B : Set DLoc} (hB : MeasurableSet B) :
    (stableLocalLaw θ : Measure DLoc) (A ∩ DLoc.shiftAt (supHitting θ z) ⁻¹' B) =
      (stableLocalLaw θ : Measure DLoc) A * (stableLocalLaw θ : Measure DLoc) B := sorry

/-- **Restart theorem**: the post-`A_z` path has the original law `stableLocalLaw θ` and is
independent of `F_{A_z}`. -/
theorem indep_shiftAt_supHitting {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    Indep (isStoppingTime_supHitting θ z).measurableSpace
      (MeasurableSpace.comap (DLoc.shiftAt (supHitting θ z)) (inferInstance : MeasurableSpace DLoc))
      (stableLocalLaw θ : Measure DLoc) := sorry

theorem map_shiftAt_supHitting {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    (stableLocalLaw θ : Measure DLoc).map (DLoc.shiftAt (supHitting θ z)) =
      (stableLocalLaw θ : Measure DLoc) := sorry

/-! ### The ladder process is a subordinator -/

/-- The ladder pair `(A_z, B_z)` as a real vector. -/
noncomputable def supLadderPair (θ : ℝ) (z : ℝ≥0) (f : DLoc) : ℝ × ℝ :=
  ((supLadderTime θ z f : ℝ), supLadderHeight θ z f)

/-- The ladder increment `(A_z - A_y, B_z - B_y)` over levels `y ≤ z`. -/
noncomputable def supLadderIncrement (θ : ℝ) (y z : ℝ≥0) (f : DLoc) : ℝ × ℝ :=
  ((supLadderTime θ z f : ℝ) - supLadderTime θ y f, supLadderHeight θ z f - supLadderHeight θ y f)

theorem measurable_supLadderPair (θ : ℝ) (z : ℝ≥0) : Measurable (supLadderPair θ z) := sorry

theorem measurable_supLadderIncrement (θ : ℝ) (y z : ℝ≥0) :
    Measurable (supLadderIncrement θ y z) := sorry

/-- Start at the origin: `(A_0, B_0) = (0, 0)` almost surely. -/
theorem ae_supLadderPair_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), supLadderPair θ 0 f = (0, 0) := sorry

/-- Almost surely the ladder pair is nonnegative, nondecreasing in both coordinates, and
right-continuous in the level, for all levels simultaneously. -/
theorem ae_supLadderPair_path {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (∀ z, 0 ≤ (supLadderPair θ z f).1 ∧ 0 ≤ (supLadderPair θ z f).2) ∧
      Monotone (fun z => (supLadderPair θ z f).1) ∧
      Monotone (fun z => (supLadderPair θ z f).2) ∧
      ∀ z, ContinuousWithinAt (fun z => supLadderPair θ z f) (Ici z) z := sorry

/-- **Stationary increments**: the increment over `[y, z]` has the law of the pair at level
`z - y`. -/
theorem map_supLadderIncrement {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {y z : ℝ≥0} (hyz : y ≤ z) :
    (stableLocalLaw θ : Measure DLoc).map (supLadderIncrement θ y z) =
      (stableLocalLaw θ : Measure DLoc).map (supLadderPair θ (z - y)) := sorry

/-- **Independence of the future increment from `F_{A_y}`**: the increment over `[y, z]` is
independent of the stopped σ-algebra of `supHitting θ y`. -/
theorem indep_supLadderIncrement_stopped {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {y z : ℝ≥0}
    (hyz : y ≤ z) :
    Indep (isStoppingTime_supHitting θ y).measurableSpace
      (MeasurableSpace.comap (supLadderIncrement θ y z) (inferInstance : MeasurableSpace (ℝ × ℝ)))
      (stableLocalLaw θ : Measure DLoc) := sorry

/-- **Independent increments**: along every finite monotone chain of levels
`z 0 ≤ z 1 ≤ ... ≤ z n`, the `n` successive increments are mutually independent. -/
theorem iIndepFun_supLadderIncrement {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (n : ℕ)
    (z : Fin (n + 1) → ℝ≥0) (hz : Monotone z) :
    iIndepFun (fun k : Fin n => supLadderIncrement θ (z k.castSucc) (z k.succ))
      (stableLocalLaw θ : Measure DLoc) := sorry

end BGW.StableTrees
