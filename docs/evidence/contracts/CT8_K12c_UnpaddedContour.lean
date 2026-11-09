import BGW.StableTrees.DiscreteForest
import BGW.Tree.ContourBracket
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import BGW.StableTrees.HeightContinuity
import BGW.StableTrees.ForestContour

/-! Contract probe for CT8 node K12c (split from K12b after the K12b/K13 audit, finding 3): the
UNPADDED forest contour clock.  Blueprint §1 concatenates tree contours padded by two zero units
per tree (duration `2z`); the classical (Duquesne-Le Gall) forest contour is unpadded (duration
`2(z-1)` per tree, singletons last zero time).  This node proves that the unpadded clock diverges
almost surely, identifies the unpadded contour with the padded one along the shifted clock, and
shows the normalized difference vanishes in probability.  Nothing in K13-K16 consumes it; it is
needed only if a public C27 statement must use the unpadded contour.

TRUTH CHECK (audit k12b13, findings 2-3).  `ae_tendsto_unpaddedStart` needs criticality and
nondegeneracy (`μ = δ_1` gives `unpaddedStart ≡ 0`) and infinitely many blocks of size `≥ 2`
(iid block law, K02 `blockTrees_law`, Borel-Cantelli), not just one long block.  The identity
`forestContourUnpaddedLin_eq` holds under divergence, including across block boundaries where
both sides vanish.  The comparison holds since the number of completed trees by time `n T` is
`O_P(B_n)` (walk running infimum).  Definitions of K12b used here are copied (marked).

BINDER SCOPE (AUDITOR_RULES): suprema have the absolute value as body; nothing follows them. -/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.StableTrees

namespace BGW.StableTrees.ForestContour

open BGW.StableTrees.DiscreteForest BGW.PlaneTree

/-! ### The unpadded clock (AUDIT finding 7) -/

/-- Start of tree `r` on the unpadded clock: `2 (L r - r)`, each earlier tree of size `z`
contributing `2 (z - 1)` (zero for a singleton). -/
noncomputable def unpaddedStart (ω : ℕ → ℕ) (r : ℕ) : ℕ := 2 * (ladderTime ω r - r)

/-- The block whose unpadded interval `[2 (L r - r), 2 (L (r+1) - r - 1))` contains `m`
(singletons have empty intervals and are skipped; junk `0` when no block does). -/
noncomputable def unpaddedBlock (ω : ℕ → ℕ) (m : ℕ) : ℕ :=
  sInf {r | m < unpaddedStart ω (r + 1)}

/-- **Unpadded forest contour** at integer time `m`: the plain concatenation of the tree
contours (junk `0` off `LadderFinite`). -/
noncomputable def forestContourUnpadded (ω : ℕ → ℕ) (m : ℕ) : ℕ :=
  if LadderFinite ω then
    (blockTree ω (unpaddedBlock ω m)).contourAt (m - unpaddedStart ω (unpaddedBlock ω m))
  else 0

/-- Linear interpolation of the unpadded forest contour at integer times. -/
noncomputable def forestContourUnpaddedLin (ω : ℕ → ℕ) (s : ℝ) : ℝ :=
  (1 - (s - ⌊s⌋₊)) * (forestContourUnpadded ω ⌊s⌋₊ : ℝ) +
    (s - ⌊s⌋₊) * (forestContourUnpadded ω (⌊s⌋₊ + 1) : ℝ)

/-- The uniform distance on `[0,T]` between the normalized unpadded and padded contours, both
at time `2nt`. -/
noncomputable def forestContourUnpaddedError (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (ω : ℕ → ℕ) : ℝ :=
  ⨆ t : Set.Icc (0 : ℝ) (T : ℝ),
    |B n / n * forestContourUnpaddedLin ω (2 * (n : ℝ) * (t : ℝ)) -
      B n / n * forestContourLin ω (2 * (n : ℝ) * (t : ℝ))|

/-- The unpadded clock: tree `r` lasts `2 (z_r - 1)`, zero for a singleton. -/
theorem unpaddedStart_succ {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ) :
    unpaddedStart ω (r + 1) = unpaddedStart ω r + 2 * ((blockTree ω r).size - 1) := sorry

/-- The total unpadded contour duration is infinite almost surely. -/
theorem ae_tendsto_unpaddedStart (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∀ᵐ ω ∂(offspringSeqLaw μ : Measure (ℕ → ℕ)), Tendsto (unpaddedStart ω) atTop atTop :=
  sorry

/-- **Padded/unpadded identity**: when the unpadded clock diverges, the unpadded contour at time
`s` is the padded contour at time `s + 2r`, `r = unpaddedBlock ω ⌊s⌋` the number of earlier
trees. -/
theorem forestContourUnpaddedLin_eq {ω : ℕ → ℕ} (hω : LadderFinite ω)
    (hdiv : Tendsto (unpaddedStart ω) atTop atTop) {s : ℝ} (hs : 0 ≤ s) :
    forestContourUnpaddedLin ω s =
      forestContourLin ω (s + 2 * (unpaddedBlock ω ⌊s⌋₊ : ℝ)) := sorry

/-- **Padded/unpadded comparison** on every positive horizon: the two normalized contours are
uniformly close in probability. -/
theorem unpadded_contour_error_tendstoInMeasure {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure (offspringSeqLaw μ : Measure (ℕ → ℕ))
      (fun n ω => forestContourUnpaddedError B n T ω) atTop (fun _ => (0 : ℝ)) := sorry

end BGW.StableTrees.ForestContour
