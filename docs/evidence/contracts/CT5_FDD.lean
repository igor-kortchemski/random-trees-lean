import BGW.Probability.RealWalk
import BGW.Skorokhod.ExitPartition
import BGW.Skorokhod.Measurable
import BGW.StableTrees.Scalar.DensityLaw
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

/-! Contract probe for CT.C16/C17 route, blueprint Node 10 (audit correction 2): convergence of the
finite-dimensional laws of the step paths `t ↦ S_{⌊n t⌋} / B n` to the product of the stable
increment laws, along any finite strictly increasing family of times in `[0,T]`.

No characteristic functions in `EuclideanSpace` are used: the proof is block independence
(`iIndepFun_blockSum`, disjoint blocks of lengths `⌊n t_{i+1}⌋₊ - ⌊n t_i⌋₊`, which are NOT
`⌊n (t_{i+1} - t_i)⌋₊`), scalar convergence of each block (Node 4: `B (m n) / B n → c^{1/θ}`
and Slutsky), and Mathlib's `ProbabilityMeasure.continuous_pi` (continuity of the finite product
of probability measures). The statement is consistent with `IsStableLevyLaw.increments`.
Maintained file: `BGW/StableTrees/WalkFiniteDimensional.lean`. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

/-! ## Copied declarations (not part of this contract) -/

namespace BGW.Skorokhod

variable {T : ℝ} {E : Type*}

-- copied from contract CT2_PathSpace (not part of this contract)
theorem measurable_eval [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (t : Set.Icc (0 : ℝ) T) : Measurable (fun f : D T E => f t) := sorry

-- copied from contract CT5_WalkTightness (not part of this contract)
theorem measurable_realStepPath (T : ℝ) (n : ℕ) (b : ℝ) :
    Measurable (realStepPath T n b) := sorry

end BGW.Skorokhod

namespace BGW.StableTrees

open BGW.Probability.RealWalk BGW.Skorokhod

-- copied from contract CT4_StableLaw (not part of this contract)
noncomputable def stableLaw (θ : ℝ) : ProbabilityMeasure ℝ :=
  if hθ : 1 < θ ∧ θ ≤ 2 then
    ⟨volume.withDensity (fun x => ENNReal.ofReal (Scalar.stableDensity θ x)), sorry⟩
  else ⟨Measure.dirac 0, inferInstance⟩

-- copied from contract CT4_StableLaw (not part of this contract)
noncomputable def stableLawAt (θ t : ℝ) : ProbabilityMeasure ℝ :=
  (stableLaw θ).map (fun x => t ^ (1 / θ) * x)

-- copied from contract CT5_Normalizer (not part of this contract)
structure IsRealStableAttracted (ν : ProbabilityMeasure ℝ) (θ : ℝ) (B : ℕ → ℝ) : Prop where
  index_mem : 1 < θ ∧ θ ≤ 2
  pos : ∀ᶠ n in atTop, 0 < B n
  converges : Tendsto (fun n => scaledSumLaw ν B n) atTop (𝓝 (stableLaw θ))

-- copied from contract CT5_Normalizer (not part of this contract)
theorem IsRealStableAttracted.tendsto_norming_ratio {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {m q : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hq : Tendsto q atTop atTop)
    (hmq : Tendsto (fun j => (m j : ℝ) / q j) atTop (𝓝 c)) :
    Tendsto (fun j => B (m j) / B (q j)) atTop (𝓝 (c ^ (1 / θ))) := sorry

-- copied from contract CT5_WalkTightness (not part of this contract)
noncomputable def stepPathLaw (ν : ProbabilityMeasure ℝ) (T : ℝ) (B : ℕ → ℝ) (n : ℕ) :
    ProbabilityMeasure (D T ℝ) :=
  (iidLaw ν).map (realStepPath T n (B n))

-- copied from contract CT5_Characterization (not part of this contract)
structure IsStableLevyLaw (θ T : ℝ) (P : ProbabilityMeasure (D T ℝ)) : Prop where
  start : ∀ h : 0 ≤ T, ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)), f ⟨0, le_rfl, h⟩ = 0
  increments : ∀ (k : ℕ) (t : Fin (k + 1) → Set.Icc (0 : ℝ) T),
    StrictMono t → (t 0 : ℝ) = 0 →
    Measure.map (fun f : D T ℝ => fun i : Fin k => f (t i.succ) - f (t i.castSucc))
      (P : Measure (D T ℝ)) =
      Measure.pi (fun i : Fin k =>
        (stableLawAt θ ((t i.succ : ℝ) - t i.castSucc) : Measure ℝ))

/-! ## The contract -/

/-- The increment vector `(f t_1 - f t_0, …, f t_k - f t_{k-1})` of a path at the times `t`. -/
def incrementsMap {T : ℝ} {k : ℕ} (t : Fin (k + 1) → Set.Icc (0 : ℝ) T) :
    D T ℝ → (Fin k → ℝ) := fun f i => f (t i.succ) - f (t i.castSucc)

theorem measurable_incrementsMap {T : ℝ} {k : ℕ} (t : Fin (k + 1) → Set.Icc (0 : ℝ) T) :
    Measurable (incrementsMap t) := sorry

/-- The product of the stable increment laws at a finite family of times
(Node 10; the underlying measure is `Measure.pi (fun i => stableLawAt θ (t (i+1) - t i))`). -/
noncomputable def incrementVectorLaw (θ : ℝ) {k : ℕ} (t : Fin (k + 1) → ℝ) :
    ProbabilityMeasure (Fin k → ℝ) :=
  ProbabilityMeasure.pi (fun i : Fin k => stableLawAt θ (t i.succ - t i.castSucc))

theorem coe_incrementVectorLaw (θ : ℝ) {k : ℕ} (t : Fin (k + 1) → ℝ) :
    (incrementVectorLaw θ t : Measure (Fin k → ℝ)) =
      Measure.pi (fun i : Fin k => (stableLawAt θ (t i.succ - t i.castSucc) : Measure ℝ)) :=
  sorry

/-- Consistency with the characterization: a law with `IsStableLevyLaw.increments` has exactly the
increment law `incrementVectorLaw` along every strictly increasing family starting at `0`. -/
theorem IsStableLevyLaw.map_incrementsMap {θ T : ℝ} {P : ProbabilityMeasure (D T ℝ)}
    (hP : IsStableLevyLaw θ T P) {k : ℕ} (t : Fin (k + 1) → Set.Icc (0 : ℝ) T)
    (ht : StrictMono t) (ht0 : (t 0 : ℝ) = 0) :
    P.map (incrementsMap t) = incrementVectorLaw θ (fun i => (t i : ℝ)) := sorry

/-- The step path starts at `0` with the exact increments being block sums: for `0 ≤ s ≤ u`,
`path u - path s = blockSum ω ⌊n s⌋₊ (⌊n u⌋₊ - ⌊n s⌋₊) / b`. -/
theorem realStepPath_sub {T : ℝ} (n : ℕ) (b : ℝ) (ω : ℕ → ℝ) (s u : Set.Icc (0 : ℝ) T)
    (hsu : s ≤ u) :
    realStepPath T n b ω u - realStepPath T n b ω s =
      blockSum ω ⌊(n : ℝ) * s⌋₊ (⌊(n : ℝ) * u⌋₊ - ⌊(n : ℝ) * s⌋₊) / b := sorry

/-- Exact finite-dimensional structure for every `n` (Node 1 block independence, valid even when
blocks are empty): along a monotone family of times the increments of the step path are
independent, with the laws of the normalized block sums of lengths
`⌊n t_{i+1}⌋₊ - ⌊n t_i⌋₊`. -/
theorem map_stepPathLaw_incrementsMap (ν : ProbabilityMeasure ℝ) (T : ℝ) (B : ℕ → ℝ) (n : ℕ)
    {k : ℕ} (t : Fin (k + 1) → Set.Icc (0 : ℝ) T) (ht : Monotone t) :
    ((stepPathLaw ν T B n).map (incrementsMap t) : Measure (Fin k → ℝ)) =
      Measure.pi (fun i : Fin k =>
        (sumLaw ν (⌊(n : ℝ) * t i.succ⌋₊ - ⌊(n : ℝ) * t i.castSucc⌋₊) : Measure ℝ).map
          (fun x => x / B n)) := sorry

/-- Scalar step (Node 4 + Slutsky): for `0 ≤ a < b` the normalized block sum of length
`⌊n b⌋₊ - ⌊n a⌋₊` (normalized by `B n`, NOT by the block's own normalizer) converges to
`stableLawAt θ (b - a)`. The length is `~ (b - a) n`, so `B (m n) / B n → (b - a)^{1/θ}`. -/
theorem IsRealStableAttracted.tendsto_scaled_block_law {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Tendsto (fun n : ℕ => (sumLaw ν (⌊(n : ℝ) * b⌋₊ - ⌊(n : ℝ) * a⌋₊)).map (fun x => x / B n))
      atTop (𝓝 (stableLawAt θ (b - a))) := sorry

/-- Node 10: the finite-dimensional increments of the step paths converge to the product of the
stable increments at any finite strictly increasing family of times in `[0,T]` (not necessarily
starting at `0`; the terminal time `T` is allowed). -/
theorem IsRealStableAttracted.tendsto_stepPathLaw_increments {ν : ProbabilityMeasure ℝ}
    {θ : ℝ} {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {T : ℝ} {k : ℕ}
    (t : Fin (k + 1) → Set.Icc (0 : ℝ) T) (ht : StrictMono t) :
    Tendsto (fun n => (stepPathLaw ν T B n).map (incrementsMap t)) atTop
      (𝓝 (incrementVectorLaw θ (fun i => (t i : ℝ)))) := sorry

/-- Partial sums of an increment vector (positions from increments, starting value `0`). -/
def cumulativeSum {k : ℕ} (x : Fin k → ℝ) : Fin k → ℝ :=
  fun j => ∑ i ∈ Finset.univ.filter (fun i : Fin k => i ≤ j), x i

/-- Position form, starting at `0` (the family `t` has `t 0 = 0`): the vector
`(f t_1, …, f t_k)` converges to the cumulative sum of the independent stable increments
(`f t_0 = f 0 = 0` for every step path). -/
theorem IsRealStableAttracted.tendsto_stepPathLaw_positions {ν : ProbabilityMeasure ℝ}
    {θ : ℝ} {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {T : ℝ} {k : ℕ}
    (t : Fin (k + 1) → Set.Icc (0 : ℝ) T) (ht : StrictMono t) (ht0 : (t 0 : ℝ) = 0) :
    Tendsto (fun n => (stepPathLaw ν T B n).map (fun f : D T ℝ => fun i : Fin k => f (t i.succ)))
      atTop
      (𝓝 ((incrementVectorLaw θ (fun i => (t i : ℝ))).map cumulativeSum)) := sorry

end BGW.StableTrees
