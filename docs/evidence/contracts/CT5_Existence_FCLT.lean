import BGW.StableTrees.StableLaw
import BGW.StableTrees.StableLevyLaw
import BGW.StableTrees.RealAttraction
import BGW.StableTrees.RealAttractionBounds
import BGW.StableTrees.WalkPathTightness
import BGW.StableTrees.WalkPathFDD
import BGW.Skorokhod.Measurable
import BGW.Skorokhod.CompleteMetricCompleteness
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-! Contract probe for CT.C16/C17, blueprint Nodes 11-15 and 18, plus the offspring/integer
corollaries (Node 21) and the normalizer floor ratio.

Everything imported is sealed (`WalkPathFDD` included). Maintained files (proposed):
`BGW/StableTrees/WalkPathLimit.lean` (Nodes 11-12), `BGW/StableTrees/StableProcess.lean`
(Node 14 existence and `stableProcessLaw`), `BGW/StableTrees/FCLT.lean` (Node 15, corollaries),
`BGW/StableTrees/NoNegativeJumps.lean` (Node 18).

Proof route: Node 11 = `isTightMeasureSet_stepPathLaw` + `isCompact_closure_of_isTightMeasureSet`
+ `IsCompact.tendsto_subseq` (metrizable `ProbabilityMeasure (D T ℝ)`). Node 12 = f.d.d. limits
at times outside the countable fixed-jump set, extension to all times by right continuity,
`0` and `T` handled by global continuity of evaluation there. Node 14 = existence from the
`exists_stableDomain` witness + `StableDomain.isRealStableAttracted` + Nodes 11-12, `unique` is
sealed. Node 15 = subsequence criterion. Node 18 = witness steps `≥ -1`, continuous mapping
of the maximal negative jump. -/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace BGW.StableTrees

open BGW.Skorokhod BGW.Probability.RealWalk

/-! ## Node 11: subsequential extraction (no Polishness needed) -/

/-- Every sequence of indices has a subsequence along which the step-path laws converge weakly
in `ProbabilityMeasure (D T ℝ)`. -/
theorem IsRealStableAttracted.exists_subseq_stepPathLaw {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {T : ℝ} (hT : 0 < T) (q : ℕ → ℕ) :
    ∃ (P : ProbabilityMeasure (D T ℝ)) (r : ℕ → ℕ), StrictMono r ∧
      Tendsto (fun j => stepPathLaw ν T B (q (r j))) atTop (𝓝 P) := sorry

/-! ## Node 12: every cluster law is a stable Lévy law -/

/-- Any weak limit of step-path laws along indices tending to infinity satisfies
`IsStableLevyLaw`, including the terminal time `T` and all deterministic times. -/
theorem IsRealStableAttracted.isStableLevyLaw_of_tendsto {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {T : ℝ} (hT : 0 < T)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) {P : ProbabilityMeasure (D T ℝ)}
    (hP : Tendsto (fun j => stepPathLaw ν T B (q j)) atTop (𝓝 P)) :
    IsStableLevyLaw θ T P := sorry

/-! ## Node 14: existence, uniqueness and the chosen law -/

/-- Existence of a stable Lévy law, from the genuine `exists_stableDomain` witness. -/
theorem exists_isStableLevyLaw {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) :
    ∃ P : ProbabilityMeasure (D T ℝ), IsStableLevyLaw θ T P := sorry

/-- Existence and uniqueness (uniqueness is the sealed `IsStableLevyLaw.unique`). -/
theorem existsUnique_isStableLevyLaw {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) :
    ∃! P : ProbabilityMeasure (D T ℝ), IsStableLevyLaw θ T P := sorry

/-- The law of the spectrally positive `θ`-stable Lévy process on `[0,T]`; chosen after
existence is proved. Junk value (Dirac at the zero path) unless `1 < θ ≤ 2` and `0 < T`. -/
noncomputable def stableProcessLaw (θ T : ℝ) : ProbabilityMeasure (D T ℝ) :=
  if h : (1 < θ ∧ θ ≤ 2) ∧ 0 < T then Classical.choose (exists_isStableLevyLaw h.1 h.2)
  else ⟨Measure.dirac (Skorokhod.ofContinuous (ContinuousMap.const _ 0)), inferInstance⟩

theorem isStableLevyLaw_stableProcessLaw {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) :
    IsStableLevyLaw θ T (stableProcessLaw θ T) := sorry

/-- Characterization: the stable process law is the unique stable Lévy law. -/
theorem eq_stableProcessLaw_iff {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    {P : ProbabilityMeasure (D T ℝ)} :
    P = stableProcessLaw θ T ↔ IsStableLevyLaw θ T P := sorry

/-- Fixed-time marginals of the stable process law: `X_t` has law `stableLawAt θ t` for `0 < t ≤ T`
(Sol audit coverage addition). -/
theorem map_eval_stableProcessLaw {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    (t : Set.Icc (0 : ℝ) T) (ht : 0 < (t : ℝ)) :
    (stableProcessLaw θ T : Measure (D T ℝ)).map (fun f : D T ℝ => f t) =
      (stableLawAt θ t : Measure ℝ) := sorry

/-- The stable process law starts at `0` almost surely. -/
theorem ae_eval_zero_stableProcessLaw {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) :
    ∀ᵐ f : D T ℝ ∂(stableProcessLaw θ T : Measure (D T ℝ)), f ⟨0, le_rfl, hT.le⟩ = 0 := sorry

/-- No fixed discontinuities for the stable process law (P3, specialization). -/
theorem ae_continuousAt_stableProcessLaw {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    (t : Set.Icc (0 : ℝ) T) :
    ∀ᵐ f : D T ℝ ∂(stableProcessLaw θ T : Measure (D T ℝ)), ContinuousAt f t := sorry

/-- Consistency of the stable process laws under restriction (P1, specialization). -/
theorem map_restrict_stableProcessLaw {θ T a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 < a)
    (haT : a ≤ T) :
    (stableProcessLaw θ T).map (Skorokhod.restrict haT) = stableProcessLaw θ a := sorry


/-! ## Node 15: the general FCLT -/

/-- C17: for every real iid walk in the domain of attraction (arbitrary positive-eventually
normalizers, no centering, no monotonicity, no moments), every horizon `T > 0`, the laws of the
step paths `t ↦ S_{⌊nt⌋} / B n`, terminal value at `T` included, converge weakly in `D T ℝ`
to the stable process law. -/
theorem IsRealStableAttracted.tendsto_stepPathLaw {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n => stepPathLaw ν T B n) atTop (𝓝 (stableProcessLaw θ T)) := sorry

/-- Subsequence form. -/
theorem IsRealStableAttracted.tendsto_stepPathLaw_subseq {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {T : ℝ} (hT : 0 < T)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    Tendsto (fun j => stepPathLaw ν T B (q j)) atTop (𝓝 (stableProcessLaw θ T)) := sorry

/-- Any measurable iid realization of the steps has the same step-path laws. -/
theorem IsRealStableAttracted.tendsto_map_realStepPath_iid {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {T : ℝ} (hT : 0 < T)
    {Ω : Type*} [MeasurableSpace Ω] (μ : ProbabilityMeasure Ω) (ξ : ℕ → Ω → ℝ)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ (μ : Measure Ω))
    (hlaw : ∀ i, Measure.map (ξ i) (μ : Measure Ω) = (ν : Measure ℝ)) :
    Tendsto (fun n => μ.map (fun ω => realStepPath T n (B n) (fun i => ξ i ω))) atTop (𝓝 (stableProcessLaw θ T)) := sorry

/-- Normalizer floor ratio for every `t > 0`. -/
theorem IsRealStableAttracted.tendsto_norming_floor_ratio {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ => B ⌊(n : ℝ) * t⌋₊ / B n) atTop (𝓝 (t ^ (1 / θ))) := sorry

/-! ## Corollaries through the sealed bridges -/

/-- Integer-step corollary through `Attraction.IsStableAttracted.isRealStableAttracted`
(centering `0`, eventual positivity of `B`). -/
theorem Attraction.IsStableAttracted.tendsto_stepPathLaw {ν : Measure ℤ}
    [IsProbabilityMeasure ν] {θ : ℝ} {B : ℕ → ℝ}
    (h : Attraction.IsStableAttracted ν θ 0 B) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n => stepPathLaw (castLaw ν) T B n) atTop (𝓝 (stableProcessLaw θ T)) := sorry

/-- Offspring corollary: the step `K - 1` as a real law, normalizer `a` of `StableDomain`. -/
theorem StableDomain.tendsto_stepPathLaw {μ : PMF ℕ} {θ : ℝ} {a : ℕ → ℝ}
    (h : StableDomain μ θ a) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n => stepPathLaw (realOffspringStepLaw μ) T a n) atTop
      (𝓝 (stableProcessLaw θ T)) := sorry

/-! ## Node 18: P4, no negative jumps (spectral positivity) -/

/-- Almost surely, simultaneously at all times `t ∈ [0,T]`, the path has no negative jump:
`f (t-) ≤ f t`. Proved through the offspring witness (steps `≥ -1`) and uniqueness, not through
P3. -/
theorem ae_leftLim_le_stableProcessLaw {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) :
    ∀ᵐ f : D T ℝ ∂(stableProcessLaw θ T : Measure (D T ℝ)),
      ∀ t : Set.Icc (0 : ℝ) T, Function.leftLim f t ≤ f t := sorry

end BGW.StableTrees
