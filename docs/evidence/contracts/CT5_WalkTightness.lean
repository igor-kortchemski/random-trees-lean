import BGW.Probability.RealWalk
import BGW.Skorokhod.ExitPartition
import BGW.Skorokhod.Tightness
import BGW.Skorokhod.Measurable
import BGW.StableTrees.Attraction.Defs
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Contract probe for CT.C16/C17 route, blueprint Node 9 (with the Node 2 declarations it
needs, audit correction 4): the step-path laws `stepPathLaw ν T B n` of the real iid walk, the
single-law tightness of each of them, the three probabilistic reductions (compact containment,
initial window, terminal window), the outer-measure bridge from the exit-partition event to the
modulus event, the eventual modulus estimate and the tightness of the whole sequence for every
`IsRealStableAttracted` walk. Its hypotheses are exactly those of
`BGW.Skorokhod.isTightMeasureSet_of_cadlagModulus_eventually` (`htight`, `hbdd`, `hmod`).
Maintained files: `BGW/Skorokhod/RealStepPath.lean` (Node 2, already hosts `realStepPath` in
`ExitPartition.lean`) and `BGW/StableTrees/WalkTightness.lean`. -/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-! ## Copied declarations (not part of this contract) -/

namespace BGW.Probability.RealWalk

-- copied from contract CT5_Ottaviani (not part of this contract)
def maxExceed (m : ℕ) (r : ℝ) : Set (ℕ → ℝ) := {ω | ∃ k ≤ m, r < |partialSum ω k|}

-- copied from contract CT5_Ottaviani (not part of this contract)
noncomputable def maxTail (ν : ProbabilityMeasure ℝ) (m : ℕ) (r : ℝ) : ℝ :=
  (iidLaw ν : Measure (ℕ → ℝ)).real (maxExceed m r)

-- copied from contract CT5_Ottaviani (not part of this contract)
theorem measureReal_exceed_block (ν : ProbabilityMeasure ℝ) (a m : ℕ) (r : ℝ) :
    (iidLaw ν : Measure (ℕ → ℝ)).real {ω | ∃ k ≤ m, r < |blockSum ω a k|} = maxTail ν m r :=
  sorry

end BGW.Probability.RealWalk

namespace BGW.StableTrees

open BGW.Probability.RealWalk

-- copied from contract CT4_StableLaw (not part of this contract)
noncomputable def stableLaw (θ : ℝ) : ProbabilityMeasure ℝ :=
  if hθ : 1 < θ ∧ θ ≤ 2 then
    ⟨volume.withDensity (fun x => ENNReal.ofReal (Scalar.stableDensity θ x)), sorry⟩
  else ⟨Measure.dirac 0, inferInstance⟩

-- copied from contract CT5_Normalizer (not part of this contract)
structure IsRealStableAttracted (ν : ProbabilityMeasure ℝ) (θ : ℝ) (B : ℕ → ℝ) : Prop where
  index_mem : 1 < θ ∧ θ ≤ 2
  pos : ∀ᶠ n in atTop, 0 < B n
  converges : Tendsto (fun n => scaledSumLaw ν B n) atTop (𝓝 (stableLaw θ))

-- copied from contract CT5_Ottaviani (not part of this contract)
theorem IsRealStableAttracted.small_block_max {ν : ProbabilityMeasure ℝ} {θ : ℝ} {B : ℕ → ℝ}
    (h : IsRealStableAttracted ν θ B) :
    ∀ ε > 0, ∀ η > 0, ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ m : ℕ,
      (m : ℝ) ≤ δ * n + 2 → maxTail ν m (ε * B n) ≤ η := sorry

-- copied from contract CT5_Ottaviani (not part of this contract)
theorem IsRealStableAttracted.horizon_max_tight {ν : ProbabilityMeasure ℝ} {θ : ℝ} {B : ℕ → ℝ}
    (h : IsRealStableAttracted ν θ B) {T : ℝ} (hT : 0 < T) :
    ∀ η > 0, ∃ K > 0, ∃ N : ℕ, ∀ n ≥ N, maxTail ν ⌊(n : ℝ) * T⌋₊ (K * B n) ≤ η := sorry

end BGW.StableTrees

/-! ## Node 2: measurability and continuity of the step path (new declarations) -/

namespace BGW.Skorokhod

open BGW.Probability.RealWalk

/-- The step path depends continuously on the walk, for the product topology on `ℕ → ℝ`
(it only uses the first `⌊n T⌋₊` coordinates, continuously, into J1 via `dist_le_iSup_dist`). -/
theorem continuous_realStepPath (T : ℝ) (n : ℕ) (b : ℝ) :
    Continuous (realStepPath T n b) := sorry

/-- Hence it is Borel measurable for the Borel structure on `D T ℝ`. -/
theorem measurable_realStepPath (T : ℝ) (n : ℕ) (b : ℝ) :
    Measurable (realStepPath T n b) := sorry

/-- The step path starts at `0` (also for `T < 0` vacuously). -/
theorem realStepPath_apply_zero {T : ℝ} (hT : 0 ≤ T) (n : ℕ) (b : ℝ) (ω : ℕ → ℝ) :
    realStepPath T n b ω ⟨0, le_rfl, hT⟩ = 0 := sorry

end BGW.Skorokhod

/-! ## The contract -/

namespace BGW.StableTrees

open BGW.Probability.RealWalk BGW.Skorokhod

/-- The law of the step path `t ↦ S_{⌊n t⌋} / B n` on `[0,T]` under the canonical iid walk:
the genuine pushforward of `iidLaw ν`. (`B n` is an arbitrary real number here: no attraction
hypothesis is needed to define it.) -/
noncomputable def stepPathLaw (ν : ProbabilityMeasure ℝ) (T : ℝ) (B : ℕ → ℝ) (n : ℕ) :
    ProbabilityMeasure (D T ℝ) :=
  (iidLaw ν).map (realStepPath T n (B n))

theorem coe_stepPathLaw (ν : ProbabilityMeasure ℝ) (T : ℝ) (B : ℕ → ℝ) (n : ℕ) :
    (stepPathLaw ν T B n : Measure (D T ℝ)) =
      Measure.map (realStepPath T n (B n)) (iidLaw ν : Measure (ℕ → ℝ)) := sorry

/-- Single-law tightness (Node 2 / audit item 4), no hypothesis on `ν`, `B`: the law of the
step path is the image of a law on `ℕ → ℝ` under a map that factors continuously through the
finite product `Fin ⌊n T⌋₊ → ℝ`, so compact sets of the finite product have compact images;
alternatively `isTightMeasureSet_singleton` once `D T ℝ` is completely metrizable. -/
theorem isTightMeasureSet_stepPathLaw_singleton (ν : ProbabilityMeasure ℝ) (T : ℝ)
    (B : ℕ → ℝ) (n : ℕ) :
    IsTightMeasureSet {(stepPathLaw ν T B n : Measure (D T ℝ))} := sorry

/-! ### Probabilistic reductions -/

/-- Compact containment reduces to `maxTail`: exceeding `[-K, K]` somewhere on `[0,T]` is the
event `∃ k ≤ ⌊nT⌋₊, K b < |S_k|`. Stated as an inequality of (outer) measures. -/
theorem stepPathLaw_not_mem_Icc_le (ν : ProbabilityMeasure ℝ) {T : ℝ} (hT : 0 < T)
    (B : ℕ → ℝ) (n : ℕ) (hB : 0 < B n) (K : ℝ) :
    (stepPathLaw ν T B n : Measure (D T ℝ)) {f | ∃ t, f t ∉ Set.Icc (-K) K} ≤
      ENNReal.ofReal (maxTail ν ⌊(n : ℝ) * T⌋₊ (K * B n)) := sorry

/-- The initial window event is controlled by a short-block maximum (index `⌊2 n δ⌋₊`). -/
theorem measureReal_initialBad_le (ν : ProbabilityMeasure ℝ) (T : ℝ) (n : ℕ) {b ε δ : ℝ}
    (hb : 0 < b) :
    (iidLaw ν : Measure (ℕ → ℝ)).real {ω | initialBad T n b ε δ ω} ≤
      maxTail ν ⌊2 * (n : ℝ) * δ⌋₊ (ε * b) := sorry

/-- The terminal window event is controlled, by fresh start at the deterministic index
`⌊n (T - 2δ)⌋₊` (no symmetry of the steps and no time reversal), by a short-block maximum of
length `⌊n T⌋₊ - ⌊n (T - 2δ)⌋₊ ≤ 2 n δ + 1`. -/
theorem measureReal_terminalBad_le (ν : ProbabilityMeasure ℝ) {T : ℝ} (n : ℕ) {b ε δ : ℝ}
    (hb : 0 < b) (hδ : 0 ≤ δ) (hδT : 2 * δ ≤ T) :
    (iidLaw ν : Measure (ℕ → ℝ)).real {ω | terminalBad T n b ε δ ω} ≤
      maxTail ν (⌊(n : ℝ) * T⌋₊ - ⌊(n : ℝ) * (T - 2 * δ)⌋₊) (ε * b) := sorry

/-- The length of the terminal window is at most `2 n δ + 1`. -/
theorem floor_sub_floor_le {T : ℝ} (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (hδT : 2 * δ ≤ T) :
    ((⌊(n : ℝ) * T⌋₊ - ⌊(n : ℝ) * (T - 2 * δ)⌋₊ : ℕ) : ℝ) ≤ 2 * n * δ + 1 := sorry

/-- Outer-measure bridge (audit item 4; blueprint Node 9, last paragraph). The modulus event
`{4 ε < w'_f(δ)}` may be nonmeasurable, but its outer measure under the step-path law is at most
the probability of the bad finite-coordinate event of Node 8 (`closeExit`, `initialBad`,
`terminalBad`): the good event has compact subsets of almost full mass (inner regularity on the
Polish space `ℕ → ℝ`), their step-path images are compact, hence closed, subsets of the good path
set. No `Measure.map_apply` on a nonmeasurable set is used. -/
theorem stepPathLaw_modulus_le (ν : ProbabilityMeasure ℝ) {T : ℝ} (hT : 0 < T)
    (B : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) (hB : 0 < B n) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hδT : 4 * δ < T) :
    (stepPathLaw ν T B n : Measure (D T ℝ)) {f | 4 * ε < cadlagModulus f δ} ≤
      ENNReal.ofReal
        ((iidLaw ν : Measure (ℕ → ℝ)).real
            {ω | closeExit ⌊(n : ℝ) * T⌋₊ (ε * B n) ⌈2 * n * δ + 2⌉₊ ω} +
          (iidLaw ν : Measure (ℕ → ℝ)).real {ω | initialBad T n (B n) ε δ ω} +
          (iidLaw ν : Measure (ℕ → ℝ)).real {ω | terminalBad T n (B n) ε δ ω}) := sorry

/-! ### Eventual estimates and tightness for an attracted walk -/

/-- Eventual compact containment: first hypothesis (`hbdd`) of
`isTightMeasureSet_of_cadlagModulus_eventually`. Proof: `horizon_max_tight` and
`stepPathLaw_not_mem_Icc_le`, with `K = Set.Icc (-K) K` bounded. -/
theorem IsRealStableAttracted.stepPath_bounded_eventually {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {T : ℝ} (hT : 0 < T) :
    ∀ η > 0, ∃ K : Set ℝ, Bornology.IsBounded K ∧ ∃ N : ℕ, ∀ n ≥ N,
      (stepPathLaw ν T B n : Measure (D T ℝ)) {f | ∃ t, f t ∉ K} ≤ ENNReal.ofReal η := sorry

/-- Eventual modulus estimate: second hypothesis (`hmod`) of
`isTightMeasureSet_of_cadlagModulus_eventually` (Node 9; the order of choices is: exit radius
`ε/8`, coarse time length `a`, exit-count constant `C`, and only then `δ`). -/
theorem IsRealStableAttracted.stepPath_modulus_eventually {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {T : ℝ} (hT : 0 < T) :
    ∀ ε > 0, ∀ η > 0, ∃ δ : ℝ, 0 < δ ∧ δ < T ∧ ∃ N : ℕ, ∀ n ≥ N,
      (stepPathLaw ν T B n : Measure (D T ℝ)) {f | ε < cadlagModulus f δ} ≤
        ENNReal.ofReal η := sorry

/-- J1 tightness of the step-path laws of every attracted walk (Node 9), no centering, no
monotonicity, no lattice assumption. Follows from `isTightMeasureSet_of_cadlagModulus_eventually`
with `htight := isTightMeasureSet_stepPathLaw_singleton`. -/
theorem IsRealStableAttracted.isTightMeasureSet_stepPathLaw {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {T : ℝ} (hT : 0 < T) :
    IsTightMeasureSet (Set.range fun n => (stepPathLaw ν T B n : Measure (D T ℝ))) := sorry

end BGW.StableTrees
