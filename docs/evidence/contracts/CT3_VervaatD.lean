import Mathlib.Topology.Order.Cadlag
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Real
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.MetricSpace.Polish
import BGW.Tree.CycleLemma
import BGW.ContinuumTrees.Vervaat

/-! Contract probe for CT.C1 (carrier and J1 metric). Proofs are `sorry` here only;
the maintained file `BGW/Skorokhod/Basic.lean` must prove these exact statements. -/

open Set Filter Topology

namespace BGW.Skorokhod

/-- The Skorokhod space `D([0,T], E)` of càdlàg paths on `[0,T]`. On the subtype
`Set.Icc 0 T`, `IsCadlag` is Billingsley's condition: right-continuity at every
`t < T` and a left limit at every `t > 0`. -/
structure D (T : ℝ) (E : Type*) [TopologicalSpace E] where
  /-- The underlying path. -/
  toFun : Set.Icc (0 : ℝ) T → E
  /-- The path is càdlàg. -/
  isCadlag' : IsCadlag toFun

variable {T : ℝ} {E : Type*}

instance [TopologicalSpace E] : FunLike (D T E) (Set.Icc (0 : ℝ) T) E where
  coe := D.toFun
  coe_injective f g h := by cases f; cases g; congr

theorem isCadlag [TopologicalSpace E] (f : D T E) : IsCadlag f := f.isCadlag'

@[ext] theorem ext [TopologicalSpace E] {f g : D T E} (h : ∀ t, f t = g t) : f = g :=
  DFunLike.ext f g h

/-- Time changes of `[0,T]`: increasing bijections, equivalently increasing homeomorphisms. -/
abbrev TimeChange (T : ℝ) := Set.Icc (0 : ℝ) T ≃o Set.Icc (0 : ℝ) T

/-- Billingsley's Skorokhod J1 distance:
`d(f,g) = inf_σ max (sup_t |σ t - t|) (sup_t dist (f t) (g (σ t)))`. -/
noncomputable def j1Dist [PseudoMetricSpace E] (f g : D T E) : ℝ :=
  ⨅ σ : TimeChange T, max (⨆ t, |((σ t : ℝ)) - t|) (⨆ t, dist (f t) (g (σ t)))

/-- Paths are bounded, so the suprema in `j1Dist` are genuine. -/
theorem bddAbove_range_dist [PseudoMetricSpace E] (f g : D T E) (σ : TimeChange T) :
    BddAbove (Set.range fun t => dist (f t) (g (σ t))) := sorry

/-- The J1 metric space structure, with distance `j1Dist`. -/
noncomputable instance instMetricSpace [MetricSpace E] : MetricSpace (D T E) := sorry

theorem dist_eq_j1Dist [MetricSpace E] (f g : D T E) : dist f g = j1Dist f g := sorry

/-- The J1 distance is at most the uniform distance (take the identity time change). -/
theorem dist_le_iSup_dist [MetricSpace E] (f g : D T E) :
    dist f g ≤ ⨆ t, dist (f t) (g t) := sorry

/-- Billingsley's characterization of J1 convergence by time changes. -/
theorem tendsto_iff_exists_timeChange [MetricSpace E] {ι : Type*} {l : Filter ι}
    {u : ι → D T E} {f : D T E} :
    Tendsto u l (𝓝 f) ↔ ∃ σ : ι → TimeChange T,
      Tendsto (fun i => ⨆ t, |((σ i t : ℝ)) - t|) l (𝓝 0) ∧
      Tendsto (fun i => ⨆ t, dist (u i (σ i t)) (f t)) l (𝓝 0) := sorry


/-! ## Contract CT1_Maps (CT.C5, C6, C7, C36). Statements above this line are CT1_Carrier. -/

section Maps

variable {T : ℝ} {E : Type*}

/-- A continuous path, seen as a càdlàg path (C5). -/
def ofContinuous [TopologicalSpace E] (f : C(Set.Icc (0 : ℝ) T, E)) : D T E :=
  ⟨f, f.continuous.isCadlag⟩

/-- On continuous paths the J1 distance is at most the uniform distance (C5.1). -/
theorem lipschitzWith_one_ofContinuous [MetricSpace E] :
    LipschitzWith 1 (ofContinuous (T := T) (E := E)) := sorry

/-- J1 convergence to a continuous path is uniform convergence (C5.2). -/
theorem tendsto_iSup_dist_of_tendsto_ofContinuous [MetricSpace E] {ι : Type*} {l : Filter ι}
    {u : ι → D T E} {f : C(Set.Icc (0 : ℝ) T, E)} (h : Tendsto u l (𝓝 (ofContinuous f))) :
    Tendsto (fun i => ⨆ t, dist (u i t) (f t)) l (𝓝 0) := sorry

/-- Continuous paths form a closed subset of `D`, on which J1 is the uniform topology (C5.3). -/
theorem isClosedEmbedding_ofContinuous [MetricSpace E] :
    Topology.IsClosedEmbedding (ofContinuous (T := T) (E := E)) := sorry

/-- Evaluation at time `0` is 1-Lipschitz (C6.1). -/
theorem lipschitzWith_one_eval_zero [MetricSpace E] (hT : 0 ≤ T) :
    LipschitzWith 1 (fun f : D T E => f ⟨0, le_rfl, hT⟩) := sorry

/-- Evaluation at the terminal time `T` is 1-Lipschitz (C6.1). -/
theorem lipschitzWith_one_eval_right [MetricSpace E] (hT : 0 ≤ T) :
    LipschitzWith 1 (fun f : D T E => f ⟨T, hT, le_rfl⟩) := sorry

/-- Evaluation at `t` is continuous at every path continuous at `t` (C6.1). -/
theorem continuousAt_eval [MetricSpace E] {f : D T E} {t : Set.Icc (0 : ℝ) T}
    (hf : ContinuousAt f t) : ContinuousAt (fun g : D T E => g t) f := sorry

/-- Restriction of a path on `[0,T]` to `[0,a]` (C6.2). -/
def restrict [TopologicalSpace E] {a : ℝ} (haT : a ≤ T) (f : D T E) : D a E where
  toFun t := f ⟨t, t.2.1, t.2.2.trans haT⟩
  isCadlag' := sorry

/-- Restriction is continuous at every path continuous at `a` (C6.2). -/
theorem continuousAt_restrict [MetricSpace E] {a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) {f : D T E}
    (hf : ContinuousAt f ⟨a, ha, haT⟩) : ContinuousAt (restrict haT) f := sorry

/-- Constant extension of a path on `[0,a]` to `[0,T]`: `t ↦ g (min t a)` (C6.2). -/
def extendConst [TopologicalSpace E] {a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) (g : D a E) : D T E where
  toFun t := g ⟨min (t : ℝ) a, le_min t.2.1 ha, min_le_right _ _⟩
  isCadlag' := sorry

/-- Constant extension is 1-Lipschitz (C6.2). -/
theorem lipschitzWith_one_extendConst [MetricSpace E] {a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) :
    LipschitzWith 1 (extendConst (E := E) (T := T) ha haT) := sorry

/-- The path stopped at time `a`: `t ↦ f (max 0 (min t a))`; total in `a` (C6.2). -/
def stop [TopologicalSpace E] (a : ℝ) (f : D T E) : D T E where
  toFun t := f ⟨max 0 (min (t : ℝ) a), le_max_left _ _,
    max_le (t.2.1.trans t.2.2) ((min_le_left _ _).trans t.2.2)⟩
  isCadlag' := sorry

/-- For `0 ≤ a ≤ T`, stopping is extension after restriction (C6.2). -/
theorem stop_eq_extendConst_restrict [TopologicalSpace E] {a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T)
    (f : D T E) : stop a f = extendConst ha haT (restrict haT f) := sorry

/-- Stopping at `a` is continuous at every path continuous at `a` (C6.2). -/
theorem continuousAt_stop [MetricSpace E] {a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) {f : D T E}
    (hf : ContinuousAt f ⟨a, ha, haT⟩) : ContinuousAt (stop a) f := sorry

/-- The infimum of a real path is 1-Lipschitz for J1 (C6.3). -/
theorem lipschitzWith_one_iInf (hT : 0 ≤ T) : LipschitzWith 1 (fun f : D T ℝ => ⨅ t, f t) :=
  sorry

/-- The supremum of a real path is 1-Lipschitz for J1 (C6.3). -/
theorem lipschitzWith_one_iSup (hT : 0 ≤ T) : LipschitzWith 1 (fun f : D T ℝ => ⨆ t, f t) :=
  sorry

/-- The oscillation `sup_{s ≥ c} |g s - g c|` after time `c` is continuous at every path
continuous at `c` (C6.3). -/
theorem continuousAt_oscillationFrom {c : Set.Icc (0 : ℝ) T} {f : D T ℝ}
    (hf : ContinuousAt f c) :
    ContinuousAt (fun g : D T ℝ => ⨆ s : {s : Set.Icc (0 : ℝ) T // c ≤ s}, |g s - g c|) f :=
  sorry

/-- Time–space scaling restricted to `[0,a]`: `t ↦ k * g (min (s * t) T)` for a spatial factor
`k` (coordinatewise for `E = Fin d → ℝ`) and a time factor `s > 0` (C6.4). -/
def timeSpaceScale [NormedRing E] (a : ℝ) (hT : 0 ≤ T) (p : D T E × E × Set.Ioi (0 : ℝ)) :
    D a E where
  toFun t := p.2.1 * p.1 ⟨min (p.2.2 * t) T,
    le_min (mul_nonneg (le_of_lt p.2.2.2) t.2.1) hT, min_le_right _ _⟩
  isCadlag' := sorry

/-- Time–space scaling is continuous at `(f, 1, 1)` when `f` is continuous at `a < T`
(C6.4, the core of the source's Lemma 5.7). -/
theorem continuousAt_timeSpaceScale [NormedRing E] {a : ℝ} (ha : 0 < a) (haT : a < T)
    {f : D T E} (hf : ContinuousAt f ⟨a, ha.le, haT.le⟩) :
    ContinuousAt (timeSpaceScale a (ha.le.trans haT.le)) (f, 1, ⟨1, Set.mem_Ioi.mpr one_pos⟩) := sorry

/-- Time–space scaling of continuous paths (C6.4, continuous coordinates). -/
def timeSpaceScaleC [NormedRing E] (a : ℝ) (hT : 0 ≤ T)
    (p : C(Set.Icc (0 : ℝ) T, E) × E × Set.Ioi (0 : ℝ)) : C(Set.Icc (0 : ℝ) a, E) where
  toFun t := p.2.1 * p.1 ⟨min (p.2.2 * t) T,
    le_min (mul_nonneg (le_of_lt p.2.2.2) t.2.1) hT, min_le_right _ _⟩
  continuous_toFun := sorry

/-- On continuous paths, time–space scaling is continuous everywhere (C6.4). -/
theorem continuous_timeSpaceScaleC [NormedRing E] (a : ℝ) (hT : 0 ≤ T) :
    Continuous (timeSpaceScaleC (E := E) a hT) := sorry

/-- Stopped-path approximation: the J1 distance between `f` stopped at `a` and `f` is at most
the oscillation of `f` after `a` (C7). -/
theorem dist_stop_le [MetricSpace E] {a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) (f : D T E) :
    dist (stop a f) f ≤ ⨆ s : {s : Set.Icc (0 : ℝ) T // a ≤ (s : ℝ)},
      dist (f s) (f ⟨a, ha, haT⟩) := sorry

/-- A path continuous at the terminal time is the J1 limit of its stopped paths (C7). -/
theorem tendsto_stop_nhdsLT [MetricSpace E] (hT : 0 < T) {f : D T E}
    (hf : ContinuousAt f ⟨T, hT.le, le_rfl⟩) :
    Tendsto (fun a => stop a f) (𝓝[<] T) (𝓝 f) := sorry

/-- The largest positive jump `sup_t (f t - f (t-)) ∨ 0` of a real càdlàg path (C36). -/
noncomputable def maxJump (f : D T ℝ) : ℝ := ⨆ t, max (f t - Function.leftLim f t) 0

/-- The largest positive jump is 2-Lipschitz for J1 (C36). -/
theorem lipschitzWith_two_maxJump : LipschitzWith 2 (maxJump (T := T)) := sorry

/-- The largest absolute jump `sup_t |f t - f (t-)|` of a real càdlàg path (C36). -/
noncomputable def maxAbsJump (f : D T ℝ) : ℝ := ⨆ t, |f t - Function.leftLim f t|

/-- The largest absolute jump is 2-Lipschitz for J1 (C36). -/
theorem lipschitzWith_two_maxAbsJump : LipschitzWith 2 (maxAbsJump (T := T)) := sorry

end Maps


/-! ## Contract CT2_PathSpace (CT.C2, C4, C11(2), C12). Statements above: CT1_Carrier, CT1_Maps. -/

section PathSpace

open MeasureTheory

variable {T : ℝ} {E : Type*}

/-- The Borel σ-algebra of the J1 topology on `D` (C4). -/
noncomputable instance instMeasurableSpace [MetricSpace E] : MeasurableSpace (D T E) :=
  borel (D T E)

instance instBorelSpace [MetricSpace E] : BorelSpace (D T E) := ⟨rfl⟩

/-- `D` is separable for J1 when `E` is (Billingsley 1999, Theorem 12.2; C2). -/
instance instSeparableSpace [MetricSpace E] [TopologicalSpace.SeparableSpace E] :
    TopologicalSpace.SeparableSpace (D T E) := sorry

/-- Each evaluation map is Borel for J1 (C4.1). -/
theorem measurable_eval [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (t : Set.Icc (0 : ℝ) T) : Measurable (fun f : D T E => f t) := sorry

/-- For separable `E`, the Borel σ-algebra of `D` is generated by the evaluations at the times
of any dense set containing the terminal time (Billingsley 1999, Theorem 12.5; C4.2). -/
theorem measurableSpace_eq_iSup_comap_eval [MetricSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E] {S : Set (Set.Icc (0 : ℝ) T)} (hS : Dense S)
    (hT0 : 0 ≤ T) (hTS : (⟨T, hT0, le_rfl⟩ : Set.Icc (0 : ℝ) T) ∈ S) :
    (inferInstance : MeasurableSpace (D T E)) =
      ⨆ t ∈ S, MeasurableSpace.comap (fun f : D T E => f t) ‹MeasurableSpace E› := sorry

/-- Joint evaluation `(f, t) ↦ f t` is measurable (C4.3). -/
theorem measurable_eval₂ [MetricSpace E] [MeasurableSpace E] [BorelSpace E] :
    Measurable (fun p : D T E × Set.Icc (0 : ℝ) T => p.1 p.2) := sorry

/-- The left limit at a fixed time is a measurable functional (C4.4). -/
theorem measurable_leftLim_eval [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (t : Set.Icc (0 : ℝ) T) : Measurable (fun f : D T E => Function.leftLim f t) := sorry

/-- The supremum of a real path over an interval of times is measurable (C4.4). -/
theorem measurable_iSup_eval {J : Set (Set.Icc (0 : ℝ) T)} (hJ : J.OrdConnected) :
    Measurable (fun f : D T ℝ => ⨆ s : J, f s) := sorry

/-- The infimum of a real path over an interval of times is measurable (C4.4). -/
theorem measurable_iInf_eval {J : Set (Set.Icc (0 : ℝ) T)} (hJ : J.OrdConnected) :
    Measurable (fun f : D T ℝ => ⨅ s : J, f s) := sorry

/-- Convergence in law in `D` from convergence of the restrictions to `[0, a k]` for times
`a k ↑ T`, a limit almost surely continuous at `T`, and control of the oscillation after
`a k` (Billingsley 1999, Theorem 3.2 with C7; C11(2)). -/
theorem tendsto_of_tendsto_restrict_of_oscillation {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] [MetricSpace E] [TopologicalSpace.SeparableSpace E]
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n)) {Y : (n : ℕ) → Ω n → D T E}
    (hY : ∀ n, Measurable (Y n)) {ν : ProbabilityMeasure (D T E)} (hT : 0 < T)
    {a : ℕ → ℝ} (ha0 : ∀ k, 0 ≤ a k) (haT : ∀ k, a k < T) (hlim : Tendsto a atTop (𝓝 T))
    (hpre : ∀ k, Tendsto (fun n => (μ n).map (restrict (haT k).le ∘ Y n)) atTop
      (𝓝 (ν.map (restrict (haT k).le))))
    (hcont : ∀ᵐ (f : D T E) ∂(ν : Measure (D T E)), ContinuousAt f ⟨T, hT.le, le_rfl⟩)
    (hosc : ∀ η > 0, Tendsto (fun k => limsup (fun n => (μ n : Measure (Ω n)).real
      {ω | η < ⨆ s : {s : Set.Icc (0 : ℝ) T // a k ≤ (s : ℝ)},
        dist (Y n ω s) (Y n ω ⟨a k, ha0 k, (haT k).le⟩)}) atTop) atTop (𝓝 0)) :
    Tendsto (fun n => (μ n).map (Y n)) atTop (𝓝 ν) := sorry

/-- Laws on `D` are determined by their finite-dimensional distributions at times of a dense
set containing the terminal time (C12(1)). -/
theorem ext_of_finiteDimensional [MetricSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E] {P Q : ProbabilityMeasure (D T E)}
    {S : Set (Set.Icc (0 : ℝ) T)} (hS : Dense S) (hT0 : 0 ≤ T)
    (hTS : (⟨T, hT0, le_rfl⟩ : Set.Icc (0 : ℝ) T) ∈ S)
    (h : ∀ s : Finset (Set.Icc (0 : ℝ) T), (↑s : Set (Set.Icc (0 : ℝ) T)) ⊆ S →
      P.map (fun f : D T E => fun t : s => f t) = Q.map (fun f : D T E => fun t : s => f t)) :
    P = Q := sorry

/-- Two laws on `D`, both almost surely continuous at `T`, with equal restrictions to `[0, a k]`
for times `a k ↑ T`, are equal (C12(2)). -/
theorem ext_of_restrict [MetricSpace E] [TopologicalSpace.SeparableSpace E]
    {P Q : ProbabilityMeasure (D T E)} (hT : 0 < T) {a : ℕ → ℝ} (haT : ∀ k, a k < T)
    (hlim : Tendsto a atTop (𝓝 T))
    (hP : ∀ᵐ (f : D T E) ∂(P : Measure (D T E)), ContinuousAt f ⟨T, hT.le, le_rfl⟩)
    (hQ : ∀ᵐ (f : D T E) ∂(Q : Measure (D T E)), ContinuousAt f ⟨T, hT.le, le_rfl⟩)
    (h : ∀ k, P.map (restrict (haT k).le) = Q.map (restrict (haT k).le)) : P = Q := sorry

/-- A law on `D` has at most countably many fixed discontinuity times (C12(3)). -/
theorem countable_setOf_measure_jump_ne_zero [MetricSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E] (P : ProbabilityMeasure (D T E)) :
    {t : Set.Icc (0 : ℝ) T |
      (P : Measure (D T E)) {f | Function.leftLim f t ≠ f t} ≠ 0}.Countable := sorry

end PathSpace


/-! ## Contract CT3_VervaatD (CT.C33, C34). Statements above: CT1_Carrier, CT1_Maps, CT2_PathSpace. -/

section VervaatD

open MeasureTheory

/-- The first time at which a real càdlàg path on `[0,1]` attains its infimum, either as a
value or as a left limit (with `f (0-) = f 0`); C33. -/
noncomputable def vervaatTime (f : D 1 ℝ) : Set.Icc (0 : ℝ) 1 :=
  Set.projIcc 0 1 zero_le_one (sInf {t : ℝ | ∃ h : t ∈ Set.Icc (0 : ℝ) 1,
    min (Function.leftLim f ⟨t, h⟩) (f ⟨t, h⟩) = ⨅ s, f s})

/-- The infimum is attained at `vervaatTime f`, as a value or a left limit (C33). -/
theorem min_leftLim_vervaatTime (f : D 1 ℝ) :
    min (Function.leftLim f (vervaatTime f)) (f (vervaatTime f)) = ⨅ s, f s := sorry

/-- `vervaatTime f` is the first such time (C33). -/
theorem vervaatTime_le (f : D 1 ℝ) {t : Set.Icc (0 : ℝ) 1}
    (ht : min (Function.leftLim f t) (f t) = ⨅ s, f s) : vervaatTime f ≤ t := sorry

/-- The càdlàg Vervaat map: rotate at `g = vervaatTime f`, subtract the infimum, and correct
by `f 1 - f 0` after the wrap point:
`V f t = f (g + t) - m` if `g + t ≤ 1`, `V f t = f (g + t - 1) + f 1 - m - f 0` otherwise (C33). -/
noncomputable def vervaatD (f : D 1 ℝ) : D 1 ℝ where
  toFun t :=
    if (vervaatTime f : ℝ) + t ≤ 1 then
      f (Set.projIcc 0 1 zero_le_one ((vervaatTime f : ℝ) + t)) - ⨅ s, f s
    else
      f (Set.projIcc 0 1 zero_le_one ((vervaatTime f : ℝ) + t - 1)) +
        f ⟨1, zero_le_one, le_rfl⟩ - (⨅ s, f s) - f ⟨0, le_rfl, zero_le_one⟩
  isCadlag' := sorry

/-- If the first infimum time is positive and `f` is continuous there, then `V f` is continuous
at `1` with value `f 1 - f 0` (C33.3, with the corrected premise `0 < g` of roadmap §8.3: for
`f t = t` on `[0,1)` and `f 1 = 2` one has `g = 0` and `V f = f`, discontinuous at `1`). -/
theorem vervaatD_one_of_continuousAt {f : D 1 ℝ} (hg0 : 0 < (vervaatTime f : ℝ))
    (hg : ContinuousAt f (vervaatTime f)) :
    vervaatD f ⟨1, zero_le_one, le_rfl⟩ = f ⟨1, zero_le_one, le_rfl⟩ - f ⟨0, le_rfl, zero_le_one⟩ ∧
      ContinuousAt (vervaatD f) ⟨1, zero_le_one, le_rfl⟩ := sorry

/-- The càdlàg Vervaat map is Borel (C33.4). -/
theorem measurable_vervaatD : Measurable vervaatD := sorry

/-- The step path `t ↦ w_{⌊k t⌋} / B` of a word `x` of length `k`, where `w_j` is the sum of
the first `j` letters; its value at `1` is `w_k / B` (C33.5). -/
noncomputable def stepPath (x : List ℤ) (B : ℝ) : D 1 ℝ where
  toFun t := ((x.take ⌊(x.length : ℝ) * t⌋₊).sum : ℝ) / B
  isCadlag' := sorry

/-- The paper's discrete Vervaat index: the first `i ∈ [1, k]` at which the prefix sum `w_i`
attains `min_{1 ≤ j ≤ k} w_j` (C33.5); `0` for the empty word. -/
noncomputable def vervaatIndex (x : List ℤ) : ℕ :=
  sInf {i | 1 ≤ i ∧ i ≤ x.length ∧ ∀ j, 1 ≤ j → j ≤ x.length → (x.take i).sum ≤ (x.take j).sum}

/-- Discrete correspondence: for a word whose prefix sums go below zero, the càdlàg Vervaat
map of its step path is the step path of its rotation at the Vervaat index (C33.5). -/
theorem vervaatD_stepPath {x : List ℤ} (hx : ∃ j, 1 ≤ j ∧ j ≤ x.length ∧ (x.take j).sum < 0)
    {B : ℝ} (hB : 0 < B) :
    vervaatD (stepPath x B) = stepPath (x.rotate (vervaatIndex x)) B := sorry

/-- For a bridge word, the rotation at the Vervaat index is a tree excursion (C33.5, in the
library's walk language). -/
theorem isTreeExcursion_rotate_vervaatIndex {n : ℕ} {x : List ℤ} (hx : x ∈ bridgeWords n) :
    IsTreeExcursion (x.rotate (vervaatIndex x)) := sorry

/-- On continuous loops, the càdlàg Vervaat map agrees with the existing continuous-loop
transform (C33, comparison with `ContinuumTrees.Vervaat.vervaat`). -/
theorem vervaatD_ofContinuous (g : C(unitInterval, ℝ)) (hloop : g 0 = g 1) :
    vervaatD (ofContinuous g) = ofContinuous (ContinuumTrees.Vervaat.vervaat ⟨g, hloop⟩) := sorry

/-- Continuity of the càdlàg Vervaat map (C34): at a path vanishing at `0`, continuous at `1`,
whose infimum is attained (as a value or left limit) only at an interior time `g` where the path
is continuous. Moreover `V f` vanishes at `0` and is continuous at `1 - g`. -/
theorem continuousAt_vervaatD {f : D 1 ℝ} (h0 : f ⟨0, le_rfl, zero_le_one⟩ = 0)
    (h1 : ContinuousAt f ⟨1, zero_le_one, le_rfl⟩)
    (huniq : ∀ t : Set.Icc (0 : ℝ) 1,
      min (Function.leftLim f t) (f t) = ⨅ s, f s → t = vervaatTime f)
    (hint : 0 < (vervaatTime f : ℝ) ∧ (vervaatTime f : ℝ) < 1)
    (hg : ContinuousAt f (vervaatTime f)) :
    ContinuousAt vervaatD f ∧ vervaatD f ⟨0, le_rfl, zero_le_one⟩ = 0 ∧
      ContinuousAt (vervaatD f) (Set.projIcc 0 1 zero_le_one (1 - (vervaatTime f : ℝ))) := sorry

end VervaatD

end BGW.Skorokhod
