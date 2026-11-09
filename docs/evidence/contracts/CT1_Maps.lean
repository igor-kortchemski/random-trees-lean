import Mathlib.Topology.Order.Cadlag
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Real
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Analysis.Normed.Ring.Basic

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

end BGW.Skorokhod
