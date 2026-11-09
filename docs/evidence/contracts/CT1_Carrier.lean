import Mathlib.Topology.Order.Cadlag
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Real
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

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

end BGW.Skorokhod
