import BGW.Skorokhod
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Contract probe for CT.C3 (advanced to CT4 because the compactness criterion needs it):
Billingsley's complete metric `d°` on the Skorokhod space, equivalent to the J1 metric, complete
when the state space is (Billingsley 1999, Theorems 12.1–12.2). Maintained file:
`BGW/Skorokhod/CompleteMetric.lean`. -/

open Filter Set
open scoped Topology ENNReal

namespace BGW.Skorokhod

variable {T : ℝ} {E : Type*}

/-- Billingsley's slope size `‖σ‖° = sup_{s < t} |log ((σ t - σ s) / (t - s))|` of a time
change, in `ℝ≥0∞` (it may be infinite). -/
noncomputable def TimeChange.logSlope (σ : TimeChange T) : ℝ≥0∞ :=
  ⨆ (s : Set.Icc (0 : ℝ) T) (t : Set.Icc (0 : ℝ) T) (_ : s < t),
    ENNReal.ofReal |Real.log (((σ t : ℝ) - σ s) / ((t : ℝ) - s))|

/-- Billingsley's distance `d°(f,g) = inf_σ max (‖σ‖°, sup_t dist (f t) (g (σ t)))` (C3). -/
noncomputable def j1CompleteDist [PseudoMetricSpace E] (f g : D T E) : ℝ :=
  (⨅ σ : TimeChange T, max (TimeChange.logSlope σ) (⨆ t, edist (f t) (g (σ t)))).toReal

/-- The Skorokhod space carrying Billingsley's metric `d°` (a type synonym of `D T E`). -/
def DComplete (T : ℝ) (E : Type*) [TopologicalSpace E] : Type _ := D T E

/-- The metric space structure of `d°` on `DComplete T E`. -/
noncomputable instance instMetricSpaceDComplete [MetricSpace E] : MetricSpace (DComplete T E) :=
  sorry

/-- The identity map `D T E → DComplete T E`: `d°` and the J1 metric induce the same topology
(Billingsley 1999, Theorem 12.1). -/
noncomputable def toDComplete [MetricSpace E] : D T E ≃ₜ DComplete T E where
  toEquiv := Equiv.refl _
  continuous_toFun := sorry
  continuous_invFun := sorry

/-- The distance of `DComplete` is `d°`. -/
theorem dist_toDComplete [MetricSpace E] (f g : D T E) :
    dist (toDComplete f) (toDComplete g) = j1CompleteDist f g := sorry

/-- Comparison of the two metrics on `[0,T]`: `d ≤ max 1 T * (exp d° - 1)` (Billingsley 1999,
(12.17), stated there for `T = 1`; the factor `T` comes from `|σ t - t| ≤ t (exp ‖σ‖° - 1)`). -/
theorem dist_le_exp_j1CompleteDist_sub_one [MetricSpace E] (f g : D T E) :
    dist f g ≤ max 1 T * (Real.exp (j1CompleteDist f g) - 1) := sorry

/-- `d°` is complete when `E` is complete (Billingsley 1999, Theorem 12.2). -/
instance instCompleteSpaceDComplete [MetricSpace E] [CompleteSpace E] :
    CompleteSpace (DComplete T E) := sorry

/-- The Skorokhod space of a complete metric space is completely metrizable (C3). -/
instance instIsCompletelyMetrizableSpace [MetricSpace E] [CompleteSpace E] :
    TopologicalSpace.IsCompletelyMetrizableSpace (D T E) := sorry

end BGW.Skorokhod
