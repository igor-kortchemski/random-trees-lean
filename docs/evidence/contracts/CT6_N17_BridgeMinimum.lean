import BGW.StableTrees.StableBridgeClosed
import BGW.StableTrees.BridgeProjective
import BGW.StableTrees.StableUniqueMinimum
import BGW.StableTrees.StableProcessLaw
import BGW.Skorokhod.Restrict
import BGW.Skorokhod.Vervaat
import BGW.Skorokhod.VervaatContinuity

/-! Contract probe for CT6 N17 (C32) and the N18 application (C34): under the closed stable bridge
law on `D 1 ℝ`, almost surely the generalized minimizer is unique, interior, a continuity point,
and the minimum is negative; hence the càdlàg Vervaat map is a.s. continuous at the bridge path.

Maintained files (proposed): `BGW/StableTrees/StableBridgeMinimum.lean` (N17),
`BGW/StableTrees/StableBridgeVervaat.lean` (N18, or the same file if short).

Sealed inputs: `stableBridgeLaw`, `stableBridgeLaw_endpoints`, `stableBridgeLaw_ae_continuousAt`,
`map_restrict_stableBridgeLaw_absolutelyContinuous` (prefix `a < 1` absolutely continuous w.r.t.
`stableProcessLaw θ a`), `vervaatTime`, `min_leftLim_vervaatTime`, `vervaatTime_le`,
`continuousAt_vervaatD`, `vervaatD_one_of_continuousAt`, `IsGenMinimizer` and friends.
Copied (audited/contract, unproved): the N11 continuous-minimum theorem and the N11 compact
regularity at `0`.

Route. For a fixed prefix `a ∈ (0,1)`, N11 transfers along `map restrict ≪ P_a`. The global
minimizer and any alleged second one are enclosed in one strictly larger prefix `a_n = 1 - 1/(n+2)`,
using the endpoint facts (`0`, `1` are not minimizers since `inf < 0 = f 0 = f 1 = f 1-`) and the
adapters: left limits in a restriction agree with those of the original path; the prefix infimum
equals the global one when a minimizer lies in `[0,a]`.

Flag (N18). The sealed `continuousAt_vervaatD` needs exactly: `f 0 = 0`, `ContinuousAt f 1`,
uniqueness of the generalized minimizer (with respect to `vervaatTime`), interiority of `vervaatTime`
and `ContinuousAt f (vervaatTime f)`. All five are a.s. true under the bridge law (endpoints +
`stableBridgeLaw_ae_continuousAt` at `1` + N17); no extra hypothesis (no separate "no jump at the
minimizer" or `f 1 = 0`) is required. Its conclusion also yields `vervaatD f 0 = 0` and continuity
of `vervaatD f` at the wrap point `1 - g`. -/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace BGW.StableTrees

open BGW.Skorokhod

-- copied from contract CT6_N11_ContinuousMinimum (not part of this contract)
theorem IsStableLevyLaw.ae_regular_at_zero {θ T : ℝ} {P : ProbabilityMeasure (D T ℝ)}
    (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) (hP : IsStableLevyLaw θ T P) :
    ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)),
      ∀ ε : ℝ, 0 < ε →
        (∃ s : Set.Icc (0 : ℝ) T, 0 < (s : ℝ) ∧ (s : ℝ) < ε ∧ f s < f ⟨0, le_rfl, hT.le⟩) ∧
        (∃ s : Set.Icc (0 : ℝ) T, 0 < (s : ℝ) ∧ (s : ℝ) < ε ∧ f ⟨0, le_rfl, hT.le⟩ < f s) := by
  sorry

-- copied from contract CT6_N11_ContinuousMinimum (not part of this contract)
theorem IsStableLevyLaw.ae_unique_continuous_minimum {θ T : ℝ} {P : ProbabilityMeasure (D T ℝ)}
    (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) (hP : IsStableLevyLaw θ T P) :
    ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)),
      ∃ g : Set.Icc (0 : ℝ) T,
        0 < (g : ℝ) ∧ (g : ℝ) < T ∧ ContinuousAt f g ∧
        min (Function.leftLim f g) (f g) = ⨅ t, f t ∧
        ∀ s : Set.Icc (0 : ℝ) T,
          min (Function.leftLim f s) (f s) = (⨅ t, f t) → s = g := by
  sorry

/-! ### Deterministic adapters between a path and its restriction to `[0,a]` -/

/-- Left limits in the restriction agree with those of the original path (also at `t = a`, since
only a left neighbourhood is used; at `t = 0` both are the value). -/
theorem leftLim_restrict_eq {T a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) (f : D T ℝ)
    (t : Set.Icc (0 : ℝ) a) :
    Function.leftLim (restrict (E := ℝ) haT f) t =
      Function.leftLim f (⟨t, t.2.1, t.2.2.trans haT⟩ : Set.Icc (0 : ℝ) T) := by
  sorry

/-- Continuity of the restriction at an interior time `t < a` gives continuity of the original. -/
theorem continuousAt_of_continuousAt_restrict {T a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) (f : D T ℝ)
    {t : Set.Icc (0 : ℝ) a} (ht : (t : ℝ) < a)
    (h : ContinuousAt (restrict (E := ℝ) haT f) t) :
    ContinuousAt f (⟨t, t.2.1, t.2.2.trans haT⟩ : Set.Icc (0 : ℝ) T) := by
  sorry

/-- If a generalized minimizer `g` of `f` lies in `[0,a]`, the prefix infimum is the global one. -/
theorem iInf_restrict_eq_of_genMin {T a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) (f : D T ℝ)
    {g : Set.Icc (0 : ℝ) T} (hg : IsGenMinimizer f g) (hga : (g : ℝ) ≤ a) :
    (⨅ t, restrict (E := ℝ) haT f t) = ⨅ t, f t := by
  sorry

/-- Endpoints are not generalized minimizers of a bridge path with negative infimum. -/
theorem not_isGenMinimizer_endpoints {f : D 1 ℝ}
    (h0 : f ⟨0, le_rfl, zero_le_one⟩ = 0) (h1 : f ⟨1, zero_le_one, le_rfl⟩ = 0)
    (hl : Function.leftLim f ⟨1, zero_le_one, le_rfl⟩ = 0) (hneg : (⨅ t, f t) < 0) :
    ¬ IsGenMinimizer f ⟨0, le_rfl, zero_le_one⟩ ∧ ¬ IsGenMinimizer f ⟨1, zero_le_one, le_rfl⟩ := by
  sorry

/-! ### Probabilistic transfers to bridge prefixes -/

/-- The bridge takes a negative value: the infimum is `< 0` (N06 through any prefix, plus
`f 0 = 0` a.s.). -/
theorem stableBridgeLaw_ae_iInf_neg {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)), (⨅ t, f t) < 0 := by
  sorry

/-- N11 on each strict prefix `[0,a]`, `0 < a < 1`, transferred through the absolutely continuous
prefix law. -/
theorem stableBridgeLaw_ae_prefix_unique_continuous_minimum {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (ha : 0 < a) (ha1 : a < 1) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)),
      ∃ g : Set.Icc (0 : ℝ) a,
        0 < (g : ℝ) ∧ (g : ℝ) < a ∧ ContinuousAt (restrict (E := ℝ) ha1.le f) g ∧
        min (Function.leftLim (restrict (E := ℝ) ha1.le f) g) (restrict (E := ℝ) ha1.le f g) =
          ⨅ t, restrict (E := ℝ) ha1.le f t ∧
        ∀ s : Set.Icc (0 : ℝ) a,
          min (Function.leftLim (restrict (E := ℝ) ha1.le f) s) (restrict (E := ℝ) ha1.le f s) =
            (⨅ t, restrict (E := ℝ) ha1.le f t) → s = g := by
  sorry

/-! ### N17 -/

/-- **N17 (C32).** Under the closed stable bridge law, almost surely the infimum is negative and the
generalized minimizer, `vervaatTime f`, is unique, interior, and a continuity point of `f`. -/
theorem stableBridgeLaw_ae_minimum {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)),
      (⨅ t, f t) < 0 ∧
      (0 < (vervaatTime f : ℝ) ∧ (vervaatTime f : ℝ) < 1) ∧
      ContinuousAt f (vervaatTime f) ∧
      ∀ t : Set.Icc (0 : ℝ) 1,
        min (Function.leftLim f t) (f t) = (⨅ s, f s) → t = vervaatTime f := by
  sorry

/-- The same in `∃`-form with `IsGenMinimizer`. -/
theorem stableBridgeLaw_ae_existsUnique_continuous_minimizer {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)),
      (⨅ t, f t) < 0 ∧
      ∃ g : Set.Icc (0 : ℝ) 1,
        0 < (g : ℝ) ∧ (g : ℝ) < 1 ∧ ContinuousAt f g ∧ IsGenMinimizer f g ∧
        ∀ s : Set.Icc (0 : ℝ) 1, IsGenMinimizer f s → s = g := by
  sorry

/-! ### N18 (C34 application) -/

/-- **N18.** Under the bridge law, the càdlàg Vervaat map is almost surely continuous at the
path. -/
theorem stableBridgeLaw_ae_continuousAt_vervaatD {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)), ContinuousAt vervaatD f := by
  filter_upwards [stableBridgeLaw_endpoints hθ, stableBridgeLaw_ae_minimum hθ,
    stableBridgeLaw_ae_continuousAt hθ ⟨1, zero_le_one, le_rfl⟩] with f he hm h1
  exact (continuousAt_vervaatD he.1 h1 hm.2.2.2 hm.2.1 hm.2.2.1).1

/-- **N18 (endpoints).** Almost surely the Vervaat image starts and ends at `0`, is continuous at
`1`, and is continuous at the wrap point `1 - vervaatTime f`. -/
theorem stableBridgeLaw_ae_vervaat_endpoints {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)),
      vervaatD f ⟨0, le_rfl, zero_le_one⟩ = 0 ∧
      vervaatD f ⟨1, zero_le_one, le_rfl⟩ = 0 ∧
      ContinuousAt (vervaatD f) ⟨1, zero_le_one, le_rfl⟩ ∧
      ContinuousAt (vervaatD f) (Set.projIcc 0 1 zero_le_one (1 - (vervaatTime f : ℝ))) := by
  filter_upwards [stableBridgeLaw_endpoints hθ, stableBridgeLaw_ae_minimum hθ,
    stableBridgeLaw_ae_continuousAt hθ ⟨1, zero_le_one, le_rfl⟩] with f he hm h1
  have hc := continuousAt_vervaatD he.1 h1 hm.2.2.2 hm.2.1 hm.2.2.1
  have hv := vervaatD_one_of_continuousAt hm.2.1.1 hm.2.2.1
  exact ⟨hc.2.1, by rw [hv.1, he.2.1, he.1, sub_zero], hv.2, hc.2.2⟩

/-- **Strict positivity of the Vervaat image.** Almost surely the Vervaat transform of the bridge
path is strictly positive on `(0, 1)` (the excursion property). -/
theorem stableBridgeLaw_ae_vervaatD_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)),
      ∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < vervaatD f t := sorry

end BGW.StableTrees
