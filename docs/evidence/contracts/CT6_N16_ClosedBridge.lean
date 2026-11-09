import BGW.Skorokhod.MeasurableMaps
import BGW.Skorokhod.ReverseIncrements
import BGW.StableTrees.BridgeProjective
import BGW.StableTrees.StableProcessReversal

/-! Contract probe for CT.C6 blueprint Node 16 (closed bridge law, uniqueness, reversal, no fixed
discontinuities), on the closed path space `D 1 ℝ`.

Sealed inputs reused, NOT re-declared here (see `BGW/StableTrees/BridgeProjective.lean`):
`stableBridgeLaw θ : ProbabilityMeasure (D 1 ℝ)`, the prefix identity
`map_restrict_stableBridgeLaw : (stableBridgeLaw θ).map (restrict ha1.le) =
bridgePrefixLaw θ a ha.le (stableProcessLaw θ a)` (with `bridgePrefixLaw = withDensity` of
`ofReal ∘ bridgePrefixWeight`) and `stableBridgeLaw_endpoints`
(`f 0 = 0 ∧ f 1 = 0 ∧ leftLim f 1 = 0` almost surely). `BridgeOpen`, `bridgeOpenLaw`,
`closeBridge` do not occur in any statement below (AUDIT item 1).

New exports: (1) bounded-prefix expectation formulas; (2) characterization/uniqueness of
`stableBridgeLaw θ` by its prefix laws together with the endpoint condition; (3) the bridge
reversal `f ↦ (s ↦ -f((1-s)-))` as a totalized map `D 1 ℝ → D 1 ℝ` (càdlàg lemma and
measurability separate) and invariance of the bridge law; (4) no fixed discontinuities, including
the times `0` and `1`.

Conventions. Every theorem about the law carries `1 < θ ∧ θ ≤ 2` (junk branch: the law is the Dirac
mass at the zero path). Fixed times are `Set.Icc (0 : ℝ) 1` points. The left limit at `0` is the
value (Mathlib `leftLim` convention on the bottom point), so `reverseBridge f 1 = -f 0`.
Uniqueness WITHOUT an endpoint condition is false: the prefix laws on `[0, a]`, `a < 1`, say
nothing about the value at time `1`. Fixed-time a.s. continuity does not say the bridge is a
continuous path (it jumps).
Maintained file: a new `BGW/StableTrees/StableBridgeClosed.lean` (namespace `BGW.StableTrees`). -/

open MeasureTheory Set Filter Topology
open scoped ENNReal
open BGW.Skorokhod

namespace BGW.Skorokhod

/-- The bridge reversal function `s ↦ -f((1-s)-)`, defined on every path of `D 1 ℝ` (with
`f(0-) = f 0`). On paths with `f 1 = 0` it agrees with `reverseIncrementsFun` at `T = 1`; it
preserves positive jumps (the sign flips together with the time). -/
noncomputable def reverseBridgeFun (f : D 1 ℝ) : Set.Icc (0 : ℝ) 1 → ℝ :=
  fun s => -Function.leftLim f ⟨1 - s, by linarith [s.2.2], by linarith [s.2.1]⟩

/-- The reversed function is càdlàg, including at both endpoints. -/
theorem isCadlag_reverseBridgeFun (f : D 1 ℝ) : IsCadlag (reverseBridgeFun f) := sorry

/-- The bridge reversal as a totalized map on `D 1 ℝ`. -/
noncomputable def reverseBridge (f : D 1 ℝ) : D 1 ℝ :=
  ⟨reverseBridgeFun f, isCadlag_reverseBridgeFun f⟩

/-- Pointwise formula (definitional). -/
theorem reverseBridge_apply (f : D 1 ℝ) (s : Set.Icc (0 : ℝ) 1) :
    reverseBridge f s =
      -Function.leftLim f ⟨1 - s, by linarith [s.2.2], by linarith [s.2.1]⟩ := sorry

/-- Agreement with the increment reversal on paths ending at `0`. -/
theorem reverseBridge_eq_reverseIncrements {f : D 1 ℝ} (hf : f ⟨1, zero_le_one, le_rfl⟩ = 0) :
    reverseBridge f = reverseIncrements zero_le_one f := sorry

/-- `reverseBridge` is Borel measurable. -/
theorem measurable_reverseBridge : Measurable reverseBridge := sorry

end BGW.Skorokhod

namespace BGW.StableTrees

/-! ### Bounded-prefix expectation formulas -/

/-- **Prefix expectation.** For `0 < a < 1` and bounded Borel `F` on `D a ℝ`:
`E_bridge[F(f|[0,a])] = E_{P_a}[w_a · F]`. The integrand on the right lives on `D a ℝ` (it is not
another restriction from `D 1 ℝ`). -/
theorem integral_restrict_stableBridgeLaw {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 < a)
    (ha1 : a < 1) {F : D a ℝ → ℝ} (hF : Measurable F) (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    ∫ f, F (restrict (E := ℝ) ha1.le f) ∂(stableBridgeLaw θ : Measure (D 1 ℝ)) =
      ∫ g, bridgePrefixWeight θ a ha.le g * F g ∂(stableProcessLaw θ a : Measure (D a ℝ)) :=
  sorry

/-- Prefix probabilities: for measurable `B ⊆ D a ℝ`,
`P_bridge(f|[0,a] ∈ B) = ∫_B w_a dP_a`. -/
theorem measure_restrict_preimage_stableBridgeLaw {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 < a)
    (ha1 : a < 1) {B : Set (D a ℝ)} (hB : MeasurableSet B) :
    (stableBridgeLaw θ : Measure (D 1 ℝ)) (restrict (E := ℝ) ha1.le ⁻¹' B) =
      ∫⁻ g in B, ENNReal.ofReal (bridgePrefixWeight θ a ha.le g)
        ∂(stableProcessLaw θ a : Measure (D a ℝ)) := sorry

/-- Strict prefixes of the bridge are absolutely continuous with respect to the stable law. -/
theorem map_restrict_stableBridgeLaw_absolutelyContinuous {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (ha : 0 < a) (ha1 : a < 1) :
    (stableBridgeLaw θ : Measure (D 1 ℝ)).map (restrict (E := ℝ) ha1.le) ≪
      (stableProcessLaw θ a : Measure (D a ℝ)) := sorry

/-- The prefix weight integrates to one against `P_a` (mass one of the tilted prefix law). -/
theorem integral_bridgePrefixWeight_stableProcessLaw {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (ha : 0 < a) (ha1 : a < 1) :
    ∫ g, bridgePrefixWeight θ a ha.le g ∂(stableProcessLaw θ a : Measure (D a ℝ)) = 1 := sorry

/-! ### Uniqueness (closed law, prefix laws plus endpoint conditions) -/

/-- **Uniqueness, minimal endpoint form.** A law on `D 1 ℝ` with the prescribed prefix laws on
every `[0, a]`, `a < 1`, and which a.s. has no jump at time `1` (`f 1 = f 1-`), is the stable
bridge. (The prefix laws force `f 1- = 0` a.s.) -/
theorem stableBridgeLaw_unique {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {Q : ProbabilityMeasure (D 1 ℝ)}
    (hprefix : ∀ a : ℝ, ∀ ha : 0 < a, ∀ ha1 : a < 1,
      (Q : Measure (D 1 ℝ)).map (restrict (E := ℝ) ha1.le) =
        bridgePrefixLaw θ a ha.le (stableProcessLaw θ a : Measure (D a ℝ)))
    (hend : ∀ᵐ f : D 1 ℝ ∂(Q : Measure (D 1 ℝ)),
      f ⟨1, zero_le_one, le_rfl⟩ = Function.leftLim f ⟨1, zero_le_one, le_rfl⟩) :
    Q = stableBridgeLaw θ := sorry

/-- **Uniqueness, pinned form** (the form with the endpoint conditions of
`stableBridgeLaw_endpoints`, as recommended by GPT-Sol): prefix laws plus
`f 1 = 0 ∧ f 1- = 0` almost surely. -/
theorem stableBridgeLaw_unique_of_endpoints {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {Q : ProbabilityMeasure (D 1 ℝ)}
    (hprefix : ∀ a : ℝ, ∀ ha : 0 < a, ∀ ha1 : a < 1,
      (Q : Measure (D 1 ℝ)).map (restrict (E := ℝ) ha1.le) =
        bridgePrefixLaw θ a ha.le (stableProcessLaw θ a : Measure (D a ℝ)))
    (hend : ∀ᵐ f : D 1 ℝ ∂(Q : Measure (D 1 ℝ)),
      f ⟨1, zero_le_one, le_rfl⟩ = 0 ∧ Function.leftLim f ⟨1, zero_le_one, le_rfl⟩ = 0) :
    Q = stableBridgeLaw θ := sorry

/-- **Characterization.** `Q` is the stable bridge law iff it has the tilted prefix laws and is a.s.
pinned at time `1`. -/
theorem eq_stableBridgeLaw_iff {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {Q : ProbabilityMeasure (D 1 ℝ)} :
    Q = stableBridgeLaw θ ↔
      ((∀ a : ℝ, ∀ ha : 0 < a, ∀ ha1 : a < 1,
        (Q : Measure (D 1 ℝ)).map (restrict (E := ℝ) ha1.le) =
          bridgePrefixLaw θ a ha.le (stableProcessLaw θ a : Measure (D a ℝ))) ∧
      ∀ᵐ f : D 1 ℝ ∂(Q : Measure (D 1 ℝ)),
        f ⟨1, zero_le_one, le_rfl⟩ = 0 ∧ Function.leftLim f ⟨1, zero_le_one, le_rfl⟩ = 0) :=
  sorry

/-- Prefix laws alone do not determine the law: the value at time `1` is free. This is the
necessity of the endpoint hypothesis (a concrete second law with the same prefixes: the bridge
with its terminal value overwritten by `1`). -/
theorem exists_ne_stableBridgeLaw_same_prefixes {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ Q : ProbabilityMeasure (D 1 ℝ), Q ≠ stableBridgeLaw θ ∧
      ∀ a : ℝ, ∀ ha : 0 < a, ∀ ha1 : a < 1,
        (Q : Measure (D 1 ℝ)).map (restrict (E := ℝ) ha1.le) =
          bridgePrefixLaw θ a ha.le (stableProcessLaw θ a : Measure (D a ℝ)) := sorry

/-! ### Reversal -/

/-- **Reversal invariance.** `(stableBridgeLaw θ).map reverseBridge = stableBridgeLaw θ`. -/
theorem map_reverseBridge_stableBridgeLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (stableBridgeLaw θ : Measure (D 1 ℝ)).map reverseBridge =
      (stableBridgeLaw θ : Measure (D 1 ℝ)) := sorry

/-- Almost surely the reversed path is the increment reversal of the original (the reversal of
the bridge is the reversal of increments on `{f 1 = 0}`). -/
theorem ae_reverseBridge_eq_reverseIncrements {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)),
      reverseBridge f = reverseIncrements zero_le_one f := sorry

/-- Almost surely the reversal is an involution on the bridge (the totalized map is NOT an
involution on arbitrary paths with endpoint jumps, so this is stated a.s. only). -/
theorem ae_reverseBridge_reverseBridge {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)), reverseBridge (reverseBridge f) = f := sorry

/-- The reversed bridge is again a pinned bridge: almost surely it starts and ends at `0` and has
no left jump at `1`. -/
theorem ae_endpoints_reverseBridge {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)),
      reverseBridge f ⟨0, le_rfl, zero_le_one⟩ = 0 ∧
        reverseBridge f ⟨1, zero_le_one, le_rfl⟩ = 0 ∧
        Function.leftLim (reverseBridge f) ⟨1, zero_le_one, le_rfl⟩ = 0 := sorry

/-! ### No fixed discontinuities -/

/-- **No fixed discontinuities.** At every fixed time `t ∈ [0, 1]` (including `0` and `1`) the
bridge is almost surely continuous. -/
theorem stableBridgeLaw_ae_continuousAt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : Set.Icc (0 : ℝ) 1) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)), ContinuousAt f t := sorry

/-- Fixed-time left limit equals the value, almost surely (equivalent form, quantified over
all fixed times at once is not claimed). -/
theorem stableBridgeLaw_ae_leftLim_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : Set.Icc (0 : ℝ) 1) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)), Function.leftLim f t = f t := sorry

end BGW.StableTrees
