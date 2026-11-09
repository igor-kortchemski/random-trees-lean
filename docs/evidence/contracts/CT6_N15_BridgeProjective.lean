import BGW.Skorokhod.PathLawFamily
import BGW.Skorokhod.Restrict
import BGW.Skorokhod.MeasurableLaws
import BGW.StableTrees.BridgePrefix
import BGW.StableTrees.StableProcessLaw
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Contract probe for CT.C6 blueprint Node 15 (projective bridge and terminal pinning), at the
abstract level of the audit (item 6): any family `P a` of stable Lévy laws on the compact horizons
`a < 1` gives, through the sealed N14 tilted prefix laws `bridgePrefixLaw` and the sealed N02
adapter (`exists_unique_compatiblePathLaw`) at the horizons `a_n = 1 - 2^{-(n+1)}`, a unique law
on the open-bridge carrier, and every such law has the terminal limit `0` almost surely. The
concrete instances `bridgeOpenLaw θ`, `closeBridge`, `stableBridgeLaw θ : ProbabilityMeasure
(D 1 ℝ)` follow (the blueprint defines `stableBridgeLaw` in N16; only its definition, the prefix
identity and the endpoint pinning are included here, since they are immediate from N15).
Bridge normalization: bridge from `0` to `0` on `[0, 1]` (weight `p_{1-a}(-f a) / p_1(0)`); NO
excursion normalization. Uniqueness, reversal, closed-law characterization and no fixed jumps are
N16 and are NOT stated.

The open carrier is the compatible-family subtype for the horizons `a_n` (internal to N02/N15,
not a public path space, audit correction 1); `openEval` totalizes it away from `[0,1)`.
Junk value: for `θ ∉ (1,2]` the open law is a Dirac mass at the zero compatible family.
Maintained file: `BGW/StableTrees/BridgeProjective.lean` (namespace `BGW.StableTrees`). -/

open MeasureTheory Set Filter Topology
open BGW.Skorokhod

namespace BGW.StableTrees

/-! ## Horizons and the open carrier -/

/-- The bridge prefix horizons `a_n = 1 - 2^{-(n+1)}`. -/
noncomputable def bridgeHorizon (n : ℕ) : ℝ := 1 - (1 / 2 : ℝ) ^ (n + 1)

theorem strictMono_bridgeHorizon : StrictMono bridgeHorizon := sorry

theorem bridgeHorizon_pos (n : ℕ) : 0 < bridgeHorizon n := sorry

theorem bridgeHorizon_lt_one (n : ℕ) : bridgeHorizon n < 1 := sorry

/-- Every time in `[0, 1)` lies below some horizon. -/
theorem exists_bridgeHorizon_ge {t : ℝ} (ht : t < 1) : ∃ n, t ≤ bridgeHorizon n := sorry

/-- The open-bridge carrier: compatible families of paths on `[0, a_n]`. Internal encoding of the
bridge construction: downstream results (closed-law characterization, reversal, minimum, Vervaat)
are stated on `D 1 ℝ` through `stableBridgeLaw`, not through `BridgeOpen`, `bridgeOpenLaw` or
`closeBridge`. -/
abbrev BridgeOpen : Type := CompatiblePaths bridgeHorizon strictMono_bridgeHorizon

open Classical in
/-- Totalized evaluation of an open bridge path: the value at `t ∈ [0, 1)` read in the first
coordinate whose horizon is at least `t`; `0` outside `[0, 1)`. -/
noncomputable def BridgeOpen.eval (f : BridgeOpen) (t : ℝ) : ℝ :=
  if h : 0 ≤ t ∧ ∃ n, t ≤ bridgeHorizon n then
    f.1 (Nat.find h.2) ⟨t, h.1, Nat.find_spec h.2⟩
  else 0

/-- Evaluation is read consistently in every coordinate whose horizon contains `t`. -/
theorem BridgeOpen.eval_eq_coord (f : BridgeOpen) (n : ℕ) (t : Set.Icc (0 : ℝ) (bridgeHorizon n)) :
    f.eval t = f.1 n t := sorry

theorem BridgeOpen.measurable_eval (t : ℝ) : Measurable (fun f : BridgeOpen => f.eval t) := sorry

/-- The terminal-limit event: `f(t) → 0` as `t ↑ 1` (full path limit, not convergence in
probability of `X_t`). -/
def BridgeOpen.terminalLimit : Set BridgeOpen :=
  {f | Tendsto f.eval (𝓝[<] (1 : ℝ)) (𝓝 0)}

theorem BridgeOpen.measurableSet_terminalLimit : MeasurableSet BridgeOpen.terminalLimit := sorry

/-! ## Abstract projective bridge -/

open Classical in
/-- The tilted prefix laws as probability measures on `D(a_n, ℝ)` (sealed N14: mass one). -/
noncomputable def bridgePrefixProb (θ : ℝ) (P : ∀ a : ℝ, ProbabilityMeasure (D a ℝ)) (n : ℕ) :
    ProbabilityMeasure (D (bridgeHorizon n) ℝ) :=
  if h : (1 < θ ∧ θ ≤ 2) ∧ IsStableLevyLaw θ (bridgeHorizon n) (P (bridgeHorizon n)) then
    ⟨bridgePrefixLaw θ (bridgeHorizon n) (bridgeHorizon_pos n).le
        (P (bridgeHorizon n) : Measure (D (bridgeHorizon n) ℝ)),
      isProbabilityMeasure_bridgePrefixLaw h.1 (bridgeHorizon_pos n) (bridgeHorizon_lt_one n) h.2⟩
  else P (bridgeHorizon n)

/-- Under the hypotheses, `bridgePrefixProb` is the sealed tilted prefix law. -/
theorem coe_bridgePrefixProb {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (P : ∀ a : ℝ, ProbabilityMeasure (D a ℝ))
    (hP : ∀ a, 0 < a → a < 1 → IsStableLevyLaw θ a (P a)) (n : ℕ) :
    (bridgePrefixProb θ P n : Measure (D (bridgeHorizon n) ℝ)) =
      bridgePrefixLaw θ (bridgeHorizon n) (bridgeHorizon_pos n).le
        (P (bridgeHorizon n) : Measure (D (bridgeHorizon n) ℝ)) := sorry

/-- The tilted prefixes are compatible (from N14 `bridgePrefix_consistent`). -/
theorem bridgePrefixProb_compatible {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (P : ∀ a : ℝ, ProbabilityMeasure (D a ℝ)) (hP : ∀ a, 0 < a → a < 1 → IsStableLevyLaw θ a (P a))
    (n : ℕ) :
    (bridgePrefixProb θ P (n + 1)).map
        (restrict (strictMono_bridgeHorizon.monotone (Nat.le_succ n))) =
      bridgePrefixProb θ P n := sorry

/-- **N15 (projective bridge, existence and uniqueness).** There is exactly one law on the open
bridge carrier whose `n`-th coordinate has the tilted law `w_{a_n} · P_{a_n}`. -/
theorem exists_unique_bridgeOpenLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (P : ∀ a : ℝ, ProbabilityMeasure (D a ℝ)) (hP : ∀ a, 0 < a → a < 1 → IsStableLevyLaw θ a (P a)) :
    ∃! Q : ProbabilityMeasure BridgeOpen,
      ∀ n, (Q : Measure BridgeOpen).map (CompatiblePaths.coord n) =
        bridgePrefixLaw θ (bridgeHorizon n) (bridgeHorizon_pos n).le
          (P (bridgeHorizon n) : Measure (D (bridgeHorizon n) ℝ)) := sorry

/-- **N15 (terminal pinning, abstract form).** Any law on the open carrier with the tilted prefix
marginals has full path limit `0` at the terminal time, almost surely. -/
theorem bridgeOpen_ae_terminal_limit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (P : ∀ a : ℝ, ProbabilityMeasure (D a ℝ)) (hP : ∀ a, 0 < a → a < 1 → IsStableLevyLaw θ a (P a))
    (Q : ProbabilityMeasure BridgeOpen)
    (hQ : ∀ n, (Q : Measure BridgeOpen).map (CompatiblePaths.coord n) =
      bridgePrefixLaw θ (bridgeHorizon n) (bridgeHorizon_pos n).le
        (P (bridgeHorizon n) : Measure (D (bridgeHorizon n) ℝ))) :
    ∀ᵐ f ∂(Q : Measure BridgeOpen), Tendsto f.eval (𝓝[<] (1 : ℝ)) (𝓝 0) := sorry

/-! ## The stable instance -/

/-- Zero open path (junk). -/
def BridgeOpen.zero : BridgeOpen := ⟨fun _ => ⟨fun _ => 0, IsCadlag.const⟩, fun _ => rfl⟩

/-- **The open stable bridge law.** The `exists_unique_bridgeOpenLaw` witness for
`P = stableProcessLaw θ`; junk value (Dirac at the zero family) for `θ ∉ (1,2]`. -/
noncomputable def bridgeOpenLaw (θ : ℝ) : ProbabilityMeasure BridgeOpen :=
  if hθ : 1 < θ ∧ θ ≤ 2 then
    Classical.choose (exists_unique_bridgeOpenLaw hθ (fun a => stableProcessLaw θ a)
      (fun _ ha _ => isStableLevyLaw_stableProcessLaw hθ ha)).exists
  else ⟨Measure.dirac BridgeOpen.zero, inferInstance⟩

/-- Prefix characterization of the open stable bridge. -/
theorem map_coord_bridgeOpenLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (n : ℕ) :
    (bridgeOpenLaw θ : Measure BridgeOpen).map (CompatiblePaths.coord n) =
      bridgePrefixLaw θ (bridgeHorizon n) (bridgeHorizon_pos n).le
        (stableProcessLaw θ (bridgeHorizon n) : Measure (D (bridgeHorizon n) ℝ)) := sorry

/-- Uniqueness of the open stable bridge law by its prefixes. -/
theorem eq_bridgeOpenLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {Q : ProbabilityMeasure BridgeOpen}
    (hQ : ∀ n, (Q : Measure BridgeOpen).map (CompatiblePaths.coord n) =
      bridgePrefixLaw θ (bridgeHorizon n) (bridgeHorizon_pos n).le
        (stableProcessLaw θ (bridgeHorizon n) : Measure (D (bridgeHorizon n) ℝ))) :
    Q = bridgeOpenLaw θ := sorry

/-- **N15 (terminal pinning, stable instance).** -/
theorem bridgeOpenLaw_ae_terminal_limit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(bridgeOpenLaw θ : Measure BridgeOpen), Tendsto f.eval (𝓝[<] (1 : ℝ)) (𝓝 0) := sorry

/-- On the terminal-limit event, extending an open path by `0` at time `1` gives a càdlàg path on
`[0, 1]`. -/
theorem isCadlag_closeFun {f : BridgeOpen} (h : f ∈ BridgeOpen.terminalLimit) :
    IsCadlag (fun t : Set.Icc (0 : ℝ) 1 => if (t : ℝ) < 1 then f.eval t else 0) := sorry

open Classical in
/-- Closing the bridge: extend an open path by the value `0` at time `1` on the terminal-limit
event; the zero path on its complement. -/
noncomputable def closeBridge (f : BridgeOpen) : D 1 ℝ :=
  if h : f ∈ BridgeOpen.terminalLimit then
    ⟨fun t => if (t : ℝ) < 1 then f.eval t else 0, isCadlag_closeFun h⟩
  else ⟨fun _ => 0, IsCadlag.const⟩

/-- Closing is measurable (D 1 ℝ carries its Borel σ-algebra, generated by evaluations). -/
theorem measurable_closeBridge : Measurable closeBridge := sorry

/-- On the terminal-limit event, the closed path restricts to the `n`-th coordinate. -/
theorem restrict_closeBridge {f : BridgeOpen} (hf : f ∈ BridgeOpen.terminalLimit) (n : ℕ) :
    restrict (bridgeHorizon_lt_one n).le (closeBridge f) = f.1 n := sorry

/-- **The stable bridge law on `D 1 ℝ`** (bridge from `0` to `0`): image of the open law under
`closeBridge`. Junk value: image of the junk open law (a Dirac mass at the zero path). -/
noncomputable def stableBridgeLaw (θ : ℝ) : ProbabilityMeasure (D 1 ℝ) :=
  (bridgeOpenLaw θ).map closeBridge

/-- Prefix identity: for `0 < a < 1`, the restriction to `[0, a]` is the tilted stable law
`w_a · P_a` (N14's `bridgePrefixLaw`, i.e. `withDensity` of `bridgePrefixWeight`). -/
theorem map_restrict_stableBridgeLaw {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 < a) (ha1 : a < 1) :
    (stableBridgeLaw θ : Measure (D 1 ℝ)).map (restrict ha1.le) =
      bridgePrefixLaw θ a ha.le (stableProcessLaw θ a : Measure (D a ℝ)) := sorry

/-- **Terminal pinning** (and start): almost surely `X_0 = 0`, `X_1 = 0` and `X_{1-} = 0`. -/
theorem stableBridgeLaw_endpoints {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)),
      f ⟨0, le_rfl, zero_le_one⟩ = 0 ∧ f ⟨1, zero_le_one, le_rfl⟩ = 0 ∧
        Function.leftLim f ⟨1, zero_le_one, le_rfl⟩ = 0 := sorry

end BGW.StableTrees
