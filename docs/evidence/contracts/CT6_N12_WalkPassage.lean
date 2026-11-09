import BGW.Skorokhod.DLoc
import BGW.Skorokhod.ExitPartition
import BGW.Probability.RealWalk
import BGW.StableTrees.Defs
import BGW.StableTrees.RealAttraction
import BGW.StableTrees.StableProcessLaw
import BGW.StableTrees.StableLocalLaw
import BGW.StableTrees.StableFirstPassage
import BGW.StableTrees.Scalar.ForestWalkBridge
import BGW.Tree.ForestCycle

/-! Contract probe for CT.C6 blueprint Node 12: first passage of the canonical walk below
`-ℓ_n`, divided by `n`, converges in law to the stable passage time `T_x` (F3/F4 input).

AUDIT item 5 is followed: NO dependency on N11. The atom-free statement `runningInf_noAtoms`
uses only that `X_0 = 0`, right-continuity, independence of the stable increment `X_a` (which
has a density) from the future, and N06 regularity at the single level `c = 0`.

Sealed inputs reused (not re-declared): `StableDomain` (`Defs`), `StableDomain.tendsto_stepPathLaw`
(CT5 FCLT, fixed horizon `T`), `BGW.forestWeight`, `BGW.IsForestCode`, `BGW.firstPassageWords`,
`BGW.StableTrees.Scalar.forestWeight_toReal_eq` (Kemperman), `firstPassageBelow`, `runningInfLoc`,
`ae_firstPassageBelow_spec`, `integral_exp_neg_strictPassageBelow` (N08), `realStepPath`,
`iidLaw`, `realOffspringStepLaw`.

Conventions.
* The canonical walk is `w ↦ partialSum w k` under `iidLaw (realOffspringStepLaw μ)`, i.e.
  `S_k = Σ_{i<k} (K_i - 1)`; steps are `≥ -1` a.s. (support of `μ`), hence downward
  skip-free. `walkHitTime ℓ w = inf{k | S_k ≤ -ℓ}` is the WEAK first hit (`ℕ∞`, `⊤` if never);
  a.s. `S = -ℓ` there. The limit `T_x = inf{t | X_t < -x}` is the STRICT passage time: the
  weak/strict mismatch is resolved by atom-freeness of the limiting running infimum
  (`runningInf_noAtoms`, `passageLaw_Iic_eq_runningInf`), never by continuity of the hitting map.
* Time scale: `n` steps per unit time, space scale `B n` (the `StableDomain` normalizer), so
  `walkHitTime (ℓ n) / n` is compared to `T_x` when `ℓ n / B n → x > 0`. No lattice factor appears.
* `walkPassageLaw μ ℓ n` is a measure on `ℝ`; it is the law of `(walkHitTime ℓ w).toNat / n`
  (junk `0` on `{hit = ⊤}`, which is null for `StableDomain`: `ae_walkHitTime_ne_top`).
  Convergence in law is stated through bounded continuous tests (the limit is the real
  `passageLaw θ x`).
* `x > 0` is essential: `x = 0` would need `ℓ_n = o(B n)`, mass escapes to `0`; `ℓ n ≥ 1` is
  needed for `forestWeight` (a forest of `0` trees has size `0`).
Maintained file: a new `BGW/StableTrees/StableWalkPassage.lean`. Estimate 500–900 lines. -/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open BGW.Skorokhod BGW.StableTrees BGW.Probability.RealWalk

namespace BGW.StableTrees

-- copied from contract CT6_N09_PassageSubordinator (not part of this contract)
/-- The `ℝ≥0`-valued passage time (junk value `0` on `{T_x = ⊤}`, a null set). -/
noncomputable def passageTime (x : ℝ≥0) (f : DLoc) : ℝ≥0 := (firstPassageBelow x f).untopD 0

-- copied from contract CT6_N09_PassageSubordinator (not part of this contract)
/-- The law of the passage time `T_x` under the local stable law, on `ℝ`. -/
noncomputable def passageLaw (θ : ℝ) (x : ℝ≥0) : Measure ℝ :=
  Measure.map (fun f : DLoc => ((passageTime x f : ℝ≥0) : ℝ)) (stableLocalLaw θ : Measure DLoc)

/-- `passageLaw θ x` is a probability measure (copied from N09). -/
theorem passageLaw_isProbabilityMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0) :
    IsProbabilityMeasure (passageLaw θ x) := sorry

/-! ### The canonical walk and its (weak) first hit -/

/-- The first (weak) hit of `(-∞, -ℓ]` by the walk `k ↦ partialSum w k`; `⊤` if never. -/
noncomputable def walkHitTime (ℓ : ℕ) (w : ℕ → ℝ) : ℕ∞ :=
  ⨅ k ∈ {k : ℕ | partialSum w k ≤ -(ℓ : ℝ)}, (k : ℕ∞)

/-- The law of `walkHitTime ℓ / n` for the canonical offspring walk (finite reading). -/
noncomputable def walkPassageLaw (μ : PMF ℕ) (ℓ n : ℕ) : Measure ℝ :=
  Measure.map (fun w : ℕ → ℝ => (((walkHitTime ℓ w).toNat : ℝ)) / n)
    (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ))

theorem measurable_walkHitTime (ℓ : ℕ) : Measurable (walkHitTime ℓ) := sorry

/-- Almost surely the canonical walk is downward skip-free: every step is an integer `≥ -1`. -/
theorem ae_step_ge_neg_one (μ : PMF ℕ) :
    ∀ᵐ w ∂(iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)), ∀ i : ℕ, ∃ k : ℕ, w i = (k : ℝ) - 1 :=
  sorry

/-- Weak hit is exact hit: a.s., if the walk ever reaches `(-∞, -ℓ]` it equals `-ℓ` there. -/
theorem ae_partialSum_walkHitTime {μ : PMF ℕ} (ℓ : ℕ) :
    ∀ᵐ w ∂(iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)), ∀ k : ℕ,
      walkHitTime ℓ w = (k : ℕ∞) → partialSum w k = -(ℓ : ℝ) := sorry

/-- `walkPassageLaw` is a probability measure when the hit is a.s. finite. -/
theorem walkPassageLaw_isProbabilityMeasure {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (ℓ n : ℕ) : IsProbabilityMeasure (walkPassageLaw μ ℓ n) := sorry

/-- The critical, nondegenerate offspring walk hits every level `-ℓ` a.s. -/
theorem ae_walkHitTime_ne_top {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B) (ℓ : ℕ) :
    ∀ᵐ w ∂(iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)), walkHitTime ℓ w ≠ ⊤ := sorry

/-! ### Identification with `forestWeight` (Kemperman) -/

/-- **First-hit mass is the forest weight.** For `ℓ ≥ 1`, `P(first hit of `-ℓ` at time `q`)` equals
`forestWeight μ ℓ q` (via `IsForestCode`, `firstPassageWords`; the support condition `K ≥ 0`, i.e.
steps `≥ -1`, is used, since `walkWeight` of an arbitrary integer word does not encode `μ`). -/
theorem walkHitTime_mass_eq_forestWeight (μ : PMF ℕ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (q : ℕ) :
    (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)) {w | walkHitTime ℓ w = (q : ℕ∞)} =
      BGW.forestWeight μ ℓ q := sorry

/-- **Kemperman for the first-hit mass.** For `ℓ ≥ 1`, `q ≥ 1`: `P(hit = q) = (ℓ / q) P(S_q = -ℓ)`,
with the integer walk point probability `walkProb`. -/
theorem walkHitTime_mass_toReal {μ : PMF ℕ} {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {q : ℕ} (hq : 1 ≤ q) :
    ((iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)).real {w | walkHitTime ℓ w = (q : ℕ∞)}) =
      ℓ / q * walkProb μ q (-(ℓ : ℤ)) := sorry

/-- The masses of the hitting times add up to `1` (a.s. finite hit), as `tsum` over `q`. -/
theorem tsum_walkHitTime_mass {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) : ∑' q : ℕ, BGW.forestWeight μ ℓ q = 1 := sorry

/-- **Weak hit versus running minimum of the step path** (deterministic, no limit): for `b > 0`,
`walkHitTime ℓ ≤ ⌊n t⌋ ↔ inf_{s ≤ t} realStepPath ≤ -ℓ/b`. The infimum over `[0, t]` of the
step path is a minimum over `j ≤ ⌊n t⌋`, so the WEAK inequality `≤ -ℓ/b` is exact. -/
theorem walkHitTime_le_iff_iInf_stepPath_le {ℓ n : ℕ} {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (w : ℕ → ℝ) :
    walkHitTime ℓ w ≤ ((⌊(n : ℝ) * t⌋₊ : ℕ) : ℕ∞) ↔
      (⨅ s : Set.Icc (0 : ℝ) t, realStepPath t n b w s) ≤ -(ℓ : ℝ) / b := sorry

/-! ### The limit: atom-free running infimum and passage-law CDF -/

/-- **`runningInf_noAtoms`** (the public lemma the blueprint mentions): for `t > 0` the running
infimum `I_t = inf_{u ≤ t} X_u` has no atoms. For `c > 0` this is empty (`I_t ≤ X_0 = 0`); for
`c = 0` it is N06 regularity; for `c < 0`, `I_t = inf_{[a,t]} X` for some rational `a > 0` and
`X_a + inf_u (X_{a+u} - X_a)` is a sum with an independent atom-free (density) first term. -/
theorem runningInf_noAtoms {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0} (ht : 0 < t) (c : ℝ) :
    (stableLocalLaw θ : Measure DLoc) {f | runningInfLoc f t = c} = 0 := sorry

/-- The fixed-horizon form on `D T ℝ`, the one consumed with `StableDomain.tendsto_stepPathLaw`:
the law of `inf_{s ≤ T} g s` under `stableProcessLaw θ T` has no atoms. -/
theorem iInf_noAtoms_stableProcessLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {T : ℝ} (hT : 0 < T) (c : ℝ) :
    (stableProcessLaw θ T : Measure (D T ℝ)) {g | (⨅ s : Set.Icc (0 : ℝ) T, g s) = c} = 0 := sorry

/-- **CDF of the passage time through the running infimum** (strict vs weak resolved by
`runningInf_noAtoms`): for `x ≥ 0`, `t > 0`,
`P(T_x ≤ t) = P(I_t ≤ -x) = P(I_t < -x)`. -/
theorem passageLaw_Iic_eq_runningInf {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0) {t : ℝ≥0}
    (ht : 0 < t) :
    passageLaw θ x (Iic (t : ℝ)) =
        (stableLocalLaw θ : Measure DLoc) {f | runningInfLoc f t ≤ -(x : ℝ)} ∧
      (stableLocalLaw θ : Measure DLoc) {f | runningInfLoc f t ≤ -(x : ℝ)} =
        (stableLocalLaw θ : Measure DLoc) {f | runningInfLoc f t < -(x : ℝ)} := sorry

/-- **N12 (blueprint `tendsto_walkPassageLaw`).** For a `StableDomain μ θ B` witness, integers
`ℓ n ≥ 1` eventually, and `ℓ n / B n → x > 0`: `walkHitTime (ℓ n) / n ⟹ T_x` in law. Stated for
bounded continuous test functions on `ℝ` (all measures involved are probability measures). -/
theorem tendsto_walkPassageLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {x : ℝ≥0} (hx : 0 < x) {ℓ : ℕ → ℕ} (hℓ : ∀ᶠ n in atTop, 1 ≤ ℓ n)
    (hscale : Tendsto (fun n : ℕ => (ℓ n : ℝ) / B n) atTop (𝓝 (x : ℝ))) :
    ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ => ∫ t, f t ∂(walkPassageLaw μ (ℓ n) n)) atTop
        (𝓝 (∫ t, f t ∂(passageLaw θ x))) := sorry

end BGW.StableTrees
