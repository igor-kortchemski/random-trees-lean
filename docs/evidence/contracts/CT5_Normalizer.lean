import BGW.StableTrees.Attraction.Defs
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Group.Convolution

/-! Contract probe for CT.C16/C17 route, blueprint Node 4 with audit correction 1: the real
attraction predicate with EVENTUAL positivity of the normalizer, invariance under eventual
equality of normalizers, the moving-argument characteristic-function lemma, the ratio theorem
`B_{m_j} / B_{q_j} → c^{1/θ}` without monotonicity, and the bridges from the existing integer
`IsStableAttracted ν θ 0 B` and from `StableDomain`. No centering is ever added.
Maintained file: `BGW/StableTrees/RealAttraction.lean`. -/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-! ## Copied declarations (not part of this contract) -/

namespace BGW.Probability.RealWalk

-- copied from contract CT5_RealWalk (not part of this contract)
def partialSum (ω : ℕ → ℝ) (m : ℕ) : ℝ := ∑ i ∈ Finset.range m, ω i

-- copied from contract CT5_RealWalk (not part of this contract)
noncomputable def iidLaw (ν : ProbabilityMeasure ℝ) : ProbabilityMeasure (ℕ → ℝ) :=
  ⟨Measure.infinitePi (fun _ : ℕ => (ν : Measure ℝ)), inferInstance⟩

-- copied from contract CT5_RealWalk (not part of this contract)
noncomputable def sumLaw (ν : ProbabilityMeasure ℝ) (m : ℕ) : ProbabilityMeasure ℝ :=
  (iidLaw ν).map (fun ω : ℕ → ℝ => partialSum ω m)

-- copied from contract CT5_RealWalk (not part of this contract)
noncomputable def scaledSumLaw (ν : ProbabilityMeasure ℝ) (B : ℕ → ℝ) (m : ℕ) :
    ProbabilityMeasure ℝ :=
  (sumLaw ν m).map (fun x : ℝ => x / B m)

-- copied from contract CT5_RealWalk (not part of this contract)
theorem charFun_sumLaw (ν : ProbabilityMeasure ℝ) (m : ℕ) (u : ℝ) :
    charFun (sumLaw ν m : Measure ℝ) u = charFun (ν : Measure ℝ) u ^ m := sorry

-- copied from contract CT5_RealWalk (not part of this contract)
theorem charFun_scaledSumLaw (ν : ProbabilityMeasure ℝ) (B : ℕ → ℝ) (m : ℕ) (u : ℝ) :
    charFun (scaledSumLaw ν B m : Measure ℝ) u = charFun (ν : Measure ℝ) (u / B m) ^ m := sorry

-- copied from contract CT5_RealWalk (not part of this contract)
theorem sumLaw_add (ν : ProbabilityMeasure ℝ) (m k : ℕ) :
    (sumLaw ν (m + k) : Measure ℝ) = (sumLaw ν m : Measure ℝ) ∗ (sumLaw ν k : Measure ℝ) := sorry

end BGW.Probability.RealWalk

namespace BGW.StableTrees

open BGW.Probability.RealWalk

-- copied from contract CT4_StableLaw (not part of this contract)
noncomputable def stableLaw (θ : ℝ) : ProbabilityMeasure ℝ :=
  if hθ : 1 < θ ∧ θ ≤ 2 then
    ⟨volume.withDensity (fun x => ENNReal.ofReal (Scalar.stableDensity θ x)), sorry⟩
  else ⟨Measure.dirac 0, inferInstance⟩

-- copied from contract CT4_StableLaw (not part of this contract)
theorem eq_stableLaw_of_laplace {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ν : Measure ℝ}
    [IsProbabilityMeasure ν]
    (hL : ∀ lam : ℝ, 0 < lam → ∫ y, Real.exp (-lam * y) ∂ν = Real.exp (lam ^ θ)) :
    ν = (stableLaw θ : Measure ℝ) := sorry

-- copied from contract CT4_StableLaw (not part of this contract)
theorem charFun_stableLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ) :
    charFun (stableLaw θ : Measure ℝ) t = Scalar.stableCF θ t := sorry

/-! ## The contract -/

/-- Real scalar attraction (audit correction 1): `B n > 0` only eventually; no monotonicity, no
centering, no integrability. -/
structure IsRealStableAttracted (ν : ProbabilityMeasure ℝ) (θ : ℝ) (B : ℕ → ℝ) : Prop where
  index_mem : 1 < θ ∧ θ ≤ 2
  pos : ∀ᶠ n in atTop, 0 < B n
  converges : Tendsto (fun n => scaledSumLaw ν B n) atTop (𝓝 (stableLaw θ))

/-- (a) Invariance under eventual equality of normalizers. -/
theorem IsRealStableAttracted.congr_eventually {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B B' : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) (hBB' : ∀ᶠ n in atTop, B n = B' n) :
    IsRealStableAttracted ν θ B' := sorry

/-- Moving-argument characteristic-function convergence (Node 4): along `m j → ∞` and
`u j → u₀`, `φ_ν (u j / B (m j)) ^ (m j) → φ_{stableLaw θ} u₀`. -/
theorem IsRealStableAttracted.tendsto_charFun_pow_moving {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {m : ℕ → ℕ}
    (hm : Tendsto m atTop atTop) {u : ℕ → ℝ} {u₀ : ℝ} (hu : Tendsto u atTop (𝓝 u₀)) :
    Tendsto (fun j => charFun (ν : Measure ℝ) (u j / B (m j)) ^ m j) atTop
      (𝓝 (charFun (stableLaw θ : Measure ℝ) u₀)) := sorry

/-- The ratio theorem (Node 4): no monotonicity, no lattice, no criticality. -/
theorem IsRealStableAttracted.tendsto_norming_ratio {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {m q : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hq : Tendsto q atTop atTop)
    (hmq : Tendsto (fun j => (m j : ℝ) / q j) atTop (𝓝 c)) :
    Tendsto (fun j => B (m j) / B (q j)) atTop (𝓝 (c ^ (1 / θ))) := sorry

/-! ### Bridge from the integer predicate -/

/-- The cast pushforward of an integer step law to `ℝ`. -/
noncomputable def castLaw (ν : Measure ℤ) [IsProbabilityMeasure ν] : ProbabilityMeasure ℝ :=
  ⟨ν.map (fun z : ℤ => (z : ℝ)), inferInstance⟩

/-- The real sum law of cast integer steps is the cast of the integer walk law. -/
theorem sumLaw_castLaw (ν : Measure ℤ) [IsProbabilityMeasure ν] (n : ℕ) :
    (sumLaw (castLaw ν) n : Measure ℝ) =
      (Attraction.intWalk ν n).map (fun z : ℤ => (z : ℝ)) := sorry

/-- (b) The existing integer attraction predicate (`Attraction/Defs.lean`, centering `0`)
implies the real one for the cast step law, with the same normalizer; uses
`eq_stableLaw_of_laplace` to identify the limit. -/
theorem Attraction.IsStableAttracted.isRealStableAttracted {ν : Measure ℤ}
    [IsProbabilityMeasure ν] {θ : ℝ} {B : ℕ → ℝ}
    (h : Attraction.IsStableAttracted ν θ 0 B) :
    IsRealStableAttracted (castLaw ν) θ B := sorry

/-- The real offspring step law `K - 1`, as a cast of `stepLaw μ`. -/
noncomputable def realOffspringStepLaw (μ : PMF ℕ) : ProbabilityMeasure ℝ :=
  castLaw (stepLaw μ)

/-- (c) Offspring bridge, through `stableDomain_isStableAttracted` and (b). -/
theorem StableDomain.isRealStableAttracted {μ : PMF ℕ} {θ : ℝ} {a : ℕ → ℝ}
    (h : StableDomain μ θ a) : IsRealStableAttracted (realOffspringStepLaw μ) θ a := sorry

end BGW.StableTrees
