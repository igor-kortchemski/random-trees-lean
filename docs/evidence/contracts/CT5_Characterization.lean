import BGW.Skorokhod.Measurable
import BGW.StableTrees.Scalar.DensityLaw
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Group.Convolution

/-! Contract probe for CT.C16 characterization (blueprint Nodes 12 (definition), 13, 14
(uniqueness), 16 and 17 in their "any `P` with `IsStableLevyLaw`" forms, audit corrections 5
and 7). No existence statement here. Maintained file: `BGW/StableTrees/StableLevyLaw.lean`
(namespace `BGW.StableTrees`). -/

open MeasureTheory Filter Set
open scoped Topology

/-! ## Copied declarations (not part of this contract) -/

namespace BGW.Skorokhod

-- copied from contract CT2_PathSpace (not part of this contract)
theorem ext_of_finiteDimensional {T : ℝ} {E : Type*} [MetricSpace E]
    [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E] {P Q : ProbabilityMeasure (D T E)}
    {S : Set (Set.Icc (0 : ℝ) T)} (hS : Dense S) (hT0 : 0 ≤ T)
    (hTS : (⟨T, hT0, le_rfl⟩ : Set.Icc (0 : ℝ) T) ∈ S)
    (h : ∀ s : Finset (Set.Icc (0 : ℝ) T), (↑s : Set (Set.Icc (0 : ℝ) T)) ⊆ S →
      P.map (fun f : D T E => fun t : s => f t) = Q.map (fun f : D T E => fun t : s => f t)) :
    P = Q := sorry

-- copied from contract CT1_Maps (not part of this contract)
def restrict {T : ℝ} {E : Type*} [TopologicalSpace E] {a : ℝ} (haT : a ≤ T) (f : D T E) :
    D a E where
  toFun t := f ⟨t, t.2.1, t.2.2.trans haT⟩
  isCadlag' := sorry

-- copied from contract CT1_Maps (not part of this contract)
/-- Time–space scaling restricted to `[0,a]`: `t ↦ k * g (min (s * t) T)`. -/
def timeSpaceScale {T : ℝ} {E : Type*} [NormedRing E] (a : ℝ) (hT : 0 ≤ T)
    (p : D T E × E × Set.Ioi (0 : ℝ)) : D a E where
  toFun t := p.2.1 * p.1 ⟨min (p.2.2 * t) T,
    le_min (mul_nonneg (le_of_lt p.2.2.2) t.2.1) hT, min_le_right _ _⟩
  isCadlag' := sorry

end BGW.Skorokhod

namespace BGW.StableTrees

open BGW.Skorokhod

-- copied from contract CT4_StableLaw (not part of this contract)
noncomputable def stableLaw (θ : ℝ) : ProbabilityMeasure ℝ :=
  if hθ : 1 < θ ∧ θ ≤ 2 then
    ⟨volume.withDensity (fun x => ENNReal.ofReal (Scalar.stableDensity θ x)), sorry⟩
  else ⟨Measure.dirac 0, inferInstance⟩

-- copied from contract CT4_StableLaw (not part of this contract)
noncomputable def stableLawAt (θ t : ℝ) : ProbabilityMeasure ℝ :=
  (stableLaw θ).map (fun x => t ^ (1 / θ) * x)

-- copied from contract CT4_StableLaw (not part of this contract)
theorem stableLawAt_conv {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (stableLawAt θ s : Measure ℝ) ∗ (stableLawAt θ t : Measure ℝ) =
      (stableLawAt θ (s + t) : Measure ℝ) := sorry

/-! ## The contract -/

/-- `P` is a law of a spectrally positive θ-stable Lévy process on `[0,T]`, in Billingsley's
finite-dimensional form: the path starts at `0` almost surely, and along every strictly
increasing finite family of times starting at `0` (the terminal time `T` allowed) the increments
are independent with laws `stableLawAt θ (t_i - t_{i-1})`. The stable-process interpretation
requires `1 < θ ∧ θ ≤ 2` and `0 < T`: outside the index range `stableLaw` is a junk Dirac mass
and the zero-path law satisfies the predicate; for `T ≤ 0` the fields are degenerate. -/
structure IsStableLevyLaw (θ T : ℝ) (P : ProbabilityMeasure (D T ℝ)) : Prop where
  /-- Audit correction 7: the start condition, with the proof `0 ≤ T` as hypothesis. -/
  start : ∀ h : 0 ≤ T, ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)), f ⟨0, le_rfl, h⟩ = 0
  increments : ∀ (k : ℕ) (t : Fin (k + 1) → Set.Icc (0 : ℝ) T),
    StrictMono t → (t 0 : ℝ) = 0 →
    Measure.map (fun f : D T ℝ => fun i : Fin k => f (t i.succ) - f (t i.castSucc))
      (P : Measure (D T ℝ)) =
      Measure.pi (fun i : Fin k =>
        (stableLawAt θ ((t i.succ : ℝ) - t i.castSucc) : Measure ℝ))

/-- Increments along any strictly increasing finite family of times (not necessarily starting at
`0`) are independent with stable laws (Sol audit suggestion; obtained by prepending `0` and
marginalizing). -/
theorem IsStableLevyLaw.map_increments {θ T : ℝ} {P : ProbabilityMeasure (D T ℝ)}
    (hP : IsStableLevyLaw θ T P) (k : ℕ) (t : Fin (k + 1) → Set.Icc (0 : ℝ) T)
    (ht : StrictMono t) :
    Measure.map (fun f : D T ℝ => fun i : Fin k => f (t i.succ) - f (t i.castSucc))
      (P : Measure (D T ℝ)) =
      Measure.pi (fun i : Fin k =>
        (stableLawAt θ ((t i.succ : ℝ) - t i.castSucc) : Measure ℝ)) := sorry

/-- Uniqueness of the stable Lévy law on a positive horizon (blueprint Node 14). -/
theorem IsStableLevyLaw.unique {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    {P Q : ProbabilityMeasure (D T ℝ)} (hP : IsStableLevyLaw θ T P)
    (hQ : IsStableLevyLaw θ T Q) : P = Q := sorry

/-- P3 (blueprint Node 13): almost surely continuous at each fixed time, including `T`.
The quantifier over the time is outside `∀ᵐ`. -/
theorem IsStableLevyLaw.ae_continuousAt {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    {P : ProbabilityMeasure (D T ℝ)} (hP : IsStableLevyLaw θ T P) (t : Set.Icc (0 : ℝ) T) :
    ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)), ContinuousAt f t := sorry

/-- Restriction to `[0,a]` is measurable for the Borel structures. -/
theorem measurable_restrict {T a : ℝ} (haT : a ≤ T) :
    Measurable (restrict (E := ℝ) haT) := sorry

/-- P1 form (blueprint Node 16): the restriction of any stable Lévy law to a positive
subhorizon `a ≤ T` is the stable Lévy law there. -/
theorem IsStableLevyLaw.map_restrict {θ T a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 < a)
    (haT : a ≤ T) {P : ProbabilityMeasure (D T ℝ)} (hP : IsStableLevyLaw θ T P) :
    IsStableLevyLaw θ a (P.map (restrict haT)) := sorry

/-- For fixed horizon-to-horizon rescaling the scaling map is measurable. -/
theorem measurable_timeSpaceScale_fixed {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (k : ℝ) :
    Measurable (fun f : D (c * T) ℝ =>
      timeSpaceScale T (mul_pos hc hT).le (f, k, (⟨c, hc⟩ : Set.Ioi (0 : ℝ)))) := sorry

/-- P2 form (blueprint Node 17): if `P` is the stable Lévy law on `[0, c T]`, then
`t ↦ c^{-1/θ} X_{c t}` on `[0,T]` has the stable Lévy law there. -/
theorem IsStableLevyLaw.map_timeSpaceScale {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    {c : ℝ} (hc : 0 < c) {P : ProbabilityMeasure (D (c * T) ℝ)}
    (hP : IsStableLevyLaw θ (c * T) P) :
    IsStableLevyLaw θ T
      (P.map (fun f : D (c * T) ℝ =>
        timeSpaceScale T (mul_pos hc hT).le
          (f, c ^ (-(1 / θ)), (⟨c, hc⟩ : Set.Ioi (0 : ℝ))))) := sorry

end BGW.StableTrees
