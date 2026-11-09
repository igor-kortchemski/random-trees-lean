import BGW.StableTrees.StableProcessMarkov
import BGW.StableTrees.StableDensityAPI
import BGW.Skorokhod.Vervaat
import BGW.Skorokhod.MeasurableExtrema

/-! Contract probe for CT6 N11, uniqueness part only (wave B): a.s. there is exactly one
generalized minimizer (a time `g` with `min (leftLim f g) (f g) = ⨅ t, f t`).

Maintained file (proposed): `BGW/StableTrees/StableMinimumUnique.lean`.

Notes.
* `F f s = min (leftLim f s) (f s)` is the generalized value; `genMin f J = ⨅ s : J, F f s`.
  `leftLim f 0 = f 0` on `Icc 0 T` (no left neighbourhood), so `0` is harmless.
* `genMinOn f a b` uses the closed window `[a,b]` of `Icc 0 T`; the left limit at `a` is taken in
  the whole path, so `genMinOn f a b = min (f a-) (inf over [a,b] of f)` for `a > 0`.
* Existence is the sealed `BGW.Skorokhod.exists_min_leftLim`; only a wrapper is stated.
* Separation: two distinct generalized minimizers `g₁ < g₂` are separated by rationals
  `b < c` with `g₁ ≤ b`, `c ≤ g₂`; then both windows `[0,b]`, `[c,T]` have generalized
  minimum equal to the global one (`F ≥ ⨅ f` everywhere). Only outer endpoints `0`, `T` are
  needed, but the probability-zero lemma is stated for general windows `[a,b]`, `[c,d]`.
* The probability-zero events are stated with the (outer) measure, so no measurability proof is
  needed for the main theorem; `measurable_genMinOn` is an optional convenience.
* The left limit at `c` is `X_c` almost surely (`ae_continuousAt`), which is why the window
  `[c,d]` is `X_c + (shifted increment path)`-measurable up to a null set. -/

open MeasureTheory ProbabilityTheory
open scoped Topology

namespace BGW.StableTrees

open BGW.Skorokhod

/-- Generalized value of `f` at `s`: the minimum of the left limit and the value. -/
noncomputable def genVal {T : ℝ} (f : D T ℝ) (s : Set.Icc (0 : ℝ) T) : ℝ :=
  min (Function.leftLim f s) (f s)

/-- Generalized minimum over a set of times. -/
noncomputable def genMin {T : ℝ} (f : D T ℝ) (J : Set (Set.Icc (0 : ℝ) T)) : ℝ :=
  ⨅ s : J, genVal f s

/-- The window `[a,b]` of times. -/
def window (T a b : ℝ) : Set (Set.Icc (0 : ℝ) T) := {s | a ≤ (s : ℝ) ∧ (s : ℝ) ≤ b}

/-- `g` is a generalized minimizer of `f`. -/
def IsGenMinimizer {T : ℝ} (f : D T ℝ) (g : Set.Icc (0 : ℝ) T) : Prop :=
  genVal f g = ⨅ t, f t

/-! ### Deterministic part -/

/-- Existence of a generalized minimizer (wrapper of `exists_min_leftLim`). -/
theorem exists_isGenMinimizer {T : ℝ} (hT : 0 ≤ T) (f : D T ℝ) :
    ∃ g, IsGenMinimizer f g :=
  exists_min_leftLim f hT

/-- The generalized value is bounded below by the global infimum. -/
theorem iInf_le_genVal {T : ℝ} (f : D T ℝ) (s : Set.Icc (0 : ℝ) T) :
    (⨅ t, f t) ≤ genVal f s := by
  sorry

/-- A generalized minimizer in a window gives the window the global minimum. -/
theorem genMin_eq_iInf_of_mem {T : ℝ} (f : D T ℝ) {J : Set (Set.Icc (0 : ℝ) T)}
    {g : Set.Icc (0 : ℝ) T} (hg : IsGenMinimizer f g) (hgJ : g ∈ J) :
    genMin f J = ⨅ t, f t := by
  sorry

/-- Separation: two distinct generalized minimizers are separated by rationals `b < c`, and the
windows `[0,b]`, `[c,T]` have equal generalized minima. -/
theorem exists_rat_separation {T : ℝ} {f : D T ℝ} {g₁ g₂ : Set.Icc (0 : ℝ) T}
    (h₁ : IsGenMinimizer f g₁) (h₂ : IsGenMinimizer f g₂) (hne : g₁ ≠ g₂) :
    ∃ b c : ℚ, 0 ≤ (b : ℝ) ∧ (b : ℝ) < c ∧ (c : ℝ) ≤ T ∧
      genMin f (window T 0 b) = genMin f (window T c T) := by
  sorry

/-- If a path has a generalized minimizer but not a unique one, some rational pair separates. -/
theorem exists_rat_pair_of_not_existsUnique {T : ℝ} (hT : 0 ≤ T) {f : D T ℝ}
    (h : ¬ ∃! g : Set.Icc (0 : ℝ) T, IsGenMinimizer f g) :
    ∃ b c : ℚ, 0 ≤ (b : ℝ) ∧ (b : ℝ) < c ∧ (c : ℝ) ≤ T ∧
      genMin f (window T 0 b) = genMin f (window T c T) := by
  sorry

/-- Measurability of window generalized minima (via rational infima / `measurable_iInf_eval`). -/
theorem measurable_genMinOn {T : ℝ} (a b : ℝ) :
    Measurable (fun f : D T ℝ => genMin f (window T a b)) := by
  sorry


/-- Adapter 1: the window minimum on `[a,b]` only depends on the restriction to `[0,b]`. -/
theorem genMin_window_eq_restrict {T : ℝ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T)
    (f : D T ℝ) :
    genMin f (window T a b) = genMin (restrict (E := ℝ) hbT f) (window b a b) := by
  sorry

/-- Adapter 2: on `{ContinuousAt f c}` the window minimum on `[c,d]` is `f c` plus the window
minimum of the shifted increment path on `[0, d-c]`. -/
theorem genMin_window_eq_of_continuousAt {T : ℝ} {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d)
    (hdT : d ≤ T) (f : D T ℝ) (hcT : c ≤ T)
    (hf : ContinuousAt f (⟨c, hc, hcT⟩ : Set.Icc (0 : ℝ) T)) :
    genMin f (window T c d) =
      f ⟨c, hc, hcT⟩ + genMin (shiftIncrement hc hcT f) (window (T - c) 0 (d - c)) := by
  sorry

/-! ### Probabilistic part -/

/-- Increments of a stable Lévy law have no atoms. -/
theorem IsStableLevyLaw.measure_increment_eq {θ T : ℝ} {P : ProbabilityMeasure (D T ℝ)}
    (hθ : 1 < θ ∧ θ ≤ 2) (hP : IsStableLevyLaw θ T P) {s u : ℝ} (hs : 0 ≤ s) (hsu : s < u)
    (huT : u ≤ T) (x : ℝ) :
    (P : Measure (D T ℝ))
        ({f : D T ℝ | f ⟨u, hs.trans hsu.le, huT⟩ - f ⟨s, hs, hsu.le.trans huT⟩ = x} : Set (D T ℝ))
      = 0 := by
  sorry

/-- Three-way independence: for `0 ≤ b < c ≤ T`, the increment `f c - f b` is independent of the
pair (past restricted to `[0,b]`, increment path after `c`), for the product σ-algebra. -/
theorem IsStableLevyLaw.indepFun_increment_restrict_shiftIncrement {θ T : ℝ}
    {P : ProbabilityMeasure (D T ℝ)} (hP : IsStableLevyLaw θ T P) {b c : ℝ}
    (hb : 0 ≤ b) (hbc : b < c) (hcT : c ≤ T) :
    IndepFun
      (fun f : D T ℝ =>
        f ⟨c, hb.trans hbc.le, hcT⟩ - f ⟨b, hb, hbc.le.trans hcT⟩)
      (fun f : D T ℝ =>
        (restrict (E := ℝ) (hbc.le.trans hcT) f,
          shiftIncrement (hb.trans hbc.le) hcT f))
      (P : Measure (D T ℝ)) := by
  sorry

/-- Key lemma: for separated windows `[a,b]`, `[c,d]` (`0 ≤ a ≤ b < c ≤ d ≤ T`), the generalized
minima over them coincide with probability zero. Proof: write them as `A` and `X_b + Z + M`
with `Z = X_c - X_b` atom-free and independent of `(past through b, increment path after c)`
(`IsStableLevyLaw.indepFun_restrict_shiftIncrement` at `b`, `c`, the three-way independence
lemma `IsStableLevyLaw.indepFun_increment_restrict_shiftIncrement`, and the two measurability
adapters `genMin_window_eq_restrict`, `genMin_window_eq_of_continuousAt`; `ae_continuousAt` at
`c`). -/
theorem IsStableLevyLaw.measure_genMin_window_eq_zero {θ T : ℝ} {P : ProbabilityMeasure (D T ℝ)}
    (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) (hP : IsStableLevyLaw θ T P)
    {a b c d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b < c) (hcd : c ≤ d) (hdT : d ≤ T) :
    (P : Measure (D T ℝ))
        ({f : D T ℝ | genMin f (window T a b) = genMin f (window T c d)} : Set (D T ℝ)) = 0 := by
  sorry

/-- Main theorem (uniqueness part of N11): almost surely there is exactly one generalized
minimizer. -/
theorem IsStableLevyLaw.ae_existsUnique_generalizedMinimizer {θ T : ℝ}
    {P : ProbabilityMeasure (D T ℝ)} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    (hP : IsStableLevyLaw θ T P) :
    ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)),
      ∃! g : Set.Icc (0 : ℝ) T, min (Function.leftLim f g) (f g) = ⨅ t, f t := by
  sorry

/-- The same for the canonical stable process law. -/
theorem stableProcessLaw_ae_existsUnique_generalizedMinimizer {θ T : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) :
    ∀ᵐ f : D T ℝ ∂(stableProcessLaw θ T : Measure (D T ℝ)),
      ∃! g : Set.Icc (0 : ℝ) T, min (Function.leftLim f g) (f g) = ⨅ t, f t :=
  (isStableLevyLaw_stableProcessLaw hθ hT).ae_existsUnique_generalizedMinimizer hθ hT


/-- (a) Transfer to any measure absolutely continuous w.r.t. a stable Lévy law. -/
theorem ae_existsUnique_generalizedMinimizer_of_absolutelyContinuous {θ T : ℝ}
    {P : ProbabilityMeasure (D T ℝ)} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    (hP : IsStableLevyLaw θ T P) {μ : Measure (D T ℝ)} (hμ : μ ≪ (P : Measure (D T ℝ))) :
    ∀ᵐ f : D T ℝ ∂μ, ∃! g : Set.Icc (0 : ℝ) T, IsGenMinimizer f g :=
  hμ.ae_le (hP.ae_existsUnique_generalizedMinimizer hθ hT)

/-- (b) Window-relative uniqueness: a.s. there is a unique time `g ≤ b` whose generalized value
is the generalized minimum over `[0,b]`. -/
theorem IsStableLevyLaw.ae_existsUnique_windowMinimizer {θ T : ℝ}
    {P : ProbabilityMeasure (D T ℝ)} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    (hP : IsStableLevyLaw θ T P) {b : ℝ} (hb : 0 < b) (hbT : b ≤ T) :
    ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)),
      ∃! g : Set.Icc (0 : ℝ) T, (g : ℝ) ≤ b ∧ genVal f g = genMin f (window T 0 b) := by
  sorry

/-- (c) Transfer of (b) to measures absolutely continuous w.r.t. a stable Lévy law. -/
theorem ae_existsUnique_windowMinimizer_of_absolutelyContinuous {θ T : ℝ}
    {P : ProbabilityMeasure (D T ℝ)} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    (hP : IsStableLevyLaw θ T P) {b : ℝ} (hb : 0 < b) (hbT : b ≤ T)
    {μ : Measure (D T ℝ)} (hμ : μ ≪ (P : Measure (D T ℝ))) :
    ∀ᵐ f : D T ℝ ∂μ,
      ∃! g : Set.Icc (0 : ℝ) T, (g : ℝ) ≤ b ∧ genVal f g = genMin f (window T 0 b) :=
  hμ.ae_le (hP.ae_existsUnique_windowMinimizer hθ hT hb hbT)

end BGW.StableTrees
