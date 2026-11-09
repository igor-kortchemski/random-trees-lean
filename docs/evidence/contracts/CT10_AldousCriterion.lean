import BGW.Skorokhod.CompleteMetricSpace
import BGW.Skorokhod.Separable
import BGW.Skorokhod.Measurable
import BGW.Skorokhod.Tightness
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Probability.Process.Filtration

/-! Contract probe for CT.C8 (CT10), Aldous's criterion (Billingsley 1999, Theorem 16.10;
Jacod-Shiryaev VI.4.5; Kallenberg FMP Thm 16.11), finite horizon `[0,T]`, `D T ℝ` with J1.

DATA. For each `n`, a probability space `(Ω n, P n)`, a filtration `𝓕 n` indexed by
`Set.Icc 0 T` and a measurable `X n : Ω n → D T ℝ` (Borel for J1), adapted: `ω ↦ X n ω t` is
`𝓕 n t`-measurable. Measurability of `X n` is a hypothesis: otherwise `Measure.map` is `0`
and tightness would be vacuous. The `Ω n` may be distinct spaces.

STOPPING TIMES. Own definition `IsStopTime`: `τ : Ω → Icc 0 T` with `{τ ≤ t} ∈ 𝓕 t` for all
`t`. This is the bounded case (`τ ≤ T`), the one in the spec. `τ + h` is truncated at `T` by
`Set.projIcc`; for `h ≥ 0` this is `min (τ+h) T`.

HYPOTHESES (spec formulation, sequence form)
 (i) `lim_{c→∞} limsup_n P_n(‖X^n‖ ≥ c) = 0`, as `∀ η>0, ∃ c, limsup_n P_n(∃ t, c ≤ |X^n_t|) ≤ η`
     (`‖f‖ = sup_t |f t|`; the event `{∃ t, c ≤ |f t|}` is `{‖f‖ ≥ c}` up to `c ↔ c ± ε`);
 (ii) for every choice of stopping times `τ_n` and reals `h_n → 0`, `h_n ≥ 0`:
     `P_n(|X^n_{τ_n+h_n} - X^n_{τ_n}| ≥ ε) → 0` for each `ε > 0`.
CONCLUSION: `{law of X^n}` is tight on `D T ℝ`.
Hypothesis (ii) is equivalent to `∀ ε η, ∃ δ n₀, ∀ n ≥ n₀, ∀ τ, ∀ h ∈ [0,δ], P_n(...) ≤ η`
(Billingsley (16.22)); the sequence form quantifies over `τ_n` and `h_n` arbitrarily, so
the two are equivalent by a diagonal argument; the sequence form is the easier one to use
downstream (the constructed sequence of bad `(τ, h)` is the proof's first step).
Variant `isTightMeasureSet_of_aldous_fixedTimes`: (i) may be replaced by tightness of `X^n_t` at
every fixed time `t` (Billingsley 16.10); tightness of `X^n_0` alone does not suffice (see the
counterexample in its docstring).  Adaptedness of `X` is essential.
Event measures are outer measures of the sets (no measurability of events needed in
the statement); they are in fact measurable. Events use `≥`, as in the spec.
Depends only on Mathlib and `BGW.Skorokhod`. -/

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace BGW.Skorokhod

variable {T : ℝ}

/-- `τ : Ω → [0,T]` is a stopping time for `𝓕`. -/
def IsStopTime {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration (Set.Icc (0 : ℝ) T) m)
    (τ : Ω → Set.Icc (0 : ℝ) T) : Prop :=
  ∀ t, MeasurableSet[𝓕 t] {ω | τ ω ≤ t}

/-- Billingsley 1999, Theorem 16.10 (sufficiency), CT.C8, spec form. -/
theorem isTightMeasureSet_of_aldous (hT : 0 < T)
    {Ω : ℕ → Type*} [m : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (𝓕 : ∀ n, Filtration (Set.Icc (0 : ℝ) T) (m n))
    (X : ∀ n, Ω n → D T ℝ) (hX : ∀ n, Measurable (X n))
    (hadapted : ∀ n t, Measurable[𝓕 n t] (fun ω => X n ω t))
    (hsup : ∀ η > 0, ∃ c : ℝ,
      limsup (fun n => P n {ω | ∃ t, c ≤ |X n ω t|}) atTop ≤ ENNReal.ofReal η)
    (hAldous : ∀ (τ : ∀ n, Ω n → Set.Icc (0 : ℝ) T), (∀ n, IsStopTime (𝓕 n) (τ n)) →
      ∀ h : ℕ → ℝ, (∀ n, 0 ≤ h n) → Tendsto h atTop (𝓝 0) →
      ∀ ε > 0, Tendsto
        (fun n => P n {ω | ε ≤ |X n ω (Set.projIcc 0 T hT.le (τ n ω + h n)) - X n ω (τ n ω)|})
        atTop (𝓝 0)) :
    IsTightMeasureSet (Set.range fun n => (P n).map (X n)) := sorry

/-- Same conclusion with the sup-norm tightness (i) replaced by tightness of `X^n_t` at every fixed
time `t ∈ [0,T]` (Billingsley 1999, Theorem 16.10 with fixed-time tightness).  Tightness of `X^n_0`
alone is NOT enough: `X^n_t = n·1{U ≤ t}` with `U` uniform satisfies Aldous's condition and has
tight `X^n_0 = 0`, but is not tight. -/
theorem isTightMeasureSet_of_aldous_fixedTimes (hT : 0 < T)
    {Ω : ℕ → Type*} [m : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (𝓕 : ∀ n, Filtration (Set.Icc (0 : ℝ) T) (m n))
    (X : ∀ n, Ω n → D T ℝ) (hX : ∀ n, Measurable (X n))
    (hadapted : ∀ n t, Measurable[𝓕 n t] (fun ω => X n ω t))
    (hfixed : ∀ t : Set.Icc (0 : ℝ) T, ∀ η > 0, ∃ c : ℝ,
      limsup (fun n => P n {ω | c ≤ |X n ω t|}) atTop ≤ ENNReal.ofReal η)
    (hAldous : ∀ (τ : ∀ n, Ω n → Set.Icc (0 : ℝ) T), (∀ n, IsStopTime (𝓕 n) (τ n)) →
      ∀ h : ℕ → ℝ, (∀ n, 0 ≤ h n) → Tendsto h atTop (𝓝 0) →
      ∀ ε > 0, Tendsto
        (fun n => P n {ω | ε ≤ |X n ω (Set.projIcc 0 T hT.le (τ n ω + h n)) - X n ω (τ n ω)|})
        atTop (𝓝 0)) :
    IsTightMeasureSet (Set.range fun n => (P n).map (X n)) := sorry

end BGW.Skorokhod
