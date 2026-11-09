import BGW.StableTrees.ExcursionMeasure
import BGW.StableTrees.MarkedExcursions
import BGW.StableTrees.StableExcursionSupport
import BGW.ContinuumTrees.ExcursionCarrier
import BGW.StableTrees.StableStrongMarkov
import BGW.StableTrees.StableFirstPassage
import BGW.StableTrees.StablePassageSubordinator
import BGW.StableTrees.StableKendall

/-! Contract probe for CT7 node E08 (Kendall adapter, survival kernel and the Gamma analytic
API), following `r3-ct7-blueprint/blueprint.md` E08 and the signature block.

FINDING (what already exists).  `BGW/StableTrees/StableKendall.lean` already proves, for every
`x > 0` and with the sealed names, the full distribution identity
`kendall : passageLaw θ x = (volume.restrict (Ioi 0)).withDensity
  (fun s => ofReal (x / s * stableDensityAt θ s (-x)))`,
and `StableKendallLocal.lean` defines `kendallKernel θ x s = x / s * stableDensityAt θ s (-x)`
(argument order `(level, time)`), with `kendallKernel_nonneg`, `kendallKernel_continuousOn`
(joint, on `{0 < s}`) and `lintegral_kendallKernel` (mass one).  So E08 is only an ADAPTER:
the missing form is (a) the blueprint argument order `qKernel θ s x` (time first), (b) the
`volume.withDensity (if 0 < s then _ else 0)` shape used by E09 (instead of
`volume.restrict (Ioi 0)`), and (c) the survival-kernel / Gamma analytic definitions, which do
not exist in the library.  N12/N13 are NOT needed any more: the blueprint's "waits for N13"
is obsolete, the identity is in the library (`kendall`).

CONSTANTS.  `q_s(x) = (x/s) p_s(-x)` is the density of `T_x` (first passage below `-x`) at
time `s`; `p_s` is `stableDensityAt θ s` (`p_s(y) = s^{-1/θ} p_1(s^{-1/θ} y)`).  Tail:
`G_r(x) = P(T_x > r) = ∫_{s>r} q_s(x) ds`, which equals `θ ∫_0^{x r^{-1/θ}} p_1(-u) du`
(substitution `u = x s^{-1/θ}`).  `gammaA θ a x = θ q_{1-a}(x) / G_{1-a}(x)` (blueprint).

TRUTH.  All statements bind `hθ : 1 < θ ∧ θ ≤ 2`.  `sizeTailKernel` is a Bochner integral
(junk `0` if not integrable), so the finiteness theorem `sizeTailKernelENN_lt_top` is what
makes it meaningful; the nonnegative-integral version `sizeTailKernelENN` is primary.
`sizeTailKernel_pos` needs `r > 0, x > 0`; `qKernel` is junk for `s ≤ 0`.

PROOF PLAN.  Adapter lemmas by `rfl`/`kendall` + `withDensity_indicator`.  Tail =
`passageLaw θ x (Ioi r)` by integrating `passageLaw_eq_qKernel`.  Positivity: the density
`q_s(x) = x s^{-1-1/θ} p_1(-x s^{-1/θ})` is positive for large `s` since `p_1(-u) > 0` for
`u` near `0` (continuity and `p_1(0) > 0`, `Scalar.stableDensity_zero_pos`); no global
positivity of the density is assumed.  Continuity of `G` in `(r, x)`: dominated convergence
with the local bound `qKernel_le_of_ge`, plus the tail bound `∫_{s>r} q_s(x) ≤ 1`.
Estimate 400-800 lines beyond the existing `kendall`. -/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace BGW.StableTrees

/-! ### Definitions -/

/-- **The Kendall density** `q_s(x) = (x/s) p_s(-x)`, time first, level second (real arguments,
junk for `s ≤ 0`).  Same function as `kendallKernel θ x s`. -/
noncomputable def qKernel (θ s x : ℝ) : ℝ := (x / s) * stableDensityAt θ s (-x)

/-- **Survival (size-tail) kernel in the nonnegative-integral form**
`∫⁻_{s > r} q_s(x) ds` (primary definition, never junk). -/
noncomputable def sizeTailKernelENN (θ r x : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioi r, ENNReal.ofReal (qKernel θ s x)

/-- **Survival (size-tail) kernel** `G_r(x) = ∫_{s > r} q_s(x) ds` as a real integral
(equal to `(sizeTailKernelENN θ r x).toReal` for `r ≥ 0`, `x ≥ 0`, see
`ofReal_sizeTailKernel`). -/
noncomputable def sizeTailKernel (θ r x : ℝ) : ℝ := ∫ s in Ioi r, qKernel θ s x

/-- **The Gamma factor** `Γ_a(x) = θ q_{1-a}(x) / G_{1-a}(x)` of the path identity (E10). -/
noncomputable def gammaA (θ a x : ℝ) : ℝ := θ * qKernel θ (1 - a) x / sizeTailKernel θ (1 - a) x

/-! ### Adapter to the existing Kendall theorem -/

/-- `qKernel` is the library's `kendallKernel` with the arguments in the blueprint order. -/
theorem qKernel_eq_kendallKernel (θ s x : ℝ) : qKernel θ s x = kendallKernel θ x s := rfl

/-- `qKernel` is nonnegative for `x ≥ 0`, `s > 0`. -/
theorem qKernel_nonneg {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) :
    0 ≤ qKernel θ s x := kendallKernel_nonneg hθ hx hs

/-- **Kendall, adapter form (the only missing form of the existing `kendall`).**  For `x > 0`,
`passageLaw θ x` has density `qKernel θ s x` on `s > 0` (and `0` elsewhere) w.r.t. Lebesgue
measure on `ℝ`.  Proof: `kendall` plus `withDensity_indicator` on `Ioi 0`. -/
theorem passageLaw_eq_qKernel {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0) (hx : 0 < x) :
    passageLaw θ x = volume.withDensity
      (fun s => ENNReal.ofReal (if 0 < s then qKernel θ s x else 0)) := by
  rw [kendall hθ hx, ← withDensity_indicator measurableSet_Ioi]
  congr 1
  funext s
  by_cases hs : 0 < s <;> simp [qKernel, hs, Set.indicator]

/-! ### Survival kernel: finiteness and identification -/

/-- **The tail is the passage-time tail**: for `r ≥ 0`, `x > 0`,
`∫⁻_{s>r} q_s(x) = P(T_x > r)`. -/
theorem sizeTailKernelENN_eq_passageLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {r : ℝ} (hr : 0 ≤ r)
    (x : ℝ≥0) (hx : 0 < x) :
    sizeTailKernelENN θ r (x : ℝ) = passageLaw θ x (Ioi r) := sorry

/-- **Finiteness** of the survival kernel (it is at most `1`), for `r ≥ 0`, `x > 0`. -/
theorem sizeTailKernelENN_lt_top {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {r : ℝ} (hr : 0 ≤ r) {x : ℝ}
    (hx : 0 < x) : sizeTailKernelENN θ r x < ⊤ := sorry

/-- **Finiteness**, `x : ℝ≥0` form (same statement for the cast level). -/
theorem sizeTailKernelENN_lt_top_nnreal {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {r : ℝ} (hr : 0 ≤ r)
    {x : ℝ≥0} (hx : 0 < x) : sizeTailKernelENN θ r (x : ℝ) < ⊤ :=
  sizeTailKernelENN_lt_top hθ hr (NNReal.coe_pos.2 hx)

/-- **Conversion** between the real and nonnegative-integral survival kernels
(finite real-valued reading), for `r ≥ 0`, `x > 0`. -/
theorem ofReal_sizeTailKernel {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {r : ℝ} (hr : 0 ≤ r) {x : ℝ}
    (hx : 0 < x) : ENNReal.ofReal (sizeTailKernel θ r x) = sizeTailKernelENN θ r x := sorry

/-- **Positivity of the survival kernel**: `G_r(x) > 0` for `r > 0`, `x > 0`. -/
theorem sizeTailKernel_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {r : ℝ} (hr : 0 < r) {x : ℝ}
    (hx : 0 < x) : 0 < sizeTailKernel θ r x := sorry

/-! ### Continuity and local bounds -/

/-- **Joint continuity of `q`** in `(s, x)` on `s > 0` (adapter of `kendallKernel_continuousOn`). -/
theorem continuousOn_qKernel {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ContinuousOn (fun z : ℝ × ℝ => qKernel θ z.1 z.2) {z | 0 < z.1} := by
  have h := (kendallKernel_continuousOn hθ).comp continuous_swap.continuousOn
    (s := {z : ℝ × ℝ | 0 < z.1}) (fun z hz => hz)
  exact h

/-- **Local integrable dominator** (`stableDensityAt_le_of_ge`, `q_s(x) = (x/s) p_s(-x)` and
`p_s ≤ M s^{-1/θ}`): for `r > 0` and `X ≥ 0` there is `C` (depending on `θ`, `r`, `X`) with
`q_s(x) ≤ C x s^{-1-1/θ}` for all `s ≥ r`, `0 ≤ x ≤ X`.  The right side is integrable on
`s ≥ r` (exponent `-1-1/θ < -1`), uniformly in `x ≤ X`. -/
theorem qKernel_le_of_ge {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {r : ℝ} (hr : 0 < r) (X : ℝ) :
    ∃ C : ℝ, ∀ s, r ≤ s → ∀ x, 0 ≤ x → x ≤ X →
      qKernel θ s x ≤ C * x * s ^ (-1 - 1 / θ) := sorry

/-- **Measurability** of `q` jointly in `(s, x)` on all of `ℝ × ℝ`. -/
theorem measurable_qKernel (θ : ℝ) : Measurable (fun z : ℝ × ℝ => qKernel θ z.1 z.2) := sorry

/-- **Measurability** of the nonnegative size-tail kernel jointly in `(r, x)`
(parametric lintegral of the jointly measurable `measurable_qKernel`). -/
theorem measurable_sizeTailKernelENN (θ : ℝ) :
    Measurable (fun z : ℝ × ℝ => sizeTailKernelENN θ z.1 z.2) := sorry

/-- **Mass one of the Kendall density**, in `qKernel` form (from `lintegral_kendallKernel`). -/
theorem lintegral_qKernel {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {x : ℝ≥0} (hx : 0 < x) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (qKernel θ s x) = 1 :=
  lintegral_kendallKernel hθ hx

/-- **Joint continuity of the survival kernel** in `(r, x)` on `r > 0`, `x > 0`.  Proof plan:
dominated convergence on `s > r₀` (locally `r ≥ r₀ > 0`, `x ≤ X`) with the integrable
dominator `C X s^{-1-1/θ}` of `qKernel_le_of_ge` (and `continuousOn_qKernel`); or the scaling
route `G_r(x) = P(T_1 > r x^{-θ})` and continuity of the law of `T_1`. -/
theorem continuousOn_sizeTailKernel {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ContinuousOn (fun z : ℝ × ℝ => sizeTailKernel θ z.1 z.2) {z | 0 < z.1 ∧ 0 < z.2} := sorry

/-- **Continuity of `Γ_a(x)`** jointly in `(a, x)` on `a < 1`, `x > 0` (quotient of continuous
functions with positive denominator `sizeTailKernel_pos`). -/
theorem continuousOn_gammaA {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ContinuousOn (fun z : ℝ × ℝ => gammaA θ z.1 z.2) {z | z.1 < 1 ∧ 0 < z.2} := sorry

/-- **Measurability** of `Γ` jointly in `(a, x)`. -/
theorem measurable_gammaA (θ : ℝ) : Measurable (fun z : ℝ × ℝ => gammaA θ z.1 z.2) := sorry

/-- **Defining identity** of `Γ`: `Γ_a(x) G_{1-a}(x) = θ q_{1-a}(x)` when `G_{1-a}(x) > 0`. -/
theorem gammaA_mul_sizeTail {θ a x : ℝ} (h : 0 < sizeTailKernel θ (1 - a) x) :
    gammaA θ a x * sizeTailKernel θ (1 - a) x = θ * qKernel θ (1 - a) x := by
  unfold gammaA
  exact div_mul_cancel₀ _ h.ne'

/-- **Nonnegativity of `Γ_a(x)`** for `a < 1`, `x > 0`. -/
theorem gammaA_nonneg {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {a x : ℝ} (ha : a < 1) (hx : 0 < x) :
    0 ≤ gammaA θ a x := sorry

end BGW.StableTrees
