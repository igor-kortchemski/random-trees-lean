import BGW.Skorokhod.ProductPathsVector
import BGW.Skorokhod.Prefix
import BGW.Skorokhod.MeasurableMaps
import BGW.Skorokhod.VervaatContinuity
import BGW.Skorokhod.Jump

/-! Contract probe W109/G3 for the optional gaps in `CLASSICAL_THEORY_INPUTS.md`: C5 item 4
converse, C7 in continuous path space, C11 item 2 in continuous path space, C33 item 3b and
C36 (attainment and the zero-jump remarks).  Suggested maintained module for C5/C7/C11:
`BGW/Skorokhod/ProductPathsInverse.lean` and `BGW/Skorokhod/ContinuousPrefix.lean`; C33 belongs
in `VervaatContinuity.lean`, and C36 in `Jump.lean`.  Namespace: `BGW.Skorokhod`.

SOURCE.  C5 item 4: "Hence convergence in law in `D_T(ℝ) × C_T^k` with continuous coordinates
implies convergence in `D_T(ℝ^{1+k})`; the converse holds always (coordinates)."  C7: the stopped
path satisfies `d_T(φ_{T−δ}f, f) ≤ sup_{s∈[T−δ,T]} |f(s)−f(T−δ)|`, and
"The same holds in `C_T` with the uniform norm."  C11 item 2: for random elements of `D_T`,
`D_T × C_T^k`, or `C_T`,
prefix convergence, a.s. continuity of the limit at `T`, and terminal oscillation control imply
full convergence.  C33 item 3: "the only jump of V(ω) not coming from a jump of ω is at
`t = 1 − g_1`, of size `ω(1) − ω(1−)`."  C36: "`Δ̄` ... is the largest positive jump,
0 for continuous f; it is attained by finiteness of jumps > ε."

DEFINITIONS.  Sealed: `prodWithCont f g t = (f t, g t)`, `ofContinuous`, `stop`, `restrict`,
`extendConst`, `dist_stop_le`, `tendsto_of_tendsto_restrict_of_oscillation`, `vervaatD`,
`vervaatTime`, and `maxJump f = ⨆ t, max (f t - Function.leftLim f t) 0`.  New:
* `fstWithCont` takes the first coordinate of an `E × F`-valued càdlàg path.
  `splitProdWithCont f` is this first path together with the second coordinate as a continuous
  map when the latter is continuous.  Off that locus its second component is the constant
  `default`; this is the only junk branch.  It is never used under the law hypotheses, and
  `prodWithCont_splitProdWithCont` records that splitting is a genuine right inverse on the
  continuous-second-coordinate locus.
* `restrictContinuous`, `extendContinuous`, and `stopContinuous` are exactly restriction,
  constant extension, and stopping, but between `ContinuousMap` spaces with their uniform
  metrics.  They use the same clamped times as their sealed `D` counterparts.
* `vervaatWrapTime f = 1 - vervaatTime f`, as a point of `[0,1]`.

TRUTH CHECK.
(1) C5: both the pre-limit laws and the limit law must charge the continuous-second-coordinate
  locus; otherwise a continuous-map-valued random element cannot be formed.  `splitProdWithCont`
  is continuous ON this locus `L` (not at its points as a map on all of `D`: audit g3, finding 1,
  `f_n = (e, 1 + n⁻¹·1_{t ≥ T/2}) → (e, 1)` leaves `L`): within `L` the first coordinate inherits
  J1 convergence with the same time changes and the second converges uniformly by C5.2.  `L` is
  closed (`isClosedEmbedding_ofContinuous`, 1-Lipschitz second projection) and the map is
  measurable, so the closed-set portmanteau (or a Tietze extension from `L`) gives the theorem;
  `tendsto_map_of_ae_continuousAt` does NOT apply.  The default off `L` is irrelevant.
(2) C7: `dist` on `C([0,T],E)` is exactly `⨆ t, dist (f t) (g t)`, so the stated bound is the
  uniform-norm bound, not another use of the J1 distance.  The hypotheses `0 ≤ a ≤ T` ensure
  that the comparison at `a` and the tail subtype are nonempty in the intended way.  Replacing
  `a` by `T - δ` is only a substitution.
(3) C11: terminal continuity of every `C_T` path is automatic, so the redundant a.s. premise of
  the `D_T` formulation is omitted rather than hidden.  The hpre laws are on `C([0,a],E)`, and
  hosc uses the uniform distance on the original continuous paths.  Thus the conclusion is weak
  convergence on `C_T` itself, not merely after applying `ofContinuous`.
(4) C33: from the definition of `vervaatD`, the value and left limit at the wrap are
  `V(c) = f(1) - m` and `V(c-) = f(1-) - m`.  Although evaluating the second branch at `c`
  displays both `f(0)` and `-f(0)`, they cancel.  Consequently the signed jump is exactly
  `V(c) - V(c-) = f(1) - f(1-)`, as stated in the spec, with no `f(0)=0` correction.  At `g=0`,
  where `c=1`, the same formulas remain valid; no `0<g` premise is needed here.  If `g=1`, then
  `c=0`, `𝓝[<] c = ⊥`, and Mathlib's `leftLim` is the value by convention, not a limit from the
  left.  The left-limit and jump formulas therefore assume `0<c`; the value formula needs no
  hypothesis.  "Size" means signed upward jump `f(t)-f(t-)`, not absolute value or positive part.
(5) C36: for `T<0` the time domain is empty and there is no attaining time, so attainment needs
  `0≤T`; at `T=0`, time zero attains the zero jump.  Since `max` truncates downward jumps,
  `maxJump f=0` is NOT equivalent to continuity: it is equivalent to absence of upward jumps,
  `∀t, f(t)≤f(t-)`.  A downward-jump-only discontinuous path is the counterexample to the
  unqualified converse.  Under the additional spectrally nonnegative hypothesis
  `∀t, f(t-)≤f(t)`, the equivalence with continuity is true.

PROOF PLAN.
* C5 (180–300 lines): prove `fstWithCont` continuous by `tendsto_iff_exists_timeChange` and
  coordinatewise distance bounds.  On the continuous-second locus, identify the second component
  with the continuous limit and apply `tendsto_iSup_dist_of_tendsto_ofContinuous` plus
  `ContinuousMap.dist_eq_iSup`; use
  `isClosedEmbedding_ofContinuous` when comparing topologies.  Finish with
  `BGW.Probability.tendsto_map_of_ae_continuousAt` and `prodWithCont_splitProdWithCont`.
* C7 (50–100 lines): define `stopContinuous` by continuity of `max`, `min`, and composition.
  Either repeat `dist_stop_le` with the identity time change, or transfer it through the isometry
  `ofContinuous`; `isClosedEmbedding_ofContinuous` supplies the topology identification.
* C11 (160–280 lines): show restriction, constant extension, and stopping are 1-Lipschitz on
  continuous maps.  Apply `BGW.Probability.tendsto_of_tendsto_approx` directly on `C_T`, with
  `X k n = stopContinuous (a k) ∘ Y n` and `Z k = ν.map (stopContinuous (a k))`.  Push hpre
  forward by `extendContinuous` using `ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous`;
  obtain `Z k → ν` from the sealed deterministic stopped-path convergence, transported by
  `isClosedEmbedding_ofContinuous`, and the CMT.  Bound the approximation error by hosc using
  `dist_stopContinuous_le`, exactly as in `tendsto_of_tendsto_restrict_of_oscillation`.
* C33 (90–170 lines): unfold `vervaatD` at `vervaatWrapTime`.  On the left, the `g+t≤1` branch
  holds eventually and `g+t` increases to `1`; compose
  `(isCadlag f).tendsto_nhdsLT_leftLim` with this map and use `leftLim_eq_of_tendsto`.  Evaluate
  the value using the first branch, or the second branch with wrapped time zero; both agree.
  The hypothesis `0<vervaatWrapTime f` makes the left neighborhood nontrivial and excludes `g=1`.
  Ring normalization gives the jump.  The existing `continuousAt_vervaatD_wrap` is the special
  case `f(1-)=f(1)`, and is a useful consistency check, not a sufficient proof of the size.
* C36 (100–180 lines): if `maxJump f=0`, choose time zero using `0≤T`.  If it is positive,
  approximate the supremum within `maxJump f/2`; the corresponding times form a finite set by
  `finite_setOf_jump_gt`, since an upward jump is bounded by its absolute jump distance.  Take a
  maximum of the jump function on that finite set and compare it with the supremum.  For the zero
  lemmas use `bddAbove_maxJump`, `le_ciSup`, `ciSup_le`, and
  `ContinuousAt.continuousWithinAt.leftLim_eq`.  Conversely, hnonneg and no upward jump give
  `leftLim f t=f t`; combine `(isCadlag f).isRightContinuous` with
  `continuousAt_iff_continuous_left'_right'` at every time.

ACYCLICITY.  C5 uses `ProductPaths`, `ContinuousEmbedding`, `Measurable`, `Separable`, and
`Probability.WeakConvergence`; C7/C11 use `Restrict`, `Prefix`, and `ContinuousEmbedding`; C33
uses only `Vervaat`/`VervaatRotate` and the càdlàg API; C36 adds `StepApprox` to `Jump`.  None of
these new declarations is an input to an imported module, and no consumer-level theorem is used.

BINDER SCOPE (AUDITOR_RULES).  No integral or sum occurs.  Every `⨆` in the C7 and C11 statements
has its complete distance expression as body, with no `+` or `-` outside that body.  The `-` in
`maxJump` is inside the sealed parenthesized body `max (f t - leftLim f t) 0`. -/

open Filter MeasureTheory Set Topology
open scoped Topology Classical

namespace BGW.Skorokhod

variable {T : ℝ} {E F : Type*} [MetricSpace E] [MetricSpace F]

/-! ### C5 item 4, converse -/

/-- First coordinate of a product-valued càdlàg path. -/
def fstWithCont (f : D T (E × F)) : D T E :=
  ⟨fun t => (f t).1, (isCadlag f).continuous_comp continuous_fst⟩

/-- Split a product-valued path when its second coordinate is continuous.  Outside that locus,
use the constant continuous path `default` as an explicit junk value. -/
noncomputable def splitProdWithCont [Inhabited F] (f : D T (E × F)) :
    D T E × C(Set.Icc (0 : ℝ) T, F) :=
  (fstWithCont f, if h : Continuous (fun t => (f t).2) then
    ⟨fun t => (f t).2, h⟩ else ContinuousMap.const _ default)

/-- Splitting followed by `prodWithCont` is the identity on paths with continuous second
coordinate. -/
theorem prodWithCont_splitProdWithCont [Inhabited F] (f : D T (E × F))
    (hf : Continuous (fun t => (f t).2)) :
    prodWithCont (splitProdWithCont f).1 (splitProdWithCont f).2 = f := sorry

/-- **C5 item 4, converse.**  Convergence in law in `D_T(E × F)`, on the locus where the second
coordinate is continuous, implies convergence in law in `D_T(E) × C([0,T],F)`. -/
theorem tendsto_map_splitProdWithCont [Inhabited F]
    [TopologicalSpace.SeparableSpace E] [TopologicalSpace.SeparableSpace F]
    {μ : ℕ → ProbabilityMeasure (D T (E × F))} {ν : ProbabilityMeasure (D T (E × F))}
    (hlim : Tendsto μ atTop (𝓝 ν))
    (hμ : ∀ n, ∀ᵐ f ∂(μ n : Measure (D T (E × F))), Continuous (fun t => (f t).2))
    (hν : ∀ᵐ f ∂(ν : Measure (D T (E × F))), Continuous (fun t => (f t).2)) :
    Tendsto (fun n => (μ n).map (splitProdWithCont (T := T))) atTop
      (𝓝 (ν.map (splitProdWithCont (T := T)))) := sorry

/-! ### C7 and C11 in continuous path space -/

/-- Restriction of a continuous path to `[0,a]`. -/
def restrictContinuous {a : ℝ} (haT : a ≤ T) (f : C(Set.Icc (0 : ℝ) T, E)) :
    C(Set.Icc (0 : ℝ) a, E) :=
  f.comp ⟨fun t => ⟨t.1, t.2.1, t.2.2.trans haT⟩, by fun_prop⟩

/-- Extend a continuous path on `[0,a]` constantly to `[0,T]`. -/
def extendContinuous {a : ℝ} (ha : 0 ≤ a)
    (f : C(Set.Icc (0 : ℝ) a, E)) : C(Set.Icc (0 : ℝ) T, E) :=
  f.comp ⟨fun t => ⟨min t.1 a, le_min t.2.1 ha, min_le_right _ _⟩, by fun_prop⟩

/-- Stop a continuous path at `a`, with the same clamped-time convention as `Skorokhod.stop`. -/
def stopContinuous (a : ℝ) (f : C(Set.Icc (0 : ℝ) T, E)) : C(Set.Icc (0 : ℝ) T, E) :=
  f.comp ⟨fun t => ⟨max 0 (min t.1 a), le_max_left _ _,
    max_le (t.2.1.trans t.2.2) ((min_le_left _ _).trans t.2.2)⟩, by fun_prop⟩

/-- **C7 in `C_T`.**  Stopping at `a` is controlled by the uniform oscillation after `a`. -/
theorem dist_stopContinuous_le {a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T)
    (f : C(Set.Icc (0 : ℝ) T, E)) :
    dist (stopContinuous a f) f ≤ ⨆ s : {s : Set.Icc (0 : ℝ) T // a ≤ (s : ℝ)},
      dist (f s) (f ⟨a, ha, haT⟩) := sorry

/-- **C11 item 2 in `C_T`.**  Convergence of continuous prefixes and terminal oscillation control
imply convergence in law on the full continuous path space. -/
theorem tendsto_continuous_of_tendsto_restrict_of_oscillation {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] [TopologicalSpace.SeparableSpace E]
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n))
    {Y : (n : ℕ) → Ω n → C(Set.Icc (0 : ℝ) T, E)} (hY : ∀ n, Measurable (Y n))
    {ν : ProbabilityMeasure C(Set.Icc (0 : ℝ) T, E)} (hT : 0 < T) {a : ℕ → ℝ}
    (ha0 : ∀ k, 0 ≤ a k) (haT : ∀ k, a k < T) (hlim : Tendsto a atTop (𝓝 T))
    (hpre : ∀ k, Tendsto (fun n => (μ n).map (restrictContinuous (haT k).le ∘ Y n)) atTop
      (𝓝 (ν.map (restrictContinuous (haT k).le))))
    (hosc : ∀ η > 0, Tendsto (fun k => limsup (fun n => (μ n : Measure (Ω n)).real
      {ω | η < ⨆ s : {s : Set.Icc (0 : ℝ) T // a k ≤ (s : ℝ)},
        dist (Y n ω s) (Y n ω ⟨a k, ha0 k, (haT k).le⟩)}) atTop) atTop (𝓝 0)) :
    Tendsto (fun n => (μ n).map (Y n)) atTop (𝓝 ν) := sorry

/-! ### C33 item 3b: the wrap jump -/

/-- The wrap time `1 - g`, viewed as a point of `[0,1]`. -/
noncomputable def vervaatWrapTime (f : D 1 ℝ) : Set.Icc (0 : ℝ) 1 :=
  Set.projIcc 0 1 zero_le_one (1 - (vervaatTime f : ℝ))

/-- Value of the Vervaat transform at its wrap time. -/
theorem vervaatD_wrap (f : D 1 ℝ) :
    vervaatD f (vervaatWrapTime f) = f ⟨1, zero_le_one, le_rfl⟩ - ⨅ s, f s := sorry

/-- Left limit of the Vervaat transform at its wrap time. -/
theorem leftLim_vervaatD_wrap (f : D 1 ℝ) (hc : 0 < (vervaatWrapTime f : ℝ)) :
    Function.leftLim (vervaatD f) (vervaatWrapTime f) =
      Function.leftLim f ⟨1, zero_le_one, le_rfl⟩ - ⨅ s, f s := sorry

/-- **C33 item 3b.**  The signed jump at the wrap is `f(1) - f(1-)`. -/
theorem vervaatD_wrap_sub_leftLim (f : D 1 ℝ) (hc : 0 < (vervaatWrapTime f : ℝ)) :
    vervaatD f (vervaatWrapTime f) - Function.leftLim (vervaatD f) (vervaatWrapTime f) =
      f ⟨1, zero_le_one, le_rfl⟩ - Function.leftLim f ⟨1, zero_le_one, le_rfl⟩ := sorry

/-- **C33 item 3b, localization** (audit g3, finding 2): away from the wrap time, the jump of the
Vervaat transform at `t > 0` is the jump of `f` at the rotated time `g + t` (mod 1). -/
theorem vervaatD_jump_of_ne_wrap (f : D 1 ℝ) (t : Set.Icc (0 : ℝ) 1) (ht0 : 0 < (t : ℝ))
    (htc : t ≠ vervaatWrapTime f) :
    vervaatD f t - Function.leftLim (vervaatD f) t =
      f (Set.projIcc 0 1 zero_le_one (if (vervaatTime f : ℝ) + t < 1
          then (vervaatTime f : ℝ) + t else (vervaatTime f : ℝ) + t - 1)) -
        Function.leftLim f (Set.projIcc 0 1 zero_le_one (if (vervaatTime f : ℝ) + t < 1
          then (vervaatTime f : ℝ) + t else (vervaatTime f : ℝ) + t - 1)) := sorry

/-! ### C36: attainment and zero largest upward jump -/

/-- **C36, attainment.**  On a nonempty bounded time interval, `maxJump` is attained. -/
theorem exists_eq_maxJump (hT : 0 ≤ T) (f : D T ℝ) :
    ∃ t, max (f t - Function.leftLim f t) 0 = maxJump f := sorry

/-- **C36, continuous paths.**  A continuous path has zero largest upward jump. -/
theorem maxJump_eq_zero_of_continuous {f : D T ℝ} (hf : Continuous f) : maxJump f = 0 := sorry

/-- The exact meaning of `maxJump f = 0`: there are no upward jumps.  Downward jumps are
invisible to `maxJump`. -/
theorem maxJump_eq_zero_iff (f : D T ℝ) :
    maxJump f = 0 ↔ ∀ t, f t ≤ Function.leftLim f t := sorry

/-- **C36 with nonnegative jumps.**  If every jump is nonnegative, vanishing of `maxJump` is
equivalent to continuity. -/
theorem maxJump_eq_zero_iff_continuous_of_leftLim_le (f : D T ℝ)
    (hf : ∀ t, Function.leftLim f t ≤ f t) : maxJump f = 0 ↔ Continuous f := sorry

end BGW.Skorokhod
