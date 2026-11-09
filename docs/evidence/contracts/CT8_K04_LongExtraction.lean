import BGW.Skorokhod.ExitPartition
import BGW.Skorokhod.CompleteMetricSpace
import BGW.StableTrees.WalkPassage
import BGW.StableTrees.StableExcursionSupport
import BGW.StableTrees.MarkedExcursions
import BGW.ContinuumTrees.ExcursionCarrier
import BGW.StableTrees.LongExtractionDefs

/-! Contract probe for CT8 node K04 (R5 blueprint §3, audit finding 1 and "first nodes" item 2):
deterministic extraction of the FIRST LONG EXCURSION from a skip-free walk path, with endpoint
and stopped-cut convergence.  K04 is purely deterministic (paths in `D (M : ℝ) ℝ` and `DLoc`);
the a.s. supplier is K05 (`CT8_K05_FirstLongMark.lean`) and is NOT assumed here.

DEFINITIONS.  Continuum side (`f : DLoc`, sealed `ST.passageTime`, `passageTimeMinus`,
`passageJumpSet`, `reflectedFrom`, `jumpExcursion`): `longLabelSet f = {x ∈ J(f) | ζ_x > 1}`
with `ζ_x = T_x - T_{x-}`, `firstLongLabel f = sInf` of it (junk `0` if empty), the selected
interval `(g,d) = (T_{L-}, T_L)`.  Discrete side (increments `ω : ℕ → ℝ`, `W = partialSum ω`):
ladder times `L_r = (walkHitTime r ω).toNat` (weak hit of `(-∞,-r]`; equal to the exact hit
by skip-freeness), block `r` has size `L_{r+1} - L_r`, the first LONG block is the least `r`
with size `≥ n`.  Endpoints `(L_r/n, L_{r+1}/n)`.  The extracted cut path uses the block
increments with the LAST step (the `-1`) replaced by `0`, i.e. `t ↦ (W_{L_r+⌊nt⌋} - W_{L_r})/b`
for `t < (L_{r+1}-L_r-1)/n`, extended by the constant `0`: this is the translated block path
extended by zero, whose distance to the sealed `cutPath` is at most `1/b`.

THE GOOD-PATH PREDICATE (audit finding 1, exact form).  `GoodLongExtractionPath M f` is a
STRUCTURE of geometric facts about `f`; it never mentions convergence of anything.
(i) `f 0 = 0`, no negative jumps, running infimum `I` continuous;
(ii) every passage time finite, creeping `f (T_x) = -x`, `x ↦ T_x` strictly increasing;
(iii) for EVERY jump level `x ∈ J(f)` (`IsRegularExcursionLevel`): the cut `(T_{x-},T_x)` is
valid, the reflected path `R = reflectedFrom 0 f` is continuous at both endpoints (zero
endpoints), for every compact `[a,b] ⊂ (T_{x-},T_x)` there is `c > 0` with BOTH `R t ≥ c` AND
`R(t-) ≥ c` on `[a,b]` (left limits are NOT implied by `IsExcursionInterval`, which gives only
`R > 0`), and each side has a strict record-level bracket: for every `η > 0` there are
non-jump levels `x₁ < x₂ < x` with `T_{x₁} > T_{x-} - η`, `T_{x₂} < T_{x-}` (before the start)
and non-jump levels `x < x₁ < x₂` with `T_{x₁} > T_x`, `T_{x₂} < T_x + η` (after the end);
(iv) no jump level has lifetime exactly `1`; (v) the long label set has a least element `L`
and its end `T_L < M` (finite source horizon).
Quantifying (iii) over all jump levels is what matches ALL excursions of length `≥ η` before
`T_L` (finitely many, disjoint intervals, lifetimes avoid the threshold gap by (iv)).
`GoodLongExtractionCutPath M T f` adds `ContinuousAt (cut path) T`.

TRUTH CHECK (probabilistic sanity, not proved here).  (i),(ii): sealed
`ae_runningInf_continuous_antitone_tendsto`, `ae_leftLim_le_stableLocalLaw`,
`ae_passageTime_eq_firstPassageBelow`, `ae_creeping_passageTime`,
`strictMono_passageTime_of_creeping`; (iii) cut validity/continuity at the end/`ae_jump_window_inf`
(`StableExcursionSupport*`, `MarkedExcursionsSupport`); the brackets follow from strict
monotonicity of `T` and `T_{x-} = sup_{y<x} T_y` plus countability of `J(f)`; the left-limit
interior bound is the generalized-minimum argument of finding 1 (the real content, K05);
(iv) sealed `excursionMeasure_lifetime_eq_zero` + Poisson (K05).  Conclusions: with mesh `1/n`
and downward step `1/B_n → 0`, J1 convergence of the walks on `[0,M]` to a path `f` satisfying
(i)-(v) forces convergence of the selected endpoints and of the stopped cut at every `T` where
the limit cut is continuous.  A blanket continuity statement of extraction on all of `D` is
FALSE (a limit with a lifetime-1 excursion, a jump start, or a touch of the minimum inside an
excursion breaks it); this is why every fact (i)-(v) is a hypothesis.

PROOF PLAN.  (1) `tendsto_ladderTime_of_not_mem_passageJumpSet`: for a non-jump level `x` with
`T_x < M`, `L_{⌈xB_n⌉}/n → T_x` from J1 convergence, creeping, strict monotone `T` and
continuity of `I` (hit time of a level the limit crosses strictly is continuous).  (2) Bracketing
by two non-jump levels on each side of `L` puts the discrete selected block start/end within
`η` of `g`/`d`, using the interior bounds on `R` and `R(·-)` (a block cannot contain a record
drop, and a compact interior is matched inside a single discrete block).  (3) Match all
excursions of length at least `1 - δ` before the selected end.  For excursions strictly
preceding the selected one, use `noLifetimeOne` and finiteness to choose a uniform gap below 1,
then exclude an earlier discrete long block; the selected excursion has lifetime `> 1` and its
matching block is eventually long.  `passageZero` rules out an initial discrete plateau.
(4) Align endpoints by a J1 time change, subtract the start value, extend by zero (the last
`-1/b` is dropped by the
definition of the cut increments).  Size 1400-2600 lines.

BINDER SCOPE (AUDITOR_RULES): there is no integral or big operator followed by `+`/`-` in
this file; the only big operator is inside the sealed `partialSum`. -/

open Filter Topology
open scoped NNReal
open BGW.Skorokhod BGW.Probability.RealWalk

namespace BGW.StableTrees

-- Definitions: `BGW/StableTrees/LongExtractionDefs.lean` (verbatim from this contract).

/-! ### Theorems -/

/-- **Ladder times converge at non-jump levels.**  Level `x` is read at index `⌈x B_n⌉`. -/
theorem tendsto_ladderTime_of_not_mem_passageJumpSet {B : ℕ → ℝ}
    (hB : Tendsto B atTop atTop) {M : ℝ≥0} (ω : ℕ → ℕ → ℝ)
    (hω : ∀ n i, IsSkipFreeIncrement (ω n i)) {f : DLoc} (hf : GoodLongExtractionPath M f)
    (hu : Tendsto (fun n => realStepPath (M : ℝ) n (B n) (ω n)) atTop
      (𝓝 (DLoc.restrict M f)))
    {x : ℝ≥0} (hx : x ∉ passageJumpSet f) (hxM : passageTime x f < M) :
    (∀ᶠ n in atTop, walkHitTime ⌈(x : ℝ) * B n⌉₊ (ω n) ≠ ⊤) ∧
      Tendsto (fun n => (ladderTime (ω n) ⌈(x : ℝ) * B n⌉₊ : ℝ) / n) atTop
        (𝓝 ((passageTime x f : ℝ≥0) : ℝ)) := by
  sorry

/-- **Endpoint matching** (finding 1): the first long block's endpoints converge to the
selected excursion interval `(T_{L-}, T_L)`.  No convergence of extraction is assumed. -/
theorem tendsto_firstLongBlock_endpoints {B : ℕ → ℝ} (hB : Tendsto B atTop atTop)
    {M : ℝ≥0} (ω : ℕ → ℕ → ℝ) (hω : ∀ n i, IsSkipFreeIncrement (ω n i))
    {f : DLoc} (hf : GoodLongExtractionPath M f)
    (hu : Tendsto (fun n => realStepPath (M : ℝ) n (B n) (ω n)) atTop
      (𝓝 (DLoc.restrict M f))) :
    Tendsto (fun n => extractionEndpoints n (ω n)) atTop (𝓝 (firstLongEnds f)) := by
  sorry

/-- **Stopped-cut convergence**: the whole triple `(g_n, d_n, cut_n)` converges, in
`ℝ × ℝ × D T ℝ`, for every cutoff `T` at which the limit cut is continuous.  The cut is the
translated block path, extended by zero. -/
theorem tendsto_firstLongBlock_cut {B : ℕ → ℝ} (hB : Tendsto B atTop atTop)
    {M T : ℝ≥0} (ω : ℕ → ℕ → ℝ) (hω : ∀ n i, IsSkipFreeIncrement (ω n i))
    {f : DLoc} (hf : GoodLongExtractionCutPath M T f)
    (hu : Tendsto (fun n => realStepPath (M : ℝ) n (B n) (ω n)) atTop
      (𝓝 (DLoc.restrict M f))) :
    Tendsto (fun n => extractionTriple (B n) n T (ω n)) atTop (𝓝 (longCutTriple T f)) := by
  sorry

end BGW.StableTrees
