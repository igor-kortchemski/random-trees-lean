import BGW.StableTrees.UnitExcursionLaw
import BGW.StableTrees.ExcursionMeasure
import BGW.ContinuumTrees.ExcursionCarrier
import BGW.StableTrees.DiscreteForest
import BGW.StableTrees.StableLocalLaw
import BGW.StableTrees.SupremumLocalTimePublic
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import BGW.StableTrees.HeightProcess
import BGW.StableTrees.HeightBridges
import BGW.StableTrees.HeightContinuity

/-! Contract probe for CT8 node K11 (`r5-ct8-blueprint/blueprint.md` K11): tightness of the
normalized forest height by discrete regeneration (Duquesne-Le Gall 2002, Ch. 2, Thms
2.3.1-2.3.2, Lemmas 2.3.3-2.3.5), and the joint walk/height limit on every horizon.

OBJECTS.  K02 (sealed): `offspringSeqLaw μ`, `walk`, `forestHeight ω k = #{j < k | W_j ≤ W_l on
[j,k]}`, `forestHeightLin` (linear interpolation of heights at integer times, NOT of the walk),
`forestHeightPath B n T ω = t ↦ (B_n/n) forestHeightLin ω (n t)` in `C([0,T], ℝ)`,
`forestWalkPath`, `forestPairPath`.  New: `heightOscillation B n T δ ω`, the modulus of
continuity of the normalized interpolated height on `[0,T]`; `maxHeightJump B n T ω`, the
normalized largest adjacent height jump before `⌊nT⌋ + 1`.  The limit pair is the H03 graph
`f ↦ (DLoc.restrict T f, heightPrefix θ T (DLoc.restrict T f))` under `stableLocalLaw θ`
(H03 not yet sealed: `heightPrefix` and the definitions it needs are copied below).

TRUTH CHECK.  (1) Regeneration (deterministic, SEALED in K02 as `shiftedHeight_eq`, with the
strong-Markov form at stopping times in K02 as well): for every `ω, m, k`,
`H_{m+k} - min_{m ≤ i ≤ m+k} H_i = H'_k` with `H'` the height of `shiftSeq m ω`.  Write
`H_i = A(i) + H'_{i-m}` for `i ≥ m`, where `A(i)` counts the `j < m` that are weak records seen
from `i`; `A` is nonincreasing; at the first time `i*` where `W` attains its minimum over
`[m, m+k]`, `H'_{i*-m} = 0` and `A(i*) = A(m+k)`; hence the minimum is `A(m+k)`.  (2) Modulus:
DLG's theorem for the height process of a critical BGW forest in the stable domain with the
extinction condition, which K10 supplies (`tendsto_extinction_pow_floor`); the limit is the
continuous H03 height, so the modulus tends to `0`.  (3) Adjacent jumps: the sup runs over `k ≤
⌊nT⌋`, which includes the jump at `⌊nT⌋`, so use
`maxHeightJump B n T ω ≤ heightOscillation B n (T + 1) (1/n) ω` (`n ≥ 1`) and (2) at horizon
`T + 1`.
(4) Tightness in `C([0,T], ℝ)`: Arzelà-Ascoli from the modulus and `H_0 = 0` (the modulus
is a limsup, so combine eventual tightness with the finitely many first laws).  The running
maximum `(B_n/n) max_{k ≤ ⌊nT⌋} H_k` is then tight (consumed by K12/K13).  (5) Joint law:
tightness of both coordinates (CT5 walk tightness, (4)) and K09's walk/height
finite-dimensional limit identify every subsequential limit with the H03 graph law, using
H03's graph identity and `ae_heightLoc_eq_height`.

PROOF PLAN (blueprint K11, DLG stopping-time route; NOT an all-moments bound).  At an integer
stopping time `τ`, (1) makes successive upcrossings by `η` above the running height minimum
regenerate with iid interarrival times.  With `τ_η` the first upcrossing and `T_l` the end of
`l` trees: `P(τ_η/n ≤ x) ≤ ⌊aB_n⌋ s(⌊ηn/B_n⌋) + P(T_{⌊aB_n⌋}/n ≤ x)`; take `limsup n`, then
`x ↓ 0` (`tendsto_walkPassageLaw`, `passageLaw_Iic_zero`), then `a ↓ 0` (K10).  An exponential
Markov bound on the sum of `L` iid gaps makes the number of upcrossings before `T` tight; a
union bound over the first `L` gaps controls short gaps.  Combine with K09 on a deterministic
grid and H03 continuity to exclude spikes and dips between grid points.  Size 1800-3200.
RISK: treating the height as Markov instead of the regenerated height above its minimum; a
naive union bound over `n` possible spikes is insufficient.

ACYCLICITY.  Suppliers: K02 (incl. `shiftedHeight_eq`), K09, K10, H02, H03, CT5, CT6
(`WalkPassage`).  No K12-K19.

BINDER SCOPE (AUDITOR_RULES): the suprema in `heightOscillation` have the whole `if` as body;
`maxHeightJump` applies `Finset.sup` to a lambda; nothing follows a big operator. -/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees

end BGW.StableTrees

namespace BGW.StableTrees.HeightTightness

open BGW.StableTrees.DiscreteForest

/-! ### Modulus of continuity -/

/-- The modulus of continuity at scale `δ` of the normalized interpolated height on `[0,T]`. -/
noncomputable def heightOscillation (B : ℕ → ℝ) (n : ℕ) (T δ : ℝ) (ω : ℕ → ℕ) : ℝ :=
  ⨆ s : Set.Icc (0 : ℝ) T, ⨆ t : Set.Icc (0 : ℝ) T,
    if |(s : ℝ) - t| ≤ δ then
      |B n / n * forestHeightLin ω (n * s) - B n / n * forestHeightLin ω (n * t)|
    else 0

/-- The normalized largest adjacent height jump before index `⌊n T⌋ + 1`. -/
noncomputable def maxHeightJump (B : ℕ → ℝ) (n : ℕ) (T : ℝ) (ω : ℕ → ℕ) : ℝ :=
  B n / n * (((Finset.range (⌊(n : ℝ) * T⌋₊ + 1)).sup
    (fun k => ((forestHeight ω (k + 1) : ℤ) - forestHeight ω k).natAbs) : ℕ) : ℝ)

theorem measurable_heightOscillation (B : ℕ → ℝ) (n : ℕ) (T δ : ℝ) :
    Measurable (heightOscillation B n T δ) := sorry

/-- **Height modulus** (DLG Theorem 2.3.1 route). -/
theorem forestHeight_modulus {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {T η : ℝ} (hT : 0 < T) (hη : 0 < η) :
    Tendsto (fun δ : ℝ => limsup (fun n : ℕ =>
        ((offspringSeqLaw μ : Measure (ℕ → ℕ))).real {ω | η < heightOscillation B n T δ ω})
        atTop) (𝓝[>] 0) (𝓝 0) := sorry

/-- The largest adjacent height jump vanishes in probability on the height scale. -/
theorem maxHeightJump_tendstoInMeasure {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {T : ℝ} (hT : 0 < T) :
    TendstoInMeasure (offspringSeqLaw μ : Measure (ℕ → ℕ))
      (fun n ω => maxHeightJump B n T ω) atTop (fun _ => (0 : ℝ)) := sorry

/-! ### Tightness and the joint limit -/

/-- **Running maximum** of the normalized height is tight (`sup H / n = O_P(1/B_n)`, used by
K12/K13). -/
theorem forestHeight_sup_tight {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {T : ℝ} (hT : 0 < T) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, limsup (fun n : ℕ => ((offspringSeqLaw μ : Measure (ℕ → ℕ))).real
      {ω | M < B n / n * (((Finset.range (⌊(n : ℝ) * T⌋₊ + 1)).sup
        (fun k => forestHeight ω k) : ℕ) : ℝ)}) atTop ≤ ε := sorry

/-- The laws of the normalized height paths on `[0,T]` are tight. -/
theorem isTightMeasureSet_forestHeightLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (T : ℝ≥0) :
    IsTightMeasureSet (Set.range fun n : ℕ =>
      ((offspringSeqLaw μ).map (forestHeightPath B n T) :
        Measure C(Set.Icc (0 : ℝ) (T : ℝ), ℝ))) := sorry

/-- **Joint walk/height limit** on every positive horizon: the forest pair converges to the H03
graph of the stable process. -/
theorem tendsto_forestPairLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {T : ℝ≥0} (hT : 0 < T) :
    Tendsto (fun n : ℕ => (offspringSeqLaw μ).map (forestPairPath B n T)) atTop
      (𝓝 ((stableLocalLaw θ).map
        (fun f : DLoc => (DLoc.restrict T f, heightPrefix θ T (DLoc.restrict T f))))) := sorry

end BGW.StableTrees.HeightTightness
