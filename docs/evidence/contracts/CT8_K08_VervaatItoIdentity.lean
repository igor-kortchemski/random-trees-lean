import BGW.StableTrees.ForestLocalLimit
import BGW.StableTrees.BridgeProjectiveClose
import BGW.StableTrees.BridgeProjective
import BGW.StableTrees.StableBridgeMinimum
import BGW.StableTrees.StableBridgeUniformMinimum
import BGW.StableTrees.UnitExcursionLaw
import BGW.StableTrees.StableLaw
import BGW.Probability.WeakConvergence
import BGW.StableTrees.Attraction.Defs
import BGW.Skorokhod.VervaatStep
import BGW.Skorokhod.VervaatMeasurable
import BGW.Skorokhod.VervaatContinuity
import BGW.Skorokhod.MeasurableMaps
import BGW.Skorokhod.MeasurableLaws
import BGW.Skorokhod.RestrictContinuity
import BGW.LocallyFinite.WalkLaw
import BGW.LocallyFinite.ExcursionLaw
import BGW.Tree.Decode
import BGW.StableTrees.DiscreteBridge
import BGW.StableTrees.ExactPrefix

/-! Contract probe for CT8 node K08 = classical input C35 (`r5-ct8-blueprint/blueprint.md` K08,
finding 6 of `AUDIT.md`): the Vervaat image of the stable bridge is the normalized Itô excursion,
`(stableBridgeLaw θ).map vervaatD = levyExcLaw θ`.

TRUTH.  The theorem is the continuum identity "Vervaat transform of the bridge = normalized
excursion" (Chaumont; Le Gall, Random trees and applications, §2.3 for `θ = 2`; Bertoin Ch. VIII
for stable processes).  It is proved here by identifying two limits of ONE discrete object, and
by NO other route: the library has constructed `stableBridgeLaw θ` (CT6) and `levyExcLaw θ`
(unit excursion law, O01/Itô) independently, and C35 is not among their definitions.
ONE witness: `w : DiscreteWitness θ` fixes `(μ, B, h : StableDomain μ θ B)` once
(`exists_discreteWitness`, from `exists_stableDomain` and `Attraction.sizeProb_pos_iff`) and one
unbounded admissible sequence `q`, `Admissible μ (q k)`.  The same sequence feeds
(K06) `tendsto_walkBridgeLaw` + the cyclic law `map_vervaatD_walkBridgeLaw`: the exact-size
walk laws `E_k = exactWalkLaw μ B (q k)` converge to `vervaatImage θ` (full path, CMT at the
a.s. continuity points of `vervaatD`), and (K07) `tendsto_exactWalkLaw_prefix`: the same `E_k`
have prefixes on `[0,a]` converging to the unit-excursion prefix.  Hence the prefixes of
`vervaatImage θ` and `levyExcLaw θ` agree at every `a` where `vervaatImage θ` has no fixed
discontinuity (this avoids assuming that it has none).  Those `a` are cocountable
(`countable_fixedDiscontinuities`), hence dense.  Terminal coordinate: the paths of `E_k` end at
`-1/B n` (vanishing, J1), but the limit paths are NOT assumed to end at `0`; instead both
`vervaatImage θ` and `levyExcLaw θ` are a.s. `0` at time `1`
(`stableBridgeLaw_ae_vervaat_endpoints`, `levyExcLaw_endpoints_pos`), which pins the
terminal coordinate in the finite-dimensional uniqueness `S.ext_of_finiteDimensional` (dense
set of times containing `1`), see `eq_of_restrict_eq_of_terminal_zero`.

ACYCLICITY (finding 6).  Suppliers: K06, K07 (and through them K02/K03/K05b), CT5/CT6 bridge,
Vervaat continuity (`stableBridgeLaw_ae_continuousAt_vervaatD`), excursion theory.  This node
does NOT use C29, C30, C35, or any article theorem; K05, K06 and K07 must not import K08.

PROOF PLAN.  (1) `exists_discreteWitness`: `exists_stableDomain hθ`; `sizeProb_pos_iff` gives
`N` with `P(ζ = n) ≠ 0 ↔ d ∣ n - 1` for `n ≥ N`, take `q k = 1 + d * (N + k + 1)` with `d = Scalar.latticeSpan μ`
(`Scalar.latticeSpan_pos` for unboundedness and `N ≤ q k`; `d ∣ q k - 1` for
`sizeProb_pos_iff`).  (2)
`tendsto_exactWalkLaw_vervaatImage`: K06 convergence of bridges, `vervaatD` continuous at
the bridge law a.e., continuous mapping (`BGW.Probability.tendsto_map_of_ae_continuousAt`
from `BGW.Probability.WeakConvergence`, with `measurable_vervaatD.aemeasurable` at each discrete
law and `stableBridgeLaw_ae_continuousAt_vervaatD hθ` at the limit; `NoFixedDiscontinuity` is
converted to the a.e. proposition), and the pathwise cyclic law identifying the transformed
walk bridge with `exactWalkLaw`.  (3) `restrictLaw_vervaatImage_eq_unitPrefix`: for the SAME witness `w`, apply
`continuousAt_restrict` (continuity at `a` a.e.) to (2) and use K07; Hausdorff uniqueness of
weak limits.  (4) `countable_fixedDiscontinuities`: standard (the set of times where a
probability law on `D` charges discontinuity is countable: for each `ε,η` only finitely many
`t` with `P(|Δf(t)| > ε) > η`, via disjointness of pairs of jump times in `Q`-many windows /
Billingsley, Section 13).  (5) `eq_of_restrict_eq_of_terminal_zero` via `ext_of_finiteDimensional`
with `S = A ∪ {1}`, using that evaluation at `1` is a.s. the constant `0`: the finite-dimensional
law at times `s ⊆ A ∪ {1}` is the image of the prefix law at `max (s ∩ A)` under the map
adjoining the constant coordinate `0` at time `1` (no independence is asserted).  (6) Assemble.

AMBIGUITIES RESOLVED.  `Measure.map vervaatD` is the total push-forward of the measurable map
`vervaatD` (`measurable_vervaatD`); no hypothesis `θ ≠ 2` (the proof is uniform in `1 < θ ≤ 2`,
Brownian case included, giving `levyExcLaw 2` the normalized excursion).  `hθ` is the sealed
`1 < θ ∧ θ ≤ 2`.  Times `a` are `ℝ≥0` in `Ioo 0 1`.

BINDER SCOPE (AUDITOR_RULES): no integral or big operator followed by `+`/`-` occurs. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteBridge (offspringVec vecPath conditionedVecOrJunk walkBridgeLaw exactWalkLaw offspringVec_countBridges_ne_zero offspringVec_countExcursions_ne_zero restrictLaw)

namespace BGW.StableTrees.VervaatIto

open BGW BGW.Skorokhod BGW.Probability.RealWalk

/-! ## 1. Shared discrete carriers (copied from contracts K06/K07, not part of this contract) -/

instance (μ : PMF ℕ) (n : ℕ) : IsProbabilityMeasure (offspringVec μ n) := by
  unfold offspringVec
  infer_instance

/-- (K06 statement) **Walk bridge invariance principle**. -/
theorem tendsto_walkBridgeLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, Admissible μ (q k)) :
    Tendsto (fun k => walkBridgeLaw μ B (q k) (hq k)) atTop (𝓝 (stableBridgeLaw θ)) :=
  sorry

/-- (K06 statement) **Cyclic law**: the Vervaat image of the discrete walk bridge is the
exact-size Łukasiewicz path law. -/
theorem map_vervaatD_walkBridgeLaw {μ : PMF ℕ} {B : ℕ → ℝ} {n : ℕ} (hn : Admissible μ n)
    (hB : 0 < B n) :
    ((walkBridgeLaw μ B n hn : ProbabilityMeasure (D 1 ℝ)) : Measure (D 1 ℝ)).map vervaatD =
      ((exactWalkLaw μ B n hn : ProbabilityMeasure (D 1 ℝ)) : Measure (D 1 ℝ)) := sorry

-- Definitional ADAPTATION of contract CT8_K07_ExactSizePrefixes `tendsto_exactWalkLaw_prefix`
-- (not a literal copy): K07's `exactWalkPrefixLaw` is unfolded to `restrictLaw ... exactWalkLaw`.
/-- (K07 statement) **Exact-size walk prefixes**: the restriction of the exact-size path law to
`[0,a]` converges to the unit-excursion prefix. -/
theorem tendsto_exactWalkLaw_prefix {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, Admissible μ (q k))
    (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    Tendsto (fun k => restrictLaw a ha.2.le (exactWalkLaw μ B (q k) (hq k))) atTop
      (𝓝 ((unitExcursionLaw θ).map (excursionRestrict a))) := sorry

/-! ## 2. The single witness -/

/-- **One witness** for the whole identification: an offspring law, a norming, the stable
domain proof and an unbounded admissible sequence of sizes, all chosen once. -/
structure DiscreteWitness (θ : ℝ) where
  /-- The offspring law. -/
  μ : PMF ℕ
  /-- The norming sequence. -/
  B : ℕ → ℝ
  /-- Attraction to the spectrally positive `θ`-stable law. -/
  h : StableDomain μ θ B
  /-- The sample sizes. -/
  q : ℕ → ℕ
  /-- The sizes are unbounded. -/
  hqtop : Tendsto q atTop atTop
  /-- The sizes are admissible: `P(ζ = q k) ≠ 0`. -/
  hq : ∀ k, Admissible μ (q k)

/-- The witness exists for every `1 < θ ≤ 2` (`exists_stableDomain`, `sizeProb_pos_iff`:
choose `q k = 1 + d * (N + k + 1)`, `d = Scalar.latticeSpan μ`, beyond the lattice
threshold `N`; then `q k ≡ 1 mod d` and `N ≤ q k`). -/
theorem exists_discreteWitness {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) : Nonempty (DiscreteWitness θ) :=
  sorry

/-! ## 3. The Vervaat image and the full-path limit -/

/-- The Vervaat image `(stableBridgeLaw θ).map vervaatD` as a probability measure. -/
noncomputable def vervaatImage (θ : ℝ) : ProbabilityMeasure (D 1 ℝ) :=
  (stableBridgeLaw θ).map vervaatD

/-- **Full-path limit of the transformed walk bridge**: along the witness the exact-size walk
laws converge to the Vervaat image of the stable bridge.  K06 convergence, the a.s.
continuity of `vervaatD` at the bridge (`stableBridgeLaw_ae_continuousAt_vervaatD`), the
continuous mapping theorem, and the cyclic law `map_vervaatD_walkBridgeLaw`.  The terminal
value of the paths is `-1/B n`; nothing is assumed about the limit at time `1`. -/
theorem tendsto_exactWalkLaw_vervaatImage {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (w : DiscreteWitness θ) :
    Tendsto (fun k => exactWalkLaw w.μ w.B (w.q k) (w.hq k)) atTop (𝓝 (vervaatImage θ)) :=
  sorry

/-! ## 4. Prefixes on a dense set of times and the terminal coordinate -/

/-- The time `a ∈ [0,1]` as a point of the domain of `D 1 ℝ`. -/
def timePoint (a : ℝ≥0) (ha : a ≤ 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨(a : ℝ), a.coe_nonneg, by exact_mod_cast ha⟩

/-- `P` has no fixed discontinuity at `t`: almost every path is continuous at `t`. -/
def NoFixedDiscontinuity (P : ProbabilityMeasure (D 1 ℝ)) (t : Set.Icc (0 : ℝ) 1) : Prop :=
  (P : Measure (D 1 ℝ)) {f | ¬ ContinuousAt f t} = 0

/-- A probability law on `D[0,1]` has at most countably many fixed discontinuities. -/
theorem countable_fixedDiscontinuities (P : ProbabilityMeasure (D 1 ℝ)) :
    {t : Set.Icc (0 : ℝ) 1 | ¬ NoFixedDiscontinuity P t}.Countable := sorry

/-- A dense set of cutoff times outside the fixed discontinuities of the Vervaat image
(`countable_fixedDiscontinuities` and density of the complement of a countable set). -/
theorem exists_dense_noFixedDiscontinuity_times (θ : ℝ) :
    ∃ A : Set ℝ≥0, (∀ a ∈ A, a ∈ Ioo (0 : ℝ≥0) 1) ∧
      Ioo (0 : ℝ) 1 ⊆ closure (((↑) : ℝ≥0 → ℝ) '' A) ∧
      ∀ a ∈ A, ∀ ha : a ≤ 1, NoFixedDiscontinuity (vervaatImage θ) (timePoint a ha) :=
  sorry

/-- **Equality of prefixes** (K06 + K07 on the same witness `w`, which is exposed here and passed
to `tendsto_exactWalkLaw_vervaatImage hθ w`): at every `a ∈ (0,1)` where the
Vervaat image has no fixed discontinuity, its restriction to `[0,a]` is the unit-excursion
prefix.  The same sequence `E_k = exactWalkLaw` converges to both (CMT for `restrict`
at continuity points and K07). -/
theorem restrictLaw_vervaatImage_eq_unitPrefix {θ : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (w : DiscreteWitness θ) (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1)
    (hcont : NoFixedDiscontinuity (vervaatImage θ) (timePoint a ha.2.le)) :
    restrictLaw a ha.2.le (vervaatImage θ) =
      (unitExcursionLaw θ).map (excursionRestrict a) := sorry

/-- Both laws vanish a.s. at the terminal time (`stableBridgeLaw_ae_vervaat_endpoints`). -/
theorem ae_vervaatImage_terminal_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(vervaatImage θ : Measure (D 1 ℝ)), f ⟨1, zero_le_one, le_rfl⟩ = 0 := sorry

/-- **Uniqueness with the terminal coordinate**: two laws on `D[0,1]` that agree on the prefixes
`[0,a]` for `a` in a set of times dense in `(0,1)`, and are both a.s. `0` at time `1`, are equal
(`ext_of_finiteDimensional` with the dense set `A ∪ {1}`). -/
theorem eq_of_restrict_eq_of_terminal_zero (P Q : ProbabilityMeasure (D 1 ℝ))
    (A : Set ℝ≥0) (hA : ∀ a ∈ A, a ∈ Ioo (0 : ℝ≥0) 1)
    (hdense : Ioo (0 : ℝ) 1 ⊆ closure (((↑) : ℝ≥0 → ℝ) '' A))
    (h : ∀ (a : ℝ≥0) (ha : a ∈ A), restrictLaw a (hA a ha).2.le P = restrictLaw a (hA a ha).2.le Q)
    (hP : ∀ᵐ f ∂(P : Measure (D 1 ℝ)), f ⟨1, zero_le_one, le_rfl⟩ = 0)
    (hQ : ∀ᵐ f ∂(Q : Measure (D 1 ℝ)), f ⟨1, zero_le_one, le_rfl⟩ = 0) : P = Q := sorry

/-! ## 5. C35 -/

/-- **C35, probability-measure form**: the Vervaat image of the stable bridge is the unit
excursion law. -/
theorem vervaatImage_eq_levyExcLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    vervaatImage θ = levyExcLaw θ := sorry

/-- **C35 (K08 main theorem)**: for `1 < θ ≤ 2`, the Vervaat transform of the stable bridge has
the law of the normalized Itô excursion (`levyExcLaw θ`).  Statement as in the blueprint. -/
theorem map_vervaatD_stableBridgeLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ((stableBridgeLaw θ : ProbabilityMeasure (D 1 ℝ)) : Measure (D 1 ℝ)).map vervaatD =
      (levyExcLaw θ : Measure (D 1 ℝ)) := sorry

end BGW.StableTrees.VervaatIto
