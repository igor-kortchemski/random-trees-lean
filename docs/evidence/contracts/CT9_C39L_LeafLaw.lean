import BGW.ContinuumTrees.LeafMeasure
import BGW.ContinuumTrees.ContourAdapters

/-! Contract probe for CT9 node C39L: the law-level form of `CLASSICAL_THEORY_INPUTS.md` C39
("Uniform leaf measure versus uniform vertex measure"), coverage row C39.g5 of
`.orchestration/coverage/part3_C27-C39.md` (OPEN, "true gap in the generic CT9 scope").
Suggested maintained module: `BGW/ContinuumTrees/LeafLawConvergence.lean` (new; it must also be
added to the aggregator `BGW/ContinuumTrees.lean`), namespaces `BGW.MetricMeasure` (one generic
lemma), `BGW.ContinuumTrees.LeafMeasure` (leaf statements, the namespace of `leafMass`) and
`BGW.ContinuumTrees.FiniteTree` (one vertex statement, the namespace of C38).

This is the GENERIC library theorem of roadmap CT9, not the article's leaf-conditioned
application: `cor_Lambda` (discrepancy) and 5.9(ii) (contour tightness) later discharge the
hypotheses `hleaf` and `hlim` below; that specialization stays article-side (C39.c, C39.c',
C39.app).

SOURCE (C39(a), last bullet).  "Corollary 3.3 (`cor_Lambda`, proved) makes δ → 0 in
probability.  The tightness of `(B_ζ/ζ)H_{ζ·}` in C (5.9(ii)) makes `ω_H(δ)` → 0.  BGW's
perturbation lemma (C10(1)) then transfers C38 to the leaf measure."  Here δ bounds the index
displacement `sup_t |Λ^{−1}(λt) − ζt|/ζ` (`Λ^{-1}(j)` = DFS index of the `j`-th leaf, `λ` leaves,
`ζ` vertices).  Read as: under the C38 hypotheses plus "leaf-index discrepancy → 0 in
probability", the rescaled rooted trees carrying the uniform LEAF measure converge in law, in
rooted GHP, to the same limit `ν.map Coding.rootedMeasuredGHSpace` as with the vertex measure.

DEFINITIONS.  Sealed: `FiniteTree.mass t` (uniform on `Vertex t`), `rootedCompactMeasuredSpace t`
(rooted at `FiniteTree.root t`, the empty address), `LeafMeasure.leafMass t`
(`(numLeaves t)⁻¹ • ∑_{k < numLeaves t} δ_{leafVertex t k}`, a probability measure by the
sealed instance, `numLeaves_pos`), `leafIndex t k` (DFS index of the `k`-th leaf, junk `0` only
for `k ≥ numLeaves t`, never used below), `rank N s = min ⌊N s⌋₊ (N - 1)` (the quantile
convention of C39.g2), `FiniteTree.sampleVertex t s` (vertex number `rank t.size s` in DFS
order, law `mass t`: `map_sampleVertex_volume`), `RootedMeasuredGHSpace.scale`,
`Coding.rootedMeasuredGHSpace`.  New:
* `leafLaw t : ProbabilityMeasure (Vertex t)`: `leafMass t` bundled (`⟨leafMass t, inferInstance⟩`).
* `leafCompactMeasuredSpace t := CompactMeasuredSpace.of (Vertex t) (leafLaw t)` and
  `leafRootedCompactMeasuredSpace t` (same carrier, same graph metric, same root `root t` as
  `rootedCompactMeasuredSpace t`; only the measure changes).  Exactly the pattern of
  `FiniteTree.compactMeasuredSpace` / `rootedCompactMeasuredSpace`.
* Leaf-index discrepancy event (inline, no definition): `∃ k < numLeaves t,
  ε < |leafIndex t k / t.size − k / numLeaves t|`, i.e. `ε < max_k |…|`.  Probabilities use
  `Measure.real` of the set, as `hratio` in C38 (`tendsto_rooted_laws_of_contour`): no
  measurability of the event is required, and for measurable trees it is the usual probability.

TRUTH CHECK.
(1) Scaling of the Lévy–Prokhorov distance (the trap of item (ii)).  LP is NOT homogeneous: the
    LP distance for `c·d` is at most `max c 1` times the `d` distance
    (`levyProkhorovDist_map_le_mul`), useless for `c = (b n)⁻¹ → 0` since the unscaled bound
    `2ω` of `levyProkhorovDist_mass_leafMass_le` is of order `b n`.  What scales is a COUPLING:
    if `dist (F s) (G s) ≤ r` for all `s`, then in the metric `c·d` the distance is `≤ c r`
    and `levyProkhorovDist_map_le_of_dist_le` gives LP `≤ c r`.  Hence the pointwise coupling
    bound `dist_sampleVertex_leafVertex_le` (unscaled `2ω`) is stated separately, and the
    scaled bound `dist_scale_leaf_vertex_le` uses the oscillation `ω` of the SCALED contour
    `c • t.contourFunction` (equivalently `c` times the unscaled oscillation): conclusion `2ω`.
(2) Measure change on one carrier: rooted GHP between `(X, μ, x)` and `(X, ν, x)` is at most
    `levyProkhorovDist μ ν` (identity embeddings into `X`: root distance `0`, Hausdorff `0`).
    No such lemma exists in `BGW/MetricMeasure` (searched `rootedGHPDistance_le_*`,
    `RootedCommonSource`, `RootedGHPTransport`); it is the supporting statement
    `dist_toRootedMeasuredGHSpace_le_levyProkhorovDist`.
(3) `numLeaves → ∞` in probability FOLLOWS and is not assumed: the last DFS vertex is a leaf
    (preorder `vertices_node`: the last address is the last address of the last child, or the
    root of a leaf), so `leafIndex t (numLeaves t - 1) = t.size - 1`, and the discrepancy at
    `k = N - 1` is `|1/N − 1/n|` (`n = t.size`, `N = numLeaves t`); hence `1/N ≤ D + 1/n`
    (`one_div_numLeaves_le`).  Since `b n → ∞` and `b n / n → 0` in probability, `1/n ≤ b n/n`
    eventually.  Without the tree structure this fails (a path has `N = 1`, `D = (n-1)/n`).
    Sanity: size `1` gives `N = 1`, `leafIndex t 0 = 0 = 1 - 1`.
(4) `size ≥ 2` with high probability: `b/n ≤ r ≤ 1/2` and `b ≥ 1` force `n ≥ 2` (the argument of
    the private C38 lemma `exists_ratio_bound_on_compact`).  The deterministic statements keep
    the sealed hypothesis `hn : 2 ≤ t.size` (the existing `levyProkhorovDist_mass_leafMass_le`
    and `abs_vertexTime_sampleVertex_sub_le` need it).
(5) Time scale on a compact `K ⊆ C([0,1])` with `‖g‖ ≤ M`: with `b ≥ 1`, `b/n ≤ r`, all
    discrepancies `≤ r`: `D ≤ r`, `1/N ≤ r + 1/n ≤ 2r`, and by `contour_time_error_le`
    `2 (‖c‖/(2(n-1))) + 3/n ≤ 2 (‖c‖/(2(n-1)) + 2/n) ≤ 2 (M + 2) (b/n)`.  Total
    `≤ (2M + 7) r`, below the uniform modulus `δ` of `K` for small `r`.  So
    `exists_leaf_ratio_bound_on_compact` holds (with `ω = ε/2`).
(6) The main theorem drops C38's `hF` (measurability of the VERTEX-measure map): the perturbation
    lemma is applied with `F = ` leaf map (`hFL`) and `G = Coding.rootedMeasuredGHSpace ∘ G_n`
    (measurable from `hG`), and the discrepancy `dist(leaf, coded) ≤ dist(leaf, vertex) +
    dist(vertex, coded)` is handled event-wise with outer measures (`measureReal_mono`,
    `measureReal_union_le`), so the vertex map is never pushed forward.  `hFL` IS needed: for a
    non-measurable map `ProbabilityMeasure.map` is junk.  It holds for `⊤`-measurable trees
    (`measurable_leafRootedMeasuredGHSpace_of_top`).
(7) Not weaker than the spec: the conclusion is convergence in law in the rooted measured GHP
    space (`RootedMeasuredGHSpace`, whole-carrier isometry classes, the C38 target) to the SAME
    limit; the hypotheses are those of C38 minus `hF`, plus `hleaf` (the spec's δ → 0 in
    probability) and `hFL`.  A windowed discrepancy (sup over `t ≥ η`, as the spec's "plus η")
    implies `hleaf` by monotonicity of `leafIndex` (`leafIndex_strictMonoOn`); that reduction is
    article-side.  The in-probability statements take TIGHTNESS of the rescaled contour laws
    (`htight`, implied by `hlim` via `isTightMeasureSet_of_isCompact_closure`), the
    "height-modulus" input of roadmap CT9, so they apply beyond weak convergence.

PROOF PLAN (total 450-620 lines; no new mathematics beyond C38's argument and the sealed
coupling, except the list induction (a)).
(a) `leafIndex_numLeaves_sub_one`: induction on `t` (`vertices_node`): the last address of
    `t.vertices` satisfies `IsLeafAddr` (leaf: `[]`, `IsVertex [0]` false; node with children:
    `(len-1) :: (last address of the last child)`, `fringe?_node_cons` / `IsVertex` of a cons);
    it survives the filter as the last element of `leafAddrs t` (`List.getLast_filter`-type
    lemma, or `List.filter_append` on `vertices = dropLast ++ [last]`); `leafVertex_val`
    (re-prove: private) and `List.Nodup.idxOf_getElem` (`nodup_vertices`, `length_vertices`).
    (40-70)
(b) `one_div_numLeaves_le`: (a), `hD (numLeaves t - 1)`, `Nat.cast_sub`, `abs_le`, `field_simp`
    / `linarith` as in the private `one_div_n_le` of `LeafMeasure`.  (15)
(c) `map_leafVertex_rank_volume`: the private `map_leafVertex_rank` (same statement, new name to
    avoid any clash).  Re-prove `measurable_rank` (3 lines: `Measurable.nat_floor`, `.min`), then
    either copy `map_rank_volume_nat` (needs the private fibre lemmas, ~60) or, shorter: by the
    public `map_rank_volume N hN` and `rank N (idxTime N i) = i` for `i < N`
    (`Nat.floor_natCast`, `mul_div_cancel₀`), `volume.map (leafVertex t ∘ rank N) =
    (vertexTimeMeasure N).map (leafVertex t ∘ rank N)` (`Measure.map_map`, `Measure.map_congr`
    pointwise), `Measure.map_smul`, `Measure.map_finset_sum` (or `Measure.map_sum`),
    `Measure.map_dirac`.  (25-60)
(d) `dist_sampleVertex_leafVertex_le`: the body of the sealed `levyProkhorovDist_mass_leafMass_le`
    after `intro s`, verbatim (time triangle `abs_vertexTime_sampleVertex_sub_le`,
    `abs_vertexTime_sub_dfsTime_le`, `contourFunction_vertexTime`, `apply_le_norm`, then
    `isometry_vertexEmbedding` and `Coding.codingDist_le_of_oscillation`); re-prove the private
    `rank_lt` (3) and `abs_rank_div_sub_time_le` (+ `rank_cell_bounds`, ~35).  (90-120)
(e) `dist_toRootedMeasuredGHSpace_le_levyProkhorovDist`: CHECKED in a scratch probe (9 lines):
    `rw [RootedMeasuredGHSpace.dist_toRootedMeasuredGHSpace]`, `change rootedGHPDistance (μ :
    Measure X) (ν : Measure X) x x ≤ _`, `h := rootedGHPDistance_le_of_isometries μ ν x x X id id
    isometry_id isometry_id`, `simp only [dist_self, Metric.hausdorffDist_self_zero, add_zero,
    zero_add] at h`, `hb : borel X = ‹MeasurableSpace X› := BorelSpace.measurable_eq.symm`,
    `convert h using 1`, `rw [hb, Measure.map_id, Measure.map_id]`.  (Do NOT `subst` the
    `BorelSpace` equation: it removes the instance and elaboration times out.)  (10)
(f) `dist_scale_leaf_vertex_le`: CHECKED in a scratch probe from `sorry`ed (c), (d) and
    `measurable_rank` (~55 lines).  `ω ≥ 0` from `hω 0 0`; `hω'` (oscillation of `c_t` bounded
    by `ω / c`: `ContinuousMap.smul_apply`, `← mul_sub`, `abs_mul`, `le_div_iff₀`); with
    `c' := ⟨c, hc⟩`, `refine (dist_toRootedMeasuredGHSpace_le_levyProkhorovDist
    ((leafLaw t).map (toScaled c')) ((mass t).map (toScaled c')) (toScaled c' (root t))).trans ?_`
    works DIRECTLY (both scaled rooted spaces are definitionally `⟨of (ScaledMetric c'
    (Vertex t)) (_.map toScaled), toScaled (root t)⟩`, checked by `rfl`); then
    `F = toScaled ∘ leafVertex t ∘ rank N`, `G = toScaled ∘ sampleVertex t`, marginals by
    `Measure.map_map` with (c) and `map_sampleVertex_volume`, `levyProkhorovDist_comm`,
    `levyProkhorovDist_map_le_of_dist_le volume hG hF`, pointwise `ScaledMetric.dist_toScaled`
    and (d) at `ω / c` (`field_simp` for `c * (2 * (ω / c)) = 2 * ω`).  (55)
(g) `exists_leaf_ratio_bound_on_compact`: as the private C38 lemma
    `exists_ratio_bound_on_compact` (`ContourLawConvergence.lean`): `hK.isBounded
    .exists_pos_norm_le`, a uniform modulus on `K` (copy the private
    `exists_uniform_oscillation_of_isCompact`, 15 lines, with `ε / 2`), `r := min (1/2)
    (δ / (2 * M + 7))`; size `≥ 2` from `b/n ≤ 1/2`; time scale by TRUTH CHECK (5) with (b) and
    `contour_time_error_le`; conclude by (f) with `c = b⁻¹`.  (50-70)
(h) `tendsto_dist_leaf_vertex_probability`: the `herr` block of `tendsto_rooted_laws_of_contour`
    with `htight` in place of the compactness of `insert ν (range P)`
    (`isTightMeasureSet_iff_exists_isCompact_measure_compl_le`, `Measure.map_apply (hG n)`), (g),
    the three-set cover `{G ∉ K} ∪ {r < b/n} ∪ {∃ k, r < |…|}`, `measureReal_union_le`,
    `hratio r`, `hleaf r`, `hbinfty.eventually (eventually_ge_atTop 1)`.  (50-70)
(i) `tendsto_dist_vertex_coded_probability`: the same `herr` block of C38 verbatim (with
    `htight`), using a private copy of `exists_ratio_bound_on_compact` (public ingredients:
    `rooted_distance_scale_contour_le`, `contour_time_error_le`).  (60-80)
(j) `tendsto_rooted_leaf_laws_of_contour` (main): tightness from `hlim` exactly as in C38
    (`hlim.isCompact_insert_range`, `isTightMeasureSet_of_isCompact_closure`,
    `IsTightMeasureSet.subset`); `herr` for `F = ` leaf, `G = Coding.rootedMeasuredGHSpace ∘ G_n`
    by `dist_triangle`, the cover `{ε/2 < d(L,V)} ∪ {ε/2 < d(V,C)}`, (h), (i); `hcode` and
    `hmap` copied from C38 (`ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous`,
    `Coding.continuous_rootedMeasuredGHSpace`, `Measure.map_map`); conclude by
    `tendsto_probabilityMap_of_error_probability μ hFL hCG herr hcode`.  (40-60)
(k) `measurable_leafRootedMeasuredGHSpace_of_top`: `measurable_comp_of_top`.  (3)
(l) `tendsto_rooted_leaf_laws_of_contour_of_top`: (j) with (k) and `measurable_contour_of_top`.
    (8)
RISK: (a) is the only new combinatorics (list induction; moderate; truth argued in TRUTH CHECK
(3)).  The scaled-carrier definitional unfolding of (f), the only elaboration risk, was checked.
Private sealed helpers (`rank_lt`, `rank_cell_bounds`, `abs_rank_div_sub_time_le`,
`measurable_rank`, `map_leafVertex_rank`, `leafVertex_val`, `one_div_n_le`, C38's
`exists_ratio_bound_on_compact`, `exists_uniform_oscillation_of_isCompact`) are re-proved
privately, not exposed: the worker owns only the new module (if the coordinator grants
`LeafMeasure.lean` / `ContourLawConvergence.lean`, exposing them saves ~150 lines).

ACYCLICITY.  Sealed suppliers only: `LeafMeasure` (CT9 C39 deterministic part), `FiniteTree`,
`UniformVertexSampling`, `ContourEmbedding`, `ContourComparison`, `ContourConvergence`,
`ContourLawConvergence` (C38), `ContourAdapters` (measurability), `MetricMeasure.RootedGHP`,
`RootedScaling`, `ProkhorovBounds`, `WeakPerturbation` (C10(1)), Mathlib `Prokhorov`/`Tight`.
No article lemma (`cor_Lambda`, 5.9) and no StableTrees input.

BINDER SCOPE (AUDITOR_RULES).  No integral, sum or supremum occurs in the new statements (the
sealed `leafMass` sum is parenthesized at its definition).  The time scale is the sealed
expression `D + 1 / N + 2 * (‖c‖ / (2 * ((n - 1 : ℕ) : ℝ))) + 3 / n` with explicit casts and
parentheses; `(c • g) u` is a function application. -/

open MeasureTheory Filter Set
open scoped ENNReal Topology
open BGW.MetricMeasure

/-! ### Measure change on one rooted carrier -/

namespace BGW.MetricMeasure

universe u

/-- **Measure change on one carrier.**  Two probability measures on the same compact metric
space with the same root give rooted measured GHP classes at distance at most the
Lévy–Prokhorov distance of the measures. -/
theorem dist_toRootedMeasuredGHSpace_le_levyProkhorovDist {X : Type u} [MetricSpace X]
    [Nonempty X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ ν : ProbabilityMeasure X) (x : X) :
    dist (toRootedMeasuredGHSpace ⟨CompactMeasuredSpace.of X μ, x⟩)
        (toRootedMeasuredGHSpace ⟨CompactMeasuredSpace.of X ν, x⟩) ≤
      levyProkhorovDist (μ : Measure X) (ν : Measure X) := sorry

end BGW.MetricMeasure

namespace BGW.ContinuumTrees.LeafMeasure

open BGW.PlaneTree BGW.ContinuumTrees.FiniteTree

/-! ### The leaf-measured rooted tree -/

/-- The uniform probability on the leaves of a plane tree, bundled. -/
noncomputable def leafLaw (t : PlaneTree) : ProbabilityMeasure (Vertex t) :=
  ⟨leafMass t, inferInstance⟩

@[simp] theorem coe_leafLaw (t : PlaneTree) :
    (leafLaw t : Measure (Vertex t)) = leafMass t := rfl

/-- The vertex set with its graph metric and the uniform probability on leaves. -/
noncomputable def leafCompactMeasuredSpace (t : PlaneTree) : CompactMeasuredSpace :=
  CompactMeasuredSpace.of (Vertex t) (leafLaw t)

/-- The same leaf-measured space, rooted at the empty address (as
`FiniteTree.rootedCompactMeasuredSpace`). -/
noncomputable def leafRootedCompactMeasuredSpace (t : PlaneTree) :
    RootedCompactMeasuredSpace where
  space := leafCompactMeasuredSpace t
  root := FiniteTree.root t

/-! ### Deterministic statements -/

/-- The last leaf in DFS order is the last vertex in DFS order. -/
theorem leafIndex_numLeaves_sub_one (t : PlaneTree) :
    leafIndex t (numLeaves t - 1) = t.size - 1 := sorry

/-- A leaf-index discrepancy bound forces many leaves: `1 / N ≤ D + 1 / n`. -/
theorem one_div_numLeaves_le (t : PlaneTree) {D : ℝ}
    (hD : ∀ k < numLeaves t,
      |(leafIndex t k : ℝ) / (t.size : ℝ) - (k : ℝ) / (numLeaves t : ℝ)| ≤ D) :
    1 / (numLeaves t : ℝ) ≤ D + 1 / (t.size : ℝ) := sorry

/-- The leaf quantile map sends Lebesgue measure on `[0,1]` to the uniform leaf measure. -/
theorem map_leafVertex_rank_volume (t : PlaneTree) :
    (volume : Measure unitInterval).map (fun s => leafVertex t (rank (numLeaves t) s)) =
      leafMass t := sorry

/-- **Quantile coupling bound** (C39(a), unscaled).  The vertex and the leaf selected by the same
uniform time `s` are within graph distance `2 ω`, where `ω` bounds the oscillation of the contour
at the time scale `D + 1/N + 2 ‖c‖/(2(n-1)) + 3/n`. -/
theorem dist_sampleVertex_leafVertex_le (t : PlaneTree) (hn : 2 ≤ t.size) {D ω : ℝ}
    (hD : ∀ k < numLeaves t,
      |(leafIndex t k : ℝ) / (t.size : ℝ) - (k : ℝ) / (numLeaves t : ℝ)| ≤ D)
    (hω : ∀ u v : unitInterval, |(u : ℝ) - (v : ℝ)| ≤ D + 1 / (numLeaves t : ℝ)
        + 2 * (‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ))) + 3 / (t.size : ℝ) →
        |t.contourFunction u - t.contourFunction v| ≤ ω)
    (s : unitInterval) :
    dist (sampleVertex t s) (leafVertex t (rank (numLeaves t) s)) ≤ 2 * ω := sorry

/-- **Scaled vertex/leaf comparison.**  After multiplying the graph distance by `c > 0`, the
leaf-measured and vertex-measured rooted trees are within rooted GHP distance `2 ω`, where `ω`
bounds the oscillation of the SCALED contour `c • c_t` at the time scale
`D + 1/N + 2 ‖c_t‖/(2(n-1)) + 3/n`. -/
theorem dist_scale_leaf_vertex_le (t : PlaneTree) (hn : 2 ≤ t.size) (c : ℝ) (hc : 0 < c)
    {D ω : ℝ}
    (hD : ∀ k < numLeaves t,
      |(leafIndex t k : ℝ) / (t.size : ℝ) - (k : ℝ) / (numLeaves t : ℝ)| ≤ D)
    (hω : ∀ u v : unitInterval, |(u : ℝ) - (v : ℝ)| ≤ D + 1 / (numLeaves t : ℝ)
        + 2 * (‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ))) + 3 / (t.size : ℝ) →
        |(c • t.contourFunction) u - (c • t.contourFunction) v| ≤ ω) :
    dist (RootedMeasuredGHSpace.scale c hc
        (toRootedMeasuredGHSpace (leafRootedCompactMeasuredSpace t)))
      (RootedMeasuredGHSpace.scale c hc
        (toRootedMeasuredGHSpace (rootedCompactMeasuredSpace t))) ≤ 2 * ω := sorry

/-- **Uniform deterministic bound on a compact set of rescaled contours.**  For a compact `K`
and `ε > 0` there is `r > 0` such that a tree whose rescaled contour lies in `K`, with
divisor-to-size ratio `≤ r` and all leaf-index discrepancies `≤ r`, has rescaled leaf- and
vertex-measured rooted trees within `ε`. -/
theorem exists_leaf_ratio_bound_on_compact
    (K : Set C(unitInterval, ℝ)) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ (t : PlaneTree) (b : ℝ) (hb : 0 < b), 1 ≤ b →
      b⁻¹ • t.contourFunction ∈ K → b / (t.size : ℝ) ≤ r →
      (∀ k < numLeaves t,
        |(leafIndex t k : ℝ) / (t.size : ℝ) - (k : ℝ) / (numLeaves t : ℝ)| ≤ r) →
      dist (RootedMeasuredGHSpace.scale b⁻¹ (inv_pos.mpr hb)
          (toRootedMeasuredGHSpace (leafRootedCompactMeasuredSpace t)))
        (RootedMeasuredGHSpace.scale b⁻¹ (inv_pos.mpr hb)
          (toRootedMeasuredGHSpace (rootedCompactMeasuredSpace t))) ≤ ε := sorry

/-! ### In probability -/

/-- **Leaf versus vertex measure in probability** (the C10(1) perturbation input of C39).
If the rescaled contour laws are tight, the divisor-to-size ratio and the leaf-index
discrepancy vanish in probability, then the rescaled leaf- and vertex-measured rooted trees are
within `o_P(1)` in rooted GHP distance. -/
theorem tendsto_dist_leaf_vertex_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n))
    (t : (n : ℕ) → Ω n → PlaneTree) (b : ℕ → ℝ)
    (hb : ∀ n, 0 < b n) (hbinfty : Tendsto b atTop atTop)
    (hG : ∀ n, Measurable (fun ω : Ω n => (b n)⁻¹ • (t n ω).contourFunction))
    (hratio : ∀ r > 0, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | r < b n / ((t n ω).size : ℝ)}) atTop (𝓝 0))
    (hleaf : ∀ ε > 0, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | ∃ k < numLeaves (t n ω), ε < |(leafIndex (t n ω) k : ℝ) / ((t n ω).size : ℝ) -
        (k : ℝ) / (numLeaves (t n ω) : ℝ)|}) atTop (𝓝 0))
    (htight : IsTightMeasureSet (Set.range fun n =>
      ((μ n).map (fun ω : Ω n => (b n)⁻¹ • (t n ω).contourFunction) :
        Measure C(unitInterval, ℝ)))) :
    ∀ ε > 0, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | ε < dist
        (RootedMeasuredGHSpace.scale (b n)⁻¹ (inv_pos.mpr (hb n))
          (toRootedMeasuredGHSpace (leafRootedCompactMeasuredSpace (t n ω))))
        (RootedMeasuredGHSpace.scale (b n)⁻¹ (inv_pos.mpr (hb n))
          (toRootedMeasuredGHSpace (rootedCompactMeasuredSpace (t n ω))))}) atTop (𝓝 0) :=
  sorry

end BGW.ContinuumTrees.LeafMeasure

namespace BGW.ContinuumTrees.FiniteTree

/-- **Vertex measure versus contour coding in probability** (the discrepancy step inside C38,
exported).  Under tight rescaled contour laws and vanishing divisor-to-size ratio, the rescaled
vertex-measured rooted tree is within `o_P(1)` of the tree coded by its rescaled contour. -/
theorem tendsto_dist_vertex_coded_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n))
    (t : (n : ℕ) → Ω n → PlaneTree) (b : ℕ → ℝ)
    (hb : ∀ n, 0 < b n) (hbinfty : Tendsto b atTop atTop)
    (hG : ∀ n, Measurable (fun ω : Ω n => (b n)⁻¹ • (t n ω).contourFunction))
    (hratio : ∀ r > 0, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | r < b n / ((t n ω).size : ℝ)}) atTop (𝓝 0))
    (htight : IsTightMeasureSet (Set.range fun n =>
      ((μ n).map (fun ω : Ω n => (b n)⁻¹ • (t n ω).contourFunction) :
        Measure C(unitInterval, ℝ)))) :
    ∀ ε > 0, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | ε < dist
        (RootedMeasuredGHSpace.scale (b n)⁻¹ (inv_pos.mpr (hb n))
          (toRootedMeasuredGHSpace (rootedCompactMeasuredSpace (t n ω))))
        (Coding.rootedMeasuredGHSpace ((b n)⁻¹ • (t n ω).contourFunction))}) atTop (𝓝 0) :=
  sorry

end BGW.ContinuumTrees.FiniteTree

namespace BGW.ContinuumTrees.LeafMeasure

open BGW.PlaneTree BGW.ContinuumTrees.FiniteTree

/-! ### Convergence in law (public CT9 interface) -/

/-- **C39, law-level form (CT9).**  Weak convergence of the rescaled contours on varying
probability spaces, vanishing divisor-to-size tails and vanishing leaf-index discrepancy in
probability give convergence in law, in the rooted measured GHP space, of the rescaled trees
carrying the uniform LEAF measure, to the same limit `ν.map Coding.rootedMeasuredGHSpace` as for
the vertex measure (C38, `tendsto_rooted_laws_of_contour`).  The measurability of the
vertex-measure map (`hF` of C38) is not needed. -/
theorem tendsto_rooted_leaf_laws_of_contour
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n))
    (t : (n : ℕ) → Ω n → PlaneTree) (b : ℕ → ℝ)
    (hb : ∀ n, 0 < b n) (hbinfty : Tendsto b atTop atTop)
    (hFL : ∀ n, Measurable (fun ω : Ω n =>
      RootedMeasuredGHSpace.scale (b n)⁻¹ (inv_pos.mpr (hb n))
        (toRootedMeasuredGHSpace (leafRootedCompactMeasuredSpace (t n ω)))))
    (hG : ∀ n, Measurable (fun ω : Ω n => (b n)⁻¹ • (t n ω).contourFunction))
    (hratio : ∀ r > 0, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | r < b n / ((t n ω).size : ℝ)}) atTop (𝓝 0))
    (hleaf : ∀ ε > 0, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | ∃ k < numLeaves (t n ω), ε < |(leafIndex (t n ω) k : ℝ) / ((t n ω).size : ℝ) -
        (k : ℝ) / (numLeaves (t n ω) : ℝ)|}) atTop (𝓝 0))
    {ν : ProbabilityMeasure C(unitInterval, ℝ)}
    (hlim : Tendsto (fun n => (μ n).map
      (fun ω : Ω n => (b n)⁻¹ • (t n ω).contourFunction)) atTop (𝓝 ν)) :
    Tendsto (fun n => (μ n).map (fun ω : Ω n =>
      RootedMeasuredGHSpace.scale (b n)⁻¹ (inv_pos.mpr (hb n))
        (toRootedMeasuredGHSpace (leafRootedCompactMeasuredSpace (t n ω)))))
      atTop (𝓝 (ν.map Coding.rootedMeasuredGHSpace)) := sorry

/-- Hypothesis `hFL` for random trees measurable for the `⊤` σ-algebra on `PlaneTree`. -/
theorem measurable_leafRootedMeasuredGHSpace_of_top {X : Type*} [MeasurableSpace X]
    (t : X → PlaneTree) {b : ℝ} (hb : 0 < b) (ht : @Measurable X PlaneTree _ ⊤ t) :
    Measurable (fun x : X => RootedMeasuredGHSpace.scale b⁻¹ (inv_pos.mpr hb)
      (toRootedMeasuredGHSpace (leafRootedCompactMeasuredSpace (t x)))) := sorry

/-- **Consumer form**: C39 law-level transfer for `⊤`-measurable random trees, with no separate
measurability hypothesis. -/
theorem tendsto_rooted_leaf_laws_of_contour_of_top
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n))
    (t : (n : ℕ) → Ω n → PlaneTree) (ht : ∀ n, @Measurable (Ω n) PlaneTree _ ⊤ (t n))
    (b : ℕ → ℝ) (hb : ∀ n, 0 < b n) (hbinfty : Tendsto b atTop atTop)
    (hratio : ∀ r > 0, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | r < b n / ((t n ω).size : ℝ)}) atTop (𝓝 0))
    (hleaf : ∀ ε > 0, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | ∃ k < numLeaves (t n ω), ε < |(leafIndex (t n ω) k : ℝ) / ((t n ω).size : ℝ) -
        (k : ℝ) / (numLeaves (t n ω) : ℝ)|}) atTop (𝓝 0))
    {ν : ProbabilityMeasure C(unitInterval, ℝ)}
    (hlim : Tendsto (fun n => (μ n).map
      (fun ω : Ω n => (b n)⁻¹ • (t n ω).contourFunction)) atTop (𝓝 ν)) :
    Tendsto (fun n => (μ n).map (fun ω : Ω n =>
      RootedMeasuredGHSpace.scale (b n)⁻¹ (inv_pos.mpr (hb n))
        (toRootedMeasuredGHSpace (leafRootedCompactMeasuredSpace (t n ω)))))
      atTop (𝓝 (ν.map Coding.rootedMeasuredGHSpace)) := sorry

end BGW.ContinuumTrees.LeafMeasure
