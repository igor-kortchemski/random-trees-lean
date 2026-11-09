import BGW.ContinuumTrees.CodingMeasure
import BGW.ContinuumTrees.ContourComparison
import BGW.ContinuumTrees.ContourEmbedding
import BGW.ContinuumTrees.UniformVertexSampling
import BGW.MetricMeasure.ProkhorovBounds

/-! Contract probe for CT.C39 (CT9): a reusable deterministic coupling/Prokhorov estimate between
two time measures pushed to a tree coded by a function, its discrete form for vertex-time and
leaf-time measures with an explicit quantile convention, and its convergence consequence.
Intended maintained file: `BGW/ContinuumTrees/LeafMeasure.lean`.

This is NOT the article's leaf-conditioned theorem: `cor_Lambda` and the tightness of the height
process supply, later, the hypotheses `hD` and `hmod` below.

Conventions.
* Coding: `Coding.Space g`, `Coding.projection g` and `codingDist g s t = g s + g t - 2 m` with
  `m = min_{[s,t]} g`. Hence `dist (π s) (π t) ≤ 2 ω` whenever `g` oscillates by at most `ω` on
  pairs at time distance `≤ δ ≥ |s - t|` (both endpoints are within `|s-t|` of a minimiser).
  This is `Coding.codingDist_le_of_oscillation`.
  The `+2` of C39 arises only when `Vertex t` is compared with a height-function coding. With the
  contour coding, `vertexEmbedding` is an isometry and no `+2` occurs.
* Index times: the index `i` among `n` points sits at time `i / n` (`idxTime`, clamped to `[0,1]`).
* Quantile convention (matches `FiniteTree.sampleVertex`): `rank n s = min ⌊n s⌋₊ (n - 1)`, so
  `[0,1)` is cut into `n` cells `[i/n, (i+1)/n)` and `s = 1` goes to the last index `n - 1`.
  For `n = 0` the rank is `0` and the empirical measures below are `0`; every theorem therefore
  assumes `0 < n` and `0 < N`.
* Leaf indices: `ℓ k` is the index (among the `n` vertices, in the library's DFS order) of the
  `k`-th leaf, `k < N`, `ℓ k < n`. Strict monotonicity of `ℓ` is not needed by the estimates. -/

open MeasureTheory Filter Set
open scoped ENNReal Topology
open BGW.MetricMeasure BGW.ContinuumTrees.Coding

namespace BGW.ContinuumTrees.LeafMeasure

/-- Time `i / n` of the index `i` among `n` points, as a point of `[0,1]` (clamped). -/
noncomputable def idxTime (n i : ℕ) : unitInterval :=
  Set.projIcc 0 1 zero_le_one ((i : ℝ) / (n : ℝ))

/-- Quantile rank: the index in `{0, …, n-1}` selected by the uniform time `s`
(`⌊n s⌋`, with `s = 1` sent to `n - 1`). -/
noncomputable def rank (n : ℕ) (s : unitInterval) : ℕ :=
  min (Nat.floor ((n : ℝ) * (s : ℝ))) (n - 1)

/-- Uniform measure on the times `i/n`, `i < n` (vertex-time measure). -/
noncomputable def vertexTimeMeasure (n : ℕ) : Measure unitInterval :=
  (n : ℝ≥0∞)⁻¹ • ∑ i ∈ Finset.range n, Measure.dirac (idxTime n i)

/-- Uniform measure on the times `ℓ k / n`, `k < N` (leaf-time measure). -/
noncomputable def leafTimeMeasure (n N : ℕ) (ℓ : ℕ → ℕ) : Measure unitInterval :=
  (N : ℝ≥0∞)⁻¹ • ∑ k ∈ Finset.range N, Measure.dirac (idxTime n (ℓ k))

instance (n : ℕ) [NeZero n] : IsProbabilityMeasure (vertexTimeMeasure n) := sorry

instance (n N : ℕ) [NeZero N] (ℓ : ℕ → ℕ) : IsProbabilityMeasure (leafTimeMeasure n N ℓ) := sorry

/-- The vertex-time measure is the pushforward of Lebesgue measure under the quantile map. -/
theorem map_rank_volume (n : ℕ) (hn : 0 < n) :
    (volume : Measure unitInterval).map (fun s => idxTime n (rank n s)) =
      vertexTimeMeasure n := sorry

/-- The leaf-time measure is the pushforward of Lebesgue measure under the leaf quantile map. -/
theorem map_leafRank_volume (n N : ℕ) (hN : 0 < N) (ℓ : ℕ → ℕ) :
    (volume : Measure unitInterval).map (fun s => idxTime n (ℓ (rank N s))) =
      leafTimeMeasure n N ℓ := sorry

/-- (1) Deterministic coupling estimate. If `π` is a coupling of `μ` and `ν` on `[0,1]²` giving mass
`≤ δ'` to the set `{|s - t| > δ}`, and `g` oscillates by at most `ω` at time scale `δ`, then the
Prokhorov distance of the images in the coded tree is at most `max δ' (2 ω)`. Valid for all
`δ, δ' ≥ 0`; the coding estimate used is `Coding.codingDist_le_of_oscillation` (for `δ ≥ 1` the bad set is empty; for `g` constant `ω = 0`). -/
theorem levyProkhorovDist_map_projection_le_of_coupling
    (g : C(unitInterval, ℝ)) (μ ν : Measure unitInterval)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (π : Measure (unitInterval × unitInterval)) (hπ₁ : π.map Prod.fst = μ)
    (hπ₂ : π.map Prod.snd = ν) {δ δ' ω : ℝ} (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ')
    (hbad : π {p | δ < |(p.1 : ℝ) - (p.2 : ℝ)|} ≤ ENNReal.ofReal δ')
    (hω : ∀ u v : unitInterval, |(u : ℝ) - (v : ℝ)| ≤ δ → |g u - g v| ≤ ω) :
    levyProkhorovDist (μ.map (projection g)) (ν.map (projection g)) ≤ max δ' (2 * ω) := sorry

/-- (2a) Quantile coupling bound: the leaf time and the vertex time selected by the same uniform
time `s` differ by at most `D + 1/N + 1/n`, where `D` bounds the leaf-index discrepancy
`|ℓ k / n - k / N|`. No exceptional set is needed (including `s = 0` and `s = 1`). -/
theorem abs_idxTime_leaf_sub_vertex_le (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (ℓ : ℕ → ℕ)
    (hℓ : ∀ k < N, ℓ k < n) {D : ℝ}
    (hD : ∀ k < N, |(ℓ k : ℝ) / (n : ℝ) - (k : ℝ) / (N : ℝ)| ≤ D) (s : unitInterval) :
    |(idxTime n (ℓ (rank N s)) : ℝ) - (idxTime n (rank n s) : ℝ)| ≤ D + 1 / N + 1 / n := sorry

/-- (2) Discrete estimate: for every continuous coding function `g`, the vertex-time and leaf-time
measures on the coded tree are within `2 ω` in Prokhorov distance, where `ω` bounds the oscillation
of `g` at time scale `D + 1/N + 1/n`. -/
theorem levyProkhorovDist_vertex_leaf_le (g : C(unitInterval, ℝ)) (n N : ℕ) (hn : 0 < n)
    (hN : 0 < N) (ℓ : ℕ → ℕ) (hℓ : ∀ k < N, ℓ k < n) {D ω : ℝ}
    (hD : ∀ k < N, |(ℓ k : ℝ) / (n : ℝ) - (k : ℝ) / (N : ℝ)| ≤ D)
    (hω : ∀ u v : unitInterval, |(u : ℝ) - (v : ℝ)| ≤ D + 1 / N + 1 / n → |g u - g v| ≤ ω) :
    levyProkhorovDist ((vertexTimeMeasure n).map (projection g))
      ((leafTimeMeasure n N ℓ).map (projection g)) ≤ 2 * ω := sorry

/-- (3) Convergence consequence under asymptotic equicontinuity of the coding functions
(`hmod`: every `ε > 0` has a time scale `δ > 0` that works for all large `j`), explicit
leaf-index discrepancy `D j → 0`, and `N j → ∞` (`n j → ∞` follows: at `k = N-1`, `1/n ≤ 1/N + D`). The number of leaves must tend to infinity
(`D j → 0` alone does not force it: `N = 1`, `ℓ 0 = 0` has `D = 0`). -/
theorem tendsto_levyProkhorovDist_vertex_leaf (g : ℕ → C(unitInterval, ℝ)) (n N : ℕ → ℕ)
    (hn : ∀ j, 0 < n j) (hN : ∀ j, 0 < N j) (ℓ : ℕ → ℕ → ℕ)
    (hℓ : ∀ j, ∀ k < N j, ℓ j k < n j) (D : ℕ → ℝ)
    (hD : ∀ j, ∀ k < N j, |(ℓ j k : ℝ) / (n j : ℝ) - (k : ℝ) / (N j : ℝ)| ≤ D j)
    (hD0 : Tendsto D atTop (𝓝 0)) (hNTop : Tendsto N atTop atTop)
    (hmod : ∀ ε > 0, ∃ δ > 0, ∀ᶠ j in atTop, ∀ u v : unitInterval,
      |(u : ℝ) - (v : ℝ)| ≤ δ → |g j u - g j v| ≤ ε) :
    Tendsto (fun j =>
      levyProkhorovDist ((vertexTimeMeasure (n j)).map (projection (g j)))
        ((leafTimeMeasure (n j) (N j) (ℓ j)).map (projection (g j)))) atTop (𝓝 0) := sorry

/-- (3′) The case of uniform convergence of the coding functions `g j → g₀` in `C([0,1])`
(the modulus hypothesis `hmod` holds, `g₀` being uniformly continuous). -/
theorem tendsto_levyProkhorovDist_vertex_leaf_of_tendsto (g : ℕ → C(unitInterval, ℝ))
    (g₀ : C(unitInterval, ℝ)) (hg : Tendsto g atTop (𝓝 g₀)) (n N : ℕ → ℕ)
    (hn : ∀ j, 0 < n j) (hN : ∀ j, 0 < N j) (ℓ : ℕ → ℕ → ℕ)
    (hℓ : ∀ j, ∀ k < N j, ℓ j k < n j) (D : ℕ → ℝ)
    (hD : ∀ j, ∀ k < N j, |(ℓ j k : ℝ) / (n j : ℝ) - (k : ℝ) / (N j : ℝ)| ≤ D j)
    (hD0 : Tendsto D atTop (𝓝 0)) (hNTop : Tendsto N atTop atTop) :
    Tendsto (fun j =>
      levyProkhorovDist ((vertexTimeMeasure (n j)).map (projection (g j)))
        ((leafTimeMeasure (n j) (N j) (ℓ j)).map (projection (g j)))) atTop (𝓝 0) := sorry

/-! ### Adapter to plane trees -/

section PlaneTreeAdapter

open BGW.PlaneTree BGW.ContinuumTrees.FiniteTree

/-- A vertex address is a leaf when it has no first child. -/
def IsLeafAddr (t : PlaneTree) (u : List ℕ) : Prop := ¬ t.IsVertex (u ++ [0])

/-- Leaf addresses, in the DFS order of `t.vertices`. -/
noncomputable def leafAddrs (t : PlaneTree) : List (List ℕ) :=
  haveI := Classical.propDecidable
  t.vertices.filter (fun u => decide (IsLeafAddr t u))

/-- Number of leaves (vertices without children). -/
noncomputable def numLeaves (t : PlaneTree) : ℕ := (leafAddrs t).length

/-- The `k`-th leaf in DFS order; junk value `root t` for `k ≥ numLeaves t`. -/
noncomputable def leafVertex (t : PlaneTree) (k : ℕ) : Vertex t :=
  haveI := Classical.propDecidable
  if h : k < numLeaves t then
    ⟨(leafAddrs t)[k]'h, (mem_vertices_iff t _).mp (List.mem_filter.mp (List.getElem_mem h)).1⟩
  else root t

/-- DFS index (position in `t.vertices`) of the `k`-th leaf; junk value `0` (the root's index)
for `k ≥ numLeaves t`. -/
noncomputable def leafIndex (t : PlaneTree) (k : ℕ) : ℕ := t.vertices.idxOf (leafVertex t k).val

/-- Uniform probability on the leaves (`0` if there were no leaf; see `numLeaves_pos`). -/
noncomputable def leafMass (t : PlaneTree) : Measure (Vertex t) :=
  (numLeaves t : ℝ≥0∞)⁻¹ • ∑ k ∈ Finset.range (numLeaves t), Measure.dirac (leafVertex t k)

/-- Every finite plane tree has a leaf. -/
theorem numLeaves_pos (t : PlaneTree) : 0 < numLeaves t := sorry

theorem leafVertex_isLeaf (t : PlaneTree) {k : ℕ} (hk : k < numLeaves t) :
    IsLeafAddr t (leafVertex t k).val := sorry

theorem leafIndex_lt_size (t : PlaneTree) (k : ℕ) : leafIndex t k < t.size := sorry

theorem leafIndex_strictMonoOn (t : PlaneTree) :
    StrictMonoOn (leafIndex t) (Set.Iio (numLeaves t)) := sorry

instance (t : PlaneTree) : IsProbabilityMeasure (leafMass t) := sorry

/-- Transfer to a plane tree. The metric of `Vertex t` is the graph metric, for which
`vertexEmbedding t` is an isometry into `Coding.Space t.contourFunction`. The time scale is
`D + 1/N + 2A + 3/n` with `A = ‖c‖ / (2 (n-1))` (`c` the contour function, `n = t.size`,
`N = numLeaves t`), hence at most the threshold in `hω`.
Proof: for `s` uniform, `k = rank N s` and `u = sampleVertex t s`, with `ℓ = leafIndex t k`:
`|vertexTime (leaf k) - ℓ/n| ≤ A + 1/n` (`abs_vertexTime_sub_dfsTime_le`, depth `≤ ‖c‖`),
`|ℓ/n - k/N| ≤ D`, `|k/N - s| ≤ 1/N`, and `|s - vertexTime u| ≤ A + 2/n`
(`abs_vertexTime_sampleVertex_sub_le`). Then `Coding.codingDist_le_of_oscillation` and
`levyProkhorovDist_map_le_of_dist_le` apply, via the pushforward under the isometry. -/
theorem levyProkhorovDist_mass_leafMass_le (t : PlaneTree) (hn : 2 ≤ t.size)
    {D ω : ℝ} (hD : ∀ k < numLeaves t, |(leafIndex t k : ℝ) / t.size - k / numLeaves t| ≤ D)
    (hω : ∀ u v : unitInterval, |(u : ℝ) - v| ≤ D + 1 / numLeaves t
          + 2 * (‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ))) + 3 / t.size →
          |t.contourFunction u - t.contourFunction v| ≤ ω) :
    levyProkhorovDist (mass t : Measure (Vertex t)) (leafMass t) ≤ 2 * ω := sorry

end PlaneTreeAdapter

end BGW.ContinuumTrees.LeafMeasure
