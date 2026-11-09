/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.Topology.Sets.VietorisTopology

/-!
# A compact hull for a convergent sequence of compact sets

A convergent sequence of compact sets and its limit fit inside a single
compact set. The hull retains every point in every set; it is not a measure
support. This lets varying compact carriers share one compact probability
space in the GHP completeness argument.

Adapted from `Freezing2/Geometry/CompactHausdorffHull.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
-/

@[expose] public section

open Filter Set TopologicalSpace
open scoped Topology

namespace BGW.MetricMeasure

variable {Z : Type*} [MetricSpace Z]

/-- The union of a sequence of compact sets and its proposed limit. -/
def compactSequenceHull (S : ℕ → NonemptyCompacts Z) (L : NonemptyCompacts Z) : Set Z :=
  ⋃ K ∈ insert L (range S), (K : Set Z)

theorem subset_compactSequenceHull_limit (S : ℕ → NonemptyCompacts Z)
    (L : NonemptyCompacts Z) : (L : Set Z) ⊆ compactSequenceHull S L := by
  intro x hx
  exact mem_iUnion₂.mpr ⟨L, mem_insert _ _, hx⟩

theorem subset_compactSequenceHull (S : ℕ → NonemptyCompacts Z)
    (L : NonemptyCompacts Z) (n : ℕ) : (S n : Set Z) ⊆ compactSequenceHull S L := by
  intro x hx
  exact mem_iUnion₂.mpr ⟨S n, mem_insert_of_mem _ (mem_range_self n), hx⟩

theorem isCompact_compactSequenceHull {S : ℕ → NonemptyCompacts Z}
    {L : NonemptyCompacts Z} (h : Tendsto S atTop (𝓝 L)) :
    IsCompact (compactSequenceHull S L) :=
  NonemptyCompacts.isCompact_biUnion_coe_of_isCompact h.isCompact_insert_range

/-- A Hausdorff-Cauchy sequence in a complete ambient metric space converges
and all its full carriers lie in one common compact carrier. -/
theorem exists_common_compact_of_cauchySeq [CompleteSpace Z]
    (S : ℕ → NonemptyCompacts Z) (hS : CauchySeq S) :
    ∃ L K : NonemptyCompacts Z, Tendsto S atTop (𝓝 L) ∧
      (L : Set Z) ⊆ K ∧ ∀ n, (S n : Set Z) ⊆ K := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hS
  let K : NonemptyCompacts Z :=
    ⟨⟨compactSequenceHull S L, isCompact_compactSequenceHull hL⟩,
      L.nonempty.mono (subset_compactSequenceHull_limit S L)⟩
  exact ⟨L, K, hL, subset_compactSequenceHull_limit S L, subset_compactSequenceHull S L⟩

end BGW.MetricMeasure

