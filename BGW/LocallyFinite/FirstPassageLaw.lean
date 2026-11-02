/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.LocallyFinite.ForestWalkLaw
public import BGW.Tree.FirstPassage

/-!
# The first-passage convolution for forests

For an offspring probability measure `μ`, `1 ≤ ℓ` and every `N`, decomposing the walk of independent
offspring counts at its first passage time `q` to `-ℓ`,

`P(S_N = -ℓ) = ∑_{q ≤ N} P(|𝒢_ℓ| = q) P(S_{N-q} = 0)`

(`pi_countForestBridges_eq_sum`), where `P(S_n = -ℓ)` is the mass of `countForestBridges ℓ n` under
`Measure.pi (fun _ : Fin n => μ)` and `P(|𝒢_ℓ| = q)` is `forestWeight (fun d => μ {d}) ℓ q`. The
identity is unconditional: no criticality, positivity or lattice hypothesis, and it holds for
`N < ℓ` as well, where both sides vanish. For `ℓ = 1` the factor `P(|𝒢_1| = q)` is the mass of
`sizeEvent q` under the Bienaymé–Galton–Watson law (`pi_countBridges_eq_sum`). It is obtained from
the word-level decomposition `tsum_forestBridgeWords_eq_sum` by the reindexing of `ForestWalkLaw`.
The uniform cyclic-shift representation and the conditional bridge law are not part of this module.
Adapted from `PoissonDeclumping/Bridge/Kemperman.lean` (`walkMass_neg_eq_sum`).
-/

@[expose] public section

namespace BGW

open MeasureTheory
open scoped ENNReal BigOperators

/-- **First-passage convolution for forests**:
`P(S_N = -ℓ) = ∑_{q ≤ N} P(|𝒢_ℓ| = q) P(S_{N-q} = 0)`, for every offspring probability measure,
`1 ≤ ℓ` and every `N`. -/
theorem pi_countForestBridges_eq_sum (μ : Measure ℕ) [IsProbabilityMeasure μ] {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (N : ℕ) :
    Measure.pi (fun _ : Fin N => μ) (countForestBridges ℓ N) =
      ∑ q ∈ Finset.range (N + 1), forestWeight (fun d => μ {d}) ℓ q *
        Measure.pi (fun _ : Fin (N - q) => μ) (countForestBridges 0 (N - q)) := by
  rw [pi_eq_tsum_indicator]
  refine (tsum_forestBridgeWords_walkWeight (fun d => μ {d}) ℓ N).symm.trans ?_
  rw [tsum_forestBridgeWords_eq_sum _ hℓ]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [pi_eq_tsum_indicator]
  exact congrArg _ (tsum_forestBridgeWords_walkWeight (fun d => μ {d}) 0 (N - q))

/-- The walk ends at `0` exactly when the counts sum to `n`. -/
theorem countForestBridges_zero (n : ℕ) : countForestBridges 0 n = {ω | ∑ i, ω i = n} := rfl

/-- The tree case `ℓ = 1`: `P(S_N = -1) = ∑_{q ≤ N} P(|T| = q) P(S_{N-q} = 0)`. -/
theorem pi_countBridges_eq_sum (μ : Measure ℕ) [IsProbabilityMeasure μ] (N : ℕ) :
    Measure.pi (fun _ : Fin N => μ) (countBridges N) =
      ∑ q ∈ Finset.range (N + 1), LocallyFinite.bienaymeLaw μ (LocallyFinite.sizeEvent q) *
        Measure.pi (fun _ : Fin (N - q) => μ) {ω | ∑ i, ω i = N - q} := by
  rw [← countForestBridges_one, pi_countForestBridges_eq_sum μ le_rfl]
  simp_rw [LocallyFinite.forestWeight_one_eq_bienaymeLaw_sizeEvent]
  rfl

end BGW
