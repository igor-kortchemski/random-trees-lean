import BGW.Skorokhod.Restrict
import BGW.Skorokhod.MeasurableMaps
import BGW.Skorokhod.CompleteMetricCompleteness
import BGW.Skorokhod.Separable
import BGW.Skorokhod.Measurable
import KolmogorovExtension4.KolmogorovExtension
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Contract probe for CT.C6 blueprint Node 2 (audit: first node, "compatible path-law adapter"):
a consistent sequence of probability laws on the path spaces `D([0,b_n], ℝ)`, `b_n` strictly
increasing and positive, has a unique probability law on the *compatible-family subtype*
`CompatiblePaths b ⊆ ∏ₙ D(b_n, ℝ)` with the given coordinate marginals.

Route (for the proof, not the statement): the *max-index family*
`J ↦ (P (J.sup id)).map (restrictions)` is a projective measure family on `Finset ℕ`
(`maxIndexLaw`, `isProjectiveMeasureFamily_maxIndexLaw`); the vendored
`MeasureTheory.projectiveLimit` applies because every `D (b n) ℝ` is second countable and
completely pseudo-metrizable (the two instance checks below, sealed inputs
`BGW.Skorokhod.instSeparableSpace`, `instIsCompletelyMetrizableSpace`); the compatibility set is
measurable (NOT closed in the product, so no closedness argument) and has full limit measure
because the two-coordinate marginals are `(P (n+1)).map (restrict, id)`-supported on the graph.
Bridge (`b n = 1 - 2^(-n-1)`) and process (`b n = n + 1`) reuse this adapter.
Maintained file: `BGW/Skorokhod/PathLawFamily.lean` (namespace `BGW.Skorokhod`; module file with
`@[expose] public section`). -/

open MeasureTheory Set

namespace BGW.Skorokhod

/-! ## Instance requirements of the vendored projective limit -/

/-- Instance check 1 (needed by `MeasureTheory.projectiveLimit`). -/
example (T : ℝ) : SecondCountableTopology (D T ℝ) := inferInstance

/-- Instance check 2 (needed by `MeasureTheory.projectiveLimit`). -/
example (T : ℝ) : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (D T ℝ) := inferInstance

/-! ## The contract -/

/-- Compatible integer-style horizon families: paths `p n ∈ D(b n, ℝ)` with
`restrict (p (n+1)) = p n` for every `n`. The subtype carries the subspace σ-algebra of the
product of the Borel σ-algebras. -/
def CompatiblePaths (b : ℕ → ℝ) (hb : StrictMono b) : Type :=
  {p : (n : ℕ) → D (b n) ℝ // ∀ n, restrict (hb.monotone (Nat.le_succ n)) (p (n + 1)) = p n}

noncomputable instance (b : ℕ → ℝ) (hb : StrictMono b) : MeasurableSpace (CompatiblePaths b hb) :=
  (inferInstance : MeasurableSpace (Subtype _))

/-- The coordinate map of the compatible-family subtype. -/
def CompatiblePaths.coord {b : ℕ → ℝ} {hb : StrictMono b} (n : ℕ) (p : CompatiblePaths b hb) :
    D (b n) ℝ := p.1 n

/-- Coordinate maps are measurable. -/
theorem CompatiblePaths.measurable_coord (b : ℕ → ℝ) (hb : StrictMono b) (n : ℕ) :
    Measurable (CompatiblePaths.coord (b := b) (hb := hb) n) := sorry

/-- The compatibility set is measurable in `∏ₙ D(b n, ℝ)` (not claimed closed). -/
theorem measurableSet_compatible (b : ℕ → ℝ) (hb : StrictMono b) :
    MeasurableSet {p : (n : ℕ) → D (b n) ℝ |
      ∀ n, restrict (hb.monotone (Nat.le_succ n)) (p (n + 1)) = p n} := sorry

/-- Consistency along all `n ≤ m`: an iterated restriction of `P m` is `P n`, derived from the
one-step hypothesis. Needed to build the max-index family. -/
theorem map_restrict_eq_of_le (b : ℕ → ℝ) (hb : StrictMono b)
    (P : ∀ n, ProbabilityMeasure (D (b n) ℝ))
    (hP : ∀ n, (P (n + 1)).map (restrict (hb.monotone (Nat.le_succ n))) = P n)
    {n m : ℕ} (hnm : n ≤ m) :
    (P m).map (restrict (hb.monotone hnm)) = P n := sorry

/-- The max-index family on finite index sets: the law of the restrictions of a path of
`P (J.sup id)` to the horizons `b j`, `j ∈ J`. For `J = ∅` it is the Dirac law on the empty
product. -/
noncomputable def maxIndexLaw (b : ℕ → ℝ) (hb : StrictMono b)
    (P : ∀ n, ProbabilityMeasure (D (b n) ℝ)) (J : Finset ℕ) :
    Measure ((j : J) → D (b j) ℝ) :=
  (P (J.sup id) : Measure (D (b (J.sup id)) ℝ)).map
    (fun f (j : J) => restrict (hb.monotone (Finset.le_sup (f := id) j.2)) f)

/-- The max-index family is projective (the finite-index adapter, one owner for all clients). -/
theorem isProjectiveMeasureFamily_maxIndexLaw (b : ℕ → ℝ) (hb : StrictMono b)
    (P : ∀ n, ProbabilityMeasure (D (b n) ℝ))
    (hP : ∀ n, (P (n + 1)).map (restrict (hb.monotone (Nat.le_succ n))) = P n) :
    IsProjectiveMeasureFamily (α := fun n => D (b n) ℝ) (maxIndexLaw b hb P) := sorry

/-- **N02.** Existence and uniqueness of the compatible path law with prescribed coordinate
marginals. -/
theorem exists_unique_compatiblePathLaw
    (b : ℕ → ℝ) (hb : StrictMono b) (hb0 : ∀ n, 0 < b n)
    (P : ∀ n, ProbabilityMeasure (D (b n) ℝ))
    (hP : ∀ n, (P (n + 1)).map (restrict (hb.monotone (Nat.le_succ n))) = P n) :
    ∃! Q : ProbabilityMeasure (CompatiblePaths b hb),
      ∀ n, (Q : Measure (CompatiblePaths b hb)).map (CompatiblePaths.coord n) =
        (P n : Measure (D (b n) ℝ)) := sorry

/-- Uniqueness alone, on measures (finite-measure form, product cylinders). -/
theorem CompatiblePaths.measure_ext (b : ℕ → ℝ) (hb : StrictMono b)
    {Q Q' : Measure (CompatiblePaths b hb)} [IsFiniteMeasure Q] [IsFiniteMeasure Q']
    (h : ∀ n, Q.map (CompatiblePaths.coord (hb := hb) n) =
      Q'.map (CompatiblePaths.coord (hb := hb) n)) : Q = Q' := sorry

end BGW.Skorokhod
