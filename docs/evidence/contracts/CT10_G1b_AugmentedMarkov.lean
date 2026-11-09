import BGW.StableTrees.StableStrongMarkov
import BGW.StableTrees.ReflectedRestart
import BGW.StableTrees.ExcursionGapsStrongMarkov

/-! Contract probe for CT10 node G1b: the strong Markov property of the reflected process for
the AUGMENTED canonical filtration (Sol audit `sol-audit-g1`, finding 1).

SOURCE (`CLASSICAL_THEORY_INPUTS.md` C20(a), first claim).  "`X − I` is a strong Markov process
for `(F_t)` (the canonical filtration of X, augmented)".  Node G1 (`CT10_G1_ExcursionGaps.lean`,
`condExp_reflectedFutureAt`) proves it for `DLoc.filtration`, the right-continuous raw
filtration, which is law independent and has no null sets.  Stopping times of the augmented
filtration are more general and their stopped σ-algebras larger, so the augmented statement is
not a consequence by the tower property; it needs a completion transfer.

DEFINITIONS.  On the completed space `NullMeasurableSpace DLoc (stableLocalLaw θ)` (the
completion σ-algebra of the stable law), `stableAugmentedBase θ t = DLoc.filtration t ⊔ σ(null
sets)` and `stableAugmentedFiltration θ` is its right-continuous regularization (the usual
augmentation).  `reflectedStateAt`, `reflectedFutureAt` are copied from G1.

TRUTH CHECK.  Standard (Revuz-Yor I.4, III.2): for an augmented stopping time `τ` there is a
`DLoc.filtration` stopping time `τ'` with `τ = τ'` almost surely (built from countably many
rational sublevel events, each equal to a raw-right-continuous event modulo a null set), and
every event of the augmented stopped σ-algebra differs from an event of `F_{τ'}` by a null set.
Both sides of the identity then agree almost surely with those for `τ'`, where G1 applies.  The
conclusion uses the completed law; no new hypothesis is added (`hfin` as in G1).

PROOF PLAN.  (1) `stableAugmentedFiltration` is a filtration of the completion σ-algebra
(elaborated by the Sol audit).  (2) Raw version `τ'` of an augmented stopping time, a.s. equal
(100-200 lines).  (3) Stopped σ-algebras agree modulo null sets (80-150 lines).  (4) Conditional
expectations on the completion agree with those of the original law for Borel integrands
(`MeasureTheory.Measure.completion`, `condExp` congruence, 60-120 lines).  (5) Combine with G1
`condExp_reflectedFutureAt` at `τ'`.  Size 300-500 lines.

ACYCLICITY.  Consumes G1 (to be sealed first; the copies below are then replaced by its import),
the sealed strong Markov property and the reflected restart.

BINDER SCOPE (AUDITOR_RULES): the conditional expectation and the integral have nothing after
them. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The canonical space with the completion σ-algebra of the stable law. -/
abbrev StableCompletedSpace (θ : ℝ) :=
  NullMeasurableSpace DLoc (stableLocalLaw θ : Measure DLoc)

/-- The raw right-continuous filtration joined with the null sets of the stable law. -/
noncomputable def stableAugmentedBase (θ : ℝ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (StableCompletedSpace θ)) where
  seq t := DLoc.filtration t ⊔
    MeasurableSpace.generateFrom {A : Set DLoc | (stableLocalLaw θ : Measure DLoc) A = 0}
  mono' _ _ hst := sup_le_sup (DLoc.filtration.mono hst) le_rfl
  le' t := sup_le
    (fun A hA => ((DLoc.filtration.le t) A hA).nullMeasurableSet)
    (MeasurableSpace.generateFrom_le fun _ hA => NullMeasurableSet.of_null hA)

/-- The usual augmentation of the canonical filtration under the stable law. -/
noncomputable def stableAugmentedFiltration (θ : ℝ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (StableCompletedSpace θ)) :=
  (stableAugmentedBase θ).rightCont

/-- **C20.1, strong Markov property for the augmented filtration.**  For a stopping time of the
usual augmentation, conditionally on its stopped σ-algebra, the post-τ reflected path has the
reflected stable transition law started at its stopped reflected value. -/
theorem condExp_reflectedFutureAt_augmented {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {τ : StableCompletedSpace θ → ℝ≥0∞}
    (hτ : IsStoppingTime (stableAugmentedFiltration θ) τ)
    (hfin : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc).completion, τ f < ⊤)
    {G : DLoc → ℝ} (hG : Measurable G) (hGb : ∃ C : ℝ, ∀ p, |G p| ≤ C) :
    (stableLocalLaw θ : Measure DLoc).completion[
        fun f => G (reflectedFutureAt τ f) | hτ.measurableSpace]
      =ᵐ[(stableLocalLaw θ : Measure DLoc).completion]
      fun f => ∫ g, G (reflectedFrom (reflectedStateAt τ f) g)
        ∂(stableLocalLaw θ : Measure DLoc) := sorry

end BGW.StableTrees
