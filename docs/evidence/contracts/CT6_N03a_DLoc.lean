import BGW.Skorokhod.Restrict
import BGW.Skorokhod.MeasurableMaps
import BGW.Skorokhod.Measurable
import BGW.Skorokhod.MeasurableLaws
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Process.Adapted
import Mathlib.Topology.Order.Cadlag
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Contract probe for CT.C6 blueprint Node 3a (audit correction 1): the DETERMINISTIC local càdlàg
carrier `DLoc := {f : ℝ≥0 → ℝ // IsCadlag f}` with the evaluation σ-algebra, no law involved.
It exposes: measurable restriction to `D([0,T], ℝ)`, evaluation, centered shift, gluing from
integer-horizon compatible families, extensionality by restrictions (pointwise and for finite
measures), the natural filtration (named `DLoc.rawFiltration`, no `θ`), its right-continuous
version `DLoc.filtration`, and the strict-passage stopping times.

Strict passages only (audit correction 8): the raw `F⁺` filtration makes `inf{t | f t > x}` and
`inf{t | f t < x}` (open-set debuts) stopping times; closed-set debuts and `T_{x-}` are NOT
claimed. Compatible-family subtype (internal to N02/N03) is copied from CT6_N02 below.
Maintained file: `BGW/Skorokhod/LocalPaths.lean` (namespace `BGW.Skorokhod`). -/

open MeasureTheory Set Filter Topology MeasureTheory.Filtration
open scoped NNReal

/-! ## Copied declarations (not part of this contract) -/

namespace BGW.Skorokhod

-- copied from contract CT6_N02_PathLawFamily (not part of this contract)
def CompatiblePaths (b : ℕ → ℝ) (hb : StrictMono b) : Type :=
  {p : (n : ℕ) → D (b n) ℝ // ∀ n, restrict (hb.monotone (Nat.le_succ n)) (p (n + 1)) = p n}

-- copied from contract CT6_N02_PathLawFamily (not part of this contract)
noncomputable instance (b : ℕ → ℝ) (hb : StrictMono b) : MeasurableSpace (CompatiblePaths b hb) :=
  (inferInstance : MeasurableSpace (Subtype _))

/-- The integer horizons `n + 1` (positive, strictly increasing), as used by N02 for the process. -/
theorem strictMono_succHorizon : StrictMono (fun n : ℕ => (n : ℝ) + 1) := by
  intro m n h; simpa using h

/-! ## The contract -/

/-- The local càdlàg carrier: càdlàg real paths on `ℝ≥0` (Mathlib's `IsCadlag`; at `0` the left
limit is vacuous). -/
def DLoc : Type := {f : ℝ≥0 → ℝ // IsCadlag f}

namespace DLoc

/-- Evaluation at time `t`. -/
def eval (t : ℝ≥0) (f : DLoc) : ℝ := f.1 t

/-- The evaluation σ-algebra: the supremum of the pullbacks of the Borel σ-algebra of `ℝ` under
all evaluations. -/
noncomputable instance : MeasurableSpace DLoc :=
  ⨆ t : ℝ≥0, MeasurableSpace.comap (eval t) inferInstance

/-- Restriction to `[0, T]`, as an element of the compact path space. -/
def restrict (T : ℝ≥0) (f : DLoc) : D (T : ℝ) ℝ where
  toFun t := f.1 ⟨t.1, t.2.1⟩
  isCadlag' := sorry

/-- Centered shift: `u ↦ f (s + u) - f s`. -/
def shift (s : ℝ≥0) (f : DLoc) : DLoc :=
  ⟨fun u => f.1 (s + u) - f.1 s, sorry⟩

theorem measurable_eval (t : ℝ≥0) : Measurable (eval t) := sorry

/-- Restriction to every compact horizon is measurable. -/
theorem measurable_restrict (T : ℝ≥0) : Measurable (restrict T) := sorry

/-- The σ-algebra is the supremum of the pullbacks of the integer-horizon restrictions. -/
theorem measurableSpace_eq_iSup_comap_restrict :
    (inferInstance : MeasurableSpace DLoc) =
      ⨆ n : ℕ, MeasurableSpace.comap (restrict (n : ℝ≥0)) inferInstance := sorry

/-- Joint measurability of `(f, t) ↦ f t`. -/
theorem measurable_eval₂ : Measurable (fun p : DLoc × ℝ≥0 => p.1.1 p.2) := sorry

/-- Joint measurability of the centered shift `(s, f) ↦ shift s f`. -/
theorem measurable_shift : Measurable (fun p : ℝ≥0 × DLoc => shift p.1 p.2) := sorry

/-- The shift is a semigroup action: `shift s (shift t f) = shift (t + s) f`. -/
theorem shift_shift (s t : ℝ≥0) (f : DLoc) : shift s (shift t f) = shift (t + s) f := sorry

/-- Restrictions are compatible with each other. -/
theorem restrict_restrict {a T : ℝ≥0} (h : a ≤ T) (f : DLoc) :
    BGW.Skorokhod.restrict (show (a : ℝ) ≤ T from h) (restrict T f) = restrict a f := sorry

/-- Extensionality by restrictions to the integer horizons. -/
theorem ext_of_restrict {f g : DLoc} (h : ∀ n : ℕ, restrict (n : ℝ≥0) f = restrict (n : ℝ≥0) g) :
    f = g := sorry

/-- The compatible integer-horizon family of a local path (horizons `n + 1`). -/
def toCompatible (f : DLoc) : CompatiblePaths (fun n : ℕ => (n : ℝ) + 1) strictMono_succHorizon :=
  ⟨fun n => restrict ⟨(n : ℝ) + 1, by positivity⟩ f, sorry⟩

/-- Gluing: a compatible integer-horizon family determines a local càdlàg path. -/
noncomputable def glue (p : CompatiblePaths (fun n : ℕ => (n : ℝ) + 1) strictMono_succHorizon) : DLoc :=
  ⟨fun t => (p.1 ⌈(t : ℝ)⌉₊) ⟨t, sorry⟩, sorry⟩

/-- Gluing restricts back to the family. -/
theorem restrict_glue (p : CompatiblePaths (fun n : ℕ => (n : ℝ) + 1) strictMono_succHorizon)
    (n : ℕ) (t : Set.Icc (0 : ℝ) ((n : ℝ) + 1)) :
    (glue p).1 ⟨t.1, t.2.1⟩ = p.1 n t := sorry

/-- The gluing is inverted by the family of restrictions. -/
theorem glue_toCompatible (f : DLoc) : glue (toCompatible f) = f := sorry

theorem toCompatible_glue
    (p : CompatiblePaths (fun n : ℕ => (n : ℝ) + 1) strictMono_succHorizon) :
    toCompatible (glue p) = p := sorry

/-- `DLoc` is measurably equivalent to the compatible-family subtype (so laws constructed by N02
transfer to `DLoc`, and the subtype stays internal). -/
noncomputable def measurableEquivCompatible :
    DLoc ≃ᵐ CompatiblePaths (fun n : ℕ => (n : ℝ) + 1) strictMono_succHorizon where
  toEquiv := ⟨toCompatible, glue, glue_toCompatible, toCompatible_glue⟩
  measurable_toFun := sorry
  measurable_invFun := sorry

/-- Two finite measures with equal restrictions to every integer horizon are equal. -/
theorem measure_ext_of_restrict {P Q : Measure DLoc} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : ∀ n : ℕ, P.map (restrict (n : ℝ≥0)) = Q.map (restrict (n : ℝ≥0))) : P = Q := sorry

/-! ### Filtrations -/

/-- The natural (raw) filtration `F_t = σ(f s : s ≤ t)`. It does not depend on any law. -/
noncomputable def rawFiltration : Filtration ℝ≥0 (inferInstance : MeasurableSpace DLoc) where
  seq t := ⨆ s ≤ t, MeasurableSpace.comap (eval s) inferInstance
  mono' _ _ hst := biSup_mono fun _ hs => hs.trans hst
  le' _ := iSup₂_le fun s _ => le_iSup (fun r : ℝ≥0 => MeasurableSpace.comap (eval r) inferInstance) s

/-- The right-continuous natural filtration `F⁺_t = ⋂_{u > t} F_u` (Mathlib's `rightCont`). -/
noncomputable def filtration : Filtration ℝ≥0 (inferInstance : MeasurableSpace DLoc) :=
  rawFiltration.rightCont

instance : DLoc.filtration.IsRightContinuous := inferInstanceAs rawFiltration.rightCont.IsRightContinuous

/-- The σ-algebra of `DLoc` is the supremum of the raw filtration. -/
theorem iSup_rawFiltration :
    ⨆ t, rawFiltration t = (inferInstance : MeasurableSpace DLoc) := sorry

/-- The coordinate process is adapted to the raw filtration, hence to `filtration`. -/
theorem adapted_eval : Adapted filtration (fun t (f : DLoc) => f.1 t) := sorry

/-- Càdlàg coordinate process is progressively measurable. -/
theorem isStronglyProgressive_eval :
    IsStronglyProgressive filtration (fun t (f : DLoc) => f.1 t) := sorry

/-! ### Strict passage times -/

/-- `T_x = inf {t | f t > x}` (strict passage upward); `⊤` if the set is empty. -/
noncomputable def strictPassageAbove (x : ℝ) (f : DLoc) : WithTop ℝ≥0 :=
  ⨅ (t : ℝ≥0) (_ : x < f.1 t), (t : WithTop ℝ≥0)

/-- `inf {t | f t < x}` (strict passage downward). -/
noncomputable def strictPassageBelow (x : ℝ) (f : DLoc) : WithTop ℝ≥0 :=
  ⨅ (t : ℝ≥0) (_ : f.1 t < x), (t : WithTop ℝ≥0)

/-- Deterministic description by rationals (right-continuity): `T_x < t` iff some rational time
before `t` has value above `x`. -/
theorem strictPassageAbove_lt_iff (x : ℝ) (f : DLoc) (t : ℝ≥0) :
    strictPassageAbove x f < t ↔ ∃ q : ℚ, 0 ≤ q ∧ (q : ℝ) < t ∧ x < f.1 (Real.toNNReal q) := sorry

/-- `T_x` is a stopping time of the right-continuous filtration. -/
theorem isStoppingTime_strictPassageAbove (x : ℝ) :
    IsStoppingTime filtration (strictPassageAbove x) := sorry

/-- `inf {t | f t < x}` is a stopping time of the right-continuous filtration. -/
theorem isStoppingTime_strictPassageBelow (x : ℝ) :
    IsStoppingTime filtration (strictPassageBelow x) := sorry

/-- Deterministic reflection identity (audit, F3): `inf{t | f t < -x}` is the strict passage of
`-f` above `x`. -/
theorem strictPassageBelow_neg (x : ℝ) (f : DLoc) :
    strictPassageBelow (-x) f = strictPassageAbove x (⟨fun t => -f.1 t, sorry⟩ : DLoc) := sorry

end DLoc

end BGW.Skorokhod
