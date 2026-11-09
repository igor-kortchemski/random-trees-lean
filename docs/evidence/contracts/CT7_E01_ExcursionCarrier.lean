import BGW.Skorokhod.DLoc

/-! Contract probe for CT7 node E01 (tagged excursion carrier, cutting, scaling; C21 infrastructure),
following `r3-ct7-blueprint/blueprint.md` §2 and the "first three nodes" of `AUDIT.md`.

CARRIER CHOICE (flagged). `Excursion` is the Borel subtype of `DLoc × Set.Ioi (0 : ℝ≥0)` with
coordinates `path` and `lifetime` (the tag), cut out by the three countably-describable conditions
`path 0 = 0`, `path ≥ 0`, `path = 0` at and after the tag.  No strict interior positivity, no
"no negative jumps", no endpoint left-continuity and no "tag = true lifetime" in the constructor:
those are support theorems of the constructed excursion measure (E02-E05).
Why `DLoc` and not `D T ℝ`: the excursion measure `N` lives on excursions of arbitrary finite
lifetime, and the marks are cut out of full `DLoc` paths; a horizon-`T` carrier cannot hold them.
The import closure therefore contains `BGW.Skorokhod.PathLawFamily` and hence
`KolmogorovExtension4` (not Mathlib-only).  Horizon-`a` restrictions land in the sealed
`D a ℝ` (`excursionRestrict`).

JUNK CONVENTION. The zero path with tag one is `junkExcursion`; its tag is NOT its true lifetime.
`excursionCut g d f` is the cut of `f` between times `g < d` whenever it is a valid excursion
(`cutValid`: `f d = f g` and `f ≥ f g` on `[g,d]`), and `junkExcursion` otherwise.
Cut path: `t ↦ f (min (g+t) d) - f g` (this is `stopLoc (d-g) (DLoc.shift g f)`).

SCALING. `excursionScale θ c e` has path `t ↦ c^(1/θ) * e(t/c)` and tag `c * ζ`: lifetime
multiplies by `c`, space by `c^(1/θ)`.  With this sign `(S_c)_* N = c^(1/θ) N` (AUDIT item 7:
`N(ζ>t) = t^(-1/θ)/Γ(1-1/θ)`, so `N(cζ>t) = c^(1/θ) N(ζ>t)`).
`normalizeExc θ e = excursionScale θ (1/ζ) e` has lifetime one.

Sealed inputs reused (not re-declared): `DLoc`, `DLoc.eval`, `DLoc.shift`, `DLoc.restrict`,
`DLoc.measurable_eval`, `DLoc.measurable_eval₂`, `DLoc.measurable_restrict`,
`DLoc.measurableEquivCompatible`.  
STANDARD BORELNESS (flagged).  The instance `StandardBorelSpace Excursion` requires proving that
the compatible integer-horizon families form a Borel subset of the countable product of Polish
`D (n+1) ℝ`; NO `StandardBorelSpace DLoc` instance exists yet.  The intermediate statements
`measurableSet_compatibleFamilies` and `instance : StandardBorelSpace DLoc` are stated below as
separate `sorry` theorems and feed `instance : StandardBorelSpace Excursion`.

PROOF OBLIGATIONS ARE NOT INLINED: every càdlàg/validity proof used by a definition is a named
theorem (`isCadlag_stopLoc`, `isCadlag_scaleLoc`, `isExcursionTag_cutPath`,
`isExcursionTag_scale`); the definitions themselves contain no `sorry`.
Estimate 450-800 lines. -/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Stopping a càdlàg path at a deterministic time is càdlàg. -/
theorem isCadlag_stopLoc (a : ℝ≥0) (f : DLoc) : IsCadlag (fun t : ℝ≥0 => f.1 (min t a)) := sorry

/-- Stopping a local path at a deterministic time: `t ↦ f (min t a)`. -/
noncomputable def stopLoc (a : ℝ≥0) (f : DLoc) : DLoc :=
  ⟨fun t => f.1 (min t a), isCadlag_stopLoc a f⟩

/-- The constant zero local path. -/
noncomputable def zeroLoc : DLoc := ⟨fun _ => 0, IsCadlag.const⟩

/-- The path of the cut of `f` between times `g` and `d`: `t ↦ f (min (g+t) d) - f g`
(for `g ≤ d`). -/
noncomputable def cutPath (g d : ℝ≥0) (f : DLoc) : DLoc :=
  stopLoc (d - g) (DLoc.shift g f)

/-- The valid-excursion conditions on a (path, tag) pair: starts at `0`, nonnegative, identically
zero at and after the tag. -/
def IsExcursionTag (p : DLoc × Set.Ioi (0 : ℝ≥0)) : Prop :=
  p.1.1 0 = 0 ∧ (∀ t, 0 ≤ p.1.1 t) ∧ ∀ t : ℝ≥0, (p.2 : ℝ≥0) ≤ t → p.1.1 t = 0

/-- The tagged excursion carrier (Borel subtype of `DLoc × Ioi 0`). -/
def Excursion : Type := {p : DLoc × Set.Ioi (0 : ℝ≥0) // IsExcursionTag p}

noncomputable instance : MeasurableSpace Excursion :=
  (inferInstance : MeasurableSpace {p : DLoc × Set.Ioi (0 : ℝ≥0) // IsExcursionTag p})

namespace Excursion

/-- The path coordinate. -/
def path (e : Excursion) : DLoc := e.1.1
/-- The tagged lifetime. -/
def lifetime (e : Excursion) : ℝ≥0 := e.1.2
/-- The tagged lifetime as a positive real. -/
def lifetimePos (e : Excursion) : Set.Ioi (0 : ℝ) := ⟨(e.lifetime : ℝ), NNReal.coe_pos.2 e.1.2.2⟩

theorem lifetime_pos (e : Excursion) : 0 < e.lifetime := e.1.2.2

end Excursion

/-- Cut-validity: between times `g < d`, `f d = f g` and `f ≥ f g` on `[g, d]`.

CAVEAT: a valid cut uses the POST-JUMP value `f g` as the base level (the cut path is
`f(g + ·) - f g`), so `excursionCut` never represents an excursion that starts with a jump out of
the infimum (jump-start components `[g,d)` of E02a); this is consistent with
`IsExcursionInterval` of E02a, which requires `R g = 0`. -/
def cutValid (g d : ℝ≥0) (f : DLoc) : Prop :=
  g < d ∧ f.1 d = f.1 g ∧ ∀ t : ℝ≥0, g ≤ t → t ≤ d → f.1 g ≤ f.1 t

/-- The cut of a valid window, with tag `d - g`, satisfies the excursion-tag conditions. -/
theorem isExcursionTag_cutPath {g d : ℝ≥0} {f : DLoc} (h : cutValid g d f) :
    IsExcursionTag (cutPath g d f, ⟨d - g, tsub_pos_of_lt h.1⟩) := sorry

/-- Measurability of the validity predicate: a Borel subset of `DLoc × Ioi 0`. -/
theorem measurableSet_isExcursionTag : MeasurableSet {p : DLoc × Set.Ioi (0 : ℝ≥0) | IsExcursionTag p} :=
  sorry

/-- **Compatible families form a Borel set**: the integer-horizon compatible families are a
measurable subset of the countable product of the spaces `D (n+1) ℝ`. -/
theorem measurableSet_compatibleFamilies :
    MeasurableSet {p : (n : ℕ) → D ((n : ℝ) + 1) ℝ | ∀ n : ℕ,
      BGW.Skorokhod.restrict (strictMono_succHorizon.monotone (Nat.le_succ n)) (p (n + 1)) =
        p n} := sorry

/-- **`DLoc` is standard Borel** (measurably equivalent to the Borel set of compatible families
in a countable product of standard Borel spaces `D (n+1) ℝ`). -/
instance : StandardBorelSpace DLoc := sorry

/-- **Standard Borel.** The carrier is a standard Borel space (through
`DLoc.measurableEquivCompatible` and the Borel compatible-family subset of the countable product
of Polish `D (n+1) ℝ`; no closedness or J1-completeness is assumed). -/
instance : StandardBorelSpace Excursion := sorry

/-- The junk excursion: zero path with tag one. -/
noncomputable def junkExcursion : Excursion :=
  ⟨(zeroLoc, ⟨1, Set.mem_Ioi.2 one_pos⟩), by
    refine ⟨rfl, fun t => le_refl _, fun t _ => rfl⟩⟩

/-- Measurability of the path coordinate. -/
theorem measurable_excursion_path : Measurable (Excursion.path) := sorry

/-- Measurability of the tagged lifetime. -/
theorem measurable_excursion_lifetime : Measurable (Excursion.lifetime) := sorry

/-- Measurability of each coordinate evaluation `e ↦ e(t)`. -/
theorem measurable_excursion_eval (t : ℝ≥0) : Measurable (fun e : Excursion => e.path.1 t) := sorry

/-- **Joint evaluation** `(e, t) ↦ e(t)` is measurable. -/
theorem measurable_excursion_eval₂ :
    Measurable (fun p : Excursion × ℝ≥0 => p.1.path.1 p.2) := sorry

/-- `e ↦ e(ζ(e))` evaluates to `0` (the path is stopped at the tag), so evaluation at the tag is
trivially measurable; kept as the sanity statement that the tag convention is "zero at the tag". -/
theorem excursion_path_zero_at_lifetime (e : Excursion) : e.path.1 e.lifetime = 0 :=
  e.2.2.2 _ le_rfl

/-- Cutting a path at a window `[g, d]`: the excursion with path `t ↦ f (min (g+t) d) - f g` and
tag `d - g` when the cut is valid, the junk excursion otherwise.  A valid cut is based at the
post-jump value `f g`, so an excursion starting with a jump out of the infimum is never
represented (see `cutValid`). -/
noncomputable def excursionCut (g d : ℝ≥0) (f : DLoc) : Excursion :=
  letI := Classical.propDecidable (cutValid g d f)
  if h : cutValid g d f then
    ⟨(cutPath g d f, ⟨d - g, tsub_pos_of_lt h.1⟩), isExcursionTag_cutPath h⟩
  else junkExcursion

/-- **Junk branch.** -/
theorem excursionCut_of_not_cutValid {g d : ℝ≥0} {f : DLoc} (h : ¬ cutValid g d f) :
    excursionCut g d f = junkExcursion := by
  unfold excursionCut
  simp [h]

/-- **Exact evaluation formula** for cutting between two finite times with equal values. -/
theorem excursionCut_eval {g d : ℝ≥0} {f : DLoc} (h : cutValid g d f) (t : ℝ≥0) :
    (excursionCut g d f).path.1 t = f.1 (min (g + t) d) - f.1 g := sorry

/-- The lifetime of a valid cut is the window length. -/
theorem excursionCut_lifetime {g d : ℝ≥0} {f : DLoc} (h : cutValid g d f) :
    (excursionCut g d f).lifetime = d - g := sorry

/-- The validity set is jointly measurable in `(g, d, f)`. -/
theorem measurableSet_cutValid :
    MeasurableSet {p : ℝ≥0 × ℝ≥0 × DLoc | cutValid p.1 p.2.1 p.2.2} := sorry

/-- **Joint cut measurability**: `(g, d, f) ↦ excursionCut g d f` is measurable jointly (not
merely at fixed times). -/
theorem measurable_excursionCut :
    Measurable (fun p : ℝ≥0 × ℝ≥0 × DLoc => excursionCut p.1 p.2.1 p.2.2) := sorry

/-- Space-time scaling of a càdlàg path is càdlàg. -/
theorem isCadlag_scaleLoc (θ : ℝ) (c : Set.Ioi (0 : ℝ)) (f : DLoc) :
    IsCadlag (fun t : ℝ≥0 => (c : ℝ) ^ (1 / θ) * f.1 (t / (c : ℝ).toNNReal)) := sorry

/-- Scaling of the underlying path: `t ↦ c^(1/θ) * f (t / c)`. -/
noncomputable def scaleLoc (θ : ℝ) (c : Set.Ioi (0 : ℝ)) (f : DLoc) : DLoc :=
  ⟨fun t => (c : ℝ) ^ (1 / θ) * f.1 (t / (c : ℝ).toNNReal), isCadlag_scaleLoc θ c f⟩

/-- Scaling preserves the excursion-tag conditions (with tag `c ζ`). -/
theorem isExcursionTag_scale (θ : ℝ) (c : Set.Ioi (0 : ℝ)) (e : Excursion) :
    IsExcursionTag (scaleLoc θ c e.path, ⟨(c : ℝ).toNNReal * e.lifetime,
      mul_pos (Real.toNNReal_pos.2 c.2) e.lifetime_pos⟩) := sorry

/-- **Excursion scaling `S_c`**: path `c^(1/θ) e(t/c)`, tag `c * ζ`; the lifetime multiplies by `c`. -/
noncomputable def excursionScale (θ : ℝ) (c : Set.Ioi (0 : ℝ)) (e : Excursion) : Excursion :=
  ⟨(scaleLoc θ c e.path, ⟨(c : ℝ).toNNReal * e.lifetime,
      mul_pos (Real.toNNReal_pos.2 c.2) e.lifetime_pos⟩), isExcursionTag_scale θ c e⟩

/-- Scaling multiplies the lifetime by `c`. -/
theorem excursionScale_lifetime (θ : ℝ) (c : Set.Ioi (0 : ℝ)) (e : Excursion) :
    ((excursionScale θ c e).lifetime : ℝ) = (c : ℝ) * e.lifetime := sorry

/-- **Scale group law** (identity). -/
theorem excursionScale_one (θ : ℝ) (e : Excursion) :
    excursionScale θ ⟨1, Set.mem_Ioi.2 one_pos⟩ e = e := sorry

/-- **Scale group law** (composition). -/
theorem excursionScale_mul (θ : ℝ) (c₁ c₂ : Set.Ioi (0 : ℝ)) (e : Excursion) :
    excursionScale θ c₁ (excursionScale θ c₂ e) =
      excursionScale θ ⟨(c₁ : ℝ) * c₂, Set.mem_Ioi.2 (mul_pos c₁.2 c₂.2)⟩ e := sorry

/-- Scaling is measurable at each fixed `c`. -/
theorem measurable_excursionScale (θ : ℝ) (c : Set.Ioi (0 : ℝ)) :
    Measurable (excursionScale θ c) := sorry

/-- Scaling is jointly measurable in `(c, e)`. -/
theorem measurable_excursionScale_joint (θ : ℝ) :
    Measurable (fun p : Set.Ioi (0 : ℝ) × Excursion => excursionScale θ p.1 p.2) := sorry

/-- **Normalization**: rescale to lifetime one, `S_{1/ζ} e`. -/
noncomputable def normalizeExc (θ : ℝ) (e : Excursion) : Excursion :=
  excursionScale θ ⟨((e.lifetime : ℝ≥0) : ℝ)⁻¹, inv_pos.2 (NNReal.coe_pos.2 e.lifetime_pos)⟩ e

/-- A normalized excursion has lifetime one. -/
theorem normalizeExc_lifetime (θ : ℝ) (e : Excursion) : (normalizeExc θ e).lifetime = 1 := sorry

/-- **Measurable normalization** (variable positive scaling `c = 1/ζ(e)`; the raw functional need
not be J1-continuous). -/
theorem measurable_normalizeExc (θ : ℝ) : Measurable (normalizeExc θ) := sorry

/-- Restriction of an excursion to the horizon `[0, T]`, as a path in the sealed compact space. -/
noncomputable def excursionRestrict (T : ℝ≥0) (e : Excursion) : D (T : ℝ) ℝ :=
  DLoc.restrict T e.path

/-- Restriction is measurable, for the Borel `σ`-algebra of `D T ℝ`. -/
theorem measurable_excursionRestrict (T : ℝ≥0) : Measurable (excursionRestrict T) := sorry

/-- **Lifetime/shape map**: `e ↦ (ζ(e), normalized e)`. -/
noncomputable def shapeLifetime (θ : ℝ) (e : Excursion) : Set.Ioi (0 : ℝ) × Excursion :=
  (e.lifetimePos, normalizeExc θ e)

/-- **Inverse map** `(ζ, s) ↦ S_ζ s`. -/
noncomputable def fromShapeLifetime (θ : ℝ) (p : Set.Ioi (0 : ℝ) × Excursion) : Excursion :=
  excursionScale θ p.1 p.2

theorem measurable_shapeLifetime (θ : ℝ) : Measurable (shapeLifetime θ) := sorry

theorem measurable_fromShapeLifetime (θ : ℝ) : Measurable (fromShapeLifetime θ) := sorry

/-- `fromShapeLifetime ∘ shapeLifetime = id` on all excursions. -/
theorem fromShapeLifetime_shapeLifetime (θ : ℝ) (e : Excursion) :
    fromShapeLifetime θ (shapeLifetime θ e) = e := sorry

/-- `shapeLifetime ∘ fromShapeLifetime = id` on (lifetime, unit-lifetime shape) pairs. -/
theorem shapeLifetime_fromShapeLifetime (θ : ℝ) (ζ : Set.Ioi (0 : ℝ)) (s : Excursion)
    (hs : s.lifetime = 1) : shapeLifetime θ (fromShapeLifetime θ (ζ, s)) = (ζ, s) := sorry

end BGW.StableTrees
