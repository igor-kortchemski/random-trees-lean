import BGW.Skorokhod.ProductPaths
import BGW.StableTrees.ForestTriple

/-! Contract probe for CT8 node K13b (deferred from K13 by Sol audit k13k16, finding 1): the
vector-path form of C27.  `CLASSICAL_THEORY_INPUTS.md` C27 (a) states the Duquesne-Le Gall forest
convergence "in `D_T × C_T × C_T` (the C-coordinates after linear interpolation, or in
`D_T(ℝ³)`)".  K13 (sealed, `BGW.StableTrees.ForestTriple`, `tendsto_forestTripleLaw`) proves the
product form.  This node adds the `D_T(ℝ × ℝ × ℝ)` form, for every positive horizon.

DEFINITIONS.  `prodWithCont f g` pairs a càdlàg path `f : D T E` with a continuous path
`g : C([0,T], F)` (metric `E`, `F`) into the càdlàg path `t ↦ (f t, g t)` in `D T (E × F)`.  It
generalizes the sealed scalar map `prodCont` (`BGW/Skorokhod/ProductPaths.lean`, C5.4), whose
proof transfers verbatim: the time changes `σ_n` of `u_n → f` serve for the pair, and in the
continuous coordinate `‖v_n ∘ σ_n - g‖ ≤ ‖v_n - g‖ + ω_g(‖σ_n - id‖) → 0` by uniform
continuity of `g` on the compact `[0,T]`.  `tripleVec (w, h, c) = prodWithCont w (h.prodMk c)`
turns a point of `D_T × C_T × C_T` into a path in `D_T(ℝ × ℝ × ℝ)` with coordinates
`(w t, h t, c t)`.  The vector laws are the images of the K13 laws by `tripleVec`.

TRUTH CHECK.  `tripleVec` is continuous (product of `continuous_prodWithCont` and the continuity
of `(h, c) ↦ h.prodMk c` for the uniform topologies), hence Borel measurable (`D T E` carries its
Borel σ-algebra, `instBorelSpace`; the product `D_T × C_T × C_T` is second countable, separable
`D T ℝ` from `instSeparableSpace` and `C_T`), so the continuous mapping theorem
(`ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous`) applied to K13
`tendsto_forestTripleLaw` gives `tendsto_forestTripleVecLaw`.  The coordinate lemmas are
definitional.  No junk branch: `prodWithCont` is total.  `forestTripleVecLimit_eq` identifies the
limit with the image of the stable process law by `f ↦ (X_t, H_t, H_t)_t` (`map_map`).

PROOF PLAN.  (1) `prodWithCont` and `prodWithCont_apply` (`IsCadlag.continuous_comp₂`, as in
`prodCont`); (2) `continuous_prodWithCont` by the `tendsto_prodCont_aux` argument with `dist` in
`F`; (3) `continuous_tripleVec`; (4) laws and the two theorems by `Measure.map_map` and the
continuous mapping theorem.  Size 150-300 lines; put (1)-(2) in
`BGW/Skorokhod/ProductPathsVector.lean` and (3)-(4) in `BGW/StableTrees/ForestTripleVector.lean`.

BINDER SCOPE (AUDITOR_RULES): no integral, sum or supremum occurs in the new declarations. -/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees

namespace BGW.Skorokhod

variable {T : ℝ} {E F : Type*} [MetricSpace E] [MetricSpace F]

/-- The pair path `(f, g)` of a càdlàg path with values in `E` and a continuous path with
values in `F`. -/
def prodWithCont (f : D T E) (g : C(Set.Icc (0 : ℝ) T, F)) : D T (E × F) :=
  ⟨fun t => (f t, g t), (isCadlag f).continuous_comp₂ g.continuous.isCadlag continuous_id⟩

@[simp]
theorem prodWithCont_apply (f : D T E) (g : C(Set.Icc (0 : ℝ) T, F)) (t : Set.Icc (0 : ℝ) T) :
    prodWithCont f g t = (f t, g t) := sorry

/-- `prodWithCont` is jointly continuous on `D_T(E) × C([0,T], F)` (Skorokhod `J1` topology
and uniform topology). -/
theorem continuous_prodWithCont :
    Continuous (fun p : D T E × C(Set.Icc (0 : ℝ) T, F) => prodWithCont p.1 p.2) := sorry

end BGW.Skorokhod

namespace BGW.StableTrees.ForestTriple

open BGW.StableTrees.DiscreteForest BGW.StableTrees.ForestContour

/-- A walk/height/contour triple as one path in `D_T(ℝ × ℝ × ℝ)`. -/
noncomputable def tripleVec (T : ℝ≥0)
    (x : D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) :
    D (T : ℝ) (ℝ × ℝ × ℝ) :=
  prodWithCont x.1 (x.2.1.prodMk x.2.2)

theorem tripleVec_apply (T : ℝ≥0)
    (x : D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ))
    (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    tripleVec T x t = (x.1 t, x.2.1 t, x.2.2 t) := sorry

theorem continuous_tripleVec (T : ℝ≥0) : Continuous (tripleVec T) := sorry

/-- The law of the forest triple as a path in `D_T(ℝ × ℝ × ℝ)`: walk `W_{⌊nt⌋}/B_n`, height
`(B_n/n) H_lin(nt)`, padded contour `(B_n/n) C_lin(2nt)`. -/
noncomputable def forestTripleVecLaw (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    ProbabilityMeasure (D (T : ℝ) (ℝ × ℝ × ℝ)) :=
  (forestTripleLaw μ B n T).map (tripleVec T)

/-- The vector C27 limit on `[0,T]`: the path `t ↦ (X_t, H_t, H_t)`. -/
noncomputable def forestTripleVecLimit (θ : ℝ) (T : ℝ≥0) :
    ProbabilityMeasure (D (T : ℝ) (ℝ × ℝ × ℝ)) :=
  (forestTripleLimit θ T).map (tripleVec T)

/-- The vector law is the image of the offspring sequence law by the vector forest path. -/
theorem forestTripleVecLaw_eq_map (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    (forestTripleVecLaw μ B n T : Measure (D (T : ℝ) (ℝ × ℝ × ℝ))) =
      (offspringSeqLaw μ : Measure (ℕ → ℕ)).map
        (fun ω => tripleVec T (forestTriplePath B n T ω)) := sorry

/-- The vector limit is the image of the stable process law on `[0,T]` by
`g ↦ (g_t, H_t, H_t)_t`. -/
theorem forestTripleVecLimit_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) :
    (forestTripleVecLimit θ T : Measure (D (T : ℝ) (ℝ × ℝ × ℝ))) =
      (stableProcessLaw θ (T : ℝ) : Measure (D (T : ℝ) ℝ)).map
        (fun g => tripleVec T (g, heightPrefix θ T g, heightPrefix θ T g)) := sorry

/-- **C27, vector-path form (Duquesne-Le Gall, Corollary 2.5.1), every positive horizon**: the
rescaled walk, interpolated height and padded contour of the iid BGW forest, as one path in
`D_T(ℝ × ℝ × ℝ)`, converge in law to `(X, H, H)` on `[0,T]`. -/
theorem tendsto_forestTripleVecLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {T : ℝ≥0} (hT : 0 < T) :
    Tendsto (fun n : ℕ => forestTripleVecLaw μ B n T) atTop (𝓝 (forestTripleVecLimit θ T)) :=
  sorry

end BGW.StableTrees.ForestTriple
