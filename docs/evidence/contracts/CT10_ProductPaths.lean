import BGW.Skorokhod.ContinuousEmbedding
import BGW.Skorokhod.TimeChange

/-! Contract probe for CT.C5.4 (vector-valued formulation, CT10): Jacod-Shiryaev VI.2.2.
`f_n → f` in `D_T(ℝ)` and `g_n → g` uniformly with `g` (and each `g_n`) continuous gives
`(f_n, g_n) → (f, g)` in `D_T(ℝ × ℝ)` (J1 with the sup metric on `ℝ × ℝ`), because the same time
change that makes `f_n ∘ λ_n → f` uniformly also does it for `g_n ∘ λ_n → g` (uniform continuity
of `g` and `‖λ_n - id‖ → 0`).

TRUTH. Both entries are continuous, so the pair is càdlàg. Joint continuity at every point of
`D_T(ℝ) × C([0,T],ℝ)` holds, not only at limits: the argument above uses only that the limit
`g` is continuous, and all `g_n` are continuous by type. For `T < 0` the interval is empty and
the statement is trivial; no `0 ≤ T` hypothesis is needed (the sealed
`tendsto_iff_exists_timeChange` is stated for arbitrary `T`). The converse (projections `D(ℝ²) → D(ℝ)` continuous) is the
coordinate map; the law-level converse needs both coordinates continuous in law.

PROOF PLAN. `tendsto_iff_exists_timeChange` for the first factor (gives `σ_n`), uniform continuity
of `g` on the compact interval (as in `tendsto_iSup_dist_of_tendsto_ofContinuous`), triangle
inequality with `‖g_n - g‖_∞`, then `tendsto_iff_exists_timeChange` for the product. 120-250
lines. Law form follows from `Continuous.tendsto` and the continuous mapping theorem. -/

open Filter Topology

namespace BGW.Skorokhod

variable {T : ℝ}

/-- The pair path `(f, g)` of a càdlàg path and a continuous path. -/
def prodCont (f : D T ℝ) (g : C(Set.Icc (0 : ℝ) T, ℝ)) : D T (ℝ × ℝ) :=
  ⟨fun t => (f t, g t), sorry⟩

/-- CT.C5.4: `prodCont` is jointly continuous on `D_T(ℝ) × C([0,T],ℝ)`. -/
theorem continuous_prodCont :
    Continuous (fun p : D T ℝ × C(Set.Icc (0 : ℝ) T, ℝ) => prodCont p.1 p.2) := sorry

/-- Sequential form of CT.C5.4. -/
theorem tendsto_prodCont {ι : Type*} {l : Filter ι} {u : ι → D T ℝ} {f : D T ℝ}
    {v : ι → C(Set.Icc (0 : ℝ) T, ℝ)} {g : C(Set.Icc (0 : ℝ) T, ℝ)}
    (hu : Tendsto u l (𝓝 f)) (hv : Tendsto v l (𝓝 g)) :
    Tendsto (fun i => prodCont (u i) (v i)) l (𝓝 (prodCont f g)) := sorry

end BGW.Skorokhod
