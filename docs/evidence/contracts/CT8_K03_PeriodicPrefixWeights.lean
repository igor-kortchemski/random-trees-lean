import BGW.StableTrees.KendallAdapter
import BGW.StableTrees.StableKendallLocal
import BGW.StableTrees.Attraction.Defs
import BGW.StableTrees.Scalar.ForestBounds
import BGW.StableTrees.Scalar.LocalLimit

/-! # Contract CT8 / K03: periodic local and tail limits, and exact-prefix RN weights

NOTATION.  `μ` critical offspring law in the domain of attraction of the spectrally positive
`θ`-stable law with norming `B` (`ST.StableDomain μ θ B`); `d = Scalar.latticeSpan μ` the span of
the support differences (`μ 0 > 0`, so `μ_n > 0` for large `n` forces `d ∣ n - 1`-type lattices);
`p₀ = p₁(0) = Scalar.stableDensity θ 0 > 0`; `q = qKernel θ` (`q_s(x) = (x/s) p_s(-x)`);
`G = sizeTailKernel θ` (`G_r(x) = ∫_{s>r} q_s(x) ds`); `f_j(r) = forestMass μ j r =
(BGW.forestWeight μ j r).toReal` (probability that a `j`-forest has `r` vertices);
`G_j(r) = forestTail μ j r = ∑_{k ≥ r} f_j(k)`.

TRUTH (constants, `d` is never dropped).
* Lattice LLT (`Scalar.localLimit`): `B_n P(S_n = k) - d p_n(k/B_n) → 0` uniformly on
  `d ∣ k + n`; zero off the lattice.  Kemperman gives `f_j(r) = (j/r) P(S_r = -j)`.
  Hence, with `r/n ∈ [a,b]` and only `d ∣ r - j`:
  `n f_j(r) - d q_{r/n}(j/B_n) → 0` (the factor `d` stays; B_r/B_n → (r/n)^{1/θ} by regular
  variation moves `p_r(-j/B_r)` to `p_{r/n}(-j/B_n)` up to the scaling of `qKernel`).
* Tail: summing the local limit over the residue class `r ≡ j (mod d)` gives mesh `d/n`,
  which cancels the coefficient `d`: `G_j(r) - G_{r/n}(j/B_n) → 0` with NO lattice condition.
  Large-range tails use `Scalar.forest_tail_le`: `G_j(Ln) ≤ C j / B_{⌊Ln⌋}`.
* `B_n G_1(n) → θ p₀` along ALL `n` (sum over one residue class of `d p₀ / (k B_k)` with mesh
  `d`, Karamata, `∑_{k ≥ n} 1/(k B_k) ~ θ/B_n`).
* `n B_n f_1(n) → d p₀` and `G_1(n)/(n f_1(n)) → θ/d` ONLY along admissible sizes
  (`d ∣ n - 1`; `Attraction.sizeProb_lattice_asymp`).  Test case: offspring `(δ₀+δ₂)/2`, `d = 2`,
  only odd sizes: `f_1(n) = 0` for even `n`, so these limits fail along all integers.
  The ratio `θ/d` is the product of the factor `θ` of the tail and `1/d` of the local mass.
* RN weight from tail to exact size at prefix `m`, `j = W_m + 1`:
  `R_n(m,j) = f_j(n-m)/G_j(n-m) · G_1(n)/f_1(n)`.  With `m = ⌊a n⌋`, `j/B_n = x`:
  `f_j(n-m)/G_j(n-m) ≈ d q_{1-a}(x)/(n G_{1-a}(x))` (needs `d ∣ (n-m) - j`, which holds on
  accessible prefixes: `n ≡ 1`, `W_m ≡ -m (mod d)`), times `G_1(n)/f_1(n) ≈ n θ/d`, giving
  `Γ_a(x) = θ q_{1-a}(x)/G_{1-a}(x) = gammaA θ a x`.  The `d` cancels.
* Mass-one weights: `E[Γ_a(X_a)] = 1` and `E[R_n] = 1`; Scheffé (nonnegative weights with the
  same total mass converging in measure converge in L1) avoids any relative LLT at `x = 0, ∞`.

PROOF PLAN.  (1) Upgrade `ST.tendsto_local_walkHitTime_mass` / `Scalar.localLimit` to compact
uniformity by contradiction with subsequences, `Scalar.forestWeight_toReal_eq`, regular
variation of `B` (`Scalar.regularlyVaryingSeq`), continuity of `qKernel`
(`continuousOn_qKernel`).  (2) Tails: truncate at `L n` and `forest_tail_le`, Riemann sum over
the residue class against `continuousOn_sizeTailKernel`.  (3) `treeTail_asymp`, exact mass
(`sizeProb_lattice_asymp`) and ratio.  (4) `exactPrefixWeight_uniform` from (1), (2),
`gammaA` and positivity of `G_{1-a}(x)` on the compact `x`-range.  (5) Scheffé helper.

AMBIGUITIES RESOLVED.  `Admissible μ n` means exact-size mass nonzero (not eventual `d ∣ n - 1`,
which fails to hold for small `n`); sequence statements take explicit `q`, `hqtop`, `hq`.
`forestTail` uses `≥ r` (survival `P(ζ ≥ r)`), `Scalar.forest_tail_le` uses `> m`.
Division is totalized (`x / 0 = 0`); exports only claim limits where the denominator is positive.
No relative endpoint LLT hypothesis appears.  Binder scope: all `∑'`/`∫` bodies parenthesized.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace BGW.StableTrees

open BGW.LocallyFinite (bienaymeLaw sizeEvent)

/-- Admissible size: the exact-size mass `P[ζ = n]` is nonzero (shared with K01/K02). -/
def Admissible (μ : PMF ℕ) (n : ℕ) : Prop := bienaymeLaw μ.toMeasure (sizeEvent n) ≠ 0

/-- `f_j(r)`: probability that a `j`-forest of Bienaymé trees has `r` vertices. -/
noncomputable def forestMass (μ : PMF ℕ) (j r : ℕ) : ℝ := (BGW.forestWeight μ j r).toReal

/-- `G_j(r) = ∑_{k ≥ r} f_j(k)`: probability that a `j`-forest has at least `r` vertices. -/
noncomputable def forestTail (μ : PMF ℕ) (j r : ℕ) : ℝ :=
  ∑' k : ℕ, (Set.Ici r).indicator (fun k => forestMass μ j k) k

/-- Discrete RN weight `R_n(m,j) = f_j(n-m)/G_j(n-m) * G_1(n)/f_1(n)` from the tail-conditioned
law to the exact-size law, at prefix length `m < n` with `j = W_m + 1` (totalized division). -/
noncomputable def exactPrefixWeight (μ : PMF ℕ) (n m j : ℕ) : ℝ :=
  forestMass μ j (n - m) / forestTail μ j (n - m) *
    (forestTail μ 1 n / forestMass μ 1 n)

/-- `f_1(n) = P[ζ = n]`. -/
theorem forestMass_one_eq_sizeProb (μ : PMF ℕ) (n : ℕ) :
    forestMass μ 1 n = (bienaymeLaw μ.toMeasure).real (sizeEvent n) := by
  sorry

/-- `G_1(n) = P[ζ ≥ n]` for a critical non-degenerate law. -/
theorem forestTail_one_eq_sizeGe {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (n : ℕ) :
    forestTail μ 1 n = (bienaymeLaw μ.toMeasure).real (Attraction.sizeGeEvent n) := by
  sorry

/-- **Forest local limit, compact-uniform, periodic.**  With `d = latticeSpan μ`, uniformly for
`r/n ∈ [a,b]`, `j/B_n ∈ [0,M]` and ONLY `d ∣ r - j`:
`n f_j(r) - d q_{r/n}(j/B_n) → 0` (absolute error; includes `j = 0`, where both vanish). -/
theorem forestLocalLimit_uniform {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {a b M : ℝ} (ha : 0 < a) (hab : a ≤ b) (hM : 0 ≤ M) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ r j : ℕ, a * (n : ℝ) ≤ r → (r : ℝ) ≤ b * n → (j : ℝ) / B n ≤ M →
      ((Scalar.latticeSpan μ : ℤ) ∣ (r : ℤ) - j) →
      |(n : ℝ) * forestMass μ j r -
          Scalar.latticeSpan μ * qKernel θ ((r : ℝ) / n) ((j : ℝ) / B n)| ≤ η := by
  sorry

/-- **Forest tail limit, compact-uniform, NO lattice condition.**  Uniformly for `r/n ∈ [a,b]`,
`j/B_n ∈ [ε,M]`: `G_j(r) - G_{r/n}(j/B_n) → 0` (`G = sizeTailKernel θ`). -/
theorem forestTailLimit_uniform {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {a b ε M : ℝ} (ha : 0 < a) (hab : a ≤ b) (hε : 0 < ε) (hεM : ε ≤ M) {η : ℝ}
    (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ r j : ℕ, a * (n : ℝ) ≤ r → (r : ℝ) ≤ b * n →
      ε ≤ (j : ℝ) / B n → (j : ℝ) / B n ≤ M →
      |forestTail μ j r - sizeTailKernel θ ((r : ℝ) / n) ((j : ℝ) / B n)| ≤ η := by
  sorry

/-- **Tree tail asymptotics along ALL `n`:** `B_n G_1(n) → θ p₁(0)`.  No admissibility needed. -/
theorem treeTail_asymp {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B) :
    Tendsto (fun n : ℕ => B n * forestTail μ 1 n) atTop (𝓝 (θ * Scalar.stableDensity θ 0)) := by
  sorry

/-- **Exact mass along an explicit unbounded admissible sequence:**
`q_k B_{q_k} f_1(q_k) → d p₁(0)` (false along all integers when `d > 1`). -/
theorem exactMass_tendsto {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, Admissible μ (q k)) :
    Tendsto (fun k : ℕ => (q k : ℝ) * B (q k) * forestMass μ 1 (q k)) atTop
      (𝓝 (Scalar.latticeSpan μ * Scalar.stableDensity θ 0)) := by
  sorry

/-- **Tail/exact ratio along admissible sizes:** `G_1(q_k) / (q_k f_1(q_k)) → θ / d`. -/
theorem tailExactRatio_tendsto {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, Admissible μ (q k)) :
    Tendsto (fun k : ℕ => forestTail μ 1 (q k) / ((q k : ℝ) * forestMass μ 1 (q k))) atTop
      (𝓝 (θ / (Scalar.latticeSpan μ : ℝ))) := by
  sorry

/-- **Exact-prefix RN weights, uniform on accessible prefixes** (`d ∣ (n-m) - j`, where
`m = ⌊a n⌋`, `j = W_m + 1`, `ε ≤ j/B_n ≤ M`):
`R_n(m,j) - gammaA θ a (j/B_n) → 0` uniformly, along admissible `n`. -/
theorem exactPrefixWeight_uniform {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {a ε M η : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hε : 0 < ε) (hεM : ε ≤ M) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, Admissible μ n → ∀ j : ℕ,
      ε ≤ (j : ℝ) / B n → (j : ℝ) / B n ≤ M →
      ((Scalar.latticeSpan μ : ℤ) ∣ (n : ℤ) - (⌊a * n⌋₊ : ℕ) - j) →
      |exactPrefixWeight μ n ⌊a * n⌋₊ j - gammaA θ a ((j : ℝ) / B n)| ≤ η := by
  sorry

/-- **Scheffé for nonnegative mass-one weights** (generic helper for K07/K15).  If `w_k ≥ 0`,
`w ≥ 0`, all with integral one and `w_k → w` in measure, then `w_k → w` in `L¹`. -/
theorem tendsto_integral_abs_sub_of_massOne {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {w : ℕ → Ω → ℝ} {w₀ : Ω → ℝ}
    (hw : ∀ k, Measurable (w k)) (hw₀ : Measurable w₀)
    (hnn : ∀ k ω, 0 ≤ w k ω) (hnn₀ : ∀ ω, 0 ≤ w₀ ω)
    (h1 : ∀ k, ∫ ω, w k ω ∂P = 1) (h10 : ∫ ω, w₀ ω ∂P = 1)
    (hconv : TendstoInMeasure P w atTop w₀) :
    Tendsto (fun k => ∫ ω, |w k ω - w₀ ω| ∂P) atTop (𝓝 0) := by
  sorry

/-- **Weighted convergence** (consequence): uniformly bounded measurable `F_k → F` in measure
and weights as above give `∫ F_k w_k → ∫ F w₀`. -/
theorem tendsto_integral_mul_of_massOne {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {w : ℕ → Ω → ℝ} {w₀ : Ω → ℝ}
    (hw : ∀ k, Measurable (w k)) (hw₀ : Measurable w₀)
    (hnn : ∀ k ω, 0 ≤ w k ω) (hnn₀ : ∀ ω, 0 ≤ w₀ ω)
    (h1 : ∀ k, ∫ ω, w k ω ∂P = 1) (h10 : ∫ ω, w₀ ω ∂P = 1)
    (hconv : TendstoInMeasure P w atTop w₀)
    {F : ℕ → Ω → ℝ} {F₀ : Ω → ℝ} {C : ℝ} (hF : ∀ k, Measurable (F k)) (hF₀ : Measurable F₀)
    (hC : ∀ k ω, |F k ω| ≤ C) (hC₀ : ∀ ω, |F₀ ω| ≤ C)
    (hFc : TendstoInMeasure P F atTop F₀) :
    Tendsto (fun k => ∫ ω, (F k ω * w k ω) ∂P) atTop (𝓝 (∫ ω, (F₀ ω * w₀ ω) ∂P)) := by
  sorry

end BGW.StableTrees
