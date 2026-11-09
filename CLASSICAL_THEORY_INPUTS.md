# Classical theory inputs for random-tree scaling limits

The items C1–C39 record the classical probability and geometry used in
[*Invariance principles for Galton–Watson trees conditioned on the number of leaves*](https://arxiv.org/abs/1110.2163v4).
See the [coverage index](CLASSICAL_THEORY_COVERAGE.md) for the actual Lean declarations,
their hypotheses, and the remaining article-side obligations.

The statement and source fields give the mathematical context. Proof sketches
describe possible routes and the coverage index identifies the delivered results.
Source tags distinguish statements read in the primary source, standard results,
derivations, and numerical checks.

## Qualifications of the source statements (N1–N15)

These notes explain qualifications and normalizations used in the coverage index.

* **N1 (Theorem 5.1 is not a theorem of Duquesne–Le Gall).** The cited "concluding remark of DLG §2.5" [read,
  arXiv math/0509558] says that "the rescaled height (or contour) process of the μ_p-GW tree conditioned to have at
  least pγ_p vertices" should converge to the height excursion conditioned on length > 1, and "We will leave such
  extensions to the reader". It concerns the height or contour process only, not the joint `(W,H)`. The joint
  statement must be derived from DLG Corollary 2.5.1 (joint convergence of the forest `(V,H,C)`) by excursion
  extraction, as in the proof of DLG Prop. 2.5.2. `Kautre` cites "Section 2.6" for the same remark, which is wrong
  in the arXiv numbering.
* **N2 (Theorem 5.1 display).** Already R7. The minimal correct form uses the horizon `[0,1]` on both sides (C28).
* **N3 (Theorem 4.1 source scope).** Duquesne 2003 Thm 3.1 [read] states the convergence of the **height and
  contour** processes only. The Łukasiewicz path is not part of the statement. Kortchemski's `Kautre` [read]
  likewise proves `(H, C)` only. The paper uses only the contour, so 4.1 is correctly cited. But neither source
  states the triple `(W,C,H)` under `ζ = n`, although `Kautre`'s introduction attributes the W-part to Duquesne.
  This matters for R-G; a wider literature search was not done.
* **N4 (§5.1, θ = 2).** "If θ = 2, H is set to be equal to X." Under `P` this is wrong: `H = X − I`. Duquesne
  2003 and the published `Kautre` [read] write `X − I`, and DLG's general definition gives
  `H_t = β^{-1} m({I^s_t; s ≤ t}) = X_t − I_t` for `ψ(λ) = λ²` [read]. The statement is harmless because `H` is used
  only under `N`, where `I = 0`.
* **N5 (Proof of Proposition 6.9(i)).** "The continuity of V at X^br follows from the fact that the absolute
  minimum of X^br is a.s. attained at a unique time" is incomplete. Continuity of `V` at `f` also needs `f` to be
  continuous at its minimizing time and at time 1. Counterexample to uniqueness alone: a path whose unique infimum is
  the left limit `f(g−)` just before an upward jump at `g`. Then `V(f)(0) = f(g) − inf f > 0`, while approximants
  whose minimum sits just before the jump have `V(f_n)(0) = 0`, and J1 convergence forces convergence at time 0. The
  missing facts are true for `X^br` a.s. (C32). The correct deterministic statement is C34. Duquesne 2003 §4 [read]
  proves continuity only at **continuous** paths with a unique minimum.
* **N6 (Proposition 6.9(ii) and the existence of `X^br`).** 6.9(ii) is the **definition** of the bridge on each
  `[0,a]`, `a < 1` (Bertoin VIII.3 (8), as cited; Duquesne 2003 §4.2, equation "abscont" [read]). That a law on `D([0,1])`
  exists with these prefixes **and** `X^br_{1−} = X^br_1 = 0` is a separate classical fact (C31). The paper uses it
  silently: the Vervaat map needs the whole path.
* **N7 (Bibliography).** Le Gall–Le Jan, Ann. Probab. 26(1) is pages **213–252**, not 213–512 [read in Duquesne's
  bibliography]. The Duquesne–Le Gall reference should give the section in the Astérisque numbering (§2.5).
* **N8 (Do not copy Duquesne 2003's normalizations).** Duquesne 2003 §3.1 [read] writes `E[exp(−λX_t)] =
  exp(−cλ^α)` (sign misprint) and "when α = 2, X is 1/√2 times the standard Brownian motion" (wrong: `√2`). The
  paper's §5.1 (`√2`) is correct [num]. Duquesne's bridge reversal `X̂^br_t = −X^br_{1−t}` needs left limits:
  `X̂^br_t = −X^br_{(1−t)−}`.
* **N9 (Introduction, GHP claim).** The measure is not specified. With the uniform measure on **vertices**, the
  claim follows from the contour convergence alone (C38). With the uniform measure on **leaves**, which is Rizzolo's
  setting for `A = {0}` [read: Rizzolo 2015, Thm 1.1, "uniform probability distribution on its vertices with
  out-degree in A"], one needs Corollary 3.3 (as the text says) **and** a Prokhorov comparison (C39). Write the claim
  with the leaf measure and the rescaling `B_ζ/ζ` (or `μ₀^{1−1/θ}B_n/n`) explicitly.
* **N10 (Lemma 5.7).** Besides the typo already in R7, the proof of 5.9 (eq:cvH) needs **different** factors
  `K_n` for the two coordinates `(W, H)`: `B_{r_n}/B_ζ` for W and `(B_ζ/ζ)/(B_{r_n}/r_n)` for H. State 5.7 with a
  vector `K_n ∈ (0,∞)^d` acting coordinatewise (C6(iv)). The horizon `D([0,∞))` can be replaced by `D([0,T])`, `T > a`.
* **N11 (Cut-offs `1{1/α < X_a < α}` and `1{|X_a| < α}` in 5.8 and 6.1).** These indicators are not continuous.
  Passing to the limit needs `α` outside the countable set of atoms of the law of `X_a` (which exists for every α
  but one must choose it), or continuous cut-offs. Clarity item.
* **N12 ("Billingsley (13.8)" in the proof of 6.1).** The proved estimate (eq:montrertension) is a terminal-oscillation
  bound. By itself it is not a tightness criterion. It suffices together with convergence on every `[0,a]`, `a < 1`,
  and continuity of the limit at 1 (C11b). Clarity item; the formula number is not verified here.
* **N13 (Bertoin's book treats spectrally negative processes in Ch. VII).** Every statement must be transported by
  `X ↦ −X`: Bertoin's supremum `S` becomes `−I`, first passage above `x` becomes first passage below `−x`. Clarity
  item for the formalizer.
* **N14 (`Δ̄(W(τ)) = Δ(τ) − 1`).** False for the one-vertex tree (already R13d). For 7.1(i) it is harmless because
  `P[λ = n, ζ = 1] = 0` for `n ≥ 2`.
* **N15 (Proposition 5.3 test functions).** The paper says `F : D([0,a],ℝ²) → ℝ₊`. Since `H` is continuous, the
  natural space is `D([0,a],ℝ) × C([0,a],ℝ)`. The two formulations agree (C5, JS VI.2.2). `Kautre` states the same
  identity [read].

---

## 1. Conventions, exact normalizations, consistency checks

### 1.1 The stable process

* θ ∈ (1,2] is fixed and ψ(λ) := λ^θ. `X` is the spectrally positive Lévy process with
  `E[exp(−λX_t)] = exp(tλ^θ)` for λ ≥ 0, t ≥ 0 (paper eq:X, line 1301).
* Characteristic function: `E[exp(iuX_t)] = exp(t(−iu)^θ)`, principal branch. This is BGW's `Scalar.stableCF θ u`
  at `t = 1`. `|E e^{iuX_1}| = exp(−|u|^θ |cos(πθ/2)|)`, which is integrable, so all densities are smooth.
* Lévy measure, for θ < 2: `Π(dr) = r^{−1−θ}/Γ(−θ) dr = θ(θ−1)/Γ(2−θ) · r^{−1−θ} dr` on (0,∞). There is no
  Gaussian part and no drift (`ψ(λ) = ∫(e^{−λr} − 1 + λr)Π(dr)`). Duquesne 2003 §3.1 gives the same Lévy measure
  [read].
* θ = 2: `X = √2·B` with `B` a standard Brownian motion, and `X_1 ~ N(0,2)`, `p_1(x) = e^{−x²/4}/√(4π)`
  (paper line 609; correct, see N8).
* `E[X_1] = 0`. Scaling: `(c^{−1/θ}X_{ct})_{t≥0} = (X_t)` in law for every c > 0.

### 1.2 Densities and kernels (all formulas checked)

* `p_1 = Scalar.stableDensity θ` (BGW: Fourier inversion of `stableCF`). `p_t(x) := t^{−1/θ} p_1(t^{−1/θ}x)` is
  project `pDens θ t x`. It is the density of `X_t` (scaling).
* `p_1(0) = Γ(1+1/θ) sin(π/θ)/π = 1/(θΓ(1−1/θ)) = 1/|Γ(−1/θ)|`. The first form is BGW `stableDensity_zero`;
  the equalities follow from the reflection formula. [num: θ = 1.2, 1.5, 1.8, 2: 0.149710, 0.248855, 0.278768, 0.282095]
* `P(X_1 < 0) = 1/θ`, equivalently positivity parameter `1 − 1/θ`. [num: matches to 6 digits for θ = 1.2, 1.5, 1.8, 2]
* `q_s(x) := (x/s) p_s(−x)` for s > 0, x ≥ 0 (project `qKernel`).
  * `∫_r^∞ q_s(x) ds = θ ∫_0^{x r^{−1/θ}} p_1(−u) du` for r > 0, x ≥ 0 (substitute `u = x s^{−1/θ}`; paper proof of 5.5).
  * Hence `∫_0^∞ q_s(x) ds = θ P(X_1 < 0) = 1` for x > 0. This is consistent with Kendall's identity C18(F4) and
    with `T_x < ∞` a.s.
  * `∫_r^∞ q_s(x) ds` is project `sizeTailKernel θ r x`.
* `Γ_a(x) := θ q_{1−a}(x) / ∫_{1−a}^∞ q_s(x) ds` for a ∈ (0,1), x > 0. The denominator is
  `θ∫_0^{x(1−a)^{−1/θ}} p_1(−u)du > 0`, because p_1 is continuous and `p_1(0) > 0`; global positivity of p_1 is not
  needed. So `Γ_a` is continuous and positive on (0,∞) and bounded on compact subsets of (0,∞); also
  `Γ_a(0+) = 1/(1−a)`. Project-level expression:
  `Γ_a(x) = θ · qKernel θ (1−a) x / sizeTailKernel θ (1−a) x`.

### 1.3 Normings `B_n`

* Classical theorems are stated for **any** positive sequence `(B_n)` with `W_n/B_n ⇒ X_1`. This is BGW
  `StableDomain μ θ B` (monotone, positive) or project `IsStableAttracted (stepLaw μ) θ 0 B`; the two are related by
  `IsStableAttracted.exists_stableDomain`.
* By convergence of types, two such sequences have ratio → 1, so monotonicity is never essential. Duquesne assumes
  an increasing sequence [read].
* The project's corrected norming `norming (stepLaw μ) θ` qualifies (`locallimit_i`). The **printed** Theorem 1.10
  norming does not (R2: negative base; R4: factor √2).
* Every statement below that mentions `B_n` is true for every admissible `B_n` and false for the printed one.
* Regular variation: `B_{⌊nt⌋}/B_n → t^{1/θ}` (BGW `regularlyVaryingSeq`, `tendsto_div_of_tendsto_div`).

### 1.4 Excursion normalization

* Local time of `X − I` at 0 is `−I`. The inverse local time is `T_x = inf{t : X_t < −x}`, with
  `E[e^{−λT_x}] = e^{−xλ^{1/θ}}`. Hence `N(1 − e^{−λζ}) = λ^{1/θ}`, and:
  * `N(ζ > t) = t^{−1/θ}/Γ(1−1/θ)` (`Kautre` and Duquesne 2003 [read]);
  * `N(ζ ∈ dt) = p_1(0) t^{−1−1/θ} dt = dt/(θΓ(1−1/θ)t^{1+1/θ})`, consistent with `Kautre`'s Itô description [read]
    and with §1.2.
* `N(ζ > 1) = θ·n(1)`, where `n(s)` is the density of ζ under N. This identity is exactly why the constant θ appears
  in `Γ_a` (C24). Only ratios of N-masses enter the paper, so any other normalization of the local time leaves every
  statement of the paper unchanged.
* `N(·|ζ > 1) := N(· ∩ {ζ > 1})/N(ζ > 1)`. Under it, ζ has density `(1/θ) s^{−1−1/θ}` on (1,∞).

### 1.5 Height process scaling

* Jointly, `((k^{−1/θ}X_{kt}, k^{1/θ−1}H_{kt}))_{t≥0} = (X, H)` in law. Duquesne 2003 [read] gives index
  `θ/(θ−1)` for `H` alone.
* Excursion rescaling of pairs: `S^{(λ)}(x, h) := (λ^{1/θ}x(·/λ), λ^{1−1/θ}h(·/λ))`. For θ = 2 the two exponents
  agree, and `H = X` under `N`.

### 1.6 Path conventions for trees and walks (paper-level, recalled for the statements)

* The Łukasiewicz path is extended by 0 after ζ (paper line 1357, which overwrites `W_ζ = −1`).
* The height function is interpolated linearly, `H_t(τ)`, and is 0 after ζ.
* The contour is defined on `[0, 2ζ]`, padded by 0 on `[2(ζ−1), 2ζ]`.
* BGW `PlaneTree.contourFunction s = C_{2(ζ−1)s}`, without padding (see C38).
* The rescaled step path `t ↦ W_{⌊kt⌋}/B` on `[0,1]` has value `W_k/B` at `t = 1`. Under `W_{T_n} = −1` this value is
  `−1/B_{T_n}`: there is a jump at 1, which vanishes in the limit.

---

## 2. Part P: the Skorokhod space

### C1. The Skorokhod space `D([0,T], E)` and the J1 metric

**(a) Statement.** Fix T > 0 and a metric space (E, ρ); the paper needs E = ℝ, and C5 handles ℝ^d.

* `D_T(E)` is the set of f : [0,T] → E that are right-continuous at every t ∈ [0,T) and have a left limit `f(t−)`
  at every t ∈ (0,T]. Convention: `f(0−) := f(0)`.
* `Λ_T` is the set of increasing homeomorphisms of [0,T] (equivalently order isomorphisms; they fix 0 and T).
* `d_T(f,g) := inf_{λ∈Λ_T} max( sup_t |λ(t) − t|, sup_t ρ(f(t), g(λ(t))) )` (Billingsley's `d`).

Facts.
1. Every f ∈ D_T(E) has relatively compact range for E = ℝ^d. In particular f is bounded and has at most countably
   many jumps, and for each ε > 0 only finitely many jumps of size > ε.
2. `d_T` is a metric. The delicate point is separation, `d(f,g) = 0 ⇒ f = g`, which uses right-continuity.
3. `d_T(f,g) ≤ sup_t ρ(f(t),g(t))`.
4. Characterization: `d_T(f_n,f) → 0` iff there are `λ_n ∈ Λ_T` with `‖λ_n − id‖_∞ → 0` and
   `sup_t ρ(f_n(λ_n t), f(t)) → 0`.

The J1 topology is the metric topology of `d_T`.

**(b) Source.** Billingsley 1999 §12 (on [0,1]; [0,T] by linear rescaling) [std]; Jacod–Shiryaev 2003 VI.1 [std].

**(c) Use.** Every statement with a walk coordinate: 5.1, 5.3 (test functions on `D([0,a])`), 5.7, 5.8, 5.9(i),
6.1, 6.2(ii), 6.6–6.7, 6.9, 7.1(i), Intro (II), 8.1(II). Not needed by 4.1, 4.5, 4.6 or 5.9(ii), where `C` suffices.

**(d) Minimal.** E = ℝ only, with the products `D × C` (C5) for the joint statements. Horizons: `T = 1` and the
prefixes `T = a ∈ (0,1)`. The metric `d` only; `d°` (C3) is not needed.

**(e) Dependencies.** Mathlib `IsCadlag`, `Function.leftLim`, `isBounded_image_of_isCadlag_of_isCompact`.

**(f) Lean sketch.**
```lean
namespace BGW.Skorokhod
/-- Billingsley's D[0,T]. On `Set.Icc 0 T`, `IsCadlag` is exactly Billingsley's condition
(at `T` right-continuity is vacuous, at `0` the left-limit condition is vacuous). -/
structure D (T : ℝ) (E : Type*) [TopologicalSpace E] where
  toFun : Set.Icc (0:ℝ) T → E
  isCadlag : IsCadlag toFun
abbrev TimeChange (T : ℝ) := Set.Icc (0:ℝ) T ≃o Set.Icc (0:ℝ) T
noncomputable def j1EDist [PseudoEMetricSpace E] (f g : D T E) : ℝ≥0∞ :=
  ⨅ λ : TimeChange T, max (⨆ t, edist ((λ t : ℝ)) (t : ℝ)) (⨆ t, edist (f.toFun t) (g.toFun (λ t)))
instance [MetricSpace E] : MetricSpace (D T E)            -- finiteness + separation
instance : MeasurableSpace (D T E) := borel _
instance : BorelSpace (D T E)
theorem tendsto_iff_exists_timeChange : Tendsto f l (𝓝 g) ↔ ∃ λ : ι → TimeChange T, ... -- fact 4
```

**(g) Size and pitfalls.** 500–900 lines.
* Do **not** give `D` a normed-group structure: addition is not J1-continuous.
* `D([0,T],ℝ²)` and `D([0,T],ℝ)²` carry different topologies.
* `d` is not complete (C3), so no `CompleteSpace` instance may rest on `d`.
* Mathlib needs an `OrderTopology` instance on `Set.Icc 0 T`; the subtype order topology is the subspace topology.

### C2. Separability

**(a)** `(D_T(ℝ), d_T)` is separable: step functions with rational jump times and rational values are dense.
Consequences:
* `SecondCountableTopology (D T ℝ)`;
* `ProbabilityMeasure (D T ℝ)` is metrizable (Mathlib `instMetrizableSpaceProbabilityMeasure`), so sequential
  arguments are legitimate;
* `Borel(D × S) = Borel(D) ⊗ Borel(S)` for second-countable S.

**(b)** Billingsley 1999, Theorem 12.2 (separability part) [std; check the number].

**(c)** C10 (products; BGW's perturbation lemma assumes `SecondCountableTopology`), the measurability of maps
defined on `D × ℝ × ℝ` (5.7), and metrizability for subsequence arguments (C8, C17).

**(d)** Needed. **(e)** C1. **(f)** `instance : SeparableSpace (D T ℝ)`.

**(g)** 300–600 lines. Pitfall: the uniform metric on `D` is **not** separable; prove separability for J1.

### C3. Billingsley's complete metric `d°` and Polishness (optional)

**(a)**
* `‖λ‖° := sup_{s<t} |log((λ(t) − λ(s))/(t − s))|`.
* `d°(f,g) := inf_λ max(‖λ‖°, sup_t |f(t) − g(λ(t))|)`.
* `d` and `d°` are equivalent metrics (same topology), and `D` is complete for `d°`. Hence `D` is Polish.

**(b)** Billingsley 1999, Theorems 12.1–12.2 [std].

**(c)** Not used by the paper.

**(d)** Not needed. Needed only for `StandardBorelSpace` (regular conditional distributions, which the paper never
uses because `N(·|ζ=1)` is defined by scaling), for the converse of Prokhorov, and for Mathlib's
`tendsto_of_tight_of_separatesPoints`.

**(e)** C1.

**(g)** 1200–2200 lines. Pitfall: if added, give `PolishSpace` through `d°` while the `MetricSpace` instance uses `d`
(topology-preserving equivalence).

### C4. Borel structure of `D`

**(a)**
1. For each t ∈ [0,T], `π_t : f ↦ f(t)` is Borel.
2. For every S ⊆ [0,T] dense with T ∈ S, `Borel(D_T) = σ(π_t : t ∈ S)`.
3. `(f, t) ↦ f(t)` is jointly measurable on `D_T × [0,T]`, because `f(t) = lim_k f(⌈2^k t⌉ 2^{−k} ∧ T)` by
   right-continuity.
4. `f ↦ f(t−)`, `f ↦ sup_{s∈J} f(s)` and `f ↦ inf_{s∈J} f(s)` (J an interval) are Borel.

**(b)** Billingsley 1999, Theorem 12.5 [std]. Kortchemski `Kautre` invokes 12.5(iii) for item 2 [read].

**(c)**
* Uniqueness of laws from finite-dimensional distributions: C12(a), C16, C17, and `Kautre`'s proof of 5.3 [read].
* Measurability of the restriction `r_a`, of `V` (C33), of the normalization maps of C22, and of `H` as a functional
  (C26).

**(d)** Library: needed. Consumer layer: **avoidable**. The pre-limit laws in the paper are laws of step paths of
finite trees, which are countably supported, so every map is a.e.-measurable for them. For the limit laws, use a.e.
continuity: the set of continuity points of any map between metric spaces is G_δ (Mathlib
`IsGδ.setOfPred_continuousAt`), so a map continuous at a.e. point is `AEMeasurable` (see C9).

**(e)** C1 (C2 simplifies the proof).

**(f)**
```lean
theorem measurable_eval (t) : Measurable (fun f : D T ℝ => f.toFun t)
theorem borel_eq_iSup_comap_eval {S : Set (Icc 0 T)} (hS : Dense S) (hT : ⊤ ∈ S) :
  (borel (D T ℝ)) = ⨆ t ∈ S, (borel ℝ).comap (fun f => f.toFun t)
```

**(g)** 600–1100 lines. Pitfall: the Borel σ-field of the **uniform** topology on `D` is strictly larger; never mix
the two.

### C5. Continuous paths inside `D`; products

**(a)**
1. For f, g ∈ C([0,T]): `d_T(f,g) ≤ ‖f − g‖_∞`.
2. If f_n ∈ D_T, f ∈ C([0,T]) and `d_T(f_n,f) → 0`, then `‖f_n − f‖_∞ → 0`.
3. The inclusion `ι : C([0,T]) → D_T` is a homeomorphism onto a closed subset; on C, J1 is the uniform topology.
4. (Optional, JS VI.2.2.) If f_n → f in D_T(ℝ) and g_n → g uniformly with g ∈ C, then (f_n, g_n) → (f, g) in
   D_T(ℝ²) with a common time change. Hence convergence in law in `D_T(ℝ) × C_T^k` with continuous coordinates
   implies convergence in `D_T(ℝ^{1+k})`; the converse holds always (coordinates).

**(b)** Billingsley 1999 §12 [std]; Jacod–Shiryaev VI.1.17(b), VI.2.2 [std; check the numbers].

**(c)**
* 5.9 (eq:cvH): a J1 limit that is continuous gives uniform convergence, hence max increments → 0.
* C38 (time conventions of the contour) and C30.
* Intro (II) if stated in `D([0,1],ℝ³)`.

**(d)** Items 1–3. Item 4 gives the `ℝ³` formulation.

**(e)** C1.

**(f)** `def ofContinuous : C(Icc 0 T, ℝ) → D T ℝ`; `lipschitzWith_one_ofContinuous`;
`tendsto_uniformly_of_tendsto_of_continuous`.

**(g)** 250–400 lines.

### C6. Continuity facts for maps on `D`

**(a)** Let 0 < a < T and f ∈ D_T(ℝ).

1. *(Evaluation.)* `π_0` and `π_T` are 1-Lipschitz for `d_T`. For t ∈ (0,T), `π_t` is continuous at f if f is
   continuous at t; only this direction is used.
2. *(Restriction, extension, stopping.)*
   * The restriction `r_a : D_T → D_a`, `r_a f = f|[0,a]`, is continuous at every f that is continuous at a.
   * The extension `ι_a : D_a → D_T`, `ι_a(g)(t) := g(t ∧ a)`, is 1-Lipschitz.
   * The stopping map `φ_a := ι_a ∘ r_a`, `φ_a(f)(t) = f(t ∧ a)`, is continuous at f continuous at a.
3. *(Extrema.)*
   * `inf_{[0,T]}` and `sup_{[0,T]}` are 1-Lipschitz on `(D_T, d_T)`, since time changes do not change the range.
   * For c ∈ (0,T), `f ↦ sup_{s∈[c,T]} |f(s) − f(c)|` is continuous at every f continuous at c.
4. *(Time–space scaling; the core of 5.7.)* Let `d ≥ 1` and work in `D_T(ℝ^d)`, or in `D_T(ℝ) × C_T^{d−1}`. The map
   `Ψ : (g, k, s) ↦ (t ↦ k ⊙ g(min(st, T)))_{t ∈ [0,a]}`, from `D_T(ℝ^d) × (0,∞)^d × (0,∞)` to `D_a(ℝ^d)`, is
   continuous at every `(f, 1, 1)` with f continuous at a. Here `⊙` is coordinatewise multiplication. In the product
   form `D × C`, the C-coordinate map `(h, k, s) ↦ k·h(min(s·, T))|[0,a]` is continuous everywhere.

[D] Proof sketch of item 4. Take `λ_n` with `‖λ_n − id‖ → 0` and `g_n∘λ_n → f` uniformly. On `[0, a − ε_n]` use
`μ_n(t) := s_n^{−1}λ_n(t)`. On `[a − ε_n, a]` interpolate linearly so that `μ_n(a) = a`, with `ε_n ↓ 0` slowly.
Continuity of f at a controls the window, because `g_n` near time a is uniformly close to `f(a)`. Since `s_n a < T`
for large n, the `min` is inactive. Finally multiply by `k_n → 1` (paths are bounded).

**(b)**
* Billingsley 1999 Theorem 12.5(i) (evaluation) and §16, Theorem 16.2 and its lemmas (restrictions) [std].
* Jacod–Shiryaev VI.1.14, VI.2.1 [std; check].
* Whitt 2002, *Stochastic-Process Limits*, Theorem 13.2.2 (composition with continuous strictly increasing time
  changes) [std; check].
* Item 4 is a direct consequence of item 2 and composition [D].

**(c)**
* Item 1: the endpoint `X_a`, as in `Γ_a(X_a)` and `p_{1−a}(−X_a)` (5.3, 5.8, 6.9(ii)).
* Item 2: every restriction to `[0,a]` (5.8, 5.9, 6.1, C11, C12).
* Item 3: terminal control in Intro (II) and in R-B.
* Item 4: Lemma 5.7, hence 5.8, 5.9(i), eq:cvH, 6.1 and 6.2(ii).

**(d)** Items 1–4 as stated. Item 4 is needed with d = 2 (W, H) and with distinct factors per coordinate (N10).

**(e)** C1, C5.

**(f)**
```lean
def restrict (a) (haT : a ≤ T) : D T E → D a E
theorem continuousAt_restrict (h : ContinuousAt f.toFun ⟨a, _⟩) : ContinuousAt (restrict a _) f
def extendConst (a) (haT : a ≤ T) : D a E → D T E;  theorem lipschitzWith_one_extendConst
def timeSpaceScale (a T) : D T ℝ × ℝ × ℝ → D a ℝ      -- (g,k,s) ↦ k • g(min(s t, T))
theorem continuousAt_timeSpaceScale (ha : 0 < a) (haT : a < T) (hf : ContinuousAt f.toFun ⟨a,_⟩) :
    ContinuousAt (timeSpaceScale a T) (f, 1, 1)
```

**(g)** 800–1500 lines. Pitfall: none of these maps is continuous everywhere; push laws forward with C9.

### C7. Stopped-path approximation

**(a)** For f ∈ D_T and δ ∈ (0,T): `d_T(φ_{T−δ}(f), f) ≤ sup_{s∈[T−δ,T]} |f(s) − f(T−δ)|`. If f is continuous at T,
the right side → 0 as δ ↓ 0. The same holds in `C_T` with the uniform norm.

**(b)** [D], elementary (take λ = id).

**(c)** C11b and C12(b), hence 5.9(ii) (eq:cvC), 6.1 and Intro (II).

**(d)** As stated. **(e)** C1, C6(2).

**(g)** About 100 lines.

### C8. Relative compactness and tightness in `D` (library)

**(a)**
* Modulus: `w'_f(δ) := inf max_i sup_{s,t∈[t_{i−1},t_i)} |f(s) − f(t)|`, the infimum over partitions
  `0 = t_0 < ⋯ < t_r = T` with `min_i (t_i − t_{i−1}) > δ`.
* *(Arzelà–Ascoli analogue.)* `A ⊆ D_T` is relatively compact iff `sup_{f∈A} ‖f‖ < ∞` and
  `lim_{δ→0} sup_{f∈A} w'_f(δ) = 0`.
* *(Tightness.)* `(P_n)` is tight iff (i) `lim_{c→∞} limsup_n P_n(‖f‖ ≥ c) = 0` and
  (ii) for all ε > 0, `lim_{δ→0} limsup_n P_n(w'_f(δ) ≥ ε) = 0`.
* *(Aldous's criterion, sufficient.)* For processes `Y^n` adapted to filtrations, (i) together with
  `Y^n(τ_n + h_n) − Y^n(τ_n) → 0` in probability, for all bounded stopping times `τ_n` and all `h_n ↓ 0`, implies
  tightness.

**(b)** Billingsley 1999, Theorems 12.3 and 13.2, and §16 (Aldous's criterion, Theorem 16.10) [std; check];
Jacod–Shiryaev VI.4.5 [std]; Kallenberg FMP 2nd ed. Theorem 16.11 [std; check].

**(c)** Not used by the paper's own proofs (R-C). The paper cites "Billingsley (13.8)" in 6.1 and the remark is
unnecessary there. Needed by C17 (FCLT), C16 (existence through R-F), C27, and optionally C31 (the bridge as a limit).

**(d)** Only the sufficiency directions. The necessity direction needs C3.

**(e)** C1, C4. Mathlib `isCompact_closure_of_isTightMeasureSet` (T2 + Borel; no completeness).

**(g)** 1500–2500 lines; the survey estimates 800–1500 for compactness alone. Pitfall: Mathlib's Arzelà–Ascoli
does not apply to `D`.

---

## 3. Part W: weak-convergence add-ons

### C9. Extended continuous mapping theorem

**(a)** Let S, S' be pseudo-metric spaces with Borel σ-fields. Let `P_n → P` in `ProbabilityMeasure S`. Let
`h : S → S'` be `AEMeasurable` for every `P_n` and for `P`, with `∀ᵐ x ∂P, ContinuousAt h x`. Then
`P_n.map h → P.map h`.

Two companions:
1. If `∀ᵐ x ∂P, ContinuousAt h x`, then h is `AEMeasurable` for P, because the continuity set is G_δ.
2. Every probability law on ℝ has at most countably many atoms. So for any family of cut-offs `{1/α < y < α}` or
   `{|y| < α}`, all but countably many α give boundaries of P-measure 0 (N11).

**(b)** Billingsley 1999, Theorem 2.7 [std; well known].

[D] Proof via the closed-set portmanteau (Mathlib `limsup_measure_closed_le_of_tendsto` and
`tendsto_of_forall_isClosed_limsup_le`), using the inclusion `cl(h⁻¹F) ⊆ h⁻¹F ∪ {x : ¬ContinuousAt h x}`.

**(c)**
* 5.7 (map `Ψ`), 5.8 (`F·Γ_a(X_a)·cut-off`), 5.9 (restrictions).
* 6.1 (restrictions; the Vervaat map at `X^br`).
* Intro (II) (terminal oscillation functional).
* 7.1(i) (the map is continuous there, so the Mathlib CMT suffices).

**(d)** As stated.

**(e)** Mathlib portmanteau.

**(f)**
```lean
theorem ProbabilityMeasure.tendsto_map_of_ae_continuousAt {P : ℕ → ProbabilityMeasure S} {Q} (hPQ : Tendsto P atTop (𝓝 Q))
  {h : S → S'} (hmeas : ∀ n, AEMeasurable h (P n)) (hQ : AEMeasurable h Q)
  (hcont : ∀ᵐ x ∂(Q : Measure S), ContinuousAt h x) :
  Tendsto (fun n => (P n).map hmeas) atTop (𝓝 (Q.map hQ))
```

**(g)** 100–250 lines.

### C10. Converging together; Slutsky in metric spaces on varying probability spaces

**(a)**
1. (Billingsley Thm 3.1.) Let `F_n, G_n : Ω_n → E` be measurable. If `law(G_n) → ν` and
   `P_n(d(F_n, G_n) > ε) → 0` for every ε > 0, then `law(F_n) → ν`. This **exists** in BGW:
   `BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability` (E pseudo-metric, Borel, second countable,
   varying `Ω n`).
2. (Billingsley Thm 3.9.) Let S, S' be separable metric spaces. Let `X_n : Ω_n → S` and `Y_n : Ω_n → S'` be
   measurable, with `law(X_n) → P` and `P_n(d(Y_n, c) > ε) → 0`. Then `law(X_n, Y_n) → P ⊗ δ_c`.
   Proof: item 1 plus the CMT for `x ↦ (x, c)`.

**(b)** Billingsley 1999, Theorems 3.1 and 3.9 [std; check 3.9].

**(c)**
* 5.7 (`(Z^n, K_n, S_n)`).
* 5.9 (`C ≈ H`: eq:HC and eq:g).
* 5.10 (`B_ζ/B_n → μ₀^{−1/θ}` in probability).
* Intro (II), C39 (perturbation of the measure).

**(d)** As stated.

**(e)** C2, BGW.

**(g)** 100–200 lines. Pitfall: Mathlib's `TendstoInDistribution.prodMk_of_tendstoInMeasure_const` requires the first
codomain to be a `SeminormedAddCommGroup` and uses a **single** probability space [read in Mathlib]. It is not
applicable to `D`-valued paths of trees; use item 2.

### C11. Approximation theorem, and full convergence from prefixes plus terminal control

**(a)**
1. (Billingsley Thm 3.2.) Let `Y_n, X_{u,n} : Ω_n → S` (S metric, separable). Suppose `X_{u,n} ⇒ Z_u` as n → ∞
   for each u, `Z_u ⇒ X` as u → ∞, and `lim_u limsup_n P(d(X_{u,n}, Y_n) ≥ ε) = 0` for all ε > 0. Then `Y_n ⇒ X`.
2. **(C11b, the form the paper needs.)** Let `Y^n` be random elements of `D_T` (or of `D_T × C_T^k`, or of `C_T`)
   and let `Y` be a random element of the same space. Let `A ⊆ (0,T)` with `sup A = T`. Assume:
   * for every a ∈ A, `r_a(Y^n) ⇒ r_a(Y)`;
   * `Y` is a.s. continuous at T;
   * for every η > 0, `lim_{δ↓0, T−δ∈A} limsup_n P(sup_{s∈[T−δ,T]} |Y^n_s − Y^n_{T−δ}| > η) = 0`.

   Then `Y^n ⇒ Y`.

[D] Proof of item 2: apply item 1 with `X_{δ,n} := ι(r_{T−δ}Y^n)` and `Z_δ := ι(r_{T−δ}Y) → Y` a.s. (C7); the
distance is bounded as in C7.

**(b)** Billingsley 1999, Theorem 3.2 [std]; item 2 is [D].

**(c)**
* 5.9(ii) (eq:cvC): in `C_1`. The terminal control comes from the reversal invariance of the contour and from
  `H^exc_0 = 0`.
* 6.1: in `D_1`, with the paper's eq:montrertension and `|Y^n_1| = 1/B_{T_n} → 0`.
* Intro (II): in `D × C × C`. The W-part of the terminal control follows from 6.1 by C6(3) and C9.
* This replaces "Billingsley (13.8)" (N12, R-C).

**(d)** Item 2. **(e)** C7, C9, C2.

**(f)**
```lean
theorem tendsto_of_restrict_of_terminal {Ω : ℕ → Type*} ... (Yn : (n:ℕ) → Ω n → D T ℝ) (ν : ProbabilityMeasure (D T ℝ))
  (A : Set ℝ) (hA : ...) (hpre : ∀ a ∈ A, Tendsto (fun n => (μ n).map (restrict a _ ∘ Yn n)) atTop (𝓝 (ν.map (restrict a _))))
  (hcont : ∀ᵐ f ∂ν, ContinuousAt f.toFun ⊤) (hterm : ∀ η > 0, ...) :
  Tendsto (fun n => (μ n).map (Yn n)) atTop (𝓝 ν)
```

**(g)** 150–300 lines.

### C12. Determining classes

**(a)**
1. Two laws on `D_T` with equal finite-dimensional distributions on finite subsets of S (S dense, T ∈ S) are equal.
   This needs C4.
2. Let P, Q be laws on `D_T`, both a.s. continuous at T. Suppose `P∘r_a⁻¹ = Q∘r_a⁻¹` for a ∈ A with `sup A = T`
   (restrictions taken where P and Q are a.s. continuous at a). Then P = Q. [D] Proof: C7 and uniqueness of weak
   limits; **no C4 needed**.
3. For every law P on `D_T`, the set `{t : P(f(t−) ≠ f(t)) > 0}` is countable.

**(b)** Billingsley 1999 §12–13 (item 3: "T_P", p. 138 [std; check]); items 1–2 [std]/[D].

**(c)**
* Item 1: C16, C17, `Kautre`'s proof of 5.3.
* Items 2–3: R-B, and the uniqueness of `X^br` (C31).

**(d)** Items 2–3 for the consumer layer; item 1 for the library.

**(g)** 200–400 lines.

### C13. Prokhorov (status only)

Mathlib provides `isCompact_closure_of_isTightMeasureSet` (T2 + Borel, no completeness),
`isTightMeasureSet_of_isCompact_closure` (Polish), `IsTightMeasureSet.prodMk`, and metrizability of
`ProbabilityMeasure` for separable spaces. This is enough for C8/C17 (tight ⇒ subsequential limits) and for Duquesne–Le
Gall's tightness of triples. Nothing new is needed.

### C14. Skorokhod representation (not needed)

Billingsley 1999, Theorem 6.7: on a separable metric space, `P_n ⇒ P` admits a.s.-convergent versions on a common
probability space. The paper uses it in the proof of 5.7. Duquesne–Le Gall use it in Corollary 2.5.1 and in the
proof of Proposition 2.5.2 [read]. **Avoid it** (R-D): C9 and C10 replace every use, and a general `D`-valued
version is over 1000 lines (survey §1). The real-valued quantile version in
`Finished/arXiv-2607.22291v1 /PoissonDeclumping/Probability/Skorokhod.lean` does not help for `D`.

---

## 4. Part S: stable law, stable process, FCLT, fluctuation basics

### C15. The stable law and its density

**(a)** For θ ∈ (1,2] (all items TRUE; where each stands):

1. `μ_θ := p_1(x) dx` is a probability measure with `∫ e^{−λx} μ_θ(dx) = e^{λ^θ}` (λ ≥ 0) and characteristic
   function `exp((−iu)^θ)`. BGW has `limitLaw_eq_withDensity`, `charFun_withDensity_stableDensity`,
   `stableDensity_nonneg`, `integral_stableDensity` **under a `StableDomain` witness**. Witnesses exist for every θ
   (finite variance for θ = 2: `stableDomain_norming_finiteVariance`; tails for θ < 2:
   `exists_stableDomain_of_tail`), so an unconditional version is a short bridge. **To add.**
2. `p_1` is continuous, bounded and Lipschitz; `p_1(0) = Γ(1+1/θ)sin(π/θ)/π > 0`. BGW has
   `continuous_stableDensity`, `lipschitzWith_stableDensity`, `stableDensity_zero` and `stableDensity_zero_pos`.
3. `sup_x |x p_1(x)| < ∞` and `sup_x |x p_1'(x)| < ∞` (Fourier: `x p_1(x)` is a transform of `φ'`, which is
   integrable). The first is used in 5.12 and the second for the bounded derivative of `q_u` before 5.4. The project
   already proved what tranche 1 needed (`qKernel_one_lipschitzOn`, `sizeTailKernel_lipschitz`).
4. *(Semigroup.)* `p_s * p_t = p_{s+t}` for s, t > 0 (characteristic functions multiply), with
   `p_t := pDens θ t`. **To add.** Needed for the consistency of the bridge densities (C31) and for the f.d.d. of C16.
5. `∫ p_1(−u) 1_{u>0} du = P(X_1 < 0) = 1/θ` [num]. Optional: it is the analytic form of `T_x < ∞` (C18 F4).
6. *(Optional.)* `p_1 > 0` on ℝ [Zolotarev; std]. **Not needed**: see §1.2 for `Γ_a`.
7. `Γ_a` is continuous and positive on (0,∞) (§1.2). The project has the ingredients `qKernel`, `sizeTailKernel` and
   `sizeTailKernel_scaling`. **To add:** the definition `gammaA` and its continuity.

**(b)** Zolotarev 1986 §I.4 and §2.? (positivity, ρ = 1 − 1/θ) [std]; Sato 1999 §14 [std]; BGW
`StableTrees/Scalar/{Density,DensityLaw}.lean` [read].

**(c)**
* Item 1: the limit law in C17.
* Item 4: C16 and C31.
* Item 7: 5.3 and 5.8.
* Item 2: everywhere.

**(d)** Items 1, 2, 4, 7 (item 3 is already in tranche 1).

**(e)** BGW.

**(f)**
```lean
noncomputable def stableLaw (θ : ℝ) : ProbabilityMeasure ℝ   -- withDensity (stableDensity θ)
theorem stableLaw_laplace (hθ) (lam ≥ 0) : ∫ x, exp (-lam*x) ∂stableLaw θ = exp (lam^θ)
theorem pDens_conv (hθ) (hs : 0 < s) (ht : 0 < t) (x) : ∫ y, pDens θ s y * pDens θ t (x - y) = pDens θ (s+t) x
noncomputable def gammaA (θ a x : ℝ) : ℝ := θ * qKernel θ (1-a) x / sizeTailKernel θ (1-a) x
theorem continuousOn_gammaA, gammaA_pos
```

**(g)** 300–800 lines. Pitfall: BGW's density lemmas carry the `StableDomain` hypothesis; state the unconditional
versions once.

### C16. The θ-stable spectrally positive Lévy process as a law on `D([0,T])`

**(a)** For every T > 0 there is a unique Borel probability measure `P^X_T` on `D_T(ℝ)` such that, for the
coordinate process X:
* `X_0 = 0` a.s.;
* for all `0 = t_0 < t_1 < ⋯ < t_k ≤ T`, the increments `(X_{t_i} − X_{t_{i−1}})_i` are independent with densities
  `p_{t_i − t_{i−1}}`.

Properties:
* **(P1)** Consistency: `P^X_T ∘ r_a⁻¹ = P^X_a` for a < T.
* **(P2)** Scaling: under `P^X_{cT}`, `(c^{−1/θ}X_{ct})_{t∈[0,T]}` has law `P^X_T`.
* **(P3)** No fixed discontinuities: `P^X_T(X_{t−} ≠ X_t) = 0` for every t.
* **(P4)** A.s. no negative jumps: `X_t ≥ X_{t−}` for all t.
* **(P5)** Simple Markov property: for s ≤ T, `(X_{s+u} − X_s)_{u ≤ T−s}` is independent of `F_s` with law
  `P^X_{T−s}`. Strong Markov property at stopping times.
* **(P6)** θ = 2: `P^X_T` is the law of `√2·B`.

**(b)** Bertoin 1996 Ch. I (existence via Lévy–Itô, Thm I.1; strong Markov property, Prop. I.6) [std; check];
Sato 1999 Thm 11.5 [std]; Kallenberg FMP [std].

**(c)**
* The limit in 6.2(ii) (FCLT).
* The reference law in 6.9(ii).
* The base object of Part F (§5.1).

**(d)** For 6.2(ii) and 6.9(ii): the f.d.d. characterization, P1, P3 and P5 (simple Markov, so that
`p_{1−a}(−X_a)/p_1(0)` is a martingale for C31). P4 and the strong Markov property are needed only for Parts F
and B (C18, C20–C23, C32).

**(e)** C1, C4 (uniqueness), C15. Existence: route R-F (C17 + C8 + C13, preferred), or Kolmogorov extension (BGW
vendor `projectiveLimit`) plus a càdlàg modification theorem (harder).

**(f)**
```lean
noncomputable def stableProcessLaw (θ T : ℝ) : ProbabilityMeasure (D T ℝ)
structure IsStableLevyLaw (θ T : ℝ) (P : ProbabilityMeasure (D T ℝ)) : Prop where
  start : ∀ᵐ f ∂P, f.toFun ⊥ = 0
  increments : ∀ (k) (t : Fin (k+1) → Icc 0 T), StrictMono t → (t 0 : ℝ) = 0 → (law of increments) = Measure.pi (pDens …)
theorem stableProcessLaw_isStableLevyLaw ; theorem IsStableLevyLaw.unique
theorem stableProcessLaw_restrict, stableProcessLaw_scaling, ae_continuousAt_stableProcessLaw (t),
        ae_no_negative_jumps
```

**(g)** 1500–3000 lines, existence included. Pitfall: a law on `ℝ^{[0,T]}` (Kolmogorov) is not a law on `D`; the
regularization step is what R-F avoids.

### C17. Functional limit theorem for walks in the stable domain of attraction

**(a)** Let `ξ_1, ξ_2, …` be i.i.d. real random variables, `S_k := ξ_1 + ⋯ + ξ_k`, and `(B_n)` positive with
`S_n/B_n ⇒ μ_θ` (C15). Then for every T > 0, `(S_{⌊nt⌋}/B_n)_{t∈[0,T]} ⇒ P^X_T` in `D_T(ℝ)` (J1).

Corollaries:
* (i) the same along any subsequence `n_k → ∞`;
* (ii) `B_{⌊nt⌋}/B_n → t^{1/θ}`;
* (iii) with the random time change of C6(4) and Lemma 6.2(i) (proved): Lemma 6.2(ii).

Here "W_n/B_n ⇒ X_1" is exactly `IsStableAttracted ν θ 0 B` (project) or `StableDomain μ θ B` (BGW). No centering is
needed because the steps have mean 0 (critical μ); for a general mean m, center by `nm`.

**(b)**
* Skorokhod 1957, *Theory Probab. Appl.* 2, 138–171, Theorem 2.7. Duquesne–Le Gall cite it in the proof of their
  Theorem 2.1.1 [read]: "the functional convergence holds iff the one-dimensional one does".
* Kallenberg FMP 2nd ed. Theorem 16.14 ("approximation of random walks") [std; check].
* Jacod–Shiryaev VII.2–3 [std; check].
* The paper cites "[Shir, Chapter VII]" (line 2017).

**(c)** Lemma 6.2(ii) (through 5.7), hence 6.1. Also C27 (DLG) and R-F (existence of C16).

**(d)** As stated. The paper needs integer steps ≥ −1, but the real-valued statement is no harder.

**(e)**
* C1, C2, C4, C8 (tightness through Aldous's criterion, or Billingsley Theorem 13.2 with BGW's Ottaviani bound
  `maximal_tight`), C12 (f.d.d.), C15.
* BGW `walkVecLaw_map_split` (independent blocks), `regularlyVaryingSeq` and `tendsto_div_of_tendsto_div`
  (regular variation of `B`).

**(f)**
```lean
theorem fclt_stable {ν : Measure ℤ} [IsProbabilityMeasure ν] {B : ℕ → ℝ} (hB : IsStableAttracted ν θ 0 B) (T : ℝ) (hT : 0 < T) :
  Tendsto (fun n => (Measure.infinitePi (fun _ : ℕ => ν)).map (stepPath T n (B n))) atTop (𝓝 (stableProcessLaw θ T))
```

**(g)** 1200–2500 lines. Pitfall: tightness in J1 is not implied by tightness of the maximum; one
needs a modulus or Aldous's criterion.

### C18. Fluctuation basics for X (spectrally positive, θ ∈ (1,2])

**(a)** Let `I_t := inf_{s≤t} X_s` and `T_x := inf{t : X_t < −x}`, x ≥ 0.
* **(F1)** I is continuous and nonincreasing, `I_t → −∞`, and `X_{T_x} = −x` (creeping down; no negative jumps).
* **(F2)** 0 is regular for (−∞,0) and for (0,∞), because X has unbounded variation for θ > 1.
* **(F3)** `(T_x)_{x≥0}` is a subordinator with `E e^{−λT_x} = e^{−xλ^{1/θ}}`.
* **(F4)** Kendall's identity: for x > 0, `P(T_x ∈ ds) = q_s(x) ds = (x/s) p_s(−x) ds`.
* **(F5)** Duality: for t > 0, `(X_t − X_{(t−s)−})_{s∈[0,t]}` has the law of `(X_s)_{s∈[0,t]}`.
* **(F6)** Minimum on a fixed interval (Millar): for fixed t > 0, a.s. the infimum of X over [0,t] is attained at a
  unique time `ρ_t ∈ (0,t)`, and X is continuous at `ρ_t`.

**(b)**
* Bertoin 1996 Ch. VII §1 (Theorem 1 for F3; Corollary 3 for F4, stated for spectrally **negative** processes, see
  N13) [std; check numbers].
* Bertoin 2000, MaPhySto Lecture Notes 8, Corollary 2.3 (F4, as cited by `Kautre` [read]).
* Bertoin 1996 II.1 Lemma 2 (F5) [std].
* Millar 1977, *Trans. AMS* 226, Propositions 2.2 and 2.4 (F6, as cited by Uribe Bravo 2014 [read]).
* Rogozin / Bertoin VII Corollary 5 (F2) [std].

**(c)**
* F4: the proof of 5.3 (C24) and the interpretation of `q_s`.
* F2, F5, F6: C32 (unique minimum of the bridge), hence 6.9(i).
* F1–F3: Part F.

**(d)** For the bridge: F2, F5, F6. For 5.3: F4. The rest is for Part F.

**(e)** C16 (strong Markov property), C15.

**(f)** `theorem kendall (hx : 0 < x) : law (firstPassageBelow x) = withDensity (fun s => qKernel θ s x)`;
`theorem ae_unique_argmin (ht : 0 < t) : ∀ᵐ f ∂stableProcessLaw θ t, ∃! s, ... ∧ ContinuousAt f s`.

**(g)** 2000–4000 lines (fluctuation theory from scratch). Pitfalls: Bertoin's sign conventions (N13), and the
distinction between hitting and first passage (equal here because X creeps down).

### C19. The Brownian instance (θ = 2)

**(a)**
* `X = √2·B`. `P^X_T` is the image of BGW's `wienerMeasure` (or `brownian`) under `√2·` and the inclusion `C → D`.
* `X^br := √2·` BGW `BrownianBridge.law`. Its prefix density on `[0,a]` relative to X is
  `p_{1−a}(−X_a)/p_1(0)` with Gaussian `p_t` of variance 2t (to prove; standard).
* `X^exc := √2·` BGW `VervaatBridge.law`.
* `H = X − I`; under N, `H^exc = X^exc` (N4).

**(b)** BGW `BrownianMotion/Gaussian/BrownianMotion.lean`, `ContinuumTrees/{BrownianBridge,VervaatBridge}.lean`
[survey, read in part]; Vervaat 1979, *Ann. Probab.* 7 [std].

**(c)** Remark 4.6 (C30).

**(d)** The objects and the bridge prefix density.

**(e)** BGW, C1, C5.

**(g)** 300–800 lines. Pitfall: BGW's `VervaatBridge.law` is the Brownian excursion **by definition**. Its
identification with Itô's normalized excursion is C35 at θ = 2 (Vervaat's theorem), which is open in BGW (the
continuum unique minimizer of the bridge is "separate, unproved" there).

---

## 5. Part F: excursion theory for `X − I`

These items are the library's deepest probability layer after the height process. The paper uses them only through
the objects `N(·|ζ>1)` and `N(·|ζ=1)` and through Proposition 5.3. **Recommended encoding (R-H):**
* `excLaw θ : ProbabilityMeasure (D 1 ℝ × C(I,ℝ))`: the law of `(X^exc, H^exc)`.
* `tailExcLaw θ`: the law of `(X, H)` restricted to [0,1] under `N(·|ζ>1)`, **defined** by the Itô mixture C22(E4).

The theorems of C21–C23 then say that these coincide with the objects built from the Poisson point process of
excursions.

### C20. Reflected process and local time

**(a)** `X − I` is a strong Markov process for `(F_t)` (the canonical filtration of X, augmented); 0 is regular for
itself; `−I` is a local time of `X − I` at 0, and its right-continuous inverse is `x ↦ T_x` (C18).

**(b)** Bertoin 1996 Ch. VI–VII [std]; Duquesne 2003 §3.2 and `Kautre` §2.1 [read].

**(c)** §5.1 (definitions). **(d)** As stated. **(e)** C16, C18.

### C21. Itô's excursion theorem; the excursion measure N

**(a)** Let `(g_i, d_i)_{i∈ℐ}` be the excursion intervals of `X − I` away from 0, and
`ω^i_s := X_{(g_i+s)∧d_i} − X_{g_i}`. Then `Σ_i δ_{(−I_{g_i}, ω^i)}` is a Poisson point measure on `[0,∞) × ℰ` with
intensity `dt ⊗ N(dω)`.
* ℰ is the set of `ω ∈ D(ℝ₊, ℝ₊)` with `ω(0) = 0` and `ζ(ω) := sup{s : ω(s) > 0} ∈ (0,∞)`.
* N is σ-finite, `N(ζ > t) = t^{−1/θ}/Γ(1−1/θ)` and `N(1 − e^{−λζ}) = λ^{1/θ}`.
* N-a.e., `ω(s) > 0` for s ∈ (0, ζ), and ω ends continuously, because X has no negative jumps.

**(b)** Itô's theorem: Bertoin 1996 Ch. IV (Theorem IV.10) [std; check]. The normalization of N(ζ > t) is in
Duquesne 2003 §3.2 and `Kautre` §2.1 [read], and is consistent with §1.4.

**(c)** §5.1. **(d)** As stated, restricted to the needs of C22–C24. **(e)** C20.

**(g)** C20–C23 together: 4000–8000 lines. Pitfall: N is an infinite measure; conditional laws are normalized
restrictions, never `ProbabilityTheory.cond` on a null set.

### C22. Itô description; the normalized excursion `X^exc`; `N(·|ζ>1)`

**(a)** Let `S^{(λ)}(ω) := (λ^{1/θ}ω(s/λ))_{s≥0}`.

*Itô description.* There is a unique family `(N_{(a)})_{a>0}` of probability measures on ℰ such that
`N_{(a)}(ζ = a) = 1`, `S^{(λ)}_* N_{(a)} = N_{(λa)}`, and `N = ∫_0^∞ N_{(a)} p_1(0) a^{−1−1/θ} da`
(`Kautre` (i)–(iii) [read]).

*Definition.* `N(·|ζ=1) := N_{(1)}`. This agrees with the paper's definition, the image of `N(·|ζ>t)` under the
normalization `ω ↦ (ζ^{−1/θ}ω(ζs))_{s∈[0,1]}`, which is independent of t.

Properties, all a.s. under `N(·|ζ=1)`:
* **(E1)** `X^exc ∈ D_1`, `X^exc_0 = 0`, `X^exc_1 = X^exc_{1−} = 0`, and `X^exc_s > 0` for s ∈ (0,1).
* **(E2)** No fixed discontinuities.
* **(E3)** θ < 2: `X^exc` has a jump, so `Δ̄(X^exc) > 0`. θ = 2: `X^exc = √2 e` is continuous.
* **(E4)** *(Itô mixture, the encoding of `N(·|ζ>1)` on [0,1].)* Let U be independent of `(X^exc, H^exc)`, with
  density `(1/θ)u^{−1−1/θ}` on (1,∞). Under `N(·|ζ>1)`, the pair `((X_t, H_t))_{t∈[0,1]}` has the law of
  `((U^{1/θ}X^exc_{t/U}, U^{1−1/θ}H^exc_{t/U}))_{t∈[0,1]}`. Note that `t/U < 1`. Under `N(·|ζ>1)`, X has no fixed
  discontinuity on [0,1] and `X_t > 0` for t ∈ (0,1].

**(b)** Chaumont 1997, *Bull. Sci. Math.* 121, 377–403 [std]; Bertoin 1996 VIII.4 [std; check];
`Kautre` §2.1 [read]; Duquesne 2003 §3.2 [read].

**(c)**
* All limit objects of 4.1, 5.1, 5.3, 5.8, 5.9, 6.1, 7.1(i) and Intro (II).
* E1 is used in 5.8 (`lim_α N(1/α < X_a < α | ζ=1) = 1`), in 5.9 and 6.1 (continuity at 1) and in R-B.
* E2 is used for every restriction.
* E3 is used for the remark after 7.1(i) ("almost surely positive"), which is not a numbered claim.

**(d)** E1, E2, E4. E3 is optional.

**(e)** C21, C16 (P2), C26 (for `H` in E4).

**(f)**
```lean
noncomputable def excLaw (θ) : ProbabilityMeasure (D 1 ℝ × C(unitInterval, ℝ))        -- (X^exc, H^exc)
noncomputable def tailExcLaw (θ) : ProbabilityMeasure (D 1 ℝ × C(unitInterval, ℝ))    -- N(·|ζ>1) on [0,1]
theorem tailExcLaw_eq_mixture : tailExcLaw θ = (mixture over U of scaled excLaw)        -- E4 (definition or theorem)
theorem excLaw_endpoints, excLaw_pos, excLaw_noFixedJump                                -- E1, E2
```

**(g)** Part of 4000–8000. Pitfall: the paper's `N(·|ζ=1)` is **not** an elementary conditioning (`{ζ = 1}` is
N-null). It must be the scaling definition.

### C23. Markov property under N

**(a)** Fix t > 0. Under `N(·|ζ > t)`, conditionally on `F_t`, the process `(X_{t+s})_{s≥0}` is the Lévy process
started at `X_t` and stopped at its first hitting time of 0 (equivalently, of (−∞,0], since X creeps down). In
integrated form: for bounded measurable `F ≥ 0` (`F_t`-measurable) and `G ≥ 0`,
`N(F · G(X_{t+·}) 1{ζ>t}) = N(F · E_{X_t}[G(X_{·∧T_0})] 1{ζ>t})`.

**(b)** `Kautre` Proposition 2.1 [read], citing the proof of Revuz–Yor XII Thm 4.1 for Brownian motion.

**(c)** The proof of 5.3 (C24), and E2. **(d)** The integrated form with `G` a function of the hitting time
`ζ = t + T_0∘θ_t` and of the path. **(e)** C21, C16 (strong Markov).

### C24. Proposition 5.3: the `Γ_a` identity

**(a)** Let a ∈ (0,1) and let `F : D([0,a],ℝ) × C([0,a],ℝ) → [0,∞)` be bounded and measurable. Then
`N(F(X|[0,a], H|[0,a]) | ζ = 1) = N(F(X|[0,a], H|[0,a]) · Γ_a(X_a) | ζ > 1)`.
* `X_a > 0` holds `N(·|ζ>1)`-a.s., so `Γ_a(X_a)` is defined.
* With F ≡ 1: `N(Γ_a(X_a) | ζ > 1) = 1`.
* In the encoding of C22: `E[F(r_a X^exc, r_a H^exc)] = E[F(r_a X̃, r_a H̃) Γ_a(X̃_a)]` with `(X̃, H̃)` the
  U-mixture of E4.

TRUE [D]. The derivation, following `Kautre`'s proof [read]:
1. By C23 and Kendall (F4), for u > a: `N(F 1{ζ>a}; ζ ∈ du) = N(F 1{ζ>a} q_{u−a}(X_a)) du`.
2. By the Itô description, `N(F; ζ ∈ du) = p_1(0) u^{−1−1/θ} N_{(u)}(F) du`.
3. Both sides are continuous in u, which gives at u = 1: `N(F q_{1−a}(X_a) 1{ζ>a}) = p_1(0) N_{(1)}(F)`.
4. Also `N(F Γ_a(X_a) 1{ζ>1}) = θ N(F q_{1−a}(X_a) 1{ζ>a})`.
5. Since `N(ζ>1) = θ p_1(0)` (§1.4), the two sides agree.

The constant θ and the definition of `Γ_a` are therefore correct as printed. It suffices to take F depending on X
only, because `H|[0,a]` is a measurable functional of `X|[0,a]` (C26).

**(b)** `Kautre` Proposition 2.3 [read], cited by the paper (line 1400). Le Gall 2010 (*SPA* 120) for the Brownian
case [std].

**(c)** Lemma 5.8 (eq:cvG), hence 5.9, 6.1 (through R-B), Intro (II) and 8.1(II).

**(d)** As stated, for each a ∈ (0,1). The test-function class may be reduced to bounded continuous F plus a
monotone-class extension. Mathlib's uniqueness of finite measures from bounded continuous functions on metric spaces
suffices; C4 is not needed.

**(e)** C18 (F4), C21–C23, C26; C15 item 7.

**(f)** `theorem gamma_identity (ha : a ∈ Ioo 0 1) (F : D a ℝ × C(Icc 0 a, ℝ) → ℝ) (hF : Measurable F) (hFb : bounded) :
∫ F ∘ restrict₂ a ∂excLaw θ = ∫ (F ∘ restrict₂ a) * (gammaA θ a ∘ evalEnd) ∂tailExcLaw θ`.

**(g)** 500–1000 lines given C21–C23. Pitfall: the continuity in u in step 3 needs the scaling (C22) and
dominated convergence; it is easy to overlook.

### C25. Chaumont's path construction (optional)

**(a)** Let `g_1 := sup{s ≤ 1 : X_s = I_s}`, `d_1 := inf{s > 1 : X_s = I_s}` and `ζ_1 := d_1 − g_1`. Then
`(ζ_1^{−1/θ}(X_{g_1+ζ_1 s} − X_{g_1}))_{s∈[0,1]}` has the law of `X^exc`. Similarly, by Duquesne 2003 (pathHexc),
`H^exc = (ζ_1^{1/θ−1} H_{g_1+ζ_1 s})_s`.

**(b)** Chaumont 1997; Duquesne 2003 §3.2 [read].

**(c)** Not used by the paper. An alternative **definition** of `X^exc` that needs no N: it is a path functional of
X, hence attractive for the library. With this definition, C24 still needs Part F to be proved.

---

## 6. Part H: height process and tree invariance principles

### C26. The height process `H` and `H^exc`

**(a)**
* **(H1)** For θ ∈ (1,2) and t ≥ 0, the limit `H_t := lim_{ε↓0} ε^{−1}∫_0^t 1{X_s < I^s_t + ε} ds` exists in
  `P`-probability and in N-measure on `{t < ζ}`, where `I^s_t := inf_{[s,t]} X`. For θ = 2,
  `H_t = X_t − I_t` (N4).
* **(H2)** H has a continuous modification under P and under N. DLG Theorem 1.4.3: H has continuous paths iff
  `∫_1^∞ du/ψ(u) < ∞`, which holds for `ψ = λ^θ`. Only this modification is used.
* **(H3)** For each t, `(H_s)_{s≤t}` is a measurable functional of `(X_s)_{s≤t}`. DLG fix the version
  `H^o_t := liminf_k ε_k^{−1}∫_0^t 1{X_s < I^s_t + ε_k} ds` [read].
* **(H4)** Joint scaling (§1.5). Under N, H depends only on the excursion straddling t, so H is defined under
  `N(·|ζ>t)` and, by scaling, under `N(·|ζ=1)` (`H^exc`).
* **(H5)** `H^exc` is a.s. continuous on [0,1], with `H^exc_0 = H^exc_1 = 0` and `H^exc_s > 0` for s ∈ (0,1). Paper
  Introduction, line 238; DLG.
* **(H6)** θ = 2: `H^exc = X^exc = √2 e`.

**(b)**
* Le Gall–Le Jan 1998, *Ann. Probab.* 26, 213–252 (N7) [std].
* Duquesne–Le Gall 2002, Astérisque 281: Ch. 1, Definition 1.2.1, (1.7), Lemma 1.2.? (`techheight`), Theorem 1.4.3
  (`continuityheight`) [read in the arXiv source; Astérisque numbers to check].
* Duquesne 2003 §3.1 [read].

**(c)**
* The objects in 4.1, 4.2, 5.1, 5.3, 5.8, 5.9 and Intro (II).
* H3 is used in the reduction of C24 to X-only tests and in 5.8 ("by eq:Hmes, H^{(n)} is a measurable function of
  W^{(n)}", which is the discrete analogue).
* H5 is used in 5.9 (eq:cvH, reversal, endpoint).

**(d)** H2, H3, H4, H5 and the existence of the law `excLaw`. H1 (the ε-approximation) is needed only to **define**
H and to prove C27; it is not used directly by the paper's proofs.

**(e)** C16, C18, C21, C22.

**(g)** 5000–10000 lines (exploration process, local times, continuity). Pitfall: the continuous modification exists
only a.s.; as a functional `D → C` the height map is not continuous, so any statement "H = H(X)" is an a.s. identity.

### C27. Duquesne–Le Gall: joint convergence for forests (unconditioned)

**(a)** Let μ be critical with `μ(1) < 1`, and `B_n > 0` with `W_n/B_n ⇒ X_1` (domain of attraction, θ ∈ (1,2]).
Let `(τ_k)` be i.i.d. `GW_μ` trees, V the concatenated Łukasiewicz path (a random walk with step law ν), `H^f` the
concatenated height process and `C^f` the concatenated contour. Then, for every T > 0,
`((V_{⌊nt⌋}/B_n, (B_n/n) H^f_{⌊nt⌋}, (B_n/n) C^f_{2nt}))_{t∈[0,T]} ⇒ ((X_t, H_t, H_t))_{t∈[0,T]}` in
`D_T × C_T × C_T` (the C-coordinates after linear interpolation, or in `D_T(ℝ³)`).

**(b)** Duquesne–Le Gall 2002: Theorem 2.3.2 (stable case of the functional convergence of `H`, with Theorem 2.3.1),
Theorem 2.4.1 (contour), Corollary 2.5.1 (joint, in `D(ℝ₊,ℝ³)`) [read]. Duquesne 2003 cites "Theorems 2.3.2 and 2.4.1
in DuLG" [read].

**(c)** Not used directly. It is the input from which C28 (Theorem 5.1) is derived.

**(d)** The `(V, H)` pair on [0,T] for **every** T, because the extraction in C28 needs horizons beyond the end of
the first long excursion (a.s. finite but random). C is not needed for C28.

**(e)** C17, C26, Duquesne–Le Gall ch. 1–2 (f.d.d. Theorem 2.2.1, tightness, Grimvall's equivalence Theorem 2.1.1).

**(g)** 4000–8000 lines on top of C26. Pitfalls:
* DLG index their theorems by the **space** scale `p` (integer), with time scale `pγ_p`. Converting to "all n with
  `B_n`" requires choosing `p(n) ≈ B_n` and absorbing time and space factors → 1 by C6(4). This is not hard but must
  be written.
* The discrete height in DLG is the step version `H_{⌊nt⌋}`; the paper interpolates. The two are equivalent through
  C5, since max increments → 0.

### C28. Theorem 5.1 (trees with at least n vertices)

**(a) Correct minimal statement.** Let μ satisfy `(H_θ)`; aperiodicity is not needed, because `P_μ(ζ ≥ n) > 0` for
every n. Let `B_n` be admissible (§1.3), let `τ_n ~ P_μ(·|ζ ≥ n)`, and extend W and H by 0 after ζ (§1.6). Then
`((W_{⌊nt⌋}(τ_n)/B_n)_{t∈[0,1]}, ((B_n/n) H_{nt}(τ_n))_{t∈[0,1]}) ⇒ ((X_t)_{t∈[0,1]}, (H_t)_{t∈[0,1]}) under N(·|ζ>1)`
in `D_1 × C_1`. Equivalently `⇒ tailExcLaw θ` (C22). The same holds on any `[0,T]`.

**(b)** Not a theorem in the cited source (N1). Duquesne–Le Gall 2002, concluding remark of §2.5 [read] (height or
contour only, "left to the reader"); `Kautre` Theorem 3.1 states the joint form and cites DLG [read].

[D] Derivation from C27, following the proof of DLG Prop. 2.5.2 [read]:
1. The first tree with `ζ ≥ n` in the i.i.d. sequence has law `P_μ(·|ζ ≥ n)`. Its rescaled `(W,H)` is the piece of
   `(V, H^f)` between the start and the end of the first excursion of V above its running infimum of rescaled
   length ≥ 1.
2. In the limit this is the first excursion of `X − I` of length > 1, whose law is `N(·|ζ>1)` by the Poisson
   structure (C21).
3. The extraction map is continuous at a.e. limit path. The ingredients: no excursion of length exactly 1;
   `{H = 0}` = support of `dI`; endpoints of excursions are approximated (DLG Lemma 2.5.3 `extrema` type argument);
   C9 instead of Skorokhod representation.

**(c)** Lemma 5.8 (the claim "the law of `(W^{(n)}, H^{(n)})` under `P(·|λ ≥ n)` converges", via Prop. 4.4(ii)),
hence 5.9, 6.1 (R-B), Intro (II), 8.1(II). Also `Kautre`'s proof of 4.1 (R-A).

**(d)** On [0,1] (only restrictions to [0,a], a < 1, are used). The paper's display (t ≥ 0 on the left, `0 ≤ t ≤ 1`
on the right) is reconciled this way (R7, N2).

**(e)** C27, C21, C22, C26, C9, C6.

**(f)**
```lean
def CitedDLGTail (θ) : Prop :=          -- Option A form until C27 is formalized
  ∀ (μ : PMF ℕ) (B : ℕ → ℝ), IsCritical μ → μ 1 ≠ 1 → StableDomain μ θ B →
    Tendsto (fun n => ((bienaymeLaw μ.toMeasure)[|sizeGeEvent n]).map (lukaHeightPath B n)) atTop (𝓝 (tailExcLaw θ))
```

**(g)** 800–1500 lines given C27. Pitfall: `lukaHeightPath` must use the paper's extension by 0 after ζ.

### C29. Theorem 4.1 (Duquesne: trees with exactly n vertices)

**(a)** Let μ be critical, aperiodic and in the domain of attraction of index θ ∈ (1,2], with `B_n` admissible. Let
`τ_n ~ P_μ(·|ζ = n)` (n large). Then `((B_n/n) C_{2nt}(τ_n))_{t∈[0,1]} ⇒ H^exc` in `C([0,1],ℝ)`. Jointly,
`((B_n/n)H_{nt}(τ_n), (B_n/n)C_{2nt}(τ_n))_{t∈[0,1]} ⇒ (H^exc, H^exc)`.
* Aperiodicity in Duquesne's sense (`gcd{k ≥ 1 : μ(k) > 0} = 1`) equals `(H_θ)(iii)` because `μ(0) > 0`.
* Periodic μ works along `n ≡ 1 (mod span)` (not needed).

**(b)** Duquesne 2003, *Ann. Probab.* 31, 996–1027, Theorem 3.1 (height and contour; hypothesis (H): an increasing
sequence `a_p` with `W_p/a_p ⇒ X_1`, μ aperiodic) [read]. Kortchemski `Kautre`, Theorem 3.? (height and contour) [read].
Not the Łukasiewicz path (N3).

**(c)** Theorem 4.5 (with Prop. 4.4, proved) and Remark 4.6. **Not** used in §§5–8: 5.9 proves the contour limit
under `λ = n` directly.

**(d)** The contour statement only.

**(e)** Route **R-A** (recommended): C28, C24, C6, C9–C11, C26 (H5), and discrete facts already proved:
* Kemperman with the uniform LLT, giving `n P_j(ζ = n) − q_1(j/B_n) → 0` uniformly for `j ≤ αB_n`;
* `lem_technical2` (5.11);
* `lem_locallimit` (`P(ζ ≥ n)/(nP(ζ = n)) → θ`).

Alternatively, cite it.

**(f)** `def CitedDuquesne (θ) : Prop := ∀ μ B, … → Tendsto (fun n => (P_μ[|sizeEvent n]).map (contourRescaled B n)) atTop (𝓝 ((excLaw θ).map Prod.snd))`.

**(g)** 1500–3000 lines via R-A. This is a copy of the 5.8 and 5.9 machinery with ζ in place of λ, and the project
will have that machinery anyway. Pitfall: the printed norming of 1.10 must not be used (R2, R4).

### C30. Finite variance (and θ = 2): Brownian identifications

**(a)** For θ = 2: `X^exc = H^exc = √2 e`, where e is the normalized excursion of standard linear Brownian motion
(Itô measure of B conditioned on unit length, by scaling). Consequently, with `B_n = σ√(n/2)`, Theorem 4.5 becomes
`((σ/(2√ζ)) C_{2ζt}(τ_n))_{t∈[0,1]} ⇒ e` (Remark 4.6). This is the leaf-conditioned analogue of Aldous's theorem
`(σ/(2√n))C_{2nt} ⇒ e` under `ζ = n`.

Characterizations of e that the library may use:
* (i) Itô (scaling);
* (ii) the Vervaat transform of the standard Brownian bridge (Vervaat 1979), which is BGW's `VervaatBridge.law`;
* (iii) the Bessel(3) bridge.

(i) is what §5.1 means; (i) = (ii) is C35 at θ = 2.

**(b)** Aldous 1993, *Ann. Probab.* 21, 248–289 [std; theorem number to check]; Le Gall 2005, *Probab. Surveys* 2,
Theorem 1.15 [std; check]; Duquesne 2003, remark after Theorem 3.1 ("If the offspring distribution has a finite
variance, then α = 2, H^exc is proportional to the normalized Brownian excursion") [read]; Vervaat 1979 [std].

**(c)** Remark 4.6 and the θ = 2 case.

**(d)** `H^exc = √2·e` with e defined as in (ii), plus the identification (i) = (ii) if one wants §5.1's literal
definition.

**(e)** C19, C22, C26, C35.

**(g)** 300–800 lines, plus the identification. Pitfall: Aldous's CRT is coded by `2e`. The θ = 2 tree limit here is
`T_{√2 e}`, i.e. Aldous's CRT with distances multiplied by `1/√2` (C37).

---

## 7. Part B: stable bridge and Vervaat transform

### C31. The stable bridge `X^br`

**(a)** There is a unique Borel probability measure `P^br` on `D_1(ℝ)` such that:
* **(i)** for every a ∈ (0,1) and every bounded measurable `F` on `D_a(ℝ)`,
  `E^br[F(X|[0,a])] = E^X[F(X|[0,a]) p_{1−a}(−X_a)/p_1(0)]`. The right side is consistent across a, because
  `M_a := p_{1−a}(−X_a)/p_1(0)` is a mean-one P-martingale on [0,1) (C15 item 4 and C16 P5);
* **(ii)** `P^br(X_1 = 0 and X_{1−} = 0) = 1`.

Moreover:
* **(iii)** time reversal: under `P^br`, `(−X_{(1−t)−})_{t∈[0,1]}` (with `X_{0−} := 0`) has law `P^br`, since
  reversed increments preserve positive jumps;
* **(iv)** no fixed discontinuities.

Uniqueness follows from (i), (ii) and C12(b).

**(b)**
* Prefix density: Bertoin 1996 VIII.3 formula (8), as cited by the paper [std; check]; Duquesne 2003 (abscont)
  and (rev) [read].
* Existence on [0,1] with left limit 0 at 1: Fitzsimmons–Pitman–Yor 1993 (*Seminar on Stochastic Processes 1992*,
  Progr. Probab. 33, 101–134) [std; check]; Chaumont–Uribe Bravo 2011, *Ann. Probab.* 39, Theorem 1 (weakly continuous
  Markovian bridges) [std; check; Uribe Bravo 2014 [read] uses it with hypotheses (K) integrable characteristic
  function and (R) 0 regular for both half-lines, both true here]; Chaumont 1997 [std].
* As a weak limit of random-walk bridges: Liggett 1968, *J. Math. Mech.* 18, 559–570 [std; check].

**(c)**
* 6.9(ii) is item (i) verbatim (N6).
* 6.1 uses the limit law of the bridge path, and needs (ii) for C11b (continuity at 1) and for the Vervaat map.
* (iii) is used in C32.

**(d)** (i) and (ii); (iii) only as a tool for C32.

**(e)** C15 (items 1, 4), C16 (P1, P3, P5), C12(b). Construction, two routes:
* **Direct:** projective limit of the consistent laws `M_a·P^X_a` over `a_k ↑ 1`, then left limit at 1. The left
  limit is the hard part. One way: check the reversal invariance (iii) on the explicit finite-dimensional densities
  `Π_i p_{t_i−t_{i−1}}(x_i − x_{i−1}) · p_{1−t_k}(−x_k)/p_1(0)` (reversal only permutes the factors), then transfer
  `X_{0+} = 0` to `X_{1−} = 0`. Alternatively, cite FPY.
* **As a limit:** C8 tightness of discrete bridges + C13, with the limit identified by (i) through a local limit
  theorem. This is exactly the paper's 6.1 argument, or Liggett's theorem.

**(f)**
```lean
noncomputable def stableBridgeLaw (θ) : ProbabilityMeasure (D 1 ℝ)
theorem stableBridgeLaw_prefix (ha : a ∈ Ioo 0 1) (F) (hF) : ∫ F ∘ restrict a ∂stableBridgeLaw θ
    = ∫ (F ∘ restrict a) * (fun f => pDens θ (1-a) (-(evalEnd f)) / Scalar.stableDensity θ 0) ∂stableProcessLaw θ a
theorem stableBridgeLaw_endpoint : ∀ᵐ f ∂stableBridgeLaw θ, f 1 = 0 ∧ leftLim f 1 = 0
```

**(g)** 1500–3000 lines. Pitfall: (i) alone does not determine a law on `D_1`; (ii) is a genuine extra statement (N6).

### C32. Unique minimum of the bridge, attained continuously

**(a)** `P^br`-a.s.:
* `inf_{[0,1]} X < 0`;
* there is a unique `g ∈ [0,1]` with `min(X_{g−}, X_g) = inf X` (and `X_{0−} := X_0`), and g ∈ (0,1);
* X is continuous at g, so `X_{g−} = X_g = inf X`.

Moreover g is uniform on (0,1) (not needed).

**(b)** Duquesne 2003 §4 [read: "thanks to (abscont) it is easy to see that X^br reaches its infimum a.s. at a
unique random time … uniformly distributed"]; Chaumont 1997; Uribe Bravo 2014, proof of Theorem 3 (via Millar 1977
Props. 2.2, 2.4) [read].

[D] Proof plan:
1. By C31(i) and C18 (F6) applied on `[0,a']`: for every `a' < 1`, the infimum over `[0,a']` is attained at a
   unique time, continuously. Use countably many `a'_k ↑ 1`.
2. By C18 (F2) and C31(i): `inf_{[0,ε]} X < 0` for all ε > 0, hence `inf X < 0 = X_1 = X_{1−}` (C31(ii)).
3. If the global infimum were attained at two times `s < t`, then `t < 1` by step 2. Choose `a'_k ∈ (t,1)` and
   contradict step 1.

**(c)** Prop. 6.9(i) (continuity of V at `X^br`), hence 6.1.

**(d)** As stated, without uniformity. **(e)** C31, C18 (F2, F5, F6), C16.

**(g)** 800–1500 lines, given C18. Pitfall (N5): uniqueness alone does not give the continuity of V; continuity of
X at g is also needed.

### C33. The càdlàg Vervaat map (paper 6.6) and the discrete correspondence (6.7)

**(a)** *Definition.* For `ω ∈ D_1(ℝ)` let `m := inf_{[0,1]} ω` and
`g_1(ω) := inf{t ∈ [0,1] : min(ω(t−), ω(t)) = m}`, with `ω(0−) := ω(0)`. The infimum is attained as a value or a
left limit, since paths are càdlàg on a compact set. Define `V(ω)(t) := ω(g_1 + t) − m` if `g_1 + t ≤ 1`, and
`V(ω)(t) := ω(g_1 + t − 1) + ω(1) − m − ω(0)` if `g_1 + t ≥ 1`. On `D_0 = {ω(0) = 0}` this is the paper's map, and
the two cases agree at `g_1 + t = 1`. Duquesne 2003 [read] uses the same formula, with `−ω(0)`.

Facts:
1. `V(ω) ∈ D_1(ℝ)`.
2. `V(ω)(0) = ω(g_1) − m`, which is 0 iff the infimum is attained as a value at `g_1`.
3. If ω is continuous at `g_1` (so `ω(g_1) = ω(g_1−) = m`), then `V(ω)(1) = V(ω)(1−) = ω(1) − ω(0)`, and the
   only jump of V(ω) not coming from a jump of ω is at `t = 1 − g_1`, of size `ω(1) − ω(1−)`.
4. `V` is Borel. Either via C4, using the measurability of `g_1` and the joint evaluation, or only a.e.-measurable
   via C9 when used.
5. *(Discrete correspondence, core of 6.7.)* Let `x ∈ ℤ^k`, `w_j := x_1 + ⋯ + x_j` with `w_0 = 0`, and suppose
   `min_{1≤j≤k} w_j < 0` (e.g. `w_k = −1`). Let B > 0 and `ω_x(t) := w_{⌊kt⌋}/B` (so `ω_x(1) = w_k/B`). Then
   `V(ω_x) = ω_{𝐕(x)}`, where 𝐕 is the discrete Vervaat transform of Definition 6.3, shifting at the first index
   `i_* ≥ 1` with `w_{i_*} = min_{1≤i≤k} w_i`. In particular `g_1(ω_x) = i_*/k`.

[D] Fact 5 checked by hand: the infimum over `0..k` equals the infimum over `1..k` because `w_k < 0 = w_0`. The
first-attainment time of the step path is `i_*/k`, since `min(ω(t−), ω(t))` at `t = j/k` is `min(w_{j−1}, w_j)`.
Both cases of V give `(w_{i_*+m} − w_{i_*})/B` and `(w_{i_*+m−k} + w_k − w_{i_*})/B`, which are the rotated partial
sums.

**(b)** Paper Definition 6.6; Duquesne 2003 §4 [read]; Vervaat 1979; BGW `ContinuumTrees/Vervaat.lean` (continuous
loops only) [read].

**(c)** 6.6, 6.7 (with Proposition 6.5, proved), 6.9(i), 6.1, 7.1(ii) (only the discrete map; already proved).

**(d)** Definition, facts 1, 3, 4 (a.e. form), 5.

**(e)** C1, C4 or C9.

**(f)**
```lean
noncomputable def vervaatD : D 1 ℝ → D 1 ℝ
theorem vervaatD_stepPath (x : List ℤ) (hx : (min of partial sums over 1..k) < 0) (hB : 0 < B) :
  vervaatD (stepPath x B) = stepPath (vervaat x) B          -- links to BGWLeaves.vervaat (Vervaat/Defs.lean)
```

**(g)** 500–900 lines. Pitfall: the step path must include the final value `w_k/B` at t = 1, which is a jump at 1.
Cor. 6.7 holds with this convention [D].

### C34. Continuity of the Vervaat map

**(a)** Let `f ∈ D_1(ℝ)` with:
* `f(0) = 0`;
* f continuous at 1;
* a unique `g ∈ (0,1)` with `min(f(g−), f(g)) = inf f`;
* f continuous at g.

Then V is J1-continuous at f. Moreover V(f) is continuous at `1 − g` and `V(f)(0) = 0`, and if `f(1) = 0` then
`V(f)(1) = V(f)(1−) = 0`.

[D] Proof sketch:
1. `inf` is 1-Lipschitz (C6(3)).
2. For `f_n → f`, `g_1(f_n) → g`: any limit point g′ satisfies `min(f(g′−), f(g′)) = inf f`, by the time-change
   characterization; uniqueness then gives g′ = g.
3. Using the continuity of f at g and at 1 (the wrap point) and its right-continuity at 0, build time changes
   `μ_n ∈ Λ_1` with `μ_n(1 − g) = 1 − g_1(f_n)`, close to the identity, such that `V(f_n)∘μ_n → V(f)` uniformly.
   The pieces `[0, 1 − g]` and `[1 − g, 1]` are treated separately.

The hypotheses are necessary in general (N5).

**(b)** No published statement for càdlàg paths was located. Duquesne 2003 §4 [read] proves the continuous-path
case (there the convergence is uniform). The paper asserts the needed consequence in the proof of 6.9(i).

**(c)** Prop. 6.9(i) (first half), hence 6.1.

**(d)** As stated. **(e)** C1, C5, C6, C33.

**(f)** `theorem continuousAt_vervaatD (h0 : f 0 = 0) (h1 : ContinuousAt f 1) (hg : ∃! g, …) (hcg : ContinuousAt f g) :
ContinuousAt vervaatD f`. Corollary: `∀ᵐ f ∂stableBridgeLaw θ, ContinuousAt vervaatD f` (with C31, C32).

**(g)** 600–1000 lines.

### C35. The Vervaat image of the bridge is the normalized excursion

**(a)** Under `P^br`, `V(X)` has law `N(·|ζ=1)`, i.e. the law of `X^exc`.

**(b)** Chaumont 1997, Théorème 4 (cited by the paper, line 2171) [std]. Uribe Bravo 2014, *Bernoulli* 20(1),
Theorem 4 [read]: for Lévy processes with (K) and (R), the Vervaat transform of the bridge from 0 to 0 of length t
has the law of the bridge of the process conditioned to stay positive, `P^{↑,t}_{0,0}`. Identifying the latter with
`N(·|ζ=t)` is a further step (Chaumont 1997; Miermont 2001, *EJP*, for the spectrally positive case [std]).

The reference "Chaumont–Pitman–Rivero, *The Vervaat transform of Lévy bridges*" given in the task brief was **not
found**. The closest works are Uribe Bravo 2014; Lupu–Pitman–Tang 2015 (Brownian bridges, *EJP*);
Bertoin–Chaumont–Pitman 2003 (*ECP*, first-passage bridges); Chaumont–Uribe Bravo 2014 (exchangeable increments,
arXiv:1405.1335).

**(c)** Prop. 6.9(i) (second half), hence 6.1 (identification of the limit), 7.1(i) and Intro (II).

**(d)** **Avoidable via R-B** (§0.4). Prove 6.1 with limit `V(X^br)`; then, given 5.9(i), the identity follows from
C12(b, c). If one defines `X^exc := V(X^br)` (as BGW does for θ = 2), then R-B shows that this
definition agrees with §5.1, given C24 and C28.

**(e)** Direct proof: C22, C31, C32 (excursion theory). Via R-B: C12, 5.9(i), 6.1.

**(g)** 0 lines via R-B; 3000+ lines if direct.

---

## 8. Part J: the largest-jump functional

### C36. `Δ̄` is 2-Lipschitz on `(D_T, d_T)`

**(a)** For `f ∈ D_T(ℝ)` let `Δ̄(f) := sup_{t∈(0,T]} (f(t) − f(t−)) ∨ 0`. This is the largest positive jump, 0 for
continuous f; it is attained by finiteness of jumps > ε. Then `|Δ̄(f) − Δ̄(g)| ≤ 2 d_T(f,g)` for all `f, g ∈ D_T`.

[D] Proof: for `λ ∈ Λ_T`, the jumps of `g∘λ` at t are those of g at `λ(t)`, so `Δ̄(g∘λ) = Δ̄(g)`; and
`|Δ̄(f) − Δ̄(h)| ≤ 2‖f − h‖_∞` for every h. Take `h = g∘λ` and the infimum over λ.

The same bound holds for the largest absolute jump. For the paper's step path, the final jump to −1 at t = 1 is
negative and does not affect `Δ̄`. The identity `Δ̄(W(τ)) = Δ(τ) − 1` fails for the one-vertex tree (N14), which is
irrelevant for `λ = n ≥ 2`.

**(b)** [D]; Jacod–Shiryaev VI.2.4-type continuity of jump functionals [std; check].

**(c)** Theorem 7.1(i) (paper line 2349: "Δ̄ is a continuous functional on D([0,1],ℝ)"). Also the θ = 2, σ² = ∞ case
of the Introduction (limit 0, since `X^exc` is continuous).

**(d)** As stated, with T = 1.

**(e)** C1.

**(f)** `noncomputable def maxJump (f : D T ℝ) : ℝ`; `theorem lipschitzWith_two_maxJump : LipschitzWith 2 maxJump`.

**(g)** 150–300 lines.

---

## 9. Part G: contour, real trees, GH and GHP

### C37. Real trees coded by continuous functions; GH(P) continuity

**(a)** For `g ∈ C([0,1],ℝ)`, the coded tree `T_g` uses the pseudo-distance
`d_g(s,t) = g(s) + g(t) − 2 min_{[s∧t, s∨t]} g`; it is a compact real tree, rooted at the class of 0, with mass
measure the image of Lebesgue measure.
* `g ↦ T_g` is Lipschitz for the rooted measured GHP distance: BGW `lipschitzWith_rootedMeasuredGHSpace`, constant 6
  [read].
* It is 2-Lipschitz for GH: Le Gall 2005, Lemma 2.4 [std; check].
* The θ-stable tree is `T_{H^exc}` (Duquesne 2003 §3.3 [read]; DLG).

**(b)** BGW `ContinuumTrees/{Coding,CodingRealTree,CodingMeasure,CodingStability}.lean` [survey]; Le Gall 2005 §2
[std].

**(c)** The GH claim after 5.10; the Introduction's GHP claim.

**(d)** Exists. To add: the forgetful map from rooted measured GHP to (unrooted, unmeasured) GH is 1-Lipschitz, if
BGW lacks it (about 50 lines).

### C38. From contour convergence to rooted measured GHP convergence of the finite trees

**(a)** BGW `FiniteTree.tendsto_rooted_laws_of_contour` [read].

Hypotheses:
* varying `Ω n`, maps `t n : Ω n → PlaneTree`;
* a deterministic divisor `b n > 0` with `b n → ∞`;
* measurability of the two observables;
* `P(r < b_n/ζ(t_n)) → 0` for every r > 0;
* `(b_n)^{−1}·contourFunction(t_n) ⇒ ν` in `C([0,1])`.

Conclusion: the rooted measured finite trees (vertex set, graph distance scaled by `b_n^{−1}`, root, **uniform
measure on vertices**) converge in law to `ν.map Coding.rootedMeasuredGHSpace`.

Conversions for this paper:
1. *Time convention.* BGW's `contourFunction(s) = C_{2(ζ−1)s}`, while the paper uses `C_{2ζs}`. If one converges
   to a continuous limit and `ζ → ∞` in probability, so does the other: the time change `s ↦ s(ζ−1)/ζ` is within
   `1/ζ` of the identity (C5, C10) [D].
2. *Deterministic divisor.* Use Remark 5.10: `b_n := n/(μ₀^{1−1/θ}B_n)`. The ratio condition holds because
   `b_n/ζ ≈ μ₀^{1/θ}/B_n → 0`.
3. With `ν = law(H^exc)`, the limit is the θ-stable tree with its mass measure.

**(b)** BGW [read]; paper line 1593 (GH, citing Le Gall 2005 §2).

**(c)** The GH claim after 5.10; the Introduction's GHP claim with the vertex measure.

**(d)** Conversions 1–2. **(e)** BGW, C5, C10, 5.9(ii), 5.10.

**(g)** 100–300 lines.

### C39. Uniform leaf measure versus uniform vertex measure

**(a)** Let t be a finite plane tree with ζ vertices `u(0) < ⋯ < u(ζ−1)` (lexicographic order) and λ ≥ 1 leaves,
`m_V` the uniform measure on vertices and `m_L` the uniform measure on leaves.
* For `i < j`, `d_gr(u(i), u(j)) ≤ H_i + H_j − 2 min_{i≤k≤j} H_k + 2`.
* Coupling via U uniform on [0,1): `u(⌊ζU⌋) ~ m_V` and the `⌈λU⌉`-th leaf `~ m_L`. This gives
  `d_P^{(c·d_gr)}(m_V, m_L) ≤ c·(2 ω_H(δ) + 2) + δ'`. Here `ω_H(δ)` is the modulus of continuity of `k ↦ H_k` at
  index scale `δζ`, δ bounds the index displacement `sup_t |Λ^{−1}(λt) − ζt|/ζ` (plus η, the size of the excluded
  initial window), and δ′ is the probability of the bad event.
* Corollary 3.3 (`cor_Lambda`, proved) makes δ → 0 in probability. The tightness of `(B_ζ/ζ)H_{ζ·}` in C (5.9(ii))
  makes `ω_H(δ)` → 0. BGW's perturbation lemma (C10(1)) then transfers C38 to the leaf measure.

**(b)** [D] (paper-level); Le Gall 2005 (the inequality for `d_gr`) [std]; Rizzolo 2015 [read] for the target
statement with the leaf measure.

**(c)** The Introduction's GHP claim (N9).

**(d)** As stated. **(e)** BGW, `cor_Lambda`, C10, 5.9(ii).

**(g)** 300–600 lines.

---

## 10. Usage map: paper result to classical inputs, with the proof skeleton

Each entry gives the corrected statement where needed, then the classical items in the order the proof uses them.
"Proved" refers to tranche 1 (`FORMALIZATION_REPORT.md`).

* **4.1** (contour, `ζ = n`, `C([0,1])`): C29. If R-A is used: C28 + C24 + the proved size estimates.
* **4.2** (`H^exc` is the height excursion): definitional, C22 + C26.
* **4.5** (contour under `λ ≥ n`): 4.1, then Prop. 4.4(i)(ii) (proved) with `U_n = F(rescaled contour)` for bounded
  continuous F, then Mathlib `tendsto_iff_forall_integral_tendsto`. No `D` needed.
* **4.6**: 4.5 + C30 (divide by √2).
* **§5.1** (the objects): C16, C18, C20–C23, C26. Encoding R-H: `excLaw`, `tailExcLaw`.
* **5.1**: C28.
* **5.3**: C24.
* **5.7**, corrected (N10, R7):
  * Statement: let `Z^n` be random elements of `D_T(ℝ)×C_T^{d−1}` (or `D_T(ℝ^d)`) with `Z^n ⇒ Z`, Z a.s. continuous
    at a < T, and `K_n ∈ (0,∞)^d`, `S_n > 0` → 1 in probability on the same spaces. Then
    `(K_n ⊙ Z^n_{(S_n t) ∧ T})_{t∈[0,a]} ⇒ (Z_t)_{t∈[0,a]}`.
  * Proof: C10(2) gives `(Z^n, K_n, S_n) ⇒ (Z, 1, 1)`; then C9 with C6(4) (a.s. continuity at `(Z,1,1)`); C2 for
    products.
* **5.8**:
  1. 5.1 via C28, transferred to `P(·|λ ≥ n)` by Prop. 4.4(ii) (proved).
  2. 5.7 with `S_n = T_{aμ₀n}/(an) → 1` (Lemma 5.6, proved).
  3. Prop. 5.2 and eq:cva (from Cor. 5.5 and Thm 3.1, proved).
  4. C15 item 7 (`Γ_a` continuous, so the functional `F·Γ_a(π_a)·cutoff` is a.e. continuous), C9 with α chosen
     off the atoms (N11).
  5. 5.3 (C24).
  6. E1 of C22 (`X^exc_a > 0`) to remove the cut-off.
* **5.9(i)**: 5.8 + 5.7, with `K_n = B_{r_n}/B_ζ` and `S_n = aζ/T_{aμ₀r_n}` (from Cor. 3.3 and Lemma 5.6(ii),
  proved).
* **5.9(ii)**:
  1. eq:cvH (5.8 + 5.7 on the H coordinate) and C5 (max increments → 0).
  2. eq:HC by C10(1).
  3. The extension to [0,1] in `C_1` by C11b: the terminal control comes from the reversal invariance of the contour
     under `P(·|λ=n)` (mirror trees) and from `H^exc_0 = 0` (C26 H5); the limit is continuous at 1 (H5).
  4. eq:g with C10(1) again.
* **5.10**: C10(2) with `B_ζ/B_n → μ₀^{−1/θ}` and `ζ/n → 1/μ₀` in probability (proved discrete inputs plus regular
  variation), and the continuous map `(f, c) ↦ c·f`.
* **GH claim after 5.10**:
  * Statement: `(V(τ_n), (B_ζ/ζ)·d_gr) ⇒ (T_{H^exc}, d_{H^exc})` in GH; equivalently with
    `μ₀^{1−1/θ}B_n/n`.
  * Proof: 5.9(ii) + 5.10 + C38 + C37 (forgetful map).
* **6.2(ii)**: C17 along `N_n = ⌊n/μ₀⌋`, then 5.7 with `S_n = T_{an}/(aN_n) → 1` (Lemma 6.2(i), proved). The
  printed "for every a > 0" needs the FCLT on horizons `T > a`; use C17 for every T, or C17 on [0,1] with C16 (P2)
  and regular variation (R-E).
* **6.6**: C33 (definition). **6.7**: C33 fact 5 + Prop. 6.5 (proved).
* **6.9(i)**:
  * Continuity: C34 + C31(ii) + C32.
  * Law: C35, or R-B.
* **6.9(ii)**: C31(i).
* **6.1**:
  1. Prefix: Lemma 6.10 + Lemma 6.11 (proved) + 6.2(ii) + 6.9(ii); C9 with cut-offs (N11).
  2. Random time and space: 5.7.
  3. Terminal: eq:montrertension, discrete, using Prop. 6.8 (proved), then C11b in `D_1` (N12, R-C).
  4. Vervaat: C9 with C34 at `X^br`.
  5. Identification: C35 or R-B; 6.7.
* **7.1(i)** (θ < 2):
  * Statement: `μ₀^{1/θ}Δ(τ_n)/B_n ⇒ Δ̄(X^exc)` with admissible `B_n`.
  * Proof: 6.1 + 5.10 + C36 (continuous map) + C10(1) for the shift by `1/B_n`.
  * The θ = 2, σ² = ∞ case of the Introduction gives the limit 0, by the same argument.
* **Introduction (II)** (joint triple on [0,1], limit `(X^exc, H^exc, H^exc)` coupled under `N(·|ζ=1)`):
  1. Joint prefixes on [0,a]: 5.8 with 5.7 for the pair, then `C ≈ H` by C10(1).
  2. Terminal control: for W from 6.1 via C6(3) + C9; for C and H from the proof of 5.9(ii).
  3. Conclude by C11b in `D_1 × C_1 × C_1`; transfer to `D_1(ℝ³)` by C5(4) if wanted.
* **Introduction, GHP**: C38 (vertex measure) and C39 (leaf measure), with 5.9(ii) and 5.10. The measure must be
  specified (N9).
* **8.1(II)**: the same classical inputs as Introduction (II), with ζ_A in place of λ. The discrete A-analogues of
  5.2, 5.4, 5.6, 6.5, 6.10, 6.11 are partly proved (`eq_gen_corrected`, M10). When the span exceeds one, the discrete densities must be restricted to the admissible residue class.

---

## Sources

| Source | How | What was checked |
|---|---|---|
| Kortchemski, *A simple proof of Duquesne's theorem…* (arXiv:1109.4138, revised source 2014; Sém. Probab. XLV, LNM 2078) | LaTeX source read | normalization of N, Itô description (i)–(iii), Prop. 2.1 (Markov under N), Prop. 2.2 (Kendall, citing Bertoin 2000 Cor. 2.3), Prop. 2.3 = Γ_a identity and its proof, Theorem 3.1 (cites DLG §2.6), H = X − I at θ = 2, main theorem (H and C only) |
| Duquesne, Ann. Probab. 31 (2003) (arXiv:math/0509522) | LaTeX source read | Thm 3.1 (H and C under ζ = p; hypothesis (H)); §3.1 misprints (N8); bridge prefix density and reversal; Vervaat definition; continuity of V only at continuous paths (N5); bibliography (LGLJ pages, N7) |
| Duquesne–Le Gall, Astérisque 281 (arXiv:math/0509558) | LaTeX source read | (H1)–(H3), Definition of H, β > 0 case, Theorem 1.4.3 (continuity iff ∫du/ψ < ∞), Theorem 2.1.1 (Skorokhod 1957 Thm 2.7), Theorems 2.3.1–2.3.2, 2.4.1, Corollary 2.5.1, Prop. 2.5.2 and the concluding remark of §2.5 (N1) |
| Uribe Bravo, Bernoulli 20(1) (2014) (arXiv:1101.4184) | LaTeX source read | hypotheses (K), (R); Theorem 4 (Vervaat for Lévy bridges); Millar 1977 Props. 2.2, 2.4 for the unique minimum |
| Rizzolo, Ann. IHP 51 (2015) (arXiv:1105.2528) | LaTeX source read | Theorem 1.1: rooted GHP, uniform measure on A-vertices, finite variance |
| Mathlib (pinned) | grep | `TendstoInDistribution.prodMk_of_tendstoInMeasure_const` hypotheses; `isCompact_closure_of_isTightMeasureSet`; `IsTightMeasureSet.prodMk`; `IsGδ.setOfPred_continuousAt` |
| BGW | grep and reading | `StableDomain`, `stableDensity`, `stableDensity_zero`, `lipschitzWith_stableDensity`, `regularlyVaryingSeq`, `maximal_tight`, `tendsto_probabilityMap_of_error_probability`, `tendsto_rooted_laws_of_contour`, `lipschitzWith_rootedMeasuredGHSpace`, `BrownianBridge.law`, `VervaatBridge.law` |
