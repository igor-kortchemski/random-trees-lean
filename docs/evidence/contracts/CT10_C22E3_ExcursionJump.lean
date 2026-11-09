import BGW.StableTrees.StraddlingExcursion
import BGW.Skorokhod.Jump
import BGW.StableTrees.StablePositiveJumps

/-! Contract probe for CT10 node C22E3 (`CLASSICAL_THEORY_INPUTS.md` C22(a), property E3): the
normalized excursion `X^exc ~ levyExcLaw θ` has a positive jump (`maxJump > 0`) a.s. when
`θ < 2`, and is continuous with `maxJump = 0` a.s. when `θ = 2`.  The host-level input is the
companion contract `CT10_C22E3a_StableJumps.lean` (copied below, not part of this contract).
Suggested maintained module: `BGW/StableTrees/ExcursionJump.lean`, namespace `BGW.StableTrees`
(imports the E3a module, `BGW.StableTrees.StraddlingExcursion`, `BGW.Skorokhod.Jump`; proof-only
imports `BGW.StableTrees.BrownianExcursion` (K18b), `BGW.Skorokhod.ContinuousEmbedding`,
`BGW.StableTrees.UnitExcursionDensityTransfer` (`leftLim_excursionRestrict`)).

SOURCE (C22(a), E3).  "θ < 2: `X^exc` has a jump, so `Δ̄(X^exc) > 0`.  θ = 2: `X^exc = √2 e` is
continuous."  `Δ̄` is the largest positive jump, `maxJump` (C36, `BGW/Skorokhod/Jump.lean`).
C22(d): E3 is optional (only the remark after 7.1(i) uses it).

ROUTE (θ < 2).  Transfer from the host through the sealed straddling excursion (CT7 O01):
`map_straddling_restrict_eq_levyExcLaw` says that `excursionRestrict 1 (normalizeExc θ e_t)` has
law `levyExcLaw θ`, where `e_t = straddlingExcursion t f = excursionCut g_t d_t f` is the piece of
the host path on `[g_t, d_t]` (definitionally, see O01).  A.s. `g_t < d_t` and the cut is valid
(`ae_straddle_spec`), and a.s. the host has a positive jump in every open interval (E3a), in
particular at some `u ∈ (g_t, d_t)`.  Under the affine time change `s = (u - g_t)/ζ_t` and the
positive space factor `ζ_t^{-1/θ}` this is a positive jump of the normalized path at an interior
time `s ∈ (0,1)`.  See E3a for the comparison with the FCLT and Vervaat/bridge routes.
ROUTE (θ = 2).  K18b `BrownianIdentification.levyExcLaw_two`:
`levyExcLaw 2 = law.map (e ↦ ofContinuous (√2 • e))`; continuous paths have `leftLim = value`
everywhere, so `maxJump = 0`, and the range of `ofContinuous` is closed
(`isClosedEmbedding_ofContinuous`), hence Borel.

TRUTH CHECK (boundary conventions).
(1) `maxJump f = ⨆ t, max (f t - leftLim f t) 0` over `t ∈ [0,1]`.  At `t = 0`,
    `𝓝[<] 0 = ⊥` in `Icc 0 1`, so `leftLim f 0 = f 0` (no spurious jump at the left end).  The
    `iSup` of reals is `0` when unbounded, but càdlàg paths on `[0,1]` are bounded
    (`D.isBounded_range`), so `le_ciSup` applies; `maxJump ≥ 0` always.
(2) `excursionRestrict 1 e = DLoc.restrict 1 e.path`, and `leftLim` commutes with it at interior
    times (`leftLim_excursionRestrict`, sealed).  `normalizeExc θ e` has path
    `s ↦ (ζ⁻¹)^{1/θ} e(ζ s)` with `ζ = e.lifetime > 0`; the factor is `> 0` for EVERY real `θ`,
    so the deterministic transfer lemma carries no hypothesis on `θ`.
(3) For a valid cut, `(excursionCut g d f).path s = f(min (g + s) d) - f g`
    (`excursionCut_eval`) and its lifetime is `d - g` (`excursionCut_lifetime`).  For `u ∈ (g,d)`
    the time `min (g + ζ s) d` equals `g + ζ s` on a left neighbourhood of `s₀ = (u-g)/ζ`, so the
    normalized path jumps at `s₀` by `ζ^{-1/θ}(f u - leftLim f u) > 0`.  An excursion that
    starts with a jump is never represented by a valid cut (`cutValid` docstring); the jump used
    here is interior, so this convention is irrelevant.
(4) `{x | 0 < maxJump x}` is open (`lipschitzWith_two_maxJump.continuous`), hence Borel, so
    `ae_map_iff` transfers the a.s. statement from `stableLocalLaw θ` to `levyExcLaw θ`; the
    map is a.e.-measurable (`aemeasurable_straddleData`, `measurable_excursionRestrict`).
(5) `θ = 2` must be excluded from the first statement: the host is continuous at `θ = 2`, and
    the second statement shows `maxJump = 0` a.s. there.  Combined form:
    `0 < maxJump x ↔ θ < 2`, a.s. under `levyExcLaw θ`, for every `1 < θ ≤ 2`.
(6) No vacuity: `levyExcLaw θ` is a probability measure (sealed), so the a.s. statements are not
    trivially true; outside `1 < θ ≤ 2` it is a junk law, excluded by the hypotheses.

PROOF PLAN (size 120-220 lines; (ii)-(v) were proved in a scratch probe from `sorry`ed (i) and
`ae_forall_exists_pos_jump`, so the only open content here is (i).
(i) `maxJump_excursionRestrict_normalizeExc_pos` (deterministic): evaluate with
    `normalizeExc`, `excursionScale` and `excursionCut_eval`/`excursionCut_lifetime` (as in O01
    `ae_normalize_straddling_path`); compute `leftLim` at `s₀` with `leftLim_eq_of_tendsto`,
    `leftLim_excursionRestrict` and `IsCadlag.tendsto_nhdsLT_leftLim` composed with the
    continuous strictly increasing map `s ↦ g + ζ s`; conclude with `le_ciSup` (boundedness from
    `isBounded_range`).  (~80-150)
(ii) `ae_maxJump_straddling_pos`: filter `ae_straddle_spec hθ ht` (valid cut,
    `g_t < t < d_t`) and the copied `ae_forall_exists_pos_jump hθ hθ2` at `(g_t, d_t)`; apply (i)
    (`straddlingExcursion t f = excursionCut (straddleStart t f) (straddleEnd t f) f` by
    `rfl`).  (~5)
(iii) `ae_maxJump_pos_levyExcLaw`: `map_straddling_restrict_eq_levyExcLaw hθ one_pos`, then
    `(ae_map_iff hmeas hopen.measurableSet).mpr` with (ii) at `t = 1`.  (~10)
(iv) `ae_maxJump_eq_zero_levyExcLaw_two`: rewrite with K18b `levyExcLaw_two`, split the map as
    `ofContinuous ∘ (√2 • ·)` (fold by `rfl`, then `Measure.map_map`), `ae_map_mem_range` (args:
    the closed-range `MeasurableSet`, then `measurable_ofContinuous.aemeasurable`); for
    `x = ofContinuous g`, `leftLim = g` (`g.continuous.continuousAt.continuousWithinAt.leftLim_eq`,
    as in
    `BrownianIdentification`), so every term of the `iSup` is `0` (`simp`).  (~20)
(v) `ae_maxJump_pos_iff_levyExcLaw`: case split `θ < 2` / `θ = 2` on (iii) and (iv).  (~10)
RISK: none known for (i)-(v) beyond bookkeeping; the depth is in E3a (`ae_forall_exists_pos_jump`,
estimate 400-700 lines there).

ACYCLICITY.  Sealed suppliers: O01 (`ae_straddle_spec`, `map_straddling_restrict_eq_levyExcLaw`,
`aemeasurable_straddleData`), the carrier (`excursionCut_eval`, `excursionCut_lifetime`,
`normalizeExc`), `Skorokhod.Jump` (`maxJump`, `lipschitzWith_two_maxJump`), K18b
(`levyExcLaw_two`), `Skorokhod.ContinuousEmbedding`; and the new E3a.  No height input.

BINDER SCOPE (AUDITOR_RULES).  No integral or sum occurs; `maxJump` is a sealed definition whose
`⨆` body `max (f t - leftLim f t) 0` is fully parenthesized. -/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees



/-! ## Transfer to the normalized excursion -/

/-- **Deterministic transfer**: a positive jump of the host strictly inside a valid cut `(g, d)`
is a positive jump of the normalized cut excursion restricted to `[0,1]`. -/
theorem maxJump_excursionRestrict_normalizeExc_pos (θ : ℝ) {g d u : ℝ≥0} {f : DLoc}
    (hcut : cutValid g d f) (hu : u ∈ Set.Ioo g d)
    (hjump : Function.leftLim f.1 u < f.1 u) :
    0 < maxJump (excursionRestrict 1 (normalizeExc θ (excursionCut g d f))) := sorry

/-- For `1 < θ < 2`, the normalized excursion straddling `t > 0` has a positive jump on `[0,1]`,
almost surely. -/
theorem ae_maxJump_straddling_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hθ2 : θ < 2) {t : ℝ≥0}
    (ht : 0 < t) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      0 < maxJump (excursionRestrict 1 (normalizeExc θ (straddlingExcursion t f))) := sorry

/-! ## C22 (E3) -/

/-- **C22 (E3), `θ < 2`.**  The normalized excursion has a positive jump: `Δ̄(X^exc) > 0` a.s. -/
theorem ae_maxJump_pos_levyExcLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hθ2 : θ < 2) :
    ∀ᵐ x ∂(levyExcLaw θ : Measure (D 1 ℝ)), 0 < maxJump x := sorry

/-- **C22 (E3), `θ = 2`.**  The normalized excursion `√2 e` is continuous, so `Δ̄(X^exc) = 0`
a.s. -/
theorem ae_maxJump_eq_zero_levyExcLaw_two :
    ∀ᵐ x ∂(levyExcLaw 2 : Measure (D 1 ℝ)), maxJump x = 0 ∧ Continuous x := sorry

/-- **C22 (E3), combined form**: for `1 < θ ≤ 2`, almost surely `Δ̄(X^exc) > 0` iff `θ < 2`. -/
theorem ae_maxJump_pos_iff_levyExcLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ x ∂(levyExcLaw θ : Measure (D 1 ℝ)), (0 < maxJump x ↔ θ < 2) := sorry

end BGW.StableTrees
