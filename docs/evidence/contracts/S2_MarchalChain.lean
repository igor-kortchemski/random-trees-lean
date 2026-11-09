import BGW.StableTrees.MarchalWeights
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Set.Card

/-! # Contract probe S2: Marchal growth chain on finite leaf-labelled trees

State space: `LTree n` = a `SimpleGraph (Fin m)` (for some `m`) that is a tree, with leaves
exactly `labels : Fin (n+1) ↪ Fin m` (label `i` is `A_i`, `A_0` the root) and no vertex of
degree two; `State n` is the quotient by label-preserving graph isomorphism. The carrier is
`Fin m` (not an arbitrary type) so the quotient lives in `Type`.

Chain: from `⟦T⟧` with `T : LTree (k+1)`, draw a `Position T.G` from `selectionPMF`
(edge weight `α - 1`, degree-`d ≥ 3` vertex weight `d - 1 - α`), graft the leaf `A_{k+2}`
on the middle of the edge / on the vertex, and take the class.

Law: `law k` is the law of the state with leaves `A_0..A_{k+1}` started from the edge `A_0 — A_1`.

Exact law (derived here, to be double-checked against Curien–Haas arXiv:1207.5418 §1.3 and
Marchal 2008): the history of a leaf-labelled tree is unique (restrictions to the first leaves,
suppressing degree-two vertices), so
`P(T_n = t) = (α-1)^{#internal} ∏_{v internal} ∏_{j=2}^{deg v - 2} (j - α) / ∏_{j=1}^{n-1} (jα-1)`.

No plane-tree Rémy algorithm exists in the library; Rémy's law is stated directly as the
uniform law on binary states (`(2n-3)!!` of them at step `n`). -/

open scoped ENNReal Classical

namespace BGW.StableTrees.Marchal

/-- Finite leaf-labelled trees with leaves exactly `A_0, …, A_n` and no degree-two vertex. -/
structure LTree (n : ℕ) where
  /-- Number of vertices. -/
  m : ℕ
  /-- The tree. -/
  G : SimpleGraph (Fin m)
  tree : G.IsTree
  /-- Leaf `A_i` is the vertex `labels i`. -/
  labels : Fin (n + 1) ↪ Fin m
  leaf : ∀ v, G.degree v = 1 ↔ v ∈ Set.range labels
  branch : ∀ v, G.degree v ≠ 1 → 3 ≤ G.degree v

/-- Label-preserving graph isomorphism. -/
instance LTree.setoid (n : ℕ) : Setoid (LTree n) where
  r T T' := Nonempty {e : T.G ≃g T'.G // ∀ i, e (T.labels i) = T'.labels i}
  iseqv :=
    ⟨fun T => ⟨⟨SimpleGraph.Iso.refl, fun _ => rfl⟩⟩,
     fun ⟨⟨e, h⟩⟩ => ⟨⟨e.symm, fun i => by rw [← h i]; simp⟩⟩,
     fun ⟨⟨e, h⟩⟩ ⟨⟨f, g⟩⟩ => ⟨⟨e.trans f, fun i => by simp [h i, g i]⟩⟩⟩

/-- Marchal states at step `n`: trees with leaves `A_0..A_n`, modulo labelled isomorphism. -/
abbrev State (n : ℕ) := Quotient (LTree.setoid n)

/-- The states are finitely many. -/
theorem finite_state (n : ℕ) : Finite (State n) := sorry

/-- The start state: the single edge `A_0 — A_1`. -/
def startState : State 1 :=
  ⟦{ m := 2, G := ⊤, tree := sorry, labels := Function.Embedding.refl _,
     leaf := sorry, branch := sorry }⟧

/-- Graft a new leaf `A_{n+1}` (the last vertex) on the middle of an edge (new midpoint `m`,
new leaf `m+1`) or on an internal vertex (new leaf `m`). -/
noncomputable def graftGraph {m : ℕ} (G : SimpleGraph (Fin m)) :
    (p : G.edgeSet ⊕ {v : Fin m // 3 ≤ G.degree v}) →
      SimpleGraph (Fin (match p with | .inl _ => m + 2 | .inr _ => m + 1))
  | .inl e => SimpleGraph.fromRel fun x y =>
      (∃ x' y' : Fin m, x.val = x'.val ∧ y.val = y'.val ∧ G.Adj x' y' ∧ s(x', y') ≠ e.val) ∨
      (x.val = m ∧ (y.val = m + 1 ∨ ∃ z : Fin m, z ∈ (e.val : Sym2 (Fin m)) ∧ y.val = z.val))
  | .inr v => SimpleGraph.fromRel fun x y =>
      (∃ x' y' : Fin m, x.val = x'.val ∧ y.val = y'.val ∧ G.Adj x' y') ∨
      (x.val = m ∧ y.val = v.val.val)

/-- The tree obtained by grafting `A_{n+1}` at a position of `T`. -/
noncomputable def graft {n : ℕ} (T : LTree n) (p : Position T.G) : LTree (n + 1) :=
  sorry -- carrier `Fin (m+2)` / `Fin (m+1)` per `graftGraph`; labels extended by `Fin.lastCases`

/-- One Marchal step on a representative: select a position (`selectionPMF`), graft, take class. -/
noncomputable def stepRep {k : ℕ} {α : ℝ} (hα : 1 < α) (hα2 : α ≤ 2) (T : LTree (k + 1)) :
    PMF (State (k + 2)) :=
  (selectionPMF T.G T.tree T.labels T.leaf T.branch (Nat.le_add_left 1 k) α hα hα2).map
    fun p => ⟦graft T p⟧

/-- Grafting commutes with labelled isomorphism, up to the induced bijection of positions. -/
theorem stepRep_congr {k : ℕ} {α : ℝ} (hα : 1 < α) (hα2 : α ≤ 2) {T T' : LTree (k + 1)}
    (h : T ≈ T') : stepRep hα hα2 T = stepRep hα hα2 T' := sorry

/-- The transition kernel `State (k+1) → PMF (State (k+2))` (automatically a probability
kernel: total mass one is `selectionPMF`'s normalization, i.e. `sum_selectionWeight`). -/
noncomputable def step {α : ℝ} (hα : 1 < α) (hα2 : α ≤ 2) (k : ℕ) :
    State (k + 1) → PMF (State (k + 2)) :=
  Quotient.lift (stepRep hα hα2) fun _ _ h => stepRep_congr hα hα2 h

/-- Total selection weight at step `n = k+1` is `n α - 1` (reuse of `sum_selectionWeight`). -/
theorem sum_selectionWeight_step {k : ℕ} (T : LTree (k + 1)) (α : ℝ) :
    ∑ p : Position T.G, selectionWeight T.G α p = ((k + 1 : ℕ) : ℝ) * α - 1 :=
  sum_selectionWeight T.G T.tree T.labels T.leaf T.branch α

/-- The law of the state with leaves `A_0..A_{k+1}`, started from the edge `A_0 — A_1`. -/
noncomputable def law {α : ℝ} (hα : 1 < α) (hα2 : α ≤ 2) : (k : ℕ) → PMF (State (k + 1))
  | 0 => PMF.pure startState
  | k + 1 => (law hα hα2 k).bind (step hα hα2 k)

/-- Number of vertices of degree `≥ 3`. -/
noncomputable def LTree.internalCount {n : ℕ} (T : LTree n) : ℕ :=
  Fintype.card {v : Fin T.m // 3 ≤ T.G.degree v}

/-- Numerator of the exact law: `(α-1)^{#internal} ∏_v ∏_{j=2}^{deg v - 2} (j - α)`. -/
noncomputable def LTree.lawWeight {n : ℕ} (α : ℝ) (T : LTree n) : ℝ :=
  (α - 1) ^ T.internalCount *
    ∏ v : {v : Fin T.m // 3 ≤ T.G.degree v},
      ∏ j ∈ Finset.Icc 2 (T.G.degree v.val - 2), ((j : ℝ) - α)

/-- The weight is invariant under labelled isomorphism. -/
theorem LTree.lawWeight_congr {n : ℕ} (α : ℝ) {T T' : LTree n} (h : T ≈ T') :
    T.lawWeight α = T'.lawWeight α := sorry

/-- Numerator of the exact law on states. -/
noncomputable def State.lawWeight {n : ℕ} (α : ℝ) : State n → ℝ :=
  Quotient.lift (LTree.lawWeight α) fun _ _ h => LTree.lawWeight_congr α h

/-- Exact finite-tree law of the Marchal chain (flag: derived by the unique-history argument;
check against Curien–Haas §1.3 / Marchal before use). Step `n = k+1`; denominator
the denominator `∏_{j=1}^{k} (j α - 1)` is written as `∏_{j<k} ((j+1) α - 1)`. -/
theorem law_apply {α : ℝ} (hα : 1 < α) (hα2 : α ≤ 2) (k : ℕ) (s : State (k + 1)) :
    law hα hα2 k s =
      ENNReal.ofReal (s.lawWeight α / ∏ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) * α - 1)) :=
  sorry

/-- A state is binary if every vertex has degree one or three. -/
def State.IsBinary {n : ℕ} : State n → Prop :=
  Quotient.lift (fun T : LTree n => ∀ v, T.G.degree v = 1 ∨ T.G.degree v = 3)
    fun _ _ h => by
      obtain ⟨⟨e, _⟩⟩ := h
      sorry -- `e` preserves degrees

/-- At `α = 2`, on a binary tree every internal vertex has weight zero
(`d - 1 - α = 0`): only edges are selected. -/
theorem selectionWeight_two_binary {n : ℕ} (T : LTree n)
    (hb : ∀ v, T.G.degree v = 1 ∨ T.G.degree v = 3) (p : T.G.edgeSet ⊕ {v // 3 ≤ T.G.degree v}) :
    selectionWeight T.G 2 p = match p with | .inl _ => 1 | .inr _ => 0 := by
  cases p with
  | inl e => simp [selectionWeight]; norm_num
  | inr v =>
    have := (hb v.val).resolve_left (by have := v.property; omega)
    simp [selectionWeight, this]; norm_num

/-- `α = 2` support: only binary states have positive mass (all steps from `A_0 — A_1`). -/
theorem law_two_support_binary (k : ℕ) :
    (law (α := 2) (by norm_num) le_rfl k).support ⊆ {s | s.IsBinary} := sorry

/-- `α = 2`: Rémy's law — uniform on binary states, mass `1/(2n-3)!!` with `n = k+1`. -/
theorem law_two_binary_apply (k : ℕ) (s : State (k + 1)) (hs : s.IsBinary) :
    law (α := 2) (by norm_num) le_rfl k s = ((2 * (k + 1) - 3).doubleFactorial : ℝ≥0∞)⁻¹ :=
  sorry

/-- There are `(2n-3)!!` binary leaf-labelled trees with leaves `A_0..A_n`, `n = k+1`
(with `(-1)!! = 1` read as `0‼ = 1`; checked at `n = 1,2,3`: `1, 1, 3`). -/
theorem ncard_binary_states (k : ℕ) :
    {s : State (k + 1) | s.IsBinary}.ncard = (2 * (k + 1) - 3).doubleFactorial := sorry

/-- `α = 2` step is Rémy's step: from a binary state, graft at a uniformly chosen one of the
`2k+1` edges (no plane order is involved: states are non-plane). -/
theorem step_two_binary (k : ℕ) (T : LTree (k + 1)) (hb : ∀ v, T.G.degree v = 1 ∨ T.G.degree v = 3)
    (t : State (k + 2)) :
    step (α := 2) (by norm_num) le_rfl k ⟦T⟧ t =
      ({e : T.G.edgeSet | ⟦graft T (.inl e)⟧ = t}.ncard : ℝ≥0∞) / ((2 * k + 1 : ℕ) : ℝ≥0∞) :=
  sorry

end BGW.StableTrees.Marchal
