import Lax119563Proofs.HomTensors.BagTree
import Lax119563.ColoredHomomorphisms

/-!
# Labeled graphs and their homomorphism tensors

A `k`-labeled graph `LGraph k` has a finite vertex type, an arbitrary edge relation (loops and
both orientations allowed; repeated edges are irrelevant for homomorphism counts), unary color
predicates, an *equality relation* `eqv`, and `k` labels. A homomorphism into a colored graph
must map edges to edges, respect the color predicates, and identify `eqv`-related vertices.
The equality relation replaces the identification of vertices by quotients during gluing; the
quotient is taken once, at the very end.

Goodness `Good F N` records a valid rooted bag tree of width `k` whose root bag contains all
labels, and that up to `eqv` the graph has at most `N` vertices besides the labels.

The basic construction is `glue`: a fresh set `L` of vertices together with a family of labeled
graphs, the labels of the `j`-th of which are identified with `σ j : Fin k → L`.
-/

namespace Lax119563Proofs.HomTensors

open Lax119563.ColoredGraphs Relation

/-- A `k`-labeled graph with edge relation, color predicates and equality constraints. -/
structure LGraph (k : ℕ) where
  /-- The vertices. -/
  V : Type
  [fin : Fintype V]
  /-- The edge relation. -/
  adj : V → V → Prop
  /-- Color predicates: `pred a c` requires vertex `a` to have color `c`. -/
  pred : V → ℕ → Prop
  /-- Equality constraints. -/
  eqv : V → V → Prop
  /-- The labels. -/
  lab : Fin k → V

attribute [instance] LGraph.fin

namespace LGraph

variable {k : ℕ}

/-- `h` is a homomorphism from `F` to the colored graph `G`. -/
def IsHom (F : LGraph k) (G : ColoredGraph) (h : F.V → Fin G.n) : Prop :=
  (∀ a b, F.adj a b → G.graph.Adj (h a) (h b)) ∧ (∀ a c, F.pred a c → G.color (h a) = c) ∧
    (∀ a b, F.eqv a b → h a = h b)

/-- The homomorphism tensor: the number of homomorphisms mapping the labels to `v`. -/
noncomputable def tensor (F : LGraph k) (G : ColoredGraph) (v : Fin k → Fin G.n) : ℕ :=
  Nat.card {h : F.V → Fin G.n // F.IsHom G h ∧ h ∘ F.lab = v}

/-- The number of homomorphisms. -/
noncomputable def homCount (F : LGraph k) (G : ColoredGraph) : ℕ :=
  Nat.card {h : F.V → Fin G.n // F.IsHom G h}

lemma sum_tensor (F : LGraph k) (G : ColoredGraph) : ∑ v, F.tensor G v = F.homCount G := by
  classical
  unfold tensor homCount
  rw [← Nat.card_sigma]
  refine Nat.card_congr ?_
  exact
    { toFun := fun p => ⟨p.2.1, p.2.2.1⟩
      invFun := fun h => ⟨h.1 ∘ F.lab, h.1, h.2, rfl⟩
      left_inv := by
        rintro ⟨v, h, hh, rfl⟩
        rfl
      right_inv := fun h => rfl }

/-- Bag-tree data for a labeled graph. -/
structure Decomp (F : LGraph k) where
  /-- The bag tree. -/
  T : BagTree F.V
  valid : T.Valid F.adj F.eqv
  width : ∀ t, (T.bag t).card ≤ k + 1
  root_lab : ∀ i, F.lab i ∈ T.bag T.root

/-- Up to `eqv`, `F` has at most `N` vertices besides its labels. -/
def Small (F : LGraph k) (N : ℕ) : Prop :=
  ∃ (W : Type) (g : W → F.V), Finite W ∧ Nat.card W ≤ N ∧
    ∀ a, (∃ i, EqvGen F.eqv a (F.lab i)) ∨ ∃ w, EqvGen F.eqv a (g w)

/-- Good labeled graphs: a bag tree of width `k` with all labels in the root bag, and at most
`N` vertices besides the labels. -/
def Good (F : LGraph k) (N : ℕ) : Prop :=
  Nonempty F.Decomp ∧ F.Small N

lemma Small.mono {F : LGraph k} {N N' : ℕ} (h : F.Small N) (hN : N ≤ N') : F.Small N' := by
  obtain ⟨W, g, hW, hc, hg⟩ := h
  exact ⟨W, g, hW, hc.trans hN, hg⟩

lemma Good.mono {F : LGraph k} {N N' : ℕ} (h : F.Good N) (hN : N ≤ N') : F.Good N' :=
  ⟨h.1, h.2.mono hN⟩

/-! ### Atoms -/

/-- A labeled graph whose vertices are exactly its `k` (distinct) labels. -/
def atom (adj : Fin k → Fin k → Prop) (pred : Fin k → ℕ → Prop) (eqv : Fin k → Fin k → Prop) :
    LGraph k where
  V := Fin k
  adj := adj
  pred := pred
  eqv := eqv
  lab := id

open scoped Classical in
lemma tensor_atom (adj : Fin k → Fin k → Prop) (pred : Fin k → ℕ → Prop)
    (eqv : Fin k → Fin k → Prop) (G : ColoredGraph) (v : Fin k → Fin G.n) :
    (atom adj pred eqv).tensor G v = if (atom adj pred eqv).IsHom G v then 1 else 0 := by
  classical
  unfold tensor
  split_ifs with h
  · rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨v, h, rfl⟩, ?_⟩
    rintro ⟨w, hw, rfl⟩
    rfl
  · rw [Nat.card_eq_zero]
    left
    refine ⟨fun ⟨w, hw, hwv⟩ => h ?_⟩
    subst hwv
    exact hw

lemma good_atom (adj : Fin k → Fin k → Prop) (pred : Fin k → ℕ → Prop)
    (eqv : Fin k → Fin k → Prop) : (atom adj pred eqv).Good 0 := by
  classical
  let T : BagTree (atom adj pred eqv).V :=
    { I := Unit
      root := ()
      parent := id
      depth := fun _ => 0
      depth_lt := fun t ht => absurd rfl ht
      bag := fun _ => Finset.univ }
  refine ⟨⟨{
      T := T
      valid := ?_
      width := ?_
      root_lab := ?_ }⟩, ?_⟩
  · refine ⟨fun a => ⟨(), Finset.mem_univ _⟩, fun a b _ => ⟨(), Finset.mem_univ _,
      Finset.mem_univ _⟩, fun a b _ => ⟨(), (), Finset.mem_univ _, Finset.mem_univ _,
      Or.inl rfl⟩, fun a t s _ _ => rfl⟩
  · intro t
    show (Finset.univ : Finset (Fin k)).card ≤ k + 1
    simp
  · intro i
    exact Finset.mem_univ _
  · exact ⟨Empty, Empty.elim, inferInstance, by simp, fun a => Or.inl ⟨a, EqvGen.refl _⟩⟩

/-! ### Gluing -/

section Glue

variable (L : Type) [Fintype L] (lam : Fin k → L) (J : Type) [Fintype J] (F : J → LGraph k)
  (σ : J → Fin k → L)

/-- Glue the graphs `F j` onto a fresh vertex set `L`, identifying the `i`-th label of `F j`
with `σ j i`; the new labels are `lam`. -/
def glue : LGraph k where
  V := L ⊕ Σ j, (F j).V
  adj a b := ∃ j x y, (F j).adj x y ∧ a = .inr ⟨j, x⟩ ∧ b = .inr ⟨j, y⟩
  pred a c := ∃ j x, (F j).pred x c ∧ a = .inr ⟨j, x⟩
  eqv a b := (∃ j x y, (F j).eqv x y ∧ a = .inr ⟨j, x⟩ ∧ b = .inr ⟨j, y⟩) ∨
    ∃ j i, a = .inr ⟨j, (F j).lab i⟩ ∧ b = .inl (σ j i)
  lab i := .inl (lam i)

/-- Homomorphisms from a glued graph split into a map on `L` and homomorphisms of the parts. -/
def glueHomEquiv (G : ColoredGraph) (v : Fin k → Fin G.n) :
    {h : (glue L lam J F σ).V → Fin G.n // (glue L lam J F σ).IsHom G h ∧
        h ∘ (glue L lam J F σ).lab = v} ≃
      Σ g : {g : L → Fin G.n // g ∘ lam = v},
        ∀ j, {h : (F j).V → Fin G.n // (F j).IsHom G h ∧ h ∘ (F j).lab = g.1 ∘ σ j} where
  toFun h := ⟨⟨fun l => h.1 (.inl l), h.2.2⟩, fun j => ⟨fun x => h.1 (.inr ⟨j, x⟩),
    ⟨fun x y hxy => h.2.1.1 _ _ ⟨j, x, y, hxy, rfl, rfl⟩,
      fun x c hx => h.2.1.2.1 _ _ ⟨j, x, hx, rfl⟩,
      fun x y hxy => h.2.1.2.2 _ _ (Or.inl ⟨j, x, y, hxy, rfl, rfl⟩)⟩,
    funext fun i => h.2.1.2.2 _ _ (Or.inr ⟨j, i, rfl, rfl⟩)⟩⟩
  invFun p := ⟨Sum.elim p.1.1 (fun q => (p.2 q.1).1 q.2),
    ⟨by
      rintro _ _ ⟨j, x, y, hxy, rfl, rfl⟩
      exact (p.2 j).2.1.1 x y hxy,
    by
      rintro _ c ⟨j, x, hx, rfl⟩
      exact (p.2 j).2.1.2.1 x c hx,
    by
      rintro _ _ (⟨j, x, y, hxy, rfl, rfl⟩ | ⟨j, i, rfl, rfl⟩)
      · exact (p.2 j).2.1.2.2 x y hxy
      · exact congrFun (p.2 j).2.2 i⟩,
    p.1.2⟩
  left_inv h := by
    apply Subtype.ext
    funext a
    rcases a with l | ⟨j, x⟩ <;> rfl
  right_inv p := rfl

lemma tensor_glue [DecidableEq L] (G : ColoredGraph) (v : Fin k → Fin G.n) :
    (glue L lam J F σ).tensor G v =
      ∑ g : L → Fin G.n, if g ∘ lam = v then ∏ j, (F j).tensor G (g ∘ σ j) else 0 := by
  classical
  unfold tensor
  rw [Nat.card_congr (glueHomEquiv L lam J F σ G v), Nat.card_sigma]
  simp_rw [Nat.card_pi]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (fun g => by simp)
    (fun g => ∏ j, Nat.card {h // (F j).IsHom G h ∧ h ∘ (F j).lab = g ∘ σ j})).symm

lemma liftEqvGen (j : J) {x y : (F j).V} (h : EqvGen (F j).eqv x y) :
    EqvGen (glue L lam J F σ).eqv (.inr ⟨j, x⟩) (.inr ⟨j, y⟩) := by
  induction h with
  | rel x y h => exact EqvGen.rel _ _ (Or.inl ⟨j, x, y, h, rfl, rfl⟩)
  | refl => exact EqvGen.refl _
  | symm _ _ _ ih => exact EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact EqvGen.trans _ _ _ ih1 ih2

lemma small_glue (N : J → ℕ) (hF : ∀ j, (F j).Small (N j)) :
    (glue L lam J F σ).Small (Nat.card {l : L // l ∉ Set.range lam} + ∑ j, N j) := by
  classical
  choose W g hW hc hg using hF
  let gg : {l : L // l ∉ Set.range lam} ⊕ (Σ j, W j) → (glue L lam J F σ).V :=
    Sum.elim (fun l => Sum.inl l.1) (fun p => Sum.inr ⟨p.1, g p.1 p.2⟩)
  refine ⟨{l : L // l ∉ Set.range lam} ⊕ Σ j, W j, gg, inferInstance, ?_, ?_⟩
  · rw [Nat.card_sum, Nat.card_sigma]
    exact Nat.add_le_add_left (Finset.sum_le_sum fun j _ => hc j) _
  · -- vertices of `L`
    have hL : ∀ l : L, (∃ i, EqvGen (glue L lam J F σ).eqv (.inl l) (.inl (lam i))) ∨
        ∃ w, EqvGen (glue L lam J F σ).eqv (.inl l) (gg w) := by
      intro l
      by_cases hl : l ∈ Set.range lam
      · obtain ⟨i, rfl⟩ := hl
        exact Or.inl ⟨i, EqvGen.refl _⟩
      · exact Or.inr ⟨.inl ⟨l, hl⟩, EqvGen.refl _⟩
    rintro (l | ⟨j, x⟩)
    · exact hL l
    · rcases hg j x with ⟨i, hi⟩ | ⟨w, hw⟩
      · have h1 := liftEqvGen L lam J F σ j hi
        have h2 : EqvGen (glue L lam J F σ).eqv (.inr ⟨j, (F j).lab i⟩) (.inl (σ j i)) :=
          EqvGen.rel _ _ (Or.inr ⟨j, i, rfl, rfl⟩)
        rcases hL (σ j i) with ⟨i', h3⟩ | ⟨w, h3⟩
        · exact Or.inl ⟨i', (h1.trans _ _ _ h2).trans _ _ _ h3⟩
        · exact Or.inr ⟨w, (h1.trans _ _ _ h2).trans _ _ _ h3⟩
      · exact Or.inr ⟨.inr ⟨j, w⟩, liftEqvGen L lam J F σ j hw⟩

/-- The embedding of the `j`-th part into a glued graph. -/
def inrEmb (j : J) : (F j).V ↪ (glue L lam J F σ).V :=
  ⟨fun x => Sum.inr ⟨j, x⟩, fun x y h => by
    have h' := Sum.inr_injective h
    exact eq_of_heq (Sigma.mk.inj_iff.1 h').2⟩

/-- The embedding of the fresh vertices into a glued graph. -/
def inlEmb : L ↪ (glue L lam J F σ).V := ⟨Sum.inl, Sum.inl_injective⟩

open scoped Classical in
/-- The bag tree of a glued graph: a root bag `L` with the trees of the parts below. -/
noncomputable def glueTree (D : ∀ j, (F j).Decomp) : BagTree (glue L lam J F σ).V where
  I := Option (Σ j, (D j).T.I)
  root := none
  parent t := t.elim none fun p =>
    if p.2 = (D p.1).T.root then none else some ⟨p.1, (D p.1).T.parent p.2⟩
  depth t := t.elim 0 fun p => (D p.1).T.depth p.2 + 1
  depth_lt := by
    rintro (_ | ⟨j, t⟩) ht
    · exact absurd rfl ht
    · simp only [Option.elim_some]
      split_ifs with h
      · simp
      · simpa using (D j).T.depth_lt t h
  bag t := t.elim (Finset.univ.map (inlEmb L lam J F σ)) fun p =>
    ((D p.1).T.bag p.2).map (inrEmb L lam J F σ p.1)

variable {L lam J F σ}

lemma glueTree_root (D : ∀ j, (F j).Decomp) : (glueTree L lam J F σ D).root = none := rfl

open scoped Classical in
lemma glueTree_parent_some (D : ∀ j, (F j).Decomp) (j : J) (t : (D j).T.I) :
    (glueTree L lam J F σ D).parent (some ⟨j, t⟩) =
      if t = (D j).T.root then none else some ⟨j, (D j).T.parent t⟩ := rfl

lemma glueTree_bag_none (D : ∀ j, (F j).Decomp) :
    (glueTree L lam J F σ D).bag none = Finset.univ.map (inlEmb L lam J F σ) := rfl

lemma glueTree_bag_some (D : ∀ j, (F j).Decomp) (p : Σ j, (D j).T.I) :
    (glueTree L lam J F σ D).bag (some p) = ((D p.1).T.bag p.2).map (inrEmb L lam J F σ p.1) :=
  rfl

lemma mem_glueTree_none (D : ∀ j, (F j).Decomp) (a : (glue L lam J F σ).V) :
    a ∈ (glueTree L lam J F σ D).bag none ↔ ∃ l, a = .inl l := by
  rw [glueTree_bag_none, Finset.mem_map]
  constructor
  · rintro ⟨l, -, h⟩
    exact ⟨l, h.symm⟩
  · rintro ⟨l, h⟩
    exact ⟨l, Finset.mem_univ _, h.symm⟩

lemma inr_mem_glueTree_some (D : ∀ j, (F j).Decomp) (j j' : J) (x : (F j).V)
    (t : (D j').T.I) :
    inrEmb L lam J F σ j x ∈ (glueTree L lam J F σ D).bag (some ⟨j', t⟩) ↔
      ∃ h : j' = j, x ∈ (D j).T.bag (h ▸ t) := by
  rw [glueTree_bag_some, Finset.mem_map]
  constructor
  · rintro ⟨y, hy, h⟩
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 (Sum.inr_injective h)
    cases h
    exact ⟨rfl, hy⟩
  · rintro ⟨rfl, h⟩
    exact ⟨x, h, rfl⟩

lemma inl_not_mem_glueTree_some (D : ∀ j, (F j).Decomp) (l : L) (p : Σ j, (D j).T.I) :
    inlEmb L lam J F σ l ∉ (glueTree L lam J F σ D).bag (some p) := by
  rw [glueTree_bag_some, Finset.mem_map]
  rintro ⟨y, -, h⟩
  cases h

lemma mem_glueTree_some (D : ∀ j, (F j).Decomp) (j : J) (x : (F j).V) (t : (D j).T.I) :
    inrEmb L lam J F σ j x ∈ (glueTree L lam J F σ D).bag (some ⟨j, t⟩) ↔
      x ∈ (D j).T.bag t := by
  rw [inr_mem_glueTree_some]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨rfl, h⟩⟩

lemma isTop_glueTree (D : ∀ j, (F j).Decomp) (j : J) (x : (F j).V) (t : (D j).T.I) :
    (glueTree L lam J F σ D).IsTop (inrEmb L lam J F σ j x) (some ⟨j, t⟩) ↔
      (D j).T.IsTop x t := by
  classical
  unfold BagTree.IsTop
  rw [glueTree_parent_some, mem_glueTree_some D j x t, glueTree_root]
  by_cases ht : t = (D j).T.root
  · have hn : inrEmb L lam J F σ j x ∉ (glueTree L lam J F σ D).bag none := by
      rw [mem_glueTree_none]
      rintro ⟨l, hl⟩
      have e : inrEmb L lam J F σ j x = Sum.inr ⟨j, x⟩ := rfl
      rw [e] at hl
      cases hl
    simp only [ht, if_true, hn, not_false_eq_true, or_true, true_or]
  · simp only [ht, if_false, reduceCtorEq, false_or, mem_glueTree_some]

/-- The decomposition of a glued graph. -/
noncomputable def glueDecomp (D : ∀ j, (F j).Decomp) (hL : Fintype.card L ≤ k + 1) :
    (glue L lam J F σ).Decomp where
  T := glueTree L lam J F σ D
  valid := by
    classical
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro (l | ⟨j, x⟩)
      · exact ⟨none, (mem_glueTree_none D _).2 ⟨l, rfl⟩⟩
      · obtain ⟨t, ht⟩ := (D j).valid.cover x
        exact ⟨some ⟨j, t⟩, (mem_glueTree_some D j x t).2 ht⟩
    · rintro _ _ ⟨j, x, y, hxy, rfl, rfl⟩
      obtain ⟨t, hx, hy⟩ := (D j).valid.edge x y hxy
      exact ⟨some ⟨j, t⟩, (mem_glueTree_some D j x t).2 hx, (mem_glueTree_some D j y t).2 hy⟩
    · rintro _ _ (⟨j, x, y, hxy, rfl, rfl⟩ | ⟨j, i, rfl, rfl⟩)
      · obtain ⟨t, s, hx, hy, h⟩ := (D j).valid.eqv x y hxy
        refine ⟨some ⟨j, t⟩, some ⟨j, s⟩, (mem_glueTree_some D j x t).2 hx,
          (mem_glueTree_some D j y s).2 hy, ?_⟩
        rcases h with rfl | ⟨hne, rfl⟩
        · exact Or.inl rfl
        · refine Or.inr ⟨by rw [glueTree_root]; exact Option.some_ne_none _, ?_⟩
          rw [glueTree_parent_some, if_neg hne]
      · refine ⟨some ⟨j, (D j).T.root⟩, none, (mem_glueTree_some D j _ _).2 ((D j).root_lab i),
          (mem_glueTree_none D _).2 ⟨_, rfl⟩, Or.inr ⟨by rw [glueTree_root]; exact Option.some_ne_none _, ?_⟩⟩
        rw [glueTree_parent_some, if_pos rfl]
    · rintro (l | ⟨j, x⟩) t s ht hs
      · have key : ∀ u, (glueTree L lam J F σ D).IsTop (.inl l) u → u = none := by
          rintro (_ | p) ⟨hu, -⟩
          · rfl
          · exact absurd hu (inl_not_mem_glueTree_some D l p)
        rw [key t ht, key s hs]
      · have key : ∀ u, (glueTree L lam J F σ D).IsTop (.inr ⟨j, x⟩) u →
            ∃ t', u = some ⟨j, t'⟩ ∧ (D j).T.IsTop x t' := by
          rintro (_ | ⟨j', u⟩) hu
          · obtain ⟨l, hl⟩ := (mem_glueTree_none D _).1 hu.1
            cases hl
          · obtain ⟨h, -⟩ := (inr_mem_glueTree_some D j j' x u).1 hu.1
            subst j'
            exact ⟨u, rfl, (isTop_glueTree D j x u).1 hu⟩
        obtain ⟨t', rfl, ht'⟩ := key t ht
        obtain ⟨s', rfl, hs'⟩ := key s hs
        rw [(D j).valid.top x t' s' ht' hs']
  width := by
    rintro (_ | ⟨j, t⟩)
    · rw [glueTree_bag_none, Finset.card_map, Finset.card_univ]
      exact hL
    · rw [glueTree_bag_some, Finset.card_map]
      exact (D j).width t
  root_lab i := (mem_glueTree_none D _).2 ⟨_, rfl⟩

lemma good_glue (N : J → ℕ) (hF : ∀ j, (F j).Good (N j)) (hL : Fintype.card L ≤ k + 1) :
    (glue L lam J F σ).Good (Nat.card {l : L // l ∉ Set.range lam} + ∑ j, N j) :=
  ⟨⟨glueDecomp (fun j => (hF j).1.some) hL⟩, small_glue L lam J F σ N fun j => (hF j).2⟩

end Glue

end LGraph

end Lax119563Proofs.HomTensors
