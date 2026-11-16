import Mathlib
import Lax228581.Treewidth

/-!
# Rooted bag trees

A `BagTree V` is a finite rooted tree, given by parent pointers that strictly decrease a depth
function, with a bag of vertices of `V` at every node. Such trees are easy to combine (a new root
with several subtrees below it), and every bag tree satisfying the conditions of `BagTree.Valid`
yields a tree decomposition (in the sense of `Lax228581.Treewidth`) of every graph obtained by
identifying vertices along an "equality" relation whose pairs sit in equal or adjacent bags.
-/

namespace Lax119563Proofs.HomTensors

open Lax228581.Treewidth Relation

/-- A finite rooted tree with parent pointers decreasing a depth, with bags of vertices. -/
structure BagTree (V : Type) where
  /-- The nodes. -/
  I : Type
  [fin : Fintype I]
  /-- The root. -/
  root : I
  /-- The parent of a node (arbitrary at the root). -/
  parent : I → I
  /-- The depth, strictly decreasing towards the root. -/
  depth : I → ℕ
  depth_lt : ∀ t, t ≠ root → depth (parent t) < depth t
  /-- The bag at a node. -/
  bag : I → Finset V

attribute [instance] BagTree.fin

namespace BagTree

variable {V : Type} (T : BagTree V)

/-- `t` is the topmost node whose bag contains `a`: its bag contains `a` and either it is the
root or its parent's bag does not contain `a`. -/
def IsTop (a : V) (t : T.I) : Prop :=
  a ∈ T.bag t ∧ (t = T.root ∨ a ∉ T.bag (T.parent t))

lemma parent_ne {t : T.I} (ht : t ≠ T.root) : T.parent t ≠ t := fun h => by
  have := T.depth_lt t ht
  rw [h] at this
  exact lt_irrefl _ this

/-- The tree: every non-root node is adjacent to its parent. -/
def graph : SimpleGraph T.I where
  Adj s t := (s ≠ T.root ∧ T.parent s = t) ∨ (t ≠ T.root ∧ T.parent t = s)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun s h => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact T.parent_ne h1 h2⟩

lemma graph_adj_parent {t : T.I} (ht : t ≠ T.root) : T.graph.Adj t (T.parent t) :=
  Or.inl ⟨ht, rfl⟩

lemma reachable_root (t : T.I) : T.graph.Reachable t T.root := by
  induction h : T.depth t using Nat.strong_induction_on generalizing t with
  | _ n ih =>
    by_cases ht : t = T.root
    · subst ht; rfl
    · exact (T.graph_adj_parent ht).reachable.trans (ih _ (h ▸ T.depth_lt t ht) _ rfl)

lemma connected : T.graph.Connected :=
  (SimpleGraph.connected_iff_exists_forall_reachable _).2
    ⟨T.root, fun w => (T.reachable_root w).symm⟩

lemma isTree : T.graph.IsTree := by
  classical
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨T.connected, ?_⟩
  let f : {t : T.I // t ≠ T.root} → T.graph.edgeSet := fun t =>
    ⟨s(t.1, T.parent t.1), T.graph_adj_parent t.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨t, ht⟩ ⟨t', ht'⟩ h
      have h := congrArg Subtype.val h
      simp only [f] at h
      rw [Sym2.eq_iff] at h
      rcases h with ⟨h, -⟩ | ⟨h1, h2⟩
      · exact Subtype.ext h
      · exfalso
        have a := T.depth_lt t ht
        have b := T.depth_lt t' ht'
        rw [h2] at a; rw [← h1] at b
        omega
    · rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | _ x y =>
        rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨⟨x, h1⟩, by simp [f, h2]⟩
        · exact ⟨⟨y, h1⟩, by simp [f, h2, Sym2.eq_swap]⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have := Fintype.card_subtype_compl (fun t : T.I => t = T.root)
  simp only [Fintype.card_unique] at this
  have hpos : 0 < Fintype.card T.I := Fintype.card_pos_iff.2 ⟨T.root⟩
  rw [this]
  omega

/-- Validity of a bag tree for a vertex set with an edge relation `adj` and an equality
relation `eqv`. -/
structure Valid (adj eqv : V → V → Prop) : Prop where
  cover : ∀ a, ∃ t, a ∈ T.bag t
  edge : ∀ a b, adj a b → ∃ t, a ∈ T.bag t ∧ b ∈ T.bag t
  eqv : ∀ a b, eqv a b → ∃ t s, a ∈ T.bag t ∧ b ∈ T.bag s ∧
    (s = t ∨ (t ≠ T.root ∧ s = T.parent t))
  top : ∀ a t s, T.IsTop a t → T.IsTop a s → t = s

section Reach

variable (S : Set T.I)

/-- Reachability inside the subtree induced by `S`, as a relation on nodes. -/
def Reach (t s : T.I) : Prop :=
  ∃ (ht : t ∈ S) (hs : s ∈ S), (T.graph.induce S).Reachable ⟨t, ht⟩ ⟨s, hs⟩

variable {T S}

lemma Reach.refl {t : T.I} (ht : t ∈ S) : T.Reach S t t := ⟨ht, ht, by rfl⟩

lemma Reach.symm {t s : T.I} (h : T.Reach S t s) : T.Reach S s t := by
  obtain ⟨ht, hs, h⟩ := h
  exact ⟨hs, ht, h.symm⟩

lemma Reach.trans {t s u : T.I} (h₁ : T.Reach S t s) (h₂ : T.Reach S s u) : T.Reach S t u := by
  obtain ⟨ht, hs, h₁⟩ := h₁
  obtain ⟨_, hu, h₂⟩ := h₂
  exact ⟨ht, hu, h₁.trans h₂⟩

lemma Reach.parent {t : T.I} (ht : t ≠ T.root) (h₁ : t ∈ S) (h₂ : T.parent t ∈ S) :
    T.Reach S t (T.parent t) :=
  ⟨h₁, h₂, SimpleGraph.Adj.reachable (G := T.graph.induce S) (T.graph_adj_parent ht)⟩

lemma reach_top {a : V} (hS : ∀ t, a ∈ T.bag t → t ∈ S) (t : T.I) (ha : a ∈ T.bag t) :
    ∃ s, T.IsTop a s ∧ T.Reach S t s := by
  induction h : T.depth t using Nat.strong_induction_on generalizing t with
  | _ n ih =>
    by_cases htop : t = T.root ∨ a ∉ T.bag (T.parent t)
    · exact ⟨t, ⟨ha, htop⟩, Reach.refl (hS t ha)⟩
    · push Not at htop
      obtain ⟨s, hs, hr⟩ := ih _ (h ▸ T.depth_lt t htop.1) _ htop.2 rfl
      exact ⟨s, hs, (Reach.parent htop.1 (hS t ha) (hS _ htop.2)).trans hr⟩

lemma reach_of_mem {adj eqv : V → V → Prop} (hT : T.Valid adj eqv) {a : V}
    (hS : ∀ t, a ∈ T.bag t → t ∈ S) {t s : T.I} (ht : a ∈ T.bag t) (hs : a ∈ T.bag s) :
    T.Reach S t s := by
  obtain ⟨t', ht', h1⟩ := reach_top hS t ht
  obtain ⟨s', hs', h2⟩ := reach_top hS s hs
  rw [hT.top a t' s' ht' hs'] at h1
  exact h1.trans h2.symm

end Reach

/-- A valid bag tree yields a tree decomposition of any graph `S` on a quotient `W` of `V`
whose kernel is generated by `eqv` and whose edges come from `adj`. -/
theorem hasTreewidthAtMost {adj eqv : V → V → Prop} (hT : T.Valid adj eqv)
    {W : Type} (S : SimpleGraph W) (π : V → W) (hπ : Function.Surjective π)
    (hker : ∀ a b, π a = π b → EqvGen eqv a b) (hcompat : ∀ a b, eqv a b → π a = π b)
    (hS : ∀ x y, S.Adj x y → ∃ a b, π a = x ∧ π b = y ∧ (adj a b ∨ adj b a))
    (w : ℕ) (hw : ∀ t, (T.bag t).card ≤ w + 1) : HasTreewidthAtMost S w := by
  classical
  have hcompat' : ∀ a b, EqvGen eqv a b → π a = π b := by
    intro a b h
    induction h with
    | rel x y h => exact hcompat x y h
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  refine ⟨{
      Node := T.I
      tree := T.graph
      isTree := T.isTree
      bag := fun t => (T.bag t).image π
      vertex_mem_bag := ?_
      edge_mem_bag := ?_
      bag_indices_connected := ?_ }, ?_⟩
  · intro x
    obtain ⟨a, rfl⟩ := hπ x
    obtain ⟨t, ht⟩ := hT.cover a
    exact ⟨t, Finset.mem_image_of_mem _ ht⟩
  · intro x y hxy
    obtain ⟨a, b, rfl, rfl, hab⟩ := hS x y hxy
    rcases hab with hab | hab
    · obtain ⟨t, ha, hb⟩ := hT.edge a b hab
      exact ⟨t, Finset.mem_image_of_mem _ ha, Finset.mem_image_of_mem _ hb⟩
    · obtain ⟨t, hb, ha⟩ := hT.edge b a hab
      exact ⟨t, Finset.mem_image_of_mem _ ha, Finset.mem_image_of_mem _ hb⟩
  · intro x
    set S' : Set T.I := {i | x ∈ (T.bag i).image π}
    obtain ⟨a₀, rfl⟩ := hπ x
    obtain ⟨t₀, ht₀⟩ := hT.cover a₀
    have memS : ∀ {a t}, π a = π a₀ → a ∈ T.bag t → t ∈ S' := fun ha ht =>
      Finset.mem_image.2 ⟨_, ht, ha⟩
    -- all bags of `π`-equivalent vertices are mutually reachable inside `S'`
    have key : ∀ a b, EqvGen eqv a b → π a = π a₀ →
        ∀ t s, a ∈ T.bag t → b ∈ T.bag s → T.Reach S' t s := by
      intro a b h
      induction h with
      | rel a b hab =>
        intro ha t s hat hbs
        have hb : π b = π a₀ := (hcompat a b hab).symm.trans ha
        obtain ⟨t', s', hat', hbs', h⟩ := hT.eqv a b hab
        have r1 := reach_of_mem hT (fun u hu => memS ha hu) hat hat'
        have r3 := reach_of_mem hT (fun u hu => memS hb hu) hbs' hbs
        have r2 : T.Reach S' t' s' := by
          rcases h with rfl | ⟨hne, rfl⟩
          · exact Reach.refl (memS ha hat')
          · exact Reach.parent hne (memS ha hat') (memS hb hbs')
        exact r1.trans (r2.trans r3)
      | refl a =>
        intro ha t s hat has
        exact reach_of_mem hT (fun u hu => memS ha hu) hat has
      | symm a b hab ih =>
        intro hb t s hbt has
        have ha : π a = π a₀ := (hcompat' a b hab).trans hb
        exact (ih ha s t has hbt).symm
      | trans a b c hab hbc ih1 ih2 =>
        intro ha t s hat hcs
        have hb : π b = π a₀ := (hcompat' a b hab).symm.trans ha
        obtain ⟨u, hu⟩ := hT.cover b
        exact (ih1 ha t u hat hu).trans (ih2 hb u s hu hcs)
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨t₀, memS rfl ht₀⟩, ?_⟩
    rintro ⟨s, hs⟩
    obtain ⟨b, hbs, hb⟩ := Finset.mem_image.1 hs
    obtain ⟨_, _, h⟩ := key a₀ b (hker _ _ hb.symm) rfl t₀ s ht₀ hbs
    exact h
  · intro t
    exact (Finset.card_image_le).trans (hw t)

end BagTree

end Lax119563Proofs.HomTensors
