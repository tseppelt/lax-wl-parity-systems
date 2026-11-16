import Mathlib
import Lax228581.Treewidth

/-!
# One-vertex tree decompositions (Abramsky–Jakl–Paine, Theorem 3.4)

Every graph of treewidth at most `k` has a tree decomposition of width at most `k`, rooted at a
node with empty bag, in which every other node introduces exactly one vertex. Identifying each
non-root node with the vertex it introduces turns the decomposition tree into a rooted forest on
the vertices; we record it as `OneVertexForest`.

The proof roots the decomposition tree at some node `r`. Each vertex `v` gets its topmost node
`top v` (the node of least depth whose bag contains `v`), which is an ancestor of every node whose
bag contains `v`. Ordering vertices by the depth of their topmost node, the bag of `v` is the part
of the bag of `top v` that comes no later than `v`, and the parent of `v` is the latest other
vertex of that bag.
-/

open Lax228581.Treewidth SimpleGraph

namespace Lax119563Proofs.RowSpace

/-- A one-vertex tree decomposition of width at most `k`, as a rooted forest on the vertices:
`bag p` is the bag of the node introducing `p`, and `(bag p).erase p` is contained in the bag of
the parent (and empty at roots). -/
structure OneVertexForest {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) where
  /-- The parent of a vertex in the forest (`none` at roots). -/
  parent : Fin n → Option (Fin n)
  /-- A depth function witnessing that `parent` is acyclic. -/
  depth : Fin n → ℕ
  depth_lt : ∀ p q, parent p = some q → depth q < depth p
  /-- The bag of the node introducing `p`. -/
  bag : Fin n → Finset (Fin n)
  mem_bag : ∀ p, p ∈ bag p
  card_bag : ∀ p, (bag p).card ≤ k + 1
  bag_sub : ∀ p q, parent p = some q → (bag p).erase p ⊆ bag q
  bag_root : ∀ p, parent p = none → (bag p).erase p = ∅
  adj_mem : ∀ p q, G.Adj p q → q ∈ (bag p).erase p ∨ p ∈ (bag q).erase q

namespace OneVertex

section RootedTree

variable {N : Type*} [DecidableEq N] {T : SimpleGraph N}

omit [DecidableEq N] in
lemma path_eq (hT : T.IsTree) {u v : N} {p q : T.Walk u v} (hp : p.IsPath) (hq : q.IsPath) :
    p = q := by
  have := (hT.isAcyclic.subsingleton_path u v).elim ⟨p, hp⟩ ⟨q, hq⟩
  exact congrArg Subtype.val this

lemma length_eq_dist (hT : T.IsTree) {u v : N} {p : T.Walk u v} (hp : p.IsPath) :
    p.length = T.dist u v := by
  obtain ⟨q, hq⟩ := hT.connected.exists_walk_length_eq_dist u v
  have h1 : q.bypass = p := path_eq hT (q.bypass_isPath) hp
  have h2 := q.length_bypass_le_length
  have h3 := T.dist_le p
  rw [h1] at h2
  omega

lemma dist_add_of_mem (hT : T.IsTree) {x y z : N} {p : T.Walk x y} (hp : p.IsPath)
    (hz : z ∈ p.support) : T.dist x z + T.dist z y = T.dist x y := by
  rw [← length_eq_dist hT (hp.takeUntil hz), ← length_eq_dist hT (hp.dropUntil hz),
    ← length_eq_dist hT hp, ← Walk.length_append, Walk.take_spec]

/-- `a` is an ancestor of `i` in `T` rooted at `r`: `a` lies on the path from `r` to `i`. -/
def Anc (T : SimpleGraph N) (r a i : N) : Prop := ∃ p : T.Walk r i, p.IsPath ∧ a ∈ p.support

omit [DecidableEq N] in
lemma anc_of_mem (hT : T.IsTree) {r a i : N} {p : T.Walk r i} (hp : p.IsPath)
    (ha : Anc T r a i) : a ∈ p.support := by
  obtain ⟨q, hq, haq⟩ := ha
  rwa [path_eq hT hp hq]

lemma anc_self (hT : T.IsTree) (r i : N) : Anc T r i i := by
  obtain ⟨p⟩ := hT.connected r i
  exact ⟨p.toPath, p.toPath.2, Walk.end_mem_support _⟩

lemma anc_dist (hT : T.IsTree) {r a i : N} (ha : Anc T r a i) :
    T.dist r a + T.dist a i = T.dist r i := by
  obtain ⟨p, hp, hap⟩ := ha
  exact dist_add_of_mem hT hp hap

lemma anc_le (hT : T.IsTree) {r a i : N} (ha : Anc T r a i) : T.dist r a ≤ T.dist r i := by
  have := anc_dist hT ha; omega

lemma anc_eq (hT : T.IsTree) {r a i : N} (ha : Anc T r a i) (h : T.dist r i ≤ T.dist r a) :
    a = i := by
  have := anc_dist hT ha
  exact (hT.connected.dist_eq_zero_iff).1 (by omega)

lemma anc_trans (hT : T.IsTree) {r a b c : N} (hab : Anc T r a b) (hbc : Anc T r b c) :
    Anc T r a c := by
  obtain ⟨p, hp, hbp⟩ := hbc
  exact ⟨p, hp, p.support_takeUntil_subset_support hbp (anc_of_mem hT (hp.takeUntil hbp) hab)⟩

lemma anc_total (hT : T.IsTree) {r a b i : N} (ha : Anc T r a i) (hb : Anc T r b i) :
    Anc T r a b ∨ Anc T r b a := by
  obtain ⟨p, hp, hap⟩ := ha
  have hbp := anc_of_mem hT hp hb
  by_cases h1 : b ∈ (p.takeUntil a hap).support
  · exact Or.inr ⟨_, hp.takeUntil hap, h1⟩
  by_cases h2 : a ∈ (p.takeUntil b hbp).support
  · exact Or.inl ⟨_, hp.takeUntil hbp, h2⟩
  have h1' : b ∈ (p.dropUntil a hap).support := by
    have := hbp; rw [← p.take_spec hap, Walk.mem_support_append_iff] at this; tauto
  have h2' : a ∈ (p.dropUntil b hbp).support := by
    have := hap; rw [← p.take_spec hbp, Walk.mem_support_append_iff] at this; tauto
  have e1 := dist_add_of_mem hT (hp.dropUntil hap) h1'
  have e2 := dist_add_of_mem hT (hp.dropUntil hbp) h2'
  have hab : T.dist a b = 0 := by rw [T.dist_comm (u := b) (v := a)] at e2; omega
  rw [hT.connected.dist_eq_zero_iff] at hab
  subst hab
  exact Or.inl (anc_self hT r a)

/-- If `a` is an ancestor of `b` and `b` of `c`, then `b` lies on the path from `a` to `c`. -/
lemma anc_path (hT : T.IsTree) {r a b c : N} (hab : Anc T r a b) (hbc : Anc T r b c) :
    ∃ q : T.Walk a c, q.IsPath ∧ b ∈ q.support := by
  obtain ⟨p, hp, hbp⟩ := hbc
  have hap : a ∈ p.support :=
    p.support_takeUntil_subset_support hbp (anc_of_mem hT (hp.takeUntil hbp) hab)
  refine ⟨p.dropUntil a hap, hp.dropUntil hap, ?_⟩
  have := hbp
  rw [← p.take_spec hap, Walk.mem_support_append_iff] at this
  rcases this with h | h
  · have hba : b = a := anc_eq hT ⟨_, hp.takeUntil hap, h⟩ (anc_le hT hab)
    subst hba
    exact Walk.start_mem_support _
  · exact h

/-- `p` is the parent of `x` in `T` rooted at `r`. -/
def Par (T : SimpleGraph N) (r p x : N) : Prop := T.Adj p x ∧ Anc T r p x

lemma par_dist (hT : T.IsTree) {r p x : N} (h : Par T r p x) :
    T.dist r p + 1 = T.dist r x := by
  have := anc_dist hT h.2
  rwa [dist_eq_one_iff_adj.2 h.1] at this

lemma adj_par (hT : T.IsTree) (r : N) {x y : N} (h : T.Adj x y) : Par T r x y ∨ Par T r y x := by
  obtain ⟨p⟩ := hT.connected r x
  by_cases hy : y ∈ p.toPath.1.support
  · exact Or.inr ⟨h.symm, _, p.toPath.2, hy⟩
  · exact Or.inl ⟨h, _, p.toPath.2.concat hy h, by simp⟩

lemma par_unique (hT : T.IsTree) {r p q x : N} (hp : Par T r p x) (hq : Par T r q x) : p = q := by
  have e1 := par_dist hT hp
  have e2 := par_dist hT hq
  rcases anc_total hT hp.2 hq.2 with h | h
  · exact anc_eq hT h (by omega)
  · exact (anc_eq hT h (by omega)).symm

/-- A path from `x` that avoids the parent of `x` stays below `x`. -/
lemma anc_or_par_mem (hT : T.IsTree) (r : N) {x y : N} (q : T.Walk x y) (hq : q.IsPath) :
    Anc T r x y ∨ ∃ p ∈ q.support, Par T r p x := by
  induction q with
  | nil => exact Or.inl (anc_self hT r _)
  | @cons x x' y h q ih =>
    rw [Walk.cons_isPath_iff] at hq
    rcases adj_par hT r h with hp | hp
    · rcases ih hq.1 with h' | ⟨p, hpq, hpp⟩
      · exact Or.inl (anc_trans hT hp.2 h')
      · exact absurd (par_unique hT hpp hp ▸ hpq) hq.2
    · exact Or.inr ⟨x', by simp, hp⟩

end RootedTree

/-- A vertex in the bags at both ends of a path of the decomposition tree is in every bag along
the path. -/
lemma mem_bag_of_mem_path {V : Type} {G : SimpleGraph V} (D : TreeDecomposition G)
    [DecidableEq D.Node] {v : V} {a b c : D.Node} (ha : v ∈ D.bag a) (hb : v ∈ D.bag b)
    {q : D.tree.Walk a b} (hq : q.IsPath) (hc : c ∈ q.support) : v ∈ D.bag c := by
  obtain ⟨w⟩ := (D.bag_indices_connected v).preconnected ⟨a, ha⟩ ⟨b, hb⟩
  have h1 := path_eq D.isTree
    (w.map (Embedding.induce {i : D.Node | v ∈ D.bag i}).toHom).bypass_isPath hq
  have h2 := Walk.support_bypass_subset_support
    (w.map (Embedding.induce {i : D.Node | v ∈ D.bag i}).toHom) (h1 ▸ hc)
  rw [Walk.support_map, List.mem_map] at h2
  obtain ⟨x, -, rfl⟩ := h2
  exact x.2

end OneVertex

open OneVertex in
/-- **Abramsky–Jakl–Paine, Theorem 3.4.** A graph of treewidth at most `k` has a one-vertex tree
decomposition of width at most `k`. -/
theorem oneVertexForest_of_treewidth {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ}
    (h : HasTreewidthAtMost G k) : Nonempty (OneVertexForest G k) := by
  classical
  obtain ⟨D, hD⟩ := h
  have hT := D.isTree
  obtain ⟨r⟩ := hT.connected.nonempty
  have hex : ∀ v, ∃ t, v ∈ D.bag t ∧
      ∀ j, v ∈ D.bag j → D.tree.dist r t ≤ D.tree.dist r j := by
    intro v
    obtain ⟨i, hi⟩ := D.vertex_mem_bag v
    obtain ⟨t, ht, hmin⟩ := (InvImage.wf (fun j => D.tree.dist r j) wellFounded_lt).has_min
      {j | v ∈ D.bag j} ⟨i, hi⟩
    exact ⟨t, ht, fun j hj => not_lt.1 (hmin j hj)⟩
  choose top htop hmin using hex
  have hanc : ∀ v i, v ∈ D.bag i → Anc D.tree r (top v) i := by
    intro v i hi
    obtain ⟨q⟩ := hT.connected (top v) i
    rcases anc_or_par_mem hT r q.toPath.1 q.toPath.2 with h | ⟨p, hp, hpar⟩
    · exact h
    · have h1 := hmin v p (mem_bag_of_mem_path D (htop v) hi q.toPath.2 hp)
      have h2 := par_dist hT hpar
      omega
  have hM : ∀ u w i, u ∈ D.bag i → w ∈ D.bag i →
      D.tree.dist r (top u) ≤ D.tree.dist r (top w) → u ∈ D.bag (top w) := by
    intro u w i hu hw hle
    rcases anc_total hT (hanc u i hu) (hanc w i hw) with h | h
    · obtain ⟨q, hq, hmem⟩ := anc_path hT h (hanc w i hw)
      exact mem_bag_of_mem_path D (htop u) hu hq hmem
    · rw [anc_eq hT h hle]
      exact htop u
  obtain ⟨key, hinj, hmono⟩ : ∃ key : Fin n → ℕ, Function.Injective key ∧
      ∀ u v, key u ≤ key v → D.tree.dist r (top u) ≤ D.tree.dist r (top v) := by
    have mono : ∀ u v : Fin n, D.tree.dist r (top u) * n + u.val ≤
        D.tree.dist r (top v) * n + v.val → D.tree.dist r (top u) ≤ D.tree.dist r (top v) := by
      intro u v h
      by_contra hlt
      have h1 : (D.tree.dist r (top v) + 1) * n ≤ D.tree.dist r (top u) * n :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 := v.isLt
      rw [Nat.add_mul, one_mul] at h1
      omega
    refine ⟨fun v => D.tree.dist r (top v) * n + v.val, fun u v h => ?_, mono⟩
    have e := le_antisymm (mono u v h.le) (mono v u h.ge)
    simp only [e] at h
    exact Fin.ext (by omega)
  let B : Fin n → Finset (Fin n) := fun v => (D.bag (top v)).filter (fun u => key u ≤ key v)
  have hpar : ∀ v, ∃ o : Option (Fin n), (o = none ∧ (B v).erase v = ∅) ∨
      ∃ w, o = some w ∧ w ∈ (B v).erase v ∧ ∀ u ∈ (B v).erase v, key u ≤ key w := by
    intro v
    rcases ((B v).erase v).eq_empty_or_nonempty with h | h
    · exact ⟨none, Or.inl ⟨rfl, h⟩⟩
    · obtain ⟨w, hw, hmax⟩ := ((B v).erase v).exists_max_image key h
      exact ⟨some w, Or.inr ⟨w, rfl, hw, hmax⟩⟩
  choose parent hparent using hpar
  have hsome : ∀ p q, parent p = some q →
      q ∈ (B p).erase p ∧ ∀ u ∈ (B p).erase p, key u ≤ key q := by
    intro p q h
    rcases hparent p with ⟨h1, -⟩ | ⟨w, h1, hw, hmax⟩
    · simp [h1] at h
    · rw [h1, Option.some_inj] at h
      subst h
      exact ⟨hw, hmax⟩
  refine ⟨⟨parent, key, ?_, B, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro p q h
    have hq := (hsome p q h).1
    simp only [B, Finset.mem_erase, Finset.mem_filter] at hq
    exact lt_of_le_of_ne hq.2.2 (fun e => hq.1 (hinj e))
  · intro p
    simp [B, htop p]
  · intro p
    exact (Finset.card_filter_le _ _).trans (hD _)
  · intro p q h u hu
    obtain ⟨hq, hmax⟩ := hsome p q h
    have hku := hmax u hu
    simp only [B, Finset.mem_erase, Finset.mem_filter] at hu hq ⊢
    exact ⟨hM u q (top p) hu.2.1 hq.2.1 (hmono _ _ hku), hku⟩
  · intro p h
    rcases hparent p with ⟨-, h1⟩ | ⟨w, h1, -⟩
    · exact h1
    · simp [h1] at h
  · intro p q hpq
    obtain ⟨i, hp, hq⟩ := D.edge_mem_bag hpq
    simp only [B, Finset.mem_erase, Finset.mem_filter]
    rcases le_total (key p) (key q) with h | h
    · exact Or.inr ⟨G.ne_of_adj hpq, hM p q i hp hq (hmono _ _ h), h⟩
    · exact Or.inl ⟨(G.ne_of_adj hpq).symm, hM q p i hq hp (hmono _ _ h), h⟩

end Lax119563Proofs.RowSpace
