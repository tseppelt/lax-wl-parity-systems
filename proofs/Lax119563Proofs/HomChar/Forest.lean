import Lax119563Proofs.RowSpace.OneVertex

/-!
# Subtrees of one-vertex forests, and sums over partial assignments

For a one-vertex forest `T` (`RowSpace.OneVertexForest`) we write `Up T v a` when `a` is an
ancestor of `v` (reflexively), `S T c` for the vertices below `c` (the subtree of `c`),
`ch T c` for the children of `c` and `I T c` for the bag of `c` without `c` itself. Every vertex in
the bag of `v` is an ancestor of `v`, so the subtrees of the children of `c` are pairwise disjoint
and only see each other through the bag of `c`.

`agreeOff s g` is the set of maps that agree with `g` outside `s`. Sums over such sets split along
a vertex (`sum_agreeOff_insert`) and factor over disjoint blocks (`sum_agreeOff_biUnion`).
-/

namespace Lax119563Proofs.HomChar

open Lax119563Proofs.RowSpace Relation

section Forest

variable {n k : ℕ} {Γ : SimpleGraph (Fin n)} (T : OneVertexForest Γ k)

/-- `a` is an ancestor of `v` (or `v` itself). -/
def Up (v a : Fin n) : Prop := ReflTransGen (fun x y => T.parent x = some y) v a

/-- The bag of `v` without `v`. -/
def I (v : Fin n) : Finset (Fin n) := (T.bag v).erase v

/-- The vertices below `c` (including `c`). -/
noncomputable def S (c : Fin n) : Finset (Fin n) := by
  classical exact Finset.univ.filter fun v => Up T v c

/-- The children of `c`. -/
noncomputable def ch (c : Fin n) : Finset (Fin n) := by
  classical exact Finset.univ.filter fun v => T.parent v = some c

/-- The roots. -/
noncomputable def roots : Finset (Fin n) := by
  classical exact Finset.univ.filter fun v => T.parent v = none

variable {T}

@[simp] lemma mem_S {c v : Fin n} : v ∈ S T c ↔ Up T v c := by
  classical simp [S]

@[simp] lemma mem_ch {c v : Fin n} : v ∈ ch T c ↔ T.parent v = some c := by
  classical simp [ch]

@[simp] lemma mem_roots {v : Fin n} : v ∈ roots T ↔ T.parent v = none := by
  classical simp [roots]

lemma mem_I {v b : Fin n} : b ∈ I T v ↔ b ≠ v ∧ b ∈ T.bag v := Finset.mem_erase

lemma up_refl (v : Fin n) : Up T v v := ReflTransGen.refl

lemma up_single {v c : Fin n} (h : T.parent v = some c) : Up T v c := ReflTransGen.single h

lemma Up.trans {a b c : Fin n} (h1 : Up T a b) (h2 : Up T b c) : Up T a c :=
  ReflTransGen.trans h1 h2

lemma up_head {v c a : Fin n} (h : T.parent v = some c) (h2 : Up T c a) : Up T v a :=
  ReflTransGen.head h h2

lemma Up.depth_le {v a : Fin n} (h : Up T v a) : T.depth a ≤ T.depth v := by
  induction h with
  | refl => exact le_rfl
  | tail _ h2 ih => exact (T.depth_lt _ _ h2).le.trans ih

lemma Up.ne_parent {v a : Fin n} (h : Up T v a) (hne : v ≠ a) :
    ∃ c, T.parent v = some c ∧ Up T c a := by
  rcases ReflTransGen.cases_head h with h | h
  · exact absurd h hne
  · exact h

lemma Up.last {v a : Fin n} (h : Up T v a) (hne : v ≠ a) :
    ∃ d, Up T v d ∧ T.parent d = some a := by
  rcases ReflTransGen.cases_tail h with h | h
  · exact absurd h.symm hne
  · exact h

lemma Up.total {u a b : Fin n} (ha : Up T u a) (hb : Up T u b) : Up T a b ∨ Up T b a :=
  ReflTransGen.total_of_right_unique (fun _ _ _ h1 h2 => Option.some_injective _ (h1.symm.trans h2))
    ha hb

lemma Up.eq_of_root {ρ a : Fin n} (h : Up T ρ a) (hρ : T.parent ρ = none) : ρ = a := by
  rcases ReflTransGen.cases_head h with h | ⟨c, hc, _⟩
  · exact h
  · rw [hρ] at hc; cases hc

lemma I_eq_empty_of_root {ρ : Fin n} (hρ : T.parent ρ = none) : I T ρ = ∅ := T.bag_root ρ hρ

lemma I_subset_parent {v c : Fin n} (h : T.parent v = some c) : I T v ⊆ T.bag c :=
  T.bag_sub v c h

lemma up_of_mem_bag {v a : Fin n} (ha : a ∈ T.bag v) : Up T v a := by
  induction hd : T.depth v using Nat.strong_induction_on generalizing v with
  | _ m ih =>
    by_cases hav : a = v
    · subst hav; exact up_refl _
    have haI : a ∈ I T v := mem_I.2 ⟨hav, ha⟩
    cases hp : T.parent v with
    | none => simp [I_eq_empty_of_root hp] at haI
    | some c =>
      exact up_head hp (ih _ (hd ▸ T.depth_lt _ _ hp) (I_subset_parent hp haI) rfl)

lemma exists_root (v : Fin n) : ∃ ρ, T.parent ρ = none ∧ Up T v ρ := by
  induction hd : T.depth v using Nat.strong_induction_on generalizing v with
  | _ m ih =>
    cases hp : T.parent v with
    | none => exact ⟨v, hp, up_refl _⟩
    | some c =>
      obtain ⟨ρ, h1, h2⟩ := ih _ (hd ▸ T.depth_lt _ _ hp) c rfl
      exact ⟨ρ, h1, up_head hp h2⟩

/-- A vertex in the bag of a vertex below `d` that is not itself below `d` is in `I d`. -/
lemma mem_I_of_up {u d a : Fin n} (hud : Up T u d) (ha : a ∈ T.bag u) (had : ¬ Up T a d) :
    a ∈ I T d := by
  induction hud using ReflTransGen.head_induction_on generalizing a with
  | refl =>
    refine mem_I.2 ⟨fun h => had (h ▸ up_refl _), ha⟩
  | head h hrest ih =>
    rename_i u u'
    have hau : a ≠ u := fun e => had (e ▸ up_head h hrest)
    exact ih (I_subset_parent h (mem_I.2 ⟨hau, ha⟩)) had

lemma S_eq_insert (c : Fin n) : S T c = insert c ((ch T c).biUnion (S T)) := by
  classical
  ext v
  simp only [mem_S, Finset.mem_insert, Finset.mem_biUnion, mem_ch]
  constructor
  · intro h
    by_cases hvc : v = c
    · exact Or.inl hvc
    · obtain ⟨d, h1, h2⟩ := h.last hvc
      exact Or.inr ⟨d, h2, h1⟩
  · rintro (rfl | ⟨d, h1, h2⟩)
    · exact up_refl _
    · exact h2.trans (up_single h1)

lemma not_up_child {c d : Fin n} (hd : T.parent d = some c) : ¬ Up T c d := fun h => by
  have := h.depth_le
  have := T.depth_lt _ _ hd
  omega

lemma not_mem_S_child {c d : Fin n} (hd : d ∈ ch T c) : c ∉ S T d := by
  rw [mem_S]; exact not_up_child (mem_ch.1 hd)

lemma S_child_subset {c d : Fin n} (hd : d ∈ ch T c) : S T d ⊆ S T c := fun v hv => by
  rw [mem_S] at hv ⊢; exact hv.trans (up_single (mem_ch.1 hd))

lemma disjoint_S_children {c d d' : Fin n} (hd : d ∈ ch T c) (hd' : d' ∈ ch T c) (hne : d ≠ d') :
    Disjoint (S T d) (S T d') := by
  rw [Finset.disjoint_left]
  intro u hu hu'
  rw [mem_S] at hu hu'
  rw [mem_ch] at hd hd'
  have key : ∀ {e e' : Fin n}, T.parent e = some c → T.parent e' = some c → e ≠ e' →
      ¬ Up T e e' := by
    intro e e' he he' hne h
    obtain ⟨f, hf, hfe⟩ := h.ne_parent hne
    rw [he, Option.some_inj] at hf
    subst hf
    exact not_up_child he' hfe
  rcases hu.total hu' with h | h
  · exact key hd hd' hne h
  · exact key hd' hd (Ne.symm hne) h

lemma disjoint_bag_S_child {c d : Fin n} (hd : d ∈ ch T c) : Disjoint (T.bag c) (S T d) := by
  rw [Finset.disjoint_left]
  intro a ha haS
  rw [mem_S] at haS
  exact not_up_child (mem_ch.1 hd) ((up_of_mem_bag ha).trans haS)

lemma bag_subset_of_child {c d u : Fin n} (hd : d ∈ ch T c) (hu : u ∈ S T d) :
    T.bag u ⊆ S T d ∪ T.bag c := by
  intro a ha
  rw [Finset.mem_union, mem_S]
  by_cases had : Up T a d
  · exact Or.inl had
  · exact Or.inr (I_subset_parent (mem_ch.1 hd) (mem_I_of_up (mem_S.1 hu) ha had))

lemma univ_eq_roots : (Finset.univ : Finset (Fin n)) = (roots T).biUnion (S T) := by
  classical
  ext v
  simp only [Finset.mem_univ, Finset.mem_biUnion, mem_roots, mem_S, true_iff]
  exact exists_root v

lemma disjoint_S_roots {ρ ρ' : Fin n} (h : ρ ∈ roots T) (h' : ρ' ∈ roots T) (hne : ρ ≠ ρ') :
    Disjoint (S T ρ) (S T ρ') := by
  rw [Finset.disjoint_left]
  intro u hu hu'
  rw [mem_S] at hu hu'
  rw [mem_roots] at h h'
  rcases hu.total hu' with e | e
  · exact hne (e.eq_of_root h)
  · exact hne (e.eq_of_root h').symm

lemma bag_subset_of_root {ρ u : Fin n} (hρ : ρ ∈ roots T) (hu : u ∈ S T ρ) : T.bag u ⊆ S T ρ := by
  intro a ha
  rw [mem_S]
  by_contra h
  have := mem_I_of_up (mem_S.1 hu) ha h
  rw [I_eq_empty_of_root (mem_roots.1 hρ)] at this
  simp at this

lemma I_child_root {ρ d : Fin n} (hρ : ρ ∈ roots T) (hd : d ∈ ch T ρ) {b : Fin n}
    (hb : b ∈ I T d) : b = ρ := by
  have hb' := I_subset_parent (mem_ch.1 hd) hb
  by_contra hne
  have : b ∈ I T ρ := mem_I.2 ⟨hne, hb'⟩
  rw [I_eq_empty_of_root (mem_roots.1 hρ)] at this
  simp at this

lemma card_I (v : Fin n) : (I T v).card ≤ k := by
  have := T.card_bag v
  have := Finset.card_erase_of_mem (T.mem_bag v)
  unfold I; omega

end Forest

/-! ### Sums over maps agreeing with a given map outside a set -/

section Sums

variable {V M : Type*} [Fintype V] [DecidableEq V] [Fintype M] [DecidableEq M]

/-- The maps that agree with `g` outside `s`. -/
noncomputable def agreeOff (s : Finset V) (g : V → M) : Finset (V → M) := by
  classical exact Finset.univ.filter fun h => ∀ v, v ∉ s → h v = g v

@[simp] lemma mem_agreeOff {s : Finset V} {g h : V → M} :
    h ∈ agreeOff s g ↔ ∀ v, v ∉ s → h v = g v := by
  classical simp [agreeOff]

lemma agreeOff_univ (g : V → M) : agreeOff Finset.univ g = Finset.univ := by
  ext h; simp

lemma sum_agreeOff_insert {c : V} {U : Finset V} (hc : c ∉ U) (g : V → M) (f : (V → M) → ℕ) :
    ∑ h ∈ agreeOff (insert c U) g, f h = ∑ x, ∑ h ∈ agreeOff U (Function.update g c x), f h := by
  rw [← Finset.sum_fiberwise (agreeOff (insert c U) g) (fun h => h c) f]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr ?_ fun _ _ => rfl
  ext h
  simp only [Finset.mem_filter, mem_agreeOff, Finset.mem_insert, not_or]
  constructor
  · rintro ⟨hh, rfl⟩ v hv
    by_cases hvc : v = c
    · subst hvc; simp
    · rw [Function.update_of_ne hvc]; exact hh v ⟨hvc, hv⟩
  · intro hh
    refine ⟨fun v ⟨hvc, hv⟩ => by rw [hh v hv, Function.update_of_ne hvc], ?_⟩
    rw [hh c hc, Function.update_self]

lemma sum_agreeOff_biUnion {ι : Type*} [DecidableEq ι] (A : Finset ι) (B D : ι → Finset V)
    (P : ι → (V → M) → ℕ) (g : V → M)
    (hB : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (B i) (B j))
    (hD : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (D i) (B j))
    (hP : ∀ i ∈ A, ∀ h h' : V → M, (∀ v ∈ D i, h v = h' v) → P i h = P i h') :
    ∑ h ∈ agreeOff (A.biUnion B) g, ∏ i ∈ A, P i h = ∏ i ∈ A, ∑ h ∈ agreeOff (B i) g, P i h := by
  induction A using Finset.induction_on with
  | empty =>
    simp only [Finset.biUnion_empty, Finset.prod_empty, Finset.sum_const, smul_eq_mul, mul_one]
    rw [Finset.card_eq_one]
    refine ⟨g, ?_⟩
    ext h
    simp only [mem_agreeOff, Finset.notMem_empty, not_false_eq_true, forall_const,
      Finset.mem_singleton]
    exact ⟨funext, fun e v => by rw [e]⟩
  | insert a A ha ih =>
    have hB' : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (B i) (B j) := fun i hi j hj =>
      hB i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    have hD' : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (D i) (B j) := fun i hi j hj =>
      hD i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    have hP' : ∀ i ∈ A, ∀ h h' : V → M, (∀ v ∈ D i, h v = h' v) → P i h = P i h' :=
      fun i hi => hP i (Finset.mem_insert_of_mem hi)
    simp_rw [Finset.prod_insert ha]
    rw [← ih hB' hD' hP', Finset.sum_mul_sum, ← Finset.sum_product']
    set U := A.biUnion B
    have haA : ∀ j ∈ A, a ≠ j := fun j hj e => ha (e ▸ hj)
    have hdisj : ∀ v, v ∈ B a → v ∉ U := by
      intro v hv hvU
      obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.1 hvU
      exact Finset.disjoint_left.1 (hB a (Finset.mem_insert_self _ _) j
        (Finset.mem_insert_of_mem hj) (haA j hj)) hv hvj
    have hDa : ∀ v, v ∈ D a → v ∉ U := by
      intro v hv hvU
      obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.1 hvU
      exact Finset.disjoint_left.1 (hD a (Finset.mem_insert_self _ _) j
        (Finset.mem_insert_of_mem hj) (haA j hj)) hv hvj
    have hDj : ∀ j ∈ A, ∀ v, v ∈ D j → v ∉ B a := fun j hj v hv hva =>
      Finset.disjoint_left.1 (hD j (Finset.mem_insert_of_mem hj) a (Finset.mem_insert_self _ _)
        (haA j hj).symm) hv hva
    rw [Finset.biUnion_insert]
    refine Finset.sum_nbij' (fun h => ((fun v => if v ∈ B a then h v else g v),
      (fun v => if v ∈ U then h v else g v)))
      (fun p v => if v ∈ B a then p.1 v else p.2 v) ?_ ?_ ?_ ?_ ?_
    · intro h _
      simp only [Finset.mem_product, mem_agreeOff]
      exact ⟨fun v hv => by simp [hv], fun v hv => by simp [hv]⟩
    · rintro ⟨h1, h2⟩ hh
      simp only [Finset.mem_product, mem_agreeOff, Finset.mem_union, not_or] at hh ⊢
      intro v ⟨hva, hvU⟩
      simp [hva, hh.2 v hvU]
    · intro h hh
      simp only [mem_agreeOff, Finset.mem_union, not_or] at hh
      funext v
      by_cases hva : v ∈ B a
      · simp [hva]
      · by_cases hvU : v ∈ U
        · simp [hva, hvU]
        · simp [hva, hvU, hh v ⟨hva, hvU⟩]
    · rintro ⟨h1, h2⟩ hh
      simp only [Finset.mem_product, mem_agreeOff] at hh
      refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
      · by_cases hva : v ∈ B a
        · simp [hva]
        · simp [hva, hh.1 v hva]
      · by_cases hvU : v ∈ U
        · have hva : v ∉ B a := fun h => hdisj v h hvU
          simp [hvU, hva]
        · simp [hvU, hh.2 v hvU]
    · intro h hh
      simp only [mem_agreeOff, Finset.mem_union, not_or] at hh
      congr 1
      · refine hP a (Finset.mem_insert_self _ _) _ _ fun v hv => ?_
        by_cases hva : v ∈ B a
        · simp [hva]
        · simp [hva, hh v ⟨hva, hDa v hv⟩]
      · refine Finset.prod_congr rfl fun j hj => hP' j hj _ _ fun v hv => ?_
        by_cases hvU : v ∈ U
        · simp [hvU]
        · simp [hvU, hh v ⟨hDj j hj v hv, hvU⟩]

end Sums

end Lax119563Proofs.HomChar
