import Lax119563Proofs.HomTensors.Spaces
import Lax119563.WeisfeilerLeman

/-!
# Color-class indicators of `k`-WL lie in `𝒱`

With `M = |V(G)|^k + |V(H)|^k` and `ν_0 = 0`, `ν_{r+1} = (M - 1)(1 + k ν_r)`, every
color-class indicator of round `r` lies in `Vs G H ν_r`.

* Round zero: the atomic type is a function of the values of the atom tensors
  `[v_i = v_j]`, `[v_i v_j ∈ E]`, `[χ(v_i) = c]` (all in `Vs 0`), so polynomial closure applies.
* Step: the round-`r+1` color is a function of the round-`r` class indicators and of the
  extensions `N_c` of `k` class indicators, which lie in `Vs (1 + k ν_r)`.
-/

namespace Lax119563Proofs.HomTensors

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman LGraph Finset

variable {k : ℕ} {G H : ColoredGraph}

variable (G H) in
/-- The round-`r` coloring on `Tup k G H`. -/
noncomputable def chi (r : ℕ) : Tup k G H → Color k r := Sum.elim (color G r) (color H r)

open scoped Classical in
variable (G H) in
/-- The indicator of a round-`r` color class on `Tup k G H`. -/
noncomputable def ind (r : ℕ) (c : Color k r) : Tup k G H → ℚ :=
  fun x => if chi G H r x = c then 1 else 0

/-- The size bound: `ν_0 = 0`, `ν_{r+1} = (M - 1)(1 + k ν_r)`. -/
def nu (k M : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => (M - 1) * (1 + k * nu k M r)

lemma ite_one_zero_iff {p q : Prop} [Decidable p] [Decidable q]
    (h : (if p then (1 : ℚ) else 0) = if q then 1 else 0) : p ↔ q := by
  split_ifs at h with hp hq hq <;> simp_all

/-! ### Round zero -/

/-- `[v_i = v_j]`. -/
def eqAtom (i j : Fin k) : LGraph k := atom (fun _ _ => False) (fun _ _ => False)
  (fun a b => a = i ∧ b = j)

/-- `[v_i v_j ∈ E]`. -/
def adjAtom (i j : Fin k) : LGraph k := atom (fun a b => a = i ∧ b = j) (fun _ _ => False)
  (fun _ _ => False)

/-- `[χ(v_i) = c]`. -/
def colAtom (i : Fin k) (c : ℕ) : LGraph k := atom (fun _ _ => False) (fun a c' => a = i ∧ c' = c)
  (fun _ _ => False)

variable (G H) in
/-- Equality of two entries. -/
def eqF (x : Tup k G H) (i j : Fin k) : Prop := Sum.elim (fun v => v i = v j) (fun v => v i = v j) x

variable (G H) in
/-- Adjacency of two entries. -/
def adjF (x : Tup k G H) (i j : Fin k) : Prop :=
  Sum.elim (fun v => G.graph.Adj (v i) (v j)) (fun v => H.graph.Adj (v i) (v j)) x

variable (G H) in
/-- The color of an entry. -/
def colF (x : Tup k G H) (i : Fin k) : ℕ :=
  Sum.elim (fun v => G.color (v i)) (fun v => H.color (v i)) x

open scoped Classical in
lemma tens_eqAtom (i j : Fin k) (x : Tup k G H) :
    tens G H (eqAtom i j) x = if eqF G H x i j then 1 else 0 := by
  rcases x with v | v
  · rw [eqAtom, tens_atom_inl]; simp [IsHom, atom, eqF]; try (split_ifs <;> simp_all)
  · rw [eqAtom, tens_atom_inr]; simp [IsHom, atom, eqF]; try (split_ifs <;> simp_all)

open scoped Classical in
lemma tens_adjAtom (i j : Fin k) (x : Tup k G H) :
    tens G H (adjAtom i j) x = if adjF G H x i j then 1 else 0 := by
  rcases x with v | v
  · rw [adjAtom, tens_atom_inl]; simp [IsHom, atom, adjF]; try (split_ifs <;> simp_all)
  · rw [adjAtom, tens_atom_inr]; simp [IsHom, atom, adjF]; try (split_ifs <;> simp_all)

open scoped Classical in
lemma tens_colAtom (i : Fin k) (c : ℕ) (x : Tup k G H) :
    tens G H (colAtom i c) x = if colF G H x i = c then 1 else 0 := by
  rcases x with v | v
  · rw [colAtom, tens_atom_inl]; simp [IsHom, atom, colF]; try (split_ifs <;> simp_all)
  · rw [colAtom, tens_atom_inr]; simp [IsHom, atom, colF]; try (split_ifs <;> simp_all)

lemma chi_zero_eq (x : Tup k G H) (i j : Fin k) : (chi G H 0 x).eq i j = true ↔ eqF G H x i j := by
  rcases x with v | v <;> exact decide_eq_true_iff

open scoped Classical in
lemma chi_zero_adj (x : Tup k G H) (i j : Fin k) :
    (chi G H 0 x).adj i j = true ↔ adjF G H x i j := by
  rcases x with v | v <;> exact decide_eq_true_iff

lemma chi_zero_color (x : Tup k G H) (i : Fin k) : (chi G H 0 x).color i = colF G H x i := by
  rcases x with v | v <;> rfl

lemma atomicType_ext {a b : AtomicType k} (h₁ : ∀ i j, a.eq i j = b.eq i j)
    (h₂ : ∀ i j, a.adj i j = b.adj i j) (h₃ : ∀ i, a.color i = b.color i) : a = b := by
  cases a; cases b
  simp only [AtomicType.mk.injEq]
  exact ⟨funext fun i => funext fun j => h₁ i j, funext fun i => funext fun j => h₂ i j,
    funext h₃⟩

variable (G H) in
/-- The colors of `G` and `H`. -/
noncomputable def colors : Finset ℕ := by
  classical exact univ.image G.color ∪ univ.image H.color

lemma colF_mem (x : Tup k G H) (i : Fin k) : colF G H x i ∈ colors G H := by
  classical
  rcases x with v | v <;> simp [colF, colors]

variable (G H) in
open scoped Classical in
/-- The generators for round zero. -/
noncomputable def gens0 : Finset (Tup k G H → ℚ) :=
  (univ : Finset (Fin k × Fin k)).image (fun p => tens G H (eqAtom p.1 p.2)) ∪
    (univ : Finset (Fin k × Fin k)).image (fun p => tens G H (adjAtom p.1 p.2)) ∪
    (univ ×ˢ colors G H).image (fun p => tens G H (colAtom p.1 p.2))

lemma gens0_sub :
    ((gens0 G H : Finset (Tup k G H → ℚ)) : Set _) ⊆ (Vs (k := k) G H 0 : Set (Tup k G H → ℚ)) := by
  classical
  intro g hg
  simp only [gens0, coe_union, coe_image, Set.mem_union, Set.mem_image, mem_coe] at hg
  rcases hg with ((⟨p, -, rfl⟩ | ⟨p, -, rfl⟩) | ⟨p, -, rfl⟩) <;> exact tens_mem (good_atom _ _ _)

lemma chi_zero_eq_of (x y : Tup k G H) (h : ∀ g ∈ gens0 G H, g x = g y) :
    chi G H 0 x = chi G H 0 y := by
  classical
  apply atomicType_ext
  · intro i j
    have := h _ (by simp only [gens0, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_product]; exact Or.inl (Or.inl ⟨(i, j), rfl⟩))
    rw [tens_eqAtom, tens_eqAtom] at this
    have := ite_one_zero_iff this
    rw [Bool.eq_iff_iff, chi_zero_eq, chi_zero_eq]
    exact this
  · intro i j
    have := h _ (by simp only [gens0, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_product]; exact Or.inl (Or.inr ⟨(i, j), rfl⟩))
    rw [tens_adjAtom, tens_adjAtom] at this
    have := ite_one_zero_iff this
    rw [Bool.eq_iff_iff, chi_zero_adj, chi_zero_adj]
    exact this
  · intro i
    have := h (tens G H (colAtom i (colF G H x i))) (by
      simp only [gens0, mem_union, mem_image, mem_product, mem_univ, true_and]
      exact Or.inr ⟨⟨i, colF G H x i⟩, colF_mem x i, rfl⟩)
    rw [tens_colAtom, tens_colAtom] at this
    have := (ite_one_zero_iff this).1 rfl
    rw [chi_zero_color, chi_zero_color, this]

theorem ind_zero_mem (c : Color k 0) : ind G H 0 c ∈ Vs G H 0 := by
  classical
  have h := mem_polySpan (gens0 G H) (ind G H 0 c) (fun x y hxy => by
    simp only [ind, chi_zero_eq_of x y hxy])
  have := polySpan_le_Vs _ 0 _ gens0_sub h
  simpa using this

/-! ### The step -/

variable (G H) in
/-- The neighbouring tuples `(v[q/1], …, v[q/k])` over all `q`. -/
noncomputable def nbr (x : Tup k G H) : Multiset (Fin k → Tup k G H) :=
  Sum.elim (fun p => (univ : Finset (Fin G.n)).val.map fun q i => .inl (Function.update p i q))
    (fun p => (univ : Finset (Fin H.n)).val.map fun q i => .inr (Function.update p i q)) x

lemma extOp_eq_nbr (f : Fin k → Tup k G H → ℚ) (x : Tup k G H) :
    extOp f x = ((nbr G H x).map fun y => ∏ j, f j (y j)).sum := by
  rcases x with p | p <;> simp [extOp, nbr, Multiset.map_map, Finset.sum_eq_multiset_sum] <;> rfl

lemma chi_succ (r : ℕ) (x : Tup k G H) :
    chi G H (r + 1) x = (chi G H r x, (nbr G H x).map fun y => chi G H r ∘ y) := by
  rcases x with p | p <;> simp [chi, color, nbr, Multiset.map_map] <;> rfl

open scoped Classical in
lemma extOp_ind (r : ℕ) (c : Fin k → Color k r) (x : Tup k G H) :
    extOp (fun j => ind G H r (c j)) x =
      (((nbr G H x).map fun y => chi G H r ∘ y).count c : ℚ) := by
  classical
  rw [extOp_eq_nbr]
  induction nbr G H x using Multiset.induction_on with
  | empty => simp
  | cons y s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.map_cons, Multiset.count_cons]
    have : ∏ j, ind G H r (c j) (y j) = if c = chi G H r ∘ y then 1 else 0 := by
      by_cases hc : c = chi G H r ∘ y
      · subst hc
        simp [ind]
      · rw [if_neg hc]
        obtain ⟨j, hj⟩ : ∃ j, chi G H r (y j) ≠ c j := by
          by_contra hcon
          push Not at hcon
          exact hc (funext fun j => (hcon j).symm)
        exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [ind, hj])
    rw [this]
    split_ifs <;> push_cast <;> ring

variable (G H) in
open scoped Classical in
/-- The generators for the step: the round-`r` class indicators and the extensions `N_c`. -/
noncomputable def gensSucc (r : ℕ) : Finset (Tup k G H → ℚ) :=
  (univ : Finset (Tup k G H)).image (fun x => ind G H r (chi G H r x)) ∪
    (univ : Finset (Fin k → Tup k G H)).image
      (fun y => extOp (fun j => ind G H r (chi G H r (y j))))

lemma chi_succ_eq_of (r : ℕ) (x y : Tup k G H) (h : ∀ g ∈ gensSucc G H r, g x = g y) :
    chi G H (r + 1) x = chi G H (r + 1) y := by
  classical
  rw [chi_succ, chi_succ]
  have h₁ : chi G H r x = chi G H r y := by
    by_contra hne
    have := h _ (by
      simp only [gensSucc, mem_union, mem_image, mem_univ, true_and]
      exact Or.inl ⟨x, rfl⟩)
    simp only [ind] at this
    rw [if_neg (Ne.symm hne)] at this
    simp at this
  refine Prod.ext h₁ (Multiset.ext.2 fun c => ?_)
  by_cases hc : ∃ z : Fin k → Tup k G H, chi G H r ∘ z = c
  · obtain ⟨z, rfl⟩ := hc
    have := h _ (by
      simp only [gensSucc, mem_union, mem_image, mem_univ, true_and]
      exact Or.inr ⟨z, rfl⟩)
    have e : (fun j => ind G H r (chi G H r (z j))) = fun j => ind G H r ((chi G H r ∘ z) j) :=
      rfl
    rw [e, extOp_ind, extOp_ind] at this
    exact_mod_cast this
  · push Not at hc
    rw [Multiset.count_eq_zero.2, Multiset.count_eq_zero.2]
    · intro hm
      obtain ⟨z, -, hz⟩ := Multiset.mem_map.1 hm
      exact hc z hz
    · intro hm
      obtain ⟨z, -, hz⟩ := Multiset.mem_map.1 hm
      exact hc z hz

theorem ind_succ_mem (hk : 1 ≤ k) (r : ℕ) (N : ℕ) (hr : ∀ c : Color k r, ind G H r c ∈ Vs G H N)
    (c : Color k (r + 1)) :
    ind G H (r + 1) c ∈ Vs G H ((Fintype.card (Tup k G H) - 1) * (1 + k * N)) := by
  classical
  have hsub : ((gensSucc G H r : Finset (Tup k G H → ℚ)) : Set _) ⊆
      (Vs (k := k) G H (1 + k * N) : Set (Tup k G H → ℚ)) := by
    intro g hg
    simp only [gensSucc, coe_union, coe_image, Set.mem_union, Set.mem_image, mem_coe] at hg
    rcases hg with ⟨x, -, rfl⟩ | ⟨z, -, rfl⟩
    · exact Vs_mono (by nlinarith) (hr _)
    · exact extOp_mem _ fun j => hr _
  have h := mem_polySpan (gensSucc G H r) (ind G H (r + 1) c) (fun x y hxy => by
    simp only [ind, chi_succ_eq_of r x y hxy])
  exact polySpan_le_Vs _ _ _ hsub h

theorem ind_mem (hk : 1 ≤ k) (r : ℕ) (c : Color k r) :
    ind G H r c ∈ Vs G H (nu k (Fintype.card (Tup k G H)) r) := by
  induction r with
  | zero => exact ind_zero_mem c
  | succ r ih => exact ind_succ_mem hk r _ ih c

end Lax119563Proofs.HomTensors
