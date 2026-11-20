import Lax119563.WeisfeilerLeman
import Lax119563Proofs.UpperBound.Rounds
import Lax119563Proofs.Stabilization.Interface

/-!
# Colorings produced by `k`-WL and their matrix spaces

Döring–Neuen §4 and §6.1, for the colorings `χ_r = color G r` of `k`-WL on a colored graph `G`
(the sequence is infinite; no termination index is needed):

* `χ_{r+1}` refines `χ_r`; `χ_r` is compatible with equality and shufflable for every
  `σ : Fin k → Fin k` (Lemma 4.2);
* the space `classSpace χ` of matrices constant on the color classes of a coloring `χ` of pairs
  (the span `⟨χ⟩` of the paper), and Lemmas 4.5–4.7;
* for `k = m + 2` and `v ∈ V^m` the projections `χ^v_r (a, b) = χ_r (v, a, b)`:
  multiplicativity (Lemma 6.2) and extendability (Lemma 6.4).
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman

namespace Lax119563Proofs.Stabilization

/-! ### Refinement, compatibility with equality, shufflability -/

section Basic

variable {G : ColoredGraph} {k : ℕ}

theorem color_succ (r : ℕ) (p : Fin k → Fin G.n) :
    color G (r + 1) p =
      (color G r p, (Finset.univ : Finset (Fin G.n)).val.map
        fun q i => color G r (Function.update p i q)) := rfl

/-- `χ_{r+1}` refines `χ_r`. -/
theorem color_eq_of_succ {r : ℕ} {p q : Fin k → Fin G.n}
    (h : color G (r + 1) p = color G (r + 1) q) : color G r p = color G r q := by
  rw [color_succ, color_succ] at h
  exact congrArg Prod.fst h

theorem color_eq_of_le {s r : ℕ} (hsr : s ≤ r) {p q : Fin k → Fin G.n}
    (h : color G r p = color G r q) : color G s p = color G s q := by
  induction r, hsr using Nat.le_induction with
  | base => exact h
  | succ r _ ih => exact ih (color_eq_of_succ h)

/-- `χ_r` is compatible with equality. -/
theorem eq_iff_of_color_eq {r : ℕ} {p q : Fin k → Fin G.n} (h : color G r p = color G r q)
    (i j : Fin k) : p i = p j ↔ q i = q j := by
  have h0 := congrArg AtomicType.eq (color_eq_of_le (Nat.zero_le r) h)
  have := congrFun (congrFun h0 i) j
  simpa [color, atp] using this

/-- Replacing coordinate `i` of `p ∘ σ` is replacing some coordinate of `p` and then
composing with some map: for injective `σ` take `σ i` and `σ`, otherwise a coordinate `j`
outside the range of `σ` and `σ` redirected to `j` at `i`. -/
theorem exists_update_comp {α : Type*} (σ : Fin k → Fin k) (i : Fin k) :
    ∃ (j : Fin k) (τ : Fin k → Fin k), ∀ (p : Fin k → α) (x : α),
      Function.update (p ∘ σ) i x = Function.update p j x ∘ τ := by
  classical
  by_cases hσ : Function.Injective σ
  · exact ⟨σ i, σ, fun p x => (Function.update_comp_eq_of_injective p hσ i x).symm⟩
  · have hs : ¬ Function.Surjective σ := fun hs => hσ (Finite.injective_iff_surjective.2 hs)
    simp only [Function.Surjective, not_forall, not_exists] at hs
    obtain ⟨j, hj⟩ := hs
    refine ⟨j, Function.update σ i j, fun p x => ?_⟩
    funext i'
    by_cases hi : i' = i
    · subst hi; simp
    · simp [Function.update_of_ne hi, Function.update_of_ne (hj i')]

/-- `χ_r` is shufflable, for every (not necessarily bijective) `σ : Fin k → Fin k`. -/
theorem color_comp_eq (r : ℕ) : ∀ (σ : Fin k → Fin k) {p q : Fin k → Fin G.n},
    color G r p = color G r q → color G r (p ∘ σ) = color G r (q ∘ σ) := by
  induction r with
  | zero =>
    intro σ p q h
    have he := congrArg AtomicType.eq h
    have ha := congrArg AtomicType.adj h
    have hc := congrArg AtomicType.color h
    have key : ∀ p : Fin k → Fin G.n, color G 0 (p ∘ σ) =
        ⟨fun i j => (atp G p).eq (σ i) (σ j), fun i j => (atp G p).adj (σ i) (σ j),
          fun i => (atp G p).color (σ i)⟩ := fun p => rfl
    rw [key p, key q]
    change (atp G p).eq = (atp G q).eq at he
    change (atp G p).adj = (atp G q).adj at ha
    change (atp G p).color = (atp G q).color at hc
    rw [he, ha, hc]
  | succ r ih =>
    intro σ p q h
    rw [color_succ, color_succ] at h ⊢
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    refine Prod.ext (ih σ h1) ?_
    refine UpperBound.multiset_map_eq_of_map_eq (fun a b hab => ?_) _ _ h2
    funext i
    obtain ⟨j, τ, hjτ⟩ := exists_update_comp (α := Fin G.n) σ i
    rw [hjτ p a, hjτ q b]
    exact ih τ (congrFun hab j)

end Basic

/-! ### Matrix spaces of colorings of pairs -/

section ClassSpace

variable {α β β' : Type*}

/-- The matrices constant on the color classes of `χ` (the span `⟨χ⟩` of the paper). -/
def classSpace (χ : α → α → β) : Submodule ℂ (Matrix α α ℂ) where
  carrier := {M | ∀ a b c d, χ a b = χ c d → M a b = M c d}
  add_mem' := by
    intro M N hM hN a b c d h
    simp [hM a b c d h, hN a b c d h]
  zero_mem' := by
    intro a b c d _
    rfl
  smul_mem' := by
    intro s M hM a b c d h
    simp [hM a b c d h]

theorem mem_classSpace {χ : α → α → β} {M : Matrix α α ℂ} :
    M ∈ classSpace χ ↔ ∀ a b c d, χ a b = χ c d → M a b = M c d := Iff.rfl

/-- A finer coloring has a larger space. -/
theorem classSpace_le {χ : α → α → β} {χ' : α → α → β'}
    (h : ∀ a b c d, χ' a b = χ' c d → χ a b = χ c d) : classSpace χ ≤ classSpace χ' :=
  fun _ hM a b c d hc => hM a b c d (h a b c d hc)

/-- Lemma 4.7 (and Equation (5)): the space determines the partition. -/
theorem eq_of_classSpace_le {χ : α → α → β} {χ' : α → α → β'}
    (h : classSpace χ' ≤ classSpace χ) {a b c d : α} (hc : χ a b = χ c d) :
    χ' a b = χ' c d := by
  classical
  let M : Matrix α α ℂ := fun x y => if χ' x y = χ' a b then 1 else 0
  have hM : M ∈ classSpace χ' := by
    intro x y z w hxy
    simp only [M, hxy]
  have := h hM a b c d hc
  simp only [M, if_pos rfl] at this
  by_contra hne
  rw [if_neg (Ne.symm hne)] at this
  exact one_ne_zero this

/-- Lemma 4.5: compatibility with equality gives the identity. -/
theorem one_mem_classSpace [DecidableEq α] {χ : α → α → β}
    (h : ∀ a b c d, χ a b = χ c d → (a = b ↔ c = d)) : (1 : Matrix α α ℂ) ∈ classSpace χ := by
  intro a b c d hc
  simp only [Matrix.one_apply, h a b c d hc]

/-- Lemma 4.6: symmetric classes give closure under conjugate transposition. -/
theorem star_mem_classSpace {χ : α → α → β}
    (h : ∀ a b c d, χ a b = χ c d → χ b a = χ d c) {M : Matrix α α ℂ}
    (hM : M ∈ classSpace χ) : star M ∈ classSpace χ := by
  intro a b c d hc
  simp only [Matrix.star_apply, hM b a d c (h a b c d hc)]

end ClassSpace

/-! ### Projections `χ^v_r (a, b) = χ_r (v, a, b)` for `k = m + 2` -/

section Projections

variable {α : Type*} {m : ℕ}

/-- The tuple `(v, a, b)`. -/
def tup (v : Fin m → α) (a b : α) : Fin (m + 2) → α :=
  Fin.snoc (Fin.snoc v a : Fin (m + 1) → α) b

/-- The coordinate of `a` in `(v, a, b)`. -/
def penIdx (m : ℕ) : Fin (m + 2) := (Fin.last m).castSucc

/-- The coordinates of `v` in `(v, a, b)`. -/
def vIdx (m : ℕ) (i : Fin m) : Fin (m + 2) := i.castSucc.castSucc

@[simp] theorem tup_last (v : Fin m → α) (a b : α) : tup v a b (Fin.last (m + 1)) = b := by
  simp [tup]

@[simp] theorem tup_pen (v : Fin m → α) (a b : α) : tup v a b (penIdx m) = a := by
  simp [tup, penIdx]

@[simp] theorem tup_vIdx (v : Fin m → α) (a b : α) (i : Fin m) : tup v a b (vIdx m i) = v i := by
  simp [tup, vIdx]

theorem tup_eta (p : Fin (m + 2) → α) :
    tup (p ∘ vIdx m) (p (penIdx m)) (p (Fin.last (m + 1))) = p := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · exact tup_pen _ _ _
    · exact tup_vIdx _ _ _ j

theorem comp_tup {γ : Type*} (f : α → γ) (v : Fin m → α) (a b : α) :
    f ∘ tup v a b = tup (f ∘ v) (f a) (f b) := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · exact (tup_pen (f ∘ v) (f a) (f b)).symm ▸ congrArg f (tup_pen v a b)
    · exact (tup_vIdx (f ∘ v) (f a) (f b) j).symm ▸ congrArg f (tup_vIdx v a b j)

theorem tup_comp_tup (v : Fin m → α) (a b : α) (x y : Fin (m + 2)) :
    tup v a b ∘ tup (vIdx m) x y = tup v (tup v a b x) (tup v a b y) := by
  rw [comp_tup]
  congr 1
  funext i
  simp

@[simp] theorem update_tup_last (v : Fin m → α) (a b w : α) :
    Function.update (tup v a b) (Fin.last (m + 1)) w = tup v a w := by
  simp [tup, Fin.update_snoc_last]

@[simp] theorem update_tup_pen (v : Fin m → α) (a b w : α) :
    Function.update (tup v a b) (penIdx m) w = tup v w b := by
  rw [tup, penIdx, ← Fin.snoc_update, Fin.update_snoc_last, tup]

end Projections

section WLProjections

variable {G : ColoredGraph} {m : ℕ}

/-- The projection `χ^v_r (a, b) = χ_r (v, a, b)`. -/
noncomputable def proj (G : ColoredGraph) (r : ℕ) (v : Fin m → Fin G.n) (a b : Fin G.n) :
    Color (m + 2) r :=
  color G r (tup v a b)

theorem proj_eq_of_succ {r : ℕ} {v w : Fin m → Fin G.n} {a b c d : Fin G.n}
    (h : proj G (r + 1) v a b = proj G (r + 1) w c d) : proj G r v a b = proj G r w c d :=
  color_eq_of_succ h

theorem proj_eq_iff {r : ℕ} {v w : Fin m → Fin G.n} {a b c d : Fin G.n}
    (h : proj G r v a b = proj G r w c d) : a = b ↔ c = d := by
  have := eq_iff_of_color_eq h (penIdx m) (Fin.last (m + 1))
  simpa using this

/-- Shuffling the coordinates of `(v, a, b)` by `(vIdx, x, y)`. -/
theorem proj_shuffle {r : ℕ} {v w : Fin m → Fin G.n} {a b c d : Fin G.n}
    (h : proj G r v a b = proj G r w c d) (x y : Fin (m + 2)) :
    proj G r v (tup v a b x) (tup v a b y) = proj G r w (tup w c d x) (tup w c d y) := by
  have := color_comp_eq r (tup (vIdx m) x y) h
  rwa [tup_comp_tup, tup_comp_tup] at this

theorem proj_swap {r : ℕ} {v w : Fin m → Fin G.n} {a b c d : Fin G.n}
    (h : proj G r v a b = proj G r w c d) : proj G r v b a = proj G r w d c := by
  simpa using proj_shuffle h (Fin.last (m + 1)) (penIdx m)

theorem one_mem_classSpace_proj (r : ℕ) (v : Fin m → Fin G.n) :
    (1 : Matrix (Fin G.n) (Fin G.n) ℂ) ∈ classSpace (proj G r v) :=
  one_mem_classSpace fun _ _ _ _ h => proj_eq_iff h

theorem star_mem_classSpace_proj (r : ℕ) (v : Fin m → Fin G.n)
    {M : Matrix (Fin G.n) (Fin G.n) ℂ} (hM : M ∈ classSpace (proj G r v)) :
    star M ∈ classSpace (proj G r v) :=
  star_mem_classSpace (fun _ _ _ _ h => proj_swap h) hM

theorem classSpace_proj_le_succ (r : ℕ) (v : Fin m → Fin G.n) :
    classSpace (proj G r v) ≤ classSpace (proj G (r + 1) v) :=
  classSpace_le fun _ _ _ _ h => proj_eq_of_succ h

/-- **Lemma 6.2** (multiplicativity): entry `(u, u')` of a product of two matrices constant on
the classes of `χ^v_r` is a sum over the multiset part of `χ_{r+1} (v, u, u')`. -/
theorem classSpace_proj_mul_le (r : ℕ) (v : Fin m → Fin G.n) :
    classSpace (proj G r v) * classSpace (proj G r v) ≤ classSpace (proj G (r + 1) v) := by
  rw [Submodule.mul_le]
  intro A hA B hB u u' c d h
  simp only [Matrix.mul_apply, Finset.sum_eq_multiset_sum]
  unfold proj at h
  rw [color_succ, color_succ] at h
  refine congrArg Multiset.sum
    (UpperBound.multiset_map_eq_of_map_eq (fun a b hab => ?_) _ _ (Prod.mk.inj h).2)
  have h1 := congrFun hab (Fin.last (m + 1))
  have h2 := congrFun hab (penIdx m)
  simp only [update_tup_last, update_tup_pen] at h1 h2
  rw [hA u a c b h1, hB a u' b d h2]

/-- **Lemma 6.4** (extendability). -/
theorem proj_succ_diag_ne {r : ℕ} {v w : Fin m → Fin G.n} {a b : Fin G.n}
    (h : ∀ x y, proj G r v a b ≠ proj G r w x y) (x : Fin G.n) :
    proj G (r + 1) v a a ≠ proj G (r + 1) w x x := by
  intro hx
  unfold proj at hx
  rw [color_succ, color_succ] at hx
  have h2 := (Prod.mk.inj hx).2
  have hmem : (fun i => color G r (Function.update (tup v a a) i b)) ∈
      (Finset.univ : Finset (Fin G.n)).val.map
        (fun q i => color G r (Function.update (tup v a a) i q)) :=
    Multiset.mem_map.2 ⟨b, Finset.mem_univ_val b, rfl⟩
  rw [h2] at hmem
  obtain ⟨y, -, hy⟩ := Multiset.mem_map.1 hmem
  have := congrFun hy (Fin.last (m + 1))
  simp only [update_tup_last] at this
  exact h x y this.symm

end WLProjections

end Lax119563Proofs.Stabilization
