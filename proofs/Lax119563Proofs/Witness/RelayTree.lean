import Lax119563Proofs.Witness.RelaySystem
import Lax119563Proofs.Witness.Counter
import Lax119563Proofs.Witness.Derivation

/-!
# No small contradiction tree (Lemma relay-tree)

Every contradiction tree of the relay counter has more than `2^(2^m - 1)` nodes. We use the
weights of Lemma oneway-tree-size: with `M = 2^(2^m - 1)` and `λ(X_{x,a}) =
2^(2^m - 1 - N(a))`, doubled at the locations `r_j`, a zero fact at `X` has weight `λ(X)` and a
one fact weight `M - λ(X)`. Equalities join variables of equal `λ`, and the ternary schemas
join variables with `λ` values `t, t, 2t` where `2t ≤ M`; so no inference increases weight,
initial facts have weight at most `1`, and opposite facts have weights summing to `M`.
-/

open Lax119563.ImplicitParitySystems Lax119563.ParitySystems Lax119563.ContradictionTrees

namespace Lax119563Proofs.Witness

open Finset

variable {V : Type*} [DecidableEq V]

/-- Weight of a fact with base value `l`. -/
def W (M l : ℕ) (b : ZMod 2) : ℕ := if b = 0 then l else M - l

theorem W_le_add (M t : ℕ) (h2 : 2 * t ≤ M) (x y : ZMod 2) :
    W M t (x + y) ≤ W M t x + W M (2 * t) y ∧ W M (2 * t) (x + y) ≤ W M t x + W M t y := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases y with rfl | rfl <;>
    simp only [W, h11, add_zero, zero_add, if_neg h10, eq_self_iff_true, if_true] <;>
    constructor <;> omega

theorem erase_pair_left {X Y : V} (h : X ≠ Y) : ({X, Y} : Finset V).erase X = {Y} :=
  Finset.erase_insert (by simpa using h)

theorem binary_ok (w : V × ZMod 2 → ℕ) {X Y : V} (hXY : X ≠ Y) (hw : ∀ b, w (X, b) = w (Y, b)) :
    ∀ Z ∈ ({X, Y} : Finset V), ∀ b : V → ZMod 2,
      w (Z, ∑ Y' ∈ ({X, Y} : Finset V).erase Z, b Y') ≤
        ∑ Y' ∈ ({X, Y} : Finset V).erase Z, w (Y', b Y') := by
  intro Z hZ b
  rw [Finset.mem_insert, Finset.mem_singleton] at hZ
  rcases hZ with rfl | rfl
  · rw [erase_pair_left hXY]; simp [hw]
  · rw [Finset.pair_comm, erase_pair_left hXY.symm]; simp [hw]

theorem ternary_ok (M t : ℕ) (h2 : 2 * t ≤ M) (lam : V → ℕ) {P Q R : V}
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) (hP : lam P = t) (hQ : lam Q = t)
    (hR : lam R = 2 * t) :
    ∀ Z ∈ ({P, Q, R} : Finset V), ∀ b : V → ZMod 2,
      W M (lam Z) (∑ Y' ∈ ({P, Q, R} : Finset V).erase Z, b Y') ≤
        ∑ Y' ∈ ({P, Q, R} : Finset V).erase Z, W M (lam Y') (b Y') := by
  intro Z hZ b
  simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
  rcases hZ with rfl | rfl | rfl
  · have : ({Z, Q, R} : Finset V).erase Z = {Q, R} :=
      Finset.erase_insert (by simp [hPQ, hPR])
    rw [this, sum_pair hQR, sum_pair hQR, hP, hQ, hR]
    exact (W_le_add M t h2 _ _).1
  · have : ({P, Z, R} : Finset V).erase Z = {P, R} := by
      rw [Finset.erase_insert_of_ne hPQ, Finset.erase_insert (by simpa using hQR)]
    rw [this, sum_pair hPR, sum_pair hPR, hP, hQ, hR]
    exact (W_le_add M t h2 _ _).1
  · have : ({P, Q, Z} : Finset V).erase Z = {P, Q} := by
      rw [Finset.erase_insert_of_ne hPR, Finset.erase_insert_of_ne hQR, Finset.erase_singleton,
        Finset.insert_empty]
    rw [this, sum_pair hPQ, sum_pair hPQ, hP, hQ, hR]
    exact (W_le_add M t h2 _ _).2

variable {k ℓ : ℕ}

/-- `1` at the locations `r_j`, `0` elsewhere. -/
def rbit : Fin 3 ⊕ (Fin (nbits k ℓ) × Fin 3) → ℕ
  | .inl _ => 0
  | .inr (_, c) => if c = 2 then 1 else 0

/-- The base weight `λ` of a variable. -/
def lam (X : Fin (nlocs k ℓ) × (Fin k → BlockCoord ℓ)) : ℕ :=
  2 ^ ((2 ^ nbits k ℓ - 1 - cval X.2) + rbit ((locEquiv _).symm X.1))

theorem lam_loc (σ) (a : Fin k → BlockCoord ℓ) :
    lam (loc k ℓ σ, a) = 2 ^ ((2 ^ nbits k ℓ - 1 - cval a) + rbit σ) := by
  simp [lam, loc]

/-- The bound `M = 2^(2^m - 1)`. -/
abbrev bigM (k ℓ : ℕ) : ℕ := 2 ^ (2 ^ nbits k ℓ - 1)

/-- The weight of a fact. -/
def wf (f : (Fin (nlocs k ℓ) × (Fin k → BlockCoord ℓ)) × ZMod 2) : ℕ :=
  W (bigM k ℓ) (lam f.1) f.2

theorem rbit_inl (i : Fin 3) : rbit (k := k) (ℓ := ℓ) (.inl i) = 0 := rfl

theorem rbit_r (j : Fin (nbits k ℓ)) : rbit (k := k) (ℓ := ℓ) (.inr (j, 2)) = 1 := rfl

theorem rbit_p (j : Fin (nbits k ℓ)) : rbit (k := k) (ℓ := ℓ) (.inr (j, 0)) = 0 := rfl

theorem rbit_q (j : Fin (nbits k ℓ)) : rbit (k := k) (ℓ := ℓ) (.inr (j, 1)) = 0 := rfl

theorem relay_hinit : ∀ f ∈ (relay k ℓ).toParitySystem.initial, wf f ≤ 1 := by
  rintro ⟨⟨x, a⟩, b⟩ ⟨b', hinit, hb, ha, hsupp⟩
  obtain rfl : b = b' := hb
  obtain ⟨σ, rfl⟩ : ∃ σ, x = loc k ℓ σ := ⟨(locEquiv _).symm x, ((locEquiv _).apply_symm_apply x).symm⟩
  change (relay k ℓ).init (loc k ℓ σ) = some b at hinit
  change supp a ⊆ (relay k ℓ).domain (loc k ℓ σ) at hsupp
  rw [relay_domain] at hsupp
  rw [relay_init] at hinit
  show W (bigM k ℓ) (lam (loc k ℓ σ, a)) b ≤ 1
  rcases σ with i | ⟨j, c⟩
  · fin_cases i
    · simp [initS] at hinit
    · simp [initS] at hinit
      subst hinit
      have := eq_of_supp_subset (by simpa [domS] using hsupp)
      subst this
      have hs := cval_sAddr (k := k) (ℓ := ℓ)
      rw [lam_loc, rbit_inl, show 2 ^ nbits k ℓ - 1 - cval (sAddr k ℓ) = 0 by omega]
      simp [W]
    · simp [initS] at hinit
      subst hinit
      have := eq_of_supp_subset (by simpa [domS] using hsupp)
      subst this
      have h10 : (1 : ZMod 2) ≠ 0 := by decide
      rw [lam_loc, rbit_inl, cval_zero]
      simp [W, h10]
  · simp [initS] at hinit

theorem relay_hM (X : Fin (nlocs k ℓ) × (Fin k → BlockCoord ℓ)) :
    bigM k ℓ ≤ wf (X, 0) + wf (X, 1) := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  show bigM k ℓ ≤ W (bigM k ℓ) (lam X) 0 + W (bigM k ℓ) (lam X) 1
  simp only [W, if_neg h10, eq_self_iff_true, if_true]
  omega

theorem relay_hinfer : ∀ h ∈ (relay k ℓ).toParitySystem.equations, ∀ X ∈ h,
    ∀ b : _ → ZMod 2, wf (X, ∑ Y ∈ h.erase X, b Y) ≤ ∑ Y ∈ h.erase X, wf (Y, b Y) := by
  rintro h ⟨e, he, a, ha, hsupp, rfl⟩
  have hbin : ∀ σ τ : Fin 3 ⊕ (Fin (nbits k ℓ) × Fin 3), σ ≠ τ → rbit σ = rbit τ →
      ∀ X ∈ ({(loc k ℓ σ, a), (loc k ℓ τ, a)} : Finset _), ∀ b : _ → ZMod 2,
        wf (X, ∑ Y ∈ ({(loc k ℓ σ, a), (loc k ℓ τ, a)} : Finset _).erase X, b Y) ≤
        ∑ Y ∈ ({(loc k ℓ σ, a), (loc k ℓ τ, a)} : Finset _).erase X, wf (Y, b Y) := by
    intro σ τ hστ hr
    apply binary_ok
    · intro heq; exact hστ (loc_inj.mp (congrArg Prod.fst heq))
    · intro b
      show W (bigM k ℓ) (lam (loc k ℓ σ, a)) b = W (bigM k ℓ) (lam (loc k ℓ τ, a)) b
      rw [lam_loc, lam_loc, hr]
  rcases mem_relaySchemas.mp he with he | ⟨j, he⟩
  · simp only [endpoints, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp only [Schema.equation, idP_act]
    · exact hbin _ _ (by simp) rfl
    · exact hbin _ _ (by simp) rfl
  · have hj : (j : ℕ) < (k - 1) * ℓ := j.2
    simp only [gate, List.mem_cons, List.not_mem_nil, or_false] at he
    have hsupp' : supp a ⊆ relayDom j := by
      rcases he with rfl | rfl | rfl | rfl <;> exact hsupp
    have hdec := cval_decP hj hsupp'
    have hpos : 1 ≤ cval a := by omega
    have hlt := cval_lt a
    rcases he with rfl | rfl | rfl | rfl
    · simp only [Schema.equation, idP_act]; exact hbin _ _ (by simp) rfl
    · simp only [Schema.equation, idP_act]; exact hbin _ _ (by simp) rfl
    · simp only [Schema.equation, idP_act]
      have h2t : 2 * 2 ^ (2 ^ nbits k ℓ - 1 - cval a) ≤ bigM k ℓ := by
        rw [← pow_succ']
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      exact ternary_ok (bigM k ℓ) (2 ^ (2 ^ nbits k ℓ - 1 - cval a)) h2t lam
        (P := (loc k ℓ (.inr (j, 0)), a)) (Q := (loc k ℓ (.inr (j, 1)), a))
        (R := (loc k ℓ (.inr (j, 2)), a)) (by simp [loc_inj]) (by simp [loc_inj])
        (by simp [loc_inj]) (by rw [lam_loc, rbit_p]; rfl) (by rw [lam_loc, rbit_q]; rfl)
        (by rw [lam_loc, rbit_r, pow_succ, mul_comm])
    · simp only [Schema.equation, idP_act]
      have hl : lam (loc k ℓ (.inr (j, 2)), a) = lam (loc k ℓ (.inl 0), (decP (j : ℕ)).act a) := by
        rw [lam_loc, lam_loc, rbit_r, rbit_inl]
        congr 1
        omega
      apply binary_ok
      · intro heq; exact absurd (loc_inj.mp (congrArg Prod.fst heq)) (by simp)
      · intro b
        show W (bigM k ℓ) (lam (loc k ℓ (.inr (j, 2)), a)) b =
          W (bigM k ℓ) (lam (loc k ℓ (.inl 0), (decP (j : ℕ)).act a)) b
        rw [hl]

/-- **No small contradiction tree.** Every contradiction tree of the relay counter has more
than `2^(2^m - 1)` nodes, where `m = (k-1)ℓ`. -/
theorem relay_tree_bound {s : ℕ} (h : HasContradictionWithin (relay k ℓ).toParitySystem s) :
    2 ^ (2 ^ nbits k ℓ - 1) < s :=
  lt_of_hasContradictionWithin _ wf relay_hinit relay_hinfer _ relay_hM h

end Lax119563Proofs.Witness
