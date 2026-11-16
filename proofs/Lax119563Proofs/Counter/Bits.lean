import Mathlib
import Lax119563.ImplicitParitySystems

/-!
# Counter values of addresses

We fix `k = K + 1` blocks and block coordinates in `𝔽₂^ℓ`. The first `K` blocks are the
*data blocks*, the last block is the checksum block. The `m = ℓ K` data bits of an array `a`
are read row by row: data position `p = i + K t` (with `i < K`, `t < ℓ`) is bit `t` of the
block coordinate `a_i`. The *counter value* of `a` is `∑_p a_p 2^p`.

The increment at position `j` adds the shift `δ_j` flipping all data positions `≤ j` (and
updating the checksum accordingly). On arrays whose data word starts with `1^j 0`, it
increases the counter value by one.
-/

open Lax119563.ImplicitParitySystems

namespace Lax119563Proofs.Counter

variable {K ℓ : ℕ}

/-- Arrays of block coordinates with `K + 1` blocks. -/
abbrev Arr (K ℓ : ℕ) := Fin (K + 1) → BlockCoord ℓ

/-- The data position `i + K t` of row `t` and data block `i`. -/
def pos (K ℓ : ℕ) : Fin ℓ × Fin K ≃ Fin (ℓ * K) := finProdFinEquiv

theorem pos_val (x : Fin ℓ × Fin K) : (pos K ℓ x : ℕ) = x.2 + K * x.1 := by
  simp [pos, finProdFinEquiv_apply_val]

/-- The data bit at data position `p`. -/
def dbit (a : Arr K ℓ) (p : Fin (ℓ * K)) : ZMod 2 :=
  a (Fin.castSucc ((pos K ℓ).symm p).2) ((pos K ℓ).symm p).1

theorem dbit_pos (a : Arr K ℓ) (t : Fin ℓ) (i : Fin K) :
    dbit a (pos K ℓ (t, i)) = a (Fin.castSucc i) t := by
  simp [dbit]

/-- The counter value of an array. -/
def val (a : Arr K ℓ) : ℕ :=
  ∑ p : Fin (ℓ * K), (dbit a p).val * 2 ^ (p : ℕ)

/-- The data part of the shift `δ_j`: ones at all data positions `≤ j`. -/
def dataShift (K ℓ j : ℕ) (i : Fin K) : BlockCoord ℓ :=
  fun t => if (pos K ℓ (t, i) : ℕ) ≤ j then 1 else 0

/-- The shift `δ_j`, completed by the checksum. -/
def shift (K ℓ j : ℕ) : Arr K ℓ :=
  Fin.snoc (α := fun _ => BlockCoord ℓ) (dataShift K ℓ j) (∑ i, dataShift K ℓ j i)

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

theorem blockCoord_add_self (x : BlockCoord ℓ) : x + x = 0 := by
  funext t
  exact zmod2_add_self (x t)

theorem zmod2_val_one : (1 : ZMod 2).val = 1 := rfl

theorem zmod2_eq_one_of_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl h
  · rfl

theorem sum_shift (j : ℕ) : ∑ i, shift K ℓ j i = 0 := by
  rw [Fin.sum_univ_castSucc]
  simp only [shift, Fin.snoc_castSucc, Fin.snoc_last]
  exact blockCoord_add_self _

theorem dbit_add (a b : Arr K ℓ) (p : Fin (ℓ * K)) : dbit (a + b) p = dbit a p + dbit b p := rfl

theorem dbit_shift (j : ℕ) (p : Fin (ℓ * K)) :
    dbit (shift K ℓ j) p = if (p : ℕ) ≤ j then 1 else 0 := by
  simp [dbit, shift, dataShift]

/-- An array is an address iff its checksum block is the sum of its data blocks. -/
theorem last_eq_of_isAddress {a : Arr K ℓ} (ha : IsAddress a) :
    a (Fin.last K) = ∑ i : Fin K, a (Fin.castSucc i) := by
  unfold IsAddress at ha
  rw [Fin.sum_univ_castSucc] at ha
  have := congrArg (· + a (Fin.last K)) ha
  simp only [add_assoc, blockCoord_add_self, add_zero, zero_add] at this
  exact this.symm

theorem isAddress_add {a b : Arr K ℓ} (ha : IsAddress a) (hb : IsAddress b) :
    IsAddress (a + b) := by
  unfold IsAddress at *
  simp [Finset.sum_add_distrib, ha, hb]

theorem isAddress_shift (j : ℕ) : IsAddress (shift K ℓ j) := sum_shift j

/-- Addresses are determined by their data bits. -/
theorem eq_zero_of_dbit {a : Arr K ℓ} (ha : IsAddress a) (h : ∀ p, dbit a p = 0) : a = 0 := by
  have hd : ∀ i : Fin K, a (Fin.castSucc i) = 0 := by
    intro i
    funext t
    show a (Fin.castSucc i) t = 0
    rw [← dbit_pos a t i]
    exact h _
  funext i
  refine Fin.lastCases ?_ (fun i => hd i) i
  rw [last_eq_of_isAddress ha]
  simp [hd]

/-! ### Geometric sums -/

theorem geom_two (j : ℕ) : ∑ n ∈ Finset.range j, 2 ^ n + 1 = 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [Finset.sum_range_succ, pow_succ]; omega

theorem sum_range_ite_lt {m j : ℕ} (hj : j ≤ m) :
    ∑ n ∈ Finset.range m, (if n < j then 2 ^ n else 0) = ∑ n ∈ Finset.range j, 2 ^ n := by
  induction m, hj using Nat.le_induction with
  | base => exact Finset.sum_congr rfl fun n hn => if_pos (Finset.mem_range.mp hn)
  | succ m hm ih => rw [Finset.sum_range_succ, ih, if_neg (by omega), add_zero]

theorem sum_fin_ite_lt {m j : ℕ} (hj : j ≤ m) :
    ∑ p : Fin m, (if (p : ℕ) < j then 2 ^ (p : ℕ) else 0) + 1 = 2 ^ j := by
  rw [Fin.sum_univ_eq_sum_range (fun n => if n < j then 2 ^ n else 0) m, sum_range_ite_lt hj,
    geom_two]

/-- Arrays whose data word starts with `1^j 0`. -/
def Prefix (j : ℕ) (a : Arr K ℓ) : Prop :=
  ∀ p : Fin (ℓ * K), (p : ℕ) ≤ j → dbit a p = if (p : ℕ) < j then 1 else 0

/-- **Increment.** Adding `δ_j` to an array with data prefix `1^j 0` increases the counter
value by one. -/
theorem val_add_shift {j : ℕ} (hj : j < ℓ * K) {a : Arr K ℓ} (ha : Prefix j a) :
    val (a + shift K ℓ j) = val a + 1 := by
  have hpt : ∀ p : Fin (ℓ * K),
      (dbit (a + shift K ℓ j) p).val * 2 ^ (p : ℕ) + (if (p : ℕ) < j then 2 ^ (p : ℕ) else 0) =
        (dbit a p).val * 2 ^ (p : ℕ) + (if (p : ℕ) = j then 2 ^ (p : ℕ) else 0) := by
    intro p
    rw [dbit_add, dbit_shift]
    rcases lt_trichotomy (p : ℕ) j with h | h | h
    · rw [ha p h.le, if_pos h, if_pos h.le, if_pos h, if_neg h.ne]
      simp [zmod2_add_self, zmod2_val_one]
    · rw [ha p h.le, if_neg (by omega), if_pos h.le, if_neg (by omega), if_pos h]
      simp [zmod2_val_one]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp
  have hsum := Finset.sum_congr rfl (fun p (_ : p ∈ Finset.univ) => hpt p)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have h1 := sum_fin_ite_lt (m := ℓ * K) hj.le
  have h2 : ∑ p : Fin (ℓ * K), (if (p : ℕ) = j then 2 ^ (p : ℕ) else 0) = 2 ^ j := by
    rw [Finset.sum_eq_single ⟨j, hj⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      exact fun h => hb (Fin.ext h)
    · simp
  unfold val
  omega

/-! ### The all-ones address -/

/-- The address `t` with all data bits `1`. -/
def top (K ℓ : ℕ) : Arr K ℓ :=
  Fin.snoc (α := fun _ => BlockCoord ℓ) (fun _ _ => 1) (fun _ => (K : ZMod 2))

theorem isAddress_top : IsAddress (top K ℓ) := by
  unfold IsAddress
  rw [Fin.sum_univ_castSucc]
  simp only [top, Fin.snoc_castSucc, Fin.snoc_last]
  funext t
  simp [zmod2_add_self]

theorem dbit_top (p : Fin (ℓ * K)) : dbit (top K ℓ) p = 1 := by
  simp [dbit, top]

theorem val_top : val (top K ℓ) + 1 = 2 ^ (ℓ * K) := by
  have := sum_fin_ite_lt (m := ℓ * K) (j := ℓ * K) le_rfl
  unfold val
  simp only [dbit_top, zmod2_val_one, one_mul]
  simpa using this

theorem val_zero : val (0 : Arr K ℓ) = 0 := by
  simp [val, dbit]

end Lax119563Proofs.Counter
