import Mathlib
import Lax119563.ImplicitParitySystems

/-!
# The relay counter

We build the relay counter `Î^{k,ℓ}_ctr` as an implicit parity system. In contrast to the paper
we let the counter count *down*: bit `j` of the counter (`0 ≤ j < m = (k-1)ℓ`) is bit
`j / (k-1)` of block `j % (k-1)` (data bits read row by row), and the decrement `T_j` applies
to the addresses whose bits below `j` are `0` and whose bit `j` is `1`. Then all fixed bits of
the coordinate domain `𝔠'_j` are zero in the first `j / (k-1)` rows of every block, so the
corresponding checksum rows of the check matrix vanish on `𝔠'_j`.

Locations: the main location `v`, the endpoints `z₀, z₁`, and private locations
`p_j, q_j, r_j` for every bit position `j`; they are indexed by
`Fin 3 ⊕ (Fin m × Fin 3)` through `locEquiv`. Schemas: `X_{z₀,s} = X_{v,s}` and
`X_{z₁,0} = X_{v,0}` with `s` the address with all data bits `1`, and for every `j` the one-way
gate `X_{v,a} = X_{p_j,a}`, `X_{v,a} = X_{q_j,a}`, `X_{p_j,a} + X_{q_j,a} + X_{r_j,a} = 0`,
`X_{r_j,a} = X_{v,T_j a}`. The initialization is `ι(z₀) = 0`, `ι(z₁) = 1`.
-/

open Lax119563.ImplicitParitySystems Lax119563.ParitySystems

namespace Lax119563Proofs.Witness

variable {k ℓ : ℕ}

/-! ### Bit positions -/

theorem pos_lt {j : ℕ} (hj : j < (k - 1) * ℓ) : j % (k - 1) < k := by
  have hk : 0 < k - 1 := Nat.pos_of_ne_zero fun h => by simp [h] at hj
  have := Nat.mod_lt j hk
  omega

theorem row_lt {j : ℕ} (hj : j < (k - 1) * ℓ) : j / (k - 1) < ℓ := by
  rw [Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero fun h => by simp [h] at hj)]
  linarith [mul_comm (k - 1) ℓ]

/-- Bit `j` of the counter value of the array `a`: bit `j / (k-1)` of block `j % (k-1)`. -/
def bitVal (a : Fin k → BlockCoord ℓ) (j : ℕ) : ZMod 2 :=
  if hj : j < (k - 1) * ℓ then a ⟨j % (k - 1), pos_lt hj⟩ ⟨j / (k - 1), row_lt hj⟩ else 0

theorem pos_div {i t : ℕ} (hi : i < k - 1) : (t * (k - 1) + i) / (k - 1) = t := by
  have hk : 0 < k - 1 := by omega
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hi, zero_add]

theorem pos_mod {i t : ℕ} (hi : i < k - 1) : (t * (k - 1) + i) % (k - 1) = i := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

theorem pos_lt_m {i t : ℕ} (hi : i < k - 1) (ht : t < ℓ) : t * (k - 1) + i < (k - 1) * ℓ := by
  have : (t + 1) * (k - 1) ≤ ℓ * (k - 1) := Nat.mul_le_mul_right _ ht
  rw [mul_comm (k - 1) ℓ]
  nlinarith

theorem bitVal_pos (a : Fin k → BlockCoord ℓ) (i : Fin k) (t : Fin ℓ) (hi : (i : ℕ) < k - 1) :
    bitVal a (t * (k - 1) + i) = a i t := by
  unfold bitVal
  rw [dif_pos (pos_lt_m hi t.2)]
  exact congrArg₂ (fun x y => a x y) (Fin.ext (pos_mod hi)) (Fin.ext (pos_div hi))

/-- The counter value `N(a) = ∑_{j<m} bit_j(a) 2^j`. -/
def cval (a : Fin k → BlockCoord ℓ) : ℕ :=
  ∑ j ∈ Finset.range ((k - 1) * ℓ), (bitVal a j).val * 2 ^ j

/-! ### Checksums -/

/-- The array with data blocks `d i` (`i < k - 1`) and last block the sum of these. -/
def withChecksum (d : Fin k → BlockCoord ℓ) : Fin k → BlockCoord ℓ := fun i =>
  if (i : ℕ) < k - 1 then d i else ∑ i' ∈ Finset.univ.filter (fun i' : Fin k => (i' : ℕ) < k - 1), d i'

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by revert x; decide

theorem sum_withChecksum (d : Fin k → BlockCoord ℓ) : ∑ i, withChecksum d i = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hlast : Finset.univ.filter (fun i : Fin k => ¬ (i : ℕ) < k - 1) = {⟨k - 1, by omega⟩} := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; ext; simp; omega
    · rintro rfl; simp
  unfold withChecksum
  rw [Finset.sum_ite, hlast, Finset.sum_singleton]
  exact zmod2_add_self' _
where
  zmod2_add_self' (x : BlockCoord ℓ) : x + x = 0 := by
    funext t; exact zmod2_add_self (x t)

theorem isAddress_withChecksum (d : Fin k → BlockCoord ℓ) : IsAddress (withChecksum d) :=
  sum_withChecksum d

theorem zmod2_eq_of_add (x y : ZMod 2) (h : x + y = 0) : x = y := by
  revert x y; decide

/-- The last block of an address is the sum of its data blocks. -/
theorem last_eq_of_isAddress {a : Fin k → BlockCoord ℓ} (ha : IsAddress a) (i : Fin k)
    (hi : ¬ (i : ℕ) < k - 1) (t : Fin ℓ) :
    a i t = ∑ i' ∈ Finset.univ.filter (fun i' : Fin k => (i' : ℕ) < k - 1), a i' t := by
  have hlast : Finset.univ.filter (fun i : Fin k => ¬ (i : ℕ) < k - 1) = {i} := by
    ext i'; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; ext; omega
    · rintro rfl; exact hi
  have h := congrFun ha t
  simp only [Finset.sum_apply, Pi.zero_apply] at h
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun i' : Fin k => (i' : ℕ) < k - 1), hlast,
    Finset.sum_singleton] at h
  exact (zmod2_eq_of_add _ _ (by rw [add_comm]; exact h))

/-- The start address `s`: all data bits `1`. -/
def sAddr (k ℓ : ℕ) : Fin k → BlockCoord ℓ := withChecksum fun _ _ => 1

/-! ### Block-induced permutations -/

theorem perm_one_symm (i : Fin k) : (1 : Equiv.Perm (Fin k)).symm i = i := rfl

/-- The identity block-induced permutation. -/
def idP : BlockPerm k ℓ := ⟨1, 0, by simp⟩

@[simp] theorem idP_act (a : Fin k → BlockCoord ℓ) : (idP : BlockPerm k ℓ).act a = a := by
  funext i; simp [BlockPerm.act, idP, perm_one_symm]

@[simp] theorem idP_apply (c : Coord k ℓ) : (idP : BlockPerm k ℓ).apply c = c := by
  simp [BlockPerm.apply, idP]

/-- The flips of the decrement `T_j` in the data blocks: all bits up to `j`. -/
def decFlip (j : ℕ) : Fin k → BlockCoord ℓ := fun i t =>
  if (t : ℕ) * (k - 1) + i ≤ j then 1 else 0

/-- The decrement `T_j`, a translation of the addresses. -/
def decP (j : ℕ) : BlockPerm k ℓ := ⟨1, withChecksum (decFlip j), sum_withChecksum _⟩

theorem decP_act (j : ℕ) (a : Fin k → BlockCoord ℓ) :
    (decP j).act a = a + withChecksum (decFlip j) := by
  funext i; simp [BlockPerm.act, decP, perm_one_symm]

theorem isAddress_act {π : BlockPerm k ℓ} {a : Fin k → BlockCoord ℓ} (ha : IsAddress a) :
    IsAddress (π.act a) := by
  unfold IsAddress BlockPerm.act at *
  rw [Finset.sum_add_distrib, Equiv.sum_comp π.perm.symm a,
    Equiv.sum_comp π.perm.symm π.shift, ha, π.sum_shift, add_zero]

/-! ### Coordinate domains -/

/-- The coordinate domain `𝔠'_j`: in the data blocks, bits below position `j` are `0` and bit
`j` is `1`; in the checksum block, the first `j / (k-1)` bits are `0`. -/
def relayDom (j : ℕ) : Finset (Coord k ℓ) := Finset.univ.filter fun c =>
  if (c.1 : ℕ) < k - 1 then
    (∀ t : Fin ℓ, (t : ℕ) * (k - 1) + c.1 < j → c.2 t = 0) ∧
      (∀ t : Fin ℓ, (t : ℕ) * (k - 1) + c.1 = j → c.2 t = 1)
  else ∀ t : Fin ℓ, (t : ℕ) < j / (k - 1) → c.2 t = 0

theorem supp_subset_iff {a : Fin k → BlockCoord ℓ} {D : Finset (Coord k ℓ)} :
    supp a ⊆ D ↔ ∀ i, (i, a i) ∈ D := by
  simp [supp, Finset.image_subset_iff]

theorem eq_of_supp_subset {a b : Fin k → BlockCoord ℓ} (h : supp a ⊆ supp b) : a = b := by
  funext i
  have := supp_subset_iff.mp h i
  simp only [supp, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq] at this
  obtain ⟨i', rfl, h'⟩ := this
  exact h'.symm

/-! ### Locations -/

/-- Indices of the locations: `inl 0, inl 1, inl 2` are `v, z₀, z₁`; `inr (j, 0/1/2)` are
`p_j, q_j, r_j`. -/
def locEquiv (m : ℕ) : Fin 3 ⊕ (Fin m × Fin 3) ≃ Fin (3 + m * 3) :=
  (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv

/-- The number `m = (k-1)ℓ` of counter bits. -/
abbrev nbits (k ℓ : ℕ) : ℕ := (k - 1) * ℓ

/-- The number of locations. -/
abbrev nlocs (k ℓ : ℕ) : ℕ := 3 + nbits k ℓ * 3

/-- The location with index `σ`. -/
def loc (k ℓ : ℕ) (σ : Fin 3 ⊕ (Fin (nbits k ℓ) × Fin 3)) : Fin (nlocs k ℓ) := locEquiv _ σ

theorem loc_inj {σ σ' : Fin 3 ⊕ (Fin (nbits k ℓ) × Fin 3)} : loc k ℓ σ = loc k ℓ σ' ↔ σ = σ' :=
  (locEquiv _).apply_eq_iff_eq

/-- The coordinate domain of a location index. -/
def domS (k ℓ : ℕ) : Fin 3 ⊕ (Fin (nbits k ℓ) × Fin 3) → Finset (Coord k ℓ)
  | .inl i => ![Finset.univ, supp (sAddr k ℓ), supp 0] i
  | .inr (j, _) => relayDom j

/-- The initialization of a location index. -/
def initS (k ℓ : ℕ) : Fin 3 ⊕ (Fin (nbits k ℓ) × Fin 3) → Option (ZMod 2)
  | .inl i => ![none, some 0, some 1] i
  | .inr _ => none

/-- The four schemas of the one-way gate at bit position `j`. -/
def gate (j : Fin (nbits k ℓ)) : List (Schema k ℓ (nlocs k ℓ)) :=
  [.binary (loc k ℓ (.inl 0)) (loc k ℓ (.inr (j, 0))) (relayDom j) idP idP,
   .binary (loc k ℓ (.inl 0)) (loc k ℓ (.inr (j, 1))) (relayDom j) idP idP,
   .ternary (loc k ℓ (.inr (j, 0))) (loc k ℓ (.inr (j, 1))) (loc k ℓ (.inr (j, 2)))
      (relayDom j) idP idP idP,
   .binary (loc k ℓ (.inr (j, 2))) (loc k ℓ (.inl 0)) (relayDom j) idP (decP j)]

/-- The two endpoint schemas. -/
def endpoints (k ℓ : ℕ) : List (Schema k ℓ (nlocs k ℓ)) :=
  [.binary (loc k ℓ (.inl 1)) (loc k ℓ (.inl 0)) (supp (sAddr k ℓ)) idP idP,
   .binary (loc k ℓ (.inl 2)) (loc k ℓ (.inl 0)) (supp 0) idP idP]

/-- All schemas of the relay counter. -/
def relaySchemas (k ℓ : ℕ) : List (Schema k ℓ (nlocs k ℓ)) :=
  endpoints k ℓ ++ (List.finRange (nbits k ℓ)).flatMap gate

theorem mem_relaySchemas {e : Schema k ℓ (nlocs k ℓ)} :
    e ∈ relaySchemas k ℓ ↔ e ∈ endpoints k ℓ ∨ ∃ j, e ∈ gate j := by
  simp [relaySchemas, List.mem_flatMap]

end Lax119563Proofs.Witness
