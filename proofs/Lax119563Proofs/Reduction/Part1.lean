import Lax119563.ContradictionTrees
import Lax119563.ImplicitParitySystems
import Lax119563.RowSpaceCompiler
import Lax119563.WeisfeilerLeman
import Lax119563Proofs.Circuits.Part1
import Lax119563Proofs.Hardness.Part1
import Lax119563Proofs.Programs.Part1
import Mathlib

/-! ### Formerly `Lax119563Proofs.Witness.Derivation` -/

section Witness_Derivation

/-!
# Derivation trees, weights, and rounds

Generic facts about a parity system `P`:

* a *weight* on facts that is at most `1` on initial facts and subadditive along every
  inference bounds the size of every derivation tree from below; if opposite facts have
  weights summing to at least `M`, every contradiction tree has more than `M` nodes;
* a fact known after round `r` has a derivation tree with at most `2^(r+1) - 1` nodes, so a
  conflict in round `r` gives a contradiction tree with at most `2^(r+2) - 1` nodes;
* the conflict round is `Nat.find` of the existence of a conflict.
-/

open Lax119563.ParitySystems Lax119563.ContradictionTrees

namespace Lax119563Proofs.Witness

variable {V : Type*} [DecidableEq V]

theorem hasDerivationWithin_mono {P : ParitySystem V} {f : V × ZMod 2} {s s' : ℕ}
    (h : HasDerivationWithin P f s) (hs : s ≤ s') : HasDerivationWithin P f s' := by
  cases h with
  | initial hf h1 => exact .initial hf (by omega)
  | infer b size hh hX ch hs0 => exact .infer b size hh hX ch (by omega)

section Weight

variable (P : ParitySystem V) (w : V × ZMod 2 → ℕ)

/-- A weight on facts which is at most `1` on initial facts and does not increase along
inferences bounds the size of derivation trees from below. -/
theorem weight_le_of_derivation (hinit : ∀ f ∈ P.initial, w f ≤ 1)
    (hinfer : ∀ h ∈ P.equations, ∀ X ∈ h, ∀ b : V → ZMod 2,
      w (X, ∑ Y ∈ h.erase X, b Y) ≤ ∑ Y ∈ h.erase X, w (Y, b Y))
    {f : V × ZMod 2} {s : ℕ} (hd : HasDerivationWithin P f s) : w f ≤ s := by
  induction hd with
  | initial hf hs => exact (hinit _ hf).trans hs
  | @infer X h s b size hh hX children hs ih =>
    calc w (X, ∑ Y ∈ h.erase X, b Y) ≤ ∑ Y ∈ h.erase X, w (Y, b Y) := hinfer _ hh _ hX b
      _ ≤ ∑ Y ∈ h.erase X, size Y := Finset.sum_le_sum fun Y hY => ih Y hY
      _ ≤ s := by omega

/-- With such a weight, if opposite facts have weights summing to at least `M`, every
contradiction tree has more than `M` nodes. -/
theorem lt_of_hasContradictionWithin (hinit : ∀ f ∈ P.initial, w f ≤ 1)
    (hinfer : ∀ h ∈ P.equations, ∀ X ∈ h, ∀ b : V → ZMod 2,
      w (X, ∑ Y ∈ h.erase X, b Y) ≤ ∑ Y ∈ h.erase X, w (Y, b Y))
    (M : ℕ) (hM : ∀ X, M ≤ w (X, 0) + w (X, 1)) {s : ℕ} (h : HasContradictionWithin P s) :
    M < s := by
  obtain ⟨X, s₀, s₁, h₀, h₁, hs⟩ := h
  have := weight_le_of_derivation P w hinit hinfer h₀
  have := weight_le_of_derivation P w hinit hinfer h₁
  have := hM X
  omega

end Weight

section Rounds

variable (P : ParitySystem V)

theorem known_mono {r s : ℕ} (h : r ≤ s) : P.known r ⊆ P.known s := by
  induction s, h using Nat.le_induction with
  | base => exact le_rfl
  | succ s _ ih => exact ih.trans fun f hf => Or.inl hf

theorem derivation_of_known :
    ∀ r : ℕ, ∀ f ∈ P.known r, HasDerivationWithin P f (2 ^ (r + 1) - 1) := by
  intro r
  induction r with
  | zero =>
    intro f hf
    exact .initial hf (by norm_num)
  | succ r ih =>
    intro f hf
    rcases hf with hf | ⟨h, hh, hX, b, hb, hval⟩
    · exact hasDerivationWithin_mono (ih f hf)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) (by omega)) 1)
    · obtain ⟨X, c⟩ := f
      simp only at hX hb hval
      subst hval
      refine .infer b (fun _ => 2 ^ (r + 1) - 1) hh hX (fun Y hY => ?_) ?_
      · exact ih _ (hb Y (Finset.mem_of_mem_erase hY) (Finset.ne_of_mem_erase hY))
      · rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hX]
        have hc : h.card ≤ 3 := by rcases P.card_equation h hh with h2 | h3 <;> omega
        have hp : 1 ≤ 2 ^ (r + 1) := Nat.one_le_two_pow
        have : (h.card - 1) * (2 ^ (r + 1) - 1) ≤ 2 * (2 ^ (r + 1) - 1) :=
          Nat.mul_le_mul_right _ (by omega)
        rw [pow_succ 2 (r + 1)]
        omega

theorem hasContradictionWithin_of_hasConflict {r : ℕ} (h : P.HasConflict r) :
    HasContradictionWithin P (2 ^ (r + 2) - 1) := by
  obtain ⟨X, h₀, h₁⟩ := h
  refine ⟨X, _, _, derivation_of_known P r _ h₀, derivation_of_known P r _ h₁, ?_⟩
  have hp : 1 ≤ 2 ^ (r + 1) := Nat.one_le_two_pow
  rw [pow_succ 2 (r + 1)]
  omega

theorem exists_conflictRound_eq (h : ∃ r, P.HasConflict r) :
    ∃ τ : ℕ, P.conflictRound = τ ∧ P.HasConflict τ := by
  classical
  refine ⟨Nat.find h, ?_, Nat.find_spec h⟩
  unfold ParitySystem.conflictRound
  apply le_antisymm
  · exact iInf₂_le _ (Nat.find_spec h)
  · exact le_iInf₂ fun r hr => by exact_mod_cast Nat.find_min' h hr

end Rounds

end Lax119563Proofs.Witness

end Witness_Derivation

/-! ### Formerly `Lax119563Proofs.Witness.Relay` -/

section Witness_Relay

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

end Witness_Relay

/-! ### Formerly `Lax119563Proofs.Witness.Counter` -/

section Witness_Counter

/-!
# Counter values

Facts about the counter value `cval a = ∑_{j<m} bit_j(a) 2^j`: it is below `2^m`, the start
address has value `2^m - 1`, the zero address has value `0`, and the decrement `T_j` lowers the
value of every address allowed in `𝔠'_j` by one.
-/

open Lax119563.ImplicitParitySystems

namespace Lax119563Proofs.Witness

open Finset

variable {k ℓ : ℕ}

theorem geom_two (n : ℕ) : ∑ i ∈ range n, 2 ^ i + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, pow_succ]; omega

theorem bitVal_of_ge (a : Fin k → BlockCoord ℓ) {j : ℕ} (hj : ¬ j < (k - 1) * ℓ) :
    bitVal a j = 0 := by
  simp [bitVal, hj]

theorem cval_lt (a : Fin k → BlockCoord ℓ) : cval a < 2 ^ nbits k ℓ := by
  have : cval a ≤ ∑ i ∈ range (nbits k ℓ), 2 ^ i := by
    unfold cval
    refine sum_le_sum fun i _ => ?_
    have := ZMod.val_lt (bitVal a i)
    calc (bitVal a i).val * 2 ^ i ≤ 1 * 2 ^ i := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ i := one_mul _
  have := geom_two (nbits k ℓ)
  omega

theorem cval_zero : cval (0 : Fin k → BlockCoord ℓ) = 0 := by
  simp [cval, bitVal]

/-- The data block of a bit position is a data block. -/
theorem pos_lt_data {j : ℕ} (hj : j < (k - 1) * ℓ) : j % (k - 1) < k - 1 :=
  Nat.mod_lt j (Nat.pos_of_ne_zero fun h => by simp [h] at hj)

@[simp] theorem zmod2_val_one : (1 : ZMod 2).val = 1 := rfl

@[simp] theorem zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := rfl

theorem bitVal_withChecksum (d : Fin k → BlockCoord ℓ) {j : ℕ} (hj : j < (k - 1) * ℓ) :
    bitVal (withChecksum d) j = bitVal d j := by
  simp [bitVal, hj, withChecksum, pos_lt_data hj]

theorem cval_sAddr : cval (sAddr k ℓ) + 1 = 2 ^ nbits k ℓ := by
  rw [← geom_two]
  congr 1
  unfold cval
  refine sum_congr rfl fun i hi => ?_
  rw [mem_range] at hi
  rw [sAddr, bitVal_withChecksum _ hi]
  simp [bitVal, hi]

/-- Decreasing a binary number by one: `f` has bits `0…01` up to position `j`, `g` has bits
`1…10`, and they agree above. -/
theorem sum_dec (f g : ℕ → ℕ) (j : ℕ) (hlt : ∀ i < j, f i = 0 ∧ g i = 1)
    (hj : f j = 1 ∧ g j = 0) (hgt : ∀ i, j < i → f i = g i) :
    ∀ n, j < n → ∑ i ∈ range n, f i * 2 ^ i = ∑ i ∈ range n, g i * 2 ^ i + 1 := by
  have low : ∀ n ≤ j, ∑ i ∈ range n, f i * 2 ^ i = 0 ∧
      ∑ i ∈ range n, g i * 2 ^ i + 1 = 2 ^ n := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      obtain ⟨hf, hg⟩ := hlt n (by omega)
      rw [sum_range_succ, sum_range_succ, h1, hf, hg, pow_succ]
      omega
  intro n hn
  obtain ⟨d, rfl⟩ : ∃ d, n = j + 1 + d := ⟨n - (j + 1), by omega⟩
  induction d with
  | zero =>
    obtain ⟨h1, h2⟩ := low j le_rfl
    rw [add_zero, sum_range_succ, sum_range_succ, h1, hj.1, hj.2]
    omega
  | succ d ih =>
    rw [← add_assoc, sum_range_succ, sum_range_succ, ih (by omega), hgt (j + 1 + d) (by omega)]
    ring

theorem bitVal_add (a d : Fin k → BlockCoord ℓ) (j : ℕ) :
    bitVal (a + d) j = bitVal a j + bitVal d j := by
  unfold bitVal; split_ifs <;> simp

theorem bitVal_decFlip {j j' : ℕ} (hj' : j' < (k - 1) * ℓ) :
    bitVal (decFlip (k := k) (ℓ := ℓ) j) j' = if j' ≤ j then 1 else 0 := by
  simp only [bitVal, hj', dif_pos, decFlip]
  rw [Nat.div_add_mod']

/-- An address allowed in `𝔠'_j` has bits `0` below `j` and bit `1` at `j`. -/
theorem bitVal_of_allowed {a : Fin k → BlockCoord ℓ} {j : ℕ} (h : supp a ⊆ relayDom j)
    {j' : ℕ} (hj' : j' < (k - 1) * ℓ) :
    (j' < j → bitVal a j' = 0) ∧ (j' = j → bitVal a j' = 1) := by
  have hmem := supp_subset_iff.mp h ⟨j' % (k - 1), pos_lt hj'⟩
  simp only [relayDom, mem_filter, mem_univ, true_and] at hmem
  rw [if_pos (pos_lt_data hj')] at hmem
  have e : (j' / (k - 1)) * (k - 1) + j' % (k - 1) = j' := Nat.div_add_mod' j' (k - 1)
  simp only [bitVal, hj', dif_pos]
  exact ⟨fun hlt => hmem.1 ⟨j' / (k - 1), row_lt hj'⟩ (by simp only; omega),
    fun heq => hmem.2 ⟨j' / (k - 1), row_lt hj'⟩ (by simp only; omega)⟩

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by revert x; decide

/-- The decrement `T_j` lowers the counter value of an allowed address by one. -/
theorem cval_decP {a : Fin k → BlockCoord ℓ} {j : ℕ} (hj : j < (k - 1) * ℓ)
    (h : supp a ⊆ relayDom j) : cval ((decP j).act a) + 1 = cval a := by
  rw [decP_act]
  unfold cval
  have hbit : ∀ i, bitVal (a + withChecksum (decFlip j)) i =
      bitVal a i + if i < (k - 1) * ℓ ∧ i ≤ j then 1 else 0 := by
    intro i
    rw [bitVal_add]
    by_cases hi : i < (k - 1) * ℓ
    · rw [bitVal_withChecksum _ hi, bitVal_decFlip hi]; simp [hi]
    · simp [bitVal_of_ge _ hi, hi]
  symm
  apply sum_dec (fun i => (bitVal a i).val) (fun i => (bitVal (a + withChecksum (decFlip j)) i).val) j
  · intro i hi
    rw [hbit, (bitVal_of_allowed h (by omega)).1 hi]
    simp [show i < (k - 1) * ℓ by omega, hi.le]
  · rw [hbit, (bitVal_of_allowed h hj).2 rfl]
    simp [hj]
  · intro i hi
    rw [hbit]; simp [show ¬ i ≤ j by omega]
  · exact hj

/-- The lowest set bit: every address of nonzero value is allowed in some `𝔠'_j`. -/
theorem exists_allowed {a : Fin k → BlockCoord ℓ} (ha : IsAddress a) (hpos : cval a ≠ 0) :
    ∃ j < (k - 1) * ℓ, supp a ⊆ relayDom j := by
  have hex : ∃ j, j < (k - 1) * ℓ ∧ bitVal a j = 1 := by
    by_contra hcon
    push_neg at hcon
    apply hpos
    unfold cval
    refine sum_eq_zero fun i hi => ?_
    rcases zmod2_cases (bitVal a i) with h0 | h1
    · simp [h0]
    · exact absurd h1 (hcon i (mem_range.mp hi))
  classical
  let j := Nat.find hex
  have hj : j < (k - 1) * ℓ ∧ bitVal a j = 1 := Nat.find_spec hex
  have hmin : ∀ i < j, bitVal a i = 0 := by
    intro i hi
    have := Nat.find_min hex hi
    rcases zmod2_cases (bitVal a i) with h0 | h1
    · exact h0
    · exact absurd ⟨by omega, h1⟩ this
  refine ⟨j, hj.1, supp_subset_iff.mpr fun i => ?_⟩
  simp only [relayDom, mem_filter, mem_univ, true_and]
  split_ifs with hi
  · refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · rw [← bitVal_pos a i t hi]; exact hmin _ ht
    · rw [← bitVal_pos a i t hi, ht]; exact hj.2
  · intro t ht
    rw [last_eq_of_isAddress ha i hi t]
    refine sum_eq_zero fun i' hi' => ?_
    rw [mem_filter] at hi'
    rw [← bitVal_pos a i' t hi'.2]
    apply hmin
    have h1 : (t + 1) * (k - 1) ≤ j / (k - 1) * (k - 1) := Nat.mul_le_mul_right _ ht
    have h2 := Nat.div_mul_le_self j (k - 1)
    nlinarith

/-- The only address of value `0` is the zero address. -/
theorem eq_zero_of_cval {a : Fin k → BlockCoord ℓ} (ha : IsAddress a) (h0 : cval a = 0) :
    a = 0 := by
  have hbit : ∀ j, bitVal a j = 0 := by
    intro j
    by_cases hj : j < (k - 1) * ℓ
    · have := (sum_eq_zero_iff.mp h0) j (mem_range.mpr hj)
      simp only [mul_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and,
        or_false] at this
      exact (ZMod.val_eq_zero _).mp this
    · exact bitVal_of_ge a hj
  funext i t
  by_cases hi : (i : ℕ) < k - 1
  · rw [← bitVal_pos a i t hi, hbit]; rfl
  · rw [last_eq_of_isAddress ha i hi t]
    refine sum_eq_zero fun i' hi' => ?_
    rw [mem_filter] at hi'
    rw [← bitVal_pos a i' t hi'.2, hbit]

end Lax119563Proofs.Witness

end Witness_Counter

/-! ### Formerly `Lax119563Proofs.Witness.RelaySystem` -/

section Witness_RelaySystem

/-!
# The relay counter as an implicit parity system

Well-formedness of the schemas and the pairwise intersection condition, and the definition
`relay k ℓ : ImplicitParitySystem k ℓ`.
-/

open Lax119563.ImplicitParitySystems Lax119563.ParitySystems

namespace Lax119563Proofs.Witness

variable {k ℓ : ℕ}

theorem image_idP (D : Finset (Coord k ℓ)) : D.image (idP : BlockPerm k ℓ).apply = D := by
  have : (idP : BlockPerm k ℓ).apply = id := funext idP_apply
  rw [this, Finset.image_id]

theorem gate_wellFormed (j : Fin (nbits k ℓ)) :
    ∀ e ∈ gate j, e.WellFormed (fun x => domS k ℓ ((locEquiv _).symm x)) := by
  intro e he
  simp only [gate, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;>
    simp [Schema.WellFormed, loc, loc_inj, image_idP, domS]

theorem endpoints_wellFormed :
    ∀ e ∈ endpoints k ℓ, e.WellFormed (fun x => domS k ℓ ((locEquiv _).symm x)) := by
  intro e he
  simp only [endpoints, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;>
    simp [Schema.WellFormed, loc, loc_inj, image_idP, domS]

theorem relay_wellFormed :
    ∀ e ∈ relaySchemas k ℓ, e.WellFormed (fun x => domS k ℓ ((locEquiv _).symm x)) := by
  intro e he
  rcases mem_relaySchemas.mp he with h | ⟨j, h⟩
  · exact endpoints_wellFormed e h
  · exact gate_wellFormed j e h

/-- Every location of a gate schema at `j` is `v` or a private location of `j`. -/
theorem gate_locations {j : Fin (nbits k ℓ)} {e : Schema k ℓ (nlocs k ℓ)} (he : e ∈ gate j)
    {x : Fin (nlocs k ℓ)} (hx : x ∈ e.locations) :
    x = loc k ℓ (.inl 0) ∨ ∃ c, x = loc k ℓ (.inr (j, c)) := by
  simp only [gate, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;>
    simp only [Schema.locations, Finset.mem_insert, Finset.mem_singleton] at hx <;>
    aesop

/-- Every location of an endpoint schema is `v`, `z₀` or `z₁`. -/
theorem endpoints_locations {e : Schema k ℓ (nlocs k ℓ)} (he : e ∈ endpoints k ℓ)
    {x : Fin (nlocs k ℓ)} (hx : x ∈ e.locations) : ∃ i, x = loc k ℓ (.inl i) := by
  simp only [endpoints, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;>
    simp only [Schema.locations, Finset.mem_insert, Finset.mem_singleton] at hx <;>
    aesop

theorem card_inter_le_one_of {s t : Finset (Fin (nlocs k ℓ))}
    (h : ∀ x ∈ s, x ∈ t → x = loc k ℓ (.inl 0)) : (s ∩ t).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_inter] at ha hb
  rw [h a ha.1 ha.2, h b hb.1 hb.2]

theorem gate_pairwise (j : Fin (nbits k ℓ)) :
    (gate j).Pairwise fun e e' : Schema k ℓ (nlocs k ℓ) => (e.locations ∩ e'.locations).card ≤ 1 := by
  simp only [gate]
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_
    (List.pairwise_singleton _ _))) <;>
  · intro e' he'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
    rcases he' with rfl | rfl | rfl <;>
    · rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Schema.locations, Finset.mem_inter, Finset.mem_insert,
        Finset.mem_singleton] at ha hb
      aesop (add norm simp [loc_inj])

theorem common_loc_gate_gate {j j' : Fin (nbits k ℓ)} (hjj : j ≠ j') {e e' : Schema k ℓ (nlocs k ℓ)}
    (he : e ∈ gate j) (he' : e' ∈ gate j') :
    ∀ x ∈ e.locations, x ∈ e'.locations → x = loc k ℓ (.inl 0) := by
  intro x hx hx'
  rcases gate_locations he hx with h | ⟨c, rfl⟩
  · exact h
  rcases gate_locations he' hx' with h | ⟨c', h⟩
  · exact h
  · rw [loc_inj] at h
    simp only [Sum.inr.injEq, Prod.mk.injEq] at h
    exact absurd h.1 hjj

theorem relay_pairwise :
    (relaySchemas k ℓ).Pairwise fun e e' => (e.locations ∩ e'.locations).card ≤ 1 := by
  rw [relaySchemas, List.pairwise_append, List.pairwise_flatMap]
  refine ⟨?_, ⟨fun j _ => gate_pairwise j, ?_⟩, ?_⟩
  · simp only [endpoints]
    refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
    · intro e' he'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
      subst he'
      apply card_inter_le_one_of
      intro x hx hx'
      simp only [Schema.locations, Finset.mem_insert, Finset.mem_singleton] at hx hx'
      rcases hx with rfl | rfl <;> rcases hx' with h | h <;> simp_all [loc_inj]
  · exact (List.nodup_finRange _).imp fun hjj e he e' he' =>
      card_inter_le_one_of (common_loc_gate_gate hjj he he')
  · intro e he e' he'
    obtain ⟨j, -, he'⟩ := List.mem_flatMap.mp he'
    apply card_inter_le_one_of
    intro x hx hx'
    obtain ⟨i, rfl⟩ := endpoints_locations he hx
    rcases gate_locations he' hx' with h | ⟨c, h⟩
    · exact h
    · rw [loc_inj] at h; cases h

/-- **The relay counter** `Î^{k,ℓ}_ctr`, counting down. (Reducible, so that its number of
locations is seen to be `nlocs k ℓ` by `simp`.) -/
@[reducible] def relay (k ℓ : ℕ) : ImplicitParitySystem k ℓ where
  numLocations := nlocs k ℓ
  domain x := domS k ℓ ((locEquiv _).symm x)
  schemas := relaySchemas k ℓ
  init x := initS k ℓ ((locEquiv _).symm x)
  schema_wellFormed := relay_wellFormed
  schemas_meet := relay_pairwise

@[simp] theorem relay_domain (σ) : (relay k ℓ).domain (loc k ℓ σ) = domS k ℓ σ := by
  simp [relay, loc]

@[simp] theorem relay_init (σ) : (relay k ℓ).init (loc k ℓ σ) = initS k ℓ σ := by
  simp [relay, loc]

end Lax119563Proofs.Witness

end Witness_RelaySystem

/-! ### Formerly `Lax119563Proofs.Witness.RelayConflict` -/

section Witness_RelayConflict

/-!
# The relay counter has a conflict (Lemma relay-size, `τ < ∞`)

Unit propagation sends `X_{v,s} = 0` (from `X_{z₀,s} = 0`) down the counter: every address
`a ≠ 0` is allowed for the gate of its lowest set bit `j`, which derives
`X_{p_j,a} = X_{q_j,a} = 0`, then `X_{r_j,a} = 0`, then `X_{v,T_j a} = 0`, and `T_j a` has value
one less. After `2^m - 1` gates the zero address carries `X_{v,0} = 0`, while `X_{z₁,0} = 1`
gives `X_{v,0} = 1`.
-/

open Lax119563.ImplicitParitySystems Lax119563.ParitySystems

namespace Lax119563Proofs.Witness

variable {V : Type*} [DecidableEq V]

theorem infer_zero {P : ParitySystem V} {h : Finset V} (hh : h ∈ P.equations) {X : V}
    (hX : X ∈ h) {r : ℕ} (hk : ∀ Y ∈ h, Y ≠ X → (Y, (0 : ZMod 2)) ∈ P.known r) :
    (X, (0 : ZMod 2)) ∈ P.known (r + 1) :=
  Or.inr ⟨h, hh, hX, fun _ => 0, hk, by simp⟩

theorem infer_one {P : ParitySystem V} {X Y : V} (hh : {Y, X} ∈ P.equations) (hne : Y ≠ X)
    {r : ℕ} (hY : (Y, (1 : ZMod 2)) ∈ P.known r) : (X, (1 : ZMod 2)) ∈ P.known (r + 1) := by
  refine Or.inr ⟨{Y, X}, hh, by simp, fun _ => 1, ?_, ?_⟩
  · intro Z hZ hZX
    rw [Finset.mem_insert, Finset.mem_singleton] at hZ
    rcases hZ with rfl | rfl
    · exact hY
    · exact absurd rfl hZX
  · have : ({Y, X} : Finset V).erase X = {Y} := by
      rw [Finset.pair_comm]; exact Finset.erase_insert (by simpa using hne.symm)
    simp [this]

variable {k ℓ : ℕ}

theorem mem_relay_equations {e : Schema k ℓ (nlocs k ℓ)} (he : e ∈ relaySchemas k ℓ)
    {a : Fin k → BlockCoord ℓ} (ha : IsAddress a) (hs : supp a ⊆ e.domain) :
    e.equation a ∈ (relay k ℓ).toParitySystem.equations :=
  ⟨e, he, a, ha, hs, rfl⟩

theorem gate_mem (j : Fin (nbits k ℓ)) {e : Schema k ℓ (nlocs k ℓ)} (he : e ∈ gate j) :
    e ∈ relaySchemas k ℓ :=
  mem_relaySchemas.mpr (Or.inr ⟨j, he⟩)

/-- The main location `v`. -/
abbrev vL (k ℓ : ℕ) : Fin (nlocs k ℓ) := loc k ℓ (.inl 0)

theorem forward : ∀ n, n ≤ 2 ^ nbits k ℓ - 1 → ∃ a : Fin k → BlockCoord ℓ, IsAddress a ∧
    cval a + n = 2 ^ nbits k ℓ - 1 ∧
    ((vL k ℓ, a), (0 : ZMod 2)) ∈ (relay k ℓ).toParitySystem.known (1 + 3 * n) := by
  intro n hn
  induction n with
  | zero =>
    refine ⟨sAddr k ℓ, isAddress_withChecksum _, by have := cval_sAddr (k := k) (ℓ := ℓ); omega,
      ?_⟩
    have hh := mem_relay_equations
      (e := .binary (loc k ℓ (.inl 1)) (loc k ℓ (.inl 0)) (supp (sAddr k ℓ)) idP idP)
      (by simp [relaySchemas, endpoints]) (isAddress_withChecksum _) (subset_refl _)
    simp only [Schema.equation, idP_act] at hh
    refine infer_zero hh (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) fun Y hY hne => ?_
    rw [Finset.mem_insert, Finset.mem_singleton] at hY
    rcases hY with rfl | rfl
    · refine ⟨0, ?_, rfl, isAddress_withChecksum _, ?_⟩
      · show (relay k ℓ).init (loc k ℓ (.inl 1)) = some 0
        rw [relay_init]; rfl
      · show supp (sAddr k ℓ) ⊆ (relay k ℓ).domain (loc k ℓ (.inl 1))
        rw [relay_domain]; exact subset_refl _
    · exact absurd rfl hne
  | succ n ih =>
    obtain ⟨a, ha, hval, hk⟩ := ih (by omega)
    obtain ⟨j, hj, hsupp⟩ := exists_allowed ha (by omega)
    have hdec := cval_decP hj hsupp
    let jj : Fin (nbits k ℓ) := ⟨j, hj⟩
    refine ⟨(decP j).act a, isAddress_act ha, by omega, ?_⟩
    rw [show 1 + 3 * (n + 1) = 1 + 3 * n + 1 + 1 + 1 by ring]
    have mem := fun e (he : e ∈ gate jj) => mem_relay_equations (gate_mem jj he) ha
    have hp : ((loc k ℓ (.inr (jj, 0)), a), (0 : ZMod 2)) ∈
        (relay k ℓ).toParitySystem.known (1 + 3 * n + 1) := by
      have hh := mem (.binary (loc k ℓ (.inl 0))
        (loc k ℓ (.inr (jj, 0))) (relayDom j) idP idP) (by simp [gate, jj]) hsupp
      simp only [Schema.equation, idP_act] at hh
      refine infer_zero hh (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) fun Y hY hne => ?_
      rw [Finset.mem_insert, Finset.mem_singleton] at hY
      rcases hY with rfl | rfl
      · exact hk
      · exact absurd rfl hne
    have hq : ((loc k ℓ (.inr (jj, 1)), a), (0 : ZMod 2)) ∈
        (relay k ℓ).toParitySystem.known (1 + 3 * n + 1) := by
      have hh := mem (.binary (loc k ℓ (.inl 0))
        (loc k ℓ (.inr (jj, 1))) (relayDom j) idP idP) (by simp [gate, jj]) hsupp
      simp only [Schema.equation, idP_act] at hh
      refine infer_zero hh (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) fun Y hY hne => ?_
      rw [Finset.mem_insert, Finset.mem_singleton] at hY
      rcases hY with rfl | rfl
      · exact hk
      · exact absurd rfl hne
    have hr : ((loc k ℓ (.inr (jj, 2)), a), (0 : ZMod 2)) ∈
        (relay k ℓ).toParitySystem.known (1 + 3 * n + 1 + 1) := by
      have hh := mem (.ternary (loc k ℓ (.inr (jj, 0)))
        (loc k ℓ (.inr (jj, 1))) (loc k ℓ (.inr (jj, 2))) (relayDom j) idP idP idP) (by simp [gate, jj]) hsupp
      simp only [Schema.equation, idP_act] at hh
      refine infer_zero hh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _))) fun Y hY hne => ?_
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hY
      rcases hY with rfl | rfl | rfl
      · exact hp
      · exact hq
      · exact absurd rfl hne
    have hh := mem (.binary (loc k ℓ (.inr (jj, 2)))
      (loc k ℓ (.inl 0)) (relayDom j) idP (decP j)) (by simp [gate, jj]) hsupp
    simp only [Schema.equation, idP_act] at hh
    refine infer_zero hh (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) fun Y hY hne => ?_
    rw [Finset.mem_insert, Finset.mem_singleton] at hY
    rcases hY with rfl | rfl
    · exact hr
    · exact absurd rfl hne

/-- The round in which the relay counter has a conflict. -/
theorem relay_hasConflict :
    (relay k ℓ).toParitySystem.HasConflict (1 + 3 * (2 ^ nbits k ℓ - 1)) := by
  obtain ⟨a, ha, hval, hk⟩ := forward (k := k) (ℓ := ℓ) _ le_rfl
  have h0 := eq_zero_of_cval ha (by omega)
  subst h0
  refine ⟨(vL k ℓ, 0), hk, ?_⟩
  refine known_mono _ (by omega : 1 ≤ 1 + 3 * (2 ^ nbits k ℓ - 1)) ?_
  have hh := mem_relay_equations
    (e := .binary (loc k ℓ (.inl 2)) (loc k ℓ (.inl 0)) (supp 0) idP idP)
    (by simp [relaySchemas, endpoints]) (by simp [IsAddress]) (subset_refl _)
  simp only [Schema.equation, idP_act] at hh
  refine infer_one hh (fun h => absurd (loc_inj.mp (congrArg Prod.fst h)) (by simp)) ?_
  refine ⟨1, ?_, rfl, by simp [IsAddress], ?_⟩
  · show (relay k ℓ).init (loc k ℓ (.inl 2)) = some 1
    rw [relay_init]; rfl
  · show supp 0 ⊆ (relay k ℓ).domain (loc k ℓ (.inl 2))
    rw [relay_domain]; exact subset_refl _

end Lax119563Proofs.Witness

end Witness_RelayConflict

/-! ### Formerly `Lax119563Proofs.Witness.RelaySize` -/

section Witness_RelaySize

/-!
# Size of the relay counter (Lemma relay-size, size part)

The size parameter `∑_v |𝔠_v| + (k+1) ∑_e (|𝔠_e| + 2^{rank B_e})` of the relay counter is
`O_k(2^ℓ)`. In the domain `𝔠'_j`, the first `r_j = j / (k-1)` bits of every block coordinate
are zero, so `|𝔠'_j| ≤ k 2^{ℓ - r_j}` and the first `r_j` checksum rows of the check matrix
vanish on `𝔠'_j`, giving `rank B_e ≤ k - 1 + ℓ - r_j`. Each value of `r_j` occurs for `k - 1`
positions `j`, and the sum of `2^{ℓ - r}` is geometric.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.RowSpaceCompiler

namespace Lax119563Proofs.Witness

open Finset

variable {k ℓ : ℕ}

/-- All coordinates in `D` have their first `r` bits zero. -/
def ZeroOn (D : Finset (Coord k ℓ)) (r : ℕ) : Prop :=
  ∀ c ∈ D, ∀ t : Fin ℓ, (t : ℕ) < r → c.2 t = 0

theorem card_tail_le (r : ℕ) : Fintype.card {t : Fin ℓ // r ≤ (t : ℕ)} ≤ ℓ - r := by
  refine (Fintype.card_le_of_injective (fun t => (⟨t.1 - r, by omega⟩ : Fin (ℓ - r))) ?_).trans
    (by simp)
  intro t t' h
  simp only [Fin.mk.injEq] at h
  have := t.2; have := t'.2
  exact Subtype.ext (Fin.ext (by omega))

theorem card_le_of_zeroOn {D : Finset (Coord k ℓ)} {r : ℕ} (hD : ZeroOn D r) :
    D.card ≤ k * 2 ^ (ℓ - r) := by
  classical
  have hsub : D ⊆ univ ×ˢ (univ.filter fun b : BlockCoord ℓ => ∀ t : Fin ℓ, (t : ℕ) < r → b t = 0) := by
    intro c hc
    simp only [mem_product, mem_univ, mem_filter, true_and]
    exact hD c hc
  refine (card_le_card hsub).trans ?_
  rw [card_product, card_univ, Fintype.card_fin]
  refine Nat.mul_le_mul_left _ ?_
  let f : BlockCoord ℓ → ({t : Fin ℓ // r ≤ (t : ℕ)} → ZMod 2) := fun b t => b t.1
  have hinj : Set.InjOn f (univ.filter fun b : BlockCoord ℓ => ∀ t : Fin ℓ, (t : ℕ) < r → b t = 0) := by
    intro b hb b' hb' h
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hb hb'
    funext t
    by_cases ht : (t : ℕ) < r
    · rw [hb t ht, hb' t ht]
    · exact congrFun h ⟨t, by omega⟩
  refine (card_le_card_of_injOn f (fun _ _ => mem_univ _) hinj).trans ?_
  rw [card_univ, Fintype.card_fun, ZMod.card]
  exact Nat.pow_le_pow_right (by norm_num) (card_tail_le r)

/-- The rows of the check matrix that may be nonzero on a domain with `r` leading zero bits. -/
abbrev RowsR (k ℓ r : ℕ) := Fin (k - 1) ⊕ {t : Fin ℓ // r ≤ (t : ℕ)}

/-- The embedding of these rows into all rows. -/
def embR {r : ℕ} : RowsR k ℓ r → Fin (k - 1) ⊕ Fin ℓ := Sum.map id Subtype.val

theorem embR_inj {r : ℕ} {ρ ρ' : RowsR k ℓ r} : embR ρ = embR ρ' ↔ ρ = ρ' := by
  constructor
  · intro h
    rcases ρ with i | t <;> rcases ρ' with i' | t' <;> simp_all [embR, Subtype.ext_iff]
  · rintro rfl; rfl

theorem rank_le_of_zeroOn {D : Finset (Coord k ℓ)} {r : ℕ} (hD : ZeroOn D r) :
    (Matrix.of fun row (c : D) => checkMatrix k ℓ row c).rank ≤ (k - 1) + (ℓ - r) := by
  classical
  let M' : Matrix (RowsR k ℓ r) D (ZMod 2) := Matrix.of fun ρ c => checkMatrix k ℓ (embR ρ) c
  let P : Matrix (Fin (k - 1) ⊕ Fin ℓ) (RowsR k ℓ r) (ZMod 2) :=
    Matrix.of fun row ρ => if embR ρ = row then 1 else 0
  have hPM : (Matrix.of fun row (c : D) => checkMatrix k ℓ row c) = P * M' := by
    ext row c
    rw [Matrix.mul_apply, Matrix.of_apply]
    have hterm : ∀ ρ, P row ρ * M' ρ c = if embR ρ = row then checkMatrix k ℓ (embR ρ) c else 0 := by
      intro ρ
      show (if embR ρ = row then (1 : ZMod 2) else 0) * checkMatrix k ℓ (embR ρ) c = _
      split_ifs <;> simp
    simp only [hterm]
    by_cases hrow : ∃ ρ0 : RowsR k ℓ r, embR ρ0 = row
    · obtain ⟨ρ0, rfl⟩ := hrow
      simp only [embR_inj]
      rw [Finset.sum_ite_eq' Finset.univ ρ0, if_pos (Finset.mem_univ _)]
    · rw [Finset.sum_eq_zero fun ρ _ => if_neg fun h => hrow ⟨ρ, h⟩]
      rcases row with i | t
      · exact absurd ⟨Sum.inl i, rfl⟩ hrow
      · have ht : ¬ r ≤ (t : ℕ) := fun ht => hrow ⟨Sum.inr ⟨t, ht⟩, rfl⟩
        show c.1.2 t = 0
        exact hD c.1 c.2 t (by omega)
  rw [hPM]
  refine (Matrix.rank_mul_le_right P M').trans ((Matrix.rank_le_card_height M').trans ?_)
  simp only [RowsR, Fintype.card_sum, Fintype.card_fin]
  exact Nat.add_le_add_left (card_tail_le r) _

theorem zeroOn_relayDom (j : ℕ) : ZeroOn (relayDom (k := k) (ℓ := ℓ) j) (j / (k - 1)) := by
  intro c hc t ht
  simp only [relayDom, mem_filter, mem_univ, true_and] at hc
  split_ifs at hc with hi
  · apply hc.1 t
    have h1 : ((t : ℕ) + 1) * (k - 1) ≤ j / (k - 1) * (k - 1) := Nat.mul_le_mul_right _ ht
    have h2 := Nat.div_mul_le_self j (k - 1)
    nlinarith
  · exact hc t ht

theorem zeroOn_zero (D : Finset (Coord k ℓ)) : ZeroOn D 0 := fun _ _ _ ht => absurd ht (by omega)

theorem sum_geom_div (K : ℕ) (hK : 0 < K) :
    ∀ ℓ, ∑ j ∈ range (K * ℓ), 2 ^ (ℓ - j / K) ≤ K * 2 ^ (ℓ + 1) := by
  intro ℓ
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    rw [show K * (ℓ + 1) = K + K * ℓ by ring, sum_range_add]
    have h1 : ∑ j ∈ range K, 2 ^ (ℓ + 1 - j / K) = K * 2 ^ (ℓ + 1) := by
      rw [sum_congr rfl fun j hj => by rw [Nat.div_eq_of_lt (mem_range.mp hj), Nat.sub_zero],
        sum_const, card_range, smul_eq_mul]
    have h2 : ∑ j ∈ range (K * ℓ), 2 ^ (ℓ + 1 - (K + j) / K) = ∑ j ∈ range (K * ℓ), 2 ^ (ℓ - j / K) := by
      refine sum_congr rfl fun j _ => ?_
      rw [show K + j = j + K * 1 by ring, Nat.add_mul_div_left _ _ hK]
      congr 1; omega
    rw [h1, h2]
    have : K * 2 ^ (ℓ + 1 + 1) = 2 * (K * 2 ^ (ℓ + 1)) := by ring
    omega

theorem sum_map_flatMap {α β : Type*} (L : List α) (f : α → List β) (g : β → ℕ) :
    ((L.flatMap f).map g).sum = (L.map fun a => ((f a).map g).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, ih]

/-- The summand `|𝔠_e| + 2^{rank B_e}` of a schema. -/
noncomputable def schemaCost {w : ℕ} (e : Schema k ℓ w) : ℕ := e.domain.card + 2 ^ rowRank e

theorem schemaCost_le {w : ℕ} (e : Schema k ℓ w) {r : ℕ} (hz : ZeroOn e.domain r) :
    schemaCost e ≤ (k + 2 ^ (k - 1)) * 2 ^ (ℓ - r) := by
  unfold schemaCost
  have h1 := card_le_of_zeroOn hz
  have h2 : 2 ^ rowRank e ≤ 2 ^ (k - 1) * 2 ^ (ℓ - r) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (rank_le_of_zeroOn hz)
  nlinarith

theorem gate_cost (j : Fin (nbits k ℓ)) :
    ((gate j).map schemaCost).sum ≤ 4 * ((k + 2 ^ (k - 1)) * 2 ^ (ℓ - (j : ℕ) / (k - 1))) := by
  have h := fun (e : Schema k ℓ (nlocs k ℓ)) (he : e.domain = relayDom j) =>
    schemaCost_le e (he ▸ zeroOn_relayDom (k := k) (ℓ := ℓ) j)
  simp only [gate, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have := h (.binary (loc k ℓ (.inl 0)) (loc k ℓ (.inr (j, 0))) (relayDom j) idP idP) rfl
  have := h (.binary (loc k ℓ (.inl 0)) (loc k ℓ (.inr (j, 1))) (relayDom j) idP idP) rfl
  have := h (.ternary (loc k ℓ (.inr (j, 0))) (loc k ℓ (.inr (j, 1)))
    (loc k ℓ (.inr (j, 2))) (relayDom j) idP idP idP) rfl
  have := h (.binary (loc k ℓ (.inr (j, 2))) (loc k ℓ (.inl 0)) (relayDom j) idP (decP j)) rfl
  omega

theorem card_supp_le (a : Fin k → BlockCoord ℓ) : (supp a).card ≤ k := by
  unfold supp
  exact card_image_le.trans (by simp)

theorem endpoints_cost : ((endpoints k ℓ).map schemaCost).sum ≤ 2 * (k + 2 ^ (k - 1) * 2 ^ ℓ) := by
  simp only [endpoints, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have h : ∀ a : Fin k → BlockCoord ℓ, schemaCost (Schema.binary (loc k ℓ (.inl 1))
      (loc k ℓ (.inl 0)) (supp a) idP idP) ≤ k + 2 ^ (k - 1) * 2 ^ ℓ ∧
      schemaCost (Schema.binary (loc k ℓ (.inl 2))
      (loc k ℓ (.inl 0)) (supp a) idP idP) ≤ k + 2 ^ (k - 1) * 2 ^ ℓ := by
    intro a
    have h2 : ∀ e : Schema k ℓ (nlocs k ℓ), 2 ^ rowRank e ≤ 2 ^ (k - 1) * 2 ^ ℓ := fun e => by
      have := rank_le_of_zeroOn (zeroOn_zero e.domain)
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by simpa [rowRank] using this)
    exact ⟨Nat.add_le_add (card_supp_le a) (h2 _), Nat.add_le_add (card_supp_le a) (h2 _)⟩
  have := (h (sAddr k ℓ)).1
  have := (h 0).2
  omega

/-- The constant of the size bound. -/
def sizeConst (k : ℕ) : ℕ :=
  k + 2 * k + 3 * k * (2 * (k - 1)) +
    (k + 1) * (2 * k + 2 * 2 ^ (k - 1) + 4 * (k + 2 ^ (k - 1)) * (2 * (k - 1)))

/-- **Size of the relay counter.** For `k ≥ 2`, the size parameter of the relay counter is at
most `sizeConst k · 2^ℓ`. -/
theorem relay_size (hk : 2 ≤ k) :
    Lax119563.RowSpaceCompiler.rowSpaceSize (relay k ℓ) ≤ sizeConst k * 2 ^ ℓ := by
  set X := 2 ^ ℓ with hX
  have hX1 : 1 ≤ X := Nat.one_le_two_pow
  set A := ∑ j : Fin (nbits k ℓ), 2 ^ (ℓ - (j : ℕ) / (k - 1)) with hA
  have hAle : A ≤ 2 * (k - 1) * X := by
    have h1 : A = ∑ j ∈ range ((k - 1) * ℓ), 2 ^ (ℓ - j / (k - 1)) := by
      rw [hA]; exact Fin.sum_univ_eq_sum_range (fun j => 2 ^ (ℓ - j / (k - 1))) _
    have h2 := sum_geom_div (k - 1) (by omega) ℓ
    have h3 : (k - 1) * 2 ^ (ℓ + 1) = 2 * (k - 1) * X := by rw [hX]; ring
    omega
  -- locations
  have hloc : ∑ x, ((relay k ℓ).domain x).card ≤ k * X + k + k + 3 * (k * A) := by
    have e1 : ∑ x, ((relay k ℓ).domain x).card = ∑ σ, (domS k ℓ σ).card := by
      simp only [relay]
      exact Equiv.sum_comp (locEquiv _).symm (fun σ => (domS k ℓ σ).card)
    rw [e1, Fintype.sum_sum_type, Fin.sum_univ_three, Fintype.sum_prod_type]
    simp only [domS, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    have h0 : (univ : Finset (Coord k ℓ)).card = k * X := by
      simp [hX, Fintype.card_prod, Fintype.card_fun, ZMod.card]
    rw [Finset.card_univ] at h0
    have h3 : ∑ j : Fin (nbits k ℓ), 3 * (relayDom (k := k) (ℓ := ℓ) j).card ≤ 3 * (k * A) := by
      rw [hA, mul_sum, mul_sum]
      exact sum_le_sum fun j _ => by
        have := card_le_of_zeroOn (zeroOn_relayDom (k := k) (ℓ := ℓ) j)
        nlinarith
    have := card_supp_le (sAddr k ℓ)
    have := card_supp_le (0 : Fin k → BlockCoord ℓ)
    omega
  -- schemas
  have hsch : ((relay k ℓ).schemas.map fun e => e.domain.card + 2 ^ rowRank e).sum ≤
      2 * (k + 2 ^ (k - 1) * X) + 4 * (k + 2 ^ (k - 1)) * A := by
    change ((relaySchemas k ℓ).map schemaCost).sum ≤ _
    rw [relaySchemas, List.map_append, List.sum_append, sum_map_flatMap, ← Fin.sum_univ_def]
    have hg : ∑ j : Fin (nbits k ℓ), ((gate j).map schemaCost).sum ≤
        4 * (k + 2 ^ (k - 1)) * A := by
      rw [hA, mul_sum]
      exact sum_le_sum fun j _ => (gate_cost j).trans (le_of_eq (by ring))
    have := endpoints_cost (k := k) (ℓ := ℓ)
    rw [← hX] at this
    omega
  unfold Lax119563.RowSpaceCompiler.rowSpaceSize
  calc ∑ x, ((relay k ℓ).domain x).card +
        (k + 1) * ((relay k ℓ).schemas.map fun e => e.domain.card + 2 ^ rowRank e).sum
      ≤ (k * X + k + k + 3 * (k * A)) +
        (k + 1) * (2 * (k + 2 ^ (k - 1) * X) + 4 * (k + 2 ^ (k - 1)) * A) := by gcongr
    _ ≤ (k * X + k * X + k * X + 3 * (k * (2 * (k - 1) * X))) +
        (k + 1) * (2 * (k * X + 2 ^ (k - 1) * X) + 4 * (k + 2 ^ (k - 1)) * (2 * (k - 1) * X)) := by
      have hkX : k ≤ k * X := Nat.le_mul_of_pos_right _ hX1
      gcongr
    _ = sizeConst k * X := by unfold sizeConst; ring

end Lax119563Proofs.Witness

end Witness_RelaySize

/-! ### Formerly `Lax119563Proofs.Witness.RelayTree` -/

section Witness_RelayTree

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

end Witness_RelayTree

/-! ### Formerly `Lax119563Proofs.Witness.Stabilize` -/

section Witness_Stabilize

/-!
# Early distinctions by `k`-WL

If `k`-WL distinguishes `G` and `H` at all, it does so after at most
`|V(G)|^k + |V(H)|^k` rounds. We consider the joint partition of the `k`-tuples of both graphs
by their colors: it refines in every round, so it stabilizes after at most as many rounds as
there are tuples, and once stable it stays stable, so no new distinctions appear.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman

namespace Lax119563Proofs.Witness

open Classical

variable {k : ℕ} (G H : ColoredGraph)

/-- The `k`-tuples of both graphs. -/
abbrev Tup (k : ℕ) (G H : ColoredGraph) := (Fin k → Fin G.n) ⊕ (Fin k → Fin H.n)

/-- The color of a tuple of either graph after `r` rounds. -/
noncomputable def ucol (r : ℕ) : Tup k G H → Color k r
  | .inl p => color G r p
  | .inr q => color H r q

/-- The multiset part of the color after round `r + 1`. -/
noncomputable def umult (r : ℕ) : Tup k G H → Multiset (Fin k → Color k r)
  | .inl p => (Finset.univ : Finset (Fin G.n)).val.map fun q i => color G r (Function.update p i q)
  | .inr p => (Finset.univ : Finset (Fin H.n)).val.map fun q i => color H r (Function.update p i q)

theorem ucol_succ (r : ℕ) (x : Tup k G H) :
    ucol G H (r + 1) x = ((ucol G H r x, umult G H r x) : Color k r × Multiset _) := by
  cases x <;> rfl

/-- Projection of a round-`r+1` color to its round-`r` part. -/
def fstC {r : ℕ} (c : Color k (r + 1)) : Color k r :=
  Prod.fst (α := Color k r) (β := Multiset (Fin k → Color k r)) c

theorem fstC_ucol (r : ℕ) (x : Tup k G H) : fstC (ucol G H (r + 1) x) = ucol G H r x := by
  rw [ucol_succ]; rfl

theorem ucol_eq_of_succ {r : ℕ} {x y : Tup k G H} (h : ucol G H (r + 1) x = ucol G H (r + 1) y) :
    ucol G H r x = ucol G H r y := by
  rw [← fstC_ucol, h, fstC_ucol]

/-- The number of color classes of the joint partition after round `r`. -/
noncomputable def numClasses (r : ℕ) : ℕ := (Finset.univ.image (ucol (k := k) G H r)).card

theorem numClasses_le_succ (r : ℕ) : numClasses (k := k) G H r ≤ numClasses (k := k) G H (r + 1) := by
  unfold numClasses
  have : Finset.univ.image (ucol (k := k) G H r) =
      (Finset.univ.image (ucol G H (r + 1))).image fstC := by
    rw [Finset.image_image]; congr 1; funext x; exact (fstC_ucol G H r x).symm
  rw [this]; exact Finset.card_image_le

theorem numClasses_le_card (r : ℕ) : numClasses (k := k) G H r ≤ G.n ^ k + H.n ^ k := by
  unfold numClasses
  refine (Finset.card_image_le).trans ?_
  simp [Finset.card_univ, Fintype.card_sum, Fintype.card_fun]

/-- The joint partition does not split from round `r` to round `r + 1`. -/
def StableAt (r : ℕ) : Prop :=
  ∀ x y : Tup k G H, ucol G H r x = ucol G H r y → ucol G H (r + 1) x = ucol G H (r + 1) y

theorem stableAt_of_numClasses {r : ℕ} (h : numClasses (k := k) G H r = numClasses (k := k) G H (r + 1)) :
    StableAt (k := k) G H r := by
  intro x y hxy
  unfold numClasses at h
  have himg : Finset.univ.image (ucol (k := k) G H r) =
      (Finset.univ.image (ucol G H (r + 1))).image fstC := by
    rw [Finset.image_image]; congr 1; funext x; exact (fstC_ucol G H r x).symm
  rw [himg] at h
  have hinj := Finset.card_image_iff.mp h
  apply hinj (by simp) (by simp)
  rw [fstC_ucol, fstC_ucol, hxy]

theorem stableAt_succ {r : ℕ} (h : StableAt (k := k) G H r) : StableAt (k := k) G H (r + 1) := by
  intro x y hxy
  -- a map from round-`r` colors to round-`r+1` colors, valid on all realized colors
  let φ : Color k r → Color k (r + 1) := fun c =>
    if hc : ∃ z, ucol G H r z = c then ucol G H (r + 1) hc.choose else ucol G H (r + 1) x
  have hφ : ∀ z, φ (ucol G H r z) = ucol G H (r + 1) z := by
    intro z
    have hc : ∃ z', ucol G H r z' = ucol G H r z := ⟨z, rfl⟩
    simp only [φ, dif_pos hc]
    exact h _ _ hc.choose_spec
  have hmult : ∀ z, umult G H (r + 1) z = (umult G H r z).map fun f i => φ (f i) := by
    intro z
    cases z with
    | inl p =>
      simp only [umult, Multiset.map_map, Function.comp_def]
      congr 1; funext q; funext i
      exact (hφ (.inl (Function.update p i q))).symm
    | inr p =>
      simp only [umult, Multiset.map_map, Function.comp_def]
      congr 1; funext q; funext i
      exact (hφ (.inr (Function.update p i q))).symm
  rw [ucol_succ, ucol_succ] at hxy
  have h1 : ucol G H r x = ucol G H r y := (Prod.mk.inj hxy).1
  have h2 : umult G H r x = umult G H r y := (Prod.mk.inj hxy).2
  rw [ucol_succ, ucol_succ G H (r + 1) y, hmult, hmult, h2]
  congr 1
  rw [ucol_succ, ucol_succ G H r y, h1, h2]

theorem ucol_iff_of_stable {r : ℕ} (h : StableAt (k := k) G H r) {s : ℕ} (hrs : r ≤ s)
    (x y : Tup k G H) : ucol G H s x = ucol G H s y ↔ ucol G H r x = ucol G H r y := by
  induction s, hrs using Nat.le_induction with
  | base => rfl
  | succ s hrs ih =>
    have hs : StableAt (k := k) G H s := by
      clear ih
      induction s, hrs using Nat.le_induction with
      | base => exact h
      | succ s _ ih => exact stableAt_succ G H ih
    exact ⟨fun hxy => ih.mp (ucol_eq_of_succ G H hxy), fun hxy => hs _ _ (ih.mpr hxy)⟩

theorem exists_stableAt : ∃ r ≤ G.n ^ k + H.n ^ k, StableAt (k := k) G H r := by
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ r ≤ G.n ^ k + H.n ^ k, numClasses (k := k) G H r < numClasses (k := k) G H (r + 1) :=
    fun r hr => lt_of_le_of_ne (numClasses_le_succ G H r)
      (fun he => hcon r hr (stableAt_of_numClasses G H he))
  have key : ∀ r ≤ G.n ^ k + H.n ^ k + 1, r ≤ numClasses (k := k) G H r := by
    intro r hr
    induction r with
    | zero => exact Nat.zero_le _
    | succ r ih => exact lt_of_le_of_lt (ih (by omega)) (hlt r (by omega))
  have := key _ le_rfl
  have := numClasses_le_card (k := k) G H (G.n ^ k + H.n ^ k + 1)
  omega

theorem distinguishesAfter_of_stable {r s : ℕ} (hst : StableAt (k := k) G H r) (hrs : r ≤ s)
    (h : DistinguishesAfter k s G H) : DistinguishesAfter k r G H := by
  by_contra hcon
  obtain ⟨c, hc⟩ := h
  apply hc
  by_cases hz : ∃ z, ucol G H s z = c
  · obtain ⟨z, rfl⟩ := hz
    have hcount := not_not.mp (fun h' => hcon ⟨ucol G H r z, h'⟩)
    have e1 : Nat.card {p : Fin k → Fin G.n // color G s p = ucol G H s z} =
        Nat.card {p : Fin k → Fin G.n // color G r p = ucol G H r z} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun p =>
        ucol_iff_of_stable G H hst hrs (.inl p) z)
    have e2 : Nat.card {p : Fin k → Fin H.n // color H s p = ucol G H s z} =
        Nat.card {p : Fin k → Fin H.n // color H r p = ucol G H r z} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun p =>
        ucol_iff_of_stable G H hst hrs (.inr p) z)
    rw [e1, e2]; exact hcount
  · push_neg at hz
    have e1 : IsEmpty {p : Fin k → Fin G.n // color G s p = c} :=
      ⟨fun p => hz (.inl p.1) p.2⟩
    have e2 : IsEmpty {p : Fin k → Fin H.n // color H s p = c} :=
      ⟨fun p => hz (.inr p.1) p.2⟩
    simp [Nat.card_of_isEmpty]

/-- **Early distinction.** If `k`-WL distinguishes `G` and `H` after some round, it does so
after at most `|V(G)|^k + |V(H)|^k` rounds. -/
theorem exists_distinguishesAfter_le {s : ℕ} (h : DistinguishesAfter k s G H) :
    ∃ r ≤ G.n ^ k + H.n ^ k, DistinguishesAfter k r G H := by
  obtain ⟨r, hr, hst⟩ := exists_stableAt (k := k) G H
  by_cases hsr : s ≤ r
  · exact ⟨s, hsr.trans hr, h⟩
  · exact ⟨r, hr, distinguishesAfter_of_stable G H hst (by omega) h⟩

end Lax119563Proofs.Witness

end Witness_Stabilize

/-! ### Formerly `Lax119563Proofs.Reduction.CodeOrder` -/

section Reduction_CodeOrder

/-!
# Locations in code order

`locsByCode M H = (range numLoc).filterMap decodeLoc` enumerates the locations of the verifier
program in the order of their numbers (`Loc.code`; `decodeLoc_code`, `mem_locsByCode`).
`verifierCmds'` is the command list of the verifier program in this order
(`verifierCmds'_eq`), so that the index of a command is a count of the commands at smaller
location numbers, which a generator can compute.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Programs

variable {M : Machine} {H : ℕ}

open Classical in
/-- The location with number `c`, if any. -/
noncomputable def decodeLoc (M : Machine) (H : ℕ) (c : ℕ) : Option (Loc M H) :=
  if h : ∃ L : Loc M H, (Loc.code L).val = c then some (Classical.choose h) else none

lemma decodeLoc_code (L : Loc M H) : decodeLoc M H (Loc.code L).val = some L := by
  have h : ∃ L' : Loc M H, (Loc.code L').val = (Loc.code L).val := ⟨L, rfl⟩
  rw [decodeLoc, dif_pos h]
  exact congrArg some (Loc.code_injective (Fin.ext (Classical.choose_spec h)))

lemma code_of_decodeLoc {c : ℕ} {L : Loc M H} (h : decodeLoc M H c = some L) :
    (Loc.code L).val = c := by
  unfold decodeLoc at h
  split_ifs at h with h'
  · cases h; exact Classical.choose_spec h'

/-- The locations in the order of their numbers. -/
noncomputable def locsByCode (M : Machine) (H : ℕ) : List (Loc M H) :=
  (List.range (numLoc M H)).filterMap (decodeLoc M H)

lemma mem_locsByCode (L : Loc M H) : L ∈ locsByCode M H := by
  rw [locsByCode, List.mem_filterMap]
  exact ⟨_, List.mem_range.mpr (Loc.code L).isLt, decodeLoc_code L⟩

lemma length_locsByCode_le : (locsByCode M H).length ≤ numLoc M H :=
  (List.length_filterMap_le _ _).trans (by simp)

/-- The address commands of the verifier, in code order. -/
noncomputable def verifierCmds' (M : Machine) (x : List Bool) (s ℓ H : ℕ) :
    List (ACmd (Loc M H) s) :=
  progCmds ℓ (locsByCode M H) (moves M x s ℓ H)

/-- The commands in code order: for each number `c`, the moves of the decoded location. -/
lemma verifierCmds'_eq (x : List Bool) (s ℓ : ℕ) :
    verifierCmds' M x s ℓ H = (List.range (numLoc M H)).flatMap fun c =>
      match decodeLoc M H c with
      | some L => (moves M x s ℓ H L).map (Move.toACmd ℓ L)
      | none => [] := by
  unfold verifierCmds' progCmds locsByCode
  induction (List.range (numLoc M H)) with
  | nil => rfl
  | cons c l ih =>
    rw [List.filterMap_cons, List.flatMap_cons]
    cases h : decodeLoc M H c with
    | none => simpa using ih
    | some L => simp [ih]

end Lax119563Proofs.Reduction

end Reduction_CodeOrder

/-! ### Formerly `Lax119563Proofs.Reduction.HLib` -/

section Reduction_HLib

/-!
# A library of register programs

`HLe x w p st st' T`: `p` runs from `st` to `st'` within cost `T`. Derived instructions with
exact specifications: increment (`inc`), counting loops (`forUp`).
-/

namespace Lax119563Proofs.Reduction

variable {R : ℕ} {x : List Bool} {w : ℕ}

/-- `p` runs from `st` to `st'` within cost `T`. -/
def HLe (x : List Bool) (w : ℕ) (p : HProg R) (st st' : HSt R) (T : ℕ) : Prop :=
  ∃ t ≤ T, HRuns x w p st st' t

namespace HLe

variable {p q : HProg R} {st st' st₁ st₂ st₃ : HSt R} {T T' T₁ T₂ : ℕ}

lemma of_runs {t : ℕ} (h : HRuns x w p st st' t) : HLe x w p st st' t := ⟨t, le_rfl, h⟩

lemma mono (h : HLe x w p st st' T) (hT : T ≤ T') : HLe x w p st st' T' := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t, by omega, h⟩

lemma seq (h₁ : HLe x w p st₁ st₂ T₁) (h₂ : HLe x w q st₂ st₃ T₂) :
    HLe x w (.seq p q) st₁ st₃ (T₁ + T₂) := by
  obtain ⟨t₁, ht₁, h₁⟩ := h₁; obtain ⟨t₂, ht₂, h₂⟩ := h₂
  exact ⟨t₁ + t₂, by omega, .seq h₁ h₂⟩

lemma iteT {c} (hc : c st.view = true) (h : HLe x w p st st' T) :
    HLe x w (.ite c p q) st st' (T + 1) := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t + 1, by omega, .iteT hc h⟩

lemma iteF {c} (hc : c st.view = false) (h : HLe x w q st st' T) :
    HLe x w (.ite c p q) st st' (T + 1) := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t + 1, by omega, .iteF hc h⟩

lemma loopF {c} (hc : c st.view = false) : HLe x w (.loop c p) st st 1 := of_runs (.loopF hc)

lemma loopT {c} (hc : c st₁.view = true) (h₁ : HLe x w p st₁ st₂ T₁)
    (h₂ : HLe x w (.loop c p) st₂ st₃ T₂) : HLe x w (.loop c p) st₁ st₃ (T₁ + T₂ + 1) := by
  obtain ⟨t₁, ht₁, h₁⟩ := h₁; obtain ⟨t₂, ht₂, h₂⟩ := h₂
  exact ⟨t₁ + t₂ + 1, by omega, .loopT hc h₁ h₂⟩

lemma of_eq (h : HLe x w p st st₁ T) (hs : st₁ = st₂) (hT : T ≤ T') : HLe x w p st st₂ T' :=
  hs ▸ h.mono hT

/-- A loop along a sequence of states. -/
lemma loop_seq {c} (n : ℕ) (S : ℕ → HSt R) (C : ℕ → ℕ)
    (hc : ∀ k < n, c (S k).view = true) (hn : c (S n).view = false)
    (hb : ∀ k < n, HLe x w p (S k) (S (k + 1)) (C k)) :
    HLe x w (.loop c p) (S 0) (S n) (∑ k ∈ Finset.range n, (C k + 1) + 1) := by
  suffices H : ∀ d m, m + d = n →
      HLe x w (.loop c p) (S m) (S n) (∑ k ∈ Finset.Ico m n, (C k + 1) + 1) by
    simpa using H n 0 (by simp)
  intro d
  induction d with
  | zero => intro m hm; subst hm; simpa using loopF hn
  | succ d ih =>
    intro m hm
    have hlt : m < n := by omega
    refine (loopT (hc m hlt) (hb m hlt) (ih (m + 1) (by omega))).mono (le_of_eq ?_)
    rw [Finset.sum_eq_sum_Ico_succ_bot hlt]; ring

/-- A loop along a sequence of states with a uniform cost bound. -/
lemma loop_seq_const {c} (n : ℕ) (S : ℕ → HSt R) (C : ℕ)
    (hc : ∀ k < n, c (S k).view = true) (hn : c (S n).view = false)
    (hb : ∀ k < n, HLe x w p (S k) (S (k + 1)) C) :
    HLe x w (.loop c p) (S 0) (S n) (n * (C + 1) + 1) := by
  refine (loop_seq n S (fun _ => C) hc hn hb).mono (le_of_eq ?_)
  simp

end HLe

/-! ## Views -/

namespace HSt

lemma view_isSome_iff (st : HSt R) (r : Fin R) : (st.view r).isSome = true ↔ st.env r ≠ 0 := by
  unfold view; split_ifs with h <;> simp [h]

@[simp] lemma set_set_same (st : HSt R) (r : Fin R) (u v : ℕ) :
    (st.set r u).set r v = st.set r v := by
  ext <;> simp [set]

@[simp] lemma set_self (st : HSt R) (r : Fin R) : st.set r (st.env r) = st := by
  ext <;> simp [set]

@[simp] lemma set_env_self (st : HSt R) (r : Fin R) (v : ℕ) : (st.set r v).env r = v := by
  simp [set]

lemma set_env_ne (st : HSt R) {r s : Fin R} (h : s ≠ r) (v : ℕ) : (st.set r v).env s = st.env s := by
  simp [set, Function.update_of_ne h]

end HSt

/-! ## Increment and constants -/

/-- `r := r + 1`, using the scratch register `t` (left at `1`). -/
def HProg.inc (r t : Fin R) : HProg R := .seq (.clr t) (.seq (.one t) (.add r t))

lemma inc_spec {r t : Fin R} (hrt : r ≠ t) {st : HSt R} (ht : st.env t < 2 ^ w)
    (hr : st.env r + 1 < 2 ^ w) :
    HLe x w (HProg.inc r t) st ((st.set t 1).set r (st.env r + 1)) (3 * unitCost w) := by
  have h2 : (1 : ℕ) < 2 ^ w := by omega
  refine ((HLe.of_runs (HRuns.clr ht)).seq ((HLe.of_runs (HRuns.one ?_)).seq
    (HLe.of_runs (HRuns.add hrt ?_)))).of_eq ?_ (by omega)
  · simpa using h2
  · simp [HSt.set_env_ne _ hrt]; omega
  · simp [HSt.set_env_ne _ hrt]

/-! ## Counting loops -/

/-- `for i ∈ [0, lim): body`, with the flag `f` (`[i < lim]`) and the scratch register `t`. -/
def HProg.forUp (i lim f t : Fin R) (body : HProg R) : HProg R :=
  .seq (.clr i) (.seq (.lt f i lim)
    (.loop (fun v => (v f).isSome) (.seq body (.seq (HProg.inc i t) (.lt f i lim)))))

/-- The flag value `[a < b]`. -/
def ltFlag (a b : ℕ) : ℕ := if a < b then 1 else 0

end Lax119563Proofs.Reduction

end Reduction_HLib

/-! ### Formerly `Lax119563Proofs.Reduction.HFrame` -/

section Reduction_HFrame

/-!
# Frame facts for register programs

Syntactic over-approximations of the effects of an `HProg`: the registers it may write
(`HProg.wr`), whether it may emit (`HProg.em`) and whether it may move the input cursor
(`HProg.mv`). A run keeps every register not written, the output if nothing is emitted, and
the cursor if it is not moved. Runs keep all registers below `2 ^ w` (`HRuns.bounded`).
-/

namespace Lax119563Proofs.Reduction

variable {R : ℕ} {x : List Bool} {w : ℕ}

namespace HProg

/-- The registers a program may write. -/
def wr : HProg R → Fin R → Bool
  | .clr r, q => decide (q = r)
  | .one r, q => decide (q = r)
  | .dbl r, q => decide (q = r)
  | .half r, q => decide (q = r)
  | .copy _ s, q => decide (q = s)
  | .add r _, q => decide (q = r)
  | .lt f _ _, q => decide (q = f)
  | .emit _, _ => false
  | .rd r, q => decide (q = r)
  | .rst, _ => false
  | .seq p p', q => p.wr q || p'.wr q
  | .ite _ p p', q => p.wr q || p'.wr q
  | .loop _ p, q => p.wr q

/-- The program may emit. -/
def em : HProg R → Bool
  | .emit _ => true
  | .seq p p' => p.em || p'.em
  | .ite _ p p' => p.em || p'.em
  | .loop _ p => p.em
  | _ => false

/-- The program may move the input cursor. -/
def mv : HProg R → Bool
  | .rd _ => true
  | .rst => true
  | .seq p p' => p.mv || p'.mv
  | .ite _ p p' => p.mv || p'.mv
  | .loop _ p => p.mv
  | _ => false

end HProg

/-- All registers are below `2 ^ w`. -/
def HSt.Bdd (w : ℕ) (st : HSt R) : Prop := ∀ q, st.env q < 2 ^ w

lemma rdVal_le (l : List Bool) : rdVal l ≤ 2 := by
  rcases l with _ | ⟨b, _⟩
  · simp [rdVal]
  · cases b <;> simp [rdVal]

lemma inBit_le (x : List Bool) (pos : ℕ) : inBit x pos ≤ 2 := rdVal_le _

lemma HRuns.frame {p : HProg R} {st st' : HSt R} {t : ℕ} (h : HRuns x w p st st' t) {q : Fin R}
    (hq : p.wr q = false) : st'.env q = st.env q := by
  induction h with
  | seq _ _ ih₁ ih₂ =>
    simp only [HProg.wr, Bool.or_eq_false_iff] at hq
    rw [ih₂ hq.2, ih₁ hq.1]
  | iteT _ _ ih => simp only [HProg.wr, Bool.or_eq_false_iff] at hq; exact ih hq.1
  | iteF _ _ ih => simp only [HProg.wr, Bool.or_eq_false_iff] at hq; exact ih hq.2
  | loopF => rfl
  | loopT _ _ _ ih₁ ih₂ => rw [ih₂ hq, ih₁ hq]
  | emit => rfl
  | rst => rfl
  | _ =>
    simp only [HProg.wr, decide_eq_false_iff_not] at hq
    simp [HSt.set, Function.update_of_ne hq]

lemma HRuns.out_eq {p : HProg R} {st st' : HSt R} {t : ℕ} (h : HRuns x w p st st' t)
    (hp : p.em = false) : st'.out = st.out := by
  induction h with
  | seq _ _ ih₁ ih₂ =>
    simp only [HProg.em, Bool.or_eq_false_iff] at hp
    rw [ih₂ hp.2, ih₁ hp.1]
  | iteT _ _ ih => simp only [HProg.em, Bool.or_eq_false_iff] at hp; exact ih hp.1
  | iteF _ _ ih => simp only [HProg.em, Bool.or_eq_false_iff] at hp; exact ih hp.2
  | loopF => rfl
  | loopT _ _ _ ih₁ ih₂ => rw [ih₂ hp, ih₁ hp]
  | emit => simp [HProg.em] at hp
  | _ => rfl

lemma HRuns.pos_eq {p : HProg R} {st st' : HSt R} {t : ℕ} (h : HRuns x w p st st' t)
    (hp : p.mv = false) : st'.pos = st.pos := by
  induction h with
  | seq _ _ ih₁ ih₂ =>
    simp only [HProg.mv, Bool.or_eq_false_iff] at hp
    rw [ih₂ hp.2, ih₁ hp.1]
  | iteT _ _ ih => simp only [HProg.mv, Bool.or_eq_false_iff] at hp; exact ih hp.1
  | iteF _ _ ih => simp only [HProg.mv, Bool.or_eq_false_iff] at hp; exact ih hp.2
  | loopF => rfl
  | loopT _ _ _ ih₁ ih₂ => rw [ih₂ hp, ih₁ hp]
  | rd => simp [HProg.mv] at hp
  | rst => simp [HProg.mv] at hp
  | _ => rfl

lemma HRuns.bounded {p : HProg R} {st st' : HSt R} {t : ℕ} (h : HRuns x w p st st' t)
    (hw : 2 ≤ w) (hb : st.Bdd w) : st'.Bdd w := by
  have h2 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  induction h with
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hb)
  | iteT _ _ ih => exact ih hb
  | iteF _ _ ih => exact ih hb
  | loopF => exact hb
  | loopT _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ hb)
  | emit => exact hb
  | rst => exact hb
  | clr =>
    intro q; simp only [HSt.set, Function.update_apply]; split_ifs
    · positivity
    · exact hb q
  | one h' =>
    intro q; simp only [HSt.set, Function.update_apply]; split_ifs
    · exact h'
    · exact hb q
  | dbl h' =>
    intro q; simp only [HSt.set, Function.update_apply]; split_ifs
    · exact h'
    · exact hb q
  | half h' =>
    intro q; simp only [HSt.set, Function.update_apply]; split_ifs
    · exact lt_of_le_of_lt (Nat.div_le_self _ _) h'
    · exact hb q
  | copy _ h' =>
    intro q; simp only [HSt.set, Function.update_apply]; split_ifs
    · exact h'
    · exact hb q
  | add _ h' =>
    intro q; simp only [HSt.set, Function.update_apply]; split_ifs
    · exact h'
    · exact hb q
  | lt =>
    intro q; simp only [HSt.set, Function.update_apply]; split_ifs
    · omega
    · omega
    · exact hb q
  | rd =>
    intro q; simp only [HSt.set, Function.update_apply]; split_ifs
    · have h4 : (4 : ℕ) ≤ 2 ^ w := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
      exact lt_of_le_of_lt (inBit_le _ _) (by omega)
    · exact hb q

lemma HLe.frame {p : HProg R} {st st' : HSt R} {T : ℕ} (h : HLe x w p st st' T) {q : Fin R}
    (hq : p.wr q = false) : st'.env q = st.env q := by
  obtain ⟨t, -, h⟩ := h; exact h.frame hq

lemma HLe.out_eq {p : HProg R} {st st' : HSt R} {T : ℕ} (h : HLe x w p st st' T)
    (hp : p.em = false) : st'.out = st.out := by
  obtain ⟨t, -, h⟩ := h; exact h.out_eq hp

lemma HLe.pos_eq {p : HProg R} {st st' : HSt R} {T : ℕ} (h : HLe x w p st st' T)
    (hp : p.mv = false) : st'.pos = st.pos := by
  obtain ⟨t, -, h⟩ := h; exact h.pos_eq hp

lemma HLe.bounded {p : HProg R} {st st' : HSt R} {T : ℕ} (h : HLe x w p st st' T)
    (hw : 2 ≤ w) (hb : st.Bdd w) : st'.Bdd w := by
  obtain ⟨t, -, h⟩ := h; exact h.bounded hw hb

end Lax119563Proofs.Reduction

end Reduction_HFrame

/-! ### Formerly `Lax119563Proofs.Reduction.HMachine` -/

section Reduction_HMachine

/-!
# Machines computing the output of register programs

`HProg.machine p` runs the compiled program `p` and then moves the output to tape `0`
(popping the input tape once per output symbol, so that the head returns to cell `0` after
the output has been pushed). `HProg.computesWithin`: if `p` runs from the zero state to a
state with cursor `0` that has emitted `out`, with `|x| ≤ |encodeNats out|`, then the machine
computes `encodeNats out` from `x` within the cost of the run plus `O(|encodeNats out|)`.
-/

open Function Lax119563.BinaryEncodings Lax119563.DeterministicTime
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Reduction

open Hierarchy Hierarchy.Prog Prog

variable {R : ℕ}

/-- Move the reversed output from `t₀` to `t₁`, popping the input tape once per symbol. -/
def countLoop : Hierarchy.Prog (R + 7) 0 :=
  .loop (fun t => (t sT0).isSome) (.seq (moveOne sT0 sT1) (.pop sIo))

/-- The output phase. -/
def finalP : Hierarchy.Prog (R + 7) 0 :=
  .seq (moveAll sOut sT0) (.seq countLoop (moveAll sT1 sIo))

/-- The machine of a register program. -/
noncomputable def HProg.machine (p : HProg R) : Machine :=
  Hierarchy.Prog.toMachine (K := R + 6) (.seq (compileH p) finalP) (fun _ => false)

lemma countLoop_runsH : ∀ (l : List Sym) (S : Stacks (R + 7) 0) (hd : Fin (R + 7) → ℤ),
    S sT0 = l →
    ∃ hd' : Fin (R + 7) → ℤ, hd' sIo = hd sIo + l.length ∧
      RunsLeH countLoop (S, hd)
        (update (update (update S sT0 []) sT1 (l.reverse ++ S sT1)) sIo
          ((S sIo).drop l.length), hd') (7 * l.length + 1)
  | [], S, hd, hS => by
    refine ⟨hd, by simp, (RunsLeH.loopF (by simp [tops, hS])).of_eq ?_ (by simp)⟩
    refine Prod.ext ?_ rfl
    funext k; simp only [update_apply]; split_ifs <;> simp_all
  | a :: l, S, hd, hS => by
    have h01 : (sT0 : Fin (R + 7)) ≠ sT1 := by dist
    have h0i : (sT0 : Fin (R + 7)) ≠ sIo := by dist
    have h1i : (sT1 : Fin (R + 7)) ≠ sIo := by dist
    have r₁ := moveOne_runsH h01 (hd := hd) hS
    set S₁ := update (update S sT0 l) sT1 (a :: S sT1)
    set hd₁ := update (update hd sT0 (hd sT0 + 1)) sT1 (hd sT1 - 1)
    have r₂ : RunsLeH (.pop sIo) (S₁, hd₁)
        (update S₁ sIo (S₁ sIo).tail, update hd₁ sIo (hd₁ sIo + 1)) 1 := ⟨1, le_rfl, .pop⟩
    obtain ⟨hd', e', r₃⟩ := countLoop_runsH l (update S₁ sIo (S₁ sIo).tail)
      (update hd₁ sIo (hd₁ sIo + 1)) (by simp [S₁, update_of_ne h0i, update_of_ne h01])
    refine ⟨hd', ?_, (RunsLeH.loopT (by simp [tops, hS]) (r₁.seq r₂) r₃).of_eq ?_ ?_⟩
    · rw [e']
      simp [hd₁, update_of_ne h0i.symm, update_of_ne h1i.symm]; ring
    · refine Prod.ext ?_ rfl
      have e1 : S₁ sIo = S sIo := by simp [S₁, update_of_ne h0i.symm, update_of_ne h1i.symm]
      funext k
      simp only [update_apply, S₁] at *
      split_ifs <;> simp_all [List.drop_tail]
    · simp; omega

lemma enc_init (x : List Bool) :
    enc x (⟨fun _ => 0, 0, []⟩ : HSt R) = inputStacks (R + 6) 0 x := by
  funext i
  unfold enc inputStacks
  by_cases h0 : i = 0
  · subst h0; simp [bs, sym, bitSym]
  · have : i.val ≠ 0 := fun e => h0 (Fin.ext e)
    simp [h0, this, encodeNats]

lemma ComputesWithin.mono {M : Machine} {x y : List Bool} {t t' : ℕ}
    (h : ComputesWithin M x y t) (ht : t ≤ t') : ComputesWithin M x y t' := by
  have e := Circuits.runOn_halted (M := M) x h.1 (t' - t)
  rw [Nat.add_sub_cancel' ht] at e
  unfold ComputesWithin HaltsWithin at *
  rw [e]; exact h

/-- **Machines of register programs.** -/
theorem HProg.computesWithin {p : HProg R} {x : List Bool} {w t : ℕ} {st' : HSt R}
    (h : HRuns x w p ⟨fun _ => 0, 0, []⟩ st' t) (hpos : st'.pos = 0)
    (hlen : x.length ≤ (encodeNats st'.out).length) :
    ComputesWithin p.machine x (encodeNats st'.out)
      (t + 20 * (encodeNats st'.out).length + 4) := by
  set y := encodeNats st'.out
  obtain ⟨hd₁, e₁, r₁⟩ := compileH_runs h (by simp) (fun _ => 0) (by simp)
  rw [hpos] at e₁
  -- the output phase
  have hoi : (sOut : Fin (R + 7)) ≠ sIo := by dist
  have h0i : (sT0 : Fin (R + 7)) ≠ sIo := by dist
  have h1i : (sT1 : Fin (R + 7)) ≠ sIo := by dist
  have ho0 : (sOut : Fin (R + 7)) ≠ sT0 := by dist
  have ho1 : (sOut : Fin (R + 7)) ≠ sT1 := by dist
  have h01 : (sT0 : Fin (R + 7)) ≠ sT1 := by dist
  have a₁ := moveAll_runs ho0 (m := 0) ((bs y).reverse) (enc x st') (enc_out x st')
  obtain ⟨hd₂, e₂, r₂⟩ := RunsLe.toH a₁ (avoids_moveAll hoi h0i) hd₁
  set S₂ := update (update (enc x st') sOut []) sT0 ((bs y).reverse.reverse ++ enc x st' sT0)
  obtain ⟨hd₃, e₃, r₃⟩ := countLoop_runsH (bs y) S₂ hd₂ (by simp [S₂])
  set S₃ := update (update (update S₂ sT0 []) sT1 ((bs y).reverse ++ S₂ sT1)) sIo
    ((S₂ sIo).drop (bs y).length)
  have r₄ := moveAll_runsH h1i (m := 0) ((bs y).reverse) S₃ hd₃
    (by simp [S₃, S₂, update_of_ne h1i, update_of_ne h01.symm, update_of_ne ho1.symm])
  have hrun := ((r₁.seq (r₂.seq (r₃.seq r₄))))
  obtain ⟨t₀, ht₀, hrunH⟩ := hrun
  rw [enc_init] at hrunH
  have hc := Prog.computesWithin (K := R + 6) (ans := fun _ => false) (y := y) hrunH ?_ ?_
  · refine ComputesWithin.mono hc ?_
    simp only [length_bs, List.length_reverse] at ht₀
    omega
  · -- the input tape holds the output
    have hio : S₃ sIo = [] := by
      simp only [S₃, update_self, S₂, update_of_ne hoi.symm, update_of_ne h0i.symm,
        enc_io, hpos, List.drop_zero, length_bs]
      exact List.drop_eq_nil_of_le (by simpa using hlen)
    show update (update S₃ sT1 []) sIo ((bs y).reverse.reverse ++ S₃ sIo) sIo = _
    rw [update_self, hio, List.reverse_reverse, List.append_nil]
    rfl
  · show update (update hd₃ sT1 (hd₃ sT1 + _)) sIo (hd₃ sIo - _) sIo = 0
    rw [update_self, e₃, e₂, e₁]
    simp

end Lax119563Proofs.Reduction

end Reduction_HMachine

/-! ### Formerly `Lax119563Proofs.Reduction.SProg` -/

section Reduction_SProg

/-!
# Structured programs with expressions

A layer above `HProg` with a total denotational semantics, so that the output and the cost of
the reduction program can be computed by equational reasoning instead of by runs.

* Expressions `Ex R` over user registers `Fin R`: variables, constants, `+`, `[a < b]`,
  `a / 2`, `a % 2`.
* Statements `Stm R`: `skip`, `set r e`, `emit e`, sequencing, `ite c p q` (`c ≠ 0`), and
  counting loops `loop i lim body` (`i = 0, …, lim - 1`, the bound read once) and
  `loopX i lim xb body`, which additionally sets `xb := x[i]` (bit `i` of the input, `0` beyond
  its end) at the start of every iteration.

`Stm.exec x c env` is the final register valuation and the emitted list; `Stm.cost x w c env`
is a cost bound and `Stm.Fits x w c env` says that all values stay below `2 ^ w`.
`Stm.code R D c : HProg (R + D + 1)` compiles a statement with `D + 1` scratch registers
(`Stm.code_spec`): it runs within `cost` and produces the denotation.
-/

namespace Lax119563Proofs.Reduction

variable {R D : ℕ} {x : List Bool} {w : ℕ}

/-! ## Registers -/

/-- User register `r` among `R + D + 1` registers. -/
def ur (D : ℕ) (r : Fin R) : Fin (R + D + 1) := ⟨r.val, by omega⟩

/-- Scratch register `k` (the registers `R, …, R + D`; indices beyond `D` are identified). -/
def sc (R D k : ℕ) : Fin (R + D + 1) := ⟨R + min k D, by omega⟩

lemma ur_ne_sc (r : Fin R) (k : ℕ) : ur D r ≠ sc R D k := by
  intro h; have := congrArg Fin.val h; simp only [ur, sc] at this; omega

lemma sc_ne_ur (r : Fin R) (k : ℕ) : sc R D k ≠ ur D r := (ur_ne_sc r k).symm

lemma sc_ne {k j : ℕ} (hk : k < D) (hkj : k < j) : sc R D k ≠ sc R D j := by
  intro h; have := congrArg Fin.val h; simp only [sc] at this; omega

lemma ur_inj {r q : Fin R} : ur D r = ur D q ↔ r = q := by
  constructor
  · intro h; exact Fin.ext (by simpa [ur] using congrArg Fin.val h)
  · rintro rfl; rfl

/-- The user registers of a state. -/
def uenv (D : ℕ) (st : HSt (R + D + 1)) : Fin R → ℕ := fun r => st.env (ur D r)

/-! ## Constants -/

/-- `r := c`. -/
def setK {N : ℕ} (r : Fin N) (c : ℕ) : HProg N :=
  if c = 0 then .clr r else .seq (setK r (c / 2)) (if c % 2 = 1 then .one r else .dbl r)
termination_by c
decreasing_by omega

lemma setK_wr {N : ℕ} (r q : Fin N) (c : ℕ) : (setK r c).wr q = true → q = r := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rw [setK]
    split_ifs with h1 h2
    · simp [HProg.wr]
    · simp only [HProg.wr, Bool.or_eq_true, decide_eq_true_eq]
      rintro (h | h)
      · exact ih _ (by omega) h
      · exact h
    · simp only [HProg.wr, Bool.or_eq_true, decide_eq_true_eq]
      rintro (h | h)
      · exact ih _ (by omega) h
      · exact h

lemma setK_em {N : ℕ} (r : Fin N) (c : ℕ) : (setK r c).em = false := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rw [setK]
    split_ifs with h1 h2
    · rfl
    · simp [HProg.em, ih _ (show c / 2 < c by omega)]
    · simp [HProg.em, ih _ (show c / 2 < c by omega)]

lemma setK_mv {N : ℕ} (r : Fin N) (c : ℕ) : (setK r c).mv = false := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rw [setK]
    split_ifs with h1 h2
    · rfl
    · simp [HProg.mv, ih _ (show c / 2 < c by omega)]
    · simp [HProg.mv, ih _ (show c / 2 < c by omega)]

lemma setK_spec {N : ℕ} (r : Fin N) : ∀ (m c : ℕ), c < 2 ^ m → m ≤ w → ∀ st : HSt N,
    st.env r < 2 ^ w → HLe x w (setK r c) st (st.set r c) ((m + 1) * unitCost w) := by
  intro m
  induction m with
  | zero =>
    intro c hc _ st hr
    have : c = 0 := by simpa using hc
    subst this
    rw [setK, if_pos rfl]
    exact (HLe.of_runs (HRuns.clr hr)).mono (by simp)
  | succ m ih =>
    intro c hc hm st hr
    rw [setK]
    split_ifs with h1 h2
    · subst h1; exact (HLe.of_runs (HRuns.clr hr)).mono (by nlinarith)
    · have h := ih (c / 2) (by rw [pow_succ] at hc; omega) (by omega) st hr
      have hlt : 2 * (st.set r (c / 2)).env r + 1 < 2 ^ w := by
        have : c < 2 ^ w := lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hm)
        simp; omega
      refine (h.seq (HLe.of_runs (HRuns.one hlt))).of_eq ?_ (by ring_nf; omega)
      simp only [HSt.set_env_self, HSt.set_set_same]
      congr 1; omega
    · have h := ih (c / 2) (by rw [pow_succ] at hc; omega) (by omega) st hr
      have hlt : 2 * (st.set r (c / 2)).env r < 2 ^ w := by
        have : c < 2 ^ w := lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hm)
        simp; omega
      refine (h.seq (HLe.of_runs (HRuns.dbl hlt))).of_eq ?_ (by ring_nf; omega)
      simp only [HSt.set_env_self, HSt.set_set_same]
      congr 1; omega

/-! ## Expressions -/

/-- Expressions over the user registers. -/
inductive Ex (R : ℕ) where
  | var (r : Fin R)
  | const (c : ℕ)
  | add (a b : Ex R)
  | lt (a b : Ex R)
  | half (a : Ex R)
  | odd (a : Ex R)

namespace Ex

/-- The value of an expression. -/
def eval (env : Fin R → ℕ) : Ex R → ℕ
  | var r => env r
  | const c => c
  | add a b => eval env a + eval env b
  | lt a b => if eval env a < eval env b then 1 else 0
  | half a => eval env a / 2
  | odd a => eval env a % 2

/-- The number of nodes. -/
def size : Ex R → ℕ
  | var _ => 1
  | const _ => 1
  | add a b => size a + size b + 1
  | lt a b => size a + size b + 1
  | half a => size a + 1
  | odd a => size a + 1

/-- The number of scratch registers used. -/
def depth : Ex R → ℕ
  | var _ => 1
  | const _ => 1
  | add a b => max (depth a) (depth b + 1)
  | lt a b => max 3 (max (depth a + 1) (depth b + 2))
  | half a => depth a
  | odd a => depth a

lemma one_le_depth : ∀ e : Ex R, 1 ≤ e.depth
  | var _ => le_rfl
  | const _ => le_rfl
  | add a _ => le_trans (one_le_depth a) (le_max_left _ _)
  | lt _ _ => le_trans (by norm_num) (le_max_left _ _)
  | half a => one_le_depth a
  | odd a => one_le_depth a

/-- All values computed while evaluating the expression are below `2 ^ w`. -/
def Fits (w : ℕ) (env : Fin R → ℕ) : Ex R → Prop
  | var r => env r < 2 ^ w
  | const c => c < 2 ^ w
  | add a b => Fits w env a ∧ Fits w env b ∧ eval env a + eval env b < 2 ^ w
  | lt a b => Fits w env a ∧ Fits w env b
  | half a => Fits w env a
  | odd a => Fits w env a

/-- Evaluate into scratch register `k`, using the scratch registers from `k` on. -/
def code (R D : ℕ) : ℕ → Ex R → HProg (R + D + 1)
  | k, var r => .copy (ur D r) (sc R D k)
  | k, const c => setK (sc R D k) c
  | k, add a b => .seq (code R D k a) (.seq (code R D (k + 1) b) (.add (sc R D k) (sc R D (k + 1))))
  | k, lt a b => .seq (code R D (k + 1) a)
      (.seq (code R D (k + 2) b) (.lt (sc R D k) (sc R D (k + 1)) (sc R D (k + 2))))
  | k, half a => .seq (code R D k a) (.half (sc R D k))
  | k, odd a => .seq (code R D k a)
      (.ite (fun v => v (sc R D k) == some true) (setK (sc R D k) 1) (.clr (sc R D k)))

lemma code_wr : ∀ (e : Ex R) (k : ℕ) (q : Fin (R + D + 1)), (code R D k e).wr q = true →
    ∃ j, k ≤ j ∧ q = sc R D j
  | var r, k, q, h => ⟨k, le_rfl, by simpa [code, HProg.wr] using h⟩
  | const c, k, q, h => ⟨k, le_rfl, setK_wr _ _ _ h⟩
  | add a b, k, q, h => by
    simp only [code, HProg.wr, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h | h
    · exact code_wr a k q h
    · obtain ⟨j, hj, rfl⟩ := code_wr b (k + 1) q h; exact ⟨j, by omega, rfl⟩
    · exact ⟨k, le_rfl, h⟩
  | lt a b, k, q, h => by
    simp only [code, HProg.wr, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h | h
    · obtain ⟨j, hj, rfl⟩ := code_wr a (k + 1) q h; exact ⟨j, by omega, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := code_wr b (k + 2) q h; exact ⟨j, by omega, rfl⟩
    · exact ⟨k, le_rfl, h⟩
  | half a, k, q, h => by
    simp only [code, HProg.wr, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · exact code_wr a k q h
    · exact ⟨k, le_rfl, h⟩
  | odd a, k, q, h => by
    simp only [code, HProg.wr, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h | h
    · exact code_wr a k q h
    · exact ⟨k, le_rfl, setK_wr _ _ _ h⟩
    · exact ⟨k, le_rfl, h⟩

lemma code_em : ∀ (e : Ex R) (k : ℕ), (code R D k e).em = false
  | var _, _ => rfl
  | const _, _ => setK_em _ _
  | add a b, k => by simp [code, HProg.em, code_em a, code_em b]
  | lt a b, k => by simp [code, HProg.em, code_em a, code_em b]
  | half a, k => by simp [code, HProg.em, code_em a]
  | odd a, k => by simp [code, HProg.em, code_em a, setK_em]

lemma code_mv : ∀ (e : Ex R) (k : ℕ), (code R D k e).mv = false
  | var _, _ => rfl
  | const _, _ => setK_mv _ _
  | add a b, k => by simp [code, HProg.mv, code_mv a, code_mv b]
  | lt a b, k => by simp [code, HProg.mv, code_mv a, code_mv b]
  | half a, k => by simp [code, HProg.mv, code_mv a]
  | odd a, k => by simp [code, HProg.mv, code_mv a, setK_mv]

lemma code_wr_ur (e : Ex R) (k : ℕ) (r : Fin R) : (code R D k e).wr (ur D r) = false := by
  cases h : (code R D k e).wr (ur D r)
  · rfl
  · obtain ⟨j, -, hj⟩ := code_wr e k _ h
    exact absurd hj (ur_ne_sc r j)

lemma code_uenv {e : Ex R} {k : ℕ} {st st' : HSt (R + D + 1)} {T : ℕ}
    (h : HLe x w (code R D k e) st st' T) : uenv D st' = uenv D st := by
  funext r; exact h.frame (code_wr_ur e k r)

lemma code_keep {e : Ex R} {k j : ℕ} (hj : j < D) (hjk : j < k) {st st' : HSt (R + D + 1)}
    {T : ℕ} (h : HLe x w (code R D k e) st st' T) : st'.env (sc R D j) = st.env (sc R D j) := by
  apply h.frame
  cases hw : (code R D k e).wr (sc R D j)
  · rfl
  · obtain ⟨i, hi, he⟩ := code_wr e k _ hw
    exact absurd he (sc_ne hj (by omega))

/-- The unit cost of an expression node. -/
def nodeCost (w : ℕ) : ℕ := (w + 3) * unitCost w

lemma unitCost_le_nodeCost (w : ℕ) : unitCost w ≤ nodeCost w := by
  unfold nodeCost; nlinarith

lemma code_spec (hw : 2 ≤ w) : ∀ (e : Ex R) (k : ℕ) (st : HSt (R + D + 1)),
    k + e.depth ≤ D → st.Bdd w → e.Fits w (uenv D st) →
    ∃ st', HLe x w (code R D k e) st st' (e.size * nodeCost w) ∧
      st'.env (sc R D k) = e.eval (uenv D st)
  | var r, k, st, hk, hb, hf => by
    refine ⟨_, (HLe.of_runs (HRuns.copy (ur_ne_sc r k) (hb _) (hb _))).mono ?_, by simp [eval, uenv]⟩
    simp [size, unitCost_le_nodeCost]
  | const c, k, st, hk, hb, hf => by
    refine ⟨_, (setK_spec (sc R D k) w c hf le_rfl st (hb _)).mono ?_, by simp [eval]⟩
    simp only [size, nodeCost, one_mul]; nlinarith
  | add a b, k, st, hk, hb, hf => by
    simp only [depth] at hk
    obtain ⟨hfa, hfb, hab⟩ := hf
    obtain ⟨st₁, h₁, e₁⟩ := code_spec hw a k st (by omega) hb hfa
    have u₁ := code_uenv h₁
    have hb₁ := h₁.bounded hw hb
    obtain ⟨st₂, h₂, e₂⟩ := code_spec hw b (k + 1) st₁ (by omega) hb₁ (by rw [u₁]; exact hfb)
    have u₂ := code_uenv h₂
    have k₂ := code_keep (j := k) (by have := one_le_depth b; omega) (by omega) h₂
    have hb₂ := h₂.bounded hw hb₁
    have hadd : st₂.env (sc R D k) + st₂.env (sc R D (k + 1)) < 2 ^ w := by
      rw [k₂, e₁, e₂, u₁]; exact hab
    refine ⟨_, (h₁.seq (h₂.seq (HLe.of_runs (HRuns.add
      (sc_ne (by have := one_le_depth b; omega) (by omega)) hadd)))).mono ?_, ?_⟩
    · simp only [size]; have := unitCost_le_nodeCost w; nlinarith
    · simp [k₂, e₁, e₂, u₁, eval]
  | lt a b, k, st, hk, hb, hf => by
    simp only [depth] at hk
    obtain ⟨hfa, hfb⟩ := hf
    obtain ⟨st₁, h₁, e₁⟩ := code_spec hw a (k + 1) st (by omega) hb hfa
    have u₁ := code_uenv h₁
    have hb₁ := h₁.bounded hw hb
    obtain ⟨st₂, h₂, e₂⟩ := code_spec hw b (k + 2) st₁ (by omega) hb₁ (by rw [u₁]; exact hfb)
    have u₂ := code_uenv h₂
    have k₂ := code_keep (j := k + 1) (by omega) (by omega) h₂
    have hb₂ := h₂.bounded hw hb₁
    refine ⟨_, (h₁.seq (h₂.seq (HLe.of_runs (HRuns.lt (sc_ne (by omega) (by omega))
      (sc_ne (by omega) (by omega)) (sc_ne (by omega) (by omega)) (hb₂ _) (hb₂ _)
      (hb₂ _))))).mono ?_, ?_⟩
    · simp only [size]; have := unitCost_le_nodeCost w; nlinarith
    · simp [k₂, e₁, e₂, u₁, eval]
  | half a, k, st, hk, hb, hf => by
    simp only [depth] at hk
    obtain ⟨st₁, h₁, e₁⟩ := code_spec hw a k st (by omega) hb hf
    have hb₁ := h₁.bounded hw hb
    refine ⟨_, (h₁.seq (HLe.of_runs (HRuns.half (hb₁ _)))).mono ?_, ?_⟩
    · simp only [size]; have := unitCost_le_nodeCost w; nlinarith
    · simp [e₁, eval]
  | odd a, k, st, hk, hb, hf => by
    simp only [depth] at hk
    obtain ⟨st₁, h₁, e₁⟩ := code_spec hw a k st (by omega) hb hf
    have hb₁ := h₁.bounded hw hb
    have h2 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
    have hU : 1 ≤ unitCost w := by unfold unitCost; omega
    by_cases hodd : st₁.env (sc R D k) % 2 = 1
    · have hc : (st₁.view (sc R D k) == some true) = true := by
        simp [HSt.view, hodd]; omega
      have h₂ := setK_spec (x := x) (sc R D k) 1 1 (by norm_num) (by omega) st₁ (hb₁ _)
      refine ⟨_, (h₁.seq (HLe.iteT (c := fun v => v (sc R D k) == some true)
        (q := .clr (sc R D k)) hc h₂)).mono ?_, ?_⟩
      · simp only [size, nodeCost]; nlinarith
      · simp [eval, ← e₁, hodd]
    · have hc : (st₁.view (sc R D k) == some true) = false := by
        simp [HSt.view]; omega
      refine ⟨_, (h₁.seq (HLe.iteF (c := fun v => v (sc R D k) == some true)
        (p := setK (sc R D k) 1) hc (HLe.of_runs (HRuns.clr (hb₁ _))))).mono ?_, ?_⟩
      · simp only [size, nodeCost]; nlinarith
      · simp [eval, ← e₁]; omega

end Ex

end Lax119563Proofs.Reduction

end Reduction_SProg

/-! ### Formerly `Lax119563Proofs.Reduction.SStm` -/

section Reduction_SStm

/-!
# Structured statements and their compilation

Statements `Stm R`: `skip`, `set r e`, `emit e`, sequencing, `ite c p q` (`c ≠ 0`), counting
loops `loop i lim body` (`i = 0, …, lim - 1`, the bound read once) and `loopX i lim xb body`,
which additionally sets `xb := x[i]` (bit `i` of the input, `0` beyond its end) at the start
of every iteration.

`Stm.exec x c env` is the final valuation and the emitted list; `Stm.cost x w c env` is a cost
bound and `Stm.Fits x w c env` says that all values stay below `2 ^ w`. `Stm.code R D c`
compiles a statement to `HProg (R + D + 1)`, and `Stm.code_spec` says that the compiled
program runs within `cost` and produces the denotation.
-/

namespace Lax119563Proofs.Reduction

variable {R D : ℕ} {x : List Bool} {w : ℕ}

/-! ## Counting loops with an invariant -/

lemma forUp_inv {N : ℕ} {i lim f t : Fin N} {body : HProg N} (hil : i ≠ lim) (hif : i ≠ f)
    (hit : i ≠ t) (hlf : lim ≠ f) (hlt : lim ≠ t) (hft : f ≠ t) (hw : 2 ≤ w) (L : ℕ)
    (hL : L + 1 < 2 ^ w) (hbi : body.wr i = false) (hbl : body.wr lim = false)
    (Inv : ℕ → HSt N → Prop) (C : ℕ → ℕ)
    (hstep : ∀ k < L, ∀ σ : HSt N, Inv k σ → σ.Bdd w → σ.env i = k → σ.env lim = L →
      ∃ σ', HLe x w body σ σ' (C k) ∧ ∀ τ : HSt N, τ.out = σ'.out → τ.pos = σ'.pos →
        (∀ q, q ≠ i → q ≠ f → q ≠ t → τ.env q = σ'.env q) → τ.env i = k + 1 → Inv (k + 1) τ)
    (st : HSt N) (hb : st.Bdd w) (hl : st.env lim = L)
    (h0 : ∀ τ : HSt N, τ.out = st.out → τ.pos = st.pos →
      (∀ q, q ≠ i → q ≠ f → q ≠ t → τ.env q = st.env q) → τ.env i = 0 → Inv 0 τ) :
    ∃ σ, HLe x w (HProg.forUp i lim f t body) st σ
      (∑ k ∈ Finset.range L, (C k + 4 * unitCost w + 1) + 2 * unitCost w + 1) ∧ Inv L σ := by
  have h2 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  set c : RView N → Bool := fun v => (v f).isSome
  set body' : HProg N := .seq body (.seq (HProg.inc i t) (.lt f i lim))
  have aux : ∀ m k (σ : HSt N), k + m = L → Inv k σ → σ.Bdd w → σ.env i = k →
      σ.env lim = L → σ.env f = ltFlag k L →
      ∃ σ', HLe x w (.loop c body') σ σ'
        (∑ j ∈ Finset.Ico k L, (C j + 4 * unitCost w + 1) + 1) ∧ Inv L σ' := by
    intro m
    induction m with
    | zero =>
      intro k σ hk hI _ _ _ hf
      have : k = L := by omega
      subst this
      refine ⟨σ, (HLe.loopF ?_).mono (by simp), hI⟩
      simp [c, HSt.view, hf, ltFlag]
    | succ m ih =>
      intro k σ hk hI hb' hi hl' hf
      have hkL : k < L := by omega
      obtain ⟨σ₁, h₁, hτ⟩ := hstep k hkL σ hI hb' hi hl'
      have hb₁ := h₁.bounded hw hb'
      have hi₁ : σ₁.env i = k := by rw [h₁.frame hbi, hi]
      have hl₁ : σ₁.env lim = L := by rw [h₁.frame hbl, hl']
      have hinc := inc_spec (x := x) hit (st := σ₁) (hb₁ t) (by omega)
      set σ₂ := (σ₁.set t 1).set i (σ₁.env i + 1)
      have hlt' : HLe x w (.lt f i lim) σ₂ (σ₂.set f (ltFlag (k + 1) L)) (unitCost w) := by
        have e : σ₂.set f (ltFlag (k + 1) L) =
            σ₂.set f (if σ₂.env i < σ₂.env lim then 1 else 0) := by
          simp [σ₂, HSt.set_env_ne _ hil.symm, HSt.set_env_ne _ hlt, hi₁, hl₁, ltFlag]
        rw [e]
        refine HLe.of_runs (HRuns.lt hif.symm hlf.symm hil ?_ ?_ ?_)
        · simp only [σ₂, HSt.set_env_ne _ hif.symm, HSt.set_env_ne _ hft]; exact hb₁ f
        · simp [σ₂]; omega
        · simp only [σ₂, HSt.set_env_ne _ hil.symm, HSt.set_env_ne _ hlt]; omega
      set σ₃ := σ₂.set f (ltFlag (k + 1) L)
      have hI₃ : Inv (k + 1) σ₃ := by
        apply hτ
        · rfl
        · rfl
        · intro q h1 h2 h3
          simp [σ₃, σ₂, HSt.set, Function.update_of_ne h1, Function.update_of_ne h2,
            Function.update_of_ne h3]
        · simp [σ₃, σ₂, Function.update_apply, hif, hi₁]
      have hb₃ : σ₃.Bdd w := (h₁.seq (hinc.seq hlt')).bounded hw hb'
      obtain ⟨σ', h', hI'⟩ := ih (k + 1) σ₃ (by omega) hI₃ hb₃
        (by simp [σ₃, σ₂, Function.update_apply, hif, hi₁])
        (by simp [σ₃, σ₂, Function.update_apply, hlf, hil.symm, hlt, hl₁])
        (by simp [σ₃])
      have hc : c σ.view = true := by
        simp only [c]; rw [HSt.view_isSome_iff, hf]; simp [ltFlag, hkL]
      refine ⟨σ', (HLe.loopT hc (h₁.seq (hinc.seq hlt')) h').mono ?_, hI'⟩
      rw [Finset.sum_eq_sum_Ico_succ_bot hkL]
      omega
  have hc1 : HLe x w (.clr i) st (st.set i 0) (unitCost w) := HLe.of_runs (HRuns.clr (hb i))
  have hc2 : HLe x w (.lt f i lim) (st.set i 0) ((st.set i 0).set f (ltFlag 0 L))
      (unitCost w) := by
    have e : (st.set i 0).set f (ltFlag 0 L) =
        (st.set i 0).set f (if (st.set i 0).env i < (st.set i 0).env lim then 1 else 0) := by
      simp [Function.update_apply, hil.symm, hl, ltFlag]
    rw [e]
    refine HLe.of_runs (HRuns.lt hif.symm hlf.symm hil ?_ ?_ ?_)
    · simp only [HSt.set_env_ne _ hif.symm]; exact hb f
    · simp
    · simp only [HSt.set_env_ne _ hil.symm]; exact hb lim
  set τ₀ := (st.set i 0).set f (ltFlag 0 L)
  have hI₀ : Inv 0 τ₀ := by
    apply h0
    · rfl
    · rfl
    · intro q h1 h2 _
      simp [τ₀, HSt.set, Function.update_of_ne h1, Function.update_of_ne h2]
    · simp [τ₀, Function.update_apply, hif]
  have hb₀ : τ₀.Bdd w := (hc1.seq hc2).bounded hw hb
  obtain ⟨σ, hσ, hI⟩ := aux L 0 τ₀ (by omega) hI₀ hb₀
    (by simp [τ₀, Function.update_apply, hif])
    (by simp [τ₀, Function.update_apply, hlf, hil.symm, hl])
    (by simp [τ₀])
  refine ⟨σ, (hc1.seq (hc2.seq hσ)).mono ?_, hI⟩
  rw [Finset.range_eq_Ico]
  omega

/-! ## Statements -/

/-- Statements over the user registers. -/
inductive Stm (R : ℕ) where
  | skip
  | set (r : Fin R) (e : Ex R)
  | emit (e : Ex R)
  | seq (p q : Stm R)
  | ite (c : Ex R) (p q : Stm R)
  | loop (i lim : Fin R) (body : Stm R)
  | loopX (i lim xb : Fin R) (body : Stm R)
  | len (r : Fin R)

/-- The first `k` iterations of a loop whose iteration `j` maps the valuation `e` to
`f j e` (final valuation, emitted list). -/
def runLoop (f : ℕ → (Fin R → ℕ) → (Fin R → ℕ) × List ℕ) :
    ℕ → (Fin R → ℕ) → (Fin R → ℕ) × List ℕ
  | 0, env => (env, [])
  | k + 1, env =>
    let a := runLoop f k env
    let b := f k a.1
    (b.1, a.2 ++ b.2)

namespace Stm

/-- The denotation: the final valuation and the emitted list. -/
def exec (x : List Bool) : Stm R → (Fin R → ℕ) → (Fin R → ℕ) × List ℕ
  | skip, env => (env, [])
  | set r e, env => (Function.update env r (e.eval env), [])
  | emit e, env => (env, [e.eval env])
  | seq p q, env =>
    let a := exec x p env
    let b := exec x q a.1
    (b.1, a.2 ++ b.2)
  | ite c p q, env => if c.eval env ≠ 0 then exec x p env else exec x q env
  | loop i lim body, env =>
    let a := runLoop (fun k e => exec x body (Function.update e i k)) (env lim) env
    (Function.update a.1 i (env lim), a.2)
  | loopX i lim xb body, env =>
    let a := runLoop (fun k e => exec x body
      (Function.update (Function.update e i k) xb (inBit x k))) (env lim) env
    (Function.update a.1 i (env lim), a.2)
  | len r, env => (Function.update env r x.length, [])

/-- A cost bound. -/
def cost (x : List Bool) (w : ℕ) : Stm R → (Fin R → ℕ) → ℕ
  | skip, _ => unitCost w
  | set _ e, _ => e.size * Ex.nodeCost w + unitCost w
  | emit e, _ => e.size * Ex.nodeCost w + unitCost w
  | seq p q, env => cost x w p env + cost x w q (exec x p env).1
  | ite c p q, env => c.size * Ex.nodeCost w + 1 +
      (if c.eval env ≠ 0 then cost x w p env else cost x w q env)
  | loop i lim body, env =>
    ∑ k ∈ Finset.range (env lim), (cost x w body (Function.update
      (runLoop (fun k e => exec x body (Function.update e i k)) k env).1 i k) +
        4 * unitCost w + 1) + 2 * unitCost w + 1
  | loopX i lim xb body, env =>
    unitCost w + (∑ k ∈ Finset.range (env lim), (unitCost w + cost x w body
      (Function.update (Function.update (runLoop (fun k e => exec x body
        (Function.update (Function.update e i k) xb (inBit x k))) k env).1 i k) xb
          (inBit x k)) + 4 * unitCost w + 1) + 2 * unitCost w + 1) +
      unitCost w * (x.length + 1)
  | len _, _ =>
    3 * unitCost w + x.length * (4 * unitCost w + 1) + 1 + unitCost w * (x.length + 1)

/-- All values stay below `2 ^ w`. -/
def Fits (x : List Bool) (w : ℕ) : Stm R → (Fin R → ℕ) → Prop
  | skip, _ => True
  | set _ e, env => e.Fits w env
  | emit e, env => e.Fits w env
  | seq p q, env => Fits x w p env ∧ Fits x w q (exec x p env).1
  | ite c p q, env => c.Fits w env ∧ (if c.eval env ≠ 0 then Fits x w p env else Fits x w q env)
  | loop i lim body, env => env lim + 1 < 2 ^ w ∧ ∀ k < env lim, Fits x w body
      (Function.update (runLoop (fun k e => exec x body (Function.update e i k)) k env).1 i k)
  | loopX i lim xb body, env => env lim + 1 < 2 ^ w ∧ ∀ k < env lim, Fits x w body
      (Function.update (Function.update (runLoop (fun k e => exec x body
        (Function.update (Function.update e i k) xb (inBit x k))) k env).1 i k) xb (inBit x k))
  | len _, _ => x.length + 1 < 2 ^ w

/-- The registers a statement may write. -/
def wr : Stm R → Fin R → Bool
  | skip, _ => false
  | set r _, q => decide (q = r)
  | emit _, _ => false
  | seq p p', q => wr p q || wr p' q
  | ite _ p p', q => wr p q || wr p' q
  | loop i _ body, q => decide (q = i) || wr body q
  | loopX i _ xb body, q => decide (q = i) || decide (q = xb) || wr body q
  | len r, q => decide (q = r)

/-- The statement contains no `loopX`. -/
def noX : Stm R → Bool
  | seq p q => noX p && noX q
  | ite _ p q => noX p && noX q
  | loop _ _ body => noX body
  | loopX .. => false
  | len _ => false
  | _ => true

/-- Well-formedness: loops keep their counter and bound. -/
def WF : Stm R → Prop
  | seq p q => WF p ∧ WF q
  | ite _ p q => WF p ∧ WF q
  | loop i lim body => i ≠ lim ∧ wr body i = false ∧ wr body lim = false ∧ WF body
  | loopX i lim xb body => i ≠ lim ∧ xb ≠ i ∧ xb ≠ lim ∧ wr body i = false ∧
      wr body lim = false ∧ noX body = true ∧ WF body
  | _ => True

/-- The number of scratch registers needed. -/
def depth : Stm R → ℕ
  | skip => 1
  | set _ e => e.depth
  | emit e => e.depth
  | seq p q => max (depth p) (depth q)
  | ite c p q => max c.depth (max (depth p) (depth q))
  | loop _ _ body => max 2 (depth body)
  | loopX _ _ _ body => max 2 (depth body)
  | len _ => 2

/-- Compilation to `HProg` with scratch registers `R, …, R + D`. -/
def code (R D : ℕ) : Stm R → HProg (R + D + 1)
  | skip => .clr (sc R D 0)
  | set r e => .seq (e.code R D 0) (.copy (sc R D 0) (ur D r))
  | emit e => .seq (e.code R D 0) (.emit (sc R D 0))
  | seq p q => .seq (code R D p) (code R D q)
  | ite c p q => .seq (c.code R D 0)
      (.ite (fun v => (v (sc R D 0)).isSome) (code R D p) (code R D q))
  | loop i lim body => HProg.forUp (ur D i) (ur D lim) (sc R D 0) (sc R D 1) (code R D body)
  | loopX i lim xb body => .seq .rst (.seq (HProg.forUp (ur D i) (ur D lim) (sc R D 0)
      (sc R D 1) (.seq (.rd (ur D xb)) (code R D body))) .rst)
  | len r => .seq .rst (.seq (.clr (ur D r)) (.seq (.rd (sc R D 0))
      (.seq (.loop (fun v => (v (sc R D 0)).isSome)
      (.seq (HProg.inc (ur D r) (sc R D 1)) (.rd (sc R D 0)))) .rst)))

lemma code_wr_ur : ∀ (c : Stm R) (r : Fin R), wr c r = false →
    (code R D c).wr (ur D r) = false
  | skip, r, _ => by simp [code, HProg.wr, ur_ne_sc]
  | set r' e, r, h => by
    simp only [wr, decide_eq_false_iff_not] at h
    simp [code, HProg.wr, Ex.code_wr_ur, ur_inj, h]
  | emit e, r, _ => by simp [code, HProg.wr, Ex.code_wr_ur]
  | seq p q, r, h => by
    simp only [wr, Bool.or_eq_false_iff] at h
    simp [code, HProg.wr, code_wr_ur p r h.1, code_wr_ur q r h.2]
  | ite c p q, r, h => by
    simp only [wr, Bool.or_eq_false_iff] at h
    simp [code, HProg.wr, Ex.code_wr_ur, code_wr_ur p r h.1, code_wr_ur q r h.2]
  | loop i lim body, r, h => by
    simp only [wr, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    simp [code, HProg.forUp, HProg.inc, HProg.wr, ur_inj, ur_ne_sc, h.1,
      code_wr_ur body r h.2]
  | loopX i lim xb body, r, h => by
    simp only [wr, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    simp [code, HProg.forUp, HProg.inc, HProg.wr, ur_inj, ur_ne_sc, h.1.1, h.1.2,
      code_wr_ur body r h.2]

  | len r', r, h => by
    simp only [wr, decide_eq_false_iff_not] at h
    simp [code, HProg.inc, HProg.wr, ur_inj, ur_ne_sc, h]

end Stm

lemma uenv_set_sc (st : HSt (R + D + 1)) (k v : ℕ) :
    uenv D (st.set (sc R D k) v) = uenv D st := by
  funext r; simp [uenv, HSt.set_env_ne _ (ur_ne_sc r k)]

lemma uenv_set_ur (st : HSt (R + D + 1)) (r : Fin R) (v : ℕ) :
    uenv D (st.set (ur D r) v) = Function.update (uenv D st) r v := by
  funext q
  by_cases h : q = r
  · subst h; simp [uenv]
  · simp [uenv, Function.update_of_ne h, HSt.set_env_ne _ (fun e => h (ur_inj.mp e))]

lemma inBit_min (x : List Bool) (k : ℕ) : inBit x (min k x.length) = inBit x k := by
  unfold inBit
  rcases le_or_gt k x.length with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h.le, List.drop_eq_nil_of_le le_rfl, List.drop_eq_nil_of_le h.le]

lemma uenv_of_agree {σ τ : HSt (R + D + 1)} {i : Fin R} {v : ℕ}
    (h : ∀ q, q ≠ ur D i → q ≠ sc R D 0 → q ≠ sc R D 1 → τ.env q = σ.env q)
    (hi : τ.env (ur D i) = v) : uenv D τ = Function.update (uenv D σ) i v := by
  funext r
  by_cases hr : r = i
  · subst hr; simp [uenv, hi]
  · simp only [uenv, Function.update_of_ne hr]
    exact h _ (fun e => hr (ur_inj.mp e)) (ur_ne_sc r 0) (ur_ne_sc r 1)

namespace Stm

/-- **Compilation of statements.** -/
theorem code_spec (hw : 2 ≤ w) : ∀ (c : Stm R) (env : Fin R → ℕ) (st : HSt (R + D + 1)),
    WF c → depth c ≤ D → Fits x w c env → uenv D st = env → st.Bdd w → st.pos ≤ x.length →
    (noX c = true ∨ st.pos = 0) →
    ∃ st', HLe x w (code R D c) st st' (cost x w c env) ∧ uenv D st' = (exec x c env).1 ∧
      st'.out = st.out ++ (exec x c env).2 ∧ st'.pos = st.pos
  | skip, env, st, _, _, _, he, hb, _, _ => by
    refine ⟨_, HLe.of_runs (HRuns.clr (hb _)), ?_, by simp [exec], rfl⟩
    rw [uenv_set_sc, he]; rfl
  | set r e, env, st, _, hd, hf, he, hb, _, _ => by
    subst he
    obtain ⟨st₁, h₁, e₁⟩ := Ex.code_spec (x := x) hw e 0 st (by simpa [depth] using hd) hb hf
    have hb₁ := h₁.bounded hw hb
    refine ⟨_, h₁.seq (HLe.of_runs (HRuns.copy (sc_ne_ur r 0) (hb₁ _) (hb₁ _))), ?_, ?_, ?_⟩
    · rw [uenv_set_ur, Ex.code_uenv h₁, e₁]; rfl
    · rw [HSt.set_out, h₁.out_eq (Ex.code_em e 0)]; simp [exec]
    · rw [HSt.set_pos, h₁.pos_eq (Ex.code_mv e 0)]
  | emit e, env, st, _, hd, hf, he, hb, _, _ => by
    subst he
    obtain ⟨st₁, h₁, e₁⟩ := Ex.code_spec (x := x) hw e 0 st (by simpa [depth] using hd) hb hf
    have hb₁ := h₁.bounded hw hb
    refine ⟨_, h₁.seq (HLe.of_runs (HRuns.emit (hb₁ _))), ?_, ?_, ?_⟩
    · rw [← Ex.code_uenv h₁]; rfl
    · simp [exec, e₁, h₁.out_eq (Ex.code_em e 0)]
    · simp [h₁.pos_eq (Ex.code_mv e 0)]
  | seq p q, env, st, hwf, hd, hf, he, hb, hp, hx => by
    simp only [depth, max_le_iff] at hd
    simp only [noX, Bool.and_eq_true] at hx
    obtain ⟨st₁, h₁, u₁, o₁, p₁⟩ := code_spec hw p env st hwf.1 hd.1 hf.1 he hb hp
      (by tauto)
    obtain ⟨st₂, h₂, u₂, o₂, p₂⟩ := code_spec hw q _ st₁ hwf.2 hd.2 hf.2 u₁
      (h₁.bounded hw hb) (by omega) (by rcases hx with h | h; exacts [Or.inl h.2, Or.inr (by omega)])
    refine ⟨st₂, (h₁.seq h₂).mono le_rfl, u₂, ?_, by omega⟩
    rw [o₂, o₁]; simp [exec]
  | ite c p q, env, st, hwf, hd, hf, he, hb, hp, hx => by
    simp only [depth, max_le_iff] at hd
    simp only [noX, Bool.and_eq_true] at hx
    subst he
    obtain ⟨st₁, h₁, e₁⟩ := Ex.code_spec (x := x) hw c 0 st (by omega) hb hf.1
    have u₁ := Ex.code_uenv h₁
    have hb₁ := h₁.bounded hw hb
    have o₁ := h₁.out_eq (Ex.code_em c 0)
    have p₁ := h₁.pos_eq (Ex.code_mv c 0)
    by_cases hc : c.eval (uenv D st) ≠ 0
    · have hf' : Fits x w p (uenv D st) := by have := hf.2; rw [if_pos hc] at this; exact this
      obtain ⟨st₂, h₂, u₂, o₂, p₂⟩ := code_spec hw p _ st₁ hwf.1 hd.2.1 hf' u₁ hb₁
        (by omega) (by rcases hx with h | h; exacts [Or.inl h.1, Or.inr (by omega)])
      refine ⟨st₂, (h₁.seq (HLe.iteT (c := fun v => (v (sc R D 0)).isSome) ?_ h₂)).mono ?_,
        ?_, ?_, by omega⟩
      · rw [HSt.view_isSome_iff, e₁]; exact hc
      · simp only [cost, if_pos hc]; omega
      · simp only [exec, if_pos hc]; exact u₂
      · simp only [exec, if_pos hc]; rw [o₂, o₁]
    · have hf' : Fits x w q (uenv D st) := by have := hf.2; rw [if_neg hc] at this; exact this
      obtain ⟨st₂, h₂, u₂, o₂, p₂⟩ := code_spec hw q _ st₁ hwf.2 hd.2.2 hf' u₁ hb₁
        (by omega) (by rcases hx with h | h; exacts [Or.inl h.2, Or.inr (by omega)])
      refine ⟨st₂, (h₁.seq (HLe.iteF (c := fun v => (v (sc R D 0)).isSome) ?_ h₂)).mono ?_,
        ?_, ?_, by omega⟩
      · rw [← Bool.not_eq_true, HSt.view_isSome_iff, e₁]; exact hc
      · simp only [cost, if_neg hc]; omega
      · simp only [exec, if_neg hc]; exact u₂
      · simp only [exec, if_neg hc]; rw [o₂, o₁]
  | loop i lim body, env, st, hwf, hd, hf, he, hb, hp, hx => by
    obtain ⟨hil, hbi, hbl, hwb⟩ := hwf
    simp only [depth, max_le_iff] at hd
    simp only [noX] at hx
    have h01 : sc R D 0 ≠ sc R D 1 := sc_ne (by omega) (by omega)
    have hil' : ur D i ≠ ur D lim := fun e => hil (ur_inj.mp e)
    set F : ℕ → (Fin R → ℕ) → (Fin R → ℕ) × List ℕ :=
      fun k e => exec x body (Function.update e i k)
    obtain ⟨σ, hσ, hI⟩ := forUp_inv (x := x) (w := w) (body := code R D body) hil'
      (ur_ne_sc i 0) (ur_ne_sc i 1) (ur_ne_sc lim 0) (ur_ne_sc lim 1) h01 hw (env lim)
      hf.1 (code_wr_ur body i hbi) (code_wr_ur body lim hbl)
      (fun k σ => uenv D σ = Function.update (runLoop F k env).1 i k ∧
        σ.out = st.out ++ (runLoop F k env).2 ∧ σ.pos = st.pos)
      (fun k => cost x w body (Function.update (runLoop F k env).1 i k))
      (by
        intro k hk σ hI hbσ _ _
        obtain ⟨σ', h', u', o', p'⟩ := code_spec hw body _ σ hwb hd.2 (hf.2 k hk) hI.1 hbσ
          (by rw [hI.2.2]; exact hp) (by rcases hx with h | h; exacts [Or.inl h, Or.inr (by rw [hI.2.2]; exact h)])
        refine ⟨σ', h', fun τ ho hpo hag hi => ⟨?_, ?_, ?_⟩⟩
        · rw [uenv_of_agree hag hi, u']; rfl
        · rw [ho, o', hI.2.1]; simp [runLoop, F]
        · rw [hpo, p', hI.2.2])
      st hb (by rw [← he]; rfl)
      (by
        intro τ ho hpo hag hi
        refine ⟨?_, by simp [ho, runLoop], hpo⟩
        rw [uenv_of_agree hag hi, he]; rfl)
    exact ⟨σ, hσ, hI.1, hI.2.1, hI.2.2⟩
  | loopX i lim xb body, env, st, hwf, hd, hf, he, hb, hp, hx => by
    obtain ⟨hil, hxi, hxl, hbi, hbl, hnx, hwb⟩ := hwf
    simp only [depth, max_le_iff] at hd
    have hp0 : st.pos = 0 := by simpa [noX] using hx
    have h01 : sc R D 0 ≠ sc R D 1 := sc_ne (by omega) (by omega)
    have hil' : ur D i ≠ ur D lim := fun e => hil (ur_inj.mp e)
    set F : ℕ → (Fin R → ℕ) → (Fin R → ℕ) × List ℕ :=
      fun k e => exec x body (Function.update (Function.update e i k) xb (inBit x k))
    have hr₁ : HLe x w .rst st st (unitCost w) :=
      (HLe.of_runs (HRuns.rst (x := x) (w := w) hp)).of_eq (by ext <;> simp [hp0]) (by simp [hp0])
    have hrd : (HProg.seq (.rd (ur D xb)) (code R D body)).wr (ur D i) = false := by
      simp [HProg.wr, ur_inj, Ne.symm hxi, code_wr_ur body i hbi]
    have hrdl : (HProg.seq (.rd (ur D xb)) (code R D body)).wr (ur D lim) = false := by
      simp [HProg.wr, ur_inj, Ne.symm hxl, code_wr_ur body lim hbl]
    obtain ⟨σ, hσ, hI⟩ := forUp_inv (x := x) (w := w)
      (body := .seq (.rd (ur D xb)) (code R D body)) hil'
      (ur_ne_sc i 0) (ur_ne_sc i 1) (ur_ne_sc lim 0) (ur_ne_sc lim 1) h01 hw (env lim)
      hf.1 hrd hrdl
      (fun k σ => uenv D σ = Function.update (runLoop F k env).1 i k ∧
        σ.out = st.out ++ (runLoop F k env).2 ∧ σ.pos = min k x.length)
      (fun k => unitCost w + cost x w body (Function.update (Function.update
        (runLoop F k env).1 i k) xb (inBit x k)))
      (by
        intro k hk σ hI hbσ _ _
        have hpσ : σ.pos ≤ x.length := by rw [hI.2.2]; exact min_le_right _ _
        have hrun := HLe.of_runs (HRuns.rd (x := x) (r := ur D xb) (hbσ _) hpσ)
        set σ₁ : HSt (R + D + 1) := { (σ.set (ur D xb) (inBit x σ.pos)) with
          pos := min (σ.pos + 1) x.length }
        have hb₁ : σ₁.Bdd w := hrun.bounded hw hbσ
        have hu₁ : uenv D σ₁ = Function.update (Function.update (runLoop F k env).1 i k) xb
            (inBit x k) := by
          show uenv D (σ.set (ur D xb) (inBit x σ.pos)) = _
          rw [uenv_set_ur, hI.1, hI.2.2, inBit_min]
        obtain ⟨σ', h', u', o', p'⟩ := code_spec hw body _ σ₁ hwb hd.2 (hf.2 k hk) hu₁ hb₁
          (by simp [σ₁]) (Or.inl hnx)
        refine ⟨σ', hrun.seq h', fun τ ho hpo hag hi => ⟨?_, ?_, ?_⟩⟩
        · rw [uenv_of_agree hag hi, u']; rfl
        · rw [ho, o']; simp [σ₁, hI.2.1, runLoop, F]
        · rw [hpo, p']; simp only [σ₁, hI.2.2]; omega)
      st hb (by rw [← he]; rfl)
      (by
        intro τ ho hpo hag hi
        refine ⟨?_, by simp [ho, runLoop], by rw [hpo, hp0]; simp⟩
        rw [uenv_of_agree hag hi, he]; rfl)
    have hr₂ : HLe x w .rst σ { σ with pos := 0 } (unitCost w * (x.length + 1)) := by
      refine (HLe.of_runs (HRuns.rst (x := x) (w := w) ?_)).mono ?_
      · rw [hI.2.2]; exact min_le_right _ _
      · rw [hI.2.2]; exact Nat.mul_le_mul_left _ (by omega)
    refine ⟨{ σ with pos := 0 }, (hr₁.seq (hσ.seq hr₂)).mono (by simp only [cost, F]; omega),
      hI.1, hI.2.1, hp0.symm⟩
  | len r, env, st, _, hd, hf, he, hb, hp, hx => by
    have hp0 : st.pos = 0 := by simpa [noX] using hx
    simp only [Fits] at hf
    simp only [depth] at hd
    have h4 : (4 : ℕ) ≤ 2 ^ w := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
    have h01 : sc R D 0 ≠ sc R D 1 := sc_ne (by omega) (by omega)
    have hr₁ : HLe x w .rst st st (unitCost w) :=
      (HLe.of_runs (HRuns.rst (x := x) (w := w) hp)).of_eq (by ext <;> simp [hp0]) (by simp [hp0])
    have hc : HLe x w (.clr (ur D r)) st (st.set (ur D r) 0) (unitCost w) :=
      HLe.of_runs (HRuns.clr (hb _))
    set S : ℕ → HSt (R + D + 1) := fun k =>
      { (((st.set (sc R D 1) (if k = 0 then st.env (sc R D 1) else 1)).set (ur D r) k).set
          (sc R D 0) (inBit x k)) with pos := min (k + 1) x.length }
    have hrd : HLe x w (.rd (sc R D 0)) (st.set (ur D r) 0) (S 0) (unitCost w) := by
      refine (HLe.of_runs (HRuns.rd
        (by simp only [HSt.set_env_ne _ (sc_ne_ur r 0)]; exact hb _) (by simp [hp0]))).of_eq ?_ le_rfl
      ext q
      · simp only [S, HSt.set, Function.update_apply, if_true]
        split_ifs <;> simp_all
      · simp [S, hp0]
      · simp [S]
    have hpos : ∀ k, k < x.length → inBit x k ≠ 0 := by
      intro k hk
      unfold inBit
      rw [List.drop_eq_getElem_cons hk]
      simp [rdVal]
    have hend : inBit x x.length = 0 := by simp [inBit, rdVal]
    have hloop := HLe.loop_seq_const (x := x) (w := w)
      (c := fun v => (v (sc R D 0)).isSome)
      (p := .seq (HProg.inc (ur D r) (sc R D 1)) (.rd (sc R D 0))) x.length S
      (3 * unitCost w + unitCost w)
      (fun k hk => by
        show ((S k).view (sc R D 0)).isSome = true
        rw [HSt.view_isSome_iff]; simpa [S] using hpos k hk)
      (by
        show ((S x.length).view (sc R D 0)).isSome = false
        rw [← Bool.not_eq_true, HSt.view_isSome_iff]; simp [S, hend])
      (fun k hk => by
        have hb₁ : (S k).env (sc R D 1) < 2 ^ w := by
          simp only [S, HSt.set_env_ne _ (Ne.symm h01), HSt.set_env_ne _ (sc_ne_ur r 1)]
          simp only [HSt.set_env_self]; split_ifs
          · exact hb _
          · omega
        have hinc := inc_spec (x := x) (ur_ne_sc r 1) (st := S k) hb₁
          (by simp only [S, HSt.set_env_ne _ (ur_ne_sc r 0), HSt.set_env_self]; omega)
        refine (hinc.seq (HLe.of_runs (HRuns.rd ?_ ?_))).of_eq ?_ le_rfl
        · simp only [HSt.set_env_ne _ (sc_ne_ur r 0), HSt.set_env_ne _ h01]
          simp only [S, HSt.set_env_self]; have := inBit_le x k; omega
        · simp [S]
        · have hk1 : min (k + 1) x.length = k + 1 := by omega
          ext q
          · simp only [S, HSt.set, Function.update_apply, hk1]
            split_ifs <;> simp_all
          · simp [S]; omega
          · simp [S])
    have hr₂ : HLe x w .rst (S x.length) { S x.length with pos := 0 }
        (unitCost w * (x.length + 1)) := by
      refine (HLe.of_runs (HRuns.rst (x := x) (w := w) (by simp [S]))).mono ?_
      simp [S]
    refine ⟨{ S x.length with pos := 0 }, (hr₁.seq (hc.seq (hrd.seq (hloop.seq hr₂)))).mono
      (by simp only [cost]; nlinarith), ?_, ?_, by simp [hp0]⟩
    · rw [← he]; funext q
      show (S x.length).env (ur D q) = _
      by_cases hq : q = r
      · subst hq; simp [S, HSt.set_env_ne _ (ur_ne_sc q 0), exec]
      · simp [S, HSt.set_env_ne _ (ur_ne_sc q 0), HSt.set_env_ne _ (ur_ne_sc q 1),
          HSt.set_env_ne _ (fun e => hq (ur_inj.mp e)), exec, Function.update_of_ne hq, uenv]
    · simp [S, exec]

end Stm

end Lax119563Proofs.Reduction

end Reduction_SStm

/-! ### Formerly `Lax119563Proofs.Reduction.SLib` -/

section Reduction_SLib

/-!
# Reasoning about structured statements

`Good x w c env out T`: from the valuation `env`, the statement `c` fits into words of `w` bits,
emits `out` and costs at most `T`. Compositional rules for all statements; for loops, the
iteration `k` is described by any valuation with counter `k` that agrees with the initial
valuation on the registers the body does not write (`good_loop`, `good_loopX`).

`Stm.computesWithin`: a well-formed statement that is good from the zero valuation gives a
deterministic machine computing `encodeNats out`.
-/

open Lax119563.BinaryEncodings Lax119563.DeterministicTime

namespace Lax119563Proofs.Reduction

variable {R : ℕ} {x : List Bool} {w : ℕ}

namespace Stm

/-! ## Frames -/

lemma runLoop_frame {f : ℕ → (Fin R → ℕ) → (Fin R → ℕ) × List ℕ} {q : Fin R}
    (hf : ∀ k e, (f k e).1 q = e q) : ∀ k env, (runLoop f k env).1 q = env q
  | 0, _ => rfl
  | k + 1, env => by simp only [runLoop]; rw [hf, runLoop_frame hf k env]

lemma runLoop_out (f : ℕ → (Fin R → ℕ) → (Fin R → ℕ) × List ℕ) : ∀ L env,
    (runLoop f L env).2 = (List.range L).flatMap fun k => (f k (runLoop f k env).1).2
  | 0, _ => rfl
  | L + 1, env => by
    simp only [runLoop]
    rw [runLoop_out f L env, List.range_succ, List.flatMap_append, List.flatMap_singleton]

lemma exec_frame : ∀ (c : Stm R) (env : Fin R → ℕ) (q : Fin R), wr c q = false →
    (exec x c env).1 q = env q
  | skip, _, _, _ => rfl
  | set r e, env, q, h => by
    simp only [wr, decide_eq_false_iff_not] at h; simp [exec, Function.update_of_ne h]
  | emit _, _, _, _ => rfl
  | seq p p', env, q, h => by
    simp only [wr, Bool.or_eq_false_iff] at h
    simp only [exec]; rw [exec_frame p' _ q h.2, exec_frame p env q h.1]
  | ite c p p', env, q, h => by
    simp only [wr, Bool.or_eq_false_iff] at h
    simp only [exec]; split_ifs
    · exact exec_frame p env q h.1
    · exact exec_frame p' env q h.2
  | loop i lim body, env, q, h => by
    simp only [wr, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    simp only [exec, Function.update_of_ne h.1]
    exact runLoop_frame (fun k e => by
      rw [exec_frame body _ q h.2, Function.update_of_ne h.1]) _ env
  | loopX i lim xb body, env, q, h => by
    simp only [wr, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    simp only [exec, Function.update_of_ne h.1.1]
    exact runLoop_frame (fun k e => by
      rw [exec_frame body _ q h.2, Function.update_of_ne h.1.2, Function.update_of_ne h.1.1]) _ env
  | len r, env, q, h => by
    simp only [wr, decide_eq_false_iff_not] at h; simp [exec, Function.update_of_ne h]

/-- An invariant of the valuations of a loop. -/
lemma runLoop_inv {f : ℕ → (Fin R → ℕ) → (Fin R → ℕ) × List ℕ} (Inv : ℕ → (Fin R → ℕ) → Prop)
    {L : ℕ} {env : Fin R → ℕ} (h0 : Inv 0 env)
    (hs : ∀ k < L, ∀ e, Inv k e → Inv (k + 1) (f k e).1) : ∀ k ≤ L, Inv k (runLoop f k env).1
  | 0, _ => h0
  | k + 1, hk => hs k (by omega) _ (runLoop_inv Inv h0 hs k (by omega))

end Stm

/-! ## Good statements -/

/-- From `env`, the statement fits into `w` bits, emits `out` and costs at most `T`. -/
structure Good (x : List Bool) (w : ℕ) (c : Stm R) (env : Fin R → ℕ) (out : List ℕ) (T : ℕ) :
    Prop where
  fits : c.Fits x w env
  out_eq : (c.exec x env).2 = out
  cost_le : c.cost x w env ≤ T

namespace Good

open Stm

variable {c p q : Stm R} {env : Fin R → ℕ} {out out' : List ℕ} {T T' : ℕ}

lemma mono (h : Good x w c env out T) (hT : T ≤ T') : Good x w c env out T' :=
  ⟨h.fits, h.out_eq, h.cost_le.trans hT⟩

lemma of_eq (h : Good x w c env out T) (ho : out = out') (hT : T ≤ T') :
    Good x w c env out' T' := ho ▸ h.mono hT

lemma skip : Good x w (Stm.skip : Stm R) env [] (unitCost w) := ⟨trivial, rfl, le_rfl⟩

lemma set {r : Fin R} {e : Ex R} (h : e.Fits w env) :
    Good x w (Stm.set r e) env [] (e.size * Ex.nodeCost w + unitCost w) := ⟨h, rfl, le_rfl⟩

lemma emit {e : Ex R} (h : e.Fits w env) :
    Good x w (Stm.emit e) env [e.eval env] (e.size * Ex.nodeCost w + unitCost w) :=
  ⟨h, rfl, le_rfl⟩

lemma seq {o₁ o₂ : List ℕ} {T₁ T₂ : ℕ} (h₁ : Good x w p env o₁ T₁)
    (h₂ : Good x w q (p.exec x env).1 o₂ T₂) : Good x w (Stm.seq p q) env (o₁ ++ o₂) (T₁ + T₂) :=
  ⟨⟨h₁.fits, h₂.fits⟩, by simp [exec, h₁.out_eq, h₂.out_eq],
    by simp only [cost]; exact Nat.add_le_add h₁.cost_le h₂.cost_le⟩

lemma iteT {e : Ex R} (he : e.Fits w env) (hc : e.eval env ≠ 0) (h : Good x w p env out T) :
    Good x w (Stm.ite e p q) env out (e.size * Ex.nodeCost w + 1 + T) :=
  ⟨⟨he, by rw [if_pos hc]; exact h.fits⟩, by simp only [exec, if_pos hc]; exact h.out_eq,
    by simp only [cost, if_pos hc]; have := h.cost_le; omega⟩

lemma iteF {e : Ex R} (he : e.Fits w env) (hc : e.eval env = 0) (h : Good x w q env out T) :
    Good x w (Stm.ite e p q) env out (e.size * Ex.nodeCost w + 1 + T) :=
  ⟨⟨he, by rw [if_neg (by simpa using hc)]; exact h.fits⟩,
    by simp only [exec, if_neg (show ¬ e.eval env ≠ 0 by simpa using hc)]; exact h.out_eq,
    by simp only [cost, if_neg (show ¬ e.eval env ≠ 0 by simpa using hc)]; have := h.cost_le; omega⟩

lemma len {r : Fin R} (h : x.length + 1 < 2 ^ w) :
    Good x w (Stm.len r) env []
      (3 * unitCost w + x.length * (4 * unitCost w + 1) + 1 + unitCost w * (x.length + 1)) :=
  ⟨h, rfl, le_rfl⟩

end Good

/-! ## Machines of statements -/

/-- **Machines of statements.** A well-formed statement that is good from the zero valuation
gives a machine computing the code of its output. -/
theorem Stm.computesWithin {D : ℕ} {c : Stm R} {out : List ℕ} {T : ℕ} (hw : 2 ≤ w)
    (hwf : c.WF) (hd : c.depth ≤ D) (h : Good x w c (fun _ => 0) out T)
    (hlen : x.length ≤ (encodeNats out).length) :
    ComputesWithin (c.code R D).machine x (encodeNats out)
      (T + 20 * (encodeNats out).length + 4) := by
  have hb : (⟨fun _ => 0, 0, []⟩ : HSt (R + D + 1)).Bdd w := fun _ => by positivity
  obtain ⟨st', ⟨t, ht, hrun⟩, -, ho, hp⟩ := Stm.code_spec (x := x) hw c (fun _ => 0)
    ⟨fun _ => 0, 0, []⟩ hwf hd h.fits rfl hb (by simp) (Or.inr rfl)
  have ho' : st'.out = out := by rw [ho, h.out_eq]; rfl
  have := HProg.computesWithin hrun hp (by rw [ho']; exact hlen)
  rw [ho'] at this
  exact ComputesWithin.mono this (by have := h.cost_le; omega)

end Lax119563Proofs.Reduction

end Reduction_SLib

/-! ### Formerly `Lax119563Proofs.Reduction.SArith` -/

section Reduction_SArith

/-!
# Arithmetic with structured statements

Multiplication by a power of two by repeated doubling (`shlS`), halving `p` times (`shrS`) and
the bitwise exclusive or of the low bits (`xorS`), each with its exact value
(`exec_shlS`, `exec_shrS`, `exec_xorS`).
-/

namespace Lax119563Proofs.Reduction

variable {R : ℕ} {x : List Bool} {w : ℕ}

namespace Stm

/-- `acc := acc * 2 ^ k` (by `k` doublings). -/
def shlS (k acc i : Fin R) : Stm R := loop i k (set acc (Ex.add (Ex.var acc) (Ex.var acc)))

lemma exec_shlS {k acc i : Fin R} (hia : i ≠ acc) (hka : k ≠ acc) (env : Fin R → ℕ) :
    (exec x (shlS k acc i) env).1 acc = env acc * 2 ^ env k ∧
    ∀ q, q ≠ i → q ≠ acc → (exec x (shlS k acc i) env).1 q = env q := by
  set F : ℕ → (Fin R → ℕ) → (Fin R → ℕ) × List ℕ :=
    fun j e' => exec x (set acc (Ex.add (Ex.var acc) (Ex.var acc))) (Function.update e' i j)
  have H := runLoop_inv (f := F) (L := env k) (env := env)
    (fun j e' => e' acc = env acc * 2 ^ j ∧ ∀ q, q ≠ i → q ≠ acc → e' q = env q)
    ⟨by simp, fun _ _ _ => rfl⟩
    (by
      intro j _ e' ⟨h1, h2⟩
      refine ⟨?_, fun q hqi hqa => ?_⟩
      · simp only [F, exec, Function.update_self, Ex.eval, Function.update_of_ne (Ne.symm hia)]
        rw [h1, pow_succ]; ring
      · simp only [F, exec, Function.update_of_ne hqa, Function.update_of_ne hqi]
        exact h2 q hqi hqa)
    (env k) le_rfl
  refine ⟨?_, fun q hqi hqa => ?_⟩
  · simp only [shlS, exec, Function.update_of_ne (Ne.symm hia)]; exact H.1
  · simp only [shlS, exec, Function.update_of_ne hqi]; exact H.2 q hqi hqa

/-- `acc := acc / 2 ^ k` (by `k` halvings). -/
def shrS (k acc i : Fin R) : Stm R := loop i k (set acc (Ex.half (Ex.var acc)))

lemma exec_shrS {k acc i : Fin R} (hia : i ≠ acc) (hka : k ≠ acc) (env : Fin R → ℕ) :
    (exec x (shrS k acc i) env).1 acc = env acc / 2 ^ env k ∧
    ∀ q, q ≠ i → q ≠ acc → (exec x (shrS k acc i) env).1 q = env q := by
  set F : ℕ → (Fin R → ℕ) → (Fin R → ℕ) × List ℕ :=
    fun j e' => exec x (set acc (Ex.half (Ex.var acc))) (Function.update e' i j)
  have H := runLoop_inv (f := F) (L := env k) (env := env)
    (fun j e' => e' acc = env acc / 2 ^ j ∧ ∀ q, q ≠ i → q ≠ acc → e' q = env q)
    ⟨by simp, fun _ _ _ => rfl⟩
    (by
      intro j _ e' ⟨h1, h2⟩
      refine ⟨?_, fun q hqi hqa => ?_⟩
      · simp only [F, exec, Function.update_self, Ex.eval, Function.update_of_ne (Ne.symm hia)]
        rw [h1, pow_succ, Nat.div_div_eq_div_mul]
      · simp only [F, exec, Function.update_of_ne hqa, Function.update_of_ne hqi]
        exact h2 q hqi hqa)
    (env k) le_rfl
  refine ⟨?_, fun q hqi hqa => ?_⟩
  · simp only [shrS, exec, Function.update_of_ne (Ne.symm hia)]; exact H.1
  · simp only [shrS, exec, Function.update_of_ne hqi]; exact H.2 q hqi hqa

/-- One step of the XOR loop. -/
def xorBody (a b res pw : Fin R) : Stm R :=
  seq (ite (Ex.odd (Ex.add (Ex.odd (Ex.var a)) (Ex.odd (Ex.var b))))
      (set res (Ex.add (Ex.var res) (Ex.var pw))) skip)
    (seq (set a (Ex.half (Ex.var a))) (seq (set b (Ex.half (Ex.var b)))
      (set pw (Ex.add (Ex.var pw) (Ex.var pw)))))

/-- `res := (a ^^^ b) % 2 ^ lim`; destroys `a, b`, uses `pw` and the counter `t`. -/
def xorS (a b res pw t lim : Fin R) : Stm R :=
  seq (set res (Ex.const 0)) (seq (set pw (Ex.const 1)) (loop t lim (xorBody a b res pw)))

lemma xor_step (a b k : ℕ) : (a ^^^ b) % 2 ^ (k + 1) =
    (a ^^^ b) % 2 ^ k + (if (a / 2 ^ k % 2 + b / 2 ^ k % 2) % 2 ≠ 0 then 2 ^ k else 0) := by
  rw [Nat.mod_pow_succ]
  have : (a ^^^ b) / 2 ^ k % 2 = (a / 2 ^ k % 2 + b / 2 ^ k % 2) % 2 := by
    rw [← Nat.shiftRight_eq_div_pow, Nat.shiftRight_xor_distrib, Nat.xor_mod_two_eq,
      Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]; omega
  rw [this]
  split_ifs with h
  · rw [show (a / 2 ^ k % 2 + b / 2 ^ k % 2) % 2 = 1 by omega, mul_one]
  · rw [show (a / 2 ^ k % 2 + b / 2 ^ k % 2) % 2 = 0 by omega, mul_zero]

lemma exec_xorS {a b res pw t lim : Fin R} (hab : a ≠ b) (har : a ≠ res) (hap : a ≠ pw)
    (hat : a ≠ t) (hbr : b ≠ res) (hbp : b ≠ pw) (hbt : b ≠ t) (hrp : res ≠ pw)
    (hrt : res ≠ t) (hpt : pw ≠ t) (hla : lim ≠ a) (hlb : lim ≠ b) (hlr : lim ≠ res)
    (hlp : lim ≠ pw) (env : Fin R → ℕ) :
    (exec x (xorS a b res pw t lim) env).1 res = (env a ^^^ env b) % 2 ^ env lim ∧
    ∀ q, q ≠ a → q ≠ b → q ≠ res → q ≠ pw → q ≠ t →
      (exec x (xorS a b res pw t lim) env).1 q = env q := by
  set env₀ := Function.update (Function.update env res 0) pw 1
  set F : ℕ → (Fin R → ℕ) → (Fin R → ℕ) × List ℕ :=
    fun j e' => exec x (xorBody a b res pw) (Function.update e' t j)
  have H := runLoop_inv (f := F) (L := env lim) (env := env₀)
    (fun j e' => e' res = (env a ^^^ env b) % 2 ^ j ∧ e' a = env a / 2 ^ j ∧
      e' b = env b / 2 ^ j ∧ e' pw = 2 ^ j ∧
      ∀ q, q ≠ a → q ≠ b → q ≠ res → q ≠ pw → q ≠ t → e' q = env₀ q)
    ⟨by simp [env₀, Function.update_apply, hrp, Nat.mod_one], by simp [env₀, Function.update_apply, hap, har],
      by simp [env₀, Function.update_apply, hbp, hbr], by simp [env₀],
      fun _ _ _ _ _ _ => rfl⟩
    (by
      intro j _ e' ⟨h1, h2, h3, h4, h5⟩
      have ea : Function.update e' t j a = env a / 2 ^ j := by
        rw [Function.update_of_ne hat, h2]
      have eb : Function.update e' t j b = env b / 2 ^ j := by
        rw [Function.update_of_ne hbt, h3]
      have er : Function.update e' t j res = (env a ^^^ env b) % 2 ^ j := by
        rw [Function.update_of_ne hrt, h1]
      have ep : Function.update e' t j pw = 2 ^ j := by
        rw [Function.update_of_ne hpt, h4]
      have hstep := xor_step (env a) (env b) j
      rw [pow_succ] at hstep
      simp only [F, xorBody, exec, Ex.eval, ea, eb]
      split_ifs with hc
      all_goals simp only [exec, Ex.eval]
      all_goals refine ⟨?_, ?_, ?_, ?_, fun q q1 q2 q3 q4 q5 => by
        simp only [Function.update_apply, q1, q2, q3, q4, q5, if_false]; exact h5 q q1 q2 q3 q4 q5⟩
      all_goals simp only [Function.update_apply, hab, hab.symm, har, har.symm, hap, hap.symm,
        hat, hat.symm, hbr, hbr.symm, hbp, hbp.symm, hbt, hbt.symm, hrp, hrp.symm, hrt,
        hrt.symm, hpt, hpt.symm, if_false, if_true, h1, h2, h3, h4, hstep, pow_succ,
        Nat.div_div_eq_div_mul, hc]
      all_goals first | rfl | (rw [if_pos hc]) | (rw [if_neg hc]) | omega | ring)
    (env lim) le_rfl
  have hL : env₀ lim = env lim := by simp [env₀, Function.update_apply, hlr, hlp]
  have hxe : exec x (xorS a b res pw t lim) env =
      exec x (loop t lim (xorBody a b res pw)) env₀ := by
    simp [xorS, exec, Ex.eval, env₀]
  rw [hxe]
  simp only [exec, hL]
  refine ⟨?_, fun q q1 q2 q3 q4 q5 => ?_⟩
  · rw [Function.update_of_ne hrt]; exact H.1
  · rw [Function.update_of_ne q5, H.2.2.2.2 q q1 q2 q3 q4 q5]
    simp [env₀, Function.update_apply, q3, q4]

end Stm

end Lax119563Proofs.Reduction

end Reduction_SArith

/-! ### Formerly `Lax119563Proofs.Reduction.SchemaParts` -/

section Reduction_SchemaParts

/-!
# Parts of schemas and register values

The accessors of equation schemas (kind, argument locations and permutations, where the
"end" of a schema is its last argument) and basic facts on `regVal` (bounded, injective, with
an inverse `toBlk` on `[0, 2^ℓ)`), as used by the schema enumerator and the system generator.
-/

open Lax119563.ImplicitParitySystems

namespace Lax119563Proofs.Reduction

variable {k ℓ w : ℕ}

/-! ## Schema accessors -/

/-- Whether a schema is ternary. -/
def isTern : Schema k ℓ w → Bool
  | .binary .. => false
  | .ternary .. => true

/-- The first argument location. -/
def locU : Schema k ℓ w → Fin w
  | .binary u .. => u
  | .ternary u .. => u

/-- The first argument permutation. -/
def permU : Schema k ℓ w → BlockPerm k ℓ
  | .binary _ _ _ σ _ => σ
  | .ternary _ _ _ _ σ _ _ => σ

/-- The second argument location. -/
def locV : Schema k ℓ w → Fin w
  | .binary _ v .. => v
  | .ternary _ v .. => v

/-- The second argument permutation. -/
def permV : Schema k ℓ w → BlockPerm k ℓ
  | .binary _ _ _ _ τ => τ
  | .ternary _ _ _ _ _ τ _ => τ

/-- The last argument location. -/
def locEnd : Schema k ℓ w → Fin w
  | .binary _ v .. => v
  | .ternary _ _ w' .. => w'

/-- The last argument permutation. -/
def permEnd : Schema k ℓ w → BlockPerm k ℓ
  | .binary _ _ _ _ τ => τ
  | .ternary _ _ _ _ _ _ π => π

/-! ## Register values -/

lemma regVal_lt (b : BlockCoord ℓ) : Circuits.regVal b < 2 ^ ℓ := by
  unfold Circuits.regVal
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [Circuits.testBit_ofBits]
  simp; omega

lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma regVal_injective : Function.Injective (Circuits.regVal (ℓ := ℓ)) := by
  intro b b' h
  funext t
  have := congrArg (fun n => n.testBit t) h
  simp only [Circuits.regVal, Circuits.testBit_ofBits, t.isLt, decide_true, Bool.true_and,
    dif_pos] at this
  have h1 := zmod2_cases (b t)
  have h2 := zmod2_cases (b' t)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp_all

/-- The block coordinate with register value `v`. -/
def toBlk (ℓ v : ℕ) : BlockCoord ℓ := (Circuits.ofAddr v : Fin 1 → Fin ℓ → ZMod 2) 0

/-! ## Location numbers of compiled programs -/

section Locs

open Lax119563Proofs.Programs

variable {s : ℕ} (R : RegisterProgram s ℓ)

lemma loc_det_val (t : DetSlot) :
    (R.loc (.det t)).val = R.numLocations + R.commands.length * 8 + t.toFin.val := by
  simp [RegisterProgram.loc, Role.equivFin, Role.toSum, finSumFinEquiv]

end Locs

end Lax119563Proofs.Reduction

end Reduction_SchemaParts

/-! ### Formerly `Lax119563Proofs.Reduction.SchemaData` -/

section Reduction_SchemaData

/-!
# Numeric descriptions of the schemas of compiled address programs

For a guard `g` of an address program and a register program command compiled from it:
* `mem_guardDomain_toGuard`: `(i, b) ∈ guardDomain (toGuard g) act` iff `act` for the
  checksum block `i = s`, and `g i (regVal b)` for `i < s`;
* `updatePerm_toUpdate_apply`: the permutation `updatePerm (toUpdate m)` keeps the block and
  XORs the value `regVal b` with `field m (i ℓ) ℓ` on block `i < s`, and with the XOR of all
  these fields on the checksum block (`regVal_shift`);
* the schemas of the commands: `commandSchemas_assign`, `commandSchemas_fork`.
-/

open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs Lax119563Proofs.Circuits

namespace Lax119563Proofs.Reduction

variable {s ℓ : ℕ}

lemma mem_guardDomain_last (g : Guard s ℓ) (act : Bool) (b : BlockCoord ℓ) :
    ((Fin.last s, b) : Coord (s + 1) ℓ) ∈ guardDomain g act ↔ act = true := by
  simp [guardDomain]

lemma mem_guardDomain_castSucc (g : Guard s ℓ) (act : Bool) (i : Fin s) (b : BlockCoord ℓ) :
    ((i.castSucc, b) : Coord (s + 1) ℓ) ∈ guardDomain g act ↔ b ∈ g.sets i := by
  simp [guardDomain]

lemma mem_toGuard (g : Fin s → ℕ → Bool) (i : Fin s) (b : BlockCoord ℓ) :
    b ∈ (toGuard g : Guard s ℓ).sets i ↔ g i (regVal b) = true := by
  simp [toGuard]

/-- Domain membership for a compiled address guard, by the block number. -/
lemma mem_guardDomain_toGuard (g : Fin s → ℕ → Bool) (act : Bool) (c : Coord (s + 1) ℓ) :
    c ∈ guardDomain (toGuard g : Guard s ℓ) act ↔
      if h : c.1.val < s then g ⟨c.1.val, h⟩ (regVal c.2) = true else act = true := by
  obtain ⟨i, b⟩ := c
  induction i using Fin.lastCases with
  | last => simp [mem_guardDomain_last]
  | cast i =>
    rw [mem_guardDomain_castSucc, mem_toGuard]
    simp

/-! ## The shift of an update -/

lemma regVal_add (b c : BlockCoord ℓ) : regVal (b + c) = regVal b ^^^ regVal c := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_xor]
  simp only [regVal, testBit_ofBits]
  by_cases ht : t < ℓ
  · simp only [ht, decide_true, Bool.true_and, dif_pos, Pi.add_apply]
    rw [zmod2_add_eq_one]
  · simp [ht]

lemma regVal_ofAddr (m : ℕ) (i : Fin s) :
    regVal ((ofAddr m : Fin s → Fin ℓ → ZMod 2) i) = field m (i * ℓ) ℓ := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [testBit_field]
  simp only [regVal, testBit_ofBits, ofAddr]
  by_cases ht : t < ℓ
  · simp only [ht, decide_true, Bool.true_and, dif_pos]
    rw [Nat.add_comm t]
    split_ifs <;> simp_all
  · simp [ht]

/-- The XOR of the register fields of a mask: the shift of the checksum block. -/
def xorFields (ℓ : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | s + 1, m => xorFields ℓ s m ^^^ field m (s * ℓ) ℓ

lemma regVal_sum_ofAddr (m : ℕ) : ∀ s : ℕ,
    regVal (∑ i, (ofAddr m : Fin s → Fin ℓ → ZMod 2) i) = xorFields ℓ s m
  | 0 => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty, xorFields]
    apply Nat.eq_of_testBit_eq; intro t
    simp [regVal, testBit_ofBits]
  | s + 1 => by
    have e1 : (∑ i : Fin s, (ofAddr m : Fin (s + 1) → Fin ℓ → ZMod 2) i.castSucc) =
        ∑ i : Fin s, (ofAddr m : Fin s → Fin ℓ → ZMod 2) i :=
      Finset.sum_congr rfl fun i _ => by funext k; simp [ofAddr]
    have e2 : regVal ((ofAddr m : Fin (s + 1) → Fin ℓ → ZMod 2) (Fin.last s)) =
        field m (s * ℓ) ℓ := by rw [regVal_ofAddr]; simp
    rw [Fin.sum_univ_castSucc, regVal_add, e1, regVal_sum_ofAddr m s, e2, xorFields]

/-- The shift of block `i` under the update XOR-ing with `m`. -/
def shiftVal (s ℓ m : ℕ) (i : ℕ) : ℕ := if i < s then field m (i * ℓ) ℓ else xorFields ℓ s m

lemma updatePerm_toUpdate_apply (m : ℕ) (c : Coord (s + 1) ℓ) :
    ((updatePerm (toUpdate m : Update s ℓ)).apply c).1 = c.1 ∧
      regVal ((updatePerm (toUpdate m : Update s ℓ)).apply c).2 =
        regVal c.2 ^^^ shiftVal s ℓ m c.1.val := by
  obtain ⟨i, b⟩ := c
  induction i using Fin.lastCases with
  | last =>
    refine ⟨by
      simp only [BlockPerm.apply, updatePerm, toUpdate]
      rw [Equiv.symm_apply_eq]; simp, ?_⟩
    simp only [BlockPerm.apply, updatePerm, toUpdate, Fin.lastCases_last]
    rw [regVal_add, regVal_sum_ofAddr]
    simp [shiftVal]
  | cast i =>
    refine ⟨by
      simp only [BlockPerm.apply, updatePerm, toUpdate]
      rw [Equiv.symm_apply_eq]; simp, ?_⟩
    simp only [BlockPerm.apply, updatePerm, toUpdate, Fin.lastCases_castSucc]
    rw [regVal_add]
    show regVal b ^^^ regVal ((ofAddr m : Fin s → Fin ℓ → ZMod 2) i) = _
    simp [shiftVal, regVal_ofAddr]

/-! ## The schemas of compiled commands -/

section Commands

variable {L : Type} {N : ℕ} (code : L → Fin N) (acc rej : L) (hne : code acc ≠ code rej)
  (cmds : List (ACmd L s))

/-- The register program compiled from an address program. -/
abbrev AP : RegisterProgram s ℓ := compile N code acc rej hne cmds

lemma AP_commands : (AP (ℓ := ℓ) code acc rej hne cmds).commands = cmds.map (ACmd.toCmd code) :=
  rfl

lemma commandSchemas_assign (j : Fin (AP (ℓ := ℓ) code acc rej hne cmds).commands.length)
    (p : L) (g : Fin s → ℕ → Bool) (m : ℕ) (q : L) :
    (AP (ℓ := ℓ) code acc rej hne cmds).commandSchemas j ((ACmd.assign p g m q).toCmd code) =
      let R := AP (ℓ := ℓ) code acc rej hne cmds
      gadget (R.loc (.prog (code q))) (updatePerm (toUpdate m)) (R.loc (.slot j .a1))
        (R.loc (.slot j .b1)) (R.loc (.slot j .z1)) (R.loc (.prog (code p)))
        (guardDomain (toGuard g) (R.executable (code p))) := rfl

lemma commandSchemas_fork (j : Fin (AP (ℓ := ℓ) code acc rej hne cmds).commands.length)
    (p : L) (g : Fin s → ℕ → Bool) (q r : L) :
    (AP (ℓ := ℓ) code acc rej hne cmds).commandSchemas j ((ACmd.fork p g q r).toCmd code) =
      let R := AP (ℓ := ℓ) code acc rej hne cmds
      gadget (R.loc (.prog (code q))) (idPerm s ℓ) (R.loc (.slot j .a1)) (R.loc (.slot j .b1))
        (R.loc (.slot j .z1)) (R.loc (.slot j .out1)) (guardDomain (toGuard g) (R.executable (code p))) ++
      gadget (R.loc (.prog (code r))) (idPerm s ℓ) (R.loc (.slot j .a2)) (R.loc (.slot j .b2))
        (R.loc (.slot j .z2)) (R.loc (.slot j .out2)) (guardDomain (toGuard g) (R.executable (code p))) ++
      [.ternary (R.loc (.slot j .out1)) (R.loc (.slot j .out2)) (R.loc (.prog (code p)))
        (guardDomain (toGuard g) (R.executable (code p))) (idPerm s ℓ) (idPerm s ℓ) (idPerm s ℓ)] :=
  rfl

lemma loc_prog_val (p : Fin (AP (ℓ := ℓ) code acc rej hne cmds).numLocations) :
    ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.prog p)).val = p.val := by
  simp [RegisterProgram.loc, Role.equivFin, Role.toSum, finSumFinEquiv]

end Commands

end Lax119563Proofs.Reduction

end Reduction_SchemaData

/-! ### Formerly `Lax119563Proofs.Reduction.SchList` -/

section Reduction_SchList

/-!
# The schemas of compiled address programs, numerically

For the register program compiled from an address program, every schema is described by a
`SchNum`: whether it is ternary, the numbers of its locations `locU, locV, locEnd`, and the
mask `msk` of its first permutation (`PermDesc`: block kept, `regVal` XOR-ed with
`shiftVal s ℓ msk`; the other permutations are the identity), together with its domain.
`schNums_compiled`: the schema list of `(compile …).compile p₀ a₀` matches the explicit list
`cmdsN … ++ detN …` (`List.Forall₂ SchMatch`).
-/

open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs
open Lax119563Proofs.Circuits

namespace Lax119563Proofs.Reduction

variable {s ℓ : ℕ}

/-- Numbers of a schema. -/
structure SchNum where
  tern : Bool
  u : ℕ
  v : ℕ
  en : ℕ
  msk : ℕ

/-- A binary schema `X → Y` with first permutation of mask `msk`. -/
def binN (X Y msk : ℕ) : SchNum := ⟨false, X, Y, Y, msk⟩

/-- A ternary schema `(A, B, Z)`. -/
def terN (A B Z : ℕ) : SchNum := ⟨true, A, B, Z, 0⟩

/-- The numbers of a one-way gadget. -/
def gadgetN (X msk A B Z Y : ℕ) : List SchNum :=
  [binN X A msk, binN X B msk, terN A B Z, binN Z Y 0]

/-- The permutation keeps blocks and XORs block `i` with `shiftVal s ℓ msk i`. -/
def PermDesc (π : BlockPerm (s + 1) ℓ) (msk : ℕ) : Prop :=
  ∀ c : Coord (s + 1) ℓ, (π.apply c).1 = c.1 ∧
    regVal (π.apply c).2 = regVal c.2 ^^^ shiftVal s ℓ msk c.1.val

/-- The permutation is the identity. -/
def PermId (π : BlockPerm (s + 1) ℓ) : Prop := ∀ c, π.apply c = c

/-- A schema matches its numbers and domain. -/
def SchMatch {N : ℕ} (D : Finset (Coord (s + 1) ℓ)) (e : Schema (s + 1) ℓ N) (n : SchNum) :
    Prop :=
  isTern e = n.tern ∧ (locU e).val = n.u ∧ (locV e).val = n.v ∧ (locEnd e).val = n.en ∧
    PermDesc (permU e) n.msk ∧ PermId (permV e) ∧ PermId (permEnd e) ∧ e.domain = D

lemma xorFields_zero : ∀ s : ℕ, xorFields ℓ s 0 = 0
  | 0 => rfl
  | s + 1 => by simp [xorFields, xorFields_zero s, field]

lemma shiftVal_zero (i : ℕ) : shiftVal s ℓ 0 i = 0 := by
  unfold shiftVal
  split_ifs
  · simp [field]
  · exact xorFields_zero s

lemma permId_id : PermId (idPerm s ℓ) := by
  intro c
  simp [BlockPerm.apply, idPerm]

lemma permDesc_id : PermDesc (idPerm s ℓ) 0 := by
  intro c
  rw [permId_id c, shiftVal_zero, Nat.xor_zero]
  exact ⟨rfl, rfl⟩

lemma permDesc_update (m : ℕ) : PermDesc (updatePerm (toUpdate m : Update s ℓ)) m :=
  fun c => updatePerm_toUpdate_apply m c

lemma gadget_match {N : ℕ} (X : Fin N) (π : BlockPerm (s + 1) ℓ) (msk : ℕ) (hπ : PermDesc π msk)
    (A B Z Y : Fin N) (D : Finset (Coord (s + 1) ℓ)) :
    List.Forall₂ (SchMatch D) (gadget X π A B Z Y D) (gadgetN X.val msk A.val B.val Z.val Y.val) := by
  simp only [gadget, gadgetN, List.forall₂_cons, binN, terN]
  refine ⟨⟨rfl, rfl, rfl, rfl, hπ, permId_id, permId_id, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, hπ, permId_id, permId_id, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, permDesc_id, permId_id, permId_id, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, permDesc_id, permId_id, permId_id, rfl⟩, List.Forall₂.nil⟩

lemma forall₂_flatMap {α β γ δ : Type} {R : γ → δ → Prop} {f : α → List γ} {g : β → List δ} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ (fun a b => List.Forall₂ R (f a) (g b)) l l' →
      List.Forall₂ R (l.flatMap f) (l'.flatMap g)
  | [], [], _ => List.Forall₂.nil
  | _ :: _, _ :: _, List.Forall₂.cons h t => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact List.rel_append h (forall₂_flatMap t)

section Commands

variable {L : Type} {N : ℕ} (code : L → Fin N)

/-- The numbers of the schemas of command `j` (locations of `N` control locations first). -/
def cmdN (j : ℕ) : ACmd L s → List SchNum
  | .assign p _ m q => gadgetN (code q).val m (N + (0 + 8 * j)) (N + (1 + 8 * j))
      (N + (2 + 8 * j)) (code p).val
  | .fork p _ q q' => gadgetN (code q).val 0 (N + (0 + 8 * j)) (N + (1 + 8 * j))
      (N + (2 + 8 * j)) (N + (6 + 8 * j)) ++
    gadgetN (code q').val 0 (N + (3 + 8 * j)) (N + (4 + 8 * j)) (N + (5 + 8 * j))
      (N + (7 + 8 * j)) ++ [terN (N + (6 + 8 * j)) (N + (7 + 8 * j)) (code p).val]

/-- The guard of a command. -/
def _root_.Lax119563Proofs.Circuits.ACmd.guard : ACmd L s → (Fin s → ℕ → Bool)
  | .assign _ g _ _ => g
  | .fork _ g _ _ => g

/-- The source of a command. -/
def _root_.Lax119563Proofs.Circuits.ACmd.src : ACmd L s → L
  | .assign p _ _ _ => p
  | .fork p _ _ _ => p

variable (acc rej : L) (hne : code acc ≠ code rej) (cmds : List (ACmd L s))

/-- The domain of the schemas of a command. -/
def cmdDom (cmd : ACmd L s) : Finset (Coord (s + 1) ℓ) :=
  guardDomain (toGuard cmd.guard) ((AP (ℓ := ℓ) code acc rej hne cmds).executable (code cmd.src))

/-- The numbers of the detector schemas. -/
def detN (r p₀ : ℕ) : List SchNum :=
  gadgetN p₀ 0 (N + r * 8 + 0) (N + r * 8 + 1) (N + r * 8 + 2) (N + r * 8 + 3)

/-- Closes the location number goals of `cmd_match`. -/
local macro "fin_close" : tactic => `(tactic| first
  | rfl
  | exact (loc_prog_val _ _ _ _ _ _).symm
  | exact loc_prog_val _ _ _ _ _ _
  | (simp only [loc_slot_val, Slot.toFin, AP, compile, Fin.val_zero, Fin.val_one, Fin.val_two,
      Fin.isValue]; omega)
  | (simp [loc_slot_val, Slot.toFin, AP, compile]))

lemma cmd_match (j : Fin (AP (ℓ := ℓ) code acc rej hne cmds).commands.length)
    (cmd : ACmd L s) :
    List.Forall₂ (fun e n => SchMatch (cmdDom (ℓ := ℓ) code acc rej hne cmds cmd) e n)
      ((AP (ℓ := ℓ) code acc rej hne cmds).commandSchemas j (cmd.toCmd code))
      (cmdN code j.val cmd) := by
  cases cmd with
  | assign p g m q =>
    rw [commandSchemas_assign]
    have := gadget_match (s := s) (ℓ := ℓ) ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.prog (code q)))
      _ m (permDesc_update m) ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.slot j .a1))
      ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.slot j .b1))
      ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.slot j .z1))
      ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.prog (code p)))
      (guardDomain (toGuard g) ((AP (ℓ := ℓ) code acc rej hne cmds).executable (code p)))
    simp only [cmdN]
    convert this using 2 <;> fin_close
  | fork p g q q' =>
    rw [commandSchemas_fork]
    refine List.rel_append (List.rel_append ?_ ?_) ?_
    · have := gadget_match (s := s) (ℓ := ℓ) ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.prog (code q)))
        _ 0 permDesc_id ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.slot j .a1))
        ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.slot j .b1))
        ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.slot j .z1))
        ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.slot j .out1))
        (guardDomain (toGuard g) ((AP (ℓ := ℓ) code acc rej hne cmds).executable (code p)))
      convert this using 2 <;> fin_close
    · have := gadget_match (s := s) (ℓ := ℓ) ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.prog (code q')))
        _ 0 permDesc_id ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.slot j .a2))
        ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.slot j .b2))
        ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.slot j .z2))
        ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.slot j .out2))
        (guardDomain (toGuard g) ((AP (ℓ := ℓ) code acc rej hne cmds).executable (code p)))
      convert this using 2 <;> fin_close
    · refine List.Forall₂.cons ⟨rfl, ?_, ?_, ?_, permDesc_id, permId_id, permId_id, rfl⟩
        List.Forall₂.nil
      all_goals simp only [locU, locV, locEnd, terN]
      all_goals fin_close

/-- **The schemas of a compiled address program, numerically.** -/
theorem schemas_match (p₀ : Fin (AP (ℓ := ℓ) code acc rej hne cmds).numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2) :
    List.Forall₂ (fun e (n : Finset (Coord (s + 1) ℓ) × SchNum) => SchMatch n.1 e n.2)
      ((AP (ℓ := ℓ) code acc rej hne cmds).compiledSchemas p₀ a₀)
      ((cmds.zipIdx.flatMap fun p => (cmdN code p.2 p.1).map
          fun n => (cmdDom (ℓ := ℓ) code acc rej hne cmds p.1, n)) ++
        (detN (N := N) cmds.length p₀.val).map fun n =>
          (guardDomain (RegisterProgram.queryGuard a₀) true, n)) := by
  refine List.rel_append (forall₂_flatMap ?_) ?_
  · rw [List.forall₂_iff_get]
    have hl : (AP (ℓ := ℓ) code acc rej hne cmds).commands.length = cmds.length := by
      simp only [AP_commands]; exact List.length_map _
    refine ⟨by rw [List.length_finRange, List.length_zipIdx, hl], fun i h1 h2 => ?_⟩
    have hi : i < cmds.length := by rwa [List.length_zipIdx] at h2
    have hc : (AP (ℓ := ℓ) code acc rej hne cmds).commands[i]'(by rw [hl]; exact hi) =
        (cmds[i]'hi).toCmd code := by
      simp only [AP_commands]; exact List.getElem_map _
    simp only [List.get_eq_getElem, List.getElem_finRange, List.getElem_zipIdx, zero_add,
      Fin.getElem_fin, Fin.val_cast]
    rw [hc, List.forall₂_map_right_iff]
    exact cmd_match code acc rej hne cmds _ _
  · rw [List.forall₂_map_right_iff]
    have := gadget_match ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.prog p₀)) (idPerm s ℓ) 0
      permDesc_id ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.det .u1))
      ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.det .u2))
      ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.det .z))
      ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.det .out))
      (guardDomain (RegisterProgram.queryGuard a₀) true)
    simp only [detN, RegisterProgram.detectorSchemas]
    convert this using 2 <;> first
      | exact (loc_prog_val _ _ _ _ _ _).symm
      | (simp [loc_det_val, DetSlot.toFin, AP, compile])

end Commands

end Lax119563Proofs.Reduction

end Reduction_SchList

/-! ### Formerly `Lax119563Proofs.Reduction.XLang` -/

section Reduction_XLang

/-!
# Expressions with loop-based operations

`Xp`: expressions over a stack of naturals (`var i` reads level `i`), with constant-time
operations (`add, lt, half, odd`) and loop-based operations whose number of iterations is the
value of their last argument `k`: `mulB a b k = a * (b % 2^k)`, `shl a k = a * 2^k`,
`shr a k = a / 2^k`, `xorM a b k = (a ^^^ b) % 2^k`.

`Xp.comp R d A t e` evaluates `e` into register `t` of `Stm (R + 1)` (register `R` is a sink),
using registers `≥ t` as temporaries; levels `i < d` not in `A` are read from register `i`,
all other levels read as `0`. `Xp.spec`: the compiled statement is `Good` (no output, cost at
most `κ w * cost`), computes the value, and keeps all registers below `t`.

`Stm.good_loopInv`: a loop rule with an invariant (for bodies writing accumulators).
-/

namespace Lax119563Proofs.Reduction

/-! ## Registers -/

/-- Register `t` among `R + 1` registers (`R` is a sink for out-of-range indices). -/
def rg (R t : ℕ) : Fin (R + 1) := ⟨min t R, by omega⟩

lemma rg_ne {R t t' : ℕ} (h : t < R) (hne : t ≠ t') : rg R t ≠ rg R t' := by
  intro e
  have := congrArg Fin.val e
  simp only [rg] at this
  omega

lemma rg_inj {R t t' : ℕ} (h : t < R) (h' : t' < R) : rg R t = rg R t' ↔ t = t' :=
  ⟨fun e => by by_contra hne; exact rg_ne h hne e, fun e => e ▸ rfl⟩

/-- The cost unit. -/
def κ (w : ℕ) : ℕ := 32 * Ex.nodeCost w

variable {R : ℕ} {x : List Bool} {w : ℕ}

/-! ## Loops with invariants -/

namespace Stm

lemma good_loopInv {N : ℕ} {i lim : Fin N} {body : Stm N} {env : Fin N → ℕ}
    (Inv : ℕ → (Fin N → ℕ) → Prop) (g : ℕ → List ℕ) (Tb : ℕ)
    (hL : env lim + 1 < 2 ^ w) (h0 : Inv 0 env)
    (hs : ∀ k < env lim, ∀ e, Inv k e →
      Good x w body (Function.update e i k) (g k) Tb ∧
        Inv (k + 1) (exec x body (Function.update e i k)).1) :
    Good x w (loop i lim body) env ((List.range (env lim)).flatMap g)
      (env lim * (Tb + 4 * unitCost w + 1) + 2 * unitCost w + 1) ∧
    Inv (env lim) (runLoop (fun k e => exec x body (Function.update e i k)) (env lim) env).1 := by
  have HI := runLoop_inv (f := fun k e => exec x body (Function.update e i k)) (L := env lim)
    Inv h0 (fun k hk e he => (hs k hk e he).2)
  have H : ∀ k < env lim, Good x w body
      (Function.update (runLoop (fun k e => exec x body (Function.update e i k)) k env).1 i k)
      (g k) Tb := fun k hk => (hs k hk _ (HI k hk.le)).1
  refine ⟨⟨⟨hL, fun k hk => (H k hk).fits⟩, ?_, ?_⟩, HI _ le_rfl⟩
  · simp only [exec]
    rw [runLoop_out]
    refine List.flatMap_congr fun k hk => ?_
    exact (H k (List.mem_range.mp hk)).out_eq
  · simp only [cost]
    have : ∑ k ∈ Finset.range (env lim), (cost x w body (Function.update
        (runLoop (fun k e => exec x body (Function.update e i k)) k env).1 i k) +
          4 * unitCost w + 1) ≤ ∑ k ∈ Finset.range (env lim), (Tb + 4 * unitCost w + 1) :=
      Finset.sum_le_sum fun k hk => by have := (H k (Finset.mem_range.mp hk)).cost_le; omega
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at this
    omega

lemma exec_loop_fst {N : ℕ} (i lim : Fin N) (body : Stm N) (env : Fin N → ℕ) :
    (exec x (loop i lim body) env).1 =
      Function.update (runLoop (fun k e => exec x body (Function.update e i k)) (env lim) env).1
        i (env lim) := rfl

lemma exec_loopX_fst {N : ℕ} (i lim xb : Fin N) (body : Stm N) (env : Fin N → ℕ) :
    (exec x (loopX i lim xb body) env).1 =
      Function.update (runLoop (fun k e => exec x body
        (Function.update (Function.update e i k) xb (inBit x k))) (env lim) env).1
        i (env lim) := rfl

end Stm

namespace Good

open Stm

variable {N : ℕ} {p q : Stm N} {env : Fin N → ℕ} {T₁ T₂ : ℕ}

lemma seq0 (h₁ : Good x w p env [] T₁) (h₂ : Good x w q (exec x p env).1 [] T₂) :
    Good x w (Stm.seq p q) env [] (T₁ + T₂) := (h₁.seq h₂).of_eq rfl le_rfl

end Good

/-! ## Expressions -/

/-- Expressions over a stack of naturals. -/
inductive Xp where
  | var (i : ℕ)
  | const (c : ℕ)
  | add (a b : Xp)
  | lt (a b : Xp)
  | half (a : Xp)
  | odd (a : Xp)
  | mulB (a b k : Xp)
  | shl (a k : Xp)
  | shr (a k : Xp)
  | xorM (a b k : Xp)

namespace Xp

/-- The value of an expression; level `i` of the stack `ρ` is `ρ.getD i 0`. -/
def eval (ρ : List ℕ) : Xp → ℕ
  | var i => ρ.getD i 0
  | const c => c
  | add a b => a.eval ρ + b.eval ρ
  | lt a b => if a.eval ρ < b.eval ρ then 1 else 0
  | half a => a.eval ρ / 2
  | odd a => a.eval ρ % 2
  | mulB a b k => a.eval ρ * (b.eval ρ % 2 ^ k.eval ρ)
  | shl a k => a.eval ρ * 2 ^ k.eval ρ
  | shr a k => a.eval ρ / 2 ^ k.eval ρ
  | xorM a b k => (a.eval ρ ^^^ b.eval ρ) % 2 ^ k.eval ρ

/-- The number of registers used from the target register on. -/
def need : Xp → ℕ
  | var _ => 1
  | const _ => 1
  | add a b => max a.need (b.need + 1)
  | lt a b => max a.need (b.need + 1)
  | half a => a.need
  | odd a => a.need
  | mulB a b k => max (max (a.need + 1) (b.need + 2)) (max (k.need + 3) 5)
  | shl a k => max (max a.need (k.need + 1)) 3
  | shr a k => max (max a.need (k.need + 1)) 3
  | xorM a b k => max (max (a.need + 1) (b.need + 2)) (max (k.need + 3) 6)

lemma one_le_need : ∀ e : Xp, 1 ≤ e.need
  | var _ => le_rfl
  | const _ => le_rfl
  | add a _ => le_trans (one_le_need a) (le_max_left _ _)
  | lt a _ => le_trans (one_le_need a) (le_max_left _ _)
  | half a => one_le_need a
  | odd a => one_le_need a
  | mulB .. => by simp only [need]; omega
  | shl .. => by simp only [need]; omega
  | shr .. => by simp only [need]; omega
  | xorM .. => by simp only [need]; omega

/-- Values stay below `B` (and the intermediate values of the loop-based operations). -/
def Fits (B : ℕ) (ρ : List ℕ) : Xp → Prop
  | var i => ρ.getD i 0 < B
  | const c => c < B
  | add a b => a.Fits B ρ ∧ b.Fits B ρ ∧ a.eval ρ + b.eval ρ < B
  | lt a b => a.Fits B ρ ∧ b.Fits B ρ
  | half a => a.Fits B ρ
  | odd a => a.Fits B ρ
  | mulB a b k => a.Fits B ρ ∧ b.Fits B ρ ∧ k.Fits B ρ ∧ a.eval ρ * 2 ^ k.eval ρ < B
  | shl a k => a.Fits B ρ ∧ k.Fits B ρ ∧ a.eval ρ * 2 ^ k.eval ρ < B
  | shr a k => a.Fits B ρ ∧ k.Fits B ρ
  | xorM a b k => a.Fits B ρ ∧ b.Fits B ρ ∧ k.Fits B ρ ∧ 2 ^ k.eval ρ < B

/-- The cost in units of `κ w`. -/
def cost (ρ : List ℕ) : Xp → ℕ
  | var _ => 1
  | const _ => 1
  | add a b => a.cost ρ + b.cost ρ + 1
  | lt a b => a.cost ρ + b.cost ρ + 1
  | half a => a.cost ρ + 1
  | odd a => a.cost ρ + 1
  | mulB a b k => a.cost ρ + b.cost ρ + k.cost ρ + k.eval ρ + 2
  | shl a k => a.cost ρ + k.cost ρ + k.eval ρ + 2
  | shr a k => a.cost ρ + k.cost ρ + k.eval ρ + 2
  | xorM a b k => a.cost ρ + b.cost ρ + k.cost ρ + k.eval ρ + 3

lemma eval_lt {B : ℕ} {ρ : List ℕ} : ∀ {e : Xp}, e.Fits B ρ → e.eval ρ < B
  | var _, h => h
  | const _, h => h
  | add _ _, h => h.2.2
  | lt a b, h => by
    have ha := eval_lt h.1; have hb := eval_lt h.2
    simp only [eval]; split_ifs <;> omega
  | half a, h => by have := eval_lt (e := a) h; simp only [eval]; omega
  | odd a, h => by
    have := eval_lt (e := a) h; simp only [eval]; have := Nat.mod_le (a.eval ρ) 2; omega
  | mulB a b k, h => by
    simp only [eval]
    have : b.eval ρ % 2 ^ k.eval ρ < 2 ^ k.eval ρ := Nat.mod_lt _ (by positivity)
    exact lt_of_le_of_lt (Nat.mul_le_mul_left _ this.le) h.2.2.2
  | shl _ _, h => h.2.2
  | shr a _, h => lt_of_le_of_lt (Nat.div_le_self _ _) (eval_lt h.1)
  | xorM _ _ _, h => lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) h.2.2.2.le

/-- The body of the multiplication loop. -/
def mulBody {N : ℕ} (res a b : Fin N) : Stm N :=
  .seq (.ite (.odd (.var b)) (.set res (.add (.var res) (.var a))) .skip)
    (.seq (.set b (.half (.var b))) (.set a (.add (.var a) (.var a))))

/-- Compilation into register `t`. -/
def comp (R d : ℕ) (A : List ℕ) : ℕ → Xp → Stm (R + 1)
  | t, var i => if i < d ∧ i ∉ A then .set (rg R t) (.var (rg R i)) else .set (rg R t) (.const 0)
  | t, const c => .set (rg R t) (.const c)
  | t, add a b => .seq (comp R d A t a) (.seq (comp R d A (t + 1) b)
      (.set (rg R t) (.add (.var (rg R t)) (.var (rg R (t + 1))))))
  | t, lt a b => .seq (comp R d A t a) (.seq (comp R d A (t + 1) b)
      (.set (rg R t) (.lt (.var (rg R t)) (.var (rg R (t + 1))))))
  | t, half a => .seq (comp R d A t a) (.set (rg R t) (.half (.var (rg R t))))
  | t, odd a => .seq (comp R d A t a) (.set (rg R t) (.odd (.var (rg R t))))
  | t, mulB a b k => .seq (comp R d A (t + 1) a) (.seq (comp R d A (t + 2) b)
      (.seq (comp R d A (t + 3) k) (.seq (.set (rg R t) (.const 0))
        (.loop (rg R (t + 4)) (rg R (t + 3)) (mulBody (rg R t) (rg R (t + 1)) (rg R (t + 2)))))))
  | t, shl a k => .seq (comp R d A t a) (.seq (comp R d A (t + 1) k)
      (Stm.shlS (rg R (t + 1)) (rg R t) (rg R (t + 2))))
  | t, shr a k => .seq (comp R d A t a) (.seq (comp R d A (t + 1) k)
      (Stm.shrS (rg R (t + 1)) (rg R t) (rg R (t + 2))))
  | t, xorM a b k => .seq (comp R d A (t + 1) a) (.seq (comp R d A (t + 2) b)
      (.seq (comp R d A (t + 3) k) (Stm.xorS (rg R (t + 1)) (rg R (t + 2)) (rg R t)
        (rg R (t + 4)) (rg R (t + 5)) (rg R (t + 3)))))

end Xp

end Lax119563Proofs.Reduction

namespace Lax119563Proofs.Reduction

variable {R : ℕ} {x : List Bool} {w : ℕ}

/-! ## Routines with fits and costs -/

section Routines

open Stm

variable {N : ℕ}

lemma exec_seq_fst (p q : Stm N) (env : Fin N → ℕ) :
    (exec x (Stm.seq p q) env).1 = (exec x q (exec x p env).1).1 := rfl

lemma exec_set_fst (r : Fin N) (e : Ex N) (env : Fin N → ℕ) :
    (exec x (Stm.set r e) env).1 = Function.update env r (e.eval env) := rfl

lemma nodeCost_ge (w : ℕ) : 64 ≤ unitCost w ∧ unitCost w ≤ Ex.nodeCost w :=
  ⟨by unfold unitCost; omega, Ex.unitCost_le_nodeCost w⟩

lemma shlS_good {k acc i : Fin N} (hia : i ≠ acc) (hka : k ≠ acc) (hik : i ≠ k)
    {env : Fin N → ℕ} {B : ℕ} (hB : 2 * B ≤ 2 ^ w) (hk : env k < B)
    (hv : env acc * 2 ^ env k < B) :
    Good x w (shlS k acc i) env [] (env k * (3 * Ex.nodeCost w + 5 * unitCost w + 1) +
      2 * unitCost w + 1) := by
  have H := good_loopInv (x := x) (w := w) (i := i) (lim := k)
    (body := Stm.set acc (Ex.add (Ex.var acc) (Ex.var acc))) (env := env)
    (fun j e => e acc = env acc * 2 ^ j ∧ e k = env k) (fun _ => [])
    (3 * Ex.nodeCost w + unitCost w) (by omega) ⟨by simp, rfl⟩ (by
      intro j hj e ⟨h1, h2⟩
      have e1 : Function.update e i j acc = env acc * 2 ^ j := by
        rw [Function.update_of_ne (Ne.symm hia), h1]
      have hle : env acc * 2 ^ (j + 1) ≤ env acc * 2 ^ env k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hj)
      have hle' : env acc * 2 ^ j ≤ env acc * 2 ^ (j + 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      have e2 : env acc * 2 ^ (j + 1) = env acc * 2 ^ j + env acc * 2 ^ j := by ring
      refine ⟨(Good.set ?_).of_eq rfl (by simp [Ex.size]), ?_, ?_⟩
      · simp only [Ex.Fits, Ex.eval, e1]; omega
      · simp only [exec_set_fst, Function.update_self, Ex.eval, e1]; ring
      · rw [exec_set_fst, Function.update_of_ne hka, Function.update_of_ne (Ne.symm hik), h2])
  have := nodeCost_ge w
  exact H.1.of_eq (by simp) (le_of_eq (by ring))

lemma shrS_good {k acc i : Fin N} (hia : i ≠ acc) (hka : k ≠ acc) (hik : i ≠ k)
    {env : Fin N → ℕ} {B : ℕ} (hB : 2 * B ≤ 2 ^ w) (hk : env k < B) (hv : env acc < B) :
    Good x w (shrS k acc i) env [] (env k * (2 * Ex.nodeCost w + 5 * unitCost w + 1) +
      2 * unitCost w + 1) := by
  have H := good_loopInv (x := x) (w := w) (i := i) (lim := k)
    (body := Stm.set acc (Ex.half (Ex.var acc))) (env := env)
    (fun _ e => e acc ≤ env acc ∧ e k = env k) (fun _ => [])
    (2 * Ex.nodeCost w + unitCost w) (by omega) ⟨le_rfl, rfl⟩ (by
      intro j hj e ⟨h1, h2⟩
      have e1 : Function.update e i j acc = e acc := Function.update_of_ne (Ne.symm hia) _ _
      refine ⟨(Good.set ?_).of_eq rfl (by simp [Ex.size]), ?_, ?_⟩
      · simp only [Ex.Fits, e1]; omega
      · simp only [exec_set_fst, Function.update_self, Ex.eval, e1]; omega
      · rw [exec_set_fst, Function.update_of_ne hka, Function.update_of_ne (Ne.symm hik), h2])
  have := nodeCost_ge w
  exact H.1.of_eq (by simp) (le_of_eq (by ring))

lemma mulBody_step {res a b : Fin N} (hra : res ≠ a) (hrb : res ≠ b) (hab : a ≠ b)
    (e : Fin N → ℕ) {Av Bv j K B : ℕ} (hB : 2 * B ≤ 2 ^ w) (h1 : e res = Av * (Bv % 2 ^ j))
    (h2 : e a = Av * 2 ^ j) (h3 : e b = Bv / 2 ^ j) (hjK : j < K) (hAK : Av * 2 ^ K < B)
    (hBv : Bv < B) :
    Good x w (Xp.mulBody res a b) e [] (10 * Ex.nodeCost w + 3 * unitCost w + 1) ∧
      (exec x (Xp.mulBody res a b) e).1 res = Av * (Bv % 2 ^ (j + 1)) ∧
      (exec x (Xp.mulBody res a b) e).1 a = Av * 2 ^ (j + 1) ∧
      (exec x (Xp.mulBody res a b) e).1 b = Bv / 2 ^ (j + 1) ∧
      ∀ q, q ≠ res → q ≠ a → q ≠ b → (exec x (Xp.mulBody res a b) e).1 q = e q := by
  have hpow : Av * 2 ^ (j + 1) ≤ Av * 2 ^ K :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hjK)
  have hmod : Bv % 2 ^ j < 2 ^ j := Nat.mod_lt _ (by positivity)
  have hres : Av * (Bv % 2 ^ j) ≤ Av * 2 ^ j := Nat.mul_le_mul_left _ hmod.le
  have e2 : Av * 2 ^ (j + 1) = Av * 2 ^ j + Av * 2 ^ j := by ring
  have hmodS : Bv % 2 ^ (j + 1) = Bv % 2 ^ j + 2 ^ j * (Bv / 2 ^ j % 2) := Nat.mod_pow_succ
  have hbv : Bv / 2 ^ j ≤ Bv := Nat.div_le_self _ _
  have hdiv : Bv / 2 ^ j / 2 = Bv / 2 ^ (j + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ]
  -- the conditional addition
  set e₁ : Fin N → ℕ := if Bv / 2 ^ j % 2 ≠ 0 then Function.update e res (e res + e a) else e
    with he₁
  have hite : Good x w (Stm.ite (.odd (.var b)) (.set res (.add (.var res) (.var a))) .skip) e []
      (2 * Ex.nodeCost w + 1 + (3 * Ex.nodeCost w + unitCost w)) ∧
      (exec x (Stm.ite (.odd (.var b)) (.set res (.add (.var res) (.var a))) .skip) e).1 = e₁ := by
    have hc : Ex.Fits w e (.odd (.var b) : Ex N) := by simp only [Ex.Fits]; omega
    by_cases hp : Bv / 2 ^ j % 2 ≠ 0
    · have hcv : (Ex.odd (.var b) : Ex N).eval e ≠ 0 := by simpa [Ex.eval, h3] using hp
      refine ⟨(Good.iteT hc hcv (Good.set ?_)).of_eq rfl (by simp [Ex.size]), ?_⟩
      · simp only [Ex.Fits, Ex.eval, h1, h2]; omega
      · rw [he₁, if_pos hp]; simp only [exec, Ex.eval] at hcv ⊢; simp [hcv]
    · have hcv : (Ex.odd (.var b) : Ex N).eval e = 0 := by
        simp only [Ex.eval, h3]; omega
      refine ⟨(Good.iteF hc hcv Good.skip).of_eq rfl (by simp [Ex.size]; try omega), ?_⟩
      simp only [exec, hcv, ne_eq, not_true_eq_false, if_false, he₁, if_neg hp]
  have r₁ : e₁ res = Av * (Bv % 2 ^ (j + 1)) := by
    rw [hmodS, he₁]
    split_ifs with hp
    · rw [Function.update_self, h1, h2]
      have : Bv / 2 ^ j % 2 = 1 := by omega
      rw [this]; ring
    · have : Bv / 2 ^ j % 2 = 0 := by omega
      rw [h1, this]; ring
  have o₁ : ∀ q, q ≠ res → e₁ q = e q := by
    intro q hq; rw [he₁]; split_ifs
    · exact Function.update_of_ne hq _ _
    · rfl
  have ea₁ : e₁ a = Av * 2 ^ j := by rw [o₁ a (Ne.symm hra), h2]
  have eb₁ : e₁ b = Bv / 2 ^ j := by rw [o₁ b (Ne.symm hrb), h3]
  have := nodeCost_ge w
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hs1 : Good x w (Stm.set b (.half (.var b))) e₁ []
        (2 * Ex.nodeCost w + unitCost w) :=
      (Good.set (by simp only [Ex.Fits, eb₁]; omega)).of_eq rfl (by simp [Ex.size])
    have hs2 : Good x w (Stm.set a (.add (.var a) (.var a)))
        (exec x (Stm.set b (.half (.var b))) e₁).1 [] (3 * Ex.nodeCost w + unitCost w) :=
      (Good.set (by
        simp only [Ex.Fits, Ex.eval, exec_set_fst, Function.update_of_ne hab, ea₁]
        omega)).of_eq rfl (by simp [Ex.size])
    have hs12 := Good.seq0 hs1 hs2
    rw [← hite.2] at hs12
    exact (Good.seq0 hite.1 hs12).mono (by omega)
  · simp only [Xp.mulBody, exec_seq_fst, hite.2, exec_set_fst, Function.update_of_ne hra,
      Function.update_of_ne hrb, r₁]
  · simp only [Xp.mulBody, exec_seq_fst, hite.2, exec_set_fst, Function.update_self, Ex.eval,
      Function.update_of_ne hab, ea₁, e2]
  · simp only [Xp.mulBody, exec_seq_fst, hite.2, exec_set_fst, Function.update_of_ne (Ne.symm hab),
      Function.update_self, Ex.eval, eb₁, hdiv]
  · intro q hq1 hq2 hq3
    simp only [Xp.mulBody, exec_seq_fst, hite.2, exec_set_fst, Function.update_of_ne hq2,
      Function.update_of_ne hq3, o₁ q hq1]

lemma xorBody_step {a b res pw : Fin N} (hab : a ≠ b) (har : a ≠ res) (hap : a ≠ pw)
    (hbr : b ≠ res) (hbp : b ≠ pw) (hrp : res ≠ pw) (e : Fin N → ℕ) {Av Bv j K B : ℕ}
    (hB : 2 * B ≤ 2 ^ w) (h1 : e res < 2 ^ j) (h2 : e pw = 2 ^ j) (h3 : e a ≤ Av)
    (h4 : e b ≤ Bv) (hjK : j < K) (hK : 2 ^ K < B) (hA : Av < B) (hBv : Bv < B) :
    Good x w (xorBody a b res pw) e [] (16 * Ex.nodeCost w + 4 * unitCost w + 1) ∧
      (exec x (xorBody a b res pw) e).1 res < 2 ^ (j + 1) ∧
      (exec x (xorBody a b res pw) e).1 pw = 2 ^ (j + 1) ∧
      (exec x (xorBody a b res pw) e).1 a ≤ Av ∧
      (exec x (xorBody a b res pw) e).1 b ≤ Bv ∧
      ∀ q, q ≠ a → q ≠ b → q ≠ res → q ≠ pw → (exec x (xorBody a b res pw) e).1 q = e q := by
  have hjp : 2 ^ (j + 1) ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hjK
  have e2 : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by ring
  set e₁ : Fin N → ℕ := if (Ex.odd (.add (.odd (.var a)) (.odd (.var b))) : Ex N).eval e ≠ 0 then Function.update e res (e res + e pw) else e
    with he₁
  have hite : Good x w (Stm.ite (Ex.odd (.add (.odd (.var a)) (.odd (.var b))) : Ex N) (.set res (.add (.var res) (.var pw))) .skip) e []
      (6 * Ex.nodeCost w + 1 + (3 * Ex.nodeCost w + unitCost w)) ∧
      (exec x (Stm.ite (Ex.odd (.add (.odd (.var a)) (.odd (.var b))) : Ex N) (.set res (.add (.var res) (.var pw))) .skip) e).1 = e₁ := by
    have hc : Ex.Fits w e (Ex.odd (.add (.odd (.var a)) (.odd (.var b))) : Ex N) := by
      simp only [Ex.Fits, Ex.eval]; omega
    by_cases hp : ((Ex.odd (.add (.odd (.var a)) (.odd (.var b))) : Ex N)).eval e ≠ 0
    · refine ⟨(Good.iteT hc hp (Good.set ?_)).of_eq rfl (by simp [Ex.size]), ?_⟩
      · simp only [Ex.Fits, Ex.eval]; omega
      · rw [he₁, if_pos hp]; simp only [exec]; rw [if_pos hp]; rfl
    · have hp' : ((Ex.odd (.add (.odd (.var a)) (.odd (.var b))) : Ex N)).eval e = 0 := by simpa using hp
      refine ⟨(Good.iteF hc hp' Good.skip).of_eq rfl (by simp [Ex.size]; try omega), ?_⟩
      rw [he₁, if_neg hp]; simp only [exec, if_neg hp]
  have o₁ : ∀ q, q ≠ res → e₁ q = e q := by
    intro q hq; rw [he₁]; split_ifs
    · exact Function.update_of_ne hq _ _
    · rfl
  have r₁ : e₁ res < 2 ^ (j + 1) := by
    rw [he₁]; split_ifs
    · rw [Function.update_self]; omega
    · omega
  have := nodeCost_ge w
  have hrest : ∀ f : Fin N → ℕ, f a ≤ Av → f b ≤ Bv → f pw = 2 ^ j →
      Good x w (Stm.seq (.set a (.half (.var a))) (.seq (.set b (.half (.var b)))
        (.set pw (.add (.var pw) (.var pw))))) f [] (7 * Ex.nodeCost w + 3 * unitCost w) := by
    intro f fa fb fp
    have g1 : Good x w (Stm.set a (.half (.var a))) f [] (2 * Ex.nodeCost w + unitCost w) :=
      (Good.set (by simp only [Ex.Fits]; omega)).of_eq rfl (by simp [Ex.size])
    have g2 : Good x w (Stm.set b (.half (.var b))) (exec x (Stm.set a (.half (.var a))) f).1 []
        (2 * Ex.nodeCost w + unitCost w) :=
      (Good.set (by simp only [Ex.Fits, exec_set_fst, Function.update_of_ne hab.symm]; omega)).of_eq
        rfl (by simp [Ex.size])
    have g3 : Good x w (Stm.set pw (.add (.var pw) (.var pw)))
        (exec x (Stm.set b (.half (.var b))) (exec x (Stm.set a (.half (.var a))) f).1).1 []
        (3 * Ex.nodeCost w + unitCost w) :=
      (Good.set (by
        simp only [Ex.Fits, Ex.eval, exec_set_fst, Function.update_of_ne hbp.symm,
          Function.update_of_ne hap.symm]
        omega)).of_eq rfl (by simp [Ex.size])
    exact (Good.seq0 g1 (Good.seq0 g2 g3)).mono (by omega)
  have hr := hrest e₁ (by rw [o₁ a har]; exact h3) (by rw [o₁ b hbr]; exact h4)
    (by rw [o₁ pw hrp.symm]; exact h2)
  rw [← hite.2] at hr
  refine ⟨(Good.seq0 hite.1 hr).mono (by omega), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [xorBody, exec_seq_fst, hite.2, exec_set_fst, Function.update_of_ne hrp,
      Function.update_of_ne hbr.symm, Function.update_of_ne har.symm]
    exact r₁
  · simp only [xorBody, exec_seq_fst, hite.2, exec_set_fst, Function.update_self,
      Function.update_of_ne hbp.symm, Function.update_of_ne hap.symm, Ex.eval, o₁ pw hrp.symm, h2]
    ring
  · simp only [xorBody, exec_seq_fst, hite.2, exec_set_fst, Function.update_of_ne hap,
      Function.update_of_ne hab, Function.update_self, Ex.eval, o₁ a har]
    have := Nat.div_le_self (e a) 2; omega
  · simp only [xorBody, exec_seq_fst, hite.2, exec_set_fst, Function.update_of_ne hbp,
      Function.update_self, Ex.eval, Function.update_of_ne hab.symm, o₁ b hbr]
    have := Nat.div_le_self (e b) 2; omega
  · intro q q1 q2 q3 q4
    simp only [xorBody, exec_seq_fst, hite.2, exec_set_fst, Function.update_of_ne q1,
      Function.update_of_ne q2, Function.update_of_ne q4, o₁ q q3]

lemma xorS_good {a b res pw t lim : Fin N} (hab : a ≠ b) (har : a ≠ res) (hap : a ≠ pw)
    (hat : a ≠ t) (hbr : b ≠ res) (hbp : b ≠ pw) (hbt : b ≠ t) (hrp : res ≠ pw)
    (hrt : res ≠ t) (hpt : pw ≠ t) (hla : lim ≠ a) (hlb : lim ≠ b) (hlr : lim ≠ res)
    (hlp : lim ≠ pw) (hlt : lim ≠ t) {env : Fin N → ℕ} {B : ℕ} (hB : 2 * B ≤ 2 ^ w)
    (hA : env a < B) (hBv : env b < B) (hK : 2 ^ env lim < B) :
    Good x w (xorS a b res pw t lim) env []
      (env lim * (16 * Ex.nodeCost w + 8 * unitCost w + 2) + 2 * Ex.nodeCost w +
        4 * unitCost w + 1) := by
  have := nodeCost_ge w
  have hKlt : env lim < 2 ^ env lim := Nat.lt_two_pow_self
  set env₀ := Function.update (Function.update env res 0) pw 1 with he₀
  have hL : env₀ lim = env lim := by
    rw [he₀, Function.update_of_ne hlp, Function.update_of_ne hlr]
  have g1 : Good x w (Stm.set res (.const 0)) env [] (Ex.nodeCost w + unitCost w) :=
    (Good.set (by simp only [Ex.Fits]; positivity)).of_eq rfl (by simp [Ex.size])
  have g2 : Good x w (Stm.set pw (.const 1)) (exec x (Stm.set res (.const 0)) env).1 []
      (Ex.nodeCost w + unitCost w) :=
    (Good.set (by have := Nat.one_le_two_pow (n := env lim); simp only [Ex.Fits]; omega)).of_eq rfl
      (by simp [Ex.size])
  have H := good_loopInv (x := x) (w := w) (i := t) (lim := lim) (body := xorBody a b res pw)
    (env := env₀) (fun j e => e res < 2 ^ j ∧ e pw = 2 ^ j ∧ e a ≤ env a ∧ e b ≤ env b)
    (fun _ => []) (16 * Ex.nodeCost w + 4 * unitCost w + 1) (by rw [hL]; omega)
    ⟨by simp [he₀, Function.update_of_ne hrp], by simp [he₀],
      by simp [he₀, Function.update_of_ne hap, Function.update_of_ne har],
      by simp [he₀, Function.update_of_ne hbp, Function.update_of_ne hbr]⟩ (by
      intro j hj e ⟨h1, h2, h3, h4⟩
      rw [hL] at hj
      have S := xorBody_step (x := x) hab har hap hbr hbp hrp (Function.update e t j) hB
        (by rw [Function.update_of_ne hrt]; exact h1) (by rw [Function.update_of_ne hpt]; exact h2)
        (by rw [Function.update_of_ne hat]; exact h3) (by rw [Function.update_of_ne hbt]; exact h4)
        hj hK hA hBv
      exact ⟨S.1, S.2.1, S.2.2.1, S.2.2.2.1, S.2.2.2.2.1⟩)
  rw [hL] at H
  have g3 : Good x w (Stm.loop t lim (xorBody a b res pw))
      (exec x (Stm.set pw (.const 1)) (exec x (Stm.set res (.const 0)) env).1).1 []
      (env lim * (16 * Ex.nodeCost w + 4 * unitCost w + 1 + 4 * unitCost w + 1) +
        2 * unitCost w + 1) := by
    have e0 : (exec x (Stm.set pw (.const 1)) (exec x (Stm.set res (.const 0)) env).1).1 = env₀ :=
      rfl
    rw [e0]; exact H.1.of_eq (by simp) le_rfl
  exact (Good.seq0 g1 (Good.seq0 g2 g3)).mono (by nlinarith)

end Routines

/-! ## Written registers -/

/-- All registers written by `c` satisfy `P`. -/
def WrIn {N : ℕ} (P : Fin N → Prop) (c : Stm N) : Prop := ∀ q, Stm.wr c q = true → P q

namespace WrIn

variable {N : ℕ} {P Q : Fin N → Prop} {p q : Stm N}

lemma mono (h : WrIn P p) (hPQ : ∀ r, P r → Q r) : WrIn Q p := fun r hr => hPQ r (h r hr)
lemma skip : WrIn P (Stm.skip : Stm N) := fun _ h => by simp [Stm.wr] at h
lemma emit {e : Ex N} : WrIn P (Stm.emit e) := fun _ h => by simp [Stm.wr] at h
lemma set {r : Fin N} {e : Ex N} (hr : P r) : WrIn P (Stm.set r e) := fun _ h => by
  simp only [Stm.wr, decide_eq_true_eq] at h; exact h ▸ hr
lemma len {r : Fin N} (hr : P r) : WrIn P (Stm.len r) := fun _ h => by
  simp only [Stm.wr, decide_eq_true_eq] at h; exact h ▸ hr
lemma seq (hp : WrIn P p) (hq : WrIn P q) : WrIn P (Stm.seq p q) := fun r h => by
  simp only [Stm.wr, Bool.or_eq_true] at h; exact h.elim (hp r) (hq r)
lemma ite {c : Ex N} (hp : WrIn P p) (hq : WrIn P q) : WrIn P (Stm.ite c p q) := fun r h => by
  simp only [Stm.wr, Bool.or_eq_true] at h; exact h.elim (hp r) (hq r)
lemma loop {i lim : Fin N} (hi : P i) (hp : WrIn P p) : WrIn P (Stm.loop i lim p) := fun r h => by
  simp only [Stm.wr, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact h ▸ hi
  · exact hp r h
lemma loopX {i lim xb : Fin N} (hi : P i) (hx : P xb) (hp : WrIn P p) :
    WrIn P (Stm.loopX i lim xb p) := fun r h => by
  simp only [Stm.wr, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (h | h) | h
  · exact h ▸ hi
  · exact h ▸ hx
  · exact hp r h

lemma frame (h : WrIn P p) {r : Fin N} (hr : ¬ P r) (env : Fin N → ℕ) :
    (Stm.exec x p env).1 r = env r :=
  Stm.exec_frame p env r (by
    by_contra hc
    exact hr (h r (by simpa using hc)))

lemma wr_false (h : WrIn P p) {r : Fin N} (hr : ¬ P r) : Stm.wr p r = false := by
  by_contra hc
  exact hr (h r (by simpa using hc))

end WrIn

/-- Registers `≥ t`. -/
def Above (R t : ℕ) (q : Fin (R + 1)) : Prop := ∃ j, t ≤ j ∧ q = rg R j

lemma above_rg {R t j : ℕ} (h : t ≤ j) : Above R t (rg R j) := ⟨j, h, rfl⟩

lemma above_mono {R t t' : ℕ} (h : t ≤ t') {q : Fin (R + 1)} (hq : Above R t' q) : Above R t q := by
  obtain ⟨j, hj, rfl⟩ := hq; exact ⟨j, by omega, rfl⟩

lemma not_above {R t j : ℕ} (hj : j < t) (hjR : j < R) : ¬ Above R t (rg R j) := by
  rintro ⟨j', hj', he⟩
  exact rg_ne hjR (by omega) he

namespace Xp

variable {d : ℕ} {A : List ℕ}

lemma wrIn_comp (e : Xp) : ∀ t : ℕ, WrIn (Above R t) (comp R d A t e) := by
  induction e with
  | var i =>
    intro t; simp only [comp]; split_ifs
    · exact WrIn.set (above_rg le_rfl)
    · exact WrIn.set (above_rg le_rfl)
  | const c => intro t; exact WrIn.set (above_rg le_rfl)
  | add a b iha ihb =>
    intro t
    exact (iha t).seq (((ihb (t + 1)).mono fun _ => above_mono (by omega)).seq
      (WrIn.set (above_rg le_rfl)))
  | lt a b iha ihb =>
    intro t
    exact (iha t).seq (((ihb (t + 1)).mono fun _ => above_mono (by omega)).seq
      (WrIn.set (above_rg le_rfl)))
  | half a iha => intro t; exact (iha t).seq (WrIn.set (above_rg le_rfl))
  | odd a iha => intro t; exact (iha t).seq (WrIn.set (above_rg le_rfl))
  | mulB a b k iha ihb ihk =>
    intro t
    refine ((iha (t + 1)).mono fun _ => above_mono (by omega)).seq
      (((ihb (t + 2)).mono fun _ => above_mono (by omega)).seq
      (((ihk (t + 3)).mono fun _ => above_mono (by omega)).seq
      ((WrIn.set (above_rg le_rfl)).seq (WrIn.loop (above_rg (by omega)) ?_))))
    exact (WrIn.ite (WrIn.set (above_rg le_rfl)) WrIn.skip).seq
      ((WrIn.set (above_rg (by omega))).seq (WrIn.set (above_rg (by omega))))
  | shl a k iha ihk =>
    intro t
    exact (iha t).seq (((ihk (t + 1)).mono fun _ => above_mono (by omega)).seq
      (WrIn.loop (above_rg (by omega)) (WrIn.set (above_rg le_rfl))))
  | shr a k iha ihk =>
    intro t
    exact (iha t).seq (((ihk (t + 1)).mono fun _ => above_mono (by omega)).seq
      (WrIn.loop (above_rg (by omega)) (WrIn.set (above_rg le_rfl))))
  | xorM a b k iha ihb ihk =>
    intro t
    refine ((iha (t + 1)).mono fun _ => above_mono (by omega)).seq
      (((ihb (t + 2)).mono fun _ => above_mono (by omega)).seq
      (((ihk (t + 3)).mono fun _ => above_mono (by omega)).seq
      ((WrIn.set (above_rg le_rfl)).seq ((WrIn.set (above_rg (by omega))).seq
        (WrIn.loop (above_rg (by omega)) ?_)))))
    exact (WrIn.ite (WrIn.set (above_rg le_rfl)) WrIn.skip).seq
      ((WrIn.set (above_rg (by omega))).seq ((WrIn.set (above_rg (by omega))).seq
        (WrIn.set (above_rg (by omega)))))

lemma comp_frame (e : Xp) {t j : ℕ} (hj : j < t) (hjR : j < R) (env : Fin (R + 1) → ℕ) :
    (Stm.exec x (comp R d A t e) env).1 (rg R j) = env (rg R j) :=
  (wrIn_comp e t).frame (not_above hj hjR) env

end Xp

end Lax119563Proofs.Reduction

end Reduction_XLang

/-! ### Formerly `Lax119563Proofs.Reduction.XSpec` -/

section Reduction_XSpec

/-!
# Specification of compiled expressions

`Xp.spec`: the compiled expression `comp R d A t e` is `Good` (fits, no output, cost at most
`κ w * cost`) and leaves the value of `e` in register `t`, provided the registers below `d`
outside `A` hold the stack and the values fit below `B` with `2 B ≤ 2 ^ w`.
-/

namespace Lax119563Proofs.Reduction

variable {R : ℕ} {x : List Bool} {w : ℕ}

namespace Xp

variable {d : ℕ} {A : List ℕ}

lemma κ_ge (w : ℕ) : 32 * Ex.nodeCost w ≤ κ w ∧ 64 ≤ unitCost w ∧ unitCost w ≤ Ex.nodeCost w :=
  ⟨le_rfl, (nodeCost_ge w).1, (nodeCost_ge w).2⟩

lemma κ_split (w a b : ℕ) : κ w * (a + b) = κ w * a + κ w * b := mul_add _ _ _

/-- The induction hypothesis of `spec`. -/
def SpecAt (x : List Bool) (w B : ℕ) (R d : ℕ) (A : List ℕ) (ρ : List ℕ) (e : Xp) (t : ℕ) :
    Prop :=
  ∀ env : Fin (R + 1) → ℕ, d ≤ t → t + e.need ≤ R →
    (∀ i < d, i ∉ A → env (rg R i) = ρ.getD i 0) → e.Fits B ρ →
    Good x w (comp R d A t e) env [] (κ w * e.cost ρ) ∧
      (Stm.exec x (comp R d A t e) env).1 (rg R t) = e.eval ρ

/-- Two-operand constant-time nodes. -/
lemma spec_bin {B : ℕ} {ρ : List ℕ} (a b : Xp) (op : Ex (R + 1) → Ex (R + 1) → Ex (R + 1))
    (t : ℕ) (env : Fin (R + 1) → ℕ) (iha : SpecAt x w B R d A ρ a t)
    (ihb : SpecAt x w B R d A ρ b (t + 1)) (hdt : d ≤ t)
    (hR : t + max a.need (b.need + 1) ≤ R)
    (henv : ∀ i < d, i ∉ A → env (rg R i) = ρ.getD i 0) (hfa : a.Fits B ρ) (hfb : b.Fits B ρ)
    (hop : ∀ env' : Fin (R + 1) → ℕ, env' (rg R t) = a.eval ρ → env' (rg R (t + 1)) = b.eval ρ →
      Ex.Fits w env' (op (.var (rg R t)) (.var (rg R (t + 1)))) ∧
        (op (.var (rg R t)) (.var (rg R (t + 1)))).size = 3) :
    Good x w (.seq (comp R d A t a) (.seq (comp R d A (t + 1) b)
        (.set (rg R t) (op (.var (rg R t)) (.var (rg R (t + 1))))))) env []
        (κ w * (a.cost ρ + b.cost ρ + 1)) ∧
      ∃ env' : Fin (R + 1) → ℕ, env' (rg R t) = a.eval ρ ∧ env' (rg R (t + 1)) = b.eval ρ ∧
        (Stm.exec x (.seq (comp R d A t a) (.seq (comp R d A (t + 1) b)
          (.set (rg R t) (op (.var (rg R t)) (.var (rg R (t + 1))))))) env).1 (rg R t) =
          Ex.eval env' (op (.var (rg R t)) (.var (rg R (t + 1)))) := by
  have K := κ_ge w
  have h1 := one_le_need b
  obtain ⟨g1, v1⟩ := iha env hdt (by omega) henv hfa
  have henv1 : ∀ i < d, i ∉ A →
      (Stm.exec x (comp R d A t a) env).1 (rg R i) = ρ.getD i 0 := fun i hi hiA => by
    rw [comp_frame a (by omega) (by omega)]; exact henv i hi hiA
  obtain ⟨g2, v2⟩ := ihb _ (by omega) (by omega) henv1 hfb
  have v1' : (Stm.exec x (comp R d A (t + 1) b) (Stm.exec x (comp R d A t a) env).1).1
      (rg R t) = a.eval ρ := by rw [comp_frame b (by omega) (by omega)]; exact v1
  obtain ⟨hf3, hs3⟩ := hop _ v1' v2
  refine ⟨(Good.seq0 g1 (Good.seq0 g2 ((Good.set hf3).of_eq rfl le_rfl))).mono ?_,
    _, v1', v2, ?_⟩
  · rw [hs3, κ_split, κ_split]; omega
  · simp only [exec_seq_fst, exec_set_fst, Function.update_self]

set_option maxHeartbeats 400000 in
lemma spec_mulB {B : ℕ} (hB : 2 * B ≤ 2 ^ w) {ρ : List ℕ} (a b k : Xp) (iha : ∀ t, SpecAt x w B R d A ρ a t) (ihb : ∀ t, SpecAt x w B R d A ρ b t) (ihk : ∀ t, SpecAt x w B R d A ρ k t) (t : ℕ) :
    SpecAt x w B R d A ρ (mulB a b k) t := by
    have K := κ_ge w
    intro env hdt hR henv hf
    obtain ⟨hfa, hfb, hfk, hAK⟩ := hf
    simp only [need] at hR
    have hBv := eval_lt hfb; have hKv := eval_lt hfk
    obtain ⟨g1, v1⟩ := iha (t + 1) env (by omega) (by omega) henv hfa
    set env1 := (Stm.exec x (comp R d A (t + 1) a) env).1 with he1
    obtain ⟨g2, v2⟩ := ihb (t + 2) env1 (by omega) (by omega) (fun i hi hiA => by
      rw [he1, comp_frame a (by omega) (by omega)]; exact henv i hi hiA) hfb
    set env2 := (Stm.exec x (comp R d A (t + 2) b) env1).1 with he2
    obtain ⟨g3, v3⟩ := ihk (t + 3) env2 (by omega) (by omega) (fun i hi hiA => by
      rw [he2, comp_frame b (by omega) (by omega), he1, comp_frame a (by omega) (by omega)]
      exact henv i hi hiA) hfk
    set env3 := (Stm.exec x (comp R d A (t + 3) k) env2).1 with he3
    have w1 : env3 (rg R (t + 1)) = a.eval ρ := by
      rw [he3, comp_frame k (by omega) (by omega), he2, comp_frame b (by omega) (by omega)]
      exact v1
    have w2 : env3 (rg R (t + 2)) = b.eval ρ := by
      rw [he3, comp_frame k (by omega) (by omega)]; exact v2
    set env4 := Function.update env3 (rg R t) 0 with he4
    have n01 := rg_ne (R := R) (t := t) (t' := t + 1) (by omega) (by omega)
    have n02 := rg_ne (R := R) (t := t) (t' := t + 2) (by omega) (by omega)
    have n03 := rg_ne (R := R) (t := t) (t' := t + 3) (by omega) (by omega)
    have n04 := rg_ne (R := R) (t := t) (t' := t + 4) (by omega) (by omega)
    have n12 := rg_ne (R := R) (t := t + 1) (t' := t + 2) (by omega) (by omega)
    have n14 := rg_ne (R := R) (t := t + 1) (t' := t + 4) (by omega) (by omega)
    have n24 := rg_ne (R := R) (t := t + 2) (t' := t + 4) (by omega) (by omega)
    have hL : env4 (rg R (t + 3)) = k.eval ρ := by
      rw [he4, Function.update_of_ne (Ne.symm n03)]; exact v3
    have H := Stm.good_loopInv (x := x) (w := w) (i := rg R (t + 4)) (lim := rg R (t + 3))
      (body := mulBody (rg R t) (rg R (t + 1)) (rg R (t + 2))) (env := env4)
      (fun j e => e (rg R t) = a.eval ρ * (b.eval ρ % 2 ^ j) ∧
        e (rg R (t + 1)) = a.eval ρ * 2 ^ j ∧ e (rg R (t + 2)) = b.eval ρ / 2 ^ j)
      (fun _ => []) (10 * Ex.nodeCost w + 3 * unitCost w + 1) (by rw [hL]; omega)
      ⟨by simp [he4, Nat.mod_one], by rw [he4, Function.update_of_ne (Ne.symm n01), w1]; simp,
        by rw [he4, Function.update_of_ne (Ne.symm n02), w2]; simp⟩ (by
        intro j hj e ⟨h1, h2, h3⟩
        rw [hL] at hj
        have S := mulBody_step (x := x) n01 n02 n12 (Function.update e (rg R (t + 4)) j) hB
          (by rw [Function.update_of_ne n04]; exact h1)
          (by rw [Function.update_of_ne n14]; exact h2)
          (by rw [Function.update_of_ne n24]; exact h3) hj hAK hBv
        exact ⟨S.1, S.2.1, S.2.2.1, S.2.2.2.1⟩)
    rw [hL] at H
    have g4 : Good x w (Stm.set (rg R t) (.const 0)) env3 [] (Ex.nodeCost w + unitCost w) :=
      (Good.set (by simp only [Ex.Fits]; positivity)).of_eq rfl (by simp [Ex.size])
    have hK1 : k.eval ρ * (10 * Ex.nodeCost w + 3 * unitCost w + 1 + 4 * unitCost w + 1) ≤
        k.eval ρ * κ w := Nat.mul_le_mul_left _ (by omega)
    refine ⟨(Good.seq0 g1 (Good.seq0 g2 (Good.seq0 g3 (Good.seq0 g4
      (H.1.of_eq (by simp) le_rfl))))).mono ?_, ?_⟩
    · simp only [cost, κ_split]; rw [Nat.mul_comm (κ w) (k.eval ρ)]; omega
    · have hx : (Stm.exec x (comp R d A t (mulB a b k)) env).1 = (Stm.exec x (Stm.loop
          (rg R (t + 4)) (rg R (t + 3)) (mulBody (rg R t) (rg R (t + 1)) (rg R (t + 2)))) env4).1 :=
        rfl
      rw [hx, Stm.exec_loop_fst, Function.update_of_ne n04, hL, H.2.1]
      rfl

set_option maxHeartbeats 400000 in
lemma spec_shl {B : ℕ} (hB : 2 * B ≤ 2 ^ w) {ρ : List ℕ} (a k : Xp) (iha : ∀ t, SpecAt x w B R d A ρ a t) (ihk : ∀ t, SpecAt x w B R d A ρ k t) (t : ℕ) :
    SpecAt x w B R d A ρ (shl a k) t := by
    have K := κ_ge w
    intro env hdt hR henv hf
    obtain ⟨hfa, hfk, hAK⟩ := hf
    simp only [need] at hR
    have hKv := eval_lt hfk
    obtain ⟨g1, v1⟩ := iha t env hdt (by omega) henv hfa
    set env1 := (Stm.exec x (comp R d A t a) env).1 with he1
    obtain ⟨g2, v2⟩ := ihk (t + 1) env1 (by omega) (by omega) (fun i hi hiA => by
      rw [he1, comp_frame a (by omega) (by omega)]; exact henv i hi hiA) hfk
    set env2 := (Stm.exec x (comp R d A (t + 1) k) env1).1 with he2
    have w1 : env2 (rg R t) = a.eval ρ := by
      rw [he2, comp_frame k (by omega) (by omega)]; exact v1
    have n01 := rg_ne (R := R) (t := t) (t' := t + 1) (by omega) (by omega)
    have n02 := rg_ne (R := R) (t := t) (t' := t + 2) (by omega) (by omega)
    have n12 := rg_ne (R := R) (t := t + 1) (t' := t + 2) (by omega) (by omega)
    have g3 := shlS_good (x := x) (Ne.symm n02) (Ne.symm n01) (Ne.symm n12) hB
      (env := env2) (by rw [v2]; exact hKv) (by rw [w1, v2]; exact hAK)
    rw [v2] at g3
    have hK1 : k.eval ρ * (3 * Ex.nodeCost w + 5 * unitCost w + 1) ≤ k.eval ρ * κ w :=
      Nat.mul_le_mul_left _ (by omega)
    refine ⟨(Good.seq0 g1 (Good.seq0 g2 g3)).mono ?_, ?_⟩
    · simp only [cost, κ_split]; rw [Nat.mul_comm (κ w) (k.eval ρ)]; omega
    · simp only [comp, exec_seq_fst]
      rw [(Stm.exec_shlS (x := x) (Ne.symm n02) (Ne.symm n01) env2).1, w1, v2]; rfl

set_option maxHeartbeats 400000 in
lemma spec_shr {B : ℕ} (hB : 2 * B ≤ 2 ^ w) {ρ : List ℕ} (a k : Xp) (iha : ∀ t, SpecAt x w B R d A ρ a t) (ihk : ∀ t, SpecAt x w B R d A ρ k t) (t : ℕ) :
    SpecAt x w B R d A ρ (shr a k) t := by
    have K := κ_ge w
    intro env hdt hR henv hf
    obtain ⟨hfa, hfk⟩ := hf
    simp only [need] at hR
    have hKv := eval_lt hfk
    have hAv := eval_lt hfa
    obtain ⟨g1, v1⟩ := iha t env hdt (by omega) henv hfa
    set env1 := (Stm.exec x (comp R d A t a) env).1 with he1
    obtain ⟨g2, v2⟩ := ihk (t + 1) env1 (by omega) (by omega) (fun i hi hiA => by
      rw [he1, comp_frame a (by omega) (by omega)]; exact henv i hi hiA) hfk
    set env2 := (Stm.exec x (comp R d A (t + 1) k) env1).1 with he2
    have w1 : env2 (rg R t) = a.eval ρ := by
      rw [he2, comp_frame k (by omega) (by omega)]; exact v1
    have n01 := rg_ne (R := R) (t := t) (t' := t + 1) (by omega) (by omega)
    have n02 := rg_ne (R := R) (t := t) (t' := t + 2) (by omega) (by omega)
    have n12 := rg_ne (R := R) (t := t + 1) (t' := t + 2) (by omega) (by omega)
    have g3 := shrS_good (x := x) (Ne.symm n02) (Ne.symm n01) (Ne.symm n12) hB
      (env := env2) (by rw [v2]; exact hKv) (by rw [w1]; exact hAv)
    rw [v2] at g3
    have hK1 : k.eval ρ * (2 * Ex.nodeCost w + 5 * unitCost w + 1) ≤ k.eval ρ * κ w :=
      Nat.mul_le_mul_left _ (by omega)
    refine ⟨(Good.seq0 g1 (Good.seq0 g2 g3)).mono ?_, ?_⟩
    · simp only [cost, κ_split]; rw [Nat.mul_comm (κ w) (k.eval ρ)]; omega
    · simp only [comp, exec_seq_fst]
      rw [(Stm.exec_shrS (x := x) (Ne.symm n02) (Ne.symm n01) env2).1, w1, v2]; rfl

/-- Distinct registers `t, …, t + 5`. -/
structure Regs6 (R t : ℕ) : Prop where
  n10 : rg R (t + 1) ≠ rg R t
  n12 : rg R (t + 1) ≠ rg R (t + 2)
  n14 : rg R (t + 1) ≠ rg R (t + 4)
  n15 : rg R (t + 1) ≠ rg R (t + 5)
  n20 : rg R (t + 2) ≠ rg R t
  n24 : rg R (t + 2) ≠ rg R (t + 4)
  n25 : rg R (t + 2) ≠ rg R (t + 5)
  n04 : rg R t ≠ rg R (t + 4)
  n05 : rg R t ≠ rg R (t + 5)
  n45 : rg R (t + 4) ≠ rg R (t + 5)
  n31 : rg R (t + 3) ≠ rg R (t + 1)
  n32 : rg R (t + 3) ≠ rg R (t + 2)
  n30 : rg R (t + 3) ≠ rg R t
  n34 : rg R (t + 3) ≠ rg R (t + 4)
  n35 : rg R (t + 3) ≠ rg R (t + 5)

lemma regs6 {R t : ℕ} (h : t + 6 ≤ R) : Regs6 R t :=
  ⟨rg_ne (by omega) (by omega), rg_ne (by omega) (by omega), rg_ne (by omega) (by omega),
    rg_ne (by omega) (by omega), rg_ne (by omega) (by omega), rg_ne (by omega) (by omega),
    rg_ne (by omega) (by omega), rg_ne (by omega) (by omega), rg_ne (by omega) (by omega),
    rg_ne (by omega) (by omega), rg_ne (by omega) (by omega), rg_ne (by omega) (by omega),
    rg_ne (by omega) (by omega), rg_ne (by omega) (by omega), rg_ne (by omega) (by omega)⟩

set_option maxHeartbeats 400000 in
lemma spec_xorM {B : ℕ} (hB : 2 * B ≤ 2 ^ w) {ρ : List ℕ} (a b k : Xp) (iha : ∀ t, SpecAt x w B R d A ρ a t) (ihb : ∀ t, SpecAt x w B R d A ρ b t) (ihk : ∀ t, SpecAt x w B R d A ρ k t) (t : ℕ) :
    SpecAt x w B R d A ρ (xorM a b k) t := by
    have K := κ_ge w
    intro env hdt hR henv hf
    obtain ⟨hfa, hfb, hfk, hK⟩ := hf
    simp only [need] at hR
    have hAv := eval_lt hfa; have hBv := eval_lt hfb
    have hn := regs6 (R := R) (t := t) (by omega)
    obtain ⟨g1, v1⟩ := iha (t + 1) env (by omega) (by omega) henv hfa
    set env1 := (Stm.exec x (comp R d A (t + 1) a) env).1 with he1
    obtain ⟨g2, v2⟩ := ihb (t + 2) env1 (by omega) (by omega) (fun i hi hiA => by
      rw [he1, comp_frame a (by omega) (by omega)]; exact henv i hi hiA) hfb
    set env2 := (Stm.exec x (comp R d A (t + 2) b) env1).1 with he2
    obtain ⟨g3, v3⟩ := ihk (t + 3) env2 (by omega) (by omega) (fun i hi hiA => by
      rw [he2, comp_frame b (by omega) (by omega), he1, comp_frame a (by omega) (by omega)]
      exact henv i hi hiA) hfk
    set env3 := (Stm.exec x (comp R d A (t + 3) k) env2).1 with he3
    have w1 : env3 (rg R (t + 1)) = a.eval ρ := by
      rw [he3, comp_frame k (by omega) (by omega), he2, comp_frame b (by omega) (by omega)]
      exact v1
    have w2 : env3 (rg R (t + 2)) = b.eval ρ := by
      rw [he3, comp_frame k (by omega) (by omega)]; exact v2
    have g4 := xorS_good (x := x) hn.n12 hn.n10 hn.n14 hn.n15 hn.n20 hn.n24 hn.n25 hn.n04 hn.n05 hn.n45 hn.n31 hn.n32 hn.n30 hn.n34 hn.n35 hB
      (env := env3) (by rw [w1]; exact hAv) (by rw [w2]; exact hBv) (by rw [v3]; exact hK)
    rw [v3] at g4
    have hK1 : k.eval ρ * (16 * Ex.nodeCost w + 8 * unitCost w + 2) ≤ k.eval ρ * κ w :=
      Nat.mul_le_mul_left _ (by omega)
    refine ⟨(Good.seq0 g1 (Good.seq0 g2 (Good.seq0 g3 g4))).mono ?_, ?_⟩
    · simp only [cost, κ_split]; rw [Nat.mul_comm (κ w) (k.eval ρ)]; omega
    · have hx : (Stm.exec x (comp R d A t (xorM a b k)) env).1 = (Stm.exec x (Stm.xorS
          (rg R (t + 1)) (rg R (t + 2)) (rg R t) (rg R (t + 4)) (rg R (t + 5)) (rg R (t + 3)))
          env3).1 := rfl
      rw [hx, (Stm.exec_xorS (x := x) hn.n12 hn.n10 hn.n14 hn.n15 hn.n20 hn.n24 hn.n25 hn.n04 hn.n05 hn.n45 hn.n31 hn.n32 hn.n30 hn.n34
        env3).1]
      rw [w1, w2, v3]; rfl

/-- **Specification of compiled expressions.** -/
theorem spec {B : ℕ} (hB : 2 * B ≤ 2 ^ w) {ρ : List ℕ} (hρ : ρ.length = d)
    (hA : ∀ i ∈ A, ρ.getD i 0 = 0) (e : Xp) : ∀ t : ℕ, SpecAt x w B R d A ρ e t := by
  have K := κ_ge w
  intro t
  induction e generalizing t with
  | var i =>
    intro env hdt hR henv hf
    simp only [comp]
    split_ifs with hi
    · refine ⟨(Good.set ?_).of_eq rfl (by simp [Ex.size, cost]; omega), ?_⟩
      · simp only [Ex.Fits]; rw [henv i hi.1 hi.2]; have : ρ.getD i 0 < B := hf; omega
      · simp only [exec_set_fst, Function.update_self, Ex.eval, eval]; exact henv i hi.1 hi.2
    · refine ⟨(Good.set ?_).of_eq rfl (by simp [Ex.size, cost]; omega), ?_⟩
      · simp only [Ex.Fits]; positivity
      · simp only [exec_set_fst, Function.update_self, Ex.eval, eval]
        rcases not_and_or.mp hi with hi | hi
        · rw [List.getD_eq_default _ _ (by omega)]
        · rw [hA i (not_not.mp hi)]
  | const c =>
    intro env hdt hR henv hf
    refine ⟨(Good.set ?_).of_eq rfl (by simp [Ex.size, cost]; omega), ?_⟩
    · simp only [Ex.Fits]; have : c < B := hf; omega
    · simp [comp, exec_set_fst, Ex.eval, eval]
  | add a b iha ihb =>
    intro env hdt hR henv hf
    obtain ⟨hfa, hfb, hs⟩ := hf
    have ha := eval_lt hfa; have hb := eval_lt hfb
    obtain ⟨g, env', e1, e2, hv⟩ := spec_bin a b Ex.add t env (iha t) (ihb (t + 1)) hdt hR henv
      hfa hfb (fun env' h1 h2 => ⟨by simp only [Ex.Fits, Ex.eval, h1, h2]; omega, rfl⟩)
    exact ⟨g, by rw [comp, hv]; simp [Ex.eval, e1, e2, eval]⟩
  | lt a b iha ihb =>
    intro env hdt hR henv hf
    obtain ⟨hfa, hfb⟩ := hf
    have ha := eval_lt hfa; have hb := eval_lt hfb
    obtain ⟨g, env', e1, e2, hv⟩ := spec_bin a b Ex.lt t env (iha t) (ihb (t + 1)) hdt hR henv
      hfa hfb (fun env' h1 h2 => ⟨by simp only [Ex.Fits, h1, h2]; omega, rfl⟩)
    exact ⟨g, by rw [comp, hv]; simp [Ex.eval, e1, e2, eval]⟩
  | half a iha =>
    intro env hdt hR henv hf
    obtain ⟨g1, v1⟩ := iha t env hdt hR henv hf
    have ha := eval_lt (e := a) hf
    refine ⟨(Good.seq0 g1 ((Good.set ?_).of_eq rfl le_rfl)).mono ?_, ?_⟩
    · simp only [Ex.Fits, v1]; omega
    · simp only [Ex.size, cost, κ_split]; omega
    · simp [comp, exec_seq_fst, exec_set_fst, Ex.eval, v1, eval]
  | odd a iha =>
    intro env hdt hR henv hf
    obtain ⟨g1, v1⟩ := iha t env hdt hR henv hf
    have ha := eval_lt (e := a) hf
    refine ⟨(Good.seq0 g1 ((Good.set ?_).of_eq rfl le_rfl)).mono ?_, ?_⟩
    · simp only [Ex.Fits, v1]; omega
    · simp only [Ex.size, cost, κ_split]; omega
    · simp [comp, exec_seq_fst, exec_set_fst, Ex.eval, v1, eval]
  | mulB a b k iha ihb ihk => exact spec_mulB hB a b k iha ihb ihk t
  | shl a k iha ihk => exact spec_shl hB a k iha ihk t
  | shr a k iha ihk => exact spec_shr hB a k iha ihk t
  | xorM a b k iha ihb ihk => exact spec_xorM hB a b k iha ihb ihk t

/-! ## Well-formedness and depth -/

lemma depth_comp (e : Xp) : ∀ t, (comp R d A t e).depth ≤ 3 := by
  induction e with
  | var i => intro t; simp only [comp]; split_ifs <;> simp [Stm.depth, Ex.depth]
  | const c => intro t; simp [comp, Stm.depth, Ex.depth]
  | add a b iha ihb =>
    intro t; have := iha t; have := ihb (t + 1)
    simp only [comp, Stm.depth, Ex.depth]; omega
  | lt a b iha ihb =>
    intro t; have := iha t; have := ihb (t + 1)
    simp only [comp, Stm.depth, Ex.depth]; omega
  | half a iha => intro t; have := iha t; simp only [comp, Stm.depth, Ex.depth]; omega
  | odd a iha => intro t; have := iha t; simp only [comp, Stm.depth, Ex.depth]; omega
  | mulB a b k iha ihb ihk =>
    intro t; have := iha (t + 1); have := ihb (t + 2); have := ihk (t + 3)
    simp only [comp, mulBody, Stm.depth, Ex.depth]; omega
  | shl a k iha ihk =>
    intro t; have := iha t; have := ihk (t + 1)
    simp only [comp, Stm.shlS, Stm.depth, Ex.depth]; omega
  | shr a k iha ihk =>
    intro t; have := iha t; have := ihk (t + 1)
    simp only [comp, Stm.shrS, Stm.depth, Ex.depth]; omega
  | xorM a b k iha ihb ihk =>
    intro t; have := iha (t + 1); have := ihb (t + 2); have := ihk (t + 3)
    simp only [comp, Stm.xorS, Stm.xorBody, Stm.depth, Ex.depth]; omega

lemma noX_comp (e : Xp) : ∀ t, (comp R d A t e).noX = true := by
  induction e with
  | var i => intro t; simp only [comp]; split_ifs <;> rfl
  | const c => intro t; rfl
  | add a b iha ihb => intro t; simp [comp, Stm.noX, iha, ihb]
  | lt a b iha ihb => intro t; simp [comp, Stm.noX, iha, ihb]
  | half a iha => intro t; simp [comp, Stm.noX, iha]
  | odd a iha => intro t; simp [comp, Stm.noX, iha]
  | mulB a b k iha ihb ihk => intro t; simp [comp, Stm.noX, iha, ihb, ihk, mulBody]
  | shl a k iha ihk => intro t; simp [comp, Stm.noX, iha, ihk, Stm.shlS]
  | shr a k iha ihk => intro t; simp [comp, Stm.noX, iha, ihk, Stm.shrS]
  | xorM a b k iha ihb ihk => intro t; simp [comp, Stm.noX, iha, ihb, ihk, Stm.xorS, Stm.xorBody]

lemma wf_comp (e : Xp) : ∀ t, t + e.need ≤ R → (comp R d A t e).WF := by
  induction e with
  | var i => intro t _; simp only [comp]; split_ifs <;> trivial
  | const c => intro t _; trivial
  | add a b iha ihb =>
    intro t h; simp only [need] at h
    exact ⟨iha t (by omega), ihb (t + 1) (by omega), trivial⟩
  | lt a b iha ihb =>
    intro t h; simp only [need] at h
    exact ⟨iha t (by omega), ihb (t + 1) (by omega), trivial⟩
  | half a iha => intro t h; exact ⟨iha t h, trivial⟩
  | odd a iha => intro t h; exact ⟨iha t h, trivial⟩
  | mulB a b k iha ihb ihk =>
    intro t h; simp only [need] at h
    have n0 : rg R (t + 4) ≠ rg R t := rg_ne (by omega) (by omega)
    have n1 : rg R (t + 4) ≠ rg R (t + 1) := rg_ne (by omega) (by omega)
    have n2 : rg R (t + 4) ≠ rg R (t + 2) := rg_ne (by omega) (by omega)
    have n3 : rg R (t + 4) ≠ rg R (t + 3) := rg_ne (by omega) (by omega)
    have m0 : rg R (t + 3) ≠ rg R t := rg_ne (by omega) (by omega)
    have m1 : rg R (t + 3) ≠ rg R (t + 1) := rg_ne (by omega) (by omega)
    have m2 : rg R (t + 3) ≠ rg R (t + 2) := rg_ne (by omega) (by omega)
    refine ⟨iha _ (by omega), ihb _ (by omega), ihk _ (by omega), trivial, n3, ?_, ?_,
      ⟨trivial, trivial⟩, trivial, trivial⟩
    · simp [mulBody, Stm.wr, n0, n1, n2]
    · simp [mulBody, Stm.wr, m0, m1, m2]
  | shl a k iha ihk =>
    intro t h; simp only [need] at h
    have n0 : rg R (t + 2) ≠ rg R t := rg_ne (by omega) (by omega)
    have n1 : rg R (t + 2) ≠ rg R (t + 1) := rg_ne (by omega) (by omega)
    have m0 : rg R (t + 1) ≠ rg R t := rg_ne (by omega) (by omega)
    exact ⟨iha _ (by omega), ihk _ (by omega), n1, by simp [Stm.wr, n0],
      by simp [Stm.wr, m0], trivial⟩
  | shr a k iha ihk =>
    intro t h; simp only [need] at h
    have n0 : rg R (t + 2) ≠ rg R t := rg_ne (by omega) (by omega)
    have n1 : rg R (t + 2) ≠ rg R (t + 1) := rg_ne (by omega) (by omega)
    have m0 : rg R (t + 1) ≠ rg R t := rg_ne (by omega) (by omega)
    exact ⟨iha _ (by omega), ihk _ (by omega), n1, by simp [Stm.wr, n0],
      by simp [Stm.wr, m0], trivial⟩
  | xorM a b k iha ihb ihk =>
    intro t h; simp only [need] at h
    have hn := regs6 (R := R) (t := t) (by omega)
    refine ⟨iha _ (by omega), ihb _ (by omega), ihk _ (by omega), trivial, trivial,
      Ne.symm hn.n35, ?_, ?_, ⟨⟨trivial, trivial⟩, trivial, trivial, trivial⟩⟩
    · simp [Stm.xorBody, Stm.wr, Ne.symm hn.n15, Ne.symm hn.n25, Ne.symm hn.n05, Ne.symm hn.n45]
    · simp [Stm.xorBody, Stm.wr, hn.n31, hn.n32, hn.n30, hn.n34]

end Xp

end Lax119563Proofs.Reduction

end Reduction_XSpec
