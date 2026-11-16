import Lax119563Proofs.Witness.Relay

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
