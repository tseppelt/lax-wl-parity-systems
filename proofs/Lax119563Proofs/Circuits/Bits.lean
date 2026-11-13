import Mathlib

/-!
# Bit fields of natural numbers

Addresses are natural numbers. A *field* of an address is a block of consecutive bits; the
programs only test fields against constants and replace fields by constants (via an XOR with
a constant mask).
-/

namespace Lax119563Proofs.Circuits

/-- The field of `m` bits of `A` starting at bit `k`, as a number `< 2 ^ m`. -/
def field (A k m : ℕ) : ℕ := A / 2 ^ k % 2 ^ m

/-- Replace the field of `m` bits of `A` starting at bit `k` by `v` (for `v < 2 ^ m`). -/
def setBits (A k m v : ℕ) : ℕ := A ^^^ ((field A k m ^^^ v) <<< k)

lemma testBit_field (A k m t : ℕ) :
    (field A k m).testBit t = (decide (t < m) && A.testBit (t + k)) := by
  simp [field, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]

lemma field_lt (A k m : ℕ) : field A k m < 2 ^ m := Nat.mod_lt _ (by positivity)

/-- A field equals `q` iff the corresponding bits agree. -/
lemma field_eq_iff {A k m q : ℕ} (hq : q < 2 ^ m) :
    field A k m = q ↔ ∀ t < m, A.testBit (t + k) = q.testBit t := by
  constructor
  · rintro rfl t ht
    simp [testBit_field, ht]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro t
    rw [testBit_field]
    by_cases ht : t < m
    · simp [ht, h t ht]
    · have : q.testBit t = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num)
          (not_lt.mp ht)))
      simp [ht, this]

lemma testBit_setBits {A k m v : ℕ} (hv : v < 2 ^ m) (i : ℕ) :
    (setBits A k m v).testBit i =
      if k ≤ i ∧ i < k + m then v.testBit (i - k) else A.testBit i := by
  have hv' : ∀ t, m ≤ t → v.testBit t = false := fun t ht =>
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) ht))
  simp only [setBits, Nat.testBit_xor, Nat.testBit_shiftLeft, testBit_field]
  by_cases hk : k ≤ i
  · by_cases hm : i < k + m
    · have h1 : i - k < m := by omega
      have h2 : i - k + k = i := by omega
      simp [hk, hm, h1, h2]
    · have h1 : ¬ i - k < m := by omega
      simp [hk, hm, h1, hv' (i - k) (by omega)]
  · simp [hk]

lemma setBits_div {A k m v : ℕ} (hv : v < 2 ^ m) :
    setBits A k m v / 2 ^ (k + m) = A / 2 ^ (k + m) := by
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [Nat.testBit_div_two_pow, testBit_setBits hv]
  rw [if_neg (by omega)]

lemma setBits_mod {A k m v : ℕ} (hv : v < 2 ^ m) :
    setBits A k m v % 2 ^ k = A % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [Nat.testBit_mod_two_pow, testBit_setBits hv]
  by_cases ht : t < k
  · simp [ht, show ¬ (k ≤ t) by omega]
  · simp [ht]

lemma field_setBits {A k m v : ℕ} (hv : v < 2 ^ m) : field (setBits A k m v) k m = v := by
  apply (field_eq_iff hv).mpr
  intro t ht
  rw [testBit_setBits hv, if_pos (by omega)]
  congr 1
  omega

/-- The decomposition of a number into the part above a field, the field, and the part
below it. -/
lemma decomp (A k m : ℕ) :
    A = A / 2 ^ (k + m) * 2 ^ (k + m) + field A k m * 2 ^ k + A % 2 ^ k := by
  have h1 := Nat.div_add_mod A (2 ^ k)
  have h2 := Nat.div_add_mod (A / 2 ^ k) (2 ^ m)
  have h3 : A / 2 ^ k / 2 ^ m = A / 2 ^ (k + m) := by
    rw [Nat.div_div_eq_div_mul, ← pow_add]
  rw [h3] at h2
  have h4 : A = 2 ^ k * (2 ^ m * (A / 2 ^ (k + m)) + A / 2 ^ k % 2 ^ m) + A % 2 ^ k := by
    rw [h2]; exact h1.symm
  unfold field
  calc A = _ := h4
    _ = _ := by rw [pow_add]; ring

lemma mod_eq_field_add (A k m : ℕ) :
    A % 2 ^ (k + m) = field A k m * 2 ^ k + A % 2 ^ k := by
  have hlt : field A k m * 2 ^ k + A % 2 ^ k < 2 ^ (k + m) := by
    have h1 := field_lt A k m
    have h2 : A % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by positivity)
    have h3 : (field A k m + 1) * 2 ^ k ≤ 2 ^ m * 2 ^ k := Nat.mul_le_mul_right _ h1
    rw [pow_add]
    nlinarith
  conv_lhs => rw [decomp A k m]
  rw [add_assoc, Nat.mul_add_mod_of_lt hlt]

/-- A number is determined by the part above a field, the field, and the part below it. -/
lemma eq_of_decomp {A k m X v u : ℕ} (hv : v < 2 ^ m) (hu : u < 2 ^ k)
    (h : A = X * 2 ^ (k + m) + v * 2 ^ k + u) :
    A / 2 ^ (k + m) = X ∧ field A k m = v ∧ A % 2 ^ k = u := by
  have hlt : v * 2 ^ k + u < 2 ^ (k + m) := by
    rw [pow_add]
    have : v + 1 ≤ 2 ^ m := hv
    nlinarith
  have hA : A = u + 2 ^ k * (v + 2 ^ m * X) := by rw [h, pow_add]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [h, add_assoc, Nat.mul_comm X, Nat.mul_add_div (by positivity),
      Nat.div_eq_of_lt hlt, add_zero]
  · unfold field
    rw [hA, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hu, zero_add,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]
  · rw [hA, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu]

lemma setBits_eq {A k m v : ℕ} (hv : v < 2 ^ m) :
    setBits A k m v = A / 2 ^ (k + m) * 2 ^ (k + m) + v * 2 ^ k + A % 2 ^ k := by
  conv_lhs => rw [decomp (setBits A k m v) k m]
  rw [setBits_div hv, field_setBits hv, setBits_mod hv]

lemma setBits_lt {A k m v N : ℕ} (hv : v < 2 ^ m) (hA : A < 2 ^ N) (hkm : k + m ≤ N) :
    setBits A k m v < 2 ^ N := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_setBits hv, if_neg (by omega)]
  exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hA (Nat.pow_le_pow_right (by norm_num) hi))

end Lax119563Proofs.Circuits
