import Mathlib.Data.Nat.Bits
import Lax119563Proofs.Machines.Numbers

/-!
# Little-endian digit lists

Facts about `Nat.bits` used by the arithmetic routines of register machines on stacks
(`Reduction.HStack`): canonical digit lists, ripple-carry addition (`addL`), and comparison
by a scan from the least significant digit (`cmpL`).
-/

namespace Lax119563Proofs.Reduction

open Machines (valBits valBits_bits bits_injective)

/-- A digit list without trailing (most significant) zeros. -/
def Canon : List Bool → Prop
  | [] => True
  | b :: l => (l = [] → b = true) ∧ Canon l

lemma valBits_ne_zero : ∀ {l : List Bool}, Canon l → l ≠ [] → valBits l ≠ 0
  | [], _, h => absurd rfl h
  | b :: l, ⟨h1, h2⟩, _ => by
    by_cases hl : l = []
    · subst hl; simp [h1 rfl, valBits]
    · have := valBits_ne_zero h2 hl
      simp only [valBits]; omega

lemma bits_valBits : ∀ {l : List Bool}, Canon l → Nat.bits (valBits l) = l
  | [], _ => by simp [valBits]
  | b :: l, ⟨h1, h2⟩ => by
    by_cases hl : l = []
    · subst hl; rw [h1 rfl]; simp [valBits]
    · have hv := valBits_ne_zero h2 hl
      have ih := bits_valBits h2
      cases b
      · simp only [valBits, Bool.toNat_false, zero_add]
        rw [Nat.bit0_bits _ hv, ih]
      · simp only [valBits, Bool.toNat_true]
        rw [add_comm, Nat.bit1_bits, ih]

lemma canon_bits (n : ℕ) : Canon (Nat.bits n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [Canon]
      · rw [Nat.bit0_bits m (by omega)]
        refine ⟨fun h => ?_, ih m (by omega)⟩
        exact absurd h (by rw [Machines.bits_eq_nil_iff]; omega)
    · rw [Nat.bit1_bits]
      exact ⟨fun _ => rfl, ih m (by omega)⟩

lemma bits_eq_of_canon {l : List Bool} (h : Canon l) {n : ℕ} (hv : valBits l = n) :
    Nat.bits n = l := hv ▸ bits_valBits h

lemma length_bits_le {n w : ℕ} (h : n < 2 ^ w) : (Nat.bits n).length ≤ w := by
  induction w generalizing n with
  | zero =>
    have : n = 0 := by simpa using h
    subst this; simp
  | succ w ih =>
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp
      · rw [Nat.bit0_bits m (by omega)]
        simp only [List.length_cons, add_le_add_iff_right]
        exact ih (by rw [pow_succ] at h; omega)
    · rw [Nat.bit1_bits]
      simp only [List.length_cons, add_le_add_iff_right]
      exact ih (by rw [pow_succ] at h; omega)

/-! ## Addition -/

/-- The carry of a full adder. -/
def maj (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

/-- Ripple-carry addition of digit lists with carry `c`. -/
def addL : List Bool → List Bool → Bool → List Bool
  | [], [], c => if c then [true] else []
  | a :: l, [], c => Bool.xor a c :: addL l [] (a && c)
  | [], b :: l', c => Bool.xor b c :: addL [] l' (b && c)
  | a :: l, b :: l', c => Bool.xor (Bool.xor a b) c :: addL l l' (maj a b c)

lemma valBits_addL : ∀ (l l' : List Bool) (c : Bool),
    valBits (addL l l' c) = valBits l + valBits l' + c.toNat
  | [], [], c => by cases c <;> simp [addL, valBits]
  | a :: l, [], c => by
    rw [addL]; simp only [valBits]; rw [valBits_addL l [] _]; cases a <;> cases c <;> simp [valBits] <;> omega
  | [], b :: l, c => by
    rw [addL]; simp only [valBits]; rw [valBits_addL [] l _]; cases b <;> cases c <;> simp [valBits] <;> omega
  | a :: l, b :: l', c => by
    rw [addL]; simp only [valBits]; rw [valBits_addL l l' _]
    cases a <;> cases b <;> cases c <;> simp [maj] <;> omega

lemma addL_eq_nil {l l' : List Bool} {c : Bool} (h : addL l l' c = []) :
    l = [] ∧ l' = [] ∧ c = false := by
  cases l <;> cases l' <;> cases c <;> simp_all [addL]

lemma canon_addL : ∀ (l l' : List Bool) (c : Bool), Canon l → Canon l' → Canon (addL l l' c)
  | [], [], c, _, _ => by cases c <;> simp [addL, Canon]
  | a :: l, [], c, hl, hl' => by
    rw [addL]
    refine ⟨fun he => ?_, canon_addL l [] _ hl.2 hl'⟩
    obtain ⟨rfl, -, h⟩ := addL_eq_nil he
    have := hl.1 rfl; subst this; cases c <;> simp_all
  | [], b :: l, c, hl, hl' => by
    rw [addL]
    refine ⟨fun he => ?_, canon_addL [] l _ hl hl'.2⟩
    obtain ⟨-, rfl, h⟩ := addL_eq_nil he
    have := hl'.1 rfl; subst this; cases c <;> simp_all
  | a :: l, b :: l', c, hl, hl' => by
    rw [addL]
    refine ⟨fun he => ?_, canon_addL l l' _ hl.2 hl'.2⟩
    obtain ⟨rfl, rfl, h⟩ := addL_eq_nil he
    have := hl.1 rfl; have := hl'.1 rfl; subst_vars; cases c <;> simp_all [maj]

/-- `Nat.bits` of a sum. -/
lemma bits_add (a b : ℕ) : Nat.bits (a + b) = addL (Nat.bits a) (Nat.bits b) false := by
  refine bits_eq_of_canon (canon_addL _ _ _ (canon_bits a) (canon_bits b)) ?_
  rw [valBits_addL, valBits_bits, valBits_bits]; simp

/-! ## Comparison -/

/-- Comparison of digit lists by a scan from the least significant digit; `st` is the result
for the digits seen so far. -/
def cmpL : List Bool → List Bool → Ordering → Ordering
  | [], [], st => st
  | a :: l, [], st => cmpL l [] ((compare a false).then st)
  | [], b :: l', st => cmpL [] l' ((compare false b).then st)
  | a :: l, b :: l', st => cmpL l l' ((compare a b).then st)

lemma compare_bit_add (a b : Bool) (x y : ℕ) :
    compare (a.toNat + 2 * x) (b.toNat + 2 * y) = (compare x y).then (compare a b) := by
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · rw [compare_lt_iff_lt.mpr hxy,
      compare_lt_iff_lt.mpr (by cases a <;> cases b <;> simp <;> omega)]
    rfl
  · cases a <;> cases b <;> simp [compare, compareOfLessAndEq]
  · rw [compare_gt_iff_gt.mpr hxy,
      compare_gt_iff_gt.mpr (by cases a <;> cases b <;> simp <;> omega)]
    rfl

lemma cmpL_spec : ∀ (l l' : List Bool) (st : Ordering),
    cmpL l l' st = (compare (valBits l) (valBits l')).then st
  | [], [], st => by simp [cmpL, valBits]
  | a :: l, [], st => by
    rw [cmpL, cmpL_spec l [] _, ← Ordering.then_assoc]
    have := compare_bit_add a false (valBits l) 0
    simp only [valBits, Bool.toNat_false, mul_zero, add_zero] at this ⊢
    rw [this]
  | [], b :: l, st => by
    rw [cmpL, cmpL_spec [] l _, ← Ordering.then_assoc]
    have := compare_bit_add false b 0 (valBits l)
    simp only [valBits, Bool.toNat_false, mul_zero, zero_add] at this ⊢
    rw [this]
  | a :: l, b :: l', st => by
    rw [cmpL, cmpL_spec l l' _, ← Ordering.then_assoc]; simp only [valBits]; rw [compare_bit_add]

/-- The value read from the remaining input: `0` at its end, else the next bit plus one. -/
def rdVal : List Bool → ℕ
  | [] => 0
  | b :: _ => b.toNat + 1

end Lax119563Proofs.Reduction
