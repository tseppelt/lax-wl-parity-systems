import Lax119563Proofs.Compiler.Bound

/-!
# Word size and cost conversion for the compiler program

With `L = log₂(H + S + 2)` the program runs with word size `w = 8 (L + 1)`:
* `two_pow_word`: `2^14 (H + S + 2) ≤ 2^w`;
* `locBase_le`: `locBase I ≤ 16 S` (for `k ≥ 2`), so `16 (H + locBase + 1) ≤ 2^w`
  (`word_hS`), the hypothesis of `p2_good` (and, a fortiori, of `p0`, `p1`, `p1r`, `p3`);
* `cost_conv`: `K (H + 1)(log₂(H + 1) + 1) · nodeCost w ≤ 7744 K (H + S + 1)(L + 1)^3`.
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

/-- The word size of the compiler program. -/
def wordOf (H S : ℕ) : ℕ := 8 * (Nat.log 2 (H + S + 2) + 1)

lemma two_le_wordOf (H S : ℕ) : 2 ≤ wordOf H S := by unfold wordOf; omega

/-- `2^14 (H + S + 2) ≤ 2^w`. -/
lemma two_pow_word (H S : ℕ) : 16384 * (H + S + 2) ≤ 2 ^ wordOf H S := by
  have hL := one_le_log H S
  have hN := lt_pow_log (H + S + 2)
  set L := Nat.log 2 (H + S + 2)
  have e : 8 * (L + 1) = (L + 1) + (14 + 7 * (L - 1)) := by omega
  have h14 : (2 : ℕ) ^ 14 ≤ 2 ^ (14 + 7 * (L - 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold wordOf
  rw [e, pow_add]
  have : (16384 : ℕ) = 2 ^ 14 := by norm_num
  rw [this, mul_comm]
  exact Nat.mul_le_mul hN.le h14

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The schema section is part of the vertex order. -/
lemma locBase_le_length : locBase I ≤ (ordL I).length := by
  rw [length_ordL]
  have h1 : (clsSizes I).sum = sizeOf' (ordCls I) := rfl
  rw [h1, ordCls, sizeOf'_append, sizeOf'_flatMap]
  have h2 : ((List.finRange I.schemas.length).map
      fun e => sizeOf' (hubsCls I e ++ nonhubsCls I e)) =
      (List.finRange I.schemas.length).map (schSize I) := rfl
  rw [h2]
  exact Nat.le_add_right _ _

lemma locBase_le (hk : 2 ≤ k) : locBase I ≤ 16 * matrixSize I :=
  (locBase_le_length I).trans (length_ordL_le I hk)

/-- **The word-size hypothesis** of the passes `P0`–`P3`. -/
lemma word_hS (hk : 2 ≤ k) :
    16 * ((encodeSystem I).length + locBase I + 1) ≤
      2 ^ wordOf (encodeSystem I).length (matrixSize I) := by
  have h1 := locBase_le I hk
  have h2 := two_pow_word (encodeSystem I).length (matrixSize I)
  omega

/-- **Cost conversion**: `nodeCost_le_sq` with `a = 8`. -/
lemma cost_conv (K H S : ℕ) :
    K * (H + 1) * (Nat.log 2 (H + 1) + 1) * Ex.nodeCost (wordOf H S) ≤
      7744 * K * (H + S + 1) * (Nat.log 2 (H + S + 2) + 1) ^ 3 := by
  have hn := nodeCost_le_sq (a := 8) (L := Nat.log 2 (H + S + 2)) (w := wordOf H S) le_rfl
  have hl : Nat.log 2 (H + 1) ≤ Nat.log 2 (H + S + 2) := Nat.log_mono_right (by omega)
  set L := Nat.log 2 (H + S + 2)
  set l := Nat.log 2 (H + 1)
  set N := Ex.nodeCost (wordOf H S)
  have e1 : K * (H + 1) * (l + 1) ≤ K * (H + S + 1) * (L + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  calc K * (H + 1) * (l + 1) * N ≤ K * (H + S + 1) * (L + 1) * (64 * (8 + 3) ^ 2 * (L + 1) ^ 2) :=
        Nat.mul_le_mul e1 hn
    _ = 7744 * K * (H + S + 1) * (L + 1) ^ 3 := by ring

end Lax119563Proofs.Compiler
