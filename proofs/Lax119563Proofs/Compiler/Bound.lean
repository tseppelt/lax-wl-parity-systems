import Lax119563Proofs.Compiler.OutLen
import Lax119563Proofs.Compiler.CMachine

/-!
# Arithmetic of the time bound

With `L = log₂(H + S + 2)` (so `L ≥ 1`):
* `nodeCost_le_sq`: for word size `w ≤ a (L + 1)`, `nodeCost w ≤ 64 (a + 3)² (L + 1)²`;
* `out_width`: `3 n < 2 ^ (L + 7)` for `n ≤ 16 S`, so the output has length
  `O((S + 1)(L + 1))` (`length_out_le_log`);
* `final_bound`: a time `K (H + S + 1)(L + 1)² + 20 (H + Y) + 10` with
  `Y ≤ K (S + 1)(L + 1)` is at most `(90 K + 30)(H + S) L²` (for `H ≥ 1`).
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

lemma nodeCost_le_sq {w a L : ℕ} (hw : w ≤ a * (L + 1)) :
    Ex.nodeCost w ≤ 64 * (a + 3) ^ 2 * (L + 1) ^ 2 := by
  have h1 : w + 3 ≤ (a + 3) * (L + 1) := by nlinarith
  have h2 : w + 1 ≤ (a + 3) * (L + 1) := by omega
  unfold Ex.nodeCost unitCost
  calc (w + 3) * (64 * (w + 1)) = 64 * ((w + 3) * (w + 1)) := by ring
    _ ≤ 64 * (((a + 3) * (L + 1)) * ((a + 3) * (L + 1))) := by
        apply Nat.mul_le_mul_left; exact Nat.mul_le_mul h1 h2
    _ = 64 * (a + 3) ^ 2 * (L + 1) ^ 2 := by ring

lemma one_le_log (H S : ℕ) : 1 ≤ Nat.log 2 (H + S + 2) :=
  Nat.le_log_of_pow_le (by norm_num) (by omega)

lemma lt_pow_log (N : ℕ) : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N

/-- The width of the output numbers. -/
lemma out_width {H S n : ℕ} (hn : n ≤ 16 * S) :
    3 * n < 2 ^ (Nat.log 2 (H + S + 2) + 7) := by
  have h := lt_pow_log (H + S + 2)
  rw [pow_add] at h ⊢
  have : (2 : ℕ) ^ 7 = 2 ^ 6 * 2 := by norm_num
  rw [this]
  nlinarith

/-- The output length in terms of `S` and `L`. -/
theorem length_out_le_log {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ) (hk : 2 ≤ k) (H : ℕ) :
    (encodeNats (gDesc I 0 ++ gDesc I 1)).length ≤
      2 * (2 + 7 * (16 * sizeParameter I)) * (2 * (Nat.log 2 (H + sizeParameter I + 2) + 7) + 1) := by
  have hn := length_ordL_le I hk
  refine (length_out_le I (out_width (H := H) hn)).trans ?_
  exact Nat.mul_le_mul_right _ (by omega)

/-- **The final arithmetic.** -/
theorem final_bound {H S L T K Y : ℕ} (hH : 1 ≤ H) (hL : 1 ≤ L)
    (hT : T ≤ K * (H + S + 1) * (L + 1) ^ 2 + 20 * (H + Y) + 10)
    (hY : Y ≤ K * (S + 1) * (L + 1)) :
    T ≤ (90 * K + 30) * (H + S) * L ^ 2 := by
  have e1 : H + S + 1 ≤ 2 * (H + S) := by omega
  have e2 : L + 1 ≤ 2 * L := by omega
  have e3 : S + 1 ≤ 2 * (H + S) := by omega
  have hL2 : 1 ≤ L ^ 2 := Nat.one_le_pow _ _ hL
  have hLL : L ≤ L ^ 2 := by nlinarith
  have hHS : 1 ≤ H + S := by omega
  have t1 : K * (H + S + 1) * (L + 1) ^ 2 ≤ 8 * K * (H + S) * L ^ 2 := by
    have : (L + 1) ^ 2 ≤ 4 * L ^ 2 := by nlinarith
    calc K * (H + S + 1) * (L + 1) ^ 2 ≤ K * (2 * (H + S)) * (4 * L ^ 2) := by
          apply Nat.mul_le_mul (Nat.mul_le_mul_left _ e1) this
      _ = 8 * K * (H + S) * L ^ 2 := by ring
  have t2 : Y ≤ 4 * K * (H + S) * L ^ 2 := by
    calc Y ≤ K * (2 * (H + S)) * (2 * L) := hY.trans
          (Nat.mul_le_mul (Nat.mul_le_mul_left _ e3) e2)
      _ = 4 * K * (H + S) * L := by ring
      _ ≤ 4 * K * (H + S) * L ^ 2 := Nat.mul_le_mul_left _ hLL
  have t3 : H ≤ (H + S) * L ^ 2 := by nlinarith
  have t4 : 10 ≤ 10 * ((H + S) * L ^ 2) := by nlinarith
  calc T ≤ 8 * K * (H + S) * L ^ 2 + 20 * ((H + S) * L ^ 2 + 4 * K * (H + S) * L ^ 2) +
        10 * ((H + S) * L ^ 2) := by omega
    _ = (88 * K + 30) * (H + S) * L ^ 2 := by ring
    _ ≤ (90 * K + 30) * (H + S) * L ^ 2 := by
        apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; omega

/-- `H ≥ 1`: the encoding of a system is nonempty. -/
lemma one_le_bitLength {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ) : 1 ≤ bitLength I := by
  unfold bitLength encodeSystem systemDescription encodeNats
  simp [encodeNat]; omega

/-- **The concept from a structured program.** A statement `c` that, for word size
`w = a (L + 1)`, fits, emits `gDesc I 0 ++ gDesc I 1` from the zero state on the input
`encodeSystem I`, and costs at most `K (H + S + 1)(L + 1)²` yields the machine of
`matrix_compiler_of_machine`. -/
theorem machine_of_program {R Q D : ℕ} (c : CStm R Q) (hd : c.depth ≤ D) (a K : ℕ) (ha : 2 ≤ a)
    (hc : ∀ k : ℕ, 3 ≤ k → ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ I : ImplicitParitySystem k ℓ,
      let w := a * (Nat.log 2 (bitLength I + sizeParameter I + 2) + 1)
      c.Fits (encodeSystem I) w (NSt.zero R Q) ∧
      (c.exec (encodeSystem I) (NSt.zero R Q)).out = gDesc I 0 ++ gDesc I 1 ∧
      c.cost (encodeSystem I) w (NSt.zero R Q) ≤
        K * (bitLength I + sizeParameter I + 1) *
          (Nat.log 2 (bitLength I + sizeParameter I + 2) + 1) ^ 2) :
    ∃ M : Lax489179.TuringMachine.Machine, Lax489179.TuringMachine.Deterministic M ∧
      ∃ C c : ℕ, ∀ k : ℕ, 3 ≤ k → ∀ ℓ : ℕ, 1 ≤ ℓ →
      ∀ I : ImplicitParitySystem k ℓ,
        Lax119563.DeterministicTime.ComputesWithin M (encodeSystem I)
          (encodeNats (gDesc I 0 ++ gDesc I 1))
          (C * (bitLength I + sizeParameter I) *
            Nat.log 2 (bitLength I + sizeParameter I + 2) ^ c) := by
  refine ⟨c.machine D, CStm.machine_deterministic D c, 90 * (K + 3400) + 30, 2,
    fun k hk ℓ hℓ I => ?_⟩
  obtain ⟨hf, ho, hco⟩ := hc k hk ℓ hℓ I
  set L := Nat.log 2 (bitLength I + sizeParameter I + 2)
  have hw : 2 ≤ a * (L + 1) := by nlinarith
  have h := CStm.computesWithin (D := D) hw hd hf
  rw [ho] at h
  refine Lax119563Proofs.Reduction.ComputesWithin.mono h ?_
  have hY := length_out_le_log I (by omega) (bitLength I)
  have hL := one_le_log (bitLength I) (sizeParameter I)
  have hH := one_le_bitLength I
  have hY' : (encodeNats (gDesc I 0 ++ gDesc I 1)).length ≤
      (K + 3400) * (sizeParameter I + 1) * (L + 1) := by
    refine hY.trans ?_
    have : 2 * (L + 7) + 1 ≤ 15 * (L + 1) := by omega
    calc 2 * (2 + 7 * (16 * sizeParameter I)) * (2 * (L + 7) + 1)
        ≤ 2 * (2 + 7 * (16 * sizeParameter I)) * (15 * (L + 1)) := Nat.mul_le_mul_left _ this
      _ ≤ (K + 3400) * (sizeParameter I + 1) * (L + 1) := by
          have hS : 2 * (2 + 7 * (16 * sizeParameter I)) * 15 ≤ (K + 3400) * (sizeParameter I + 1) := by nlinarith
          calc _ = 2 * (2 + 7 * (16 * sizeParameter I)) * 15 * (L + 1) := by ring
            _ ≤ _ := Nat.mul_le_mul_right _ hS
  have hco' : c.cost (encodeSystem I) (a * (L + 1)) (NSt.zero R Q) ≤
      (K + 3400) * (bitLength I + sizeParameter I + 1) * (L + 1) ^ 2 :=
    hco.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))
  exact final_bound (K := K + 3400) hH hL (by unfold bitLength at *; omega) hY'

end Lax119563Proofs.Compiler
