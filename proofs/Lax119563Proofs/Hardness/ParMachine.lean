import Lax119563Proofs.Hardness.PrefixProgram
import Lax119563Proofs.Hardness.SuffixMachine
import Lax119563Proofs.Hardness.Pipeline

/-!
# The machine putting the parameters in front of the input

For a constant `c₀` there is a deterministic machine that computes
`encodeNats [n + c₀, parS c₀ n] ++ x` from an input `x` of length `n` within
`K (n + c₀ + 4)^3` steps (`par_machine`): the machine of `parProg c₀` followed by
`withSuffix`.
-/

open Lax119563.BinaryEncodings Lax119563.DeterministicTime Lax119563Proofs.Reduction
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Hardness

open Compiler Compiler.CStm

lemma nodeCost_le (m : ℕ) (hm : 1 ≤ m) : Ex.nodeCost (4 * m) ≤ 64 * 49 * m ^ 2 := by
  unfold Ex.nodeCost unitCost
  have h1 : 4 * m + 3 ≤ 7 * m := by omega
  have h2 : 4 * m + 1 ≤ 7 * m := by omega
  calc (4 * m + 3) * (64 * (4 * m + 1)) ≤ (7 * m) * (64 * (7 * m)) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul_left _ h2)
    _ = 64 * 49 * m ^ 2 := by ring

lemma par_time_arith {m n c₀ s cost : ℕ} (hm : m = n + c₀ + 4) (hs : s ≤ n + c₀ + 2)
    (hcost : cost ≤ 100 * m * Ex.nodeCost (4 * m)) :
    16 * (cost + 20 * (n + ((2 * (n + c₀) + 1) + (2 * s + 1))) + 10 + n + 1) ≤
      16 * (100 * 64 * 49 + 200) * m ^ 3 := by
  have hm1 : 1 ≤ m := by omega
  have hN := nodeCost_le m hm1
  have h1 : cost ≤ 100 * 64 * 49 * m ^ 3 := by
    calc cost ≤ 100 * m * (64 * 49 * m ^ 2) := hcost.trans (Nat.mul_le_mul_left _ hN)
      _ = 100 * 64 * 49 * m ^ 3 := by ring
  have h2 : m ≤ m ^ 3 := by
    calc m = m ^ 1 := (pow_one m).symm
      _ ≤ m ^ 3 := Nat.pow_le_pow_right hm1 (by norm_num)
  have e : 16 * (100 * 64 * 49 + 200) * m ^ 3 = 16 * (100 * 64 * 49 * m ^ 3 + 200 * m ^ 3) := by
    ring
  omega

lemma parS_le (c₀ n : ℕ) : parS c₀ n ≤ n + c₀ + 2 := by
  obtain ⟨-, hs2⟩ := parS_spec c₀ n
  have := hs2 (parS c₀ n - 1) (by have := one_le_parS c₀ n; omega)
  have h1 := one_le_parA n
  have : parS c₀ n - 1 ≤ (parS c₀ n - 1) * parA n := Nat.le_mul_of_pos_right _ h1
  omega

lemma parS_mul_le (c₀ n : ℕ) : parS c₀ n * parA n ≤ n + c₀ + 2 + parA n := by
  obtain ⟨-, hs2⟩ := parS_spec c₀ n
  have := hs2 (parS c₀ n - 1) (by have := one_le_parS c₀ n; omega)
  have e : parS c₀ n * parA n = (parS c₀ n - 1) * parA n + parA n := by
    obtain ⟨k, hk⟩ : ∃ k, parS c₀ n = k + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (one_le_parS c₀ n)).symm⟩
    rw [hk]; simp; ring
  omega

lemma two_le_parS {c₀ : ℕ} (hc : 1 ≤ c₀) (n : ℕ) : 2 ≤ parS c₀ n := by
  obtain ⟨hs1, -⟩ := parS_spec c₀ n
  have ha := parA_le n
  by_contra hlt
  have : parS c₀ n * parA n ≤ 1 * parA n := Nat.mul_le_mul_right _ (by omega)
  omega

lemma packedWidth_par (c₀ n : ℕ) :
    Lax119563.PackedRepresentation.packedWidth n (n + c₀) (parS c₀ n) = parA n := by
  obtain ⟨hs1, -⟩ := parS_spec c₀ n
  have h1 := one_le_parS c₀ n
  unfold Lax119563.PackedRepresentation.packedWidth
  refine max_eq_left ?_
  show _ ≤ parA n
  apply Nat.le_of_lt_succ
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  have : (parA n).succ * parS c₀ n = parS c₀ n * parA n + parS c₀ n := by
    rw [Nat.succ_eq_add_one]; ring
  omega

/-- **The parameter machine.** -/
theorem par_machine (c₀ : ℕ) : ∃ P : Machine, Deterministic P ∧ ∃ K : ℕ, ∀ x : List Bool,
    ComputesWithin P x (encodeNats [x.length + c₀, parS c₀ x.length] ++ x)
      (K * (x.length + c₀ + 4) ^ 3) := by
  refine ⟨(withSuffix ((parProg c₀).machine 10)).compile, withSuffix_deterministic,
    16 * (100 * 64 * 49 + 200), fun x => ?_⟩
  set m := x.length + c₀ + 4 with hm
  have hw2 : 2 ≤ 4 * m := by omega
  have hw : 4 * (x.length + c₀ + 4) < 2 ^ (4 * m) := Nat.lt_two_pow_self
  obtain ⟨hf, he, hc⟩ := good_parProg (x := x) c₀ hw2 hw
  have h := CStm.computesWithin (D := 10) hw2 (parProg_depth c₀) hf
  rw [he] at h
  simp only [st6] at h
  have h2 := withSuffix_computesWithin h
  refine Main.Compose.computesWithin_mono' h2 ?_
  have hlen : (encodeNats [x.length + c₀, parS c₀ x.length]).length ≤
      (2 * (x.length + c₀) + 1) + (2 * parS c₀ x.length + 1) := by
    have e1 := length_encodeNat_le (x.length + c₀)
    have e2 := length_encodeNat_le (parS c₀ x.length)
    simp only [encodeNats, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.length_append]
    omega
  have hsle : parS c₀ x.length ≤ x.length + c₀ + 2 := by
    obtain ⟨-, hs2⟩ := parS_spec c₀ x.length
    have := hs2 (parS c₀ x.length - 1) (by have := one_le_parS c₀ x.length; omega)
    have h1 := one_le_parA x.length
    have : parS c₀ x.length - 1 ≤ (parS c₀ x.length - 1) * parA x.length :=
      Nat.le_mul_of_pos_right _ h1
    omega
  have ht := par_time_arith (cost := cost x (4 * m) (parProg c₀) (NSt.zero 6 0)) hm hsle hc
  have : 16 * (cost x (4 * m) (parProg c₀) (NSt.zero 6 0) +
      20 * (x.length + (encodeNats [x.length + c₀, parS c₀ x.length]).length) + 10 +
      x.length + 1) ≤ 16 * (cost x (4 * m) (parProg c₀) (NSt.zero 6 0) +
      20 * (x.length + ((2 * (x.length + c₀) + 1) + (2 * parS c₀ x.length + 1))) + 10 +
      x.length + 1) := by omega
  omega

end Lax119563Proofs.Hardness
