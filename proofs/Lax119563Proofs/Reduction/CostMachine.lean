import Lax119563Proofs.Reduction.CostGn

/-!
# Lengths of encodings

`length_encodeNat_le`, `length_encodeNats_le`: bounds on the length of the binary encoding of
numbers and lists of numbers.
-/

open Lax119563.BinaryEncodings Lax119563.DeterministicTime

namespace Lax119563Proofs.Reduction

open Ty

lemma length_encodeNat_le {v w : ℕ} (h : v < 2 ^ w) : (encodeNat v).length ≤ 2 * w + 1 := by
  simp only [encodeNat, List.length_append, List.length_flatMap, List.length_cons,
    List.length_nil]
  have : (Nat.bits v).length ≤ w := by rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr h
  have e : ((Nat.bits v).map fun _ => 2).sum = 2 * (Nat.bits v).length := by
    simp [Nat.mul_comm]
  simp only [zero_add, Nat.reduceAdd] at *
  rw [e]; omega

lemma length_encodeNats_le {l : List ℕ} {w : ℕ} (h : ∀ v ∈ l, v < 2 ^ w) :
    (encodeNats l).length ≤ l.length * (2 * w + 1) := by
  induction l with
  | nil => simp [encodeNats]
  | cons v l ih =>
    simp only [encodeNats, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    have h1 := length_encodeNat_le (h v (by simp))
    have h2 := ih fun u hu => h u (by simp [hu])
    nlinarith

namespace Gn

end Gn

end Lax119563Proofs.Reduction
