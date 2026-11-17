import Lax119563Proofs.Reduction.CostGn

/-!
# Quasi-linear machines from generators

`Gn.computesWithin_quasiLinear`: a generator with `HasCost [] g 1 d` (cost
`O(2^ℓ (ℓ+1)^(d+1))` at every scale `ℓ` with `|x| ≤ 2^ℓ`, values below `2^(O(ℓ))`) gives a
deterministic machine computing `encodeNats (g.out x [])` within
`C · |x| · (log₂ |x|)^(d + 3)` steps for `|x| ≥ 2` (word size `w = O(log |x|)`; the
exponent `d + 3` accounts for the cost `κ w = O(w²)` of a unit and for the output length).
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

/-- **Quasi-linear machines from generators.** -/
theorem computesWithin_quasiLinear {g : Gn} {d R : ℕ} (hc : HasCost [] g 1 d)
    (hR : g.need ≤ R) (hwf : g.WFX) :
    ∃ C : ℕ, ∀ x : List Bool, 2 ≤ x.length →
      x.length ≤ (encodeNats (g.out x [])).length →
      ComputesWithin (machine R g) x (encodeNats (g.out x []))
        (C * x.length * Nat.log 2 x.length ^ (d + 3)) := by
  obtain ⟨K, hK⟩ := hc 0
  set A := 3 * (K + 5) with hA
  refine ⟨2088 * A ^ 2 * (2 * K * 3 ^ (d + 1)) + 4, fun x hx hlen => ?_⟩
  set n := x.length with hn
  set L := Nat.log 2 n with hL
  have hL1 : 1 ≤ L := Nat.le_log_of_pow_le (by norm_num) (by simpa using hx)
  have hn2 : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h2L : 2 ^ L ≤ n := Nat.pow_log_le_self 2 (by omega)
  obtain ⟨hF, hC⟩ := hK (L + 1) x [] hn2.le List.Forall₂.nil
  set w := (K + 1) * (L + 1 + 1) + 1 with hw
  have hF' : g.Fits x (2 ^ ((K + 1) * (L + 1 + 1))) [] := fits_up (by omega) hF
  have hB : 2 * 2 ^ ((K + 1) * (L + 1 + 1)) ≤ 2 ^ w := by rw [hw, pow_succ]; omega
  have hw2 : 2 ≤ w := by rw [hw]; nlinarith
  have H := computesWithin hw2 hB hR hwf hF' hlen
  refine ComputesWithin.mono H ?_
  -- bounds
  set c := g.cost x [] with hc'
  have hout : (g.out x []).length ≤ c := length_out_le_cost g []
  have henc : (encodeNats (g.out x [])).length ≤ c * (2 * w + 1) := by
    refine le_trans (length_encodeNats_le (w := w) fun v hv => ?_) (Nat.mul_le_mul_right _ hout)
    exact lt_of_lt_of_le (lt_of_mem_out g hF' v hv) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hw3 : w + 3 ≤ A * L := by rw [hw, hA]; nlinarith
  have hκ : κ w ≤ 2048 * (A * L) ^ 2 := by
    have : κ w ≤ 2048 * (w + 3) ^ 2 := by
      simp only [κ, Ex.nodeCost, unitCost]; nlinarith
    exact le_trans this (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw3 2))
  have hA1 : 1 ≤ A := by rw [hA]; omega
  have hAL : 1 ≤ A * L := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h2w : 20 * (2 * w + 1) ≤ 40 * (A * L) ^ 2 := by nlinarith
  have hcost : c ≤ 2 * K * 3 ^ (d + 1) * (n * L ^ (d + 1)) := by
    refine le_trans hC ?_
    simp only [Ty.bnd, one_mul]
    have e1 : 2 ^ (L + 1) ≤ 2 * n := by rw [pow_succ]; omega
    have e2 : (L + 1 + 1) ^ (d + 1) ≤ (3 * L) ^ (d + 1) := Nat.pow_le_pow_left (by omega) _
    rw [mul_pow] at e2
    calc K * 2 ^ (L + 1) * (L + 1 + 1) ^ (d + 1) ≤ K * (2 * n) * (3 ^ (d + 1) * L ^ (d + 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ e1) e2
      _ = _ := by ring
  have hT : κ w * c + 20 * (encodeNats (g.out x [])).length ≤
      2088 * A ^ 2 * (2 * K * 3 ^ (d + 1)) * (n * L ^ (d + 3)) := by
    have s1 : κ w * c + 20 * (encodeNats (g.out x [])).length ≤ (κ w + 20 * (2 * w + 1)) * c := by
      nlinarith
    have s2 : κ w + 20 * (2 * w + 1) ≤ 2088 * A ^ 2 * L ^ 2 := by
      have : (A * L) ^ 2 = A ^ 2 * L ^ 2 := mul_pow A L 2
      nlinarith
    calc κ w * c + 20 * (encodeNats (g.out x [])).length
        ≤ (2088 * A ^ 2 * L ^ 2) * (2 * K * 3 ^ (d + 1) * (n * L ^ (d + 1))) :=
          le_trans s1 (Nat.mul_le_mul s2 hcost)
      _ = _ := by ring
  have h4 : 4 ≤ 4 * (n * L ^ (d + 3)) := by
    have : 1 ≤ n * L ^ (d + 3) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  calc κ w * c + 20 * (encodeNats (g.out x [])).length + 4
      ≤ 2088 * A ^ 2 * (2 * K * 3 ^ (d + 1)) * (n * L ^ (d + 3)) + 4 * (n * L ^ (d + 3)) := by
        omega
    _ = _ := by ring

end Gn

end Lax119563Proofs.Reduction
