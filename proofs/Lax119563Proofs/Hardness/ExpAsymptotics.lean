import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Estimates for the exponential lower bound

* `pow_le_two_rpow_quarter`: `m^d ≤ (4d + 4)^d 2^{m/4}`;
* `eps_mul_rpow_le`: if `N ≤ B m^5`, then `ε N^{1/5} ≤ m / 4` for
  `ε = 1 / (4 (B + 1)^{1/5})`;
* `two_rpow_quarter_add_le`: `2^{(n + c)/4} ≤ 2^c 2^{n/4}`.
-/

namespace Lax119563Proofs.Hardness

/-- A polynomial is dominated by `2^{m/4}`. -/
theorem pow_le_two_rpow_quarter (m d : ℕ) :
    (m : ℝ) ^ d ≤ ((4 * d + 4 : ℕ) : ℝ) ^ d * (2 : ℝ) ^ ((m : ℝ) / 4) := by
  set D := d + 1 with hD
  set k := m / (4 * D) with hk
  have h2D : 0 < 4 * D := by omega
  have hm : m ≤ 4 * D * 2 ^ k := by
    have h1 : m < 4 * D * (k + 1) := by
      have := Nat.lt_mul_div_succ m h2D
      rw [hk]; linarith
    have h2 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
    calc m ≤ 4 * D * (k + 1) := h1.le
      _ ≤ 4 * D * 2 ^ k := Nat.mul_le_mul_left _ h2
  have hmd : m ^ d ≤ (4 * D) ^ d * 2 ^ (k * d) := by
    calc m ^ d ≤ (4 * D * 2 ^ k) ^ d := Nat.pow_le_pow_left hm d
      _ = (4 * D) ^ d * 2 ^ (k * d) := by rw [mul_pow, ← pow_mul]
  have hkd : ((k * d : ℕ) : ℝ) ≤ (m : ℝ) / 4 := by
    have : 4 * (k * d) ≤ m := by
      have h1 : k * (4 * D) ≤ m := Nat.div_mul_le_self m (4 * D)
      have h2 : k * d ≤ k * D := Nat.mul_le_mul_left _ (by omega)
      have h3 : k * (4 * D) = 4 * (k * D) := by ring
      omega
    rw [le_div_iff₀ (by norm_num)]
    exact_mod_cast (by omega : k * d * 4 ≤ m)
  have hpow : ((2 : ℝ) ^ (k * d : ℕ)) ≤ (2 : ℝ) ^ ((m : ℝ) / 4) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hkd
  have hcast : ((m ^ d : ℕ) : ℝ) ≤ (((4 * D) ^ d * 2 ^ (k * d) : ℕ) : ℝ) := by exact_mod_cast hmd
  push_cast at hcast
  have e : (4 * (D : ℝ)) = ((4 * d + 4 : ℕ) : ℝ) := by rw [hD]; push_cast; ring
  rw [e] at hcast
  calc (m : ℝ) ^ d ≤ ((4 * d + 4 : ℕ) : ℝ) ^ d * 2 ^ (k * d) := hcast
    _ ≤ ((4 * d + 4 : ℕ) : ℝ) ^ d * (2 : ℝ) ^ ((m : ℝ) / 4) := by gcongr

/-- The exponent estimate. -/
theorem eps_mul_rpow_le (B N m : ℕ) (h : N ≤ B * m ^ 5) :
    1 / (4 * ((B : ℝ) + 1) ^ ((1 : ℝ) / 5)) * (N : ℝ) ^ ((1 : ℝ) / 5) ≤ (m : ℝ) / 4 := by
  have hB : (0 : ℝ) < (B : ℝ) + 1 := by positivity
  have hBr : 0 < ((B : ℝ) + 1) ^ ((1 : ℝ) / 5) := Real.rpow_pos_of_pos hB _
  have hN : (N : ℝ) ≤ ((B : ℝ) + 1) * (m : ℝ) ^ 5 := by
    have : (N : ℝ) ≤ (B : ℝ) * (m : ℝ) ^ 5 := by exact_mod_cast h
    nlinarith [pow_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) 5]
  have h1 : (N : ℝ) ^ ((1 : ℝ) / 5) ≤ (((B : ℝ) + 1) * (m : ℝ) ^ 5) ^ ((1 : ℝ) / 5) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hN (by norm_num)
  have h2 : (((B : ℝ) + 1) * (m : ℝ) ^ 5) ^ ((1 : ℝ) / 5) =
      ((B : ℝ) + 1) ^ ((1 : ℝ) / 5) * (m : ℝ) := by
    rw [Real.mul_rpow hB.le (by positivity)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  rw [h2] at h1
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- Shifting the exponent. -/
theorem two_rpow_quarter_add_le (n c : ℕ) :
    (2 : ℝ) ^ (((n + c : ℕ) : ℝ) / 4) ≤ (2 ^ c : ℕ) * (2 : ℝ) ^ ((n : ℝ) / 4) := by
  have e : (((n + c : ℕ) : ℝ) / 4) = (n : ℝ) / 4 + (c : ℝ) / 4 := by push_cast; ring
  rw [e, Real.rpow_add (by norm_num), mul_comm]
  gcongr
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [(Nat.cast_nonneg c : (0 : ℝ) ≤ c)])

end Lax119563Proofs.Hardness
