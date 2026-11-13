import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Log

/-!
# The running-time estimate for the composed decider

Polylogarithmic factors are absorbed by an arbitrarily small polynomial factor, which yields
the bound `2 t₁ + C t₁^e + C + 3 = O(n^{e + δ})` for `t₁ = C' n (log n)^c`.
-/

namespace Lax119563Proofs.Main

/-- A real power of `log₂ n` is at most a constant times an arbitrarily small power of `n`. -/
theorem natLog_rpow_le (m δ : ℝ) (hm : 0 ≤ m) (hδ : 0 < δ) :
    ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n → ((Nat.log 2 n : ℕ) : ℝ) ^ m ≤ K * (n : ℝ) ^ δ := by
  rcases hm.eq_or_lt with rfl | hm
  · refine ⟨1, fun n hn => ?_⟩
    rw [Real.rpow_zero, one_mul]
    exact Real.one_le_rpow (by exact_mod_cast hn) hδ.le
  set η := δ / m with hη
  have hηpos : 0 < η := div_pos hδ hm
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(1 / (η * Real.log 2)) ^ m, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set L : ℕ := Nat.log 2 n
  have hL : (L : ℝ) * Real.log 2 ≤ Real.log n := by
    have h2 : ((2 ^ L : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have := Real.log_le_log (by positivity) h2
    simpa [Real.log_pow] using this
  have hlogn : Real.log n ≤ (n : ℝ) ^ η / η := Real.log_le_rpow_div hn0.le hηpos
  have hLle : (L : ℝ) ≤ 1 / (η * Real.log 2) * (n : ℝ) ^ η := by
    have h1 : (L : ℝ) ≤ Real.log n / Real.log 2 := (le_div_iff₀ hlog2).mpr hL
    calc (L : ℝ) ≤ Real.log n / Real.log 2 := h1
      _ ≤ ((n : ℝ) ^ η / η) / Real.log 2 := by gcongr
      _ = 1 / (η * Real.log 2) * (n : ℝ) ^ η := by field_simp
  calc ((L : ℝ)) ^ m ≤ (1 / (η * Real.log 2) * (n : ℝ) ^ η) ^ m :=
        Real.rpow_le_rpow (by positivity) hLle hm.le
    _ = (1 / (η * Real.log 2)) ^ m * (n : ℝ) ^ δ := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hn0.le, hη,
          div_mul_cancel₀ _ hm.ne']

/-- The total running time of reduction followed by the fast decider is `O(n^{e + δ})`. -/
theorem composed_time_estimate (CR c Cw : ℕ) (e δ : ℝ) (he : 1 ≤ e) (hδ : 0 < δ) :
    ∃ K : ℕ, ∀ n : ℕ, 1 ≤ n →
      2 * ((CR * n * Nat.log 2 n ^ c : ℕ) : ℝ) +
          (Cw * ((CR * n * Nat.log 2 n ^ c : ℕ) : ℝ) ^ e + Cw) + 3 ≤
        K * (n : ℝ) ^ (e + δ) + K := by
  obtain ⟨K₁, hK₁⟩ := natLog_rpow_le c δ (by positivity) hδ
  obtain ⟨K₂, hK₂⟩ := natLog_rpow_le (c * e) δ (by positivity) hδ
  set A : ℝ := 2 * CR * K₁ + Cw * (CR : ℝ) ^ e * K₂
  refine ⟨⌈A⌉₊ + Cw + 3, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set L : ℝ := ((Nat.log 2 n : ℕ) : ℝ)
  have hL0 : 0 ≤ L := Nat.cast_nonneg _
  have hcast : ((CR * n * Nat.log 2 n ^ c : ℕ) : ℝ) = CR * n * L ^ c := by push_cast; rfl
  rw [hcast]
  have hpow := Real.rpow_nonneg hn0.le (e + δ)
  -- the linear term
  have h1 : (CR : ℝ) * n * L ^ c ≤ CR * K₁ * (n : ℝ) ^ (e + δ) := by
    have hLc : L ^ c ≤ K₁ * (n : ℝ) ^ δ := by
      have := hK₁ n hn; rwa [Real.rpow_natCast] at this
    have hn_le : (n : ℝ) * (n : ℝ) ^ δ ≤ (n : ℝ) ^ (e + δ) := by
      rw [Real.rpow_add hn0]
      gcongr
      calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (n : ℝ) ^ e := Real.rpow_le_rpow_of_exponent_le hn1 he
    calc (CR : ℝ) * n * L ^ c ≤ CR * n * (K₁ * (n : ℝ) ^ δ) := by gcongr
      _ = CR * K₁ * (n * (n : ℝ) ^ δ) := by ring
      _ ≤ CR * K₁ * (n : ℝ) ^ (e + δ) := by
          have hK₁0 : 0 ≤ K₁ := by
            by_contra hneg
            rw [not_le] at hneg
            have := mul_neg_of_neg_of_pos hneg (Real.rpow_pos_of_pos hn0 δ)
            have := Real.rpow_nonneg hL0 (c : ℝ)
            linarith [hK₁ n hn]
          gcongr
  -- the power term
  have h2 : ((CR : ℝ) * n * L ^ c) ^ e ≤ (CR : ℝ) ^ e * K₂ * (n : ℝ) ^ (e + δ) := by
    have hLce : (L ^ c) ^ e = L ^ ((c : ℝ) * e) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0]
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hn0.le,
      hLce, Real.rpow_add hn0]
    have := hK₂ n hn
    have hcr := Real.rpow_nonneg (Nat.cast_nonneg CR) e
    have hne := Real.rpow_nonneg hn0.le e
    calc (CR : ℝ) ^ e * (n : ℝ) ^ e * L ^ ((c : ℝ) * e)
        ≤ (CR : ℝ) ^ e * (n : ℝ) ^ e * (K₂ * (n : ℝ) ^ δ) := by gcongr
      _ = (CR : ℝ) ^ e * K₂ * ((n : ℝ) ^ e * (n : ℝ) ^ δ) := by ring
  have hA : A ≤ ⌈A⌉₊ := Nat.le_ceil A
  have hCw : (0 : ℝ) ≤ Cw := Nat.cast_nonneg _
  push_cast
  calc 2 * ((CR : ℝ) * n * L ^ c) + (Cw * ((CR : ℝ) * n * L ^ c) ^ e + Cw) + 3
      ≤ 2 * (CR * K₁ * (n : ℝ) ^ (e + δ)) +
          (Cw * ((CR : ℝ) ^ e * K₂ * (n : ℝ) ^ (e + δ)) + Cw) + 3 := by gcongr
    _ = A * (n : ℝ) ^ (e + δ) + Cw + 3 := by ring
    _ ≤ ⌈A⌉₊ * (n : ℝ) ^ (e + δ) + Cw + 3 := by gcongr
    _ ≤ (⌈A⌉₊ + Cw + 3) * (n : ℝ) ^ (e + δ) + (⌈A⌉₊ + Cw + 3) := by
        have : (0 : ℝ) ≤ (Cw + 3) * (n : ℝ) ^ (e + δ) := by positivity
        have : (0 : ℝ) ≤ ⌈A⌉₊ := Nat.cast_nonneg _
        nlinarith

end Lax119563Proofs.Main
