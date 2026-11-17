import Lax119563Proofs.Reduction.CostGn

/-!
# The input length and its logarithm

Growth classes do not remember relations between levels, so `2^(log₂ |x|)` cannot be typed
as `P 1 0` from the classes of `|x|` and `log₂ |x|`. **`hasCost_lenLog`** types the prelude
`len (log (var n) (bind (shl (const 1) (var (n + 1))) g))`, which pushes `|x|` (`P 1 0`),
`L = log₂ |x|` (`P 0 1`) and `2^L ≤ |x|` (`P 1 0`); multiples of `2^L` (e.g. `2^ℓ` for
`ℓ = L + c`, via `mulC (2^c)`) are then `P 1 0` as well, so a `loopX` over them adds `1` to `e`.
-/

namespace Lax119563Proofs.Reduction

open Xp Ty

namespace Gn

lemma hasCost_lenLog {τs : List Ty} {n : ℕ} (hn : τs.length = n) {g : Gn} {e d : ℕ}
    (hg : HasCost (τs ++ [P 1 0, P 0 1, P 1 0]) g e d) :
    HasCost τs (len (log (var n) (bind (shl (const 1) (var (n + 1))) g))) (max 1 e) d := by
  intro K₀
  obtain ⟨Kg, hKg⟩ := hg (K₀ + 1)
  refine ⟨Kg + 10, fun ℓ x ρ hx hA => ?_⟩
  have hρ : ρ.length = n := hA.length_eq.trans hn
  set m := x.length
  set L := Nat.log 2 m
  have hL : L ≤ ℓ := by
    calc L ≤ Nat.log 2 (2 ^ ℓ) := Nat.log_mono_right hx
      _ = ℓ := Nat.log_pow (by norm_num) ℓ
  have hp : 2 ^ L ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hL
  have e1 : (var n).eval (ρ ++ [m]) = m := by
    simp only [Xp.eval]
    rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hρ]
  have e2 : (var (n + 1)).eval (ρ ++ [m] ++ [L]) = L := by
    simp only [Xp.eval, List.append_assoc]
    rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hρ]
  have hA' : Ag (K₀ + 1) ℓ (τs ++ [P 1 0, P 0 1, P 1 0]) (ρ ++ [m, L, 1 * 2 ^ L]) :=
    (hA.mono (by omega)).push3
      (by simp only [Ty.bnd, one_mul, pow_zero, mul_one]
          exact le_trans hx (Nat.le_mul_of_pos_left _ (by omega)))
      (by simp only [Ty.bnd, zero_mul, pow_zero, mul_one, pow_one]; nlinarith)
      (by simp only [Ty.bnd, one_mul, pow_zero, mul_one]
          exact le_trans hp (Nat.le_mul_of_pos_left _ (by omega)))
  have hstk : ρ ++ [m] ++ [L] ++ [1 * 2 ^ L] = ρ ++ [m, L, 1 * 2 ^ L] := by simp
  obtain ⟨g1, g2⟩ := hKg ℓ x _ hx hA'
  have hB1 : ℓ + 1 ≤ (Kg + 10) * (ℓ + 1) := by nlinarith
  have hlt : 2 ^ ℓ < 2 ^ ((Kg + 10) * (ℓ + 1)) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hl1 : ℓ < 2 ^ ((Kg + 10) * (ℓ + 1)) := lt_of_lt_of_le Nat.lt_two_pow_self hlt.le
  refine ⟨⟨by omega, ?_, ?_⟩, ?_⟩
  · show (var n).Fits _ (ρ ++ [m])
    simp only [Xp.Fits]; rw [show (ρ ++ [m]).getD n 0 = m from e1]; omega
  · show (bind (shl (const 1) (var (n + 1))) g).Fits x _ (ρ ++ [m] ++ [Nat.log 2 ((var n).eval (ρ ++ [m]))])
    rw [e1]
    refine ⟨⟨by show 1 < _; exact lt_of_le_of_lt Nat.one_le_two_pow hlt, ?_, ?_⟩, ?_⟩
    · show (ρ ++ [m] ++ [L]).getD (n + 1) 0 < _; rw [show (ρ ++ [m] ++ [L]).getD (n + 1) 0 = L
        from e2]; omega
    · show 1 * 2 ^ (var (n + 1)).eval (ρ ++ [m] ++ [L]) < _; rw [e2]; omega
    · show g.Fits x _ (ρ ++ [m] ++ [L] ++ [1 * 2 ^ (var (n + 1)).eval (ρ ++ [m] ++ [L])])
      rw [e2, hstk]; exact fits_up (by omega) g1
  · show m + 1 + ((var n).cost (ρ ++ [m]) + (var n).eval (ρ ++ [m]) + 2 +
      ((shl (const 1) (var (n + 1))).cost (ρ ++ [m] ++ [Nat.log 2 ((var n).eval (ρ ++ [m]))]) +
        g.cost x (ρ ++ [m] ++ [Nat.log 2 ((var n).eval (ρ ++ [m]))] ++
          [(shl (const 1) (var (n + 1))).eval (ρ ++ [m] ++
            [Nat.log 2 ((var n).eval (ρ ++ [m]))])]))) ≤ _
    rw [e1]
    simp only [Xp.cost, Xp.eval]
    rw [show (ρ ++ [m] ++ [L]).getD (n + 1) 0 = L from e2, hstk]
    have k1 := Ty.bnd_P_mono (le_max_right 1 e) le_rfl Kg ℓ (d := d + 1)
    have k2 := Ty.two_pow_le_bnd (le_max_left 1 e) (d + 1) ℓ
    have k3 := Ty.lin_le_bnd (max 1 e) d 1 ℓ
    have k4 : (P (max 1 e) (d + 1)).bnd Kg ℓ + (P (max 1 e) (d + 1)).bnd 10 ℓ =
        (P (max 1 e) (d + 1)).bnd (Kg + 10) ℓ := Ty.bnd_add ..
    have k5 : (P (max 1 e) (d + 1)).bnd 10 ℓ = 10 * (P (max 1 e) (d + 1)).bnd 1 ℓ := by
      simp only [Ty.bnd]; ring
    have := Ty.one_le_bnd (le_refl 1) ℓ (P (max 1 e) (d + 1))
    omega

end Gn

end Lax119563Proofs.Reduction
