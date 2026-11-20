import Lax119563Proofs.Reduction.GuardEval
import Lax119563Proofs.Reduction.SchFinal

/-!
# Expressions for the domain test

The field expressions of the domain test of a schema: `fieldX` (a field of a register value),
`fieldBadX` (the field violates the guard; `fieldBad_iff`, `fieldOK_iff`) and `initCVX` (the
initial cell value), with their values, and further evaluation lemmas for the derived
expressions (`Xp.le`, `eval_and'`, `eval_or'`, `eval_not'`, `eval_shr`, `eval_xorM`).
-/

namespace Lax119563Proofs.Reduction

open Circuits Xp

namespace Xp

variable {ρ : List ℕ}

/-- `a ≤ b`. -/
def le (a b : Xp) : Xp := not (lt b a)

lemma eval_bool {e : Xp} {P : Prop} [Decidable P] (h : e.eval ρ = if P then 1 else 0) :
    e.eval ρ ≤ 1 := by
  rw [h]; split_ifs <;> omega

lemma eval_and' {a b : Xp} {P Q : Prop} [Decidable P] [Decidable Q]
    (ha : a.eval ρ = if P then 1 else 0) (hb : b.eval ρ = if Q then 1 else 0) :
    (and a b).eval ρ = if P ∧ Q then 1 else 0 := by
  rw [eval_and (eval_bool ha) (eval_bool hb), ha, hb]
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

lemma eval_or' {a b : Xp} {P Q : Prop} [Decidable P] [Decidable Q]
    (ha : a.eval ρ = if P then 1 else 0) (hb : b.eval ρ = if Q then 1 else 0) :
    (or a b).eval ρ = if P ∨ Q then 1 else 0 := by
  rw [eval_or, ha, hb]
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

lemma eval_not' {a : Xp} {P : Prop} [Decidable P] (ha : a.eval ρ = if P then 1 else 0) :
    (not a).eval ρ = if ¬ P then 1 else 0 := by
  rw [eval_not, ha]
  by_cases hP : P <;> simp [hP]

lemma eval_le (a b : Xp) : (le a b).eval ρ = if a.eval ρ ≤ b.eval ρ then 1 else 0 := by
  rw [le, eval_not' (P := b.eval ρ < a.eval ρ) (by rw [eval_lt_eq])]
  by_cases h : a.eval ρ ≤ b.eval ρ
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

@[simp] lemma eval_odd (a : Xp) : (odd a).eval ρ = a.eval ρ % 2 := rfl
@[simp] lemma eval_shr (a k : Xp) : (shr a k).eval ρ = a.eval ρ / 2 ^ k.eval ρ := rfl
@[simp] lemma eval_xorM (a b k : Xp) :
    (xorM a b k).eval ρ = (a.eval ρ ^^^ b.eval ρ) % 2 ^ k.eval ρ := rfl

end Xp

/-! ## Arithmetic of the field guard -/

lemma div_eq_iff_window {a ℓ i : ℕ} (hℓ : 0 < ℓ) : a / ℓ = i ↔ i * ℓ ≤ a ∧ a < i * ℓ + ℓ := by
  constructor
  · rintro rfl
    exact ⟨Nat.div_mul_le_self a ℓ, by have := Nat.lt_div_mul_add (a := a) hℓ; linarith⟩
  · rintro ⟨h1, h2⟩
    exact Nat.div_eq_of_lt_le h1 (by rw [Nat.succ_mul]; exact h2)

lemma testBit_eq_mod (v j : ℕ) : v.testBit j = decide (v / 2 ^ j % 2 = 1) :=
  Nat.testBit_eq_decide_div_mod_eq

lemma shift_bit (v a j : ℕ) : v * 2 ^ a / 2 ^ (a + j) = v / 2 ^ j := by
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (by positivity)]

/-- A violation of the field guard at offset `t`. -/
lemma fieldBad_iff {ℓ k t i v q : ℕ} (hℓ : 0 < ℓ) :
    ((k + t) / ℓ = i ∧ v.testBit ((k + t) % ℓ) ≠ q.testBit t) ↔
      (i * ℓ ≤ k + t ∧ k + t < i * ℓ + ℓ ∧ v * 2 ^ (i * ℓ) / 2 ^ (k + t) % 2 ≠ q / 2 ^ t % 2) := by
  rw [div_eq_iff_window hℓ]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, ?_⟩
    obtain ⟨j, hj⟩ : ∃ j, k + t = i * ℓ + j := ⟨k + t - i * ℓ, by omega⟩
    have hm : (k + t) % ℓ = j := by
      rw [hj, Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (by omega)
    rw [hm, testBit_eq_mod, testBit_eq_mod] at h3
    rw [hj, shift_bit]
    intro h; apply h3; rw [h]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    obtain ⟨j, hj⟩ : ∃ j, k + t = i * ℓ + j := ⟨k + t - i * ℓ, by omega⟩
    have hm : (k + t) % ℓ = j := by
      rw [hj, Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (by omega)
    rw [hm, testBit_eq_mod, testBit_eq_mod]
    rw [hj, shift_bit] at h3
    intro h
    apply h3
    have e1 := Nat.mod_two_eq_zero_or_one (v / 2 ^ j)
    have e2 := Nat.mod_two_eq_zero_or_one (q / 2 ^ t)
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;> simp_all

lemma fieldOK_iff {ℓ k m q i v : ℕ} (hℓ : 0 < ℓ) :
    fieldOK ℓ k m q i v = true ↔ ∀ t < m, ¬ (i * ℓ ≤ k + t ∧ k + t < i * ℓ + ℓ ∧
      v * 2 ^ (i * ℓ) / 2 ^ (k + t) % 2 ≠ q / 2 ^ t % 2) := by
  simp only [fieldOK, decide_eq_true_eq]
  refine forall_congr' fun t => imp_congr_right fun _ => ?_
  rw [← fieldBad_iff hℓ]
  tauto

/-! ## The generator -/

/-- The field `field (2^H) (iℓ) ℓ`. -/
def fieldX (iℓX ℓX HX : Xp) : Xp := xorM (shr (pow2 HX) iℓX) (const 0) ℓX

/-- The number `initCV x ν v` from `xb = inBit x v`. -/
def initCVX (νX vX xbX : Xp) : Xp :=
  add (eq vX (const 0)) (mulC 2 (mul xbX (eq νX (const 0))))

/-- A violation of the field guard at offset `t`. -/
def fieldBadX (iℓX kX tX vX qX ℓX : Xp) : Xp :=
  and (and (le iℓX (add kX tX)) (lt (add kX tX) (add iℓX ℓX)))
    (not (eq (odd (shr (shl vX iℓX) (add kX tX))) (odd (shr qX tX))))

lemma eval_fieldX {ρ : List ℕ} (iℓX ℓX HX : Xp) :
    (fieldX iℓX ℓX HX).eval ρ = field (2 ^ HX.eval ρ) (iℓX.eval ρ) (ℓX.eval ρ) := by
  simp [fieldX, field]

lemma eval_initCVX {ρ : List ℕ} {x : List Bool} {ν v : ℕ} {νX vX xbX : Xp}
    (hν : νX.eval ρ = ν) (hv : vX.eval ρ = v) (hxb : xbX.eval ρ = inBit x v) :
    (initCVX νX vX xbX).eval ρ = initCV x ν v := by
  simp only [initCVX, initCV, Xp.eval_add, Xp.eval_eq, Xp.eval_const, Xp.eval_mulC, Xp.eval_mul,
    hν, hv, hxb]
  by_cases h : ν = 0 <;> simp [h]


end Lax119563Proofs.Reduction
