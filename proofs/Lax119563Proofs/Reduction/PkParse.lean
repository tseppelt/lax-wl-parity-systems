import Lax119563Proofs.Reduction.PkMachine
import Lax119563Proofs.Compiler.CParse
import Lax119563Proofs.Compiler.CMachine

/-!
# The preprocessor of the packed generator

A structured statement `pkPre` (`Compiler.CStm`, number registers, no stacks) reads `h, s`
from the input `encodeNats [h, s] ++ x`, computes `2^q`, `q = ⌈(h + 2)/s⌉`, by a loop, and
emits the records `pkRec x h s k` for `k < pkLen |x| h s` (reading the bits of `x` with `rd`).
**`pkPre_computesWithin`**: its machine computes `pkInput x h s` within
`C (2^ℓ + h + 2) (h + 1)^2` steps.
-/

namespace Lax119563Proofs.Reduction

open Lax119563.BinaryEncodings Lax119563.DeterministicTime Lax119563Proofs.Compiler
open Lax119563Proofs.Compiler.CStm (rdNumS rdNumFinal rdNumS_good)

namespace PkParse

/-- Registers: `0 h, 1 s, 2 acc, 3 P, 4 k, 5 b, 6, 7` (helpers of `rdNumS`). -/
abbrev rH : Fin 8 := 0
abbrev rS : Fin 8 := 1
abbrev rA : Fin 8 := 2
abbrev rP : Fin 8 := 3
abbrev rK : Fin 8 := 4
abbrev rB : Fin 8 := 5
abbrev rU : Fin 8 := 6
abbrev rT : Fin 8 := 7

/-- `2 a`. -/
def dbl (a : Ex 8) : Ex 8 := .add a a

/-- The condition of the first loop: `acc < h + 2 + s`. -/
def c1 : Ex 8 := .lt (.var rA) (.add (.add (.var rH) (.const 2)) (.var rS))

/-- The body of the first loop: `acc += s; P += P`. -/
def b1 : CStm 8 0 := .seq (.set rA (.add (.var rA) (.var rS))) (.set rP (.add (.var rP) (.var rP)))

/-- The condition of the second loop: `b ≠ 0 ∨ k < h ∨ k < s ∨ k < P`. -/
def c2 : Ex 8 := .add (.add (.lt (.const 0) (.var rB)) (.lt (.var rK) (.var rH)))
  (.add (.lt (.var rK) (.var rS)) (.lt (.var rK) (.var rP)))

/-- The first number of a record. -/
def e1 : Ex 8 := .add (.add (.const 8) (.half (.var rB)))
  (.add (dbl (.lt (.const 0) (.var rB))) (dbl (dbl (.lt (.var rK) (.var rH)))))

/-- The second number of a record. -/
def e2 : Ex 8 := .add (.const 4) (.lt (.var rK) (.var rS))

/-- The body of the second loop. -/
def b2 : CStm 8 0 := .seq (.emit e1) (.seq (.emit e2) (.seq (.set rK (.add (.var rK) (.const 1)))
  (.rd rB)))

/-- **The preprocessor.** -/
def pkPre : CStm 8 0 :=
  .seq (rdNumS rH rU rT) (.seq (rdNumS rS rU rT) (.seq (.set rA (.add (.var rS) (.var rS)))
    (.seq (.set rP (.const 2)) (.seq (.loop c1 b1) (.seq (.set rK (.const 0))
      (.seq (.rd rB) (.loop c2 b2)))))))

/-- Environments. -/
def envP (a0 a1 a2 a3 a4 a5 a6 a7 : ℕ) : Fin 8 → ℕ := ![a0, a1, a2, a3, a4, a5, a6, a7]


section Get
variable (a0 a1 a2 a3 a4 a5 a6 a7 : ℕ)
@[simp] lemma envP_H : envP a0 a1 a2 a3 a4 a5 a6 a7 rH = a0 := rfl
@[simp] lemma envP_S : envP a0 a1 a2 a3 a4 a5 a6 a7 rS = a1 := rfl
@[simp] lemma envP_A : envP a0 a1 a2 a3 a4 a5 a6 a7 rA = a2 := rfl
@[simp] lemma envP_P : envP a0 a1 a2 a3 a4 a5 a6 a7 rP = a3 := rfl
@[simp] lemma envP_K : envP a0 a1 a2 a3 a4 a5 a6 a7 rK = a4 := rfl
@[simp] lemma envP_B : envP a0 a1 a2 a3 a4 a5 a6 a7 rB = a5 := rfl
end Get

lemma upd_envP (a0 a1 a2 a3 a4 a5 a6 a7 v : ℕ) :
    Function.update (envP a0 a1 a2 a3 a4 a5 a6 a7) rA v = envP a0 a1 v a3 a4 a5 a6 a7 ∧
    Function.update (envP a0 a1 a2 a3 a4 a5 a6 a7) rP v = envP a0 a1 a2 v a4 a5 a6 a7 ∧
    Function.update (envP a0 a1 a2 a3 a4 a5 a6 a7) rK v = envP a0 a1 a2 a3 v a5 a6 a7 ∧
    Function.update (envP a0 a1 a2 a3 a4 a5 a6 a7) rB v = envP a0 a1 a2 a3 a4 v a6 a7 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext i <;> fin_cases i <;> rfl

section Sem

variable (x : List Bool) (h s : ℕ)

/-- The input. -/
abbrev inp : List Bool := encodeNats [h, s] ++ x

/-- The position after the two numbers. -/
abbrev p0 : ℕ := (encodeNat h).length + (encodeNat s).length

/-- The helper value after reading `s`. -/
abbrev uS : ℕ := 2 ^ (Nat.bits s).length

/-- The number of iterations of the first loop. -/
abbrev n1 : ℕ := (h + 1 + s) / s - 1

/-- The state after reading `h, s`. -/
def stR : NSt 8 0 := ⟨envP h s 0 0 0 0 (uS s) 1, fun _ => [], p0 h s, []⟩

/-- The states of the first loop. -/
def S1 (j : ℕ) : NSt 8 0 :=
  ⟨envP h s ((j + 2) * s) (2 ^ (j + 1)) 0 0 (uS s) 1, fun _ => [], p0 h s, []⟩

/-- The states of the second loop. -/
def S2 (j : ℕ) : NSt 8 0 :=
  ⟨envP h s ((n1 h s + 2) * s) (2 ^ ((h + 1 + s) / s)) j (inBit (inp x h s) (p0 h s + j)) (uS s) 1,
    fun _ => [], min (p0 h s + j + 1) (inp x h s).length,
    (List.range j).flatMap (pkRec x h s)⟩

end Sem

lemma drop_inp (x : List Bool) (h s j : ℕ) : (inp x h s).drop (p0 h s + j) = x.drop j := by
  rw [Compiler.drop_add]
  have : (inp x h s).drop (p0 h s) = x := by
    rw [show p0 h s = (encodeNats [h, s]).length by simp [encodeNats]]
    exact List.drop_left
  rw [this]

lemma inBit_inp (x : List Bool) (h s j : ℕ) : inBit (inp x h s) (p0 h s + j) = inBit x j := by
  unfold inBit; rw [drop_inp]

lemma inBit_min (l : List Bool) (p : ℕ) : inBit l (min p l.length) = inBit l p := by
  rcases le_total p l.length with hp | hp
  · rw [min_eq_left hp]
  · rw [min_eq_right hp]
    unfold inBit
    rw [List.drop_eq_nil_of_le le_rfl, List.drop_eq_nil_of_le hp]

lemma inBit_pos (x : List Bool) (j : ℕ) : 0 < inBit x j ↔ j < x.length := by
  unfold inBit
  rcases Nat.lt_or_ge j x.length with hj | hj
  · rw [List.drop_eq_getElem_cons hj]; simp [rdVal, hj]
  · rw [List.drop_eq_nil_of_le hj]; simp [rdVal]; omega

lemma inBit_x_cases (x : List Bool) (j : ℕ) :
    inBit x j / 2 = (x.getD j false).toNat ∧ (if 0 < inBit x j then 1 else 0) =
      (if j < x.length then 1 else 0) := by
  unfold inBit
  rcases Nat.lt_or_ge j x.length with hj | hj
  · rw [List.drop_eq_getElem_cons hj, List.getD_eq_getElem _ _ hj]
    cases x[j] <;> simp [rdVal, hj]
  · rw [List.drop_eq_nil_of_le hj, List.getD_eq_default _ _ hj]
    simp [rdVal, show ¬ j < x.length by omega]


open CStm in
lemma stR_eq (h s : ℕ) :
    rdNumFinal (rdNumFinal (NSt.zero 8 0) rH rU rT h) rS rU rT s = stR h s := by
  simp only [rdNumFinal, stR, NSt.zero]
  congr 1
  · funext i; fin_cases i <;> simp [Function.update, envP, rT, rU, rS, rH]
  · simp

lemma c1_iff {h s j : ℕ} (hs : 1 ≤ s) : (j + 2) * s < h + 2 + s ↔ j < n1 h s := by
  have hq : 1 ≤ (h + 1 + s) / s := (Nat.le_div_iff_mul_le hs).mpr (by omega)
  have : (j + 2) * s < h + 2 + s ↔ j + 2 ≤ (h + 1 + s) / s := by
    rw [Nat.le_div_iff_mul_le hs]; omega
  rw [this]; unfold n1; omega

lemma acc_le {h s j : ℕ} (hs : 1 ≤ s) (hj : j ≤ n1 h s) : (j + 2) * s ≤ h + 1 + 2 * s := by
  have h1 : (h + 1 + s) / s * s ≤ h + 1 + s := Nat.div_mul_le_self _ _
  have hq : 1 ≤ (h + 1 + s) / s := (Nat.le_div_iff_mul_le hs).mpr (by omega)
  have h2 : (j + 2) * s ≤ ((h + 1 + s) / s + 1) * s := Nat.mul_le_mul_right _ (by unfold n1 at hj; omega)
  have e : ((h + 1 + s) / s + 1) * s = (h + 1 + s) / s * s + s := by ring
  omega

lemma q_le {h s : ℕ} (hh : 1 ≤ h) (hs : 2 ≤ s) : (h + 1 + s) / s ≤ h + 1 := by
  apply Nat.div_le_of_le_mul; nlinarith

open CStm Good in
/-- **The preprocessor**: denotation and cost. -/
theorem pkPre_good {x : List Bool} {h s : ℕ} (hx : 2 ≤ x.length) (hh : 2 ≤ h)
    (hxh : x.length ≤ 2 ^ h) (hs : 2 ≤ s) (hsh : s ≤ h + 2) :
    CStm.Good (inp x h s) (h + 6) pkPre (NSt.zero 8 0) (S2 x h s (pkLen x.length h s))
      (1000 * Ex.nodeCost (h + 6) * ((encodeNat h).length + (encodeNat s).length +
        n1 h s + pkLen x.length h s + 10)) := by
  have hw2 : 2 ≤ h + 6 := by omega
  have hs1 : 1 ≤ s := by omega
  have hpw : 2 ^ (h + 6) = 64 * 2 ^ h := by rw [pow_add]; ring
  have hhb : h < 2 ^ h := Nat.lt_two_pow_self
  have hq := q_le (h := h) (by omega) hs
  have hP : 2 ^ ((h + 1 + s) / s) ≤ 2 * 2 ^ h := by
    calc 2 ^ ((h + 1 + s) / s) ≤ 2 ^ (h + 1) := Nat.pow_le_pow_right (by norm_num) hq
      _ = 2 * 2 ^ h := by rw [pow_succ]; ring
  have hm : pkLen x.length h s ≤ 4 * 2 ^ h := by
    unfold pkLen; omega
  have hbits : ∀ v, v ≤ h + 2 → (Nat.bits v).length < h + 6 := fun v hv => by
    rw [Nat.size_eq_bits_len]
    have : v < 2 ^ (h + 5) := by
      have : 2 ^ (h + 5) = 32 * 2 ^ h := by rw [pow_add]; ring
      omega
    have := Nat.size_le.mpr this
    omega
  -- reading `h` and `s`
  have g1 := rdNumS_good (x := inp x h s) hw2 (r := rH) (p := rU) (t := rT) (by decide) (by decide)
    (by decide) (NSt.zero 8 0) h (encodeNat s ++ x) (by simp [NSt.zero, inp, encodeNats])
    (hbits h (by omega))
  have g2 := rdNumS_good (x := inp x h s) hw2 (r := rS) (p := rU) (t := rT) (by decide) (by decide)
    (by decide) (rdNumFinal (NSt.zero 8 0) rH rU rT h) s x
    (by
      simp only [rdNumFinal, NSt.zero, zero_add]
      rw [show inp x h s = encodeNat h ++ (encodeNat s ++ x) by simp [inp, encodeNats]]
      exact List.drop_left)
    (hbits s (by omega))
  rw [stR_eq] at g2
  -- initializing the first loop
  have g3 : CStm.Good (inp x h s) (h + 6) (.set rA (.add (.var rS) (.var rS))) (stR h s)
      ((stR h s).set rA (s + s)) (3 * Ex.nodeCost (h + 6) + unitCost (h + 6)) := by
    refine (CStm.Good.set ?_).of_eq rfl (by simp [Ex.size])
    simp only [Ex.Fits, Ex.eval, stR, envP_S]
    omega
  have g4 : CStm.Good (inp x h s) (h + 6) (.set rP (.const 2)) ((stR h s).set rA (s + s))
      (S1 h s 0) (Ex.nodeCost (h + 6) + unitCost (h + 6)) := by
    refine (CStm.Good.set ?_).of_eq ?_ (by simp [Ex.size])
    · simp only [Ex.Fits]; omega
    · simp only [stR, S1, NSt.set, Ex.eval, NSt.set_env]
      rw [(upd_envP _ _ _ _ _ _ _ _ _).1, (upd_envP _ _ _ _ _ _ _ _ _).2.1]
      congr 2; ring
  -- the first loop
  have hq1 : 1 ≤ (h + 1 + s) / s := (Nat.le_div_iff_mul_le hs1).mpr (by omega)
  have g5 : CStm.Good (inp x h s) (h + 6) (.loop c1 b1) (S1 h s 0) (S1 h s (n1 h s))
      (n1 h s * (2 * (3 * Ex.nodeCost (h + 6) + unitCost (h + 6)) + condCost (h + 6) c1) +
        condCost (h + 6) c1) := by
    refine CStm.Good.loop_const (n1 h s) (S1 h s) _ (fun j hj => ?_) ?_ (fun j hj => ?_)
      (fun j hj => ?_)
    · have hc := (c1_iff (h := h) hs1).mpr hj
      simp only [c1, S1, Ex.eval, envP_A, envP_H, envP_S]
      simp [hc]
    · have hc : ¬ (n1 h s + 2) * s < h + 2 + s := fun h' =>
        lt_irrefl _ ((c1_iff hs1).mp h')
      simp only [c1, S1, Ex.eval, envP_A, envP_H, envP_S]
      simp [hc]
    · have ha := acc_le (h := h) hs1 hj
      simp only [c1, S1, Ex.Fits, Ex.eval, envP_A, envP_H, envP_S]
      omega
    · have ha := acc_le (h := h) hs1 (show j + 1 ≤ n1 h s by omega)
      have ha0 := acc_le (h := h) hs1 (show j ≤ n1 h s by omega)
      have hp : 2 ^ (j + 1) + 2 ^ (j + 1) ≤ 2 * 2 ^ h := by
        have : 2 ^ (j + 2) ≤ 2 ^ ((h + 1 + s) / s) :=
          Nat.pow_le_pow_right (by norm_num) (by unfold n1 at hj; omega)
        rw [pow_succ 2 (j + 1)] at this; omega
      refine (CStm.Good.seq (CStm.Good.set ?_) (CStm.Good.set ?_)).of_eq ?_
        (by simp [Ex.size]; omega)
      · simp only [Ex.Fits, S1, envP_A, envP_S, Ex.eval]
        refine ⟨by omega, by omega, ?_⟩
        have : (j + 2) * s + s = (j + 1 + 2) * s := by ring
        omega
      · simp only [Ex.Fits, S1, NSt.set, Ex.eval]
        rw [(upd_envP _ _ _ _ _ _ _ _ _).1]
        simp only [envP_P]
        omega
      · simp only [S1, NSt.set, Ex.eval]
        rw [(upd_envP _ _ _ _ _ _ _ _ _).1]
        simp only [envP_A, envP_S, envP_P]
        rw [(upd_envP _ _ _ _ _ _ _ _ _).2.1]
        congr 2
        · ring
        · rw [pow_succ 2 (j + 1)]; ring
  -- the second loop
  have g6 : CStm.Good (inp x h s) (h + 6) (.set rK (.const 0)) (S1 h s (n1 h s))
      (S1 h s (n1 h s)) (Ex.nodeCost (h + 6) + unitCost (h + 6)) := by
    refine (CStm.Good.set ?_).of_eq ?_ (by simp [Ex.size])
    · simp only [Ex.Fits]; omega
    · simp only [S1, NSt.set, Ex.eval]
      rw [(upd_envP _ _ _ _ _ _ _ _ _).2.2.1]
  have g7 : CStm.Good (inp x h s) (h + 6) (.rd rB) (S1 h s (n1 h s)) (S2 x h s 0)
      (unitCost (h + 6)) := by
    refine (CStm.Good.rd rB).of_eq ?_ le_rfl
    simp only [S1, S2, NSt.set]
    rw [(upd_envP _ _ _ _ _ _ _ _ _).2.2.2]
    have : n1 h s + 1 = (h + 1 + s) / s := by unfold n1; omega
    rw [this]
    simp
  -- the second loop
  have hinb : ∀ j, inBit (inp x h s) (p0 h s + j) ≤ 2 := fun j => inBit_le _ _
  have g8 : CStm.Good (inp x h s) (h + 6) (.loop c2 b2) (S2 x h s 0)
      (S2 x h s (pkLen x.length h s))
      (pkLen x.length h s * (40 * Ex.nodeCost (h + 6) + condCost (h + 6) c2) +
        condCost (h + 6) c2) := by
    refine CStm.Good.loop_const (pkLen x.length h s) (S2 x h s) _ (fun j hj => ?_) ?_
      (fun j hj => ?_) (fun j hj => ?_)
    · have hj' : j < x.length ∨ j < h ∨ j < s ∨ j < 2 ^ ((h + 1 + s) / s) := by
        unfold pkLen at hj; omega
      have hp := inBit_pos x j
      rw [← inBit_inp x h s j] at hp
      simp only [c2, S2, Ex.eval, envP_B, envP_K, envP_H, envP_S, envP_P]
      by_cases h1 : 0 < inBit (inp x h s) (p0 h s + j) <;> by_cases h2 : j < h <;>
        by_cases h3 : j < s <;> by_cases h4 : j < 2 ^ ((h + 1 + s) / s) <;>
        simp only [h1, h2, h3, h4, if_true, if_false] <;> omega
    · have hp := inBit_pos x (pkLen x.length h s)
      rw [← inBit_inp x h s] at hp
      simp only [c2, S2, Ex.eval, envP_B, envP_K, envP_H, envP_S, envP_P]
      have hm1 : x.length ≤ pkLen x.length h s ∧ h ≤ pkLen x.length h s ∧
          s ≤ pkLen x.length h s ∧ 2 ^ ((h + 1 + s) / s) ≤ pkLen x.length h s := by
        unfold pkLen; omega
      simp only [show ¬ pkLen x.length h s < x.length by omega,
        show ¬ pkLen x.length h s < h by omega, show ¬ pkLen x.length h s < s by omega,
        show ¬ pkLen x.length h s < 2 ^ ((h + 1 + s) / s) by omega, if_false,
        show ¬ 0 < inBit (inp x h s) (p0 h s + pkLen x.length h s) by rw [hp]; omega]
    · have hjm : j ≤ 4 * 2 ^ h := le_trans hj hm
      have := hinb j
      simp only [c2, S2, Ex.Fits, Ex.eval, envP_B, envP_K, envP_H, envP_S, envP_P]
      by_cases h1 : 0 < inBit (inp x h s) (p0 h s + j) <;> by_cases h2 : j < h <;>
        by_cases h3 : j < s <;> by_cases h4 : j < 2 ^ ((h + 1 + s) / s) <;>
        simp only [h1, h2, h3, h4, if_true, if_false] <;>
        (repeat' apply And.intro) <;> omega
    · have hjm : j + 1 ≤ 4 * 2 ^ h := le_trans hj hm
      have hb := hinb j
      have hx2 := inBit_x_cases x j
      rw [← inBit_inp x h s j] at hx2
      refine (CStm.Good.seq (CStm.Good.emit ?_) (CStm.Good.seq (CStm.Good.emit ?_)
        (CStm.Good.seq (CStm.Good.set ?_) (CStm.Good.rd rB)))).of_eq ?_ ?_
      · simp only [e1, dbl, S2, Ex.Fits, Ex.eval, envP_B, envP_K, envP_H]
        by_cases h1 : 0 < inBit (inp x h s) (p0 h s + j) <;> by_cases h2 : j < h <;>
          simp only [h1, h2, if_true, if_false] <;> (repeat' apply And.intro) <;> omega
      · simp only [e2, S2, Ex.Fits, Ex.eval, envP_K, envP_S]
        by_cases h3 : j < s <;>
          simp only [h3, if_true, if_false] <;> (repeat' apply And.intro) <;> omega
      · simp only [S2, Ex.Fits, Ex.eval, envP_K]
        repeat' apply And.intro
        all_goals omega
      · have ev1 : e1.eval (S2 x h s j).env = 8 + inBit (inp x h s) (p0 h s + j) / 2 +
            (((if 0 < inBit (inp x h s) (p0 h s + j) then 1 else 0) +
              (if 0 < inBit (inp x h s) (p0 h s + j) then 1 else 0)) +
            (((if j < h then 1 else 0) + (if j < h then 1 else 0)) +
              ((if j < h then 1 else 0) + (if j < h then 1 else 0)))) := rfl
        have ev2 : e2.eval (S2 x h s j).env = 4 + (if j < s then 1 else 0) := rfl
        rw [hx2.1, hx2.2] at ev1
        refine NSt.ext ?_ rfl ?_ ?_
        · show Function.update (Function.update (S2 x h s j).env rK (j + 1)) rB
            (inBit (inp x h s) (min (p0 h s + j + 1) (inp x h s).length)) =
            (S2 x h s (j + 1)).env
          simp only [S2]
          rw [(upd_envP _ _ _ _ _ _ _ _ _).2.2.1, (upd_envP _ _ _ _ _ _ _ _ _).2.2.2, inBit_min,
            show p0 h s + j + 1 = p0 h s + (j + 1) by omega]
        · show min (min (p0 h s + j + 1) (inp x h s).length + 1) (inp x h s).length =
            min (p0 h s + (j + 1) + 1) (inp x h s).length
          omega
        · show (List.range j).flatMap (pkRec x h s) ++ [e1.eval (S2 x h s j).env] ++
            [e2.eval (S2 x h s j).env] = (List.range (j + 1)).flatMap (pkRec x h s)
          rw [ev1, ev2, List.range_succ, List.flatMap_append, List.flatMap_singleton,
            List.append_assoc, List.singleton_append]
          congr 1
          simp only [pkRec]
          by_cases h1 : j < x.length <;> by_cases h2 : j < h <;> by_cases h3 : j < s <;>
            simp [h1, h2, h3] <;> omega
      · simp [Ex.size, e1, e2, dbl]
        have : unitCost (h + 6) ≤ Ex.nodeCost (h + 6) := by
          simp only [Ex.nodeCost]; nlinarith
        omega
  -- assembling
  have G := g1.seq (g2.seq (g3.seq (g4.seq (g5.seq (g6.seq (g7.seq g8))))))
  refine G.mono ?_
  have hc1 : condCost (h + 6) c1 = 7 * Ex.nodeCost (h + 6) + 1 := by
    simp [condCost, c1, Ex.size]
  have hc2 : condCost (h + 6) c2 = 15 * Ex.nodeCost (h + 6) + 1 := by
    simp [condCost, c2, Ex.size]
  have hu : unitCost (h + 6) ≤ Ex.nodeCost (h + 6) := by
    simp only [Ex.nodeCost]; nlinarith
  have hn1 : 1 ≤ Ex.nodeCost (h + 6) := by
    simp only [Ex.nodeCost, unitCost]; nlinarith
  rw [hc1, hc2]
  generalize Ex.nodeCost (h + 6) = nc at hu hn1 ⊢
  generalize unitCost (h + 6) = uc at hu ⊢
  have k1 : n1 h s * (2 * (3 * nc + uc) + (7 * nc + 1)) ≤ 16 * (n1 h s * nc) := by
    have : 2 * (3 * nc + uc) + (7 * nc + 1) ≤ 16 * nc := by omega
    calc _ ≤ n1 h s * (16 * nc) := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  have k2 : pkLen x.length h s * (40 * nc + (15 * nc + 1)) ≤
      56 * (pkLen x.length h s * nc) := by
    have : 40 * nc + (15 * nc + 1) ≤ 56 * nc := by omega
    calc _ ≤ pkLen x.length h s * (56 * nc) := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  have e1' : ((encodeNat h).length + 1) * (20 * nc) = 20 * ((encodeNat h).length * nc) + 20 * nc :=
    by ring
  have e2' : ((encodeNat s).length + 1) * (20 * nc) = 20 * ((encodeNat s).length * nc) + 20 * nc :=
    by ring
  have e3 : 1000 * nc * ((encodeNat h).length + (encodeNat s).length + n1 h s +
      pkLen x.length h s + 10) = 1000 * ((encodeNat h).length * nc) +
      1000 * ((encodeNat s).length * nc) + 1000 * (n1 h s * nc) +
      1000 * (pkLen x.length h s * nc) + 10000 * nc := by ring
  rw [e1', e2', e3]
  omega


lemma length_encodeNat_le (v : ℕ) : (encodeNat v).length ≤ 2 * v + 1 := by
  rw [CStm.length_encodeNat, Nat.size_eq_bits_len]
  have : Nat.size v ≤ v := by
    rcases Nat.eq_zero_or_pos v with h | h
    · subst h; simp
    · exact Nat.size_le.mpr Nat.lt_two_pow_self
  omega

lemma nodeCost_le (h : ℕ) : Ex.nodeCost (h + 6) ≤ 5184 * (h + 1) ^ 2 := by
  simp only [Ex.nodeCost, unitCost]; nlinarith

end PkParse

open PkParse in
/-- **The machine of the preprocessor.** -/
theorem pkPre_computesWithin : ∃ C : ℕ, ∀ (x : List Bool) (h s : ℕ), 2 ≤ x.length → 2 ≤ h →
    x.length ≤ 2 ^ h → 2 ≤ s → s ≤ h + 2 →
    ComputesWithin (pkPre.machine pkPre.depth) (encodeNats [h, s] ++ x) (pkInput x h s)
      (C * (2 ^ pkWidth x.length h s + h + 2) * (h + 1) ^ 2) := by
  refine ⟨20000 * 5184 + 1000, fun x h s hx hh hxh hs hsh => ?_⟩
  obtain ⟨hPar, hH⟩ := pk_params hx hh hxh hs
  have G := pkPre_good hx hh hxh hs hsh
  have H := CStm.computesWithin (D := pkPre.depth) (x := inp x h s) (w := h + 6) (by omega)
    le_rfl G.1
  rw [G.2.1] at H
  have hout : encodeNats (S2 x h s (pkLen x.length h s)).out = pkInput x h s := rfl
  rw [hout] at H
  refine ComputesWithin.mono H ?_
  have hc := G.2.2
  have hm := pkLen_le hPar.hx hsh
  have hlen : (pkInput x h s).length ≤ 16 * (2 ^ pkWidth x.length h s + h + 2) := by
    rw [length_pkInput]; omega
  have hinp : (inp x h s).length ≤ 2 * h + 2 * s + 2 + x.length := by
    have := PkParse.length_encodeNat_le h
    have := PkParse.length_encodeNat_le s
    simp [inp, encodeNats]; omega
  have hn : x.length ≤ 2 ^ pkWidth x.length h s := hPar.hx.le
  have heh := PkParse.length_encodeNat_le h
  have hes := PkParse.length_encodeNat_le s
  have hn1 : n1 h s ≤ h + 1 := by unfold n1; have := q_le (h := h) (by omega) hs; omega
  have hnc := nodeCost_le h
  set A := 2 ^ pkWidth x.length h s + h + 2 with hA
  set B := (h + 1) ^ 2 with hB
  have hB1 : 1 ≤ B := Nat.one_le_pow _ _ (by omega)
  have hsum : (encodeNat h).length + (encodeNat s).length + n1 h s + pkLen x.length h s + 10 ≤
      20 * A := by omega
  have hcost : 1000 * Ex.nodeCost (h + 6) * ((encodeNat h).length + (encodeNat s).length +
      n1 h s + pkLen x.length h s + 10) ≤ 20000 * 5184 * A * B := by
    calc _ ≤ 1000 * (5184 * B) * (20 * A) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hnc) hsum
      _ = _ := by ring
  have hrest : 20 * ((inp x h s).length + (pkInput x h s).length) + 10 ≤ 1000 * A * B := by
    have : 1000 * A ≤ 1000 * A * B := Nat.le_mul_of_pos_right _ (by omega)
    omega
  calc _ ≤ 20000 * 5184 * A * B + 1000 * A * B := by omega
    _ = _ := by ring

end Lax119563Proofs.Reduction
