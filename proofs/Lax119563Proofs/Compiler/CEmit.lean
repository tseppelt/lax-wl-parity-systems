import Lax119563Proofs.Compiler.CSortLoop

/-!
# Emitting a stack

* `emitAllS q t f`: pop all of `q`, emitting each value (`emitAllS_good`: the output is
  extended by the stack, top first).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

namespace CStm

/-- Pop all of `q`, emitting the values. -/
def emitAllS (q : Fin Q) (t f : Fin R) : CStm R Q :=
  .seq (.sne f q) (.loop (rv f) (.seq (.pop q t) (.seq (.emit (rv t)) (.sne f q))))

/-- The state of `emitAllS` before iteration `j`. -/
def emSt (st : NSt R Q) (q : Fin Q) (t f : Fin R) (j : ℕ) : NSt R Q :=
  ⟨Function.update (Function.update st.env t
      (if j = 0 then st.env t else (st.stk q).getD (j - 1) 0)) f
      (if j < (st.stk q).length then 1 else 0),
    Function.update st.stk q ((st.stk q).drop j), st.pos, st.out ++ (st.stk q).take j⟩

lemma emitAllS_good (hw : 2 ≤ w) {q : Fin Q} {t f : Fin R} (htf : t ≠ f)
    (st : NSt R Q) (hb : st.Bdd w) :
    ∃ st' : NSt R Q, Good x w (emitAllS q t f) st st'
        (((st.stk q).length + 1) * (10 * Ex.nodeCost w)) ∧
      st'.stk = Function.update st.stk q [] ∧
      st'.pos = st.pos ∧ st'.out = st.out ++ st.stk q ∧
      ∀ r, r ≠ t → r ≠ f → st'.env r = st.env r := by
  have h2 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have hU := nodeCost_ge w
  have hU' := unitCost_ge w
  have hlb : ∀ v ∈ st.stk q, v < 2 ^ w := hb.2 q
  have hfq : ∀ j, (emSt st q t f j).env f = if j < (st.stk q).length then 1 else 0 := by
    intro j; simp [emSt]
  have hsq : ∀ j, (emSt st q t f j).stk q = (st.stk q).drop j := by
    intro j; simp [emSt]
  have hbody : ∀ j < (st.stk q).length,
      Good x w (.seq (.pop q t) (.seq (.emit (rv t)) (.sne f q)))
        (emSt st q t f j) (emSt st q t f (j + 1)) (8 * Ex.nodeCost w) := by
    intro j hj
    have hd : (st.stk q).drop j = (st.stk q)[j] :: (st.stk q).drop (j + 1) :=
      List.drop_eq_getElem_cons hj
    refine ((Good.pop q t).seq ((Good.emit ?_).seq (Good.sne f q))).of_eq ?_ ?_
    · simp only [rv, Ex.Fits, NSt.set_env, NSt.setS_env, Function.update_self]
      rw [hsq, hd]; exact hlb _ (List.getElem_mem _)
    · rw [hsq, hd]
      refine NSt.ext (funext fun r => ?_) (funext fun r => ?_) ?_ ?_
      · simp only [emSt, NSt.set_env, NSt.setS_env, NSt.set_stk, NSt.setS_stk, rv, Ex.eval,
          Function.update_self, List.headD_cons, List.tail_cons]
        by_cases hrf : r = f
        · subst hrf
          simp only [Function.update_self, List.isEmpty_iff, List.drop_eq_nil_iff]
          split_ifs <;> omega
        · by_cases hrt : r = t
          · subst hrt; simp [Function.update_of_ne hrf, Function.update_of_ne htf,
              List.getElem?_eq_getElem hj]
          · simp [Function.update_of_ne hrf, Function.update_of_ne hrt]
      · simp only [emSt, NSt.set_stk, NSt.setS_stk, List.tail_cons]
        by_cases hrq : r = q
        · subst hrq; simp
        · simp [Function.update_of_ne hrq]
      · simp [emSt]
      · simp only [emSt, NSt.set_env, NSt.setS_env, NSt.set_stk, NSt.setS_stk, rv, Ex.eval,
          Function.update_self, List.headD_cons, NSt.set_out, NSt.setS_out]
        rw [List.take_add_one, List.getElem?_eq_getElem hj, List.append_assoc]
        rfl
    · simp only [rv, Ex.size]; omega
  have hloop := Good.loop_const (x := x) (w := w) (e := rv f) (st.stk q).length
    (emSt st q t f) (8 * Ex.nodeCost w)
    (fun j hj => by simp [rv, Ex.eval, hfq, hj])
    (by simp [rv, Ex.eval, hfq])
    (fun j _ => by simp only [rv, Ex.Fits, hfq]; split_ifs <;> omega)
    hbody
  have hinit : Good x w (.sne f q) st (emSt st q t f 0) (2 * unitCost w + 1) := by
    refine (Good.sne f q).of_eq ?_ le_rfl
    refine NSt.ext (funext fun r => ?_) (funext fun r => ?_) ?_ ?_
    · simp only [emSt, NSt.set_env, if_true]
      by_cases hrf : r = f
      · subst hrf; simp only [Function.update_self]
        rcases h : st.stk q with _ | ⟨a, l⟩ <;> simp
      · by_cases hrt : r = t
        · subst hrt; simp [Function.update_of_ne hrf]
        · simp [Function.update_of_ne hrf, Function.update_of_ne hrt]
    · simp only [emSt, NSt.set_stk, List.drop_zero]
      by_cases hrq : r = q
      · subst hrq; simp
      · simp [Function.update_of_ne hrq]
    · simp [emSt]
    · simp [emSt]
  refine ⟨emSt st q t f (st.stk q).length, (hinit.seq hloop).mono ?_, ?_, rfl, ?_,
    fun r hrt hrf => ?_⟩
  · simp only [condCost, rv, Ex.size]; nlinarith
  · simp [emSt]
  · simp [emSt]
  · simp [emSt, Function.update_of_ne hrt, Function.update_of_ne hrf]

end CStm

end Lax119563Proofs.Compiler
