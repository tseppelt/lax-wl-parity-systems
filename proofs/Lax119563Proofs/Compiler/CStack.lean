import Lax119563Proofs.Compiler.CLib

/-!
# Stack routines

* `moveAllS q q' t f`: pop all of `q` onto `q'` (reversing), with the scratch registers
  `t` (the moved value) and `f` (the loop flag); `moveAllS_good`.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

namespace CStm

/-- Pop all of `q` onto `q'`. -/
def moveAllS (q q' : Fin Q) (t f : Fin R) : CStm R Q :=
  .seq (.sne f q) (.loop (rv f) (.seq (.pop q t) (.seq (.push q' (rv t)) (.sne f q))))

lemma nodeCost_ge (w : ℕ) : unitCost w ≤ Ex.nodeCost w := Ex.unitCost_le_nodeCost w

lemma unitCost_ge (w : ℕ) : 64 ≤ unitCost w := by unfold unitCost; omega

/-- The state of `moveAllS` before iteration `j`. -/
def mvSt (st : NSt R Q) (q q' : Fin Q) (t f : Fin R) (j : ℕ) : NSt R Q :=
  ⟨Function.update (Function.update st.env t
      (if j = 0 then st.env t else (st.stk q).getD (j - 1) 0)) f
      (if j < (st.stk q).length then 1 else 0),
    Function.update (Function.update st.stk q ((st.stk q).drop j)) q'
      (((st.stk q).take j).reverse ++ st.stk q'),
    st.pos, st.out⟩

lemma moveAllS_good (hw : 2 ≤ w) {q q' : Fin Q} {t f : Fin R} (hq : q ≠ q') (htf : t ≠ f)
    (st : NSt R Q) (hb : st.Bdd w) :
    ∃ st' : NSt R Q, Good x w (moveAllS q q' t f) st st'
        (((st.stk q).length + 1) * (10 * Ex.nodeCost w)) ∧
      st'.stk = Function.update (Function.update st.stk q [])
        q' ((st.stk q).reverse ++ st.stk q') ∧
      st'.pos = st.pos ∧ st'.out = st.out ∧ ∀ r, r ≠ t → r ≠ f → st'.env r = st.env r := by
  have h2 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have hU := nodeCost_ge w
  have hU' := unitCost_ge w
  have hlb : ∀ v ∈ st.stk q, v < 2 ^ w := hb.2 q
  have hfq : ∀ j, (mvSt st q q' t f j).env f = if j < (st.stk q).length then 1 else 0 := by
    intro j; simp [mvSt]
  have hsq : ∀ j, (mvSt st q q' t f j).stk q = (st.stk q).drop j := by
    intro j; simp [mvSt, Function.update_of_ne hq]
  -- the body
  have hbody : ∀ j < (st.stk q).length,
      Good x w (.seq (.pop q t) (.seq (.push q' (rv t)) (.sne f q)))
        (mvSt st q q' t f j) (mvSt st q q' t f (j + 1)) (8 * Ex.nodeCost w) := by
    intro j hj
    have hd : (st.stk q).drop j = (st.stk q)[j] :: (st.stk q).drop (j + 1) :=
      List.drop_eq_getElem_cons hj
    refine ((Good.pop q t).seq ((Good.push ?_).seq (Good.sne f q))).of_eq ?_ ?_
    · simp only [rv, Ex.Fits, NSt.set_env, NSt.setS_env, Function.update_self]
      rw [hsq, hd]; exact hlb _ (List.getElem_mem _)
    · rw [hsq, hd]
      refine NSt.ext (funext fun r => ?_) (funext fun r => ?_) ?_ ?_
      · simp only [mvSt, NSt.set_env, NSt.setS_env, NSt.set_stk, NSt.setS_stk, rv, Ex.eval,
          Function.update_self, Function.update_of_ne hq, List.headD_cons, List.tail_cons,
          Function.update_of_ne hq.symm]
        by_cases hrf : r = f
        · subst hrf
          simp only [Function.update_self, List.isEmpty_iff, List.drop_eq_nil_iff]
          split_ifs <;> omega
        · by_cases hrt : r = t
          · subst hrt; simp [Function.update_of_ne hrf, Function.update_of_ne htf,
              List.getElem?_eq_getElem hj]
          · simp [Function.update_of_ne hrf, Function.update_of_ne hrt]
      · simp only [mvSt, NSt.set_env, NSt.setS_env, NSt.set_stk, NSt.setS_stk, rv, Ex.eval,
          Function.update_self, Function.update_of_ne htf.symm, List.headD_cons, List.tail_cons]
        by_cases hrq' : r = q'
        · subst hrq'
          simp only [Function.update_self, Function.update_of_ne hq.symm]
          rw [List.take_add_one, List.getElem?_eq_getElem hj, List.reverse_append]
          rfl
        · by_cases hrq : r = q
          · subst hrq; simp [Function.update_of_ne hq, Function.update_of_ne hrq']
          · simp [Function.update_of_ne hrq, Function.update_of_ne hrq']
      · simp [mvSt]
      · simp [mvSt]
    · simp only [rv, Ex.size]; omega
  have hloop := Good.loop_const (x := x) (w := w) (e := rv f) (st.stk q).length
    (mvSt st q q' t f) (8 * Ex.nodeCost w)
    (fun j hj => by simp [rv, Ex.eval, hfq, hj])
    (by simp [rv, Ex.eval, hfq])
    (fun j _ => by simp only [rv, Ex.Fits, hfq]; split_ifs <;> omega)
    hbody
  have hinit : Good x w (.sne f q) st (mvSt st q q' t f 0) (2 * unitCost w + 1) := by
    refine (Good.sne f q).of_eq ?_ le_rfl
    refine NSt.ext (funext fun r => ?_) (funext fun r => ?_) ?_ ?_
    · simp only [mvSt, NSt.set_env, if_true]
      by_cases hrf : r = f
      · subst hrf; simp only [Function.update_self]
        rcases h : st.stk q with _ | ⟨a, l⟩ <;> simp
      · by_cases hrt : r = t
        · subst hrt; simp [Function.update_of_ne hrf]
        · simp [Function.update_of_ne hrf, Function.update_of_ne hrt]
    · simp only [mvSt, NSt.set_stk, List.drop_zero, List.take_zero, List.reverse_nil,
        List.nil_append]
      by_cases hrq' : r = q'
      · subst hrq'; simp
      · by_cases hrq : r = q
        · subst hrq; simp [Function.update_of_ne hrq']
        · simp [Function.update_of_ne hrq, Function.update_of_ne hrq']
    · simp [mvSt]
    · simp [mvSt]
  refine ⟨mvSt st q q' t f (st.stk q).length, (hinit.seq hloop).mono ?_, ?_, rfl, rfl,
    fun r hrt hrf => ?_⟩
  · simp only [condCost, rv, Ex.size]; nlinarith
  · simp [mvSt]
  · simp [mvSt, Function.update_of_ne hrt, Function.update_of_ne hrf]

end CStm

end Lax119563Proofs.Compiler
