import Lax119563Proofs.Compiler.CEmit
import Lax119563Proofs.Compiler.OrderDesc

/-!
# Emitting the colors of a list of class sizes

`colorsS q t f p i`: pop the class sizes on `q`; for a size `n` emit `n` times the current
position `p` and advance `p` by `n` (`colorsS_good`: the output is extended by
`colorsOf P (stk q)`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

namespace CStm

/-- Emit `p`, `t` times (counter `i`). -/
def repS (t p i : Fin R) : CStm R Q :=
  .loop (.lt (rv i) (rv t)) (.seq (.emit (rv p)) (.set i (.add (rv i) (.const 1))))

/-- The body of `colorsS`. -/
def colBody (q : Fin Q) (t f p i : Fin R) : CStm R Q :=
  .seq (.pop q t) (.seq (.set i (.const 0)) (.seq (repS t p i)
    (.seq (.set p (.add (rv p) (rv t))) (.sne f q))))

/-- Emit the colors of the class sizes on `q`. -/
def colorsS (q : Fin Q) (t f p i : Fin R) : CStm R Q :=
  .seq (.sne f q) (.loop (rv f) (colBody q t f p i))

lemma repS_good (hw : 2 ≤ w) {t p i : Fin R} (hti : t ≠ i) (hpi : p ≠ i) (st : NSt R Q) (n : ℕ)
    (hi : st.env i = 0) (ht : st.env t = n) (hn : n < 2 ^ w) (hp : st.env p < 2 ^ w) :
    Good x w (repS t p i) st
      { (st.set i n) with out := st.out ++ List.replicate n (st.env p) }
      ((n + 1) * (10 * Ex.nodeCost w)) := by
  have hU := nodeCost_ge w
  have hU' := unitCost_ge w
  have h := Good.loop_const (x := x) (w := w) (e := .lt (rv i) (rv t))
    (body := .seq (.emit (rv p)) (.set i (.add (rv i) (.const 1)))) n
    (fun j => { (st.set i j) with out := st.out ++ List.replicate j (st.env p) })
    (6 * Ex.nodeCost w)
    (fun j hj => by
      simp [Ex.eval, rv, Function.update_of_ne hti, ht, hj])
    (by simp [Ex.eval, rv, Function.update_of_ne hti, ht])
    (fun j hj => by
      simp only [Ex.Fits, rv, NSt.set_env, Function.update_self, Function.update_of_ne hti, ht]
      omega)
    (fun j hj => by
      refine ((Good.emit ?_).seq (Good.set ?_)).of_eq ?_ ?_
      · simp only [Ex.Fits, rv, NSt.set_env, Function.update_of_ne hpi]; exact hp
      · simp only [Ex.Fits, rv, NSt.set_env, Function.update_self, Ex.eval]
        have : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
        omega
      · refine NSt.ext (funext fun r => ?_) rfl rfl ?_
        · simp only [NSt.set_env, Ex.eval, rv, Function.update_self]
          by_cases hr : r = i
          · subst hr; simp
          · simp [Function.update_of_ne hr]
        · simp [Ex.eval, rv, Function.update_of_ne hpi, List.replicate_succ']
      · simp only [Ex.size, rv]; omega)
  have e0 : ({ (st.set i 0) with out := st.out ++ List.replicate 0 (st.env p) } : NSt R Q) =
      st := by
    refine NSt.ext ?_ rfl rfl (by simp)
    funext r
    by_cases hr : r = i
    · subst hr; simp [hi]
    · simp [NSt.set_env, Function.update_of_ne hr]
  simp only [e0] at h
  refine h.mono ?_
  simp only [condCost, Ex.size, rv]; nlinarith

/-- **Colors from a stack of class sizes.** -/
lemma colorsS_loop_good (hw : 2 ≤ w) {q : Fin Q} {t f p i : Fin R} (htf : t ≠ f) (hti : t ≠ i)
    (htp : t ≠ p) (hfp : f ≠ p) (hfi : f ≠ i) (hpi : p ≠ i) :
    ∀ (L : List ℕ) (st : NSt R Q), st.stk q = L → st.env f = (if L = [] then 0 else 1) →
      st.env p + L.sum < 2 ^ w →
      ∃ st' : NSt R Q, Good x w (.loop (rv f) (colBody q t f p i)) st st'
          ((L.length + L.sum + 1) * (30 * Ex.nodeCost w)) ∧
        st'.stk = Function.update st.stk q [] ∧ st'.pos = st.pos ∧
        st'.out = st.out ++ colorsOf (st.env p) L ∧ st'.env p = st.env p + L.sum ∧
        ∀ r, r ≠ t → r ≠ f → r ≠ p → r ≠ i → st'.env r = st.env r
  | [], st, hq, hf, _ => by
    have hU := nodeCost_ge w
    have hU' := unitCost_ge w
    have h2 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
    refine ⟨st, (Good.loop_stop (by simp only [Ex.Fits, rv, hf] <;> simp <;> omega)
      (by simp [Ex.eval, rv, hf])).mono ?_,
      ?_, rfl, by simp [colorsOf], by simp, fun _ _ _ _ _ => rfl⟩
    · simp only [condCost, rv, Ex.size, List.length_nil, List.sum_nil]; omega
    · rw [← hq]; simp
  | n :: L, st, hq, hf, hP => by
    have hU := nodeCost_ge w
    have hU' := unitCost_ge w
    have h2 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
    simp only [List.sum_cons] at hP
    -- the body
    have r1 := Good.pop (x := x) (w := w) (st := st) q t
    set s1 := (st.setS q (st.stk q).tail).set t ((st.stk q).headD 0)
    have e1t : s1.env t = n := by simp [s1, hq]
    have e1p : s1.env p = st.env p := by simp [s1, Function.update_of_ne htp.symm]
    have r2 := Good.set (x := x) (w := w) (st := s1) (r := i) (e := .const 0)
      (by simp only [Ex.Fits]; omega)
    set s2 := s1.set i ((Ex.const 0 : Ex R).eval s1.env)
    have r3 := repS_good (x := x) (w := w) hw hti hpi s2 n (by simp [s2, Ex.eval])
      (by simp [s2, Function.update_of_ne hti, e1t]) (by omega)
      (by simp [s2, Function.update_of_ne hpi, e1p]; omega)
    set s3 := { (s2.set i n) with out := s2.out ++ List.replicate n (s2.env p) }
    have e3t : s3.env t = n := by simp [s3, s2, Function.update_of_ne hti, e1t]
    have e3p : s3.env p = st.env p := by simp [s3, s2, Function.update_of_ne hpi, e1p]
    have r4 := Good.set (x := x) (w := w) (st := s3) (r := p) (e := .add (rv p) (rv t))
      (by simp only [Ex.Fits, rv, Ex.eval, e3t, e3p]; omega)
    set s4 := s3.set p ((Ex.add (rv p) (rv t)).eval s3.env)
    have r5 := Good.sne (x := x) (w := w) (st := s4) f q
    set s5 := s4.set f (if (s4.stk q).isEmpty then 0 else 1)
    have e5q : s5.stk q = L := by simp [s5, s4, s3, s2, s1, hq]
    have e5f : s5.env f = if L = [] then 0 else 1 := by
      simp only [s5, NSt.set_env, Function.update_self]
      rw [show s4.stk q = L from e5q]
      cases L <;> rfl
    have e5p : s5.env p = st.env p + n := by
      simp [s5, s4, Function.update_of_ne hfp.symm, Ex.eval, rv, e3t, e3p]
    have hbody := r1.seq (r2.seq (r3.seq (r4.seq r5)))
    obtain ⟨st', h', hs', hp', ho', hP', he'⟩ :=
      colorsS_loop_good hw htf hti htp hfp hfi hpi L s5 e5q e5f (by rw [e5p]; omega)
    have hst5 : s5.stk = Function.update st.stk q L := by
      funext r; by_cases hr : r = q
      · subst hr; simp [e5q]
      · simp [s5, s4, s3, s2, s1, Function.update_of_ne hr]
    refine ⟨st', (Good.loop_cons (by simp only [Ex.Fits, rv, hf]; simpa using h2)
      (by simp [Ex.eval, rv, hf]) hbody h').mono ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [condCost, Ex.size, rv, List.length_cons, List.sum_cons]
      generalize Ex.nodeCost w = N at hU hU' ⊢
      generalize unitCost w = U at hU hU' ⊢
      rw [show L.length + 1 + (n + L.sum) + 1 = (L.length + L.sum + 1) + (n + 1) by ring]
      generalize L.length + L.sum + 1 = m
      nlinarith
    · rw [hs', hst5]; simp
    · rw [hp']; rfl
    · rw [ho', e5p]
      simp [s5, s4, s3, s2, s1, colorsOf, Function.update_of_ne hpi, Function.update_of_ne htp.symm]
    · rw [hP', e5p, List.sum_cons]; ring
    · intro r h1 h2' h3 h4
      rw [he' r h1 h2' h3 h4]
      simp [s5, s4, s3, s2, s1, Function.update_of_ne h1, Function.update_of_ne h2',
        Function.update_of_ne h3, Function.update_of_ne h4]

end CStm

end Lax119563Proofs.Compiler
