import Lax119563Proofs.Computability.StackParse

/-!
# Loading stacks and clearing them

* `pushBits q t`: push the symbols of `pairs (Nat.bits k)` onto `q` (reversed), where `k` is
  the value of `t` (`pushBits_good`);
* `readIn q t`: push the symbols of the remaining input onto `q` (reversed; `readIn_good`);
* `clrS q t f`: empty the stack `q` (`clrS_good`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler

namespace Lax119563Proofs.Computability

open CStm

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

lemma syms_pairs_take_succ (l : List Bool) (j : ℕ) (hj : j < l.length) :
    (syms (pairs (l.take (j + 1)))).reverse = symOf l[j] :: 2 :: (syms (pairs (l.take j))).reverse := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj]
  simp only [Option.toList_some, pairs_append, pairs_cons, pairs_nil, syms, List.map_append,
    List.reverse_append, List.map_cons, List.map_nil]
  rfl

lemma syms_take_succ (l : List Bool) (j : ℕ) (hj : j < l.length) :
    (syms (l.take (j + 1))).reverse = symOf l[j] :: (syms (l.take j)).reverse := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj]
  simp only [syms, List.map_append, List.reverse_append, Option.toList_some, List.map_cons,
    List.map_nil]
  rfl

/-! ## Pushing the digits of a number -/

/-- Push `2, symOf d` for the digits `d` of the value of `t` (least significant first). -/
def pushBits (q : Fin Q) (t : Fin R) : CStm R Q :=
  .loop (.var t) (seqL [.push q (.const 2), .push q (.add (.odd (.var t)) (.const 1)),
    .set t (.half (.var t))])

lemma symOf_decide (m : ℕ) : symOf (decide (m % 2 = 1)) = m % 2 + 1 := by
  rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [symOf, h]

lemma pushBits_good (hw : 2 ≤ w) {q : Fin Q} {t : Fin R} (st : NSt R Q) (k : ℕ)
    (ht : st.env t = k) (hk : k < 2 ^ w) :
    Good x w (pushBits q t) st (exec x (pushBits q t) st)
        ((k.bits.length + 1) * (14 * Ex.nodeCost w)) ∧
      (exec x (pushBits q t) st).stk q = (syms (pairs k.bits)).reverse ++ st.stk q ∧
      (exec x (pushBits q t) st).env t = 0 ∧
      ∀ r, r ≠ t → (exec x (pushBits q t) st).env r = st.env r := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  set B : CStm R Q := seqL [.push q (.const 2), .push q (.add (.odd (.var t)) (.const 1)),
    .set t (.half (.var t))] with hB
  set S : ℕ → NSt R Q := fun j => iter x B st j with hS
  set n := k.bits.length
  have hnz : ∀ j < n, k / 2 ^ j ≠ 0 := fun j hj h => by
    have := bits_drop k j
    rw [h, Nat.zero_bits, List.drop_eq_nil_iff] at this; omega
  have hbit : ∀ j (hj : j < n), symOf (k.bits[j]) = k / 2 ^ j % 2 + 1 := fun j hj => by
    have e := bits_drop k j
    rw [List.drop_eq_getElem_cons hj, bits_eq_cons (hnz j hj)] at e
    rw [(List.cons.inj e).1, symOf_decide]
  have hstep : ∀ (S' : NSt R Q) j (hj : j < n), S'.env t = k / 2 ^ j →
      Good x w B S' (exec x B S') (12 * Ex.nodeCost w) ∧
        (exec x B S').env t = k / 2 ^ (j + 1) ∧
        (exec x B S').stk q = symOf (k.bits[j]'hj) :: 2 :: S'.stk q ∧
        ∀ r, r ≠ t → (exec x B S').env r = S'.env r := by
    intro S' j hj hS'
    have hkj : k / 2 ^ j ≤ k := Nat.div_le_self _ _
    have g := (Good.push (x := x) (w := w) (st := S') (q := q) (e := .const 2)
      (show (2 : ℕ) < 2 ^ w by omega)).seq ((Good.push (q := q) (e := .add (.odd (.var t)) (.const 1))
        (by simp only [Ex.Fits, NSt.setS_env, Ex.eval, hS']; refine ⟨by omega, by omega, ?_⟩
            have := Nat.mod_lt (k / 2 ^ j) (show 2 > 0 by norm_num); omega)).seq
        ((Good.set (r := t) (e := .half (.var t)) (by simp [Ex.Fits, hS']; omega)).seq Good.skip))
    have hex : exec x B S' = _ := g.2.1
    refine ⟨?_, ?_, ?_, fun r hr => ?_⟩
    · rw [hex]; refine g.mono ?_; simp only [Ex.size]; omega
    · rw [hex]; simp [Ex.eval, hS', pow_succ, Nat.div_div_eq_div_mul]
    · rw [hex]; simp [Ex.eval, hS', hbit j hj]
    · rw [hex]; simp [Function.update_of_ne hr]
  have hSj : ∀ j ≤ n, (S j).env t = k / 2 ^ j ∧
      (S j).stk q = (syms (pairs (k.bits.take j))).reverse ++ st.stk q ∧
      ∀ r, r ≠ t → (S j).env r = st.env r := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨by simp [hS, iter_zero, ht], by simp [hS, iter_zero, syms], fun r _ => by
        simp [hS, iter_zero]⟩
    | succ j ih =>
      intro hj
      obtain ⟨i1, i2, i3⟩ := ih (by omega)
      obtain ⟨-, e1, e2, e3⟩ := hstep (S j) j (by omega) i1
      rw [show S (j + 1) = exec x B (S j) from iter_succ _ _ _]
      refine ⟨e1, ?_, fun r hr => by rw [e3 r hr, i3 r hr]⟩
      rw [e2, i2, syms_pairs_take_succ _ _ (by omega)]; rfl
  have hn : k / 2 ^ n = 0 := by
    have := bits_drop k n
    rw [List.drop_length] at this
    exact (Machines.bits_eq_nil_iff _).mp this.symm
  have hloop := Good.loop_const (x := x) (w := w) (e := .var t) (body := B) n S
    (12 * Ex.nodeCost w)
    (fun j hj => by simp [Ex.eval, (hSj j hj.le).1, hnz j hj])
    (by simp [Ex.eval, (hSj n le_rfl).1, hn])
    (fun j hj => by
      simp only [Ex.Fits, (hSj j hj).1]; exact lt_of_le_of_lt (Nat.div_le_self _ _) hk)
    (fun j hj => by
      rw [show S (j + 1) = exec x B (S j) from iter_succ _ _ _]
      exact (hstep (S j) j hj (hSj j hj.le).1).1)
  have hex : exec x (pushBits q t) st = S n := hloop.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hex]; refine hloop.mono ?_; simp only [condCost, Ex.size]; nlinarith
  · rw [hex, (hSj n le_rfl).2.1, List.take_length]
  · rw [hex, (hSj n le_rfl).1, hn]
  · rw [hex]; exact (hSj n le_rfl).2.2

/-! ## Reading the input -/

/-- Push the symbols of the input from the cursor on (reversed). -/
def readIn (q : Fin Q) (t : Fin R) : CStm R Q :=
  .seq (.rd t) (.loop (.var t) (.seq (.push q (.var t)) (.rd t)))

lemma inBit_eq (x : List Bool) (j : ℕ) :
    inBit x j = if h : j < x.length then symOf x[j] else 0 := by
  unfold inBit
  split_ifs with h
  · rw [List.drop_eq_getElem_cons h]; cases x[j] <;> rfl
  · rw [List.drop_eq_nil_of_le (by omega)]; rfl

lemma readIn_good (hw : 2 ≤ w) {q : Fin Q} {t : Fin R} (st : NSt R Q) (hpos : st.pos = 0) :
    Good x w (readIn q t) st (exec x (readIn q t) st) ((x.length + 1) * (8 * Ex.nodeCost w)) ∧
      (exec x (readIn q t) st).stk q = (syms x).reverse ++ st.stk q ∧
      (exec x (readIn q t) st).env t = 0 ∧
      (∀ r, r ≠ t → (exec x (readIn q t) st).env r = st.env r) ∧
      (exec x (readIn q t) st).pos = x.length := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  set B : CStm R Q := .seq (.push q (.var t)) (.rd t) with hB
  set st1 : NSt R Q := exec x (.rd t) st with hst1
  set S : ℕ → NSt R Q := fun j => iter x B st1 j with hS
  have hinb : ∀ j, inBit x j ≤ 2 := fun j => by
    rw [inBit_eq]; split_ifs
    · exact symOf_le _
    · omega
  have hSj : ∀ j ≤ x.length, (S j).env t = inBit x j ∧ (S j).pos = min (j + 1) x.length ∧
      (S j).stk q = (syms (x.take j)).reverse ++ st.stk q ∧
      ∀ r, r ≠ t → (S j).env r = st.env r := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [hS, iter_zero, hst1, exec, NSt.set_env, Function.update_self, hpos]
      refine ⟨by simp, by simp, by simp [syms], fun r hr => by simp [Function.update_of_ne hr]⟩
    | succ j ih =>
      intro hj
      obtain ⟨i1, i2, i3, i4⟩ := ih (by omega)
      rw [show S (j + 1) = exec x B (S j) from iter_succ _ _ _]
      simp only [hB, exec, NSt.set_env, Function.update_self, NSt.set_pos, NSt.setS_pos, i2,
        min_eq_left (show j + 1 ≤ x.length by omega)]
      refine ⟨by simp, by simp, ?_, fun r hr => by simp [Function.update_of_ne hr, i4 r hr]⟩
      simp only [NSt.set_stk, NSt.setS_stk, Function.update_self, Ex.eval, i1, i3, inBit_eq,
        dif_pos (show j < x.length by omega), syms_take_succ _ _ (show j < x.length by omega)]
      rfl
  have hloop := Good.loop_const (x := x) (w := w) (e := .var t) (body := B) x.length S
    (2 * Ex.nodeCost w + 2 * unitCost w)
    (fun j hj => by
      simp only [Ex.eval, (hSj j hj.le).1, inBit_eq, dif_pos hj]; exact (symOf_pos _).ne')
    (by simp only [Ex.eval, (hSj _ le_rfl).1, inBit_eq, dif_neg (lt_irrefl _)])
    (fun j hj => by simp only [Ex.Fits, (hSj j hj).1]; have := hinb j; omega)
    (fun j hj => by
      rw [show S (j + 1) = exec x B (S j) from iter_succ _ _ _]
      refine ((Good.push ?_).seq (Good.rd t)).mono (by simp [Ex.size]; omega)
      simp only [Ex.Fits, (hSj j hj.le).1]; have := hinb j; omega)
  have g : Good x w (readIn q t) st (S x.length) _ := (Good.rd t).seq hloop
  have hex : exec x (readIn q t) st = S x.length := g.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hex]; refine g.mono ?_; simp only [condCost, Ex.size]; nlinarith
  · rw [hex, (hSj _ le_rfl).2.2.1, List.take_length]
  · rw [hex, (hSj _ le_rfl).1, inBit_eq, dif_neg (lt_irrefl _)]
  · rw [hex]; exact (hSj _ le_rfl).2.2.2
  · rw [hex, (hSj _ le_rfl).2.1]; omega

/-! ## Clearing a stack -/

/-- Empty the stack `q`. -/
def clrS (q : Fin Q) (t f : Fin R) : CStm R Q :=
  .seq (.sne f q) (.loop (.var f) (.seq (.pop q t) (.sne f q)))

lemma clrS_good (hw : 2 ≤ w) {q : Fin Q} {t f : Fin R} (htf : t ≠ f) (st : NSt R Q) :
    Good x w (clrS q t f) st (exec x (clrS q t f) st)
        (((st.stk q).length + 1) * (8 * Ex.nodeCost w)) ∧
      (exec x (clrS q t f) st).stk q = [] ∧
      ∀ q', q' ≠ q → (exec x (clrS q t f) st).stk q' = st.stk q' := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h1 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  set l := st.stk q with hl
  set B : CStm R Q := .seq (.pop q t) (.sne f q) with hB
  set st1 : NSt R Q := exec x (.sne f q) st with hst1
  set S : ℕ → NSt R Q := fun j => iter x B st1 j with hS
  have hSj : ∀ j ≤ l.length, (S j).stk q = l.drop j ∧
      (S j).env f = if j < l.length then 1 else 0 := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [hS, iter_zero, hst1, exec, NSt.set_env, Function.update_self, NSt.set_stk,
        List.drop_zero, ← hl]
      refine ⟨by simp, ?_⟩
      cases l <;> simp
    | succ j ih =>
      intro hj
      obtain ⟨i1, -⟩ := ih (by omega)
      rw [show S (j + 1) = exec x B (S j) from iter_succ _ _ _]
      simp only [hB, exec, NSt.set_env, Function.update_self, NSt.set_stk, NSt.setS_stk, i1]
      refine ⟨by simp, ?_⟩
      simp only [List.tail_drop, List.isEmpty_iff, List.drop_eq_nil_iff]
      split_ifs <;> omega
  have hloop := Good.loop_const (x := x) (w := w) (e := .var f) (body := B) l.length S
    (unitCost w + 1 + (2 * unitCost w + 1))
    (fun j hj => by simp [Ex.eval, (hSj j hj.le).2, hj])
    (by simp [Ex.eval, (hSj _ le_rfl).2])
    (fun j hj => by simp only [Ex.Fits, (hSj j hj).2]; split_ifs <;> omega)
    (fun j hj => by
      rw [show S (j + 1) = exec x B (S j) from iter_succ _ _ _]
      exact (Good.pop q t).seq (Good.sne f q))
  have g : Good x w (clrS q t f) st (S l.length) _ := (Good.sne f q).seq hloop
  have hex : exec x (clrS q t f) st = S l.length := g.2.1
  refine ⟨?_, ?_, fun q' hq' => ?_⟩
  · rw [hex]; refine g.mono ?_; simp only [condCost, Ex.size]; nlinarith
  · rw [hex, (hSj _ le_rfl).1, List.drop_length]
  · exact exec_stk_of _ _ (by simp [clrS, wStk, Ne.symm hq'])

end Lax119563Proofs.Computability
