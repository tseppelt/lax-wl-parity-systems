import Lax119563Proofs.Computability.SimLoop

/-!
# Reading a number from a stack, writing a number onto a stack, clearing stacks

Stack routines used to load the input of a simulated machine and to read off its output:
* `skipZ q t`: pop until a nonzero entry (in `t`);
* `parseB q t o p`: having popped the first symbol of `encodeNat v` (stored with `symOf`),
  read `v` into `o` (`parseB_good`);
* `pushCode q t`: push the symbols of `encodeNat (t)` onto `q`, reversed (`pushCode_good`);
* `clrS q t f`: empty the stack `q` (`clrS_good`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler

namespace Lax119563Proofs.Computability

open CStm

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

/-! ## Lists -/

lemma eq_append_drop_of_getD {l m : List ℕ} (h : ∀ i, l.getD i 0 = m.getD i 0)
    (hm : m ≠ []) (hlast : m.getD (m.length - 1) 0 ≠ 0) : l = m ++ l.drop m.length := by
  have hlen : m.length ≤ l.length := by
    by_contra hc
    have := h (m.length - 1)
    rw [List.getD_eq_default _ _ (by omega)] at this
    exact hlast this.symm
  have ht : l.take m.length = m := by
    refine List.ext_getElem (by simp [hlen]) fun i h1 h2 => ?_
    have := h i
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ h2] at this
    simpa using this
  conv_lhs => rw [← List.take_append_drop m.length l, ht]

lemma headD_drop (l : List ℕ) (n : ℕ) : (l.drop n).headD 0 = l.getD n 0 := by
  induction l generalizing n with
  | nil => simp
  | cons a l ih => cases n <;> simp [ih]

lemma bits_eq_cons {k : ℕ} (hk : k ≠ 0) : k.bits = decide (k % 2 = 1) :: (k / 2).bits := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [Nat.bit0_bits n (by omega)]; congr 1
    · simp
    · congr 1; omega
  · rw [Nat.bit1_bits]; congr 1
    · simp [Nat.add_mod]
    · congr 1; omega

lemma bits_drop (k j : ℕ) : k.bits.drop j = (k / 2 ^ j).bits := by
  induction j generalizing k with
  | zero => simp
  | succ j ih =>
    rw [← List.drop_drop, ih]
    rcases Nat.eq_zero_or_pos (k / 2 ^ j) with h | h
    · rw [h, Nat.zero_bits]; simp [pow_succ, ← Nat.div_div_eq_div_mul, h]
    · rw [bits_eq_cons h.ne']
      simp [pow_succ, Nat.div_div_eq_div_mul]

/-- The stack symbols of a list of bits. -/
def syms (l : List Bool) : List ℕ := l.map symOf

lemma symOf_pos (b : Bool) : 0 < symOf b := by cases b <;> simp [symOf]
lemma symOf_le (b : Bool) : symOf b ≤ 2 := by cases b <;> simp [symOf]

/-! ## Skipping zeros -/

/-- `[1 < t]`. -/
def isT (t : Fin R) : Ex R := .lt (.const 1) (.var t)

/-- Pop until a nonzero entry, which is left in `t`. -/
def skipZ (q : Fin Q) (t : Fin R) : CStm R Q :=
  .seq (.pop q t) (.loop (.lt (.var t) (.const 1)) (.pop q t))

lemma skipZ_good (hw : 2 ≤ w) {q : Fin Q} {t : Fin R} (st : NSt R Q) (d a : ℕ)
    (rest : List ℕ) (ha : a ≠ 0) (haw : a < 2 ^ w)
    (hq : st.stk q = List.replicate d 0 ++ a :: rest) :
    Good x w (skipZ q t) st (exec x (skipZ q t) st) ((d + 2) * (6 * Ex.nodeCost w)) ∧
      (exec x (skipZ q t) st).stk q = rest ∧ (exec x (skipZ q t) st).env t = a := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h1 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  set l := List.replicate d 0 ++ a :: rest with hl
  set st1 := exec x (.pop q t : CStm R Q) st with hst1
  set S : ℕ → NSt R Q := fun j => iter x (.pop q t) st1 j with hS
  have hSj : ∀ j ≤ d, (S j).stk q = l.drop (j + 1) ∧ (S j).env t = l.getD j 0 := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨?_, ?_⟩ <;> simp only [S, iter_zero, hst1, exec, NSt.set_stk, NSt.setS_stk,
        Function.update_self, NSt.set_env, hq]
      · simp
      · rw [← headD_drop, List.drop_zero]
    | succ j ih =>
      intro hj
      obtain ⟨i1, i2⟩ := ih (by omega)
      rw [show S (j + 1) = exec x (.pop q t) (S j) from iter_succ _ _ _]
      simp only [exec, NSt.set_stk, NSt.setS_stk, Function.update_self, NSt.set_env,
        Function.update_self, i1]
      refine ⟨by simp, ?_⟩
      rw [headD_drop]
  have hval : ∀ j, j < d → l.getD j 0 = 0 := fun j hj => by
    rw [hl, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hj),
      List.getElem?_replicate]
    simp [hj]
  have hd : l.getD d 0 = a := by
    rw [hl, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp
  have hloop := Good.loop_const (x := x) (w := w) (e := .lt (.var t) (.const 1)) (body := .pop q t)
    d S (unitCost w + 1)
    (fun j hj => by
      rw [show (Ex.lt (.var t) (.const 1) : Ex R).eval (S j).env =
        if (S j).env t < 1 then 1 else 0 from rfl, (hSj j hj.le).2, hval j hj]; simp)
    (by
      rw [show (Ex.lt (.var t) (.const 1) : Ex R).eval (S d).env =
        if (S d).env t < 1 then 1 else 0 from rfl, (hSj d le_rfl).2, hd, if_neg (by omega)])
    (fun j hj => by
      simp only [Ex.Fits, (hSj j hj).2]
      refine ⟨?_, h1⟩
      rcases Nat.lt_or_ge j d with h | h
      · rw [hval j h]; omega
      · rw [show j = d by omega, hd]; exact haw)
    (fun j _ => by rw [show S (j + 1) = exec x (.pop q t) (S j) from iter_succ _ _ _];
                   exact Good.pop _ _)
  have g : Good x w (skipZ q t) st (S d) _ := (Good.pop q t).seq hloop
  rw [g.2.1]
  refine ⟨g.mono ?_, ?_, by rw [(hSj d le_rfl).2, hd]⟩
  · have : d * (unitCost w + 1 + (3 * Ex.nodeCost w + 1)) ≤ d * (6 * Ex.nodeCost w) :=
      Nat.mul_le_mul_left _ (by omega)
    simp only [condCost, Ex.size]; nlinarith
  · rw [(hSj d le_rfl).1, hl]
    clear hSj hval hd hloop g hS hl hq
    induction d with
    | zero => rfl
    | succ d ih => simpa [List.replicate_succ] using ih

/-! ## Parsing -/

/-- Read the digits of a number whose first symbol is in `t` (value into `o`, power of two
in `p`). -/
def parseB (q : Fin Q) (t o p : Fin R) : CStm R Q :=
  .loop (isT t) (seqL [.pop q t, .ite (isT t) (.set o (.add (.var o) (.var p))) .skip,
    .set p (.add (.var p) (.var p)), .pop q t])

lemma isT_eval (env : Fin R → ℕ) (t : Fin R) : (isT t).eval env = if 1 < env t then 1 else 0 := rfl

lemma isT_fits (hw : 2 ≤ w) {env : Fin R → ℕ} {t : Fin R} (h : env t ≤ 2) : (isT t).Fits w env := by
  have h4 : (4 : ℕ) ≤ 2 ^ w := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  simp only [isT, Ex.Fits]; omega

lemma syms_pairs_drop (ds : List Bool) {j : ℕ} (hj : j < ds.length) :
    syms (pairs (ds.drop j) ++ [false]) =
      2 :: symOf ds[j] :: syms (pairs (ds.drop (j + 1)) ++ [false]) := by
  rw [List.drop_eq_getElem_cons hj]
  simp only [syms, pairs_cons, List.map_cons, List.cons_append]
  rfl

lemma syms_head (ds : List Bool) (j : ℕ) :
    (syms (pairs (ds.drop j) ++ [false])).headD 0 = if j < ds.length then 2 else 1 := by
  by_cases hj : j < ds.length
  · rw [syms_pairs_drop ds hj, if_pos hj]; rfl
  · rw [List.drop_eq_nil_of_le (by omega), if_neg hj]; rfl

lemma parse_iter (hw : 2 ≤ w) {q : Fin Q} {t o p : Fin R} (hto : t ≠ o) (htp : t ≠ p)
    (hop : o ≠ p) (S : NSt R Q) (ds : List Bool) (rest : List ℕ) (hL : ds.length < w)
    (j : ℕ) (hj : j < ds.length)
    (h1 : S.stk q = (syms (pairs (ds.drop j) ++ [false])).tail ++ rest)
    (h3 : S.env o = Machines.valBits (ds.take j)) (h4 : S.env p = 2 ^ j) :
    let B : CStm R Q := seqL [.pop q t, .ite (isT t) (.set o (.add (.var o) (.var p))) .skip,
      .set p (.add (.var p) (.var p)), .pop q t]
    Good x w B S (exec x B S) (16 * Ex.nodeCost w) ∧
      (exec x B S).stk q = (syms (pairs (ds.drop (j + 1)) ++ [false])).tail ++ rest ∧
      (exec x B S).env t = (if j + 1 < ds.length then 2 else 1) ∧
      (exec x B S).env o = Machines.valBits (ds.take (j + 1)) ∧
      (exec x B S).env p = 2 ^ (j + 1) := by
  intro B
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have hpj : 2 ^ (j + 1) < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hpj' : 2 ^ j < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hvl : Machines.valBits (ds.take j) < 2 ^ j := by
    have := valBits_lt (ds.take j); rwa [List.length_take, min_eq_left hj.le] at this
  have hvt := valBits_take_succ ds hj
  set rest1 := syms (pairs (ds.drop (j + 1)) ++ [false]) with hr1
  have hne : rest1 ≠ [] := by simp [hr1, syms]
  have hq1 : S.stk q = symOf ds[j] :: (rest1 ++ rest) := by
    rw [h1, syms_pairs_drop ds hj]; rfl
  -- after the first pop
  set S1 : NSt R Q := (S.setS q (rest1 ++ rest)).set t (symOf ds[j]) with hS1
  have g1 : Good x w (.pop q t : CStm R Q) S S1 (unitCost w + 1) :=
    (Good.pop q t).of_eq (by rw [hq1]; rfl) le_rfl
  have hS1o : S1.env o = Machines.valBits (ds.take j) := by
    simp [hS1, Function.update_of_ne hto.symm, h3]
  have hS1p : S1.env p = 2 ^ j := by simp [hS1, Function.update_of_ne htp.symm, h4]
  have hS1t : S1.env t = symOf ds[j] := by simp [hS1]
  -- the conditional
  set S2 : NSt R Q := if ds[j] then S1.set o (Machines.valBits (ds.take j) + 2 ^ j) else S1
    with hS2
  have g2 : Good x w (.ite (isT t) (.set o (.add (.var o) (.var p))) .skip : CStm R Q) S1 S2
      (8 * Ex.nodeCost w) := by
    have hf : (isT t).Fits w S1.env := isT_fits hw (by rw [hS1t]; exact symOf_le _)
    cases hd : ds[j]
    · refine (Good.iteF hf (by rw [isT_eval, hS1t, hd]; simp [symOf]) Good.skip).of_eq
        (by simp [hS2, hd]) ?_
      simp only [condCost, isT, Ex.size]; omega
    · refine (Good.iteT hf (by rw [isT_eval, hS1t, hd]; simp [symOf]) (Good.set ?_)).of_eq
        (by simp [hS2, hd, Ex.eval, hS1o, hS1p]) ?_
      · simp only [Ex.Fits, Ex.eval, hS1o, hS1p]; refine ⟨by omega, hpj', ?_⟩
        rw [pow_succ] at hpj; omega
      · simp only [condCost, isT, Ex.size]; omega
  have hS2p : S2.env p = 2 ^ j := by
    by_cases hd : ds[j] <;> simp [hS2, hd, Function.update_of_ne hop.symm, hS1p]
  have hS2o : S2.env o = Machines.valBits (ds.take (j + 1)) := by
    rw [hvt]; by_cases hd : ds[j] <;> simp [hS2, hd, hS1o]
  have hS2q : S2.stk q = rest1 ++ rest := by by_cases hd : ds[j] <;> simp [hS2, hd, hS1]
  -- doubling
  have g3 : Good x w (.set p (.add (.var p) (.var p)) : CStm R Q) S2 (S2.set p (2 ^ (j + 1)))
      (3 * Ex.nodeCost w + unitCost w) := by
    refine (Good.set ?_).of_eq (by simp [Ex.eval, hS2p, pow_succ, mul_two]) (by simp [Ex.size])
    simp only [Ex.Fits, Ex.eval, hS2p]
    refine ⟨hpj', hpj', ?_⟩; rw [pow_succ] at hpj; omega
  -- the second pop
  have g4 := Good.pop (x := x) (w := w) (st := S2.set p (2 ^ (j + 1))) q t
  have g := g1.seq (g2.seq (g3.seq (g4.seq (Good.skip (x := x) (w := w)))))
  have hex : exec x B S = _ := g.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hex]; exact g.mono (by omega)
  all_goals rw [hex]
  · simp only [NSt.set_stk, NSt.setS_stk, Function.update_self, hS2q]
    obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil hne
    rw [hl]; rfl
  · simp only [NSt.set_env, Function.update_self, NSt.setS_stk, NSt.set_stk, hS2q]
    rw [← syms_head ds (j + 1), ← hr1]
    obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil hne
    rw [hl]; rfl
  · simp [Function.update_of_ne hto.symm, Function.update_of_ne hop, hS2o]
  · simp [Function.update_of_ne htp.symm]

lemma parseB_good (hw : 2 ≤ w) {q : Fin Q} {t o p : Fin R} (hto : t ≠ o) (htp : t ≠ p)
    (hop : o ≠ p) (st : NSt R Q) (ds : List Bool) (rest : List ℕ) (hL : ds.length < w)
    (hq : st.stk q = (syms (pairs ds ++ [false])).tail ++ rest)
    (ht : st.env t = if 0 < ds.length then 2 else 1) (ho : st.env o = 0) (hp : st.env p = 1) :
    Good x w (parseB q t o p) st (exec x (parseB q t o p) st)
        ((ds.length + 1) * (20 * Ex.nodeCost w)) ∧
      (exec x (parseB q t o p) st).env o = Machines.valBits ds ∧
      (exec x (parseB q t o p) st).stk q = rest := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have hpow : ∀ j ≤ ds.length, 2 ^ j < 2 ^ w := fun j hj =>
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  set B : CStm R Q := seqL [.pop q t, .ite (isT t) (.set o (.add (.var o) (.var p))) .skip,
    .set p (.add (.var p) (.var p)), .pop q t] with hB
  set S : ℕ → NSt R Q := fun j => iter x B st j with hS
  have hSj : ∀ j ≤ ds.length,
      (S j).stk q = (syms (pairs (ds.drop j) ++ [false])).tail ++ rest ∧
      (S j).env t = (if j < ds.length then 2 else 1) ∧
      (S j).env o = Machines.valBits (ds.take j) ∧ (S j).env p = 2 ^ j := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [hS, iter_zero, List.drop_zero, List.take_zero]
      exact ⟨hq, ht, by rw [ho]; rfl, by rw [hp]; rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨i1, -, i3, i4⟩ := ih (by omega)
      have := parse_iter (x := x) hw hto htp hop (S j) ds rest hL j (by omega) i1 i3 i4
      rw [show S (j + 1) = exec x B (S j) from iter_succ _ _ _]
      exact ⟨this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2⟩
  have hloop := Good.loop_const (x := x) (w := w) (e := isT t) (body := B) ds.length S
    (16 * Ex.nodeCost w)
    (fun j hj => by rw [isT_eval, (hSj j hj.le).2.1, if_pos hj]; simp)
    (by rw [isT_eval, (hSj _ le_rfl).2.1, if_neg (lt_irrefl _)]; simp)
    (fun j hj => isT_fits hw (by rw [(hSj j hj).2.1]; split_ifs <;> omega))
    (fun j hj => by
      obtain ⟨i1, -, i3, i4⟩ := hSj j hj.le
      have := parse_iter (x := x) hw hto htp hop (S j) ds rest hL j hj i1 i3 i4
      rw [show S (j + 1) = exec x B (S j) from iter_succ _ _ _]
      exact this.1)
  have hex : exec x (parseB q t o p) st = S ds.length := hloop.2.1
  refine ⟨?_, ?_, ?_⟩
  · rw [hex]; refine hloop.mono ?_
    simp only [condCost, isT, Ex.size]
    nlinarith
  · rw [hex, (hSj _ le_rfl).2.2.1, List.take_length]
  · rw [hex, (hSj _ le_rfl).1, List.drop_length]; rfl

end Lax119563Proofs.Computability
