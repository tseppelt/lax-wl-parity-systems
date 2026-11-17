import Lax119563Proofs.Compiler.CStack
import Lax119563Proofs.Compiler.NumStack

/-!
# Parsing the input

The input is read through the cursor (`rd`: `0` at the end, `1` for `false`, `2` for
`true`). Numbers are self-delimiting (`encodeNat v = pairs (Nat.bits v) ++ [false]`).

* `rdNumS r p t`: read the next number into `r` (`p` holds the power of two, `t` the value
  read); `rdNumS_good`, for numbers with fewer than `w` binary digits.
* `skipNumS t`: skip the next number (any size); `skipNumS_good`.
* `rdNumsS q n i r p t`: push the next `n` numbers onto `q` (the last number read on top);
  `rdNumsS_good`.

All specifications give the final state explicitly.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

/-! ## Digit lists -/

lemma drop_pairs : ∀ (ds : List Bool) (j : ℕ), (pairs ds).drop (2 * j) = pairs (ds.drop j)
  | [], j => by simp
  | d :: ds, 0 => by simp
  | d :: ds, j + 1 => by
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, pairs_cons]
    simp only [List.drop_succ_cons, List.drop_succ_cons]
    exact drop_pairs ds j

lemma valBits_append_single : ∀ (l : List Bool) (d : Bool),
    Machines.valBits (l ++ [d]) = Machines.valBits l + d.toNat * 2 ^ l.length
  | [], d => by simp [Machines.valBits]
  | b :: l, d => by
    simp only [List.cons_append, Machines.valBits, valBits_append_single l d, List.length_cons,
      pow_succ]
    ring

lemma valBits_lt : ∀ l : List Bool, Machines.valBits l < 2 ^ l.length
  | [] => by simp [Machines.valBits]
  | b :: l => by
    have := valBits_lt l
    simp only [Machines.valBits, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

lemma valBits_take_succ (ds : List Bool) {j : ℕ} (hj : j < ds.length) :
    Machines.valBits (ds.take (j + 1)) = Machines.valBits (ds.take j) + ds[j].toNat * 2 ^ j := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj]
  simp only [Option.toList_some]
  rw [valBits_append_single, List.length_take, min_eq_left hj.le]

/-- Reading at an offset of the current position. -/
lemma drop_add (x : List Bool) (pos i : ℕ) : x.drop (pos + i) = (x.drop pos).drop i := by
  rw [List.drop_drop]

lemma inBit_pairs_marker {pos : ℕ} {ds : List Bool} {rest : List Bool}
    (h : x.drop pos = pairs ds ++ false :: rest) (j : ℕ) (hjL : j ≤ ds.length) :
    inBit x (pos + 2 * j) = if j < ds.length then 2 else 1 := by
  unfold inBit
  rw [drop_add, h, List.drop_append_of_le_length (by simp; omega), drop_pairs]
  split_ifs with hj
  · obtain ⟨a, l, e⟩ : ∃ a l, ds.drop j = a :: l := ⟨_, _, List.drop_eq_getElem_cons hj⟩
    rw [e, pairs_cons]; rfl
  · rw [List.drop_eq_nil_of_le (by omega)]; rfl

lemma inBit_pairs_digit {pos : ℕ} {ds : List Bool} {rest : List Bool}
    (h : x.drop pos = pairs ds ++ false :: rest) (j : ℕ) (hj : j < ds.length) :
    inBit x (pos + 2 * j + 1) = ds[j].toNat + 1 := by
  unfold inBit
  rw [show pos + 2 * j + 1 = pos + (2 * j + 1) by ring, drop_add, h, ← List.drop_drop,
    List.drop_append_of_le_length (by simp; omega), drop_pairs]
  have e : ds.drop j = ds[j] :: ds.drop (j + 1) := List.drop_eq_getElem_cons hj
  rw [e, pairs_cons]; rfl

lemma length_le_of_drop {pos : ℕ} {l : List Bool} (h : x.drop pos = l) (hl : l ≠ []) :
    pos + l.length = x.length := by
  have h1 := congrArg List.length h
  simp only [List.length_drop] at h1
  have : pos < x.length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by omega)] at h
    exact hl h.symm
  omega

lemma min_succ_eq {a n : ℕ} (h : a + 1 ≤ n) : min (a + 1) n = a + 1 := min_eq_left h

namespace CStm

/-! ## Reading a number -/

/-- `[1 < t]`: the value read is `true`. -/
abbrev isTrue (t : Fin R) : Ex R := .lt (.const 1) (rv t)

/-- Read the next number into `r`. -/
def rdNumS (r p t : Fin R) : CStm R Q :=
  .seq (.set r (.const 0)) (.seq (.set p (.const 1)) (.seq (.rd t)
    (.loop (isTrue t)
      (.seq (.rd t) (.seq (.ite (isTrue t) (.set r (.add (rv r) (rv p))) .skip)
        (.seq (.set p (.add (rv p) (rv p))) (.rd t)))))))

/-- The state of `rdNumS` before iteration `j` (digits `ds`). -/
def rnSt (st : NSt R Q) (r p t : Fin R) (ds : List Bool) (j : ℕ) : NSt R Q :=
  { st with
    env := Function.update (Function.update (Function.update st.env r
      (Machines.valBits (ds.take j))) p (2 ^ j)) t (if j < ds.length then 2 else 1)
    pos := st.pos + 2 * j + 1 }

lemma isTrue_eval (env : Fin R → ℕ) (t : Fin R) :
    (isTrue t).eval env = if 1 < env t then 1 else 0 := rfl

lemma isTrue_fits (hw : 2 ≤ w) {env : Fin R → ℕ} {t : Fin R} (h : env t ≤ 2) :
    (isTrue t).Fits w env := by
  have h4 : (4 : ℕ) ≤ 2 ^ w := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  simp only [isTrue, Ex.Fits, rv]; omega

lemma rdNumS_digits (hw : 2 ≤ w) {r p t : Fin R} (hrp : r ≠ p) (hrt : r ≠ t) (hpt : p ≠ t)
    (st : NSt R Q) (ds : List Bool) (rest : List Bool)
    (hx : x.drop st.pos = pairs ds ++ false :: rest) (hL : ds.length < w) :
    Good x w (rdNumS r p t : CStm R Q) st (rnSt st r p t ds ds.length)
      ((2 * ds.length + 2) * (20 * Ex.nodeCost w)) := by
  have hU := nodeCost_ge w
  have hU' := unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  have hlen : st.pos + (2 * ds.length + 1 + rest.length) = x.length := by
    have := length_le_of_drop hx (by simp)
    simp [List.length_append, length_pairs] at this; omega
  have hpow : ∀ j ≤ ds.length, 2 ^ j < 2 ^ w := fun j hj =>
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  -- environments
  have envT : ∀ j, (rnSt st r p t ds j).env t = if j < ds.length then 2 else 1 := by
    intro j; simp [rnSt]
  have envP : ∀ j, (rnSt st r p t ds j).env p = 2 ^ j := by
    intro j; simp [rnSt, Function.update_of_ne hpt]
  have envR : ∀ j, (rnSt st r p t ds j).env r = Machines.valBits (ds.take j) := by
    intro j; simp [rnSt, Function.update_of_ne hrt, Function.update_of_ne hrp]
  -- the body
  have hbody : ∀ j < ds.length, Good x w
      (.seq (.rd t) (.seq (.ite (isTrue t) (.set r (.add (rv r) (rv p))) .skip)
        (.seq (.set p (.add (rv p) (rv p))) (.rd t))))
      (rnSt st r p t ds j) (rnSt st r p t ds (j + 1)) (14 * Ex.nodeCost w) := by
    intro j hj
    set S := rnSt st r p t ds j
    have hd := inBit_pairs_digit hx j hj
    have hm := inBit_pairs_marker hx (j + 1) (by omega)
    have hvl : Machines.valBits (ds.take j) < 2 ^ j := by
      have := valBits_lt (ds.take j); rwa [List.length_take, min_eq_left hj.le] at this
    have hp1 : 2 ^ (j + 1) < 2 ^ w := hpow (j + 1) (by omega)
    have hvt := valBits_take_succ ds hj
    -- after the first read
    set S₁ : NSt R Q := { (S.set t (inBit x S.pos)) with pos := min (S.pos + 1) x.length }
    have hS₁t : S₁.env t = ds[j].toNat + 1 := by
      simp only [S₁, NSt.set_env, Function.update_self, S, rnSt]; exact hd
    -- the conditional
    set S₂ : NSt R Q := if ds[j] then S₁.set r (S₁.env r + S₁.env p) else S₁
    have hite : Good x w (.ite (isTrue t) (.set r (.add (rv r) (rv p))) .skip) S₁ S₂
        (Ex.nodeCost w * 3 + 1 + (3 * Ex.nodeCost w + unitCost w)) := by
      have hf := isTrue_fits (w := w) hw (env := S₁.env) (t := t)
        (by rw [hS₁t]; cases ds[j] <;> simp)
      have hr1 : S₁.env r = Machines.valBits (ds.take j) := by
        simp only [S₁, NSt.set_env, Function.update_of_ne hrt]; exact envR j
      have hp1' : S₁.env p = 2 ^ j := by
        simp only [S₁, NSt.set_env, Function.update_of_ne hpt]; exact envP j
      cases hdj : ds[j]
      · have hc : (isTrue t).eval S₁.env = 0 := by
          rw [isTrue_eval, hS₁t, hdj]; simp
        refine (Good.iteF hf hc Good.skip).of_eq (by simp [S₂, hdj]) ?_
        simp only [condCost, isTrue, Ex.size, rv]; omega
      · have hc : (isTrue t).eval S₁.env ≠ 0 := by
          rw [isTrue_eval, hS₁t, hdj]; simp
        refine (Good.iteT hf hc (Good.set ?_)).of_eq (by simp [S₂, hdj, Ex.eval, rv]) ?_
        · simp only [Ex.Fits, Ex.eval, rv, hr1, hp1']
          have hj2 : 2 ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
          exact ⟨lt_trans hvl (hpow j hj.le), hpow j hj.le, by omega⟩
        · simp only [condCost, isTrue, Ex.size, rv]; omega
    have hS₂p : S₂.env p = 2 ^ j := by
      have : S₁.env p = 2 ^ j := by
        simp only [S₁, NSt.set_env, Function.update_of_ne hpt]; exact envP j
      by_cases hdj : ds[j] <;> simp [S₂, hdj, Function.update_of_ne hrp.symm, this]
    have hset : Good x w (.set p (.add (rv p) (rv p))) S₂ (S₂.set p (2 ^ j + 2 ^ j))
        (3 * Ex.nodeCost w + unitCost w) := by
      refine (Good.set ?_).of_eq (by simp [Ex.eval, rv, hS₂p]) (by simp [Ex.size, rv])
      simp only [Ex.Fits, Ex.eval, rv, hS₂p]
      have hj2 : 2 ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
      exact ⟨hpow j hj.le, hpow j hj.le, by omega⟩
    have hpos₂ : S₂.pos = st.pos + 2 * j + 2 := by
      have : S₁.pos = st.pos + 2 * j + 2 := by
        simp only [S₁, S, rnSt]; rw [min_succ_eq (by omega)]
      by_cases hdj : ds[j] <;> simp [S₂, hdj, this]
    have hrd2 := Good.rd (x := x) (w := w) (Q := Q) (st := S₂.set p (2 ^ j + 2 ^ j)) t
    refine ((Good.rd t).seq (hite.seq (hset.seq hrd2))).of_eq ?_ ?_
    · have hpos' : (S₂.set p (2 ^ j + 2 ^ j)).pos = st.pos + 2 * (j + 1) := by
        simp only [NSt.set_pos, hpos₂]; ring
      rw [hpos', hm, min_succ_eq (by omega)]
      refine NSt.ext (funext fun q => ?_) ?_ ?_ ?_
      · simp only [NSt.set_env, rnSt]
        by_cases hqt : q = t
        · subst hqt; simp
        · by_cases hqp : q = p
          · subst hqp; simp [Function.update_of_ne hpt, pow_succ, mul_two]
          · by_cases hqr : q = r
            · subst hqr
              simp only [Function.update_of_ne hqt, Function.update_of_ne hqp]
              by_cases hdj : ds[j]
              · simp [S₂, hdj, S₁, S, rnSt, hvt, Function.update_of_ne hrt,
                  Function.update_of_ne hrp, Function.update_of_ne hpt]
              · simp [S₂, hdj, S₁, S, rnSt, hvt, Function.update_of_ne hrt,
                  Function.update_of_ne hrp]
            · simp only [Function.update_of_ne hqt, Function.update_of_ne hqp,
                Function.update_of_ne hqr]
              by_cases hdj : ds[j]
              · simp [S₂, hdj, S₁, S, rnSt, Function.update_of_ne hqt,
                  Function.update_of_ne hqp, Function.update_of_ne hqr]
              · simp [S₂, hdj, S₁, S, rnSt, Function.update_of_ne hqt,
                  Function.update_of_ne hqp, Function.update_of_ne hqr]
      · by_cases hdj : ds[j] <;> simp [S₂, hdj, S₁, S, rnSt]
      · simp [rnSt]; try ring
      · by_cases hdj : ds[j] <;> simp [S₂, hdj, S₁, S, rnSt]
    · omega
  -- the loop
  have hloop := Good.loop_const (x := x) (w := w) (e := isTrue t) ds.length (rnSt st r p t ds)
    (14 * Ex.nodeCost w)
    (fun j hj => by rw [isTrue_eval, envT]; simp [hj])
    (by rw [isTrue_eval, envT]; simp)
    (fun j _ => isTrue_fits hw (by rw [envT]; split_ifs <;> omega))
    hbody
  -- initialization
  have h0 := inBit_pairs_marker hx 0 (Nat.zero_le _)
  set S₀ : NSt R Q := ((st.set r 0).set p 1)
  have hS₀ : { (S₀.set t (inBit x S₀.pos)) with pos := min (S₀.pos + 1) x.length } =
      rnSt st r p t ds 0 := by
      simp only [S₀, NSt.set_pos, Nat.mul_zero, Nat.add_zero] at h0 ⊢
      rw [h0, min_succ_eq (by omega)]
      refine NSt.ext (funext fun q => ?_) rfl (by simp [rnSt]) rfl
      simp only [NSt.set_env, rnSt, Ex.eval, List.take_zero, pow_zero]
      by_cases hqt : q = t
      · subst hqt; simp
      · by_cases hqp : q = p
        · subst hqp; simp [Function.update_of_ne hqt]
        · by_cases hqr : q = r
          · subst hqr; simp [Function.update_of_ne hqt, Function.update_of_ne hqp,
              Machines.valBits]
          · simp [Function.update_of_ne hqt, Function.update_of_ne hqp,
              Function.update_of_ne hqr]
  have h1 : (Ex.const 1 : Ex R).Fits w (st.set r 0).env := by
    simp only [Ex.Fits]; omega
  have hrd0 := Good.rd (x := x) (w := w) (st := S₀) t
  rw [hS₀] at hrd0
  refine ((Good.set (r := r) (st := st) (by simp [Ex.Fits])).seq
    ((Good.set (r := p) h1).seq (hrd0.seq hloop))).mono ?_
  simp only [condCost, isTrue, Ex.size, rv]
  nlinarith

/-- The state after reading the number `v`. -/
def rdNumFinal (st : NSt R Q) (r p t : Fin R) (v : ℕ) : NSt R Q :=
  { st with
    env := Function.update (Function.update (Function.update st.env r v) p
      (2 ^ (Nat.bits v).length)) t 1
    pos := st.pos + (encodeNat v).length }

lemma length_encodeNat (v : ℕ) : (encodeNat v).length = 2 * (Nat.bits v).length + 1 := by
  simp [encodeNat_eq_pairs]

/-- **Reading a number.** -/
lemma rdNumS_good (hw : 2 ≤ w) {r p t : Fin R} (hrp : r ≠ p) (hrt : r ≠ t) (hpt : p ≠ t)
    (st : NSt R Q) (v : ℕ) (rest : List Bool) (hx : x.drop st.pos = encodeNat v ++ rest)
    (hv : (Nat.bits v).length < w) :
    Good x w (rdNumS r p t : CStm R Q) st (rdNumFinal st r p t v)
      (((encodeNat v).length + 1) * (20 * Ex.nodeCost w)) := by
  have hx' : x.drop st.pos = pairs (Nat.bits v) ++ false :: rest := by
    rw [hx, encodeNat_eq_pairs]; simp
  refine (rdNumS_digits hw hrp hrt hpt st (Nat.bits v) rest hx' hv).of_eq ?_
    (by rw [length_encodeNat])
  simp only [rnSt, rdNumFinal, List.take_length, lt_irrefl, if_false, Machines.valBits_bits,
    length_encodeNat]
  simp only [Nat.add_assoc]

/-! ## Skipping a number -/

/-- Skip the next number. -/
def skipNumS (t : Fin R) : CStm R Q :=
  .seq (.rd t) (.loop (isTrue t) (.seq (.rd t) (.rd t)))

/-- The state after skipping the number `v`. -/
def skipNumFinal (st : NSt R Q) (t : Fin R) (v : ℕ) : NSt R Q :=
  { st with env := Function.update st.env t 1, pos := st.pos + (encodeNat v).length }

/-- The state of `skipNumS` before iteration `j`. -/
def skSt (st : NSt R Q) (t : Fin R) (ds : List Bool) (j : ℕ) : NSt R Q :=
  { st with env := Function.update st.env t (if j < ds.length then 2 else 1)
            pos := st.pos + 2 * j + 1 }

/-- **Skipping a number** (of any size). -/
lemma skipNumS_good (hw : 2 ≤ w) {t : Fin R} (st : NSt R Q) (v : ℕ) (rest : List Bool)
    (hx : x.drop st.pos = encodeNat v ++ rest) :
    Good x w (skipNumS t : CStm R Q) st (skipNumFinal st t v)
      (((encodeNat v).length + 1) * (4 * Ex.nodeCost w)) := by
  have hU := nodeCost_ge w
  have hU' := unitCost_ge w
  obtain ⟨ds, hds⟩ : ∃ ds, ds = Nat.bits v := ⟨_, rfl⟩
  have hx' : x.drop st.pos = pairs ds ++ false :: rest := by
    rw [hx, encodeNat_eq_pairs, ← hds]; simp
  have hlen : st.pos + (2 * ds.length + 1 + rest.length) = x.length := by
    have := length_le_of_drop hx' (by simp)
    simp [List.length_append, length_pairs] at this; omega
  set S : ℕ → NSt R Q := skSt st t ds
  have envT : ∀ j, (S j).env t = if j < ds.length then 2 else 1 := by intro j; simp [S, skSt]
  have hbody : ∀ j < ds.length, Good x w (.seq (.rd t) (.rd t)) (S j) (S (j + 1))
      (2 * unitCost w) := by
    intro j hj
    have hm := inBit_pairs_marker hx' (j + 1) (by omega)
    refine ((Good.rd t).seq (Good.rd t)).of_eq ?_ (by omega)
    have e1 : (S j).pos = st.pos + 2 * j + 1 := rfl
    simp only [NSt.set_pos, e1]
    rw [min_succ_eq (by omega), show st.pos + 2 * j + 1 + 1 = st.pos + 2 * (j + 1) by ring, hm,
      min_succ_eq (by omega)]
    refine NSt.ext (funext fun q => ?_) rfl rfl rfl
    by_cases hq : q = t
    · subst hq; simp [S, skSt]
    · simp [S, skSt, Function.update_of_ne hq]
  have hloop := Good.loop_const (x := x) (w := w) (e := isTrue t) ds.length S (2 * unitCost w)
    (fun j hj => by rw [isTrue_eval, envT]; simp [hj])
    (by rw [isTrue_eval, envT]; simp)
    (fun j _ => isTrue_fits hw (by rw [envT]; split_ifs <;> omega))
    hbody
  have h0 := inBit_pairs_marker hx' 0 (Nat.zero_le _)
  have hrd := Good.rd (x := x) (w := w) (st := st) (Q := Q) t
  have e0 : { (st.set t (inBit x st.pos)) with pos := min (st.pos + 1) x.length } = S 0 := by
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    rw [h0, min_succ_eq (by omega)]
    refine NSt.ext (funext fun q => ?_) rfl (by simp [S, skSt]) rfl
    by_cases hq : q = t
    · subst hq; simp [S, skSt]
    · simp [S, skSt, Function.update_of_ne hq]
  rw [e0] at hrd
  refine (hrd.seq hloop).of_eq ?_ ?_
  · refine NSt.ext (funext fun q => ?_) rfl ?_ rfl
    · by_cases hq : q = t
      · subst hq; simp [S, skSt, skipNumFinal]
      · simp [S, skSt, skipNumFinal, Function.update_of_ne hq]
    · simp [S, skSt, skipNumFinal, length_encodeNat, ← hds]; ring
  · simp only [condCost, isTrue, Ex.size, rv, length_encodeNat, ← hds]
    nlinarith

/-! ## Reading a list of numbers -/

/-- Push the next `n` numbers onto `q` (counter `i`, scratch `r p t`). -/
def rdNumsS (q : Fin Q) (n i r p t : Fin R) : CStm R Q :=
  .seq (.set i (.const 0)) (.loop (.lt (rv i) (rv n))
    (.seq (rdNumS r p t) (.seq (.push q (rv r)) (.set i (.add (rv i) (.const 1))))))

/-- The state of `rdNumsS` before iteration `j`. -/
def rnsSt (st : NSt R Q) (q : Fin Q) (i r p t : Fin R) (vs : List ℕ) : ℕ → NSt R Q
  | 0 => st.set i 0
  | j + 1 =>
    let s₁ := rdNumFinal (rnsSt st q i r p t vs j) r p t (vs.getD j 0)
    (s₁.setS q (vs.getD j 0 :: s₁.stk q)).set i (j + 1)

lemma encodeNats_take_succ (vs : List ℕ) {j : ℕ} (hj : j < vs.length) :
    encodeNats (vs.take (j + 1)) = encodeNats (vs.take j) ++ encodeNat vs[j] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj]
  simp only [encodeNats, Option.toList_some, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

lemma lt_of_bits_length {v w : ℕ} (h : (Nat.bits v).length < w) : v < 2 ^ w := by
  have := valBits_lt (Nat.bits v)
  rw [Machines.valBits_bits] at this
  exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) h.le)

lemma sum_getD_eq (f : ℕ → ℕ) : ∀ vs : List ℕ,
    ∑ j ∈ Finset.range vs.length, f (vs.getD j 0) = (vs.map f).sum
  | [] => by simp
  | v :: vs => by
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons,
      ← sum_getD_eq f vs]
    simp [add_comm]

lemma length_encodeNats_sum (vs : List ℕ) :
    (encodeNats vs).length = (vs.map fun v => (encodeNat v).length).sum := by
  simp [encodeNats, List.length_flatMap]

/-- **Reading a list of numbers.** -/
lemma rdNumsS_good (hw : 2 ≤ w) {q : Fin Q} {n i r p t : Fin R} (hin : i ≠ n) (hir : i ≠ r)
    (hip : i ≠ p) (hit : i ≠ t) (hnr : n ≠ r) (hnp : n ≠ p) (hnt : n ≠ t) (hrp : r ≠ p)
    (hrt : r ≠ t) (hpt : p ≠ t) (st : NSt R Q) (vs : List ℕ) (rest : List Bool)
    (hx : x.drop st.pos = encodeNats vs ++ rest) (hn : st.env n = vs.length)
    (hnw : vs.length < 2 ^ w) (hvs : ∀ v ∈ vs, (Nat.bits v).length < w) :
    Good x w (rdNumsS q n i r p t : CStm R Q) st (rnsSt st q i r p t vs vs.length)
        ((((encodeNats vs).length + 2 * vs.length + 1)) * (20 * Ex.nodeCost w)) ∧
      (rnsSt st q i r p t vs vs.length).stk =
        Function.update st.stk q (vs.reverse ++ st.stk q) ∧
      (rnsSt st q i r p t vs vs.length).pos = st.pos + (encodeNats vs).length ∧
      (rnsSt st q i r p t vs vs.length).out = st.out ∧
      ∀ r', r' ≠ i → r' ≠ r → r' ≠ p → r' ≠ t →
        (rnsSt st q i r p t vs vs.length).env r' = st.env r' := by
  have hU := nodeCost_ge w
  have hU' := unitCost_ge w
  set S := rnsSt st q i r p t vs
  -- invariants
  have inv : ∀ j ≤ vs.length,
      (S j).stk = Function.update st.stk q ((vs.take j).reverse ++ st.stk q) ∧
      (S j).pos = st.pos + (encodeNats (vs.take j)).length ∧ (S j).out = st.out ∧
      (S j).env i = j ∧
      ∀ r', r' ≠ i → r' ≠ r → r' ≠ p → r' ≠ t → (S j).env r' = st.env r' := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨by simp [S, rnsSt], by simp [S, rnsSt, encodeNats], rfl, by simp [S, rnsSt],
        fun r' h1 _ _ _ => by simp [S, rnsSt, Function.update_of_ne h1]⟩
    | succ j ih =>
      intro hj
      obtain ⟨i1, i2, i3, i4, i5⟩ := ih (by omega)
      have hg : vs.getD j 0 = vs[j] := List.getD_eq_getElem _ _ (by omega)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · show ((rdNumFinal (S j) r p t (vs.getD j 0)).setS q _).stk = _
        funext q'
        simp only [NSt.setS_stk, rdNumFinal]
        rw [i1, hg]
        by_cases hq : q' = q
        · subst hq
          rw [Function.update_self, Function.update_self, Function.update_self,
            List.take_add_one, List.getElem?_eq_getElem (show j < vs.length by omega),
            Option.toList_some, List.reverse_append, List.reverse_singleton, List.singleton_append,
            List.cons_append]
        · rw [Function.update_of_ne hq, Function.update_of_ne hq, Function.update_of_ne hq]
      · show (rdNumFinal (S j) r p t (vs.getD j 0)).pos = _
        simp only [rdNumFinal, i2, hg, encodeNats_take_succ vs (show j < vs.length by omega),
          List.length_append]; ring
      · show (rdNumFinal (S j) r p t (vs.getD j 0)).out = _
        simp [rdNumFinal, i3]
      · simp only [S, rnsSt, NSt.set_env, Function.update_self]
      · intro r' h1 h2 h3 h4
        simp only [S, rnsSt, NSt.set_env, NSt.setS_env, rdNumFinal, Function.update_of_ne h1,
          Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h4]
        exact i5 r' h1 h2 h3 h4
  have envN : ∀ j ≤ vs.length, (S j).env n = vs.length := fun j hj => by
    rw [(inv j hj).2.2.2.2 n hin.symm hnr hnp hnt, hn]
  have cmpE : ∀ j ≤ vs.length, (Ex.lt (rv i) (rv n) : Ex R).eval (S j).env =
      if j < vs.length then 1 else 0 := fun j hj => by
    simp [Ex.eval, rv, (inv j hj).2.2.2.1, envN j hj]
  -- the body
  set C : ℕ → ℕ := fun j => ((encodeNat (vs.getD j 0)).length + 1) * (20 * Ex.nodeCost w) +
    10 * Ex.nodeCost w
  have hbody : ∀ j < vs.length, Good x w
      (.seq (rdNumS r p t) (.seq (.push q (rv r)) (.set i (.add (rv i) (.const 1)))))
      (S j) (S (j + 1)) (C j) := by
    intro j hj
    obtain ⟨i1, i2, i3, i4, i5⟩ := inv j hj.le
    have hg : vs.getD j 0 = vs[j] := List.getD_eq_getElem _ _ hj
    have hvj := hvs _ (List.getElem_mem hj)
    have hxj : x.drop (S j).pos = encodeNat (vs.getD j 0) ++
        (encodeNats (vs.drop (j + 1)) ++ rest) := by
      have e : encodeNats vs = encodeNats (vs.take j) ++
          (encodeNat vs[j] ++ encodeNats (vs.drop (j + 1))) := by
        conv_lhs => rw [← List.take_append_drop j vs, List.drop_eq_getElem_cons hj]
        simp only [encodeNats, List.flatMap_append, List.flatMap_cons]
      rw [i2, drop_add, hx, e, List.append_assoc, List.drop_left, hg, List.append_assoc]
    have h1 := rdNumS_good (Q := Q) hw hrp hrt hpt (S j) (vs.getD j 0) _ hxj (by rw [hg]; exact hvj)
    set s₁ := rdNumFinal (S j) r p t (vs.getD j 0)
    have hr₁ : s₁.env r = vs.getD j 0 := by
      simp [s₁, rdNumFinal, Function.update_of_ne hrp, Function.update_of_ne hrt]
    have hi₁ : s₁.env i = j := by
      simp [s₁, rdNumFinal, Function.update_of_ne hir, Function.update_of_ne hip,
        Function.update_of_ne hit, i4]
    have hpush := Good.push (x := x) (w := w) (q := q) (e := rv r) (st := s₁)
      (by simp only [Ex.Fits, rv, hr₁, hg]; exact lt_of_bits_length hvj)
    have hset := Good.set (x := x) (w := w) (r := i) (e := Ex.add (rv i) (.const 1))
      (st := s₁.setS q ((rv r : Ex R).eval s₁.env :: s₁.stk q))
      (by
        have h2 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
        simp only [Ex.Fits, Ex.eval, rv, NSt.setS_env, hi₁]; omega)
    refine (h1.seq (hpush.seq hset)).of_eq ?_ ?_
    · show _ = (s₁.setS q (vs.getD j 0 :: s₁.stk q)).set i (j + 1)
      simp [Ex.eval, rv, hr₁, hi₁]
    · simp only [C, Ex.size, rv]; omega
  have hloop := Good.loop (x := x) (w := w) (e := Ex.lt (rv i) (rv n)) vs.length S C
    (fun j hj => by rw [cmpE j hj.le]; simp [hj])
    (by rw [cmpE _ le_rfl]; simp)
    (fun j hj => by
      simp only [Ex.Fits, rv, (inv j hj).2.2.2.1, envN j hj]; omega)
    hbody
  have hinit : Good x w (.set i (.const 0) : CStm R Q) st (S 0) (Ex.nodeCost w + unitCost w) :=
    (Good.set (by simp [Ex.Fits])).of_eq rfl (by simp [Ex.size])
  obtain ⟨i1, i2, i3, -, i5⟩ := inv _ le_rfl
  rw [List.take_of_length_le le_rfl] at i1 i2
  refine ⟨(hinit.seq hloop).mono ?_, i1, i2, i3, i5⟩
  -- the cost
  have hsum : ∑ j ∈ Finset.range vs.length, (C j + condCost w (Ex.lt (rv i) (rv n))) ≤
      ∑ j ∈ Finset.range vs.length,
        ((encodeNat (vs.getD j 0)).length + 2) * (20 * Ex.nodeCost w) := by
    apply Finset.sum_le_sum
    intro j _
    simp only [C, condCost, Ex.size, rv]; nlinarith
  have hsum' : ∑ j ∈ Finset.range vs.length,
      ((encodeNat (vs.getD j 0)).length + 2) * (20 * Ex.nodeCost w) =
      ((encodeNats vs).length + 2 * vs.length) * (20 * Ex.nodeCost w) := by
    rw [← Finset.sum_mul, Finset.sum_add_distrib, sum_getD_eq (fun v => (encodeNat v).length),
      length_encodeNats_sum, Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring
  simp only [condCost, Ex.size, rv] at hsum ⊢
  nlinarith

end CStm

end Lax119563Proofs.Compiler
