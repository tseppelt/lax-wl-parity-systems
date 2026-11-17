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

end CStm

end Lax119563Proofs.Compiler
