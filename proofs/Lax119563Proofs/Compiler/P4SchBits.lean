import Lax119563Proofs.Compiler.P4SchHub
import Lax119563Proofs.Compiler.PEmitRank
import Lax119563Proofs.Compiler.PSch

/-!
# Pass `P4`, schema part: the bit pass of a column (checksum ranks)

`p4Bits`: with the OR bits `os` on `qOrsF` and the column bits `bs` in the input, push the codes
`2 ρ + 1` of the checksum ranks `chkRk os bs BR` on `qRk`, then the terminator `0`; count them
in `rc2`; `qOrsF` is restored (`p4Bits_good`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-! ## Reading a number (wrapper) -/

lemma rdN_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) {r : Fin CR} (hrp : r ≠ rP) (hrt : r ≠ rT)
    (s : NSt CR CQ) (v : ℕ) (rest : List Bool) (hx : x.drop s.pos = encodeNat v ++ rest)
    (hv : (Nat.bits v).length < w) :
    ∃ s', Good x w (rdNumS r rP rT) s s' (((encodeNat v).length + 1) * (20 * Ex.nodeCost w)) ∧
      s'.env r = v ∧ s'.pos = s.pos + (encodeNat v).length ∧ s'.stk = s.stk ∧ s'.out = s.out ∧
      ∀ q, q ≠ r → q ≠ rP → q ≠ rT → s'.env q = s.env q :=
  ⟨_, rdNumS_good hw hrp hrt (by decide) s v rest hx hv, rdNumFinal_env_r hrp hrt v, rfl, rfl,
    rfl, fun _ h1 h2 h3 => rdNumFinal_env_ne h1 h2 h3 v⟩

lemma length_encodeNat_le_one {v : ℕ} (hv : v ≤ 1) : (encodeNat v).length ≤ 3 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hv with rfl | rfl <;> decide

/-! ## Checksum ranks, one bit at a time -/

lemma chkRk_snoc : ∀ (os bs : List ℕ) (o b p : ℕ), os.length = bs.length →
    chkRk (os ++ [o]) (bs ++ [b]) p = chkRk os bs p ++ (if b = 1 then [p + os.sum] else [])
  | [], [], o, b, p, _ => by simp [chkRk]
  | o' :: os, b' :: bs, o, b, p, h => by
    simp only [List.cons_append, chkRk]
    rw [chkRk_snoc os bs o b (p + o') (by simpa using h)]
    simp [List.sum_cons, add_assoc]
  | [], _ :: _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h

lemma chkRk_take_succ (os bs : List ℕ) (p : ℕ) {j : ℕ} (hj : j < bs.length)
    (hl : os.length = bs.length) :
    chkRk (os.take (j + 1)) (bs.take (j + 1)) p = chkRk (os.take j) (bs.take j) p ++
      (if bs[j] = 1 then [p + (os.take j).sum] else []) := by
  rw [List.take_add_one, List.take_add_one, List.getElem?_eq_getElem hj,
    List.getElem?_eq_getElem (by omega), Option.toList_some, Option.toList_some,
    chkRk_snoc _ _ _ _ _ (by simp; omega)]

lemma chkRk_le : ∀ (os bs : List ℕ) (p : ℕ), ∀ v ∈ chkRk os bs p, v ≤ p + os.sum
  | o :: os, b :: bs, p, v, hv => by
    simp only [chkRk, List.mem_append] at hv
    rcases hv with hv | hv
    · split_ifs at hv <;> simp at hv; subst hv; simp
    · have := chkRk_le os bs (p + o) v hv; simp only [List.sum_cons]; omega
  | [], _, _, v, hv => by simp [chkRk] at hv
  | _ :: _, [], _, v, hv => by simp [chkRk] at hv

lemma length_chkRk_le : ∀ (os bs : List ℕ) (p : ℕ), (chkRk os bs p).length ≤ bs.length
  | o :: os, b :: bs, p => by
    simp only [chkRk, List.length_append, List.length_cons]
    have := length_chkRk_le os bs (p + o); split_ifs <;> simp <;> omega
  | [], _, _ => by simp [chkRk]
  | _ :: _, [], _ => by simp [chkRk]

/-- The rank code of a rank. -/
def rcode (ρ : ℕ) : ℕ := 2 * ρ + 1

/-! ## One bit -/

/-- One bit: read `b`, move `o` from `qOrsF` to `qOrsB`, push the code of the rank base `rc1`
if `b = 1` (count in `rc2`), `rc1 += o`, `rc3 += 1`. -/
def p4BitT : CStm CR CQ :=
  .seq (.pop qOrsF rc5) (.seq (.push qOrsB (rv rc5))
    (.seq (.ite (rv rc4) (.seq (.push qRk (.add (rv rc1) (.add (rv rc1) (.const 1))))
        (.set rc2 (.add (rv rc2) (.const 1)))) .skip)
      (.seq (.set rc1 (.add (rv rc1) (rv rc5))) (.set rc3 (.add (rv rc3) (.const 1))))))

def p4Bit : CStm CR CQ := .seq (rdNumS rc4 rP rT) p4BitT

/-- The bit pass. -/
def p4Bits : CStm CR CQ :=
  .seq (.set rc1 (rv r4BR)) (.seq (.set rc3 (.const 0))
    (.seq (.loop (.lt (rv rc3) (rv rL)) p4Bit)
      (.seq (moveAllS qOrsB qOrsF rc3 rc4) (.push qRk (.const 0)))))

/-- Registers written by the bit pass. -/
def bitW : List (Fin CR) := [rc1, rc2, rc3, rc4, rc5, rP, rT]

/-- The state of the bit loop after `j` bits. -/
def bitInv (os bs : List ℕ) (BR n0 P0 : ℕ) (S0 : Fin CQ → List ℕ) (s0 : NSt CR CQ) (j : ℕ)
    (s : NSt CR CQ) : Prop :=
  s.env rc3 = j ∧ s.env rc1 = BR + (os.take j).sum ∧
    s.env rc2 = n0 + (chkRk (os.take j) (bs.take j) BR).length ∧
    s.stk = Function.update (Function.update (Function.update S0 qOrsF (os.drop j)) qOrsB
      (os.take j).reverse) qRk
      (((chkRk (os.take j) (bs.take j) BR).map rcode).reverse ++ S0 qRk) ∧
    s.pos = P0 + (encodeNats (bs.take j)).length ∧ s.out = s0.out ∧
    ∀ r, r ∉ bitW → s.env r = s0.env r

/-- The tail of a bit step with explicit final state. -/
lemma p4BitT_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s : NSt CR CQ) {o b v c j : ℕ}
    {L : List ℕ} (hF : s.stk qOrsF = o :: L) (eb : s.env rc4 = b) (hb : b ≤ 1) (ho : o ≤ 1)
    (e1 : s.env rc1 = v) (e2 : s.env rc2 = c) (e3 : s.env rc3 = j)
    (hv : 2 * v + 2 < 2 ^ w) (hc : c + 1 < 2 ^ w) (hj : j + 1 < 2 ^ w) :
    Good x w p4BitT s
      (((if b = 1 then
          ((((s.setS qOrsF L).set rc5 o).setS qOrsB (o :: s.stk qOrsB)).setS qRk
            ((2 * v + 1) :: s.stk qRk)).set rc2 (c + 1)
        else (((s.setS qOrsF L).set rc5 o).setS qOrsB (o :: s.stk qOrsB))).set rc1
          (v + o)).set rc3 (j + 1)) (30 * Ex.nodeCost w) := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
  have g1 := CStm.Good.pop (x := x) (w := w) (st := s) qOrsF rc5
  rw [hF] at g1
  simp only [List.tail_cons, List.headD_cons] at g1
  set s2 := (s.setS qOrsF L).set rc5 o
  have g2 := CStm.Good.push (x := x) (w := w) (st := s2) (q := qOrsB) (e := rv rc5)
    (by simp [s2, rv, Ex.Fits]; omega)
  have ev2 : (rv rc5 : Ex CR).eval s2.env = o := by simp [s2, rv, Ex.eval]
  rw [ev2] at g2
  set s3 := s2.setS qOrsB (o :: s2.stk qOrsB)
  have e3b : s3.env rc4 = b := by simp +decide [s3, s2, eb]
  have e31 : s3.env rc1 = v := by simp +decide [s3, s2, e1]
  have e32 : s3.env rc2 = c := by simp +decide [s3, s2, e2]
  have hs3 : s2.stk qOrsB = s.stk qOrsB := by simp +decide [s2]
  have hs3' : s3.stk qRk = s.stk qRk := by simp +decide [s3, s2]
  have hFb : (rv rc4 : Ex CR).Fits w s3.env := by simp only [rv, Ex.Fits, e3b]; omega
  obtain ⟨s4, g4, e4⟩ : ∃ s4, Good x w (.ite (rv rc4) (.seq (.push qRk (.add (rv rc1)
      (.add (rv rc1) (.const 1)))) (.set rc2 (.add (rv rc2) (.const 1)))) .skip) s3 s4
      (12 * Ex.nodeCost w) ∧ s4 = if b = 1 then (s3.setS qRk ((2 * v + 1) :: s.stk qRk)).set rc2
        (c + 1) else s3 := by
    by_cases hb1 : b = 1
    · have ga := CStm.Good.push (x := x) (w := w) (st := s3) (q := qRk)
        (e := .add (rv rc1) (.add (rv rc1) (.const 1))) (by simp only [Ex.Fits, rv, Ex.eval, e31]; omega)
      have gb := CStm.Good.set (x := x) (w := w)
        (st := s3.setS qRk ((Ex.add (rv rc1) (.add (rv rc1) (.const 1)) : Ex CR).eval s3.env ::
          s3.stk qRk)) (r := rc2) (e := .add (rv rc2) (.const 1))
        (by simp only [Ex.Fits, rv, Ex.eval, NSt.setS_env, e32]; omega)
      refine ⟨_, (CStm.Good.iteT hFb (by simp [rv, Ex.eval, e3b, hb1]) (ga.seq gb)).mono ?_, ?_⟩
      · simp only [condCost, Ex.size, rv]; nlinarith
      · rw [if_pos hb1]; simp only [Ex.eval, rv, e31, NSt.setS_env, e32, hs3']; ring_nf
    · refine ⟨_, (CStm.Good.iteF hFb (by simp [rv, Ex.eval, e3b]; omega) CStm.Good.skip).mono ?_,
        by rw [if_neg hb1]⟩
      simp only [condCost, Ex.size, rv]; nlinarith
  have e41 : s4.env rc1 = v := by rw [e4]; split_ifs <;> simp +decide [e31]
  have e45 : s4.env rc5 = o := by rw [e4]; split_ifs <;> simp +decide [s3, s2]
  have g5 := CStm.Good.set (x := x) (w := w) (st := s4) (r := rc1) (e := .add (rv rc1) (rv rc5))
    (by simp only [Ex.Fits, rv, Ex.eval, e41, e45]; omega)
  have ev5 : (Ex.add (rv rc1) (rv rc5) : Ex CR).eval s4.env = v + o := by
    simp [Ex.eval, rv, e41, e45]
  rw [ev5] at g5
  have e53 : (s4.set rc1 (v + o)).env rc3 = j := by
    rw [e4]; split_ifs <;> simp +decide [s3, s2, e3]
  have g6 := CStm.Good.set (x := x) (w := w) (st := s4.set rc1 (v + o)) (r := rc3)
    (e := .add (rv rc3) (.const 1)) (by simp only [Ex.Fits, rv, Ex.eval, e53]; omega)
  have ev6 : (Ex.add (rv rc3) (.const 1) : Ex CR).eval (s4.set rc1 (v + o)).env = j + 1 := by
    simp only [Ex.eval, rv, e53]
  rw [ev6] at g6
  refine (g1.seq (g2.seq (g4.seq (g5.seq g6)))).of_eq ?_ ?_
  · rw [e4]; simp only [s3, hs3]
  · simp only [Ex.size, rv]; nlinarith

set_option maxHeartbeats 4000000 in
lemma p4Bit_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (os bs : List ℕ) (BR n0 P0 : ℕ)
    (S0 : Fin CQ → List ℕ) (s0 : NSt CR CQ) (hl : os.length = bs.length)
    (hbs : ∀ b ∈ bs, b ≤ 1) (hos : ∀ o ∈ os, o ≤ 1) (rest : List Bool)
    (hx : x.drop P0 = encodeNats bs ++ rest)
    (hW : 2 * (BR + bs.length) + n0 + 2 < 2 ^ w)
    (j : ℕ) (hj : j < bs.length) (s : NSt CR CQ) (hI : bitInv os bs BR n0 P0 S0 s0 j s) :
    ∃ s', Good x w p4Bit s s' (120 * Ex.nodeCost w) ∧ bitInv os bs BR n0 P0 S0 s0 (j + 1) s' := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  obtain ⟨e3, e1, e2, est, epos, eout, efr⟩ := hI
  have hbj : bs[j] ≤ 1 := hbs _ (List.getElem_mem hj)
  have hjo : j < os.length := by omega
  have hoj : os[j] ≤ 1 := hos _ (List.getElem_mem hjo)
  have hsplit : encodeNats bs = encodeNats (bs.take j) ++
      (encodeNat bs[j] ++ encodeNats (bs.drop (j + 1))) := by
    conv_lhs => rw [← List.take_append_drop j bs, List.drop_eq_getElem_cons hj]
    rw [encodeNats_append, encNats_cons]
  have hx1 : x.drop s.pos = encodeNat bs[j] ++ (encodeNats (bs.drop (j + 1)) ++ rest) := by
    rw [epos, drop_add, hx, hsplit, List.append_assoc, List.drop_left, List.append_assoc]
  obtain ⟨s1, g1, v1, p1, k1, o1, f1⟩ := rdN_good (x := x) hw (r := rc4) (by decide) (by decide)
    s bs[j] _ hx1 (bits_le_one hbj hw)
  have hsum : (os.take j).sum ≤ j := by
    have := List.sum_le_card_nsmul (os.take j) 1 (fun o ho => hos o (List.mem_of_mem_take ho))
    simp at this; omega
  have hcl := length_chkRk_le (os.take j) (bs.take j) BR
  have hcl' : (bs.take j).length = j := by simp; omega
  have hQ : s1.stk qOrsF = os[j] :: os.drop (j + 1) := by
    rw [k1, est, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self, List.drop_eq_getElem_cons hjo]
  have e11 : s1.env rc1 = BR + (os.take j).sum := by rw [f1 _ (by decide) (by decide) (by decide), e1]
  have e12 : s1.env rc2 = n0 + (chkRk (os.take j) (bs.take j) BR).length := by
    rw [f1 _ (by decide) (by decide) (by decide), e2]
  have e13 : s1.env rc3 = j := by rw [f1 _ (by decide) (by decide) (by decide), e3]
  have gT := p4BitT_good (x := x) hw s1 hQ v1 hbj hoj e11 e12 e13 (by omega) (by omega) (by omega)
  refine ⟨_, (g1.seq gT).mono ?_, ?_⟩
  · have := length_encodeNat_le_one hbj
    nlinarith
  have hts := chkRk_take_succ os bs BR hj hl
  have hsum1 : (os.take (j + 1)).sum = (os.take j).sum + os[j] := List.sum_take_succ _ _ hjo
  have htk : (os.take (j + 1)).reverse = os[j] :: (os.take j).reverse := by
    rw [List.take_add_one, List.getElem?_eq_getElem hjo]; simp
  have hB1 : s1.stk qOrsB = (os.take j).reverse := by rw [k1, est]; simp +decide
  have hR1 : s1.stk qRk = ((chkRk (os.take j) (bs.take j) BR).map rcode).reverse ++ S0 qRk := by
    rw [k1, est]; simp +decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · split_ifs <;> simp +decide
  · split_ifs <;> simp +decide [hsum1, e11] <;> ring
  · rw [hts]
    by_cases hb : bs[j] = 1
    · simp +decide [hb, e12]; ring
    · simp +decide [hb, e12]
  · funext q
    rw [hts, htk]
    by_cases hb : bs[j] = 1
    · simp only [hb, if_true]
      by_cases h1 : q = qRk
      · subst h1; simp +decide [hR1, rcode]; (try ring_nf)
      · by_cases h2 : q = qOrsB
        · subst h2; simp +decide [hB1]
        · by_cases h3 : q = qOrsF
          · subst h3; simp +decide
          · simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3, k1,
              est]
    · simp only [hb, if_false, List.append_nil]
      by_cases h1 : q = qRk
      · subst h1; simp +decide [hR1]
      · by_cases h2 : q = qOrsB
        · subst h2; simp +decide [hB1]
        · by_cases h3 : q = qOrsF
          · subst h3; simp +decide
          · simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3, k1,
              est]
  · have : (encodeNats (bs.take (j + 1))).length = (encodeNats (bs.take j)).length +
        (encodeNat bs[j]).length := by rw [encodeNats_take_succ bs hj, List.length_append]
    split_ifs <;> simp [p1, epos, this] <;> ring
  · split_ifs <;> simp [o1, eout]
  · intro r hr
    simp only [bitW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
    have := f1 r h4 h6 h7
    split_ifs <;> simp [Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3, Function.update_of_ne h5, this, efr r (by
        simp [bitW, h1, h2, h3, h4, h5, h6, h7])]


set_option maxHeartbeats 4000000 in
/-- **The bit pass of a column.** -/
lemma p4Bits_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (os bs : List ℕ) (s : NSt CR CQ)
    {BR n0 : ℕ} (hl : os.length = bs.length) (hbs : ∀ b ∈ bs, b ≤ 1) (hos : ∀ o ∈ os, o ≤ 1)
    (rest : List Bool) (hx : x.drop s.pos = encodeNats bs ++ rest)
    (eBR : s.env r4BR = BR) (e2 : s.env rc2 = n0) (eL : s.env rL = bs.length)
    (hF : s.stk qOrsF = os) (hB : s.stk qOrsB = []) (hbd : s.Bdd w) (hpos : s.pos ≤ x.length)
    (hW : 2 * (BR + bs.length) + n0 + 2 < 2 ^ w) :
    ∃ s', Good x w p4Bits s s' ((bs.length + 1) * (200 * Ex.nodeCost w)) ∧
      s'.stk = Function.update s.stk qRk
        (0 :: ((chkRk os bs BR).map rcode).reverse ++ s.stk qRk) ∧
      s'.env rc2 = n0 + (chkRk os bs BR).length ∧
      s'.pos = s.pos + (encodeNats bs).length ∧ s'.out = s.out ∧
      ∀ r, r ∉ bitW → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
  have ga := CStm.Good.set (x := x) (w := w) (st := s) (r := rc1) (e := rv r4BR)
    (by simp only [Ex.Fits, rv, eBR]; omega)
  have gb := CStm.Good.set (x := x) (w := w) (st := s.set rc1 BR) (r := rc3) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  have ev : (rv r4BR : Ex CR).eval s.env = BR := by simp [rv, Ex.eval, eBR]
  rw [ev] at ga
  set sa := (s.set rc1 BR).set rc3 ((Ex.const 0 : Ex CR).eval (s.set rc1 BR).env)
  have hI0 : bitInv os bs BR n0 s.pos s.stk s 0 sa := by
    refine ⟨by simp +decide [sa, Ex.eval], by simp +decide [sa], by simp +decide [sa, e2, chkRk],
      ?_, by simp [sa, encodeNats], by simp [sa], ?_⟩
    · funext q; simp only [sa, NSt.set_stk, List.drop_zero, List.take_zero, List.reverse_nil,
        List.map_nil, List.nil_append]
      by_cases h1 : q = qRk
      · subst h1; simp +decide [chkRk]
      · by_cases h2 : q = qOrsB
        · subst h2; simp +decide [hB]
        · by_cases h3 : q = qOrsF
          · subst h3; simp +decide [hF]
          · simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
    · intro r hr
      simp only [bitW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [sa, Function.update_of_ne hr.1, Function.update_of_ne hr.2.2.1]
  obtain ⟨s1, gl, hI⟩ := CStm.Good.loop_idxC (x := x) (w := w) (e := .lt (rv rc3) (rv rL))
    (body := p4Bit) bs.length (bitInv os bs BR n0 s.pos s.stk s) (120 * Ex.nodeCost w)
    (by
      intro j hj s' hs'
      have e3 := hs'.1
      have eL' : s'.env rL = bs.length := by rw [hs'.2.2.2.2.2.2 _ (by decide), eL]
      refine ⟨by simp only [Ex.Fits, rv, e3, eL']; omega, by simp [Ex.eval, rv, e3, eL', hj], ?_⟩
      exact p4Bit_good hw os bs BR n0 s.pos s.stk s hl hbs hos rest hx hW j hj s' hs')
    (by
      intro s' hs'
      have e3 := hs'.1
      have eL' : s'.env rL = bs.length := by rw [hs'.2.2.2.2.2.2 _ (by decide), eL]
      exact ⟨by simp only [Ex.Fits, rv, e3, eL']; omega, by simp [Ex.eval, rv, e3, eL']⟩)
    sa hI0
  obtain ⟨e3, e1, e2', est, epos, eout, efr⟩ := hI
  have t1 : os.take bs.length = os := List.take_of_length_le (by omega)
  have t2 : bs.take bs.length = bs := List.take_of_length_le (by omega)
  have t3 : os.drop bs.length = [] := List.drop_of_length_le (by omega)
  rw [t1] at e1
  rw [t1, t2] at e2'
  rw [t1, t2, t3] at est
  have hbs1 := ((ga.seq gb).seq gl).bdd hw hbd hpos
  obtain ⟨s2, g2, k2, p2, o2, f2⟩ := moveAllS_good (x := x) hw (q := qOrsB) (q' := qOrsF)
    (t := rc3) (f := rc4) (by decide) (by decide) s1 hbs1.1
  have g3 := CStm.Good.push (x := x) (w := w) (st := s2) (q := qRk) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  have hl2 : (s1.stk qOrsB).length = bs.length := by
    rw [est]; simp +decide; omega
  refine ⟨_, (ga.seq (gb.seq (gl.seq (g2.seq g3)))).mono ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hl2]; simp only [condCost, Ex.size, rv]; nlinarith
  · funext q
    simp only [NSt.setS_stk, k2, est, Ex.eval]
    by_cases h1 : q = qRk
    · subst h1; simp +decide
    · by_cases h2 : q = qOrsB
      · subst h2; simp +decide [hB]
      · by_cases h3 : q = qOrsF
        · subst h3; simp +decide [hF]
        · simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
  · simp only [NSt.setS_env]; rw [f2 _ (by decide) (by decide), e2']
  · simp only [NSt.setS]; rw [p2, epos, t2]
  · simp only [NSt.setS]; rw [o2, eout]
  · intro r hr
    simp only [NSt.setS_env]
    simp only [bitW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [f2 r hr.2.2.1 hr.2.2.2.1]
    exact efr r (by simp [bitW]; tauto)

end Lax119563Proofs.Compiler
