import Lax119563Proofs.Compiler.P4SchBits

/-!
# Pass `P4`, schema part: section 1 of a column, the rank part

* `p4Hd`: read the block `i` of the column into `rc1`, update the count of block changes
  `r4Dist` (from the second column on) and `r4Prev` (`p4Hd_good`, `dist1`);
* `p4Blk`: push the codes of the block ranks (`blkCodes`; count in `rc2`) (`p4Blk_good`);
* `p4LT`: the last track position `TP + 2 ((k + 1) n - 1)` into `rc1`, `r4TP += 2 (k + 1) n`
  (`p4LT_good`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-! ## The block of a column -/

/-- The count of block changes after a column with block `i` (column index `K`). -/
def dist1 (K D P i : ℕ) : ℕ := if K = 0 then D else D + (if i = P then 0 else 1)

def p4Hd : CStm CR CQ :=
  .seq (rdNumS rc1 rP rT) (.seq (.ite (rv r4K) (.set r4Dist (.add (rv r4Dist)
      (.lt (.const 0) (.add (.lt (rv rc1) (rv r4Prev)) (.lt (rv r4Prev) (rv rc1)))))) .skip)
    (.set r4Prev (rv rc1)))

set_option maxHeartbeats 2000000 in
lemma p4Hd_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s : NSt CR CQ) {i K D P : ℕ}
    (rest : List Bool) (hx : x.drop s.pos = encodeNat i ++ rest) (hi : (Nat.bits i).length < w)
    (eK : s.env r4K = K) (eD : s.env r4Dist = D) (eP : s.env r4Prev = P)
    (hK : K < 2 ^ w) (hD : D + 1 < 2 ^ w) (hP : P < 2 ^ w) :
    ∃ s', Good x w p4Hd s s' (((encodeNat i).length + 1) * (20 * Ex.nodeCost w) +
        30 * Ex.nodeCost w) ∧
      s'.env rc1 = i ∧ s'.env r4Dist = dist1 K D P i ∧ s'.env r4Prev = i ∧
      s'.pos = s.pos + (encodeNat i).length ∧ s'.stk = s.stk ∧ s'.out = s.out ∧
      ∀ r, r ∉ [rc1, rP, rT, r4Dist, r4Prev] → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
  have hiw : i < 2 ^ w := lt_of_bits_length hi
  obtain ⟨s1, g1, v1, p1, k1, o1, f1⟩ := rdN_good (x := x) hw (r := rc1) (by decide) (by decide)
    s i rest hx hi
  have e1K : s1.env r4K = K := by rw [f1 _ (by decide) (by decide) (by decide), eK]
  have e1D : s1.env r4Dist = D := by rw [f1 _ (by decide) (by decide) (by decide), eD]
  have e1P : s1.env r4Prev = P := by rw [f1 _ (by decide) (by decide) (by decide), eP]
  have hFK : (rv r4K : Ex CR).Fits w s1.env := by simp only [rv, Ex.Fits, e1K]; exact hK
  obtain ⟨s2, g2, e2⟩ : ∃ s2, Good x w (.ite (rv r4K) (.set r4Dist (.add (rv r4Dist)
      (.lt (.const 0) (.add (.lt (rv rc1) (rv r4Prev)) (.lt (rv r4Prev) (rv rc1)))))) .skip)
      s1 s2 (20 * Ex.nodeCost w) ∧ s2 = s1.set r4Dist (dist1 K D P i) := by
    by_cases hK0 : K = 0
    · refine ⟨s1, (CStm.Good.iteF hFK (by simp [rv, Ex.eval, e1K, hK0]) CStm.Good.skip).mono ?_,
        ?_⟩
      · simp only [condCost, rv, Ex.size]; nlinarith
      · rw [dist1, if_pos hK0]
        cases s1; simp only [NSt.set, NSt.mk.injEq, and_true]
        funext r; by_cases h : r = r4Dist
        · subst h; simpa using e1D
        · simp [Function.update_of_ne h]
    · have g := CStm.Good.set (x := x) (w := w) (st := s1) (r := r4Dist)
        (e := .add (rv r4Dist) (.lt (.const 0) (.add (.lt (rv rc1) (rv r4Prev))
          (.lt (rv r4Prev) (rv rc1))))) (by
          simp only [Ex.Fits, rv, Ex.eval, e1D, e1P, v1]
          refine ⟨by omega, ⟨by omega, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_⟩, ?_⟩ <;>
            split_ifs <;> omega)
      refine ⟨_, (CStm.Good.iteT hFK (by simp [rv, Ex.eval, e1K, hK0]) g).mono ?_, ?_⟩
      · simp only [condCost, rv, Ex.size]; nlinarith
      · rw [dist1, if_neg hK0]
        simp only [Ex.eval, rv, e1D, e1P, v1]
        congr 1
        by_cases h : i = P
        · subst h; simp
        · rw [if_neg h]
          rcases Nat.lt_or_gt_of_ne h with h' | h' <;> simp [h', Nat.not_lt.mpr h'.le]
  have e2c : s2.env rc1 = i := by rw [e2]; simp +decide [v1]
  have g3 := CStm.Good.set (x := x) (w := w) (st := s2) (r := r4Prev) (e := rv rc1)
    (by simp only [rv, Ex.Fits, e2c]; exact hiw)
  have ev : (rv rc1 : Ex CR).eval s2.env = i := by simp [rv, Ex.eval, e2c]
  rw [ev] at g3
  refine ⟨_, (g1.seq (g2.seq g3)).mono (by simp only [rv, Ex.size]; nlinarith), ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · simp +decide [e2c]
  · rw [e2]; simp +decide
  · simp
  · simp [e2, p1]
  · simp [e2, k1]
  · simp [e2, o1]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [NSt.set_env, Function.update_of_ne hr.2.2.2.2, e2, Function.update_of_ne hr.2.2.2.1]
    exact f1 r hr.1 hr.2.1 hr.2.2.1

/-! ## The block ranks -/

/-- The rank codes of the block rows of a column with block `i` (`k` blocks, `BR` block rows of
the domain, block-change count `d`). -/
def blkCodes (k BR d i : ℕ) : List ℕ :=
  if i + 1 < k then [rcode (if BR + 1 < k then d else i)] else (List.range (k - 1)).map rcode

/-- All block rows. -/
def blkAll : CStm CR CQ :=
  .seq (.set rc3 (.const 0)) (.seq (.loop (.lt (.add (rv rc3) (.const 1)) (rv rKk))
      (.seq (.push qRk (.add (rv rc3) (.add (rv rc3) (.const 1))))
        (.set rc3 (.add (rv rc3) (.const 1)))))
    (.set rc2 (rv rc3)))

/-- The block ranks. -/
def p4Blk : CStm CR CQ :=
  .seq (.set rc2 (.const 0)) (.ite (.lt (.add (rv rc1) (.const 1)) (rv rKk))
    (.seq (.ite (.lt (.add (rv r4BR) (.const 1)) (rv rKk))
        (.push qRk (.add (rv r4Dist) (.add (rv r4Dist) (.const 1))))
        (.push qRk (.add (rv rc1) (.add (rv rc1) (.const 1)))))
      (.set rc2 (.const 1)))
    blkAll)

set_option maxHeartbeats 4000000 in
lemma blkAll_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s : NSt CR CQ) {k : ℕ}
    (ek : s.env rKk = k) (hk1 : 1 ≤ k) (hk : 2 * k + 2 < 2 ^ w) :
    ∃ s', Good x w blkAll s s' ((k + 1) * (20 * Ex.nodeCost w)) ∧
      s'.stk = Function.update s.stk qRk
        (((List.range (k - 1)).map rcode).reverse ++ s.stk qRk) ∧
      s'.env rc2 = k - 1 ∧ s'.pos = s.pos ∧ s'.out = s.out ∧
      ∀ r, r ≠ rc2 → r ≠ rc3 → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have ga := CStm.Good.set (x := x) (w := w) (st := s) (r := rc3) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  simp only [Ex.eval] at ga
  let P : ℕ → NSt CR CQ → Prop := fun j s' =>
    s'.env rc3 = j ∧ s'.stk = Function.update s.stk qRk
      (((List.range j).map rcode).reverse ++ s.stk qRk) ∧ s'.pos = s.pos ∧ s'.out = s.out ∧
      ∀ r, r ≠ rc3 → s'.env r = s.env r
  have hP0 : P 0 (s.set rc3 0) := by
    refine ⟨by simp, ?_, rfl, rfl, fun r h => by simp [Function.update_of_ne h]⟩
    funext q; by_cases h : q = qRk
    · subst h; simp
    · simp [Function.update_of_ne h]
  obtain ⟨s1, gl, h1, k1, p1, o1, f1⟩ := CStm.Good.loop_idxC (x := x) (w := w)
    (e := .lt (.add (rv rc3) (.const 1)) (rv rKk))
    (body := .seq (.push qRk (.add (rv rc3) (.add (rv rc3) (.const 1))))
      (.set rc3 (.add (rv rc3) (.const 1)))) (k - 1) P (10 * Ex.nodeCost w)
    (by
      rintro j hj s' ⟨e3, ks, ps, os, fs⟩
      have ek' : s'.env rKk = k := by rw [fs _ (by decide), ek]
      refine ⟨by simp only [Ex.Fits, rv, Ex.eval, e3, ek']; omega,
        by simp [Ex.eval, rv, e3, ek']; omega, ?_⟩
      have gp := CStm.Good.push (x := x) (w := w) (st := s') (q := qRk)
        (e := .add (rv rc3) (.add (rv rc3) (.const 1)))
        (by simp only [Ex.Fits, rv, Ex.eval, e3]; omega)
      have gs := CStm.Good.set (x := x) (w := w) (st := s'.setS qRk
        ((Ex.add (rv rc3) (.add (rv rc3) (.const 1)) : Ex CR).eval s'.env :: s'.stk qRk))
        (r := rc3) (e := .add (rv rc3) (.const 1))
        (by simp only [Ex.Fits, rv, Ex.eval, NSt.setS_env, e3]; omega)
      refine ⟨_, (gp.seq gs).mono (by simp only [Ex.size, rv]; nlinarith), ?_, ?_, ps, os, ?_⟩
      · simp [Ex.eval, rv, e3]
      · funext q
        simp only [NSt.set_stk, NSt.setS_stk, Ex.eval, rv, e3, ks]
        by_cases h : q = qRk
        · subst h; simp [List.range_succ, rcode]; ring
        · simp [Function.update_of_ne h]
      · intro r h; simp [Function.update_of_ne h, fs r h])
    (by
      rintro s' ⟨e3, -, -, -, fs⟩
      have ek' : s'.env rKk = k := by rw [fs _ (by decide), ek]
      exact ⟨by simp only [Ex.Fits, rv, Ex.eval, e3, ek']; omega,
        by simp [Ex.eval, rv, e3, ek']; omega⟩)
    _ hP0
  have gb := CStm.Good.set (x := x) (w := w) (st := s1) (r := rc2) (e := rv rc3)
    (by simp only [Ex.Fits, rv, h1]; omega)
  refine ⟨_, (ga.seq (gl.seq gb)).mono ?_, by simp [k1], by simp [Ex.eval, rv, h1], p1, o1, ?_⟩
  · simp only [condCost, Ex.size, rv]
    have : k - 1 + 1 = k := by omega
    nlinarith
  · intro r h2 h3; simp [Function.update_of_ne h2, f1 r h3]

lemma length_blkCodes_pos (k BR d i : ℕ) (hk : 2 ≤ k) : 1 ≤ (blkCodes k BR d i).length := by
  unfold blkCodes; split_ifs <;> simp; omega

set_option maxHeartbeats 4000000 in
lemma p4Blk_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s : NSt CR CQ) {k BR d i : ℕ}
    (e1 : s.env rc1 = i) (ek : s.env rKk = k) (eBR : s.env r4BR = BR) (eD : s.env r4Dist = d)
    (hk1 : 1 ≤ k) (hk : 2 * k + 2 < 2 ^ w) (hi : 2 * i + 2 < 2 ^ w) (hd : 2 * d + 2 < 2 ^ w)
    (hBR : BR + 1 < 2 ^ w) :
    ∃ s', Good x w p4Blk s s' ((k + 2) * (30 * Ex.nodeCost w)) ∧
      s'.stk = Function.update s.stk qRk ((blkCodes k BR d i).reverse ++ s.stk qRk) ∧
      s'.env rc2 = (blkCodes k BR d i).length ∧ s'.pos = s.pos ∧ s'.out = s.out ∧
      ∀ r, r ≠ rc2 → r ≠ rc3 → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have ga := CStm.Good.set (x := x) (w := w) (st := s) (r := rc2) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  simp only [Ex.eval] at ga
  set s1 := s.set rc2 0
  have q1 : ∀ r, r ≠ rc2 → s1.env r = s.env r := fun r h => by simp [s1, Function.update_of_ne h]
  have hC : (Ex.lt (.add (rv rc1) (.const 1)) (rv rKk) : Ex CR).Fits w s1.env := by
    simp only [Ex.Fits, rv, Ex.eval, q1 rc1 (by decide), q1 rKk (by decide), e1, ek]; omega
  by_cases hik : i + 1 < k
  · have hC2 : (Ex.lt (.add (rv r4BR) (.const 1)) (rv rKk) : Ex CR).Fits w s1.env := by
      simp only [Ex.Fits, rv, Ex.eval, q1 r4BR (by decide), q1 rKk (by decide), eBR, ek]; omega
    set v := if BR + 1 < k then d else i with hv
    obtain ⟨s2, g2, e2⟩ : ∃ s2, Good x w (.ite (.lt (.add (rv r4BR) (.const 1)) (rv rKk))
        (.push qRk (.add (rv r4Dist) (.add (rv r4Dist) (.const 1))))
        (.push qRk (.add (rv rc1) (.add (rv rc1) (.const 1))))) s1 s2 (20 * Ex.nodeCost w) ∧
        s2 = s1.setS qRk (rcode v :: s1.stk qRk) := by
      by_cases hb : BR + 1 < k
      · refine ⟨_, (CStm.Good.iteT hC2 (by simp [Ex.eval, rv, q1 r4BR (by decide),
          q1 rKk (by decide), eBR, ek, hb]) (CStm.Good.push (by
            simp only [Ex.Fits, rv, Ex.eval, q1 r4Dist (by decide), eD]; omega))).mono ?_, ?_⟩
        · simp only [condCost, Ex.size, rv]; nlinarith
        · simp [Ex.eval, rv, q1 r4Dist (by decide), eD, hv, hb, rcode]; ring_nf
      · have c0 : (Ex.lt (.add (rv r4BR) (.const 1)) (rv rKk) : Ex CR).eval s1.env = 0 := by
          simp [Ex.eval, rv, q1 r4BR (by decide), q1 rKk (by decide), eBR, ek]; omega
        refine ⟨_, (CStm.Good.iteF hC2 c0 (CStm.Good.push (by
            simp only [Ex.Fits, rv, Ex.eval, q1 rc1 (by decide), e1]; omega))).mono ?_, ?_⟩
        · simp only [condCost, Ex.size, rv]; nlinarith
        · simp [Ex.eval, rv, q1 rc1 (by decide), e1, hv, hb, rcode]; ring_nf
    have g3 := CStm.Good.set (x := x) (w := w) (st := s2) (r := rc2) (e := .const 1)
      (by simp only [Ex.Fits]; omega)
    simp only [Ex.eval] at g3
    refine ⟨_, (ga.seq (CStm.Good.iteT hC (by simp [Ex.eval, rv, q1 rc1 (by decide),
      q1 rKk (by decide), e1, ek, hik]) (g2.seq g3))).mono ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [condCost, Ex.size, rv]; nlinarith
    · rw [e2]; simp [s1, blkCodes, hik, hv]
    · simp [blkCodes, hik]
    · rw [e2]; rfl
    · rw [e2]; rfl
    · intro r h2 h3; rw [e2]; simp [Function.update_of_ne h2, q1 r h2]
  · obtain ⟨s2, g2, k2, e22, p2, o2, f2⟩ := blkAll_good (x := x) hw s1
      (by rw [q1 _ (by decide), ek]) hk1 hk
    have c0 : (Ex.lt (.add (rv rc1) (.const 1)) (rv rKk) : Ex CR).eval s1.env = 0 := by
      simp [Ex.eval, rv, q1 rc1 (by decide), q1 rKk (by decide), e1, ek]; omega
    refine ⟨s2, (ga.seq (CStm.Good.iteF hC c0 g2)).mono ?_, ?_, ?_, p2, o2, ?_⟩
    · simp only [condCost, Ex.size, rv]; nlinarith
    · rw [k2]; simp [s1, blkCodes, hik]
    · rw [e22]; simp [blkCodes, hik]
    · intro r h2 h3; rw [f2 r h2 h3, q1 r h2]

end Lax119563Proofs.Compiler
