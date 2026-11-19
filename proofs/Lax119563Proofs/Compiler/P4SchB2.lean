import Lax119563Proofs.Compiler.P4SchB1

/-!
# Pass `P4`, schema part: the schema body, the record and the section bases

* `p4OrS`: move the `ℓ` OR bits of the record from `qS2` to `qOrsB`, summing them in `r4R2`
  (**`p4OrS_good`**);
* `p4Rec`: the record transfer (`qOrsF := orsL`, `r4BR, r4NE, r4NC`, `r4R2 := 2 (b + Σ ors)`)
  (**`p4Rec_good`**);
* `p4Bas`: the section bases (`r4H := r4SB`, `r4SuB, r4TrB, r4SP, r4TP`, `r4K, r4Dist := 0`)
  (**`p4Bas_good`**).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-! ## The OR bits -/

/-- One OR bit. -/
def p4OrB : CStm CR CQ :=
  .seq (.pop qS2 rT) (.seq (.push qOrsB (rv rT)) (.seq (.set r4R2 (.add (rv r4R2) (rv rT)))
    (.set rc1 (.add (rv rc1) (.const 1)))))

/-- The OR bits of the record. -/
def p4OrS : CStm CR CQ :=
  .seq (.set rc1 (.const 0)) (.seq (.set r4R2 (.const 0)) (.loop (.lt (rv rc1) (rv rL)) p4OrB))

lemma sum_take_le_length (L : List ℕ) (hL : ∀ v ∈ L, v ≤ 1) (i : ℕ) :
    (L.take i).sum ≤ i := by
  induction L generalizing i with
  | nil => simp
  | cons a t ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.take_succ_cons, List.sum_cons]
      have h1 := hL a (by simp)
      have h2 := ih (fun v hv => hL v (by simp [hv])) i
      omega

set_option maxHeartbeats 4000000 in
lemma p4OrS_good {x : List Bool} {w : ℕ} (s : NSt CR CQ) (L R' : List ℕ)
    (hS : s.stk qS2 = L ++ R') (hL : s.env rL = L.length) (hL1 : ∀ v ∈ L, v ≤ 1)
    (hw : L.length + 2 < 2 ^ w) :
    ∃ s', Good x w p4OrS s s' ((L.length + 1) * (30 * Ex.nodeCost w)) ∧
      s'.stk = Function.update (Function.update s.stk qS2 R') qOrsB (L.reverse ++ s.stk qOrsB) ∧
      s'.env r4R2 = L.sum ∧ s'.pos = s.pos ∧ s'.out = s.out ∧
      ∀ r, r ≠ rT → r ≠ rc1 → r ≠ r4R2 → s'.env r = s.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  set n := L.length with hn
  have r1 := Good.set (x := x) (w := w) (st := s) (r := rc1) (e := .const 0)
    (by simp only [Ex.Fits]; positivity)
  set s1 := s.set rc1 ((Ex.const 0 : Ex CR).eval s.env)
  have r2 := Good.set (x := x) (w := w) (st := s1) (r := r4R2) (e := .const 0)
    (by simp only [Ex.Fits]; positivity)
  set s2 := s1.set r4R2 ((Ex.const 0 : Ex CR).eval s1.env)
  set P : ℕ → NSt CR CQ → Prop := fun i t => t.env rc1 = i ∧ t.env r4R2 = (L.take i).sum ∧
    t.stk = Function.update (Function.update s.stk qS2 (L.drop i ++ R')) qOrsB
      ((L.take i).reverse ++ s.stk qOrsB) ∧ t.pos = s.pos ∧ t.out = s.out ∧
    ∀ r, r ≠ rT → r ≠ rc1 → r ≠ r4R2 → t.env r = s.env r with hP
  have hP0 : P 0 s2 := by
    refine ⟨by simp +decide [s2, s1, Ex.eval], by simp [s2, Ex.eval], ?_, rfl, rfl, ?_⟩
    · simp only [List.drop_zero, List.take_zero, List.reverse_nil, List.nil_append, ← hS]
      simp [s2, s1]
    · intro r h1 h2 h3; simp [s2, s1, Function.update_of_ne h2, Function.update_of_ne h3]
  have hstep : ∀ i < n, ∀ t, P i t → (Ex.lt (rv rc1) (rv rL) : Ex CR).Fits w t.env ∧
      (Ex.lt (rv rc1) (rv rL) : Ex CR).eval t.env ≠ 0 ∧
      ∃ t', Good x w p4OrB t t' (20 * Ex.nodeCost w) ∧ P (i + 1) t' := by
    rintro i hi t ⟨e1, e2, e3, e4, e5, e6⟩
    have eL : t.env rL = n := by rw [e6 _ (by decide) (by decide) (by decide), hL]
    have hsum := sum_take_le_length L hL1 i
    refine ⟨by simp only [Ex.Fits, rv, e1, eL]; omega, by
      simp only [Ex.eval, rv, e1, eL]; rw [if_pos hi]; omega, ?_⟩
    have hti : t.stk qS2 = L[i] :: (L.drop (i + 1) ++ R') := by
      rw [e3, Function.update_of_ne (by decide), Function.update_self,
        List.drop_eq_getElem_cons hi]; rfl
    have hLi : L[i] ≤ 1 := hL1 _ (List.getElem_mem hi)
    have g1 := Good.pop (x := x) (w := w) (st := t) qS2 rT
    set t1 := (t.setS qS2 (t.stk qS2).tail).set rT ((t.stk qS2).headD 0)
    have f1T : t1.env rT = L[i] := by simp [t1, hti]
    have g2 := Good.push (x := x) (w := w) (st := t1) (q := qOrsB) (e := rv rT)
      (by simp only [Ex.Fits, rv, f1T]; omega)
    set t2 := t1.setS qOrsB ((rv rT : Ex CR).eval t1.env :: t1.stk qOrsB)
    have f2R : t2.env r4R2 = (L.take i).sum := by
      simp +decide [t2, t1, Function.update_of_ne (show r4R2 ≠ rT by decide), e2]
    have f2T : t2.env rT = L[i] := f1T
    have g3 := Good.set (x := x) (w := w) (st := t2) (r := r4R2) (e := .add (rv r4R2) (rv rT))
      (by simp only [Ex.Fits, Ex.eval, rv, f2R, f2T]; omega)
    set t3 := t2.set r4R2 ((Ex.add (rv r4R2) (rv rT) : Ex CR).eval t2.env)
    have f3c : t3.env rc1 = i := by
      simp +decide [t3, t2, t1, Function.update_of_ne (show rc1 ≠ rT by decide), e1]
    have g4 := Good.set (x := x) (w := w) (st := t3) (r := rc1) (e := .add (rv rc1) (.const 1))
      (by simp only [Ex.Fits, Ex.eval, rv, f3c]; omega)
    refine ⟨_, (g1.seq (g2.seq (g3.seq g4))).mono ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Ex.size, rv]; omega
    · simp [Ex.eval, rv, f3c]
    · simp +decide [Function.update_of_ne (show r4R2 ≠ rc1 by decide), Ex.eval, rv, f2R, f2T,
        t3]
      rw [List.sum_take_succ _ _ hi]
    · simp only [t3, t2, t1, NSt.setS_stk, NSt.set_stk]
      rw [hti, e3]
      funext q
      by_cases hq : q = qOrsB
      · subst hq
        simp only [Function.update_self, Function.update_of_ne (show qOrsB ≠ qS2 by decide),
          Ex.eval, rv, NSt.set_env, NSt.setS_env, List.headD_cons, List.take_add_one,
          List.getElem?_eq_getElem hi, Option.toList_some, List.reverse_append,
          List.reverse_singleton, List.singleton_append, List.cons_append, List.nil_append]
      by_cases hq2 : q = qS2
      · subst hq2
        simp only [Function.update_self, Function.update_of_ne (show qS2 ≠ qOrsB by decide),
          List.tail_cons]
      simp only [Function.update_of_ne hq, Function.update_of_ne hq2]
    · simp [t3, t2, t1, e4]
    · simp [t3, t2, t1, e5]
    · intro r h1 h2 h3
      simp [t3, t2, t1, Function.update_of_ne h1, Function.update_of_ne h2,
        Function.update_of_ne h3, e6 r h1 h2 h3]
  have hend : ∀ t, P n t → (Ex.lt (rv rc1) (rv rL) : Ex CR).Fits w t.env ∧
      (Ex.lt (rv rc1) (rv rL) : Ex CR).eval t.env = 0 := by
    rintro t ⟨e1, -, -, -, -, e6⟩
    have eL : t.env rL = n := by rw [e6 _ (by decide) (by decide) (by decide), hL]
    exact ⟨by simp only [Ex.Fits, rv, e1, eL]; omega, by simp [Ex.eval, rv, e1, eL]⟩
  obtain ⟨s', g, e1, e2, e3, e4, e5, e6⟩ :=
    Good.loop_idxC (x := x) (w := w) n P (20 * Ex.nodeCost w) hstep hend s2 hP0
  refine ⟨s', (r1.seq (r2.seq g)).mono ?_, ?_, ?_, e4, e5, e6⟩
  · simp only [condCost, Ex.size, rv]
    nlinarith
  · rw [e3, List.drop_of_length_le (by omega), List.take_of_length_le (by omega)]; rfl
  · rw [e2, List.take_of_length_le (by omega)]

/-! ## The record -/

/-- The record transfer. -/
def p4Rec : CStm CR CQ :=
  .seq p4OrS (.seq (moveAllS qOrsB qOrsF rT rP) (.seq (.pop qS2 r4BR) (.seq (.pop qS2 r4NE)
    (.seq (.pop qS2 r4NC) (.seq (.set r4R2 (.add (rv r4R2) (rv r4BR)))
      (.set r4R2 (.add (rv r4R2) (rv r4R2))))))))

set_option maxHeartbeats 4000000 in
lemma p4Rec_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (s : NSt CR CQ) (L R' : List ℕ)
    (b nE nC : ℕ) (hS : s.stk qS2 = L ++ b :: nE :: nC :: R') (hL : s.env rL = L.length)
    (hL1 : ∀ v ∈ L, v ≤ 1) (hF : s.stk qOrsF = []) (hB : s.stk qOrsB = [])
    (hbd : s.Bdd w) (hp : s.pos ≤ x.length) (hbw : 2 * (L.length + b) + 2 < 2 ^ w) :
    ∃ s', Good x w p4Rec s s' ((L.length + 1) * (40 * Ex.nodeCost w) + 30 * Ex.nodeCost w) ∧
      s'.stk = Function.update (Function.update s.stk qS2 R') qOrsF L ∧
      s'.env r4BR = b ∧ s'.env r4NE = nE ∧ s'.env r4NC = nC ∧
      s'.env r4R2 = 2 * (b + L.sum) ∧ s'.pos = s.pos ∧ s'.out = s.out ∧
      ∀ r, r ∉ [rT, rP, rc1, r4R2, r4BR, r4NE, r4NC] → s'.env r = s.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hsum := sum_take_le_length L hL1 L.length
  rw [List.take_length] at hsum
  obtain ⟨s1, g1, h1s, h1R, h1p, h1o, h1f⟩ := p4OrS_good (x := x) (w := w) s L
    (b :: nE :: nC :: R') hS hL hL1 (by omega)
  have hb1 := (g1.bdd hw hbd hp).1
  obtain ⟨s2, g2, h2s, h2p, h2o, h2f⟩ := moveAllS_good (x := x) hw (q := qOrsB) (q' := qOrsF)
    (t := rT) (f := rP) (by decide) (by decide) s1 hb1
  have e2S : s2.stk qS2 = b :: nE :: nC :: R' := by
    rw [h2s, Function.update_of_ne (by decide), Function.update_of_ne (by decide), h1s,
      Function.update_of_ne (by decide), Function.update_self]
  have g3 := Good.pop (x := x) (w := w) (st := s2) qS2 r4BR
  set s3 := (s2.setS qS2 (s2.stk qS2).tail).set r4BR ((s2.stk qS2).headD 0)
  have g4 := Good.pop (x := x) (w := w) (st := s3) qS2 r4NE
  set s4 := (s3.setS qS2 (s3.stk qS2).tail).set r4NE ((s3.stk qS2).headD 0)
  have g5 := Good.pop (x := x) (w := w) (st := s4) qS2 r4NC
  set s5 := (s4.setS qS2 (s4.stk qS2).tail).set r4NC ((s4.stk qS2).headD 0)
  have e5R : s5.env r4R2 = L.sum := by
    simp +decide [s5, s4, s3]; rw [h2f _ (by decide) (by decide), h1R]
  have e5B : s5.env r4BR = b := by simp +decide [s5, s4, s3, e2S]
  have g6 := Good.set (x := x) (w := w) (st := s5) (r := r4R2) (e := .add (rv r4R2) (rv r4BR))
    (by simp only [Ex.Fits, Ex.eval, rv, e5R, e5B]; omega)
  set s6 := s5.set r4R2 ((Ex.add (rv r4R2) (rv r4BR) : Ex CR).eval s5.env)
  have e6R : s6.env r4R2 = L.sum + b := by simp [s6, Ex.eval, rv, e5R, e5B]
  have g7 := Good.set (x := x) (w := w) (st := s6) (r := r4R2) (e := .add (rv r4R2) (rv r4R2))
    (by simp only [Ex.Fits, Ex.eval, rv, e6R]; omega)
  refine ⟨_, (g1.seq (g2.seq (g3.seq (g4.seq (g5.seq (g6.seq g7)))))).mono ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · have hBl : (s1.stk qOrsB).length = L.length := by
      rw [h1s, Function.update_self, hB]; simp
    rw [hBl]; simp only [Ex.size, rv]; nlinarith
  · simp only [NSt.set_stk, s6, s5, s4, s3, NSt.setS_stk]
    rw [h2s, h1s]
    funext q
    by_cases h1 : q = qS2
    · subst h1; simp +decide [e2S]
    by_cases h2 : q = qOrsF
    · subst h2; simp +decide [hF, hB]
    by_cases h3 : q = qOrsB
    · subst h3; simp +decide [hB]
    simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
  · simp +decide [s6, s5, s4, s3, e2S]
  · simp +decide [s6, s5, s4, s3, e2S]
  · simp +decide [s6, s5, s4, s3, e2S]
  · simp [Ex.eval, rv, e6R]; ring
  · simp [s6, s5, s4, s3, h2p, h1p]
  · simp [s6, s5, s4, s3, h2o, h1o]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
    simp [s6, s5, s4, s3, Function.update_of_ne h4, Function.update_of_ne h5,
      Function.update_of_ne h6, Function.update_of_ne h7]
    rw [h2f r h1 h2, h1f r h1 h3 h4]

/-! ## The section bases -/

/-- `r4SB + 2 r4D + 4 r4NE`. -/
def sumEx2 : Ex CR :=
  .add (rv r4SB) (.add (.add (rv r4D) (rv r4D)) (.add (.add (rv r4NE) (rv r4NE))
    (.add (rv r4NE) (rv r4NE))))

/-- `r4SB + 6 r4D + 4 r4NE`. -/
def sumEx6 : Ex CR :=
  .add sumEx2 (.add (.add (rv r4D) (rv r4D)) (.add (rv r4D) (rv r4D)))

/-- The section bases. -/
def p4Bas : CStm CR CQ :=
  .seq (.set r4H (rv r4SB)) (.seq (.set r4K (.const 0)) (.seq (.set r4Dist (.const 0))
    (.seq (.ite (rv r4Tn)
        (.seq (.set r4SuB sumEx6) (.set r4TrB (.add (rv r4SuB) (.add (rv r4D) (rv r4D)))))
        (.seq (.set r4SuB sumEx2) (.set r4TrB (rv r4SuB))))
      (.seq (.set r4SP (rv r4SuB)) (.set r4TP (rv r4TrB))))))

/-- Registers written by `p4Bas`. -/
def basW : List (Fin CR) := [r4H, r4K, r4Dist, r4SuB, r4TrB, r4SP, r4TP]

set_option maxHeartbeats 4000000 in
lemma p4Bas_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (s : NSt CR CQ) {SB D NE T : ℕ}
    (eSB : s.env r4SB = SB) (eD : s.env r4D = D) (eNE : s.env r4NE = NE) (eT : s.env r4Tn = T)
    (hT : T ≤ 1) (hb : SB + 8 * D + 4 * NE < 2 ^ w) :
    ∃ s', Good x w p4Bas s s' (80 * Ex.nodeCost w) ∧
      s'.env r4H = SB ∧ s'.env r4K = 0 ∧ s'.env r4Dist = 0 ∧
      s'.env r4SuB = SB + D * (2 + 4 * T) + 4 * NE ∧
      s'.env r4TrB = SB + D * (2 + 4 * T) + 4 * NE + 2 * T * D ∧
      s'.env r4SP = SB + D * (2 + 4 * T) + 4 * NE ∧
      s'.env r4TP = SB + D * (2 + 4 * T) + 4 * NE + 2 * T * D ∧
      s'.stk = s.stk ∧ s'.pos = s.pos ∧ s'.out = s.out ∧
      ∀ r, r ∉ basW → s'.env r = s.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hlf : lf p4Bas = true := rfl
  have hsc : scost p4Bas ≤ 80 := by decide
  have h2 : (0 : ℕ) < 2 ^ w := by positivity
  have hT01 : T = 0 ∨ T = 1 := by omega
  have hfits : Fits x w p4Bas s := by
    rcases hT01 with rfl | rfl
    · simp +decide [p4Bas, CStm.Fits, CStm.exec, Ex.Fits, Ex.eval, rv, sumEx2, eSB, eD, eNE,
        eT, Function.update_of_ne]
      (repeat' apply And.intro) <;> omega
    · simp +decide [p4Bas, CStm.Fits, CStm.exec, Ex.Fits, Ex.eval, rv, sumEx2, sumEx6, eSB, eD,
        eNE, eT, Function.update_of_ne]
      (repeat' apply And.intro) <;> omega
  refine ⟨_, (good_lf hlf hfits).mono (Nat.mul_le_mul_right _ hsc), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  all_goals rcases hT01 with rfl | rfl
  all_goals simp +decide [p4Bas, CStm.exec, Ex.eval, rv, sumEx2, sumEx6, eSB, eD, eNE, eT,
      Function.update_of_ne, basW]
  all_goals try omega
  all_goals intro r h1 h2 h3 h4 h5 h6 h7
  all_goals simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h4, Function.update_of_ne h5, Function.update_of_ne h6,
      Function.update_of_ne h7]

end Lax119563Proofs.Compiler
