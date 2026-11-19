import Lax119563Proofs.Compiler.P4SchB2

/-!
# Pass `P4`, schema part: the schema body, between the sections and the end

* `p4Mid` (after section 1): rank codes `qRk → qRkF`, the record back onto `qSch` (OR bits from
  `qOrsF`, then `blkRows, nEnt, |coef|`), skip the permutations, `r4Prev := r4TP` (the
  coefficient base), `r4SP := r4SuB`, `r4TP := r4TrB`, `r4K := 0` (**`p4Mid_good`**);
* `p4End`: the next schema base `r4SB := r4Prev + 2 r4NC`, `rJ += 1` (**`p4End_good`**).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-- Between the sections. -/
def p4Mid : CStm CR CQ :=
  .seq (moveAllS qRk qRkF rT rP) (.seq (moveN qOrsF qSch rL rc1 rT)
    (.seq (.push qSch (rv r4BR)) (.seq (.push qSch (rv r4NE)) (.seq (.push qSch (rv r4NC))
      (.seq (.set rc1 (.add (.const 2) (rv r4Tn))) (.seq (mulS rc2 r4PL rc1 rc3)
        (.seq (skipNumsS rc2 rc3 rT) (.seq (.set r4Prev (rv r4TP)) (.seq (.set r4SP (rv r4SuB))
          (.seq (.set r4TP (rv r4TrB)) (.set r4K (.const 0))))))))))))

/-- Registers written by `p4Mid`. -/
def midW : List (Fin CR) := [rT, rP, rc1, rc2, rc3, r4Prev, r4SP, r4TP, r4K]

/-- Scratch registers of `p4Mid`. -/
def midW0 : List (Fin CR) := [rT, rP, rc1, rc2, rc3]

set_option maxHeartbeats 8000000 in
lemma p4Mid_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (s : NSt CR CQ) (Rk O perms : List ℕ)
    (rest : List Bool) {b nE nC T PL TP SuB TrB : ℕ}
    (hRk : s.stk qRk = Rk) (hO : s.stk qOrsF = O) (hL : s.env rL = O.length)
    (eB : s.env r4BR = b) (eNE : s.env r4NE = nE) (eNC : s.env r4NC = nC)
    (eT : s.env r4Tn = T) (hT : T ≤ 1) (ePL : s.env r4PL = PL) (eTP : s.env r4TP = TP)
    (eSu : s.env r4SuB = SuB) (eTr : s.env r4TrB = TrB)
    (hx : x.drop s.pos = encodeNats perms ++ rest) (hpl : perms.length = (2 + T) * PL)
    (hbd : s.Bdd w) (hp : s.pos ≤ x.length) (hPLw : 3 * PL + O.length + 2 < 2 ^ w) :
    ∃ s', Good x w p4Mid s s' (10 * Ex.nodeCost w * Rk.length + 12 * Ex.nodeCost w * O.length +
        40 * Ex.nodeCost w * (encodeNats perms).length + 300 * Ex.nodeCost w) ∧
      s'.stk = Function.update (Function.update (Function.update (Function.update s.stk qRk [])
        qRkF (Rk.reverse ++ s.stk qRkF)) qOrsF []) qSch (nC :: nE :: b :: O.reverse ++ s.stk qSch) ∧
      s'.pos = s.pos + (encodeNats perms).length ∧ s'.out = s.out ∧
      s'.env r4Prev = TP ∧ s'.env r4SP = SuB ∧ s'.env r4TP = TrB ∧ s'.env r4K = 0 ∧
      ∀ r, r ∉ midW → s'.env r = s.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
  -- the rank codes
  obtain ⟨s1, g1, h1s, h1p, h1o, h1f⟩ := moveAllS_good (x := x) hw (q := qRk) (q' := qRkF)
    (t := rT) (f := rP) (by decide) (by decide) s hbd
  have hb1 := (g1.bdd hw hbd hp).1
  have e1 : ∀ r, r ∉ midW0 → s1.env r = s.env r := fun r hr =>
    h1f r (fun h => hr (by simp [h, midW0])) (fun h => hr (by simp [h, midW0]))
  -- the OR bits back onto `qSch`
  have h1O : s1.stk qOrsF = O := by
    rw [h1s, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hO]
  obtain ⟨s2, g2, h2s, h2f⟩ := moveN_good (x := x) (w := w) (src := qOrsF) (dst := qSch)
    (cnt := rL) (i := rc1) (t := rT) (by decide) (by decide) (by decide) (by decide) s1
    (n := O.length) (by rw [e1 _ (by decide), hL]) (by rw [h1O]) (by omega)
    (fun v hv => hb1.2 qOrsF v (List.mem_of_mem_take hv))
  have hb2 := ((g1.seq g2).bdd hw hbd hp).1
  have e2 : ∀ r, r ∉ midW0 → s2.env r = s.env r := fun r hr => by
    rw [h2f.2.2 r (fun h => hr (by simp at h; rcases h with rfl | rfl <;> simp [midW0])), e1 r hr]
  have g3 := Good.push (x := x) (w := w) (st := s2) (q := qSch) (e := rv r4BR)
    (by simp only [Ex.Fits, rv]; exact hb2.1 _)
  set s3 := s2.setS qSch ((rv r4BR : Ex CR).eval s2.env :: s2.stk qSch)
  have g4 := Good.push (x := x) (w := w) (st := s3) (q := qSch) (e := rv r4NE)
    (by simp only [Ex.Fits, rv]; exact hb2.1 _)
  set s4 := s3.setS qSch ((rv r4NE : Ex CR).eval s3.env :: s3.stk qSch)
  have g5 := Good.push (x := x) (w := w) (st := s4) (q := qSch) (e := rv r4NC)
    (by simp only [Ex.Fits, rv]; exact hb2.1 _)
  set s5 := s4.setS qSch ((rv r4NC : Ex CR).eval s4.env :: s4.stk qSch)
  have e5 : ∀ r, s5.env r = s2.env r := fun r => rfl
  have e5T : s5.env r4Tn = T := by rw [e5, e2 _ (by decide), eT]
  have g6 := Good.set (x := x) (w := w) (st := s5) (r := rc1) (e := .add (.const 2) (rv r4Tn))
    (by simp only [Ex.Fits, Ex.eval, rv]; have := e5T; omega)
  set s6 := s5.set rc1 ((Ex.add (.const 2) (rv r4Tn) : Ex CR).eval s5.env)
  have e6c : s6.env rc1 = 2 + T := by simp [s6, Ex.eval, rv, e5T]
  have e6P : s6.env r4PL = PL := by
    simp only [s6, NSt.set_env, Function.update_of_ne (show r4PL ≠ rc1 by decide)]
    rw [e5, e2 _ (by decide), ePL]
  have g7 := mulS_good (x := x) (w := w) hw (dst := rc2) (a := r4PL) (b := rc1) (j := rc3)
    (by decide) (by decide) (by decide) (by decide) (by decide) s6 e6P e6c
    (by have : PL * (2 + T) ≤ 3 * PL := by nlinarith
        omega) (by omega)
  set s7 := (s6.set rc2 (PL * (2 + T))).set rc3 (2 + T)
  have hpos7 : s7.pos = s.pos := by
    simp only [s7, s6, s5, s4, s3, NSt.set_pos, NSt.setS_pos]; rw [h2f.1, h1p]
  obtain ⟨s8, g8, h8s, h8p, h8o, h8f⟩ := skipNumsS_good (Q := CQ) (x := x) hw (n := rc2) (i := rc3)
    (t := rT) (by decide) (by decide) (by decide) s7 perms rest (by rw [hpos7, hx])
    (by simp [s7, Function.update_of_ne (show rc2 ≠ rc3 by decide), hpl]; ring)
    (by rw [hpl]; nlinarith)
  have e8 : ∀ r, r ∉ midW0 → s8.env r = s.env r := fun r hr => by
    rw [h8f r (fun h => hr (by simp [h, midW0])) (fun h => hr (by simp [h, midW0]))]
    simp only [s7, s6, NSt.set_env]
    rw [Function.update_of_ne (fun h => hr (by simp [h, midW0])),
      Function.update_of_ne (fun h => hr (by simp [h, midW0])),
      Function.update_of_ne (fun h => hr (by simp [h, midW0])), e5, e2 r hr]
  have g9 := Good.set (x := x) (w := w) (st := s8) (r := r4Prev) (e := rv r4TP)
    (by simp only [Ex.Fits, rv]; exact ((g1.seq (g2.seq (g3.seq (g4.seq (g5.seq (g6.seq
      (g7.seq g8))))))).bdd hw hbd hp).1.1 _)
  set s9 := s8.set r4Prev ((rv r4TP : Ex CR).eval s8.env)
  have hb9 := ((g1.seq (g2.seq (g3.seq (g4.seq (g5.seq (g6.seq (g7.seq (g8.seq g9)))))))).bdd
    hw hbd hp).1
  have g10 := Good.set (x := x) (w := w) (st := s9) (r := r4SP) (e := rv r4SuB)
    (by simp only [Ex.Fits, rv]; exact hb9.1 _)
  set s10 := s9.set r4SP ((rv r4SuB : Ex CR).eval s9.env)
  have g11 := Good.set (x := x) (w := w) (st := s10) (r := r4TP) (e := rv r4TrB)
    (by simp only [Ex.Fits, rv, s10, NSt.set_env, Function.update_of_ne
          (show r4TrB ≠ r4SP by decide)]; exact hb9.1 _)
  set s11 := s10.set r4TP ((rv r4TrB : Ex CR).eval s10.env)
  have g12 := Good.set (x := x) (w := w) (st := s11) (r := r4K) (e := .const 0)
    (by simp only [Ex.Fits]; positivity)
  refine ⟨_, (g1.seq (g2.seq (g3.seq (g4.seq (g5.seq (g6.seq (g7.seq (g8.seq (g9.seq (g10.seq
    (g11.seq g12))))))))))).mono ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hRl : (s.stk qRk).length = Rk.length := by rw [hRk]
    rw [hRl]
    simp only [Ex.size, rv]
    have hT3 : 2 + T + 1 ≤ 4 := by omega
    have h7 : (2 + T + 1) * (12 * Ex.nodeCost w) ≤ 48 * Ex.nodeCost w := by nlinarith
    have hpe := length_le_encodeNats perms
    have h8 : ((encodeNats perms).length + perms.length + 1) * (20 * Ex.nodeCost w) ≤
        40 * Ex.nodeCost w * (encodeNats perms).length + 20 * Ex.nodeCost w := by nlinarith
    nlinarith
  · simp only [s11, s10, s9, NSt.set_stk]
    rw [h8s]
    simp only [s7, s6, s5, s4, s3, NSt.set_stk, NSt.setS_stk]
    rw [h2s, h1s]
    funext q
    by_cases hq : q = qSch
    · subst hq
      simp only [Function.update_self, movedStk_dst, Ex.eval, rv, NSt.setS_env]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
      rw [e2 _ (by decide), e2 _ (by decide), e2 _ (by decide), eB, eNE, eNC]
      simp only [Function.update_of_ne (show qOrsF ≠ qRkF by decide),
        Function.update_of_ne (show qOrsF ≠ qRk by decide), hO, List.take_length,
        List.cons_append]
    · simp only [Function.update_of_ne hq]
      by_cases hq2 : q = qOrsF
      · subst hq2
        simp only [Function.update_self, movedStk_src _ (show qOrsF ≠ qSch by decide),
          Function.update_of_ne (show qOrsF ≠ qRkF by decide),
          Function.update_of_ne (show qOrsF ≠ qRk by decide), hO, List.drop_length]
      · simp only [Function.update_of_ne hq2, movedStk_other _ hq2 hq, hRk]
  · simp only [s11, s10, s9, NSt.set_pos]; rw [h8p, hpos7]
  · simp only [s11, s10, s9, NSt.set_out]; rw [h8o]
    simp only [s7, s6, s5, s4, s3, NSt.set_out, NSt.setS_out]; rw [h2f.2.1, h1o]
  · simp only [s11, s10, s9, NSt.set_env, Ex.eval, rv]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_self, e8 _ (by decide), eTP]
  · simp only [s11, s10, s9, NSt.set_env, Ex.eval, rv]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self, Function.update_of_ne (by decide), e8 _ (by decide), eSu]
  · simp only [s11, s10, s9, NSt.set_env, Ex.eval, rv]
    rw [Function.update_of_ne (by decide), Function.update_self, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), e8 _ (by decide), eTr]
  · simp [Ex.eval]
  · intro r hr
    simp only [midW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hr
    simp only [s11, s10, s9, NSt.set_env]
    rw [Function.update_of_ne h9, Function.update_of_ne h8, Function.update_of_ne h7,
      Function.update_of_ne h6]
    exact e8 r (by simp [midW0, h1, h2, h3, h4, h5])

/-- The end of the schema body. -/
def p4End : CStm CR CQ :=
  .seq (.set r4SB (.add (rv r4Prev) (.add (rv r4NC) (rv r4NC))))
    (.set rJ (.add (rv rJ) (.const 1)))

lemma p4End_good {x : List Bool} {w : ℕ} (s : NSt CR CQ) {P nC j : ℕ}
    (eP : s.env r4Prev = P) (eC : s.env r4NC = nC) (eJ : s.env rJ = j)
    (hb : P + 2 * nC < 2 ^ w) (hj : j + 1 < 2 ^ w) :
    ∃ s', Good x w p4End s s' (20 * Ex.nodeCost w) ∧ s'.env r4SB = P + 2 * nC ∧
      s'.env rJ = j + 1 ∧ s'.stk = s.stk ∧ s'.pos = s.pos ∧ s'.out = s.out ∧
      ∀ r, r ≠ r4SB → r ≠ rJ → s'.env r = s.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have g1 := Good.set (x := x) (w := w) (st := s) (r := r4SB)
    (e := .add (rv r4Prev) (.add (rv r4NC) (rv r4NC)))
    (by simp only [Ex.Fits, Ex.eval, rv, eP, eC]; omega)
  set s1 := s.set r4SB ((Ex.add (rv r4Prev) (.add (rv r4NC) (rv r4NC)) : Ex CR).eval s.env)
  have e1J : s1.env rJ = j := by
    simp only [s1, NSt.set_env, Function.update_of_ne (show rJ ≠ r4SB by decide)]; exact eJ
  have g2 := Good.set (x := x) (w := w) (st := s1) (r := rJ) (e := .add (rv rJ) (.const 1))
    (by simp only [Ex.Fits, Ex.eval, rv, e1J]; omega)
  refine ⟨_, (g1.seq g2).mono ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · simp only [Ex.size, rv]; omega
  · simp [s1, Ex.eval, rv, eP, eC, Function.update_of_ne (show r4SB ≠ rJ by decide)]; ring
  · simp [Ex.eval, rv, e1J]
  · intro r h1 h2
    simp [s1, Function.update_of_ne h1, Function.update_of_ne h2]

end Lax119563Proofs.Compiler
