import Lax119563Proofs.Compiler.PSchDesc
import Lax119563Proofs.Compiler.CArith

/-!
# Pass `P2` of the compiler program: the schema pre-scan

`p2` (systems with a schema; run after `p1r`, at the position `posAt I W` of `E`, with
`rKk = k`, `rL = ℓ`, `rL1 = ℓ + 1`) reads `E` and scans the schemas. For schema `e` with
`D = coordList (dom I e)` it reads the arity, skips the locations, scans the coordinates
(counting the rows `rowsSum D`, the block changes, whether block `k - 1` occurs, and the OR of
the block coordinates on the stack `qOr`), pushes the record
`schRec I e = orsL D ++ [blkRows D, nEnt I e, |coefSteps I e|]` onto `qSch`, adds
`schSize I e` to `rLB` and skips the permutations (`p2_good`). At the end `rLB = locBase I`.
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

/-! ## Registers and stacks -/

def rKm1 : Fin CR := 17
def rK1 : Fin CR := 18
/-- The running sum of the schema sizes (`locBase` at the end). -/
def rLB : Fin CR := 19
def rTern : Fin CR := 20
def rRows : Fin CR := 21
def rCol : Fin CR := 22
def rDist : Fin CR := 23
def rLast : Fin CR := 24
def rPrev : Fin CR := 25
def rBi : Fin CR := 26
def rB : Fin CR := 27
def rO : Fin CR := 28
def rBR : Fin CR := 29
def rNE : Fin CR := 30
def rNC : Fin CR := 31
def rOrp : Fin CR := 32
def rJ2 : Fin CR := 33
/-- `k (ℓ + 1)`, the length of a permutation description. -/
def rPL : Fin CR := 34
def rPN : Fin CR := 35
/-- The OR of the block coordinates and its scratch stack. -/
def qOr : Fin CQ := 2
def qOr2 : Fin CQ := 3
/-- The schema records. -/
def qSch : Fin CQ := 4

open CStm

/-! ## The program -/

/-- One bit of a coordinate. -/
def p2Bit : CStm CR CQ :=
  .seq (rdNumS rB rP rT) (.seq (.pop qOr rO)
    (.seq (.push qOr2 (.lt (.const 0) (.add (rv rO) (rv rB))))
      (.seq (.set rRows (.add (rv rRows) (rv rB))) (.set rI (.add (rv rI) (.const 1))))))

/-- The bit loop. -/
def p2Bits : CStm CR CQ := .loop (.lt (rv rI) (rv rL)) p2Bit

/-- The block of a coordinate. -/
def p2Blk : CStm CR CQ :=
  .seq (.set rDist (.add (rv rDist)
      (.lt (.const 0) (.add (.lt (rv rBi) (rv rPrev)) (.lt (rv rPrev) (rv rBi))))))
    (.seq (.set rPrev (rv rBi))
      (.seq (.ite (.lt (.add (rv rBi) (.const 1)) (rv rKk))
          (.set rRows (.add (rv rRows) (.const 1)))
          (.seq (.set rRows (.add (rv rRows) (rv rKm1))) (.set rLast (.const 1))))
        (.ite (rv rTern) (.set rCol (.add (rv rCol) (.const 8)))
          (.set rCol (.add (rv rCol) (.const 2))))))

/-- One coordinate. -/
def p2Coord : CStm CR CQ :=
  .seq (rdNumS rBi rP rT) (.seq p2Blk (.seq (.set rI (.const 0)) (.seq p2Bits
    (.seq (moveN qOr2 qOr rL rI rO) (.set rK (.add (rv rK) (.const 1)))))))

/-- `6 a + 2 b`. -/
def six2 (a b : Fin CR) : Ex CR :=
  .add (rv a) (.add (rv a) (.add (rv a) (.add (rv a) (.add (rv a) (.add (rv a)
    (.add (rv b) (rv b)))))))

/-- The numbers of a schema. -/
def p2Fin : CStm CR CQ :=
  .seq (.set rOrp (.const 0)) (.seq (mvSumN qOr qSch rL rI rO rOrp)
    (.seq (.ite (rv rLast) (.set rBR (rv rKm1)) (.set rBR (rv rDist)))
      (.seq (.push qSch (rv rBR)) (.seq (.set rBR (.add (rv rBR) (rv rOrp)))
        (.seq (mulS rNE rRows rK1 rJ2) (.seq (mulS rNC rBR rK1 rJ2)
          (.seq (.push qSch (rv rNE)) (.seq (.push qSch (rv rNC))
            (.set rLB (.add (rv rLB) (.add (rv rCol) (six2 rNE rNC))))))))))))

/-- The initialisation of the coordinate scan. -/
def p2Init : CStm CR CQ :=
  .seq (.set rRows (.const 0)) (.seq (.set rCol (.const 0)) (.seq (.set rDist (.const 0))
    (.seq (.set rLast (.const 0)) (.seq (.set rPrev (rv rKk)) (.set rK (.const 0))))))

/-- One schema. -/
def p2Sch : CStm CR CQ :=
  .seq (rdNumS rA rP rT) (.seq (.set rTern (.lt (.const 2) (rv rA)))
    (.seq (skipNumsS rA rI rT) (.seq (rdNumS rD rP rT) (.seq p2Init
      (.seq (pushZS qOr rL rI) (.seq (.loop (.lt (rv rK) (rv rD)) p2Coord)
        (.seq p2Fin (.seq (mulS rPN rPL rA rJ2) (.seq (skipNumsS rPN rI rT)
          (.set rJ (.add (rv rJ) (.const 1))))))))))))

/-- **Pass `P2`.** -/
def p2 : CStm CR CQ :=
  .seq (rdNumS rE rP rT) (.seq (predS rKm1 rKk)
    (.seq (.set rK1 (.add (rv rKk) (.const 1))) (.seq (mulS rPL rKk rL1 rJ2)
      (.seq (.set rLB (.const 0)) (.seq (.set rJ (.const 0))
        (.loop (.lt (rv rJ) (rv rE)) p2Sch))))))

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The record of schema `e`. -/
noncomputable def schRec (e : Fin I.schemas.length) : List ℕ :=
  orsL (coordList (dom I e)) ++ [blkRows (coordList (dom I e)), nEnt I e, (coefSteps I e).length]

/-- The records of the first `j` schemas. -/
noncomputable def schRecsUpTo (j : ℕ) : List ℕ :=
  ((List.finRange I.schemas.length).take j).flatMap (schRec I)

/-! ## The bit loop -/

lemma bor_le (a b : ℕ) : bor a b ≤ 1 := by unfold bor; split_ifs <;> omega

/-- The invariant of the bit loop (bits `bs`, OR bits `ors`, start position `B`, stacks `S0`
with `S0 qOr2 = []`, row count `R0`). -/
def p2BitInv (bs ors : List ℕ) (B R0 : ℕ) (S0 : Fin CQ → List ℕ) (O : List ℕ) (s : NSt CR CQ) :
    Prop :=
  s.env rI ≤ bs.length ∧ s.env rL = bs.length ∧
    s.pos = B + (encodeNats (bs.take (s.env rI))).length ∧
    s.env rRows = R0 + (bs.take (s.env rI)).sum ∧
    s.stk = Function.update (Function.update S0 qOr (ors.drop (s.env rI))) qOr2
      (List.zipWith bor (ors.take (s.env rI)) (bs.take (s.env rI))).reverse ∧ s.out = O

lemma bits_le_one {v w : ℕ} (hv : v ≤ 1) (hw : 2 ≤ w) : (Nat.bits v).length < w := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hv with rfl | rfl <;> simp <;> omega

set_option maxHeartbeats 800000 in
lemma p2Bit_good {w : ℕ} (hw : 2 ≤ w) (bs ors : List ℕ) (hbs : ∀ b ∈ bs, b ≤ 1)
    (hors : ∀ o ∈ ors, o ≤ 1)
    (hlen : ors.length = bs.length) (B R0 : ℕ) (S0 : Fin CQ → List ℕ) (O : List ℕ)
    (rest : List Bool) (hx : (encodeSystem I).drop B = encodeNats bs ++ rest)
    (hS0 : S0 qOr2 = []) (hR : R0 + bs.sum + 1 < 2 ^ w) (hbw : bs.length + 1 < 2 ^ w)
    (s : NSt CR CQ) (hI : p2BitInv bs ors B R0 S0 O s)
    (hc : (Ex.lt (rv rI) (rv rL)).eval s.env ≠ 0) :
    ∃ s', Good (encodeSystem I) w p2Bit s s'
        (40 * Ex.nodeCost w * ((B + (encodeNats bs).length - s.pos) -
          (B + (encodeNats bs).length - s'.pos)) + 40 * Ex.nodeCost w) ∧
      p2BitInv bs ors B R0 S0 O s' ∧ bs.length - s'.env rI < bs.length - s.env rI ∧
      B + (encodeNats bs).length - s'.pos ≤ B + (encodeNats bs).length - s.pos := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  obtain ⟨hi, hL, hpos, hrows, hstk, hout⟩ := hI
  have hlt : s.env rI < bs.length := by
    by_contra h; apply hc; simp only [Ex.eval, rv, hL]; rw [if_neg h]
  set i := s.env rI with hidef
  have hsplit : bs = bs.take i ++ (bs[i] :: bs.drop (i + 1)) := by
    rw [← List.drop_eq_getElem_cons hlt, List.take_append_drop]
  have hx1 : (encodeSystem I).drop s.pos = encodeNat bs[i] ++
      (encodeNats (bs.drop (i + 1)) ++ rest) := by
    have he : encodeNats bs = encodeNats (bs.take i) ++
        (encodeNat bs[i] ++ encodeNats (bs.drop (i + 1))) := by
      conv_lhs => rw [hsplit]
      rw [encodeNats_append, encNats_cons]
    rw [hpos, drop_add, hx, he, List.append_assoc, List.drop_left, List.append_assoc]
  have hbi : bs[i] ≤ 1 := hbs _ (List.getElem_mem hlt)
  have r1 := rdNumS_good (Q := CQ) hw (r := rB) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s bs[i] _ hx1 (bits_le_one hbi hw)
  set s1 := rdNumFinal s rB rP rT bs[i]
  have e1 : ∀ q, q ≠ rB → q ≠ rP → q ≠ rT → s1.env q = s.env q :=
    fun q h1 h2 h3 => rdNumFinal_env_ne h1 h2 h3 _
  have e1B : s1.env rB = bs[i] := rdNumFinal_env_r (by decide) (by decide) _
  have hilo : i < ors.length := by omega
  have hdo : ors.drop i = ors[i] :: ors.drop (i + 1) := List.drop_eq_getElem_cons hilo
  have hq1 : s1.stk qOr = ors[i] :: ors.drop (i + 1) := by
    simp only [s1, rdNumFinal_stk, hstk, Function.update_of_ne (show qOr ≠ qOr2 by decide),
      Function.update_self, hdo]
  have r2 := Good.pop (x := encodeSystem I) (w := w) (st := s1) qOr rO
  set s2 := (s1.setS qOr (s1.stk qOr).tail).set rO ((s1.stk qOr).headD 0)
  have e2O : s2.env rO = ors[i] := by
    simp only [s2, NSt.set_env, Function.update_self, hq1, List.headD_cons]
  have e2B : s2.env rB = bs[i] := by simp [s2, Function.update_of_ne (show rB ≠ rO by decide), e1B]
  have hoi : ors[i] ≤ 1 := hors _ (List.getElem_mem hilo)
  have r3 := Good.push (x := encodeSystem I) (w := w) (st := s2) (q := qOr2)
    (e := .lt (.const 0) (.add (rv rO) (rv rB))) (by
      have h4 : 4 ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
      simp only [Ex.Fits, Ex.eval, rv, e2O, e2B]; omega)
  set s3 := s2.setS qOr2 ((Ex.lt (.const 0) (.add (rv rO) (rv rB))).eval s2.env :: s2.stk qOr2)
  have e3R : s3.env rRows = R0 + (bs.take i).sum := by
    simp only [s3, s2, NSt.setS_env, NSt.set_env, Function.update_of_ne (show rRows ≠ rO by decide)]
    rw [e1 _ (by decide) (by decide) (by decide), hrows]
  have e3B : s3.env rB = bs[i] := e2B
  have hsum1 : (bs.take (i + 1)).sum = (bs.take i).sum + bs[i] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, List.sum_append,
      List.sum_singleton]
  have hsumle : (bs.take (i + 1)).sum ≤ bs.sum := by
    conv_rhs => rw [← List.take_append_drop (i + 1) bs]
    rw [List.sum_append]; omega
  have r4 := Good.set (x := encodeSystem I) (w := w) (st := s3) (r := rRows)
    (e := .add (rv rRows) (rv rB)) (by simp only [Ex.Fits, Ex.eval, rv, e3R, e3B]; omega)
  set s4 := s3.set rRows ((Ex.add (rv rRows) (rv rB)).eval s3.env)
  have e4I : s4.env rI = i := by
    simp only [s4, s3, s2, NSt.set_env, NSt.setS_env,
      Function.update_of_ne (show rI ≠ rRows by decide), Function.update_of_ne (show rI ≠ rO by decide)]
    rw [e1 _ (by decide) (by decide) (by decide)]
  have r5 := Good.set (x := encodeSystem I) (w := w) (st := s4) (r := rI)
    (e := .add (rv rI) (.const 1)) (by simp only [Ex.Fits, Ex.eval, rv, e4I]; omega)
  set s5 := s4.set rI ((Ex.add (rv rI) (.const 1)).eval s4.env)
  have e5I : s5.env rI = i + 1 := by simp [s5, Ex.eval, e4I]
  have e5 : ∀ q, q ≠ rI → q ≠ rRows → q ≠ rO → q ≠ rB → q ≠ rP → q ≠ rT →
      s5.env q = s.env q := by
    intro q h1 h2 h3 h4 h5 h6
    simp only [s5, s4, s3, s2, NSt.set_env, NSt.setS_env, Function.update_of_ne h1,
      Function.update_of_ne h2, Function.update_of_ne h3]
    exact e1 q h4 h5 h6
  have e5R : s5.env rRows = R0 + (bs.take (i + 1)).sum := by
    simp only [s5, s4, NSt.set_env, Function.update_of_ne (show rRows ≠ rI by decide),
      Function.update_self, Ex.eval, rv, e3R, e3B, hsum1]; ring
  have hp5 : s5.pos = s.pos + (encodeNat bs[i]).length := rfl
  have hlen1 : (encodeNats (bs.take (i + 1))).length =
      (encodeNats (bs.take i)).length + (encodeNat bs[i]).length := by
    rw [encodeNats_take_succ bs hlt, List.length_append]
  have hle : (encodeNats (bs.take (i + 1))).length ≤ (encodeNats bs).length := by
    conv_rhs => rw [← List.take_append_drop (i + 1) bs]
    rw [encodeNats_append, List.length_append]; omega
  have hev : 1 ≤ (encodeNat bs[i]).length := by rw [length_encodeNat]; omega
  refine ⟨s5, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hp5]
    have hΔ : B + (encodeNats bs).length - s.pos -
        (B + (encodeNats bs).length - (s.pos + (encodeNat bs[i]).length)) =
        (encodeNat bs[i]).length := by omega
    rw [hΔ]
    simp only [Ex.size, rv]
    generalize Ex.nodeCost w = N at *
    generalize unitCost w = U at *
    generalize (encodeNat bs[i]).length = lv at *
    nlinarith
  · rw [e5I]; omega
  · rw [e5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hL]
  · rw [e5I, hp5, hpos, hlen1]; ring
  · rw [e5I, e5R]
  · show Function.update s2.stk qOr2 _ = _
    have hv : (Ex.lt (.const 0) (.add (rv rO) (rv rB))).eval s2.env = bor ors[i] bs[i] := by
      simp only [Ex.eval, rv, e2O, e2B, bor]
    rw [hv, e5I]
    have hz : List.zipWith bor (ors.take (i + 1)) (bs.take (i + 1)) =
        List.zipWith bor (ors.take i) (bs.take i) ++ [bor ors[i] bs[i]] := by
      rw [List.take_add_one, List.take_add_one, List.getElem?_eq_getElem hilo,
        List.getElem?_eq_getElem hlt, Option.toList_some, Option.toList_some,
        List.zipWith_append (by simp; omega)]
      rfl
    rw [hz, List.reverse_append]
    funext q
    by_cases h1 : q = qOr2
    · subst h1
      simp only [Function.update_self, s2, NSt.set_stk, NSt.setS_stk,
        Function.update_of_ne (show qOr2 ≠ qOr by decide), s1, rdNumFinal_stk, hstk]
      simp
    · by_cases h2 : q = qOr
      · subst h2
        simp only [Function.update_of_ne h1, Function.update_self, s2, NSt.set_stk,
          NSt.setS_stk, hq1, List.tail_cons]
      · simp only [Function.update_of_ne h1, s2, NSt.set_stk, NSt.setS_stk,
          Function.update_of_ne h2, s1, rdNumFinal_stk, hstk]
  · show s.out = O; exact hout
  · rw [e5I]; omega
  · rw [hp5]; omega

/-! ## The block of a coordinate -/

lemma dChg_append : ∀ (p : ℕ) (l : List ℕ) (i : ℕ),
    dChg p (l ++ [i]) = dChg p l + (if i = l.getLastD p then 0 else 1)
  | p, [], i => by simp [dChg]
  | p, a :: l, i => by
    simp only [List.cons_append, dChg, dChg_append a l i, List.getLastD_cons]; ring

set_option maxHeartbeats 800000 in
lemma p2Blk_good {w : ℕ} (hw : 2 ≤ w) (s : NSt CR CQ) {i p R Cl Dt Lt T : ℕ}
    (hi : s.env rBi = i) (hp : s.env rPrev = p) (hR : s.env rRows = R) (hC : s.env rCol = Cl)
    (hD : s.env rDist = Dt) (hL : s.env rLast = Lt) (hK : s.env rKk = k)
    (hKm : s.env rKm1 = k - 1) (hT : s.env rTern = T)
    (hb : k + p + i + R + Cl + Dt + Lt + T + 10 < 2 ^ w) :
    Good (encodeSystem I) w p2Blk s (((((s.set rDist (Dt + if i = p then 0 else 1)).set rPrev i).set
      rRows (R + if i + 1 < k then 1 else k - 1)).set rLast (if i + 1 < k then Lt else 1)).set rCol
      (Cl + if T = 0 then 2 else 8)) (60 * Ex.nodeCost w) := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have r1 := Good.set (x := encodeSystem I) (w := w) (st := s) (r := rDist)
    (e := .add (rv rDist) (.lt (.const 0) (.add (.lt (rv rBi) (rv rPrev)) (.lt (rv rPrev) (rv rBi)))))
    (by
      have h4 : 4 ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
      simp only [Ex.Fits, Ex.eval, rv, hi, hp, hD]; split_ifs <;> omega)
  have ev1 : (Ex.add (rv rDist) (.lt (.const 0) (.add (.lt (rv rBi) (rv rPrev))
      (.lt (rv rPrev) (rv rBi))))).eval s.env = Dt + if i = p then 0 else 1 := by
    simp only [Ex.eval, rv, hi, hp, hD]
    split_ifs <;> omega
  rw [ev1] at r1
  set s1 := s.set rDist (Dt + if i = p then 0 else 1)
  have r2 := Good.set (x := encodeSystem I) (w := w) (st := s1) (r := rPrev) (e := rv rBi)
    (by simp only [Ex.Fits, Ex.eval, rv, s1, NSt.set_env, Function.update_of_ne (show rBi ≠ rDist by decide), hi]; omega)
  have ev2 : (rv rBi : Ex CR).eval s1.env = i := by
    simp only [Ex.eval, rv, s1, NSt.set_env, Function.update_of_ne (show rBi ≠ rDist by decide), hi]
  rw [ev2] at r2
  set s2 := s1.set rPrev i
  have e2 : ∀ q, q ≠ rPrev → q ≠ rDist → s2.env q = s.env q := fun q h1 h2 => by
    simp [s2, s1, Function.update_of_ne h1, Function.update_of_ne h2]
  have e2i : s2.env rBi = i := by rw [e2 _ (by decide) (by decide), hi]
  have e2R : s2.env rRows = R := by rw [e2 _ (by decide) (by decide), hR]
  have e2K : s2.env rKk = k := by rw [e2 _ (by decide) (by decide), hK]
  have e2Km : s2.env rKm1 = k - 1 := by rw [e2 _ (by decide) (by decide), hKm]
  have hc3 : (Ex.lt (.add (rv rBi) (.const 1)) (rv rKk)).Fits w s2.env := by
    simp only [Ex.Fits, Ex.eval, rv, e2i, e2K]; omega
  have r3 : Good (encodeSystem I) w (.ite (.lt (.add (rv rBi) (.const 1)) (rv rKk))
      (.set rRows (.add (rv rRows) (.const 1)))
      (.seq (.set rRows (.add (rv rRows) (rv rKm1))) (.set rLast (.const 1)))) s2
      ((s2.set rRows (R + if i + 1 < k then 1 else k - 1)).set rLast (if i + 1 < k then Lt else 1))
      (condCost w (.lt (.add (rv rBi) (.const 1)) (rv rKk)) + 2 * (4 * Ex.nodeCost w)) := by
    by_cases hik : i + 1 < k
    · refine Good.iteT hc3 (by simp [Ex.eval, rv, e2i, e2K, hik]) ((CStm.Good.set ?_).of_eq ?_ ?_)
      · simp only [Ex.Fits, Ex.eval, rv, e2R]; omega
      · simp only [if_pos hik, Ex.eval, rv, e2R]
        have hL2 : (s2.set rRows (R + 1)).env rLast = Lt := by
          have e2L : s2.env rLast = Lt := by rw [e2 _ (by decide) (by decide), hL]
          simp [Function.update_of_ne (show rLast ≠ rRows by decide), e2L]
        rw [← hL2]; rcases s2 with ⟨e, st, ps, ot⟩; simp [NSt.set]
      · simp only [Ex.size]; omega
    · refine Good.iteF hc3 (by simp [Ex.eval, rv, e2i, e2K, hik]) (((CStm.Good.set ?_).seq
        (Good.set ?_)).of_eq ?_ ?_)
      · simp only [Ex.Fits, Ex.eval, rv, e2R, e2Km]; omega
      · simp [Ex.Fits]; omega
      · simp only [if_neg hik, Ex.eval, rv, e2R, e2Km]
      · simp only [Ex.size]; omega
  set s3 := (s2.set rRows (R + if i + 1 < k then 1 else k - 1)).set rLast (if i + 1 < k then Lt else 1)
  have e2T : s2.env rTern = T := by rw [e2 _ (by decide) (by decide), hT]
  have e2C : s2.env rCol = Cl := by rw [e2 _ (by decide) (by decide), hC]
  have e3T : s3.env rTern = T := by
    simp [s3, Function.update_of_ne (show rTern ≠ rLast by decide),
      Function.update_of_ne (show rTern ≠ rRows by decide), e2T]
  have e3C : s3.env rCol = Cl := by
    simp [s3, Function.update_of_ne (show rCol ≠ rLast by decide),
      Function.update_of_ne (show rCol ≠ rRows by decide), e2C]
  have r4 : Good (encodeSystem I) w (.ite (rv rTern) (.set rCol (.add (rv rCol) (.const 8)))
      (.set rCol (.add (rv rCol) (.const 2)))) s3 (s3.set rCol (Cl + if T = 0 then 2 else 8))
      (condCost w (rv rTern) + 4 * Ex.nodeCost w) := by
    by_cases hT0 : T = 0
    · refine Good.iteF (by simp only [Ex.Fits, Ex.eval, rv, e3T]; omega) (by simp [Ex.eval, rv, e3T, hT0])
        ((CStm.Good.set ?_).of_eq ?_ ?_)
      · simp only [Ex.Fits, Ex.eval, rv, e3C]; omega
      · simp [Ex.eval, rv, e3C, hT0]
      · simp only [Ex.size]; omega
    · refine Good.iteT (by simp only [Ex.Fits, Ex.eval, rv, e3T]; omega) (by simp [Ex.eval, rv, e3T, hT0])
        ((CStm.Good.set ?_).of_eq ?_ ?_)
      · simp only [Ex.Fits, Ex.eval, rv, e3C]; omega
      · simp [Ex.eval, rv, e3C, hT0]
      · simp only [Ex.size]; omega
  refine (r1.seq (r2.seq (r3.seq r4))).mono ?_
  simp only [condCost, Ex.size, rv]
  omega

/-! ## One coordinate -/

/-- The weight of a column in the junction, link and sum sections: `8` or `2`. -/
def colV (tern : Bool) : ℕ := if tern then 8 else 2

lemma dChg_le : ∀ (p : ℕ) (l : List ℕ), dChg p l ≤ l.length
  | _, [] => le_rfl
  | p, i :: l => by
    have := dChg_le i l
    simp only [dChg, List.length_cons]; split_ifs <;> omega

lemma getLastD_le {l : List ℕ} {p m : ℕ} (hp : p ≤ m) (hl : ∀ x ∈ l, x ≤ m) :
    l.getLastD p ≤ m := by
  rcases List.eq_nil_or_concat l with rfl | ⟨L, b, rfl⟩
  · exact hp
  · rw [List.concat_eq_append, List.getLastD_concat]; exact hl b (by simp)

lemma rowsSum_take_le (cs : List (Coord k ℓ)) (r : ℕ) : rowsSum (cs.take r) ≤ rowsSum cs := by
  conv_rhs => rw [← List.take_append_drop r cs]
  simp only [rowsSum, List.map_append, List.sum_append]; omega

lemma rowsSum_take_succ (cs : List (Coord k ℓ)) {r : ℕ} (hr : r < cs.length) :
    rowsSum (cs.take (r + 1)) = rowsSum (cs.take r) + rowsC cs[r] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hr, Option.toList_some, rowsSum,
    List.map_append, List.sum_append]
  simp [rowsSum]

/-- The invariant of the coordinate loop of a schema with coordinates `cs`. -/
def p2CoordInv (cs : List (Coord k ℓ)) (tern : Bool) (B : ℕ) (S0 : Fin CQ → List ℕ)
    (O : List ℕ) (s : NSt CR CQ) : Prop :=
  s.env rK ≤ cs.length ∧ s.env rD = cs.length ∧ s.env rL = ℓ ∧ s.env rKk = k ∧
    s.env rKm1 = k - 1 ∧ s.env rTern = (if tern then 1 else 0) ∧
    s.env rRows = rowsSum (cs.take (s.env rK)) ∧ s.env rCol = s.env rK * colV tern ∧
    s.env rDist = dChg k ((cs.take (s.env rK)).map fun c => (c.1 : ℕ)) ∧
    s.env rPrev = ((cs.take (s.env rK)).map fun c => (c.1 : ℕ)).getLastD k ∧
    s.env rLast = (if ∃ c ∈ cs.take (s.env rK), ¬ (c.1 : ℕ) + 1 < k then 1 else 0) ∧
    s.pos = B + (encodeNats ((cs.take (s.env rK)).flatMap cdesc)).length ∧
    s.stk = Function.update (Function.update S0 qOr (orsL (cs.take (s.env rK)))) qOr2 [] ∧
    s.out = O

lemma blockDescription_le (b : BlockCoord ℓ) : ∀ v ∈ blockDescription b, v ≤ 1 := by
  intro v hv
  simp only [blockDescription, List.mem_map] at hv
  obtain ⟨t, -, rfl⟩ := hv
  have := ZMod.val_lt (b t); omega

lemma orsL_le (cs : List (Coord k ℓ)) : ∀ v ∈ orsL cs, v ≤ 1 := by
  intro v hv
  simp only [orsL, List.mem_map] at hv
  obtain ⟨t, -, rfl⟩ := hv
  split_ifs <;> omega

lemma length_blockDescription (b : BlockCoord ℓ) : (blockDescription b).length = ℓ := by
  simp [blockDescription]

set_option maxHeartbeats 3000000 in
/-- One coordinate. -/
lemma p2Coord_good {w : ℕ} (hw : 2 ≤ w) (cs : List (Coord k ℓ)) (hkH : k ≤ H I)
    (hℓ : ℓ ≤ H I) (hdH : cs.length ≤ H I) (hb : 16 * (H I + 1) + rowsSum cs ≤ 2 ^ w)
    (tern : Bool) (B : ℕ) (S0 : Fin CQ → List ℕ) (O : List ℕ) (rest : List Bool)
    (hx : (encodeSystem I).drop B = encodeNats (cs.flatMap cdesc) ++ rest)
    (s : NSt CR CQ) (hI : p2CoordInv cs tern B S0 O s)
    (hc : (Ex.lt (rv rK) (rv rD)).eval s.env ≠ 0) :
    ∃ s', Good (encodeSystem I) w p2Coord s s'
        (150 * Ex.nodeCost w * ((B + (encodeNats (cs.flatMap cdesc)).length - s.pos) -
          (B + (encodeNats (cs.flatMap cdesc)).length - s'.pos)) + 150 * Ex.nodeCost w) ∧
      p2CoordInv cs tern B S0 O s' ∧ cs.length - s'.env rK < cs.length - s.env rK ∧
      B + (encodeNats (cs.flatMap cdesc)).length - s'.pos ≤
        B + (encodeNats (cs.flatMap cdesc)).length - s.pos := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  obtain ⟨hK, hD, hL, hKk, hKm, hT, hR, hC, hDi, hP, hLa, hpos, hstk, hout⟩ := hI
  have hlt : s.env rK < cs.length := by
    by_contra h; apply hc; simp only [Ex.eval, rv, hD]; rw [if_neg h]
  obtain ⟨r, hrdef⟩ : ∃ r, s.env rK = r := ⟨_, rfl⟩
  rw [hrdef] at hlt hK hR hC hDi hP hLa hpos hstk
  set c := cs[r]
  set bs := blockDescription c.2
  have hbsl : bs.length = ℓ := length_blockDescription _
  have hsplit : cs.flatMap cdesc = (cs.take r).flatMap cdesc ++
      ((c.1 : ℕ) :: bs ++ (cs.drop (r + 1)).flatMap cdesc) := by
    have e := List.take_append_drop r cs
    rw [List.drop_eq_getElem_cons hlt] at e
    conv_lhs => rw [← e]
    rw [List.flatMap_append, List.flatMap_cons]; rfl
  set rest1 := encodeNats ((cs.drop (r + 1)).flatMap cdesc) ++ rest
  have hx1 : (encodeSystem I).drop s.pos = encodeNat (c.1 : ℕ) ++ (encodeNats bs ++ rest1) := by
    rw [hpos, drop_add, hx, hsplit, encodeNats_append, List.append_assoc, List.drop_left,
      List.cons_append, encNats_cons, encodeNats_append, List.append_assoc, List.append_assoc]
  have hH2 : 2 * (H I + 1) ≤ 2 ^ w := by omega
  have hck : (c.1 : ℕ) < k := c.1.2
  -- read the block
  have r1 := rdNumS_good (Q := CQ) hw (r := rBi) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s (c.1 : ℕ) _ hx1 (bits_lt_of_le (by omega) hH2)
  set s1 := rdNumFinal s rBi rP rT (c.1 : ℕ)
  have e1 : ∀ q, q ≠ rBi → q ≠ rP → q ≠ rT → s1.env q = s.env q :=
    fun q h1 h2 h3 => rdNumFinal_env_ne h1 h2 h3 _
  have hRle : rowsSum (cs.take r) ≤ rowsSum cs := rowsSum_take_le cs r
  have hPle : ((cs.take r).map fun c => (c.1 : ℕ)).getLastD k ≤ k :=
    getLastD_le le_rfl (by simp only [List.mem_map]; rintro _ ⟨c', -, rfl⟩; exact c'.1.2.le)
  have hDle : dChg k ((cs.take r).map fun c => (c.1 : ℕ)) ≤ H I :=
    (dChg_le _ _).trans (by simp; omega)
  have hcv : colV tern ≤ 8 := by unfold colV; split_ifs <;> omega
  have hCle : r * colV tern ≤ 8 * H I := by nlinarith
  have hLle : (if ∃ c ∈ cs.take r, ¬ (c.1 : ℕ) + 1 < k then 1 else 0) ≤ 1 := by
    split_ifs <;> omega
  have hTle : (if tern then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have r2 := p2Blk_good I hw s1 (i := (c.1 : ℕ)) (rdNumFinal_env_r (by decide) (by decide) _)
    (by rw [e1 _ (by decide) (by decide) (by decide), hP])
    (by rw [e1 _ (by decide) (by decide) (by decide), hR])
    (by rw [e1 _ (by decide) (by decide) (by decide), hC])
    (by rw [e1 _ (by decide) (by decide) (by decide), hDi])
    (by rw [e1 _ (by decide) (by decide) (by decide), hLa])
    (by rw [e1 _ (by decide) (by decide) (by decide), hKk])
    (by rw [e1 _ (by decide) (by decide) (by decide), hKm])
    (by rw [e1 _ (by decide) (by decide) (by decide), hT])
    (by omega)
  set s2 := ((((s1.set rDist (dChg k ((cs.take r).map fun c => (c.1 : ℕ)) +
      if (c.1 : ℕ) = ((cs.take r).map fun c => (c.1 : ℕ)).getLastD k then 0 else 1)).set rPrev
      (c.1 : ℕ)).set rRows (rowsSum (cs.take r) + if (c.1 : ℕ) + 1 < k then 1 else k - 1)).set
      rLast (if (c.1 : ℕ) + 1 < k then (if ∃ c ∈ cs.take r, ¬ (c.1 : ℕ) + 1 < k then 1 else 0)
        else 1)).set rCol (r * colV tern + if (if tern then 1 else 0) = 0 then 2 else 8)
  have r3 := Good.set (x := encodeSystem I) (w := w) (st := s2) (r := rI) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  set s3 := s2.set rI ((Ex.const 0 : Ex CR).eval s2.env)
  have e3 : ∀ q, q ≠ rI → q ≠ rCol → q ≠ rLast → q ≠ rRows → q ≠ rPrev → q ≠ rDist →
      s3.env q = s1.env q := by
    intro q h1 h2 h3 h4 h5 h6
    simp [s3, s2, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h4, Function.update_of_ne h5, Function.update_of_ne h6]
  have e3L : s3.env rL = ℓ := by
    rw [e3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      e1 _ (by decide) (by decide) (by decide), hL]
  set R0 := rowsSum (cs.take r) + if (c.1 : ℕ) + 1 < k then 1 else k - 1
  have e3R : s3.env rRows = R0 := by
    simp [s3, s2, Function.update_of_ne (show rRows ≠ rI by decide),
      Function.update_of_ne (show rRows ≠ rCol by decide),
      Function.update_of_ne (show rRows ≠ rLast by decide), R0]
  have hrc : rowsSum (cs.take (r + 1)) = R0 + bs.sum := by
    rw [rowsSum_take_succ cs hlt, sum_blockDescription]; simp only [R0, rowsC]; ring
  have hR1 : rowsSum (cs.take (r + 1)) ≤ rowsSum cs := rowsSum_take_le cs (r + 1)
  -- the bits
  set ors := orsL (cs.take r)
  have hs3 : s3.stk = Function.update (Function.update S0 qOr ors) qOr2 [] := by
    show s.stk = _; exact hstk
  have hx3 : (encodeSystem I).drop s3.pos = encodeNats bs ++ rest1 := by
    show (encodeSystem I).drop (s.pos + (encodeNat (c.1 : ℕ)).length) = _
    rw [drop_add, hx1, List.drop_left]
  have h03 : s3.env rI = 0 := by simp [s3, Ex.eval]
  have hI3 : p2BitInv bs ors s3.pos R0 s3.stk s3.out s3 := by
    refine ⟨by rw [h03]; omega, by rw [e3L, hbsl], by rw [h03]; simp [encodeNats],
      by rw [h03, e3R, List.take_zero, List.sum_nil, Nat.add_zero], ?_, rfl⟩
    rw [h03, List.drop_zero, List.take_zero, List.take_zero]
    simp only [List.zipWith_nil_left, List.reverse_nil]
    rw [hs3]
    funext q
    by_cases h1 : q = qOr2
    · subst h1; simp
    · by_cases h2 : q = qOr
      · subst h2; simp [Function.update_of_ne (show qOr ≠ qOr2 by decide)]
      · simp [Function.update_of_ne h1, Function.update_of_ne h2]
  have hors : ors.length = bs.length := by rw [length_orsL, hbsl]
  obtain ⟨s4, r4, hI4, hc4⟩ := Good.loop_var (x := encodeSystem I) (w := w)
    (e := .lt (rv rI) (rv rL)) (body := p2Bit) (p2BitInv bs ors s3.pos R0 s3.stk s3.out)
    (fun s => bs.length - s.env rI) (fun s' => s3.pos + (encodeNats bs).length - s'.pos)
    (40 * Ex.nodeCost w) (40 * Ex.nodeCost w) (fun s' hI' => ⟨by
      obtain ⟨hi', hL', -⟩ := hI'
      simp only [Ex.Fits, rv, hL']; omega,
      fun hc' => p2Bit_good I hw bs ors (blockDescription_le _) (orsL_le _) hors s3.pos R0 s3.stk
        s3.out rest1 hx3 (by rw [hs3]; simp) (by rw [← hrc]; omega) (by omega) s' hI' hc'⟩)
    s3 hI3
  obtain ⟨hi4, hL4, hp4, hR4, hs4, ho4⟩ := hI4
  have hi4' : s4.env rI = bs.length := by
    simp only [Ex.eval, rv, hL4] at hc4; split_ifs at hc4 with h <;> omega
  rw [hi4'] at hp4 hR4 hs4
  rw [List.take_of_length_le le_rfl] at hp4 hR4
  rw [List.take_of_length_le (by omega), List.take_of_length_le le_rfl,
    List.drop_of_length_le (by omega)] at hs4
  set z := List.zipWith bor ors bs
  have hzl : z.length = ℓ := by simp [z, hors, hbsl]
  have hz : z = orsL (cs.take (r + 1)) := by
    rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, orsL_append]
  -- move the OR back
  obtain ⟨s5, r5, hs5, hf5⟩ := moveN_good (x := encodeSystem I) (w := w) (src := qOr2) (dst := qOr)
    (cnt := rL) (i := rI) (t := rO) (by decide) (by decide) (by decide) (by decide) s4
    (n := ℓ) (by rw [hL4, hbsl])
    (by rw [hs4, Function.update_self, List.length_reverse, hzl])
    (by omega)
    (by
      intro v hv
      rw [hs4, Function.update_self] at hv
      have := List.mem_of_mem_take hv
      rw [List.mem_reverse] at this
      have : v ≤ 1 := by
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp this
        simp only [z, List.getElem_zipWith]; exact bor_le _ _
      omega)
  have e5K : s5.env rK = r := by
    rw [hf5.2.2 _ (by decide), r4.env_of (r := rK) (by decide),
      e3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      e1 _ (by decide) (by decide) (by decide), hrdef]
  have r6 := Good.set (x := encodeSystem I) (w := w) (st := s5) (r := rK)
    (e := .add (rv rK) (.const 1)) (by simp only [Ex.Fits, Ex.eval, rv, e5K]; omega)
  set s6 := s5.set rK ((Ex.add (rv rK) (.const 1)).eval s5.env)
  have hall := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))
  have htail := r4.seq (r5.seq r6)
  have e6K : s6.env rK = r + 1 := by simp [s6, Ex.eval, e5K]
  have hp6 : s6.pos = s4.pos := by
    show s5.pos = _; exact hf5.1
  have hlen1 : (encodeNats ((cs.take (r + 1)).flatMap cdesc)).length =
      (encodeNats ((cs.take r).flatMap cdesc)).length + (encodeNat (c.1 : ℕ)).length +
        (encodeNats bs).length := by
    rw [List.take_add_one, List.getElem?_eq_getElem hlt]
    simp only [Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, encodeNats_append, List.length_append, cdesc, encNats_cons, c, bs]
    ring
  have hle : (encodeNats ((cs.take (r + 1)).flatMap cdesc)).length ≤
      (encodeNats (cs.flatMap cdesc)).length := by
    conv_rhs => rw [← List.take_append_drop (r + 1) cs]
    rw [List.flatMap_append, encodeNats_append, List.length_append]; omega
  have hp4' : s4.pos = s.pos + (encodeNat (c.1 : ℕ)).length + (encodeNats bs).length := by
    rw [hp4]; rfl
  have hbsE : ℓ ≤ (encodeNats bs).length := hbsl ▸ length_le_encodeNats bs
  have hcE : 1 ≤ (encodeNat (c.1 : ℕ)).length := by rw [length_encodeNat]; omega
  refine ⟨s6, hall.mono ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hp6, hp4']
    have hΔ : B + (encodeNats (cs.flatMap cdesc)).length - s.pos -
        (B + (encodeNats (cs.flatMap cdesc)).length - (s.pos + (encodeNat (c.1 : ℕ)).length +
          (encodeNats bs).length)) = (encodeNat (c.1 : ℕ)).length + (encodeNats bs).length := by
      rw [hpos] at ⊢; omega
    rw [hΔ]
    have hφ3 : s3.pos + (encodeNats bs).length - s3.pos = (encodeNats bs).length := by omega
    have hμ3 : bs.length - s3.env rI = ℓ := by rw [h03, hbsl]; rfl
    rw [hφ3, hμ3]
    simp only [condCost, Ex.size, rv]
    generalize Ex.nodeCost w = N at *
    generalize unitCost w = U at *
    generalize (encodeNat (c.1 : ℕ)).length = lc at *
    generalize (encodeNats bs).length = lb at *
    nlinarith
  · rw [e6K]; omega
  · rw [hall.env_of (by decide), hD]
  · rw [hall.env_of (by decide), hL]
  · rw [hall.env_of (by decide), hKk]
  · rw [hall.env_of (by decide), hKm]
  · rw [hall.env_of (by decide), hT]
  · rw [e6K, hrc, ← hR4]
    show s5.env rRows = s4.env rRows
    exact hf5.2.2 _ (by decide)
  · rw [e6K, htail.env_of (by decide)]
    cases tern <;> simp [s3, s2, Function.update_of_ne (show rCol ≠ rI by decide), colV] <;> ring
  · rw [e6K, htail.env_of (by decide)]
    simp only [s3, s2, NSt.set_env, Function.update_of_ne (show rDist ≠ rI by decide),
      Function.update_of_ne (show rDist ≠ rCol by decide),
      Function.update_of_ne (show rDist ≠ rLast by decide),
      Function.update_of_ne (show rDist ≠ rRows by decide),
      Function.update_of_ne (show rDist ≠ rPrev by decide), Function.update_self]
    rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, List.map_append,
      List.map_singleton, dChg_append]
  · rw [e6K, htail.env_of (by decide)]
    simp only [s3, s2, NSt.set_env, Function.update_of_ne (show rPrev ≠ rI by decide),
      Function.update_of_ne (show rPrev ≠ rCol by decide),
      Function.update_of_ne (show rPrev ≠ rLast by decide),
      Function.update_of_ne (show rPrev ≠ rRows by decide), Function.update_self]
    rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, List.map_append,
      List.map_singleton, List.getLastD_concat]
  · rw [e6K, htail.env_of (by decide)]
    simp only [s3, s2, NSt.set_env, Function.update_of_ne (show rLast ≠ rI by decide),
      Function.update_of_ne (show rLast ≠ rCol by decide), Function.update_self]
    rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some]
    simp only [List.mem_append, List.mem_singleton]
    by_cases h1 : (c.1 : ℕ) + 1 < k
    · rw [if_pos h1]
      by_cases h2 : ∃ c' ∈ cs.take r, ¬ (c'.1 : ℕ) + 1 < k
      · rw [if_pos h2, if_pos (by obtain ⟨c', h, h'⟩ := h2; exact ⟨c', Or.inl h, h'⟩)]
      · rw [if_neg h2, if_neg]
        rintro ⟨c', h | h, h'⟩
        · exact h2 ⟨c', h, h'⟩
        · subst h; exact h' h1
    · rw [if_neg h1, if_pos ⟨c, Or.inr rfl, h1⟩]
  · rw [e6K, hp6, hp4', hpos, hlen1]; ring
  · rw [e6K]
    show s5.stk = _
    rw [hs5, hs4]
    funext q
    unfold movedStk
    by_cases h1 : q = qOr
    · subst h1
      simp only [Function.update_self, Function.update_of_ne (show qOr ≠ qOr2 by decide),
        List.append_nil]
      rw [List.take_of_length_le (by simp [hzl]), List.reverse_reverse, hz]
    · by_cases h2 : q = qOr2
      · subst h2
        simp [Function.update_of_ne (show qOr2 ≠ qOr by decide), hzl]
      · simp [Function.update_of_ne h1, Function.update_of_ne h2, hs3]
  · rw [hall.out_of (by decide), hout]
  · rw [e6K]; omega
  · rw [hp6, hp4']; omega

/-! ## The numbers of a schema -/

set_option maxHeartbeats 3000000 in
lemma p2Fin_good {w : ℕ} (hw : 2 ≤ w) (s : NSt CR CQ) (ors : List ℕ) (hors : s.stk qOr = ors)
    (hlen : ors.length = ℓ) (hle : ∀ o ∈ ors, o ≤ 1) {Lt Dt R Cl LB : ℕ}
    (hL : s.env rL = ℓ) (hKm : s.env rKm1 = k - 1) (hK1 : s.env rK1 = k + 1)
    (hLa : s.env rLast = Lt) (hLt : Lt ≤ 1) (hDi : s.env rDist = Dt) (hR : s.env rRows = R)
    (hC : s.env rCol = Cl) (hLB : s.env rLB = LB)
    (hb : LB + Cl + 6 * (R * (k + 1)) + 2 * (((if Lt ≠ 0 then k - 1 else Dt) + ors.sum) * (k + 1))
      + ℓ + k + Dt + 4 < 2 ^ w) :
    ∃ s', Good (encodeSystem I) w p2Fin s s' ((ℓ + k + 10) * (60 * Ex.nodeCost w)) ∧
      s'.env rLB = LB + Cl + 6 * (R * (k + 1)) +
        2 * (((if Lt ≠ 0 then k - 1 else Dt) + ors.sum) * (k + 1)) ∧
      s'.stk = Function.update (Function.update s.stk qOr []) qSch
        ((((if Lt ≠ 0 then k - 1 else Dt) + ors.sum) * (k + 1)) :: (R * (k + 1)) ::
          (if Lt ≠ 0 then k - 1 else Dt) :: (ors.reverse ++ s.stk qSch)) ∧
      s'.pos = s.pos ∧ s'.out = s.out := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  set BR := if Lt ≠ 0 then k - 1 else Dt
  have hsum : ors.sum ≤ ℓ := by
    have : ors.sum ≤ ors.length * 1 := List.sum_le_card_nsmul ors 1 hle
    omega
  have r1 := Good.set (x := encodeSystem I) (w := w) (st := s) (r := rOrp) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  set s1 := s.set rOrp ((Ex.const 0 : Ex CR).eval s.env)
  have e1 : ∀ q, q ≠ rOrp → s1.env q = s.env q := fun q h => by
    simp [s1, Function.update_of_ne h]
  obtain ⟨s2, r2, hs2, ha2, hf2⟩ := mvSumN_good (x := encodeSystem I) (w := w) (src := qOr)
    (dst := qSch) (n := rL) (j := rI) (t := rO) (acc := rOrp) hw (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) s1 (N := ℓ)
    (by rw [e1 _ (by decide), hL]) (by simp [s1, hors, hlen])
    (by omega) (by
      simp only [s1, NSt.set_env, Function.update_self, Ex.eval, NSt.set_stk, hors,
        List.take_of_length_le (le_of_eq hlen)]
      omega)
  have e2 : ∀ q, q ≠ rI → q ≠ rO → q ≠ rOrp → s2.env q = s.env q := by
    intro q h1 h2 h3
    rw [hf2.2.2 q (by simp [h1, h2, h3]), e1 q h3]
  have e2O : s2.env rOrp = ors.sum := by
    rw [ha2]; simp [s1, Ex.eval, hors, List.take_of_length_le (le_of_eq hlen)]
  have hstk2 : s2.stk = Function.update (Function.update s.stk qOr []) qSch
      (ors.reverse ++ s.stk qSch) := by
    rw [hs2]
    funext q
    unfold movedStk
    simp only [s1, NSt.set_stk, hors, List.take_of_length_le (le_of_eq hlen),
      List.drop_of_length_le (le_of_eq hlen)]
  -- the block rows
  have r3 : Good (encodeSystem I) w (.ite (rv rLast) (.set rBR (rv rKm1)) (.set rBR (rv rDist)))
      s2 (s2.set rBR BR) (condCost w (rv rLast) + 2 * Ex.nodeCost w) := by
    have hLa2 : s2.env rLast = Lt := by rw [e2 _ (by decide) (by decide) (by decide), hLa]
    by_cases h : Lt ≠ 0
    · refine Good.iteT (by simp only [Ex.Fits, rv, hLa2]; omega)
        (by simp only [Ex.eval, rv, hLa2]; exact h)
        ((CStm.Good.set ?_).of_eq ?_ ?_)
      · simp only [Ex.Fits, rv]; rw [e2 _ (by decide) (by decide) (by decide), hKm]; omega
      · simp only [Ex.eval, rv, BR, if_pos h]; rw [e2 _ (by decide) (by decide) (by decide), hKm]
      · simp only [Ex.size]; omega
    · refine Good.iteF (by simp only [Ex.Fits, rv, hLa2]; omega)
        (by simp only [Ex.eval, rv, hLa2]; omega)
        ((CStm.Good.set ?_).of_eq ?_ ?_)
      · simp only [Ex.Fits, rv]; rw [e2 _ (by decide) (by decide) (by decide), hDi]; omega
      · simp only [Ex.eval, rv, BR, if_neg h]; rw [e2 _ (by decide) (by decide) (by decide), hDi]
      · simp only [Ex.size]; omega
  set s3 := s2.set rBR BR
  have hBR : BR ≤ k + Dt := by simp only [BR]; split_ifs <;> omega
  have r4 := Good.push (x := encodeSystem I) (w := w) (st := s3) (q := qSch) (e := rv rBR)
    (by simp only [Ex.Fits, rv, s3, NSt.set_env, Function.update_self]; omega)
  set s4 := s3.setS qSch ((rv rBR : Ex CR).eval s3.env :: s3.stk qSch)
  have e4 : ∀ q, q ≠ rBR → s4.env q = s2.env q := fun q h => by
    simp [s4, s3, Function.update_of_ne h]
  have e4B : s4.env rBR = BR := by simp [s4, s3]
  have e4O : s4.env rOrp = ors.sum := by rw [e4 _ (by decide), e2O]
  have r5 := Good.set (x := encodeSystem I) (w := w) (st := s4) (r := rBR)
    (e := .add (rv rBR) (rv rOrp)) (by simp only [Ex.Fits, Ex.eval, rv, e4B, e4O]; omega)
  set s5 := s4.set rBR ((Ex.add (rv rBR) (rv rOrp)).eval s4.env)
  have e5 : ∀ q, q ≠ rBR → s5.env q = s2.env q := fun q h => by
    simp only [s5, NSt.set_env, Function.update_of_ne h]; exact e4 q h
  have e5B : s5.env rBR = BR + ors.sum := by simp [s5, Ex.eval, e4B, e4O]
  have e5R : s5.env rRows = R := by
    rw [e5 _ (by decide), e2 _ (by decide) (by decide) (by decide), hR]
  have e5K : s5.env rK1 = k + 1 := by
    rw [e5 _ (by decide), e2 _ (by decide) (by decide) (by decide), hK1]
  have r6 := mulS_good (x := encodeSystem I) (w := w) (Q := CQ) (dst := rNE) (a := rRows)
    (b := rK1) (j := rJ2) hw (by decide) (by decide) (by decide) (by decide) (by decide) s5 e5R
    e5K (by omega) (by omega)
  set s6 := (s5.set rNE (R * (k + 1))).set rJ2 (k + 1)
  have e6 : ∀ q, q ≠ rNE → q ≠ rJ2 → s6.env q = s5.env q := fun q h1 h2 => by
    simp [s6, Function.update_of_ne h1, Function.update_of_ne h2]
  have r7 := mulS_good (x := encodeSystem I) (w := w) (Q := CQ) (dst := rNC) (a := rBR)
    (b := rK1) (j := rJ2) hw (by decide) (by decide) (by decide) (by decide) (by decide) s6
    (by rw [e6 _ (by decide) (by decide), e5B]) (by rw [e6 _ (by decide) (by decide), e5K])
    (by omega) (by omega)
  set s7 := (s6.set rNC ((BR + ors.sum) * (k + 1))).set rJ2 (k + 1)
  have e7 : ∀ q, q ≠ rNC → q ≠ rJ2 → s7.env q = s6.env q := fun q h1 h2 => by
    simp [s7, Function.update_of_ne h1, Function.update_of_ne h2]
  have e7E : s7.env rNE = R * (k + 1) := by
    rw [e7 _ (by decide) (by decide)]; simp [s6, Function.update_of_ne (show rNE ≠ rJ2 by decide)]
  have e7C : s7.env rNC = (BR + ors.sum) * (k + 1) := by
    simp [s7, Function.update_of_ne (show rNC ≠ rJ2 by decide)]
  have r8 := Good.push (x := encodeSystem I) (w := w) (st := s7) (q := qSch) (e := rv rNE)
    (by simp only [Ex.Fits, rv, e7E]; omega)
  set s8 := s7.setS qSch ((rv rNE : Ex CR).eval s7.env :: s7.stk qSch)
  have r9 := Good.push (x := encodeSystem I) (w := w) (st := s8) (q := qSch) (e := rv rNC)
    (by simp only [Ex.Fits, rv, s8, NSt.setS_env, e7C]; omega)
  set s9 := s8.setS qSch ((rv rNC : Ex CR).eval s8.env :: s8.stk qSch)
  have e9 : ∀ q, s9.env q = s7.env q := fun q => rfl
  have e9LB : s9.env rLB = LB := by
    rw [e9, e7 _ (by decide) (by decide), e6 _ (by decide) (by decide), e5 _ (by decide),
      e2 _ (by decide) (by decide) (by decide), hLB]
  have e9C : s9.env rCol = Cl := by
    rw [e9, e7 _ (by decide) (by decide), e6 _ (by decide) (by decide), e5 _ (by decide),
      e2 _ (by decide) (by decide) (by decide), hC]
  have r10 := Good.set (x := encodeSystem I) (w := w) (st := s9) (r := rLB)
    (e := .add (rv rLB) (.add (rv rCol) (six2 rNE rNC))) (by
      simp only [six2, Ex.Fits, Ex.eval, rv, e9LB, e9C, e9, e7E, e7C]; omega)
  set s10 := s9.set rLB ((Ex.add (rv rLB) (.add (rv rCol) (six2 rNE rNC))).eval s9.env)
  refine ⟨s10, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq
    r10))))))))).mono ?_, ?_, ?_, ?_, ?_⟩
  · simp only [condCost, Ex.size, rv, six2]
    nlinarith
  · simp only [s10, NSt.set_env, Function.update_self, six2, Ex.eval, rv, e9LB, e9C, e9, e7E, e7C]
    ring
  · show Function.update s8.stk qSch (s8.env rNC :: s8.stk qSch) = _
    have h8 : s8.stk qSch = R * (k + 1) :: BR :: (ors.reverse ++ s.stk qSch) := by
      show Function.update s7.stk qSch (s7.env rNE :: s7.stk qSch) qSch = _
      rw [Function.update_self, e7E]
      show R * (k + 1) :: Function.update s3.stk qSch (s3.env rBR :: s3.stk qSch) qSch = _
      rw [Function.update_self]
      simp [s3, hstk2]
    have h8' : s8.stk = Function.update s2.stk qSch (R * (k + 1) :: BR :: (ors.reverse ++ s.stk qSch)) := by
      funext q
      by_cases hq : q = qSch
      · subst hq; rw [h8, Function.update_self]
      · show Function.update s7.stk qSch _ q = _
        rw [Function.update_of_ne hq, Function.update_of_ne hq]
        show Function.update s3.stk qSch _ q = _
        rw [Function.update_of_ne hq]; rfl
    rw [h8', show s8.env rNC = (BR + ors.sum) * (k + 1) from e7C, hstk2]
    funext q
    by_cases hq : q = qSch
    · subst hq; simp
    · simp [Function.update_of_ne hq]
  · show s2.pos = s.pos
    rw [hf2.1]; rfl
  · show s2.out = s.out
    rw [hf2.2.1]; rfl

end Lax119563Proofs.Compiler
