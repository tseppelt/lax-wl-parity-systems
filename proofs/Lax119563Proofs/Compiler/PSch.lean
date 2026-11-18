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

end Lax119563Proofs.Compiler
