import Lax119563Proofs.Compiler.PRec
import Lax119563Proofs.Compiler.PJoinList

/-!
# The join of pass `P3`: the scan program

Registers and stacks of `P3`, and the scan `pJScan` over the sorted union of the location
records and the requests on `qX` (records `v :: i :: b₀ … b_{ℓ-1} ++ [tag, d₁, d₂, d₃]`):
a location record (tag `0`, data `off, labs, ι`) sets the current data
`(off, labs, seed)` with `seed = [i = 0 ∧ ι = 2]`; a request (tag `1`, data `seq, 0, 0`)
pushes the answer `[seq, off, labs, seed]` onto `qAns` (**`pJScan_good`**, against
`Join.scanF`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

/-! ## Registers and stacks of `P3` -/

/-- The union of records to be sorted. -/
def qX : Fin CQ := 5
/-- Scratch stacks of the sort (empty outside of it). -/
def qT1 : Fin CQ := 6
def qT2 : Fin CQ := 7
def qY : Fin CQ := 8
def qTmp : Fin CQ := 9
def qC1 : Fin CQ := 10
def qC2 : Fin CQ := 11
/-- The answers. -/
def qAns : Fin CQ := 12
/-- Discarded words. -/
def qJunk : Fin CQ := 13

/-- Scan registers. -/
def rTg : Fin CR := 20
def rD1 : Fin CR := 21
def rD2 : Fin CR := 22
def rD3 : Fin CR := 23
def rCo : Fin CR := 24
def rCl : Fin CR := 25
def rCs : Fin CR := 27
def rN : Fin CR := 28
def rJi : Fin CR := 29

open CStm

/-! ## The program -/

/-- The seed `[i = 0 ∧ ι = 2]`. -/
def seedEx : Ex CR := .half (.add (.lt (rv rJi) (.const 1)) (.lt (.const 1) (rv rD3)))

/-- Pop a record. -/
def pJPop : CStm CR CQ :=
  .seq (.pop qX rV) (.seq (.pop qX rJi) (.seq (moveN qX qJunk rL rI rT)
    (.seq (.pop qX rTg) (.seq (.pop qX rD1) (.seq (.pop qX rD2) (.pop qX rD3))))))

/-- Answer a request. -/
def pJAns : CStm CR CQ :=
  .seq (.push qAns (rv rCs)) (.seq (.push qAns (rv rCl))
    (.seq (.push qAns (rv rCo)) (.push qAns (rv rD1))))

/-- Remember a location record. -/
def pJLoc : CStm CR CQ :=
  .seq (.set rCo (rv rD1)) (.seq (.set rCl (rv rD2)) (.set rCs seedEx))

/-- One record. -/
def pJStep : CStm CR CQ :=
  .seq pJPop (.seq (.ite (rv rTg) pJAns pJLoc) (.set rK (.add (rv rK) (.const 1))))

/-- **The scan** over `rN` records. -/
def pJScan : CStm CR CQ := .seq (.set rK (.const 0)) (.loop (.lt (rv rK) (rv rN)) pJStep)

/-! ## The list level -/

/-- The seed value. -/
def seedV (i d : ℕ) : ℕ := ((if i < 1 then 1 else 0) + (if 1 < d then 1 else 0)) / 2

/-- The data of a location record. -/
def jCur (ℓ : ℕ) (m : List ℕ) : ℕ × ℕ × ℕ :=
  (m.getD (ℓ + 3) 0, m.getD (ℓ + 4) 0, seedV (m.getD 1 0) (m.getD (ℓ + 5) 0))

/-- The answer to a request. -/
def jAns (ℓ : ℕ) (c : ℕ × ℕ × ℕ) (r : List ℕ) : List ℕ := [r.getD (ℓ + 3) 0, c.1, c.2.1, c.2.2]

/-- The scan. -/
abbrev jScan (ℓ : ℕ) (c0 : ℕ × ℕ × ℕ) (L : List (List ℕ)) : List (List ℕ) :=
  Join.scanF (ℓ + 2) (jCur ℓ) (jAns ℓ) c0 L

/-- The current data after a prefix. -/
abbrev jCurAfter (ℓ : ℕ) (c0 : ℕ × ℕ × ℕ) (L : List (List ℕ)) : ℕ × ℕ × ℕ :=
  Join.curAfter (ℓ + 2) (jCur ℓ) c0 L

/-! ## Popping a record -/

lemma Good.pop_cons {x : List Bool} {w : ℕ} {st : NSt CR CQ} {q : Fin CQ} {r : Fin CR} {a : ℕ}
    {rest : List ℕ} (h : st.stk q = a :: rest) :
    Good x w (.pop q r : CStm CR CQ) st ((st.setS q rest).set r a) (unitCost w + 1) := by
  have := Good.pop (x := x) (w := w) (st := st) q r
  rwa [h] at this

lemma ex_rec (ℓ : ℕ) (r : List ℕ) (h : r.length = ℓ + 6) :
    ∃ a b bits tg d1 d2 d3, r = a :: b :: bits ++ [tg, d1, d2, d3] ∧ bits.length = ℓ := by
  match r, h with
  | a :: b :: t, h =>
    have ht : t.length = ℓ + 4 := by simp at h; omega
    have hd : (t.drop ℓ).length = 4 := by simp [ht]
    match hdr : t.drop ℓ, hd with
    | [tg, d1, d2, d3], _ =>
      refine ⟨a, b, t.take ℓ, tg, d1, d2, d3, ?_, by simp [ht]⟩
      rw [← hdr]; simp

set_option maxHeartbeats 1000000 in
lemma pJPop_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (s : NSt CR CQ) {ℓ a b tg d1 d2 d3 : ℕ}
    {bits rest : List ℕ} (hbits : bits.length = ℓ) (hX : s.stk qX = a :: b :: bits ++
      [tg, d1, d2, d3] ++ rest) (hL : s.env rL = ℓ) (hℓw : ℓ + 1 < 2 ^ w)
    (hbw : ∀ v ∈ bits, v < 2 ^ w) :
    ∃ s', Good x w pJPop s s' ((ℓ + 8) * (12 * Ex.nodeCost w)) ∧
      s'.stk qX = rest ∧ (∀ q, q ≠ qX → q ≠ qJunk → s'.stk q = s.stk q) ∧
      s'.env rJi = b ∧ s'.env rTg = tg ∧ s'.env rD1 = d1 ∧ s'.env rD2 = d2 ∧ s'.env rD3 = d3 ∧
      s'.pos = s.pos ∧ s'.out = s.out ∧ ∀ r, wReg r pJPop = false → s'.env r = s.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have r1 := Good.pop_cons (x := x) (w := w) (r := rV) (st := s) (q := qX) hX
  set s1 := (s.setS qX (b :: bits ++ [tg, d1, d2, d3] ++ rest)).set rV a
  have r2 := Good.pop_cons (x := x) (w := w) (r := rJi) (st := s1) (q := qX)
    (a := b) (rest := bits ++ [tg, d1, d2, d3] ++ rest) (by simp [s1])
  set s2 := (s1.setS qX (bits ++ [tg, d1, d2, d3] ++ rest)).set rJi b
  have hs2X : s2.stk qX = bits ++ [tg, d1, d2, d3] ++ rest := by simp [s2]
  have hs2L : s2.env rL = ℓ := by
    simp only [s2, s1, NSt.set_env, NSt.setS_env]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hL]
  obtain ⟨s3, r3, hs3, hf3⟩ := moveN_good (x := x) (w := w) (src := qX) (dst := qJunk)
    (cnt := rL) (i := rI) (t := rT) (by decide) (by decide) (by decide) (by decide) s2 hs2L
    (by rw [hs2X]; simp [hbits]) hℓw (by
      rw [hs2X, List.append_assoc, List.take_append_of_le_length (by omega),
        List.take_of_length_le (le_of_eq hbits)]
      exact hbw)
  have hs3X : s3.stk qX = tg :: d1 :: d2 :: d3 :: rest := by
    rw [hs3, movedStk_src _ (by decide), hs2X, List.append_assoc, List.drop_append_of_le_length
      (by omega), List.drop_eq_nil_of_le (by omega)]
    rfl
  have r4 := Good.pop_cons (x := x) (w := w) (r := rTg) hs3X
  set s4 := (s3.setS qX (d1 :: d2 :: d3 :: rest)).set rTg tg
  have r5 := Good.pop_cons (x := x) (w := w) (r := rD1) (st := s4) (q := qX) (a := d1)
    (rest := d2 :: d3 :: rest) (by simp [s4])
  set s5 := (s4.setS qX (d2 :: d3 :: rest)).set rD1 d1
  have r6 := Good.pop_cons (x := x) (w := w) (r := rD2) (st := s5) (q := qX) (a := d2)
    (rest := d3 :: rest) (by simp [s5])
  set s6 := (s5.setS qX (d3 :: rest)).set rD2 d2
  have r7 := Good.pop_cons (x := x) (w := w) (r := rD3) (st := s6) (q := qX) (a := d3)
    (rest := rest) (by simp [s6])
  set s7 := (s6.setS qX rest).set rD3 d3
  have hall := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))
  have e3 : ∀ r, r ≠ rI → r ≠ rT → s3.env r = s2.env r := fun r h1 h2 => hf3.2.2 r (by
    simp [h1, h2])
  refine ⟨s7, hall.mono ?_, by simp [s7], fun q h1 h2 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r hr => hall.env_of hr⟩
  · nlinarith
  · simp only [s7, s6, s5, s4, NSt.set_stk, NSt.setS_stk, Function.update_of_ne h1]
    rw [hs3, movedStk_other _ h1 h2]
    simp [s2, s1, Function.update_of_ne h1]
  · simp only [s7, s6, s5, s4, NSt.set_env, NSt.setS_env]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      e3 _ (by decide) (by decide)]
    simp [s2]
  · simp [s7, s6, s5, s4, Function.update_of_ne (show rTg ≠ rD1 by decide),
      Function.update_of_ne (show rTg ≠ rD2 by decide), Function.update_of_ne (show rTg ≠ rD3 by decide)]
  · simp [s7, s6, s5, Function.update_of_ne (show rD1 ≠ rD2 by decide),
      Function.update_of_ne (show rD1 ≠ rD3 by decide)]
  · simp [s7, s6, Function.update_of_ne (show rD2 ≠ rD3 by decide)]
  · simp [s7]
  · simp only [s7, s6, s5, s4, NSt.set_pos, NSt.setS_pos]; rw [hf3.1]; rfl
  · simp only [s7, s6, s5, s4, NSt.set_out, NSt.setS_out]; rw [hf3.2.1]; rfl

lemma rec_getD {ℓ a b tg d1 d2 d3 : ℕ} {bits : List ℕ} (hbits : bits.length = ℓ) :
    (a :: b :: bits ++ [tg, d1, d2, d3]).getD 1 0 = b ∧
    (a :: b :: bits ++ [tg, d1, d2, d3]).getD (ℓ + 2) 0 = tg ∧
    (a :: b :: bits ++ [tg, d1, d2, d3]).getD (ℓ + 3) 0 = d1 ∧
    (a :: b :: bits ++ [tg, d1, d2, d3]).getD (ℓ + 4) 0 = d2 ∧
    (a :: b :: bits ++ [tg, d1, d2, d3]).getD (ℓ + 5) 0 = d3 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, hbits]

lemma seedV_le (i d : ℕ) : seedV i d ≤ 1 := by
  unfold seedV; split_ifs <;> omega

set_option maxHeartbeats 1000000 in
/-- One record of the scan. -/
lemma pJStep_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (s : NSt CR CQ) {ℓ : ℕ}
    (r rest : List ℕ) (hr : r.length = ℓ + 6) (hX : s.stk qX = r ++ rest) (hL : s.env rL = ℓ)
    (hℓw : ℓ + 1 < 2 ^ w) (hrw : ∀ v ∈ r, v < 2 ^ w) (c : ℕ × ℕ × ℕ)
    (hc : (s.env rCo, s.env rCl, s.env rCs) = c) (hcw : c.1 < 2 ^ w ∧ c.2.1 < 2 ^ w ∧ c.2.2 < 2 ^ w)
    (hK : s.env rK + 1 < 2 ^ w) :
    ∃ s', Good x w pJStep s s' ((ℓ + 20) * (12 * Ex.nodeCost w)) ∧
      s'.stk qX = rest ∧
      s'.stk qAns = (if Join.isLoc (ℓ + 2) r then [] else jAns ℓ c r) ++ s.stk qAns ∧
      (∀ q, q ≠ qX → q ≠ qAns → q ≠ qJunk → s'.stk q = s.stk q) ∧
      (s'.env rCo, s'.env rCl, s'.env rCs) =
        (if Join.isLoc (ℓ + 2) r then jCur ℓ r else c) ∧
      s'.env rK = s.env rK + 1 ∧ s'.pos = s.pos ∧ s'.out = s.out ∧
      ∀ q, wReg q pJStep = false → s'.env q = s.env q := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  obtain ⟨a, b, bits, tg, d1, d2, d3, rfl, hbits⟩ := ex_rec ℓ r hr
  obtain ⟨g1, g2, g3, g4, g5⟩ := rec_getD (a := a) (b := b) (tg := tg) (d1 := d1) (d2 := d2)
    (d3 := d3) hbits
  have hw1 : ∀ v ∈ bits, v < 2 ^ w := fun v hv => hrw v (by simp [hv])
  have hd1 : d1 < 2 ^ w := hrw d1 (by simp)
  have hd2 : d2 < 2 ^ w := hrw d2 (by simp)
  have hd3 : d3 < 2 ^ w := hrw d3 (by simp)
  have hb : b < 2 ^ w := hrw b (by simp)
  have htw : tg < 2 ^ w := hrw tg (by simp)
  have h4 : (4 : ℕ) ≤ 2 ^ w := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  obtain ⟨s1, r1, h1X, h1S, h1i, h1t, h1d1, h1d2, h1d3, h1p, h1o, h1e⟩ :=
    pJPop_good (x := x) hw s hbits (by rw [hX]) hL hℓw hw1
  have e1 : ∀ q, q ≠ rV → q ≠ rJi → q ≠ rI → q ≠ rT → q ≠ rTg → q ≠ rD1 → q ≠ rD2 →
      q ≠ rD3 → s1.env q = s.env q := by
    intro q n1 n2 n3 n4 n5 n6 n7 n8
    refine h1e q ?_
    simp [pJPop, moveN, wReg, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm,
      n8.symm]
  have eCo : s1.env rCo = c.1 := by
    rw [e1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), ← hc]
  have eCl : s1.env rCl = c.2.1 := by
    rw [e1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), ← hc]
  have eCs : s1.env rCs = c.2.2 := by
    rw [e1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), ← hc]
  have eK : s1.env rK = s.env rK := by
    rw [e1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
  set r := a :: b :: bits ++ [tg, d1, d2, d3]
  by_cases htg : tg = 0
  · -- a location record
    have hloc : Join.isLoc (ℓ + 2) r = true := by
      simp only [Join.isLoc, g2, htg, beq_self_eq_true]
    have r2a := Good.set (x := x) (w := w) (r := rCo) (e := rv rD1) (st := s1)
      (by simp only [Ex.Fits, rv, h1d1]; exact hd1)
    set s2a := s1.set rCo ((rv rD1 : Ex CR).eval s1.env)
    have r2b := Good.set (x := x) (w := w) (r := rCl) (e := rv rD2) (st := s2a)
      (by simp only [Ex.Fits, rv, s2a, NSt.set_env, Function.update_of_ne (show rD2 ≠ rCo by decide), h1d2]; exact hd2)
    set s2b := s2a.set rCl ((rv rD2 : Ex CR).eval s2a.env)
    have ei : s2b.env rJi = b := by
      simp [s2b, s2a, Function.update_of_ne (show rJi ≠ rCl by decide),
        Function.update_of_ne (show rJi ≠ rCo by decide), h1i]
    have e3 : s2b.env rD3 = d3 := by
      simp [s2b, s2a, Function.update_of_ne (show rD3 ≠ rCl by decide),
        Function.update_of_ne (show rD3 ≠ rCo by decide), h1d3]
    have r2c := Good.set (x := x) (w := w) (r := rCs) (e := seedEx) (st := s2b) (by
      simp only [seedEx, Ex.Fits, Ex.eval, rv, ei, e3]
      split_ifs <;> (repeat' constructor) <;> omega)
    set s2 := s2b.set rCs (seedEx.eval s2b.env)
    have r2 := Good.iteF (x := x) (w := w) (e := rv rTg) (p := pJAns) (q := pJLoc) (st := s1)
      (by simp only [Ex.Fits, rv, h1t]; omega) (by simp [rv, Ex.eval, h1t, htg])
      (r2a.seq (r2b.seq r2c))
    have eK2 : s2.env rK = s.env rK := by
      simp [s2, s2b, s2a, Function.update_of_ne (show rK ≠ rCs by decide),
        Function.update_of_ne (show rK ≠ rCl by decide),
        Function.update_of_ne (show rK ≠ rCo by decide), eK]
    have r3 := Good.set (x := x) (w := w) (r := rK) (e := .add (rv rK) (.const 1)) (st := s2)
      (by simp only [Ex.Fits, Ex.eval, rv, eK2]; omega)
    have hall := r1.seq (r2.seq r3)
    refine ⟨_, hall.mono ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => hall.env_of hq⟩
    · simp only [condCost, rv, Ex.size, seedEx]; nlinarith
    · exact h1X
    · simp only [hloc, if_true, List.nil_append]
      simp only [NSt.set_stk, s2, s2b, s2a]; exact h1S _ (by decide) (by decide)
    · intro q n1 n2 n3; simp only [NSt.set_stk, s2, s2b, s2a]; exact h1S q n1 n3
    · simp only [hloc, if_true, jCur, g1, g3, g4, g5]
      simp [s2, s2b, s2a, Function.update_of_ne (show rCo ≠ rK by decide),
        Function.update_of_ne (show rCl ≠ rK by decide),
        Function.update_of_ne (show rCs ≠ rK by decide),
        Function.update_of_ne (show rCo ≠ rCs by decide),
        Function.update_of_ne (show rCl ≠ rCs by decide),
        Function.update_of_ne (show rCo ≠ rCl by decide), h1d1, h1d2, ei, e3, seedEx, seedV,
        Function.update_of_ne (show rD2 ≠ rCo by decide), Function.update_of_ne (show rJi ≠ rCl by decide),
        Function.update_of_ne (show rJi ≠ rCo by decide), Function.update_of_ne (show rD3 ≠ rCl by decide),
        Function.update_of_ne (show rD3 ≠ rCo by decide), h1i, h1d3,
        Ex.eval, rv]
    · simp [eK2, Ex.eval, rv]
    · simp [s2, s2b, s2a, h1p]
    · simp [s2, s2b, s2a, h1o]
  · -- a request
    have hloc : Join.isLoc (ℓ + 2) r = false := by
      simp only [Join.isLoc, g2]; simpa using htg
    have r2a := Good.push (x := x) (w := w) (q := qAns) (e := rv rCs) (st := s1)
      (by simp only [Ex.Fits, rv, eCs]; exact hcw.2.2)
    set s2a := s1.setS qAns ((rv rCs : Ex CR).eval s1.env :: s1.stk qAns)
    have r2b := Good.push (x := x) (w := w) (q := qAns) (e := rv rCl) (st := s2a)
      (by simp only [Ex.Fits, rv, s2a, NSt.setS_env, eCl]; exact hcw.2.1)
    set s2b := s2a.setS qAns ((rv rCl : Ex CR).eval s2a.env :: s2a.stk qAns)
    have r2c := Good.push (x := x) (w := w) (q := qAns) (e := rv rCo) (st := s2b)
      (by simp only [Ex.Fits, rv, s2b, s2a, NSt.setS_env, eCo]; exact hcw.1)
    set s2c := s2b.setS qAns ((rv rCo : Ex CR).eval s2b.env :: s2b.stk qAns)
    have r2d := Good.push (x := x) (w := w) (q := qAns) (e := rv rD1) (st := s2c)
      (by simp only [Ex.Fits, rv, s2c, s2b, s2a, NSt.setS_env, h1d1]; exact hd1)
    set s2 := s2c.setS qAns ((rv rD1 : Ex CR).eval s2c.env :: s2c.stk qAns)
    have r2 := Good.iteT (x := x) (w := w) (e := rv rTg) (p := pJAns) (q := pJLoc) (st := s1)
      (by simp only [Ex.Fits, rv, h1t]; omega) (by simp [rv, Ex.eval, h1t, htg])
      (r2a.seq (r2b.seq (r2c.seq r2d)))
    have eK2 : s2.env rK = s.env rK := eK
    have r3 := Good.set (x := x) (w := w) (r := rK) (e := .add (rv rK) (.const 1)) (st := s2)
      (by simp only [Ex.Fits, Ex.eval, rv, eK2]; omega)
    have hall := r1.seq (r2.seq r3)
    refine ⟨_, hall.mono ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => hall.env_of hq⟩
    · simp only [condCost, rv, Ex.size]; nlinarith
    · simp only [NSt.set_stk, s2, s2c, s2b, s2a, NSt.setS_stk]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide), h1X]
    · simp only [hloc, Bool.false_eq_true, if_false, jAns, g3]
      simp only [NSt.set_stk, s2, s2c, s2b, s2a, NSt.setS_stk, Function.update_self, NSt.setS_env,
        Ex.eval, rv, eCo, eCl, eCs, h1d1]
      rw [h1S _ (by decide) (by decide)]; rfl
    · intro q n1 n2 n3
      simp only [NSt.set_stk, s2, s2c, s2b, s2a, NSt.setS_stk]
      rw [Function.update_of_ne n2, Function.update_of_ne n2, Function.update_of_ne n2,
        Function.update_of_ne n2, h1S q n1 n3]
    · simp only [hloc, Bool.false_eq_true, if_false]
      simp only [NSt.set_env, s2, s2c, s2b, s2a, NSt.setS_env,
        Function.update_of_ne (show rCo ≠ rK by decide),
        Function.update_of_ne (show rCl ≠ rK by decide),
        Function.update_of_ne (show rCs ≠ rK by decide), eCo, eCl, eCs]
    · simp [eK2, Ex.eval, rv]
    · simp [s2, s2c, s2b, s2a, h1p]
    · simp [s2, s2c, s2b, s2a, h1o]

lemma getD_lt {r : List ℕ} {w : ℕ} (hrw : ∀ v ∈ r, v < 2 ^ w) (hw : 0 < 2 ^ w) (i : ℕ) :
    r.getD i 0 < 2 ^ w := by
  rw [List.getD_eq_getElem?_getD]
  cases h : r[i]? with
  | none => simpa using hw
  | some v => exact hrw v (List.mem_of_getElem? h)

set_option maxHeartbeats 1000000 in
/-- **The scan.** Over the records `L` on `qX` (each of `ℓ + 6` words), `pJScan` pushes the
answers of `jScan` onto `qAns` (the last answer on top). -/
theorem pJScan_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (st : NSt CR CQ) {ℓ : ℕ}
    (L : List (List ℕ)) (hX : st.stk qX = L.flatten) (hL : st.env rL = ℓ)
    (hN : st.env rN = L.length) (hlen : ∀ r ∈ L, r.length = ℓ + 6)
    (hrw : ∀ r ∈ L, ∀ v ∈ r, v < 2 ^ w) (hℓw : ℓ + 1 < 2 ^ w) (hnw : L.length + 1 < 2 ^ w)
    (hcw : st.env rCo < 2 ^ w ∧ st.env rCl < 2 ^ w ∧ st.env rCs < 2 ^ w) :
    ∃ st', Good x w pJScan st st' ((L.length + 1) * ((ℓ + 21) * (12 * Ex.nodeCost w))) ∧
      st'.stk qX = [] ∧
      st'.stk qAns = (jScan ℓ (st.env rCo, st.env rCl, st.env rCs) L).reverse.flatten ++
        st.stk qAns ∧
      (∀ q, q ≠ qX → q ≠ qAns → q ≠ qJunk → st'.stk q = st.stk q) ∧
      st'.pos = st.pos ∧ st'.out = st.out ∧
      ∀ q, wReg q pJScan = false → st'.env q = st.env q := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hw0 : 0 < 2 ^ w := by positivity
  set c0 := (st.env rCo, st.env rCl, st.env rCs)
  set n := L.length
  have hcur : ∀ j, (jCurAfter ℓ c0 (L.take j)).1 < 2 ^ w ∧
      (jCurAfter ℓ c0 (L.take j)).2.1 < 2 ^ w ∧ (jCurAfter ℓ c0 (L.take j)).2.2 < 2 ^ w := by
    intro j
    rcases Join.curAfter_cases (ℓ + 2) (jCur ℓ) c0 (L.take j) with h | ⟨m, hm, h⟩
    · simp only [jCurAfter]; rw [h]; exact hcw
    · simp only [jCurAfter]; rw [h]
      have hm' := hrw m (List.mem_of_mem_take hm)
      refine ⟨getD_lt hm' hw0 _, getD_lt hm' hw0 _, ?_⟩
      have := seedV_le (m.getD 1 0) (m.getD (ℓ + 5) 0)
      have : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
      simp only [jCur]; omega
  have r0 := Good.set (x := x) (w := w) (r := rK) (e := .const 0) (st := st)
    (by simp only [Ex.Fits]; omega)
  set s0 := st.set rK ((Ex.const 0 : Ex CR).eval st.env)
  set Inv : NSt CR CQ → Prop := fun s => s.env rK ≤ n ∧ s.env rN = n ∧ s.env rL = ℓ ∧
    s.stk qX = (L.drop (s.env rK)).flatten ∧
    s.stk qAns = (jScan ℓ c0 (L.take (s.env rK))).reverse.flatten ++ st.stk qAns ∧
    (∀ q, q ≠ qX → q ≠ qAns → q ≠ qJunk → s.stk q = st.stk q) ∧
    (s.env rCo, s.env rCl, s.env rCs) = jCurAfter ℓ c0 (L.take (s.env rK)) ∧
    s.pos = st.pos ∧ s.out = st.out ∧ ∀ q, wReg q pJScan = false → s.env q = st.env q
    with hInv
  have hloop := Good.loop_var (x := x) (w := w) (e := .lt (rv rK) (rv rN)) (body := pJStep)
    Inv (fun s => n - s.env rK) (fun _ => 0) 0 ((ℓ + 20) * (12 * Ex.nodeCost w)) (by
      intro s ⟨hk, hn, hl, hx, ha, hS, hc, hp, ho, he⟩
      refine ⟨⟨by simp only [rv, Ex.Fits]; omega, by simp only [rv, Ex.Fits]; omega⟩, ?_⟩
      intro hcond
      have hlt : s.env rK < n := by simpa [rv, Ex.eval, hn] using hcond
      set j := s.env rK
      have hjL : j < L.length := hlt
      have hd : L.drop j = L[j] :: L.drop (j + 1) := List.drop_eq_getElem_cons hjL
      obtain ⟨s', r', h1, h2, h3, h4, h5, h6, h7, h8⟩ := pJStep_good (x := x) hw s L[j]
        (L.drop (j + 1)).flatten (hlen _ (List.getElem_mem _)) (by rw [hx, hd]; rfl) hl hℓw
        (hrw _ (List.getElem_mem _)) _ hc (hcur j) (by omega)
      have htk : L.take (j + 1) = L.take j ++ [L[j]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hjL]; rfl
      refine ⟨s', r'.mono (by simp), ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by omega,
        le_rfl⟩
      · rw [h8 _ (by decide), hn]
      · rw [h8 _ (by decide), hl]
      · rw [h5, h1]
      · rw [h5, h2, htk, jScan, Join.scanF_append_single, ha]
        split_ifs <;> simp
      · intro q n1 n2 n3; rw [h3 q n1 n2 n3, hS q n1 n2 n3]
      · rw [h4, h5, htk]; simp only [jCurAfter]; rw [Join.curAfter_append_single]
      · rw [h6, hp]
      · rw [h7, ho]
      · intro q hq
        rw [h8 q (by simp only [pJScan, wReg, Bool.or_eq_false_iff] at hq; exact hq.2), he q hq])
    s0 ⟨by simp [s0, Ex.eval], by simp [s0, Function.update_of_ne (show rN ≠ rK by decide), hN],
      by simp [s0, Function.update_of_ne (show rL ≠ rK by decide), hL],
      by simp [s0, Ex.eval, hX], by simp [s0, Ex.eval, jScan, Join.scanF],
      fun q _ _ _ => rfl,
      by simp [s0, Ex.eval, jCurAfter, Join.curAfter, c0,
        Function.update_of_ne (show rCo ≠ rK by decide),
        Function.update_of_ne (show rCl ≠ rK by decide),
        Function.update_of_ne (show rCs ≠ rK by decide)],
      rfl, rfl, fun q hq => by
        simp only [pJScan, wReg, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hq
        simp [s0, Function.update_of_ne (Ne.symm hq.1)]⟩
  obtain ⟨s', r', ⟨hk, hn, -, hx, ha, hS, -, hp, ho, he⟩, hc⟩ := hloop
  have hkn : s'.env rK = n := by
    simp only [Ex.eval, rv, hn] at hc; split_ifs at hc with h <;> omega
  refine ⟨s', (r0.seq r').mono ?_, ?_, ?_, hS, hp, ho, he⟩
  · have h0 : n - s0.env rK = n := by simp [s0, Ex.eval]
    rw [h0]; simp only [condCost, rv, Ex.size]; nlinarith
  · rw [hx, hkn]; simp [n]
  · rw [ha, hkn, List.take_of_length_le (le_of_eq rfl)]

end Lax119563Proofs.Compiler
