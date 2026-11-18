import Lax119563Proofs.Compiler.PJoin

/-!
# Pass `P3`, request generation: registers, stacks and the bit loop

The request of a column `c` of a schema for the argument with permutation
`π = (f, δ)` and location `u` is `u :: f(c.1) :: bits of (c.2 + δ_{c.1}) ++ [1, seq, 0, 0]`.
The bits of `c.2 + δ_{c.1}` are computed by `p3Bits`: it pops the bits of the column from
`qDom2` (pushing them onto `qDom`), the bits of the shift from `qDl2` (pushing them onto
`qAux`) and pushes their sums mod `2` onto `qRec` (**`p3Bits_good`**).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

/-! ## Stacks and registers of the request generation -/

def qF : Fin CQ := 5
def qF2 : Fin CQ := 6
def qDl : Fin CQ := 7
def qDl2 : Fin CQ := 8
def qAux : Fin CQ := 9
def qLs : Fin CQ := 10
def qLs2 : Fin CQ := 11
def qDom : Fin CQ := 14
def qDom2 : Fin CQ := 15

def rU : Fin CR := 20
def rFi : Fin CR := 21
def rCur : Fin CR := 22
def rBi : Fin CR := 23
def rB : Fin CR := 24
def rDb : Fin CR := 25
def rSq : Fin CR := 26
def rStr : Fin CR := 27
def rAi : Fin CR := 28
def rTn : Fin CR := 29
def rNw : Fin CR := 30
def rKL : Fin CR := 31
def rJ2 : Fin CR := 32
def rI2 : Fin CR := 33
def rT2 : Fin CR := 35

open CStm

/-- Bitwise sums mod `2`. -/
def xorL (bs ds : List ℕ) : List ℕ := List.zipWith (fun a b => (a + b) % 2) bs ds

lemma xorL_take_succ (bs ds : List ℕ) {j : ℕ} (h1 : j < bs.length) (h2 : j < ds.length) :
    xorL (bs.take (j + 1)) (ds.take (j + 1)) =
      xorL (bs.take j) (ds.take j) ++ [(bs[j] + ds[j]) % 2] := by
  rw [List.take_add_one, List.take_add_one, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2]
  simp only [Option.toList_some, xorL]
  rw [List.zipWith_append (by simp; omega)]
  rfl

/-- One bit. -/
def p3Bit : CStm CR CQ :=
  .seq (.pop qDom2 rB) (.seq (.push qDom (rv rB)) (.seq (.pop qDl2 rDb)
    (.seq (.push qAux (rv rDb)) (.seq (.push qRec (.odd (.add (rv rB) (rv rDb))))
      (.set rI (.add (rv rI) (.const 1)))))))

/-- The bit loop. -/
def p3Bits : CStm CR CQ := .seq (.set rI (.const 0)) (.loop (.lt (rv rI) (rv rL)) p3Bit)

/-- The stacks after `j` bits. -/
def bitsStk (S : Fin CQ → List ℕ) (j : ℕ) : Fin CQ → List ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update S
    qDom2 ((S qDom2).drop j)) qDom (((S qDom2).take j).reverse ++ S qDom))
    qDl2 ((S qDl2).drop j)) qAux (((S qDl2).take j).reverse ++ S qAux))
    qRec ((xorL ((S qDom2).take j) ((S qDl2).take j)).reverse ++ S qRec)

lemma bitsStk_zero (S : Fin CQ → List ℕ) : bitsStk S 0 = S := by
  funext q
  simp only [bitsStk, List.drop_zero, List.take_zero, List.reverse_nil, List.nil_append, xorL,
    List.zipWith_nil_left]
  simp [Function.update_eq_self]

set_option maxHeartbeats 1000000 in
/-- **The bit loop.** -/
lemma p3Bits_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (st : NSt CR CQ) {ℓ : ℕ}
    (hL : st.env rL = ℓ) (h1 : ℓ ≤ (st.stk qDom2).length) (h2 : ℓ ≤ (st.stk qDl2).length)
    (hb1 : ∀ v ∈ (st.stk qDom2).take ℓ, v ≤ 1) (hb2 : ∀ v ∈ (st.stk qDl2).take ℓ, v ≤ 1)
    (hℓw : ℓ + 1 < 2 ^ w) :
    ∃ st', Good x w p3Bits st st' ((ℓ + 1) * (20 * Ex.nodeCost w)) ∧
      st'.stk = bitsStk st.stk ℓ ∧ st'.pos = st.pos ∧ st'.out = st.out ∧
      ∀ r, wReg r p3Bits = false → st'.env r = st.env r := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  set S := st.stk
  set Inv : NSt CR CQ → Prop := fun s => s.env rI ≤ ℓ ∧ s.env rL = ℓ ∧
    s.stk = bitsStk S (s.env rI) ∧ s.pos = st.pos ∧ s.out = st.out with hInv
  have hloop := Good.loop_var (x := x) (w := w) (e := .lt (rv rI) (rv rL)) (body := p3Bit)
    Inv (fun s => ℓ - s.env rI) (fun _ => 0) 0 (16 * Ex.nodeCost w) (by
      intro s ⟨hi, hl, hs, hp, ho⟩
      refine ⟨⟨by simp only [rv, Ex.Fits]; omega, by simp only [rv, Ex.Fits]; omega⟩, ?_⟩
      intro hcond
      have hlt : s.env rI < ℓ := by simpa [rv, Ex.eval, hl] using hcond
      set j := s.env rI with hj
      have hd1 : (S qDom2).drop j = (S qDom2)[j] :: (S qDom2).drop (j + 1) :=
        List.drop_eq_getElem_cons (by omega)
      have hd2 : (S qDl2).drop j = (S qDl2)[j] :: (S qDl2).drop (j + 1) :=
        List.drop_eq_getElem_cons (by omega)
      have hv1 : (S qDom2)[j] ≤ 1 :=
        hb1 _ (List.mem_take_iff_getElem.mpr ⟨j, by simp; omega, rfl⟩)
      have hv2 : (S qDl2)[j] ≤ 1 :=
        hb2 _ (List.mem_take_iff_getElem.mpr ⟨j, by simp; omega, rfl⟩)
      have e1 : s.stk qDom2 = (S qDom2)[j] :: (S qDom2).drop (j + 1) := by
        rw [hs, ← hd1]; simp [bitsStk, qRec, qAux, qDl2, qDom, qDom2]
      have r1 := Good.pop_cons (x := x) (w := w) (r := rB) e1
      set s1 := (s.setS qDom2 ((S qDom2).drop (j + 1))).set rB (S qDom2)[j]
      have r2 := Good.push (x := x) (w := w) (q := qDom) (e := rv rB) (st := s1)
        (by simp only [Ex.Fits, rv, s1, NSt.set_env, Function.update_self]; omega)
      set s2 := s1.setS qDom ((rv rB : Ex CR).eval s1.env :: s1.stk qDom)
      have e2 : s2.stk qDl2 = (S qDl2)[j] :: (S qDl2).drop (j + 1) := by
        simp only [s2, s1, NSt.setS_stk, NSt.set_stk]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hs, ← hd2]
        simp [bitsStk, qRec, qAux, qDl2, qDom, qDom2]
      have r3 := Good.pop_cons (x := x) (w := w) (r := rDb) e2
      set s3 := (s2.setS qDl2 ((S qDl2).drop (j + 1))).set rDb (S qDl2)[j]
      have r4 := Good.push (x := x) (w := w) (q := qAux) (e := rv rDb) (st := s3)
        (by simp only [Ex.Fits, rv, s3, NSt.set_env, Function.update_self]; omega)
      set s4 := s3.setS qAux ((rv rDb : Ex CR).eval s3.env :: s3.stk qAux)
      have eB : s4.env rB = (S qDom2)[j] := by
        simp [s4, s3, s2, s1, Function.update_of_ne (show rB ≠ rDb by decide)]
      have eD : s4.env rDb = (S qDl2)[j] := by simp [s4, s3]
      have r5 := Good.push (x := x) (w := w) (q := qRec) (e := .odd (.add (rv rB) (rv rDb)))
        (st := s4) (by
          simp only [Ex.Fits, Ex.eval, rv, eB, eD]
          have := Nat.mod_lt ((S qDom2)[j] + (S qDl2)[j]) (show 2 > 0 by norm_num)
          (repeat' constructor) <;> omega)
      set s5 := s4.setS qRec ((Ex.odd (.add (rv rB) (rv rDb)) : Ex CR).eval s4.env :: s4.stk qRec)
      have eI : s5.env rI = j := by
        show Function.update (Function.update s.env rB (S qDom2)[j]) rDb (S qDl2)[j] rI = j
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
      have r6 := Good.set (x := x) (w := w) (r := rI) (e := .add (rv rI) (.const 1)) (st := s5)
        (by simp only [Ex.Fits, Ex.eval, rv, eI]; omega)
      refine ⟨_, ((r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6)))))).mono ?_, ⟨?_, ?_, ?_, ?_, ?_⟩,
        ?_, le_rfl⟩
      · simp only [rv, Ex.size]; omega
      · simp only [NSt.set_env, Function.update_self, Ex.eval, rv, eI]; omega
      · simp only [NSt.set_env, Function.update_of_ne (show rL ≠ rI by decide)]
        simp [s5, s4, s3, s2, s1, Function.update_of_ne (show rL ≠ rDb by decide),
          Function.update_of_ne (show rL ≠ rB by decide), hl]
      · simp only [NSt.set_env, Function.update_self, Ex.eval, rv, eI, NSt.set_stk]
        funext q
        by_cases q1 : q = qRec
        · subst q1
          simp [s5, s4, s3, s2, s1, hs, bitsStk, Function.update_of_ne (show qRec ≠ qAux by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qDom by decide), Function.update_self, Ex.eval, rv,
            eB, eD, Function.update_of_ne (show rB ≠ rDb by decide)]
          rw [xorL_take_succ _ _ (by omega) (by omega)]; simp
        by_cases q2 : q = qAux
        · subst q2
          simp [s5, s4, s3, s2, s1, hs, bitsStk, Function.update_of_ne (show qRec ≠ qAux by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qDom by decide), Function.update_self, Ex.eval, rv, Function.update_of_ne (show rB ≠ rDb by decide)]
          rw [List.take_add_one, List.getElem?_eq_getElem (show j < (S qDl2).length by omega)]
          simp only [Option.toList_some, List.reverse_append, List.reverse_cons, List.reverse_nil,
            List.nil_append, List.singleton_append, List.cons_append, List.append_assoc]
        by_cases q3 : q = qDl2
        · subst q3
          simp [s5, s4, s3, s2, s1, hs, bitsStk, Function.update_of_ne (show qRec ≠ qAux by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qDom by decide), Function.update_self]
        by_cases q4 : q = qDom
        · subst q4
          simp [s5, s4, s3, s2, s1, hs, bitsStk, Function.update_of_ne (show qRec ≠ qAux by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qDom by decide), Function.update_self, Ex.eval, rv, Function.update_of_ne (show rB ≠ rDb by decide)]
          rw [List.take_add_one, List.getElem?_eq_getElem (show j < (S qDom2).length by omega)]
          simp only [Option.toList_some, List.reverse_append, List.reverse_cons, List.reverse_nil,
            List.nil_append, List.singleton_append, List.cons_append, List.append_assoc]
        by_cases q5 : q = qDom2
        · subst q5
          simp [s5, s4, s3, s2, s1, hs, bitsStk, Function.update_of_ne (show qRec ≠ qAux by decide), Function.update_of_ne (show qRec ≠ qDl2 by decide), Function.update_of_ne (show qRec ≠ qDom by decide), Function.update_of_ne (show qRec ≠ qDom2 by decide), Function.update_of_ne (show qAux ≠ qRec by decide), Function.update_of_ne (show qAux ≠ qDl2 by decide), Function.update_of_ne (show qAux ≠ qDom by decide), Function.update_of_ne (show qAux ≠ qDom2 by decide), Function.update_of_ne (show qDl2 ≠ qRec by decide), Function.update_of_ne (show qDl2 ≠ qAux by decide), Function.update_of_ne (show qDl2 ≠ qDom by decide), Function.update_of_ne (show qDl2 ≠ qDom2 by decide), Function.update_of_ne (show qDom ≠ qRec by decide), Function.update_of_ne (show qDom ≠ qAux by decide), Function.update_of_ne (show qDom ≠ qDl2 by decide), Function.update_of_ne (show qDom ≠ qDom2 by decide), Function.update_of_ne (show qDom2 ≠ qRec by decide), Function.update_of_ne (show qDom2 ≠ qAux by decide), Function.update_of_ne (show qDom2 ≠ qDl2 by decide), Function.update_of_ne (show qDom2 ≠ qDom by decide), Function.update_self]
        simp [s5, s4, s3, s2, s1, hs, bitsStk, Function.update_apply, q1, q2, q3, q4, q5]
      · simp [s5, s4, s3, s2, s1, hp]
      · simp [s5, s4, s3, s2, s1, ho]
      · simp only [NSt.set_env, Function.update_self, Ex.eval, rv, eI]; omega)
  have r0 := Good.set (x := x) (w := w) (r := rI) (e := .const 0) (st := st)
    (by simp only [Ex.Fits]; omega)
  obtain ⟨s', r', ⟨hi, hl, hs, hp, ho⟩, hc⟩ := hloop (st.set rI 0) ⟨by simp,
    by simp [Function.update_of_ne (show rL ≠ rI by decide), hL],
    by simp [bitsStk_zero, S], rfl, rfl⟩
  have hiℓ : s'.env rI = ℓ := by
    simp only [Ex.eval, rv, hl] at hc; split_ifs at hc with h <;> omega
  have hall := r0.seq r'
  refine ⟨s', hall.mono ?_, by rw [hs, hiℓ], hp, ho, fun r hr => hall.env_of hr⟩
  simp only [condCost, rv, Ex.size, Ex.eval, NSt.set_env, Function.update_self, Nat.sub_zero,
    mul_zero, zero_add]
  nlinarith

end Lax119563Proofs.Compiler
