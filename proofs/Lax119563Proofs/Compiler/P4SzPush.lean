import Lax119563Proofs.Compiler.P4Loc

/-!
# Pass `P4` (program): the class sizes of one schema

From the arity (`rA`), `|D|` (`rD`), `nEnt` (`rNe`) and `|coefSteps|` (`rNc`), `p4SPush`
pushes `schSizes I e` (in order, so reversed on the stack) on `qSzA`, adding them to `rNt`
(**`p4SPush_good`**, list form `szL`, `schSizes_eq_szL`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

/-! ## Registers of the schema-size scan -/

def rC : Fin CR := 20
def rC2 : Fin CR := 21
def rNe : Fin CR := 22
def rNc : Fin CR := 23
def rTq : Fin CR := 24
def rV4 : Fin CR := 25
def rV2 : Fin CR := 26
def rS : Fin CR := 27
/-- Scratch stack for the schema records (forward). -/
def qT : Fin CQ := 2

/-! ## List form -/

/-- The class sizes of a schema with arity flag `t`, `|D| = d`, `nEnt = nE`, `|coef| = nC`. -/
def szL (t : Bool) (d nE nC : ℕ) : List ℕ :=
  (List.replicate d (jlSizes t)).flatten ++ List.replicate nE 4 ++
    (List.replicate d (if t then [2] else [])).flatten ++ List.replicate nE 2 ++
      List.replicate nC 2

lemma flatMap_const' {α β : Type*} (l : List α) (m : List β) :
    l.flatMap (fun _ => m) = (List.replicate l.length m).flatten := by
  induction l with
  | nil => rfl
  | cons a l ih => simp (config := { decide := true }) [ih, List.replicate_succ]

lemma schSizes_eq_szL {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ) (e : Fin I.schemas.length) :
    schSizes I e = szL (Matrix.isTern (sch I e)) (coordList (dom I e)).length (nEnt I e)
      (coefSteps I e).length := by
  rw [schSizes, szL, flatMap_const', flatMap_const']

lemma rep_pair_rev (a b : ℕ) : ∀ d : ℕ,
    ((List.replicate d [a, b]).flatten).reverse = (List.replicate d [b, a]).flatten
  | 0 => rfl
  | d + 1 => by
    rw [List.replicate_succ', List.flatten_append, List.reverse_append, rep_pair_rev a b d,
      List.replicate_succ]
    simp

lemma rep_two_flatten (d : ℕ) : (List.replicate d [2]).flatten = List.replicate d 2 := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [List.replicate_succ, List.flatten_cons, ih]; rfl

lemma rep_nil_flatten (d : ℕ) : (List.replicate d ([] : List ℕ)).flatten = [] := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [List.replicate_succ, List.flatten_cons, ih]; rfl

lemma szL_rev (t : Bool) (d nE nC : ℕ) :
    (szL t d nE nC).reverse =
      List.replicate nC 2 ++ List.replicate nE 2 ++ List.replicate (if t then d else 0) 2 ++
        (List.replicate nE 4 ++
          (if t then (List.replicate d [2, 4]).flatten else List.replicate d 2)) := by
  cases t
  · simp only [szL, jlSizes, Bool.false_eq_true, if_false, rep_two_flatten, rep_nil_flatten,
      List.reverse_append, List.reverse_replicate, List.reverse_nil, List.replicate_zero,
      List.append_assoc, List.nil_append, List.append_nil]
  · simp only [szL, jlSizes, if_true, rep_two_flatten, List.reverse_append,
      List.reverse_replicate, rep_pair_rev, List.append_assoc]

lemma szL_sum (t : Bool) (d nE nC : ℕ) :
    (szL t d nE nC).sum = d * (if t then 6 else 2) + nE * 4 + (if t then d else 0) * 2 +
      nE * 2 + nC * 2 := by
  have h1 : ∀ m : List ℕ, ((List.replicate d m).flatten).sum = d * m.sum := by
    intro m; induction d with
    | zero => simp
    | succ d ih => rw [List.replicate_succ, List.flatten_cons, List.sum_append, ih]; ring
  simp only [szL, List.sum_append, List.sum_replicate, h1, smul_eq_mul, jlSizes]
  cases t <;> simp <;> ring

/-! ## The program -/

/-- Push the class sizes of the current schema. -/
def p4SPush : CStm CR CQ :=
  .seq (.set rTq (.lt (.const 2) (rv rA))) (.seq (.set rV4 (.const 4)) (.seq (.set rV2 (.const 2))
    (.seq (.ite (rv rTq) (rep2PushS qSzA rV4 rV2 rD rK rNt) (repPushS qSzA rV2 rD rK rNt))
    (.seq (repPushS qSzA rV4 rNe rK rNt) (.seq (.set rS (.add (rv rNe) (rv rNc)))
    (.seq (.ite (rv rTq) (.set rS (.add (rv rS) (rv rD))) .skip)
      (repPushS qSzA rV2 rS rK rNt)))))))

lemma p4SPush_arith {N U d nE nC td : ℕ} (hU : U ≤ N) (hU' : 64 ≤ U) (htd : td ≤ d) :
    (1 + 1 + 1) * N + U + (1 * N + U + (1 * N + U + (2 * N + 1 + (d + 1) * (30 * N) +
      ((nE + 1) * (20 * N) + ((1 + 1 + 1) * N + U + (2 * N + 1 + (3 * N + U) +
        (td + nE + nC + 1) * (20 * N))))))) ≤ (2 * d + 2 * nE + nC + 10) * (30 * N) := by
  nlinarith

/-- **The class sizes of one schema.** -/
lemma p4SPush_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (s : NSt CR CQ) (t : Bool)
    {d nE nC A : ℕ} (hA : s.env rA = if t then 3 else 2) (hD : s.env rD = d)
    (hE : s.env rNe = nE) (hC : s.env rNc = nC) (hN : s.env rNt = A)
    (hw' : A + (szL t d nE nC).sum + 8 < 2 ^ w) :
    ∃ s', Good x w p4SPush s s' ((2 * d + 2 * nE + nC + 10) * (30 * Ex.nodeCost w)) ∧
      s'.stk = Function.update s.stk qSzA ((szL t d nE nC).reverse ++ s.stk qSzA) ∧
      s'.env rNt = A + (szL t d nE nC).sum ∧ s'.pos = s.pos ∧ s'.out = s.out := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hsum := szL_sum t d nE nC
  have hAw : s.env rA < 2 ^ w := by rw [hA]; split_ifs <;> omega
  have r1 := Good.set (x := x) (w := w) (st := s) (r := rTq) (e := .lt (.const 2) (rv rA))
    (by simp only [Ex.Fits, rv]; omega)
  set s1 := s.set rTq ((Ex.lt (.const 2) (rv rA) : Ex CR).eval s.env)
  have r2 := Good.set (x := x) (w := w) (st := s1) (r := rV4) (e := .const 4)
    (by simp only [Ex.Fits]; omega)
  set s2 := s1.set rV4 ((Ex.const 4 : Ex CR).eval s1.env)
  have r3 := Good.set (x := x) (w := w) (st := s2) (r := rV2) (e := .const 2)
    (by simp only [Ex.Fits]; omega)
  set s3 := s2.set rV2 ((Ex.const 2 : Ex CR).eval s2.env)
  have e3 : ∀ r, r ≠ rTq → r ≠ rV4 → r ≠ rV2 → s3.env r = s.env r := fun r h1 h2 h3 => by
    simp (config := { decide := true }) [s3, s2, s1, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3]
  have e3T : s3.env rTq = if t then 1 else 0 := by
    simp (config := { decide := true }) [s3, s2, s1, Ex.eval, rv, hA]; cases t <;> simp
  have e3V4 : s3.env rV4 = 4 := by simp (config := { decide := true }) [s3, s2, Ex.eval]
  have e3V2 : s3.env rV2 = 2 := by simp (config := { decide := true }) [s3, Ex.eval]
  have hTF : (rv rTq : Ex CR).Fits w s3.env := by
    simp only [Ex.Fits, rv, e3T]; split_ifs <;> omega
  -- the junction/link sizes
  obtain ⟨B1, hB1⟩ : ∃ B1, B1 = d * (if t then 6 else 2) := ⟨_, rfl⟩
  obtain ⟨td, htd⟩ : ∃ td, td = if t then d else 0 := ⟨_, rfl⟩
  have hdB1 : d ≤ B1 := by rw [hB1]; cases t <;> simp <;> omega
  have htdd : td ≤ d := by rw [htd]; cases t <;> simp
  have hsum' : (szL t d nE nC).sum = B1 + nE * 4 + td * 2 + nE * 2 + nC * 2 := by
    rw [hsum, hB1, htd]
  clear hsum
  obtain ⟨P1, hP1⟩ : ∃ P1 : List ℕ, P1 = if t then (List.replicate d [2, 4]).flatten
      else List.replicate d 2 := ⟨_, rfl⟩
  have hD3 : s3.env rD = d := by rw [e3 _ (by decide) (by decide) (by decide), hD]
  have hN3 : s3.env rNt = A := by rw [e3 _ (by decide) (by decide) (by decide), hN]
  have hdw : d + 1 < 2 ^ w := by omega
  obtain ⟨s4, r4, e4⟩ : ∃ s4, Good x w (.ite (rv rTq) (rep2PushS qSzA rV4 rV2 rD rK rNt)
      (repPushS qSzA rV2 rD rK rNt)) s3 s4 (2 * Ex.nodeCost w + 1 + (d + 1) * (30 * Ex.nodeCost w)) ∧
      s4 = ((s3.setS qSzA (P1 ++ s3.stk qSzA)).set rNt (A + B1)).set rK d := by
    cases t
    · simp only [Bool.false_eq_true, if_false] at hB1 hP1
      subst hB1 hP1
      have g := repPushS_good (x := x) (w := w) hw (q := qSzA) (v := rV2) (n := rD) (j := rK)
        (acc := rNt) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        s3 e3V2 hD3 hN3 hdw (by omega)
      refine ⟨_, (CStm.Good.iteF hTF (by simp (config := { decide := true }) [rv, Ex.eval, e3T]) g).mono ?_, rfl⟩
      have : (d + 1) * (20 * Ex.nodeCost w) ≤ (d + 1) * (30 * Ex.nodeCost w) :=
        Nat.mul_le_mul_left _ (by omega)
      simp only [condCost, rv, Ex.size]; omega
    · simp only [if_true] at hB1 hP1
      subst hB1 hP1
      have g := rep2PushS_good (x := x) (w := w) hw (q := qSzA) (v₁ := rV4) (v₂ := rV2)
        (n := rD) (j := rK) (acc := rNt) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        s3 e3V4 e3V2 hD3 hN3 hdw (by omega)
      refine ⟨_, (CStm.Good.iteT hTF (by simp (config := { decide := true }) [rv, Ex.eval, e3T]) g).mono ?_, rfl⟩
      simp only [condCost, rv, Ex.size]; omega
  have e4r : ∀ r, r ≠ rK → r ≠ rNt → s4.env r = s3.env r := fun r h1 h2 => by
    rw [e4]; simp (config := { decide := true }) [Function.update_of_ne h1, Function.update_of_ne h2]
  -- the entry sizes
  have hE4 : s4.env rNe = nE := by
    rw [e4r _ (by decide) (by decide), e3 _ (by decide) (by decide) (by decide), hE]
  have r5 := repPushS_good (x := x) (w := w) hw (q := qSzA) (v := rV4) (n := rNe) (j := rK)
    (acc := rNt) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    s4 (V := 4) (N := nE) (A := A + B1) (by rw [e4r _ (by decide) (by decide), e3V4]) hE4
    (by rw [e4]; simp (config := { decide := true })) (by omega) (by omega)
  set s5 := ((s4.setS qSzA (List.replicate nE 4 ++ s4.stk qSzA)).set rNt
    (A + B1 + nE * 4)).set rK nE
  have e5r : ∀ r, r ≠ rK → r ≠ rNt → s5.env r = s3.env r := fun r h1 h2 => by
    rw [← e4r r h1 h2]; simp (config := { decide := true }) [s5, Function.update_of_ne h1, Function.update_of_ne h2]
  have e5E : s5.env rNe = nE := by rw [e5r _ (by decide) (by decide), e3 _ (by decide) (by decide) (by decide), hE]
  have e5C : s5.env rNc = nC := by rw [e5r _ (by decide) (by decide), e3 _ (by decide) (by decide) (by decide), hC]
  have r6 := Good.set (x := x) (w := w) (st := s5) (r := rS) (e := .add (rv rNe) (rv rNc))
    (by simp only [Ex.Fits, rv, Ex.eval, e5E, e5C]; refine ⟨?_, ?_, ?_⟩ <;> omega)
  set s6 := s5.set rS ((Ex.add (rv rNe) (rv rNc) : Ex CR).eval s5.env)
  have e6r : ∀ r, r ≠ rS → r ≠ rK → r ≠ rNt → s6.env r = s3.env r := fun r h0 h1 h2 => by
    rw [← e5r r h1 h2]; simp (config := { decide := true }) [s6, Function.update_of_ne h0]
  have e6S : s6.env rS = nE + nC := by simp (config := { decide := true }) [s6, Ex.eval, rv, e5E, e5C]
  obtain ⟨s7, r7, e7S, e7r, e7s, e7p, e7o⟩ : ∃ s7, Good x w (.ite (rv rTq)
      (.set rS (.add (rv rS) (rv rD))) .skip) s6 s7 (2 * Ex.nodeCost w + 1 + (3 * Ex.nodeCost w +
        unitCost w)) ∧
      s7.env rS = td + nE + nC ∧ (∀ r, r ≠ rS → s7.env r = s6.env r) ∧ s7.stk = s6.stk ∧
      s7.pos = s6.pos ∧ s7.out = s6.out := by
    have hTF6 : (rv rTq : Ex CR).Fits w s6.env := by
      simp only [Ex.Fits, rv, e6r _ (show rTq ≠ rS by decide) (by decide) (by decide)]
      exact hTF
    have hT6 : s6.env rTq = if t then 1 else 0 := by
      rw [e6r _ (by decide) (by decide) (by decide), e3T]
    cases t
    · simp only [Bool.false_eq_true, if_false] at htd; subst htd
      refine ⟨s6, (CStm.Good.iteF hTF6 (by simp (config := { decide := true }) [rv, Ex.eval, hT6]) CStm.Good.skip).mono ?_, ?_,
        fun _ _ => rfl, rfl, rfl, rfl⟩
      · simp only [condCost, rv, Ex.size]; omega
      · rw [e6S]; ring
    · simp only [if_true] at htd
      have hD6 : s6.env rD = d := by
        rw [e6r _ (by decide) (by decide) (by decide), e3 _ (by decide) (by decide) (by decide), hD]
      have g := Good.set (x := x) (w := w) (st := s6) (r := rS) (e := .add (rv rS) (rv rD))
        (by simp only [Ex.Fits, rv, Ex.eval, e6S, hD6]; refine ⟨?_, ?_, ?_⟩ <;> omega)
      refine ⟨_, (CStm.Good.iteT hTF6 (by simp (config := { decide := true }) [rv, Ex.eval, hT6]) g).mono ?_, ?_,
        fun r hr => by simp (config := { decide := true }) [Function.update_of_ne hr], rfl, rfl, rfl⟩
      · simp only [condCost, rv, Ex.size]; omega
      · rw [htd]; simp (config := { decide := true }) [Ex.eval, rv, e6S, hD6]; ring
  have hN7 : s7.env rNt = A + B1 + nE * 4 := by
    rw [e7r _ (by decide)]; simp (config := { decide := true }) [s6, s5]
  have r8 := repPushS_good (x := x) (w := w) hw (q := qSzA) (v := rV2) (n := rS) (j := rK)
    (acc := rNt) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    s7 (V := 2) (N := td + nE + nC) (A := A + B1 + nE * 4)
    (by rw [e7r _ (by decide), e6r _ (by decide) (by decide) (by decide), e3V2]) e7S hN7
    (by omega) (by omega)
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq r8))))))).mono ?_,
    ?_, ?_, ?_, ?_⟩
  · simp only [Ex.size, rv, condCost]
    exact p4SPush_arith hU hU' htdd
  · simp only [NSt.set_stk, NSt.setS_stk, e7s]
    show Function.update (Function.update s4.stk qSzA (List.replicate nE 4 ++ s4.stk qSzA)) qSzA
      (List.replicate (td + nE + nC) 2 ++ Function.update s4.stk qSzA
        (List.replicate nE 4 ++ s4.stk qSzA) qSzA) = _
    rw [e4]
    simp only [NSt.set_stk, NSt.setS_stk, Function.update_self, Function.update_idem]
    rw [szL_rev, show td + nE + nC = nC + nE + td by ring, List.replicate_add,
      List.replicate_add, ← htd, ← hP1]
    show Function.update s.stk qSzA _ = _
    simp only [List.append_assoc]; rfl
  · simp only [NSt.set_env, Function.update_of_ne (show rNt ≠ rK by decide), Function.update_self]
    rw [hsum']; ring
  · simp only [NSt.set_pos, NSt.setS_pos]; rw [e7p]
    show s4.pos = _; rw [e4]; rfl
  · simp only [NSt.set_out, NSt.setS_out]; rw [e7o]
    show s4.out = _; rw [e4]; rfl

end Lax119563Proofs.Compiler
