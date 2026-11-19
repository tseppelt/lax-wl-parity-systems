import Lax119563Proofs.Compiler.CSortMain
import Lax119563Proofs.Compiler.P3Aux

/-!
# Pass `P3`, second part: union sort, scan, sort of the answers

`p3Join` sorts the `rCnt + rSB` records of `ℓ + 6` words on `qX` (`sortS`), answers the
requests by the scan `pJScan` (answers on `qAns`) and sorts the `rSB` answers of `4` words
(**`p3Join_good`**: `qAns` ends holding `(ansAll I).flatten`, the order of `P4`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

/-! ## Registers of the sorts -/

/-- The record width of the sorts. -/
def rsA : Fin CR := 38
def rsDir : Fin CR := 20
def rsC : Fin CR := 21
def rsF1 : Fin CR := 22
def rsF2 : Fin CR := 23
def rsKc : Fin CR := 24
def rsT1 : Fin CR := 25
def rsT2 : Fin CR := 26
def rsI : Fin CR := 27
def rsT : Fin CR := 29
def rsR : Fin CR := 30
def rsDone : Fin CR := 39
def rsK : Fin CR := 32
def rsLim : Fin CR := 33

/-- Sort the `rN` records of `rsA` words on stack `X`. -/
def p3Sort (X : Fin CQ) : CStm CR CQ :=
  sortS X qT1 qT2 qY qTmp qC1 qC2 rsA rsDir rsC rsF1 rsF2 rsKc rsT1 rsT2 rsI rsT rsR rN rsDone
    rsK rsLim

/-- **The join part of `P3`.** -/
def p3Join : CStm CR CQ :=
  .seq (.set rN (.add (rv rCnt) (rv rSB))) (.seq (.set rsA (.add (rv rL) (.const 6)))
    (.seq (p3Sort qX) (.seq (.set rCo (.const 0)) (.seq (.set rCl (.const 0))
      (.seq (.set rCs (.const 0)) (.seq pJScan (.seq (.set rN (rv rSB))
        (.seq (.set rsA (.const 4)) (p3Sort qAns)))))))))

lemma log_le_of_le_four {n h : ℕ} (hn : n ≤ 4 * (h + 1)) :
    Nat.log 2 n ≤ Nat.log 2 (h + 1) + 2 := by
  calc Nat.log 2 n ≤ Nat.log 2 (2 * (2 * (h + 1))) := Nat.log_mono_right (by omega)
    _ ≤ Nat.log 2 (2 * (h + 1)) + 1 := log_two_mul_le _
    _ ≤ Nat.log 2 (h + 1) + 1 + 1 := by have := log_two_mul_le (h + 1); omega

lemma p3Join_arith (N U n m ℓ h lg ln lm : ℕ) (hU : U ≤ N) (hn : n * (ℓ + 1) ≤ 4 * h)
    (hℓ : ℓ ≤ h) (hm : m ≤ 3 * h) (hln : ln ≤ lg + 2) (hlm : lm ≤ lg + 2) (h3 : 3 ≤ h) :
    (1 + 1 + 1) * N + U + ((1 + 1 + 1) * N + U +
      ((n + 1) * (ln + 2) * (700 * (ℓ + 6 + 1) * N) + (1 * N + U + (1 * N + U + (1 * N + U +
        ((n + 1) * ((ℓ + 21) * (12 * N)) + (1 * N + U + (1 * N + U +
          (m + 1) * (lm + 2) * (700 * (4 + 1) * N))))))))) ≤
      150000 * (h + 1) * (lg + 1) * N := by
  have hn1 : n ≤ n * (ℓ + 1) := Nat.le_mul_of_pos_right _ (by omega)
  -- the first sort
  have p1 : (n + 1) * (ℓ + 7) ≤ 29 * (h + 1) := by
    have : (n + 1) * (ℓ + 7) = n * (ℓ + 1) + 6 * n + ℓ + 7 := by ring
    omega
  have q1 : ln + 2 ≤ 4 * (lg + 1) := by omega
  have t1 : (n + 1) * (ln + 2) * (700 * (ℓ + 6 + 1) * N) ≤
      700 * (29 * (h + 1)) * (4 * (lg + 1)) * N := by
    have : (n + 1) * (ln + 2) * (700 * (ℓ + 6 + 1) * N) =
        700 * ((n + 1) * (ℓ + 7)) * (ln + 2) * N := by ring
    rw [this]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ p1) q1)
  -- the scan
  have p2 : (n + 1) * (ℓ + 21) ≤ 105 * (h + 1) := by
    have : (n + 1) * (ℓ + 21) = n * (ℓ + 1) + 20 * n + ℓ + 21 := by ring
    omega
  have t2 : (n + 1) * ((ℓ + 21) * (12 * N)) ≤ 12 * (105 * (h + 1)) * (lg + 1) * N := by
    have : (n + 1) * ((ℓ + 21) * (12 * N)) = 12 * ((n + 1) * (ℓ + 21)) * 1 * N := by ring
    rw [this]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ p2) (by omega))
  -- the second sort
  have q3 : lm + 2 ≤ 4 * (lg + 1) := by omega
  have t3 : (m + 1) * (lm + 2) * (700 * (4 + 1) * N) ≤ 3500 * (3 * (h + 1)) * (4 * (lg + 1)) * N := by
    have : (m + 1) * (lm + 2) * (700 * (4 + 1) * N) = 3500 * (m + 1) * (lm + 2) * N := by ring
    rw [this]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) q3)
  have t0 : 20 * N ≤ 20 * (h + 1) * (lg + 1) * N := by
    have : 1 ≤ (h + 1) * (lg + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith
  have e : 700 * (29 * (h + 1)) * (4 * (lg + 1)) * N + 12 * (105 * (h + 1)) * (lg + 1) * N +
      3500 * (3 * (h + 1)) * (4 * (lg + 1)) * N + 20 * (h + 1) * (lg + 1) * N =
      124480 * ((h + 1) * (lg + 1) * N) := by ring
  have e' : 150000 * (h + 1) * (lg + 1) * N = 150000 * ((h + 1) * (lg + 1) * N) := by ring
  rw [e']
  omega

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

set_option maxHeartbeats 4000000 in
/-- **The join part of `P3`.** With `(union I).flatten` on `qX`, `rCnt = |locRecs I|`,
`rSB = |reqs I|`, `rL = ℓ` and `qT1, qT2, qY, qAns` empty, `p3Join` leaves the sorted answers
`(ansAll I).flatten` on `qAns` and empties `qX`. -/
theorem p3Join_good {w : ℕ} (hw : 2 ≤ w) (hk : 1 ≤ k) (hE : I.schemas ≠ [])
    (hS : 16 * (H I + 1) ≤ 2 ^ w)
    (s : NSt CR CQ) (hX : s.stk qX = (union I).flatten) (hT1 : s.stk qT1 = [])
    (hT2 : s.stk qT2 = []) (hY : s.stk qY = []) (hAns : s.stk qAns = []) (hL : s.env rL = ℓ)
    (hC : s.env rCnt = (locRecs I).length) (hSB : s.env rSB = (reqs I).length) :
    ∃ s', Good (encodeSystem I) w p3Join s s'
        (150000 * (H I + 1) * (Nat.log 2 (H I + 1) + 1) * Ex.nodeCost w) ∧
      s'.stk qAns = (ansAll I).flatten ∧ s'.stk qX = [] ∧
      (∀ q, q ≠ qX → q ≠ qAns → q ≠ qJunk → s'.stk q = s.stk q) ∧
      s'.pos = s.pos ∧ s'.out = s.out ∧ ∀ r, wReg r p3Join = false → s'.env r = s.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hU0 := Ex.unitCost_le_nodeCost w
  have hℓ := ell_le_H I hk (fun h => hE h.2)
  have h3H := three_le_H I
  have hcnt := union_mul_le I
  have hreq := length_reqs_mul_le I
  set n := (locRecs I).length + (reqs I).length with hn
  set m := (reqs I).length with hm
  have hn1 : n ≤ n * (ℓ + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hm1 : m ≤ m * (ℓ + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hw0 : 0 < 2 ^ w := by positivity
  have hrw : ∀ y ∈ union I, y.length = ℓ + 6 ∧ ∀ z ∈ y, z < 2 ^ w :=
    fun y hy => ⟨length_of_mem_union I hy, lt_of_mem_union I hE (by omega) hy⟩
  -- `rN := rCnt + rSB`
  have r1 := Good.set (x := encodeSystem I) (w := w) (st := s) (r := rN)
    (e := .add (rv rCnt) (rv rSB)) (by simp only [Ex.Fits, Ex.eval, rv, hC, hSB]; omega)
  set s1 := s.set rN ((Ex.add (rv rCnt) (rv rSB)).eval s.env)
  have e1N : s1.env rN = n := by simp [s1, Ex.eval, rv, hC, hSB, n, m]
  have r2 := Good.set (x := encodeSystem I) (w := w) (st := s1) (r := rsA)
    (e := .add (rv rL) (.const 6)) (by
      have : s1.env rL = ℓ := by simp [s1, Function.update_of_ne (show rL ≠ rN by decide), hL]
      simp only [Ex.Fits, Ex.eval, rv, this]; omega)
  set s2 := s1.set rsA ((Ex.add (rv rL) (.const 6)).eval s1.env)
  have e2A : s2.env rsA = ℓ + 6 := by
    simp [s2, s1, Ex.eval, rv, Function.update_of_ne (show rL ≠ rN by decide), hL]
  have e2N : s2.env rN = n := by
    simp only [s2, NSt.set_env, Function.update_of_ne (show rN ≠ rsA by decide)]; exact e1N
  -- the union sort
  obtain ⟨s3, r3, h3S, f3⟩ := sortS_good (x := encodeSystem I) (X := qX) (T1 := qT1) (T2 := qT2)
    (Y := qY) (tmp := qTmp) (C1 := qC1) (C2 := qC2) (A := rsA) (dir := rsDir) (c := rsC)
    (f1 := rsF1) (f2 := rsF2) (kc := rsKc) (t1 := rsT1) (t2 := rsT2) (i := rsI) (t := rsT)
    (r := rsR) (N := rN) (done := rsDone) (k := rsK) (lim2 := rsLim) (a := ℓ + 6) (n := n) hw (by decide) (by decide)
    s2 (union I) hX hT1 hT2 hY e2A (by omega) e2N (by simp [n, union]) hrw (by omega)
    (by omega)
  have r4 := Good.set (x := encodeSystem I) (w := w) (st := s3) (r := rCo) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  set s4 := s3.set rCo ((Ex.const 0 : Ex CR).eval s3.env)
  have r5 := Good.set (x := encodeSystem I) (w := w) (st := s4) (r := rCl) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  set s5 := s4.set rCl ((Ex.const 0 : Ex CR).eval s4.env)
  have r6 := Good.set (x := encodeSystem I) (w := w) (st := s5) (r := rCs) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  set s6 := s5.set rCs ((Ex.const 0 : Ex CR).eval s5.env)
  have h6S : s6.stk = s3.stk := rfl
  have f36 : ∀ r, r ≠ rCo → r ≠ rCl → r ≠ rCs → s6.env r = s3.env r := fun r h1 h2 h3 => by
    simp [s6, s5, s4, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3]
  have e6N : s6.env rN = n := by
    rw [f36 _ (by decide) (by decide) (by decide), f3.2.2 rN (by decide), e2N]
  have e6L : s6.env rL = ℓ := by
    rw [f36 _ (by decide) (by decide) (by decide), f3.2.2 rL (by decide)]
    simp [s2, s1, Function.update_of_ne (show rL ≠ rN by decide),
      Function.update_of_ne (show rL ≠ rsA by decide), hL]
  have e6SB : s6.env rSB = m := by
    rw [f36 _ (by decide) (by decide) (by decide), f3.2.2 rSB (by decide)]
    simp [s2, s1, Function.update_of_ne (show rSB ≠ rN by decide),
      Function.update_of_ne (show rSB ≠ rsA by decide), hSB, m]
  have e6a : s6.env rCo = 0 := by
    simp [s6, s5, s4, Ex.eval, Function.update_of_ne (show rCo ≠ rCs by decide),
      Function.update_of_ne (show rCo ≠ rCl by decide)]
  have e6b : s6.env rCl = 0 := by
    simp [s6, s5, Ex.eval, Function.update_of_ne (show rCl ≠ rCs by decide)]
  have e6d : s6.env rCs = 0 := by simp [s6, Ex.eval]
  -- the scan
  have hU3 : ∀ y ∈ p3Union I, y.length = ℓ + 6 ∧ ∀ z ∈ y, z < 2 ^ w :=
    fun y hy => hrw y ((mem_p3Union I).mp hy)
  obtain ⟨s7, r7, h7X, h7A, h7S, h7p, h7o, h7e⟩ := pJScan_good (x := encodeSystem I) hw s6
    (p3Union I) (by rw [h6S, h3S, Function.update_self]; rfl) e6L
    (by rw [e6N, length_p3Union]) (fun r hr => (hU3 r hr).1) (fun r hr => (hU3 r hr).2)
    (by omega) (by rw [length_p3Union]; omega) (by rw [e6a, e6b, e6d]; simp [hw0])
  have h6A : s6.stk qAns = [] := by
    rw [h6S, h3S, Function.update_of_ne (by decide)]; exact hAns
  -- `rN := rSB`, `rsA := 4`
  have e7SB : s7.env rSB = m := by rw [h7e _ (by decide), e6SB]
  have r8 := Good.set (x := encodeSystem I) (w := w) (st := s7) (r := rN) (e := rv rSB)
    (by simp only [Ex.Fits, rv, e7SB]; omega)
  set s8 := s7.set rN ((rv rSB : Ex CR).eval s7.env)
  have r9 := Good.set (x := encodeSystem I) (w := w) (st := s8) (r := rsA) (e := .const 4)
    (by simp only [Ex.Fits]; omega)
  set s9 := s8.set rsA ((Ex.const 4 : Ex CR).eval s8.env)
  have h9S : s9.stk = s7.stk := rfl
  have hscan : (p3Scan I).length = m := length_p3Scan I
  have hwB := p3Scan_words I hE (w := w) (by omega)
  -- the sort of the answers
  obtain ⟨s10, r10, h10S, f10⟩ := sortS_good (x := encodeSystem I) (X := qAns) (T1 := qT1)
    (T2 := qT2) (Y := qY) (tmp := qTmp) (C1 := qC1) (C2 := qC2) (A := rsA) (dir := rsDir)
    (c := rsC) (f1 := rsF1) (f2 := rsF2) (kc := rsKc) (t1 := rsT1) (t2 := rsT2) (i := rsI)
    (t := rsT) (r := rsR) (N := rN) (done := rsDone) (k := rsK) (lim2 := rsLim) (a := 4) (n := m) hw (by decide)
    (by decide) s9 (p3Scan I).reverse
    (by rw [h9S, h7A, h6A, List.append_nil, e6a, e6b, e6d]; rfl)
    (by rw [h9S, h7S _ (by decide) (by decide) (by decide), h6S, h3S,
      Function.update_of_ne (by decide)]; exact hT1)
    (by rw [h9S, h7S _ (by decide) (by decide) (by decide), h6S, h3S,
      Function.update_of_ne (by decide)]; exact hT2)
    (by rw [h9S, h7S _ (by decide) (by decide) (by decide), h6S, h3S,
      Function.update_of_ne (by decide)]; exact hY)
    (by simp [s9, Ex.eval]) (by omega)
    (by simp [s9, s8, Ex.eval, rv, Function.update_of_ne (show rN ≠ rsA by decide), e7SB])
    (by rw [List.length_reverse, hscan])
    (fun y hy => by
      have := hwB y (List.mem_reverse.mp hy)
      exact this)
    (by omega) (by omega)
  have hall := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq r10))))))))
  refine ⟨s10, hall.mono ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => hall.env_of hr⟩
  · rw [length_p3Union]
    simp only [condCost, Ex.size, rv]
    have hlg1 : Nat.log 2 n ≤ Nat.log 2 (H I + 1) + 2 := log_le_of_le_four (by omega)
    have hlg2 : Nat.log 2 m ≤ Nat.log 2 (H I + 1) + 2 := log_le_of_le_four (by omega)
    exact p3Join_arith _ _ n m ℓ (H I) _ _ _ hU0 hcnt hℓ (by omega) hlg1 hlg2 h3H
  · rw [h10S, Function.update_self, p3Ans_eq]
  · rw [h10S, Function.update_of_ne (by decide), h9S, h7X]
  · intro q h1 h2 h3
    rw [h10S, Function.update_of_ne h2, h9S, h7S q h1 h2 h3, h6S, h3S, Function.update_of_ne h1]
    rfl
  · rw [f10.1, show s9.pos = s7.pos from rfl, h7p, show s6.pos = s3.pos from rfl, f3.1]; rfl
  · rw [f10.2.1, show s9.out = s7.out from rfl, h7o, show s6.out = s3.out from rfl, f3.2.1]; rfl

end Lax119563Proofs.Compiler
