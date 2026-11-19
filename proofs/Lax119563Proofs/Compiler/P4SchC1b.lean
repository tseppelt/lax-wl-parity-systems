import Lax119563Proofs.Compiler.P4SchC1
import Lax119563Proofs.Compiler.P4SchRk

/-!
# Pass `P4`, schema part: section 1 of a column, last track and hub edges

* `p4LT_good`: the last track position;
* `c1Jun_good`: the junction hub (ternary schemas: answers `U`, `V`);
* `c1Lnk_good`: the link hub (answer of the end location);
* `p4Adv1_good`: advance the column pointers.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-! ## The last track -/

def p4LT : CStm CR CQ :=
  .seq (mulS rc3 rKk rc2 rc4) (.seq (.set rc3 (.add (rv rc3) (rv rc2))) (.seq (predS rc5 rc3)
    (.seq (.set rc1 (.add (rv r4TP) (.add (rv rc5) (rv rc5))))
      (.set r4TP (.add (rv rc1) (.const 2))))))

set_option maxHeartbeats 4000000 in
lemma p4LT_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s : NSt CR CQ) {k n TP : ℕ}
    (e2 : s.env rc2 = n) (ek : s.env rKk = k) (eTP : s.env r4TP = TP) (hn : 1 ≤ n)
    (hb : TP + 2 * ((k + 1) * n) + 2 < 2 ^ w) :
    ∃ s', Good x w p4LT s s' ((k + 2) * (n + 1) * (40 * Ex.nodeCost w)) ∧
      s'.env rc1 = TP + 2 * ((k + 1) * n - 1) ∧ s'.env r4TP = TP + 2 * ((k + 1) * n) ∧
      s'.stk = s.stk ∧ s'.pos = s.pos ∧ s'.out = s.out ∧
      ∀ r, r ∉ [rc1, rc3, rc4, rc5, r4TP] → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have hkn : k * n ≤ (k + 1) * n := Nat.mul_le_mul_right _ (by omega)
  have hkn' : (k + 1) * n = k * n + n := by ring
  have g1 := mulS_good (x := x) (Q := CQ) hw (dst := rc3) (a := rKk) (b := rc2) (j := rc4)
    (by decide) (by decide) (by decide) (by decide) (by decide) s ek e2 (by omega) (by omega)
  set s1 := (s.set rc3 (k * n)).set rc4 n
  have g2 := CStm.Good.set (x := x) (w := w) (st := s1) (r := rc3) (e := .add (rv rc3) (rv rc2))
    (by simp +decide [s1, Ex.Fits, rv, Ex.eval, e2]; omega)
  have ev2 : (Ex.add (rv rc3) (rv rc2) : Ex CR).eval s1.env = (k + 1) * n := by
    simp +decide [s1, Ex.eval, rv, e2]; ring
  rw [ev2] at g2
  set s2 := s1.set rc3 ((k + 1) * n)
  have g3 := predS_good (x := x) (Q := CQ) hw (dst := rc5) (n := rc3) (by decide) s2
    (N := (k + 1) * n) (by simp [s2]) (by omega)
  set s3 := s2.set rc5 ((k + 1) * n - 1)
  have e3TP : s3.env r4TP = TP := by simp +decide [s3, s2, s1, eTP]
  have e35 : s3.env rc5 = (k + 1) * n - 1 := by simp [s3]
  have g4 := CStm.Good.set (x := x) (w := w) (st := s3) (r := rc1)
    (e := .add (rv r4TP) (.add (rv rc5) (rv rc5)))
    (by simp only [Ex.Fits, rv, Ex.eval, e3TP, e35]; omega)
  have ev4 : (Ex.add (rv r4TP) (.add (rv rc5) (rv rc5)) : Ex CR).eval s3.env =
      TP + 2 * ((k + 1) * n - 1) := by simp only [Ex.eval, rv, e3TP, e35]; ring
  rw [ev4] at g4
  set s4 := s3.set rc1 (TP + 2 * ((k + 1) * n - 1))
  have g5 := CStm.Good.set (x := x) (w := w) (st := s4) (r := r4TP) (e := .add (rv rc1) (.const 2))
    (by simp +decide [s4, Ex.Fits, rv, Ex.eval]; omega)
  have ev5 : (Ex.add (rv rc1) (.const 2) : Ex CR).eval s4.env = TP + 2 * ((k + 1) * n) := by
    simp +decide [s4, Ex.eval, rv]
    have : 1 ≤ (k + 1) * n := by nlinarith
    omega
  rw [ev5] at g5
  refine ⟨_, (g1.seq (g2.seq (g3.seq (g4.seq g5)))).mono ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · simp only [Ex.size, rv]
    nlinarith
  · simp +decide [s4]
  · simp
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [s4, s3, s2, s1, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1,
      Function.update_of_ne hr.2.2.1, Function.update_of_ne hr.2.2.2.1,
      Function.update_of_ne hr.2.2.2.2]

/-! ## Junction and link hubs -/

/-- The junction hub of a column (ternary schemas only). -/
def c1Jun : CStm CR CQ := .ite (rv r4Tn) (.seq (pAns rc2 rc3) (.seq (pAns rc4 rc5) jLabs)) .skip

/-- The link hub of a column. -/
def c1Lnk : CStm CR CQ := .seq (pAns rc2 rc3) lLabs

/-- An answer `[s, off, labs, seed]` as consumed by `P4`. -/
def AnsOK (w : ℕ) (A : List ℕ) : Prop :=
  ∃ sq off labs sd, A = [sq, off, labs, sd] ∧ (labs = 1 ∨ labs = 2) ∧ sd ≤ 1 ∧
    ∀ v ∈ A, v < 2 ^ w

/-- The offset of an answer. -/
def aOff (A : List ℕ) : ℕ := A.getD 1 0

lemma ansMode_le {eps : ℕ} (he : eps ≤ 1) {A : List ℕ} {w : ℕ} (h : AnsOK w A) :
    ansMode eps A ≤ 2 := by
  obtain ⟨sq, off, labs, sd, rfl, -, hsd, -⟩ := h
  unfold ansMode; simp only [List.getD_cons_succ, List.getD_cons_zero]
  split_ifs
  · have : eps * sd ≤ 1 * 1 := Nat.mul_le_mul he hsd
    omega
  · omega

set_option maxHeartbeats 4000000 in
lemma c1Jun_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s : NSt CR CQ) {T H SP LB : ℕ}
    (AU AV rest : List ℕ) (eT : s.env r4Tn = T) (hT : T ≤ 1) (eH : s.env r4H = H)
    (eSP : s.env r4SP = SP) (eLB : s.env rLB = LB) (hE : s.env r4Eps ≤ 1)
    (hA : s.stk qAns = (if T = 1 then AU ++ AV else []) ++ rest)
    (hU : T = 1 → AnsOK w AU) (hV : T = 1 → AnsOK w AV)
    (hH : H + 4 < 2 ^ w) (hSP : SP + 2 < 2 ^ w)
    (hbU : T = 1 → LB + aOff AU + 2 < 2 ^ w) (hbV : T = 1 → LB + aOff AV + 2 < 2 ^ w)
    (hV4 : s.env r4V < 2 ^ w) (hm : s.env r4M + 12 < 2 ^ w) :
    ∃ s', Good x w c1Jun s s' (600 * Ex.nodeCost w) ∧
      EE s s' (if T = 1 then junL H SP LB (aOff AU) (ansMode (s.env r4Eps) AU) (aOff AV)
        (ansMode (s.env r4Eps) AV) else []) ∧
      s'.stk qAns = rest ∧
      s'.stk qA2 = (if T = 1 then AV.reverse ++ AU.reverse else []) ++ s.stk qA2 ∧
      (∀ q, q ≠ q4E → q ≠ qAns → q ≠ qA2 → s'.stk q = s.stk q) ∧ s'.env r4V < 2 ^ w ∧
      ∀ r, r ∉ [rc2, rc3, rc4, rc5, rc6, rc7, rc8, r4F, r4V, r4M] → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have hF : (rv r4Tn : Ex CR).Fits w s.env := by
    have : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
    simp only [rv, Ex.Fits, eT]; omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hT with rfl | rfl
  · refine ⟨s, (CStm.Good.iteF hF (by simp [rv, Ex.eval, eT]) CStm.Good.skip).mono ?_,
      by simpa using EE.refl s, by simpa using hA, by simp, fun _ _ _ _ => rfl, hV4,
      fun _ _ => rfl⟩
    simp only [condCost, rv, Ex.size]; nlinarith
  · obtain ⟨sq, oU, lU, dU, rfl, hlU, hdU, hbU'⟩ := hU rfl
    obtain ⟨sv, oV, lV, dV, rfl, hlV, hdV, hbV'⟩ := hV rfl
    simp only [if_true] at hA
    obtain ⟨s1, g1, k1, v1, m1, mm1, p1, o1, f1⟩ := pAns_good (x := x) hw (o := rc2) (m := rc3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) s (rest := [sv, oV, lV, dV] ++ rest) (by rw [hA]; simp) hbU' hlU
      hdU hE
    have e1E : s1.env r4Eps = s.env r4Eps := f1 _ (by decide) (by decide) (by decide)
      (by decide) (by decide)
    obtain ⟨s2, g2, k2, v2, m2, mm2, p2, o2, f2⟩ := pAns_good (x := x) hw (o := rc4) (m := rc5)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) s1 (rest := rest) (by rw [k1]; simp +decide) hbV' hlV hdV
      (by rw [e1E]; exact hE)
    have q2 : ∀ r, r ∉ [rc2, rc3, rc4, rc5, rc6, rc7, rc8] → s2.env r = s.env r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [f2 r hr.2.2.2.2.1 hr.2.2.2.2.2.1 hr.2.2.2.2.2.2 hr.2.2.1 hr.2.2.2.1,
        f1 r hr.2.2.2.2.1 hr.2.2.2.2.2.1 hr.2.2.2.2.2.2 hr.1 hr.2.1]
    have e2U : s2.env rc2 = oU := by
      rw [f2 _ (by decide) (by decide) (by decide) (by decide) (by decide), v1]
    have e2m : s2.env rc3 = ansMode (s.env r4Eps) [sq, oU, lU, dU] := by
      rw [f2 _ (by decide) (by decide) (by decide) (by decide) (by decide), m1]
    have hmU := ansMode_le (w := w) hE ⟨sq, oU, lU, dU, rfl, hlU, hdU, hbU'⟩
    have hmV := ansMode_le (w := w) hE ⟨sv, oV, lV, dV, rfl, hlV, hdV, hbV'⟩
    obtain ⟨s3, g3, eff3, v3, f3⟩ := jLabs_good (x := x) hw s2 (H := H) (SP := SP) (LB := LB)
      (by rw [q2 _ (by decide), eH]) (by rw [q2 _ (by decide), eSP])
      (by rw [q2 _ (by decide), eLB]) e2U e2m v2 (by rw [m2, e1E]) hmU hmV hH hSP
      (by have := hbU rfl; simpa [aOff] using this) (by have := hbV rfl; simpa [aOff] using this)
      (by rw [q2 _ (by decide)]; exact hV4) (by rw [q2 _ (by decide)]; exact hm)
    have ee : EE s s2 [] := EE.of_frame (by rw [k2, k1]; simp +decide)
      (by rw [q2 _ (by decide)]) (by rw [p2, p1]) (by rw [o2, o1])
    refine ⟨s3, (CStm.Good.iteT hF (by simp [rv, Ex.eval, eT]) (g1.seq (g2.seq g3))).mono ?_,
      ?_, ?_, ?_, ?_, v3, ?_⟩
    · simp only [condCost, rv, Ex.size]; nlinarith
    · have := ee.trans eff3.ee
      simpa [aOff] using this
    · rw [eff3.stk_ne (by decide), k2]; simp +decide
    · rw [eff3.stk_ne (by decide), k2, k1]; simp +decide
    · intro q h1 h2 h3
      rw [eff3.stk_ne h1, k2, k1]
      simp [Function.update_of_ne h2, Function.update_of_ne h3]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [f3 r (by simp [labW]; tauto)]
      exact q2 r (by simp; tauto)

set_option maxHeartbeats 4000000 in
lemma c1Lnk_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s : NSt CR CQ) {T H LT LB : ℕ}
    (AW rest : List ℕ) (eT : s.env r4Tn = T) (eH : s.env r4H = H) (e1 : s.env rc1 = LT)
    (eLB : s.env rLB = LB) (hE : s.env r4Eps ≤ 1)
    (hA : s.stk qAns = AW ++ rest) (hW : AnsOK w AW)
    (hH : H + 4 * T + 2 < 2 ^ w) (hLT : LT + 2 < 2 ^ w) (hbW : LB + aOff AW + 2 < 2 ^ w)
    (hV4 : s.env r4V < 2 ^ w) (hm : s.env r4M + 4 < 2 ^ w) :
    ∃ s', Good x w c1Lnk s s' (200 * Ex.nodeCost w) ∧
      EE s s' (lnkL (H + 4 * T) LT LB (aOff AW) (ansMode (s.env r4Eps) AW)) ∧
      s'.stk qAns = rest ∧ s'.stk qA2 = AW.reverse ++ s.stk qA2 ∧
      (∀ q, q ≠ q4E → q ≠ qAns → q ≠ qA2 → s'.stk q = s.stk q) ∧ s'.env r4V < 2 ^ w ∧
      ∀ r, r ∉ [rc2, rc3, rc6, rc7, rc8, r4F, r4V, r4M] → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  obtain ⟨sq, o, l, d, rfl, hl, hd, hb⟩ := hW
  obtain ⟨s1, g1, k1, v1, m1, mm1, p1, o1, f1⟩ := pAns_good (x := x) hw (o := rc2) (m := rc3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) s (rest := rest) hA hb hl hd hE
  have q1 : ∀ r, r ∉ [rc2, rc3, rc6, rc7, rc8] → s1.env r = s.env r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact f1 r hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2 hr.1 hr.2.1
  obtain ⟨s2, g2, eff2, v2, f2⟩ := lLabs_good (x := x) hw s1 (H := H) (T := T) (LT := LT)
    (LB := LB) (by rw [q1 _ (by decide), eH]) (by rw [q1 _ (by decide), eT])
    (by rw [q1 _ (by decide), e1]) (by rw [q1 _ (by decide), eLB]) v1 m1 (by rw [← m1]; exact mm1) hH hLT
    (by simpa [aOff] using hbW) (by rw [q1 _ (by decide)]; exact hV4)
    (by rw [q1 _ (by decide)]; exact hm)
  have ee : EE s s1 [] := EE.of_frame (by rw [k1]; simp +decide) (by rw [q1 _ (by decide)])
    p1 o1
  refine ⟨s2, (g1.seq g2).mono (by nlinarith), ?_, ?_, ?_, ?_, v2, ?_⟩
  · have := ee.trans eff2.ee
    simpa [aOff] using this
  · rw [eff2.stk_ne (by decide), k1]; simp +decide
  · rw [eff2.stk_ne (by decide), k1]; simp +decide
  · intro q h1 h2 h3
    rw [eff2.stk_ne h1, k1]
    simp [Function.update_of_ne h2, Function.update_of_ne h3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [f2 r (by simp [labW]; tauto)]
    exact q1 r (by simp; tauto)

/-! ## Advancing -/

def p4Adv1 : CStm CR CQ :=
  .seq (.set r4H (.add (rv r4H) (.add (.const 2) (.add (rv r4Tn) (.add (rv r4Tn)
      (.add (rv r4Tn) (rv r4Tn)))))))
    (.seq (.set r4SP (.add (rv r4SP) (.const 2))) (.set r4K (.add (rv r4K) (.const 1))))

lemma p4Adv1_good {w : ℕ} {x : List Bool} (s : NSt CR CQ) {H T SP K : ℕ}
    (eH : s.env r4H = H) (eT : s.env r4Tn = T) (eSP : s.env r4SP = SP) (eK : s.env r4K = K)
    (hH : H + 2 + 4 * T < 2 ^ w) (hSP : SP + 2 < 2 ^ w) (hK : K + 1 < 2 ^ w) :
    Good x w p4Adv1 s (((s.set r4H (H + 2 + 4 * T)).set r4SP (SP + 2)).set r4K (K + 1))
      (30 * Ex.nodeCost w) := by
  have hN := CStm.nodeCost_ge w
  have g1 := CStm.Good.set (x := x) (w := w) (st := s) (r := r4H)
    (e := .add (rv r4H) (.add (.const 2) (.add (rv r4Tn) (.add (rv r4Tn)
      (.add (rv r4Tn) (rv r4Tn)))))) (by simp only [Ex.Fits, rv, Ex.eval, eH, eT]; omega)
  have ev1 : (Ex.add (rv r4H) (.add (.const 2) (.add (rv r4Tn) (.add (rv r4Tn)
      (.add (rv r4Tn) (rv r4Tn))))) : Ex CR).eval s.env = H + 2 + 4 * T := by
    simp only [Ex.eval, rv, eH, eT]; ring
  rw [ev1] at g1
  have g2 := CStm.Good.set (x := x) (w := w) (st := s.set r4H (H + 2 + 4 * T)) (r := r4SP)
    (e := .add (rv r4SP) (.const 2)) (by simp +decide [Ex.Fits, rv, Ex.eval, eSP]; omega)
  have ev2 : (Ex.add (rv r4SP) (.const 2) : Ex CR).eval (s.set r4H (H + 2 + 4 * T)).env =
      SP + 2 := by simp +decide [Ex.eval, rv, eSP]
  rw [ev2] at g2
  have g3 := CStm.Good.set (x := x) (w := w)
    (st := (s.set r4H (H + 2 + 4 * T)).set r4SP (SP + 2)) (r := r4K)
    (e := .add (rv r4K) (.const 1)) (by
      have : ((s.set r4H (H + 2 + 4 * T)).set r4SP (SP + 2)).env r4K = K := by
        simp only [NSt.set_env]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), eK]
      simp only [Ex.Fits, rv, Ex.eval, this]; omega)
  have ev3 : (Ex.add (rv r4K) (.const 1) : Ex CR).eval
      ((s.set r4H (H + 2 + 4 * T)).set r4SP (SP + 2)).env = K + 1 := by
    simp +decide [Ex.eval, rv, eK]
  rw [ev3] at g3
  exact (g1.seq (g2.seq g3)).mono (by simp only [Ex.size, rv]; omega)

end Lax119563Proofs.Compiler
