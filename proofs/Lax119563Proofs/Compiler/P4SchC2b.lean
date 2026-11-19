import Lax119563Proofs.Compiler.P4SchC2

/-!
# Pass `P4`, schema part: one column of section 2 (`p4C2_good`)
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-- The start answer of a column (binary schemas), else zeros. -/
def c2Ans : CStm CR CQ :=
  .ite (rv r4Tn) (.seq (.set rc3 (.const 0)) (.set rc4 (.const 0))) (pAns rc3 rc4)

/-- The answer hypotheses of a column of section 2: `A` the consumed answer words. -/
def AnsHyp (w : ℕ) (T eps : ℕ) (A : List ℕ) (oU mU : ℕ) : Prop :=
  (T = 1 → A = [] ∧ oU = 0 ∧ mU = 0) ∧
  (T = 0 → (∃ sq labs sd, A = [sq, oU, labs, sd] ∧ (labs = 1 ∨ labs = 2) ∧ sd ≤ 1) ∧
    (∀ v ∈ A, v < 2 ^ w) ∧ mU = ansMode eps A)

lemma AnsHyp.mU_le {w T eps : ℕ} {A : List ℕ} {oU mU : ℕ} (h : AnsHyp w T eps A oU mU)
    (hT : T ≤ 1) (he : eps ≤ 1) : mU ≤ 2 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hT with rfl | rfl
  · obtain ⟨⟨sq, labs, sd, rfl, -, hsd⟩, -, rfl⟩ := h.2 rfl
    unfold ansMode; simp only [List.getD_cons_succ, List.getD_cons_zero]
    split_ifs
    · have : eps * sd ≤ 1 * 1 := Nat.mul_le_mul he hsd
      omega
    · omega
  · obtain ⟨-, -, rfl⟩ := h.1 rfl; omega

set_option maxHeartbeats 2000000 in
lemma c2Ans_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s : NSt CR CQ) {T oU mU : ℕ}
    (A ansRest : List ℕ) (eT : s.env r4Tn = T) (hT : T ≤ 1) (hE : s.env r4Eps ≤ 1)
    (hA : s.stk qAns = A ++ ansRest) (hH : AnsHyp w T (s.env r4Eps) A oU mU) :
    ∃ s', Good x w c2Ans s s' (50 * Ex.nodeCost w) ∧ s'.env rc3 = oU ∧ s'.env rc4 = mU ∧
      s'.stk = Function.update (Function.update s.stk qAns ansRest) qA2
        (A.reverse ++ s.stk qA2) ∧ s'.pos = s.pos ∧ s'.out = s.out ∧
      ∀ r, r ∉ [rc3, rc4, rc6, rc7, rc8] → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
  have hF : (rv r4Tn : Ex CR).Fits w s.env := by simp only [rv, Ex.Fits, eT]; omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hT with rfl | rfl
  · obtain ⟨⟨sq, labs, sd, rfl, hl, hsd⟩, hb, hm⟩ := hH.2 rfl
    obtain ⟨s1, g, k1, v1, m1, -, p1, o1, f1⟩ := pAns_good (x := x) hw (o := rc3) (m := rc4)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) s hA hb hl hsd hE
    refine ⟨s1, (CStm.Good.iteF hF (by simp [rv, Ex.eval, eT]) g).mono ?_, v1, by rw [m1, hm],
      by rw [k1]; simp, p1, o1, ?_⟩
    · simp only [condCost, rv, Ex.size]; nlinarith
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      exact f1 r hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2 hr.1 hr.2.1
  · obtain ⟨rfl, rfl, rfl⟩ := hH.1 rfl
    have g1 := CStm.Good.set (x := x) (w := w) (st := s) (r := rc3) (e := .const 0)
      (by simp only [Ex.Fits]; omega)
    have g2 := CStm.Good.set (x := x) (w := w) (st := s.set rc3 ((Ex.const 0 : Ex CR).eval s.env))
      (r := rc4) (e := .const 0) (by simp only [Ex.Fits]; omega)
    refine ⟨_, (CStm.Good.iteT hF (by simp [rv, Ex.eval, eT]) (g1.seq g2)).mono ?_, ?_, ?_, ?_,
      rfl, rfl, ?_⟩
    · simp only [condCost, rv, Ex.size]; nlinarith
    · simp +decide [Ex.eval]
    · simp +decide [Ex.eval]
    · funext q
      by_cases h1 : q = qA2
      · subst h1; simp +decide
      · by_cases h2 : q = qAns
        · subst h2; simp +decide [hA]
        · simp [Function.update_of_ne h1, Function.update_of_ne h2]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [Function.update_of_ne hr.1, Function.update_of_ne hr.2.1]


/-- One column of section 2. -/
def p4C2 : CStm CR CQ :=
  .seq c2Ans (.seq (.set rc6 (.const 1)) (.seq (.set rc1 (.const 0))
    (.seq (.set rc2 (rv r4Prev)) (.seq p4Qs (.seq p4Drop
      (.seq (.set r4SP (.add (rv r4SP) (.const 2))) (.set r4K (.add (rv r4K) (.const 1)))))))))

/-- Registers written by a column of section 2. -/
def c2W : List (Fin CR) :=
  [rc1, rc2, rc3, rc4, rc5, rc6, rc7, rc8, r4TP, r4H, r4F, r4V, r4M, r4Dist, r4SP, r4K]

set_option maxHeartbeats 8000000 in
/-- **One column of section 2.** -/
lemma p4C2_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s : NSt CR CQ) (k : ℕ)
    {T Hc TPc SP QB R2 LB K oU mU : ℕ} (cs rest A ansRest : List ℕ) (hn : 1 ≤ cs.length)
    (hcs : ∀ X ∈ cs, 1 ≤ X)
    (hR : s.stk qRkF = cs ++ 0 :: rest) (hB : s.stk qOrsB = [])
    (hA : s.stk qAns = A ++ ansRest) (hAH : AnsHyp w T (s.env r4Eps) A oU mU)
    (ek : s.env rKk = k) (eH : s.env r4H = Hc) (eTP : s.env r4TP = TPc)
    (eT : s.env r4Tn = T) (hT : T ≤ 1) (eSP : s.env r4SP = SP) (eR2 : s.env r4R2 = R2)
    (eLB : s.env rLB = LB) (eQB : s.env r4Prev = QB) (eK : s.env r4K = K)
    (hE : s.env r4Eps ≤ 1)
    (hV : s.env r4V < 2 ^ w) (hbd : s.Bdd w) (hpos : s.pos ≤ x.length)
    (hk : k + 2 < 2 ^ w) (hK : K + 2 < 2 ^ w)
    (hH : Hc + 4 * ((k + 1) * cs.length) + 4 < 2 ^ w)
    (hTP : TPc + 2 * ((k + 1) * cs.length) + 2 < 2 ^ w)
    (hSP : SP + 4 < 2 ^ w) (hQR : ∀ X ∈ cs, QB + (k + 1) * R2 + X + 2 < 2 ^ w)
    (hU : LB + oU + 2 < 2 ^ w)
    (hm : s.env r4M + 12 * cs.length * (k + 1) + 12 < 2 ^ w) :
    ∃ s', Good x w p4C2 s s' ((k + 3) * ((cs.length + 1) * (800 * Ex.nodeCost w))) ∧
      EE s s' (col2E T Hc TPc SP QB R2 LB oU mU k cs) ∧
      s'.stk qRkF = rest ∧ s'.stk qOrsB = [] ∧ s'.stk qAns = ansRest ∧
      s'.stk qA2 = A.reverse ++ s.stk qA2 ∧
      (∀ q, q ≠ q4E → q ≠ qRkF → q ≠ qOrsB → q ≠ qAns → q ≠ qA2 → s'.stk q = s.stk q) ∧
      s'.env r4H = Hc + 4 * ((k + 1) * cs.length) ∧
      s'.env r4TP = TPc + 2 * ((k + 1) * cs.length) ∧ s'.env r4SP = SP + 2 ∧
      s'.env r4K = K + 1 ∧ s'.env r4V < 2 ^ w ∧ s'.Bdd w ∧
      ∀ r, r ∉ c2W → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
  have hm2 := hAH.mU_le hT hE
  obtain ⟨s1, g1, e13, e14, k1, p1, o1, f1⟩ := c2Ans_good (x := x) hw s A ansRest eT hT hE hA hAH
  have q1 : ∀ r, r ∉ [rc3, rc4, rc6, rc7, rc8] → s1.env r = s.env r := f1
  have b1 := g1.bdd hw hbd hpos
  have ga := CStm.Good.set (x := x) (w := w) (st := s1) (r := rc6) (e := .const 1)
    (by simp only [Ex.Fits]; omega)
  have gb := CStm.Good.set (x := x) (w := w) (st := s1.set rc6 1) (r := rc1) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  have gc := CStm.Good.set (x := x) (w := w) (st := (s1.set rc6 1).set rc1 0) (r := rc2)
    (e := rv r4Prev) (by
      have := hQR _ (List.getElem_mem (show 0 < cs.length by omega))
      simp +decide [Ex.Fits, rv, q1 r4Prev (by decide), eQB]; omega)
  simp only [Ex.eval] at ga gb
  have ev : (rv r4Prev : Ex CR).eval ((s1.set rc6 1).set rc1 0).env = QB := by
    simp +decide [rv, Ex.eval, q1 r4Prev (by decide), eQB]
  rw [ev] at gc
  set s2 := ((s1.set rc6 1).set rc1 0).set rc2 QB
  have b2 := (ga.seq (gb.seq gc)).bdd hw b1.1 b1.2
  have q2 : ∀ r, r ∉ [rc1, rc2, rc3, rc4, rc6, rc7, rc8] → s2.env r = s.env r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [s2, NSt.set_env, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1,
      Function.update_of_ne hr.2.2.2.2.1]
    exact q1 r (by simp; tauto)
  have k2 : s2.stk = s1.stk := rfl
  obtain ⟨s3, g3, hI⟩ := p4Qs_good (x := x) hw s2 k (T := T) (Hc := Hc) (TPc := TPc) (SP := SP)
    (QB := QB) (R2 := R2) (LB := LB) (oU := oU) (mU := mU) cs rest hn hcs
    (by rw [k2, k1]; simp +decide [hR]) (by rw [k2, k1]; simp +decide [hB])
    (by simp +decide [s2]) (by simp +decide [s2]) (by simp +decide [s2])
    (by rw [q2 _ (by decide), ek]) (by rw [q2 _ (by decide), eH]) (by rw [q2 _ (by decide), eTP])
    (by rw [q2 _ (by decide), eT]) hT (by rw [q2 _ (by decide), eSP]) (by rw [q2 _ (by decide), eR2])
    (by rw [q2 _ (by decide), eLB]) (by simp +decide [s2, e13]) (by simp +decide [s2, e14]) hm2
    (by rw [q2 _ (by decide)]; exact hV) b2.1 b2.2 hk hH hTP (by omega) hQR hU
    (by rw [q2 _ (by decide)]; exact hm)
  obtain ⟨hE3, h3R, h3B, h3o, -, -, -, -, h3H, h3TP, h3V, hb3, hp3, h3fr⟩ := hI
  have hcw : ∀ X ∈ cs, X < 2 ^ w := fun X hX => by have := hQR X hX; omega
  obtain ⟨s4, g4, k4, p4, o4, f4⟩ := p4Drop_good (x := x) hw s3 cs rest hcs hcw h3R
  have b4 := g4.bdd hw hb3 hp3
  have e4SP : s4.env r4SP = SP := by
    rw [f4 _ (by decide), h3fr _ (by decide), q2 _ (by decide), eSP]
  have g5 := CStm.Good.set (x := x) (w := w) (st := s4) (r := r4SP) (e := .add (rv r4SP) (.const 2))
    (by simp only [Ex.Fits, rv, Ex.eval, e4SP]; omega)
  have ev5 : (Ex.add (rv r4SP) (.const 2) : Ex CR).eval s4.env = SP + 2 := by
    simp [Ex.eval, rv, e4SP]
  rw [ev5] at g5
  have e5K : (s4.set r4SP (SP + 2)).env r4K = K := by
    simp +decide only [NSt.set_env]
    rw [Function.update_of_ne (by decide), f4 _ (by decide), h3fr _ (by decide), q2 _ (by decide), eK]
  have g6 := CStm.Good.set (x := x) (w := w) (st := s4.set r4SP (SP + 2)) (r := r4K)
    (e := .add (rv r4K) (.const 1)) (by simp only [Ex.Fits, rv, Ex.eval, e5K]; omega)
  have ev6 : (Ex.add (rv r4K) (.const 1) : Ex CR).eval (s4.set r4SP (SP + 2)).env = K + 1 := by
    simp only [Ex.eval, rv, e5K]
  rw [ev6] at g6
  set s6 := (s4.set r4SP (SP + 2)).set r4K (K + 1)
  have b6 := (g5.seq g6).bdd hw b4.1 b4.2
  have q63 : ∀ r, r ≠ r4K → r ≠ r4SP → r ≠ rc5 → s6.env r = s3.env r := by
    intro r h1 h2 h3
    simp only [s6, NSt.set_env, Function.update_of_ne h1, Function.update_of_ne h2]
    exact f4 r h3
  have k6 : s6.stk = Function.update s3.stk qRkF rest := k4
  refine ⟨s6, (g1.seq (ga.seq (gb.seq (gc.seq (g3.seq (g4.seq (g5.seq g6))))))).mono ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, b6.1, ?_⟩
  · have hc : (cs.length + 1) * (800 * Ex.nodeCost w) ≥ 800 * Ex.nodeCost w := by nlinarith
    simp only [Ex.size, rv]
    nlinarith
  · have e01 : EE s s2 [] := EE.of_frame (by rw [k2, k1]; simp +decide)
      (by rw [q2 _ (by decide)]) (by simp [s2, p1]) (by simp [s2, o1])
    have e36 : EE s3 s6 [] := EE.of_frame (by rw [k6]; simp +decide)
      (by rw [q63 _ (by decide) (by decide) (by decide)]) (by simp [s6, p4]) (by simp [s6, o4])
    have := (e01.trans hE3).trans e36
    simpa [col2E] using this
  · rw [k6]; simp
  · rw [k6]; simp +decide [h3B]
  · rw [k6, Function.update_of_ne (by decide), h3o _ (by decide) (by decide) (by decide), k2, k1]
    simp +decide
  · rw [k6, Function.update_of_ne (by decide), h3o _ (by decide) (by decide) (by decide), k2, k1]
    simp +decide
  · intro q h1 h2 h3 h4 h5
    rw [k6, Function.update_of_ne h2, h3o q h1 h2 h3, k2, k1, Function.update_of_ne h5,
      Function.update_of_ne h4]
  · rw [q63 _ (by decide) (by decide) (by decide), h3H]
  · rw [q63 _ (by decide) (by decide) (by decide), h3TP]
  · simp +decide [s6]
  · simp +decide [s6]
  · rw [q63 _ (by decide) (by decide) (by decide)]; exact h3V
  · intro r hr
    simp only [c2W, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [q63 r hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hr.2.2.2.2.1,
      h3fr r (by simp [qW, entW]; tauto)]
    exact q2 r (by simp; tauto)

end Lax119563Proofs.Compiler
