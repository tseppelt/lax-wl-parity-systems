import Lax119563Proofs.Compiler.P4SchRk

/-!
# Pass `P4`, schema part: the `q` loop of section 2 and dropping a column's codes

* `p4QB`: one `q`: the rank loop, then the codes are restored on `qRkF` (`p4QB_good`);
* `p4Qs`: the loop over `q ≤ k` (`p4Qs_good`, edges `col2E`);
* `p4Drop`: drop the codes of a column (`p4Drop_good`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-- One `q`. -/
def p4QB : CStm CR CQ :=
  .seq p4Rks (.seq (.push qRkF (.const 0)) (.seq (moveAllS qOrsB qRkF rc8 r4Dist)
    (.seq (.set rc2 (.add (rv rc2) (rv r4R2))) (.set rc1 (.add (rv rc1) (.const 1))))))

/-- The loop over `q ≤ k`. -/
def p4Qs : CStm CR CQ := .loop (.lt (rv rc1) (.add (rv rKk) (.const 1))) p4QB

/-- The update edges of a column (numbers): for `q ≤ k` the entries `q n + p`. -/
def col2E (T Hc TPc SP QB R2 LB oU mU k : ℕ) (cs : List ℕ) : List (ℕ × ℕ) :=
  (List.range (k + 1)).flatMap fun q =>
    rksE T (q * cs.length) Hc TPc SP (QB + q * R2) LB oU mU cs

/-- The registers written by the `q` loop. -/
def qW : List (Fin CR) := rc1 :: rc2 :: rc5 :: entW

/-- The state of the `q` loop after `q` rounds. -/
def qInv (w : ℕ) (x : List Bool) (T Hc TPc SP QB R2 LB oU mU : ℕ) (cs rest : List ℕ)
    (s0 : NSt CR CQ) (q : ℕ) (s : NSt CR CQ) : Prop :=
  EE s0 s ((List.range q).flatMap fun q' =>
      rksE T (q' * cs.length) Hc TPc SP (QB + q' * R2) LB oU mU cs) ∧
    s.stk qRkF = cs ++ 0 :: rest ∧ s.stk qOrsB = [] ∧
    (∀ q', q' ≠ q4E → q' ≠ qRkF → q' ≠ qOrsB → s.stk q' = s0.stk q') ∧
    s.env rc1 = q ∧ s.env rc2 = QB + q * R2 ∧
    s.env rc6 = (if q * cs.length = 0 then 1 else 0) ∧
    (0 < q * cs.length → s.env rc7 = TPc + 2 * (q * cs.length - 1)) ∧
    s.env r4H = Hc + 4 * (q * cs.length) ∧ s.env r4TP = TPc + 2 * (q * cs.length) ∧
    s.env r4V < 2 ^ w ∧ s.Bdd w ∧ s.pos ≤ x.length ∧
    ∀ r, r ∉ qW → s.env r = s0.env r

lemma length_rksE_le' (T t0 Hc TPc SP QR LB oU mU : ℕ) (cs : List ℕ) :
    (rksE T t0 Hc TPc SP QR LB oU mU cs).length ≤ 12 * cs.length :=
  length_rksE_le T t0 Hc TPc SP QR LB oU mU cs

lemma length_qE_le (T Hc TPc SP QB R2 LB oU mU : ℕ) (cs : List ℕ) (q : ℕ) :
    ((List.range q).flatMap fun q' =>
      rksE T (q' * cs.length) Hc TPc SP (QB + q' * R2) LB oU mU cs).length ≤
      12 * cs.length * q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, List.flatMap_singleton]
    have := length_rksE_le T (q * cs.length) Hc TPc SP (QB + q * R2) LB oU mU cs
    rw [Nat.mul_succ]; omega

set_option maxHeartbeats 4000000 in
lemma p4QB_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s0 : NSt CR CQ) (k : ℕ)
    {T Hc TPc SP QB R2 LB oU mU : ℕ} (cs rest : List ℕ) (hn : 1 ≤ cs.length)
    (hcs : ∀ X ∈ cs, 1 ≤ X)
    (eT : s0.env r4Tn = T) (hT : T ≤ 1) (eSP : s0.env r4SP = SP) (eR2 : s0.env r4R2 = R2)
    (eLB : s0.env rLB = LB) (eo : s0.env rc3 = oU) (em : s0.env rc4 = mU) (hm2 : mU ≤ 2)
    (hH : Hc + 4 * ((k + 1) * cs.length) + 4 < 2 ^ w)
    (hTP : TPc + 2 * ((k + 1) * cs.length) + 2 < 2 ^ w)
    (hSP : SP + 2 < 2 ^ w) (hQR : ∀ X ∈ cs, QB + (k + 1) * R2 + X + 2 < 2 ^ w)
    (hU : LB + oU + 2 < 2 ^ w)
    (hm : s0.env r4M + 12 * cs.length * (k + 1) + 12 < 2 ^ w)
    (q : ℕ) (hq : q < k + 1) (s : NSt CR CQ)
    (hI : qInv w x T Hc TPc SP QB R2 LB oU mU cs rest s0 q s) :
    ∃ s', Good x w p4QB s s' ((cs.length + 1) * (700 * Ex.nodeCost w)) ∧
      qInv w x T Hc TPc SP QB R2 LB oU mU cs rest s0 (q + 1) s' := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  obtain ⟨hE, hsR, hsB, hso, e1, e2, e6, e7, eH, eTP, hV, hbd, hpos, hfr⟩ := hI
  have hfr' : ∀ r, r ∉ qW → s.env r = s0.env r := hfr
  have hqn : q * cs.length + cs.length ≤ (k + 1) * cs.length := by nlinarith
  have hlq := length_qE_le T Hc TPc SP QB R2 LB oU mU cs q
  have hqk : 12 * cs.length * q + 12 * cs.length ≤ 12 * cs.length * (k + 1) := by nlinarith
  obtain ⟨s1, g1, hR⟩ := p4Rks_good (x := x) hw s (T := T) (t0 := q * cs.length) (Hc := Hc)
    (TPc := TPc) (SP := SP) (QR := QB + q * R2) (LB := LB) (oU := oU) (mU := mU) cs rest hcs
    hsR hsB (by rw [hfr' _ (by decide), eT]) hT e6 e7 (by rw [hfr' _ (by decide), eSP]) eH eTP e2
    (by rw [hfr' _ (by decide), eLB]) (by rw [hfr' _ (by decide), eo])
    (by rw [hfr' _ (by decide), em]) hm2 (by omega) (by omega) hSP
    (fun X hX => by have := hQR X hX; have : q * R2 ≤ (k + 1) * R2 := by nlinarith
                    omega) hU hV (by rw [hE.2.1]; omega)
  obtain ⟨hE1, h1R, h1B, h1o, h15, h16, h17, h1H, h1TP, h1V, h1fr⟩ := hR
  rw [List.take_length] at hE1 h1B
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
    show cs.length + 1 - cs.length = 1 by omega, List.drop_one, List.tail_cons] at h1R
  have hb1 := (g1.bdd hw hbd hpos)
  have gp := CStm.Good.push (x := x) (w := w) (st := s1) (q := qRkF) (e := .const 0)
    (by simp only [Ex.Fits]; positivity)
  set s2 := s1.setS qRkF ((Ex.const 0 : Ex CR).eval s1.env :: s1.stk qRkF)
  have hb2 := gp.bdd hw hb1.1 hb1.2
  obtain ⟨s3, g3, k3, p3, o3, f3⟩ := moveAllS_good (x := x) hw (q := qOrsB) (q' := qRkF)
    (t := rc8) (f := r4Dist) (by decide) (by decide) s2 hb2.1
  have hb3 := g3.bdd hw hb2.1 hb2.2
  have e32 : s3.env rc2 = QB + q * R2 := by
    rw [f3 _ (by decide) (by decide)]; simp only [s2, NSt.setS_env]
    rw [h1fr _ (by decide), e2]
  have e3R2 : s3.env r4R2 = R2 := by
    rw [f3 _ (by decide) (by decide)]; simp only [s2, NSt.setS_env]
    rw [h1fr _ (by decide), hfr' _ (by decide), eR2]
  have g4 := CStm.Good.set (x := x) (w := w) (st := s3) (r := rc2) (e := .add (rv rc2) (rv r4R2))
    (by simp only [Ex.Fits, rv, Ex.eval, e32, e3R2]
        have : QB + (k + 1) * R2 + 1 + 2 < 2 ^ w := by
          have := hQR _ (List.getElem_mem (show 0 < cs.length by omega))
          have := hcs _ (List.getElem_mem (show 0 < cs.length by omega))
          omega
        have h1 : (q + 1) * R2 ≤ (k + 1) * R2 := Nat.mul_le_mul_right _ (by omega)
        have h2 : (q + 1) * R2 = q * R2 + R2 := add_one_mul q R2
        omega)
  set s4 := s3.set rc2 ((Ex.add (rv rc2) (rv r4R2) : Ex CR).eval s3.env)
  have e41 : s4.env rc1 = q := by
    simp only [s4, NSt.set_env, Function.update_of_ne (show rc1 ≠ rc2 by decide)]
    rw [f3 _ (by decide) (by decide)]; simp only [s2, NSt.setS_env]
    rw [h1fr _ (by decide), e1]
  have g5 := CStm.Good.set (x := x) (w := w) (st := s4) (r := rc1) (e := .add (rv rc1) (.const 1))
    (by simp only [Ex.Fits, rv, Ex.eval, e41]
        have : q + 1 < 2 ^ w := by
          have : q + 1 ≤ q * cs.length + cs.length := by nlinarith
          omega
        omega)
  set s5 := s4.set rc1 ((Ex.add (rv rc1) (.const 1) : Ex CR).eval s4.env)
  have hb5 := g5.bdd hw (g4.bdd hw hb3.1 hb3.2).1 (g4.bdd hw hb3.1 hb3.2).2
  -- frames from s1 to s5
  have q51 : ∀ r, r ≠ rc1 → r ≠ rc2 → r ≠ rc8 → r ≠ r4Dist → s5.env r = s1.env r := by
    intro r h1 h2 h3 h4
    simp only [s5, s4, NSt.set_env, Function.update_of_ne h1, Function.update_of_ne h2]
    rw [f3 r h3 h4]; rfl
  have k5 : s5.stk = Function.update (Function.update s1.stk qOrsB []) qRkF
      ((s1.stk qOrsB).reverse ++ (0 :: s1.stk qRkF)) := by
    simp only [s5, s4, NSt.set_stk, k3, s2, NSt.setS_stk,
      Function.update_of_ne (show qOrsB ≠ qRkF by decide), Function.update_self, Ex.eval]
    funext q'
    by_cases h : q' = qRkF
    · subst h; simp +decide
    · by_cases h' : q' = qOrsB
      · subst h'; simp +decide
      · simp [Function.update_of_ne h, Function.update_of_ne h']
  refine ⟨s5, (g1.seq (gp.seq (g3.seq (g4.seq g5)))).mono ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, hb5.1, hb5.2, ?_⟩
  · simp only [Ex.size, rv]
    have hs : (s2.stk qOrsB).length = cs.length := by
      simp +decide [s2, Function.update_of_ne (show qOrsB ≠ qRkF by decide), h1B]
    rw [hs]; nlinarith
  · have ee : EE s1 s5 [] := EE.of_frame (by rw [k5]; simp [Function.update_of_ne
      (show q4E ≠ qRkF by decide), Function.update_of_ne (show q4E ≠ qOrsB by decide)])
      (q51 _ (by decide) (by decide) (by decide) (by decide)) (by
        simp only [s5, s4]; show s3.pos = _; rw [p3]; rfl) (by
        simp only [s5, s4]; show s3.out = _; rw [o3]; rfl)
    have := (hE.trans hE1).trans ee
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    simpa using this
  · rw [k5]; simp +decide [h1R, h1B]
  · rw [k5]; simp +decide
  · intro q' h1 h2 h3
    rw [k5]; simp only [Function.update_of_ne h2, Function.update_of_ne h3]
    rw [h1o q' h1 h2 h3, hso q' h1 h2 h3]
  · simp +decide [s5, Ex.eval, rv, e41]
  · simp only [s5, NSt.set_env, Function.update_of_ne (show rc2 ≠ rc1 by decide), s4,
      Function.update_self, Ex.eval, rv, e32, e3R2]; ring
  · rw [q51 _ (by decide) (by decide) (by decide) (by decide), h16]
    have : q * cs.length + cs.length ≠ 0 := by omega
    simp [this, add_mul]
  · intro _
    rw [q51 _ (by decide) (by decide) (by decide) (by decide), h17 (by omega)]
    rw [add_mul, one_mul]
  · rw [q51 _ (by decide) (by decide) (by decide) (by decide), h1H]; ring
  · rw [q51 _ (by decide) (by decide) (by decide) (by decide), h1TP]; ring
  · rw [q51 _ (by decide) (by decide) (by decide) (by decide)]; exact h1V
  · intro r hr
    simp only [qW, entW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [q51 r hr.1 hr.2.1 hr.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.2.2.2.2,
      h1fr r (by simp [entW]; tauto), hfr' r (by simp [qW, entW]; tauto)]

end Lax119563Proofs.Compiler
