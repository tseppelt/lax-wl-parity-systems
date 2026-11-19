import Lax119563Proofs.Compiler.P4SchQ

/-!
# Pass `P4`, schema part: a column of section 2

* `p4Qs_good`: the loop over `q ≤ k` (edges `col2E`);
* `p4Drop_good`: drop the rank codes of the column;
* `p4C2_good`: one column (binary schemas: the start answer `U` is popped first).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

lemma qs_cost (k M N : ℕ) (hM : 1 ≤ M) (hN : 64 ≤ N) :
    (k + 1) * (M * (700 * N) + ((1 + (1 + 1 + 1) + 1) * N + 1)) +
      ((1 + (1 + 1 + 1) + 1) * N + 1) ≤ (k + 2) * (M * (800 * N)) := by
  have h1 : N ≤ M * N := Nat.le_mul_of_pos_left N hM
  have h2 : (k + 1) * N ≤ (k + 1) * (M * N) := Nat.mul_le_mul_left _ h1
  nlinarith

set_option maxHeartbeats 4000000 in
lemma p4Qs_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s : NSt CR CQ) (k : ℕ)
    {T Hc TPc SP QB R2 LB oU mU : ℕ} (cs rest : List ℕ) (hn : 1 ≤ cs.length)
    (hcs : ∀ X ∈ cs, 1 ≤ X)
    (hR : s.stk qRkF = cs ++ 0 :: rest) (hB : s.stk qOrsB = [])
    (e1 : s.env rc1 = 0) (e2 : s.env rc2 = QB) (e6 : s.env rc6 = 1) (ek : s.env rKk = k)
    (eH : s.env r4H = Hc) (eTP : s.env r4TP = TPc)
    (eT : s.env r4Tn = T) (hT : T ≤ 1) (eSP : s.env r4SP = SP) (eR2 : s.env r4R2 = R2)
    (eLB : s.env rLB = LB) (eo : s.env rc3 = oU) (em : s.env rc4 = mU) (hm2 : mU ≤ 2)
    (hV : s.env r4V < 2 ^ w) (hbd : s.Bdd w) (hpos : s.pos ≤ x.length)
    (hk : k + 2 < 2 ^ w)
    (hH : Hc + 4 * ((k + 1) * cs.length) + 4 < 2 ^ w)
    (hTP : TPc + 2 * ((k + 1) * cs.length) + 2 < 2 ^ w)
    (hSP : SP + 2 < 2 ^ w) (hQR : ∀ X ∈ cs, QB + (k + 1) * R2 + X + 2 < 2 ^ w)
    (hU : LB + oU + 2 < 2 ^ w)
    (hm : s.env r4M + 12 * cs.length * (k + 1) + 12 < 2 ^ w) :
    ∃ s', Good x w p4Qs s s' ((k + 2) * ((cs.length + 1) * (800 * Ex.nodeCost w))) ∧
      qInv w x T Hc TPc SP QB R2 LB oU mU cs rest s (k + 1) s' := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have hI0 : qInv w x T Hc TPc SP QB R2 LB oU mU cs rest s 0 s := by
    refine ⟨by simpa using EE.refl s, hR, hB, fun _ _ _ _ => rfl, e1, by simp [e2], by simp [e6],
      fun h => by simp at h, by simp [eH], by simp [eTP], hV, hbd, hpos, fun _ _ => rfl⟩
  have hek : ∀ s', qInv w x T Hc TPc SP QB R2 LB oU mU cs rest s 0 s' ∨ True →
      True := fun _ _ => trivial
  obtain ⟨s', g, hI⟩ := CStm.Good.loop_idxC (x := x) (w := w)
    (e := .lt (rv rc1) (.add (rv rKk) (.const 1))) (body := p4QB) (k + 1)
    (qInv w x T Hc TPc SP QB R2 LB oU mU cs rest s) ((cs.length + 1) * (700 * Ex.nodeCost w))
    (by
      intro q hq s1 hs1
      have e1' := hs1.2.2.2.2.1
      have ek' : s1.env rKk = k := by rw [hs1.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by decide), ek]
      refine ⟨by simp only [Ex.Fits, rv, Ex.eval, e1', ek']; omega,
        by simp [Ex.eval, rv, e1', ek']; omega, ?_⟩
      exact p4QB_good hw s k cs rest hn hcs eT hT eSP eR2 eLB eo em hm2 hH hTP hSP hQR hU hm
        q hq s1 hs1)
    (by
      intro s1 hs1
      have e1' := hs1.2.2.2.2.1
      have ek' : s1.env rKk = k := by rw [hs1.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by decide), ek]
      exact ⟨by simp only [Ex.Fits, rv, Ex.eval, e1', ek']; omega, by simp [Ex.eval, rv, e1', ek']⟩)
    s hI0
  refine ⟨s', g.mono ?_, hI⟩
  simp only [condCost, Ex.size, rv]
  exact qs_cost k (cs.length + 1) (Ex.nodeCost w) (by omega) (by omega)

/-! ## Dropping the codes of a column -/

/-- Drop the codes of a column (up to and including the terminator). -/
def p4Drop : CStm CR CQ := .seq (.pop qRkF rc5) (.loop (rv rc5) (.pop qRkF rc5))

set_option maxHeartbeats 2000000 in
lemma p4Drop_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s : NSt CR CQ) (cs rest : List ℕ)
    (hcs : ∀ X ∈ cs, 1 ≤ X) (hcw : ∀ X ∈ cs, X < 2 ^ w) (hR : s.stk qRkF = cs ++ 0 :: rest) :
    ∃ s', Good x w p4Drop s s' ((cs.length + 1) * (10 * Ex.nodeCost w)) ∧
      s'.stk = Function.update s.stk qRkF rest ∧ s'.pos = s.pos ∧ s'.out = s.out ∧
      ∀ r, r ≠ rc5 → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have h1w : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  set L := cs ++ 0 :: rest
  let P : ℕ → NSt CR CQ → Prop := fun p s' =>
    s'.stk = Function.update s.stk qRkF (L.drop (p + 1)) ∧ s'.env rc5 = L.getD p 0 ∧
      s'.pos = s.pos ∧ s'.out = s.out ∧ ∀ r, r ≠ rc5 → s'.env r = s.env r
  have g0 := CStm.Good.pop (x := x) (w := w) (st := s) qRkF rc5
  have hP0 : P 0 ((s.setS qRkF (s.stk qRkF).tail).set rc5 ((s.stk qRkF).headD 0)) := by
    refine ⟨by simp [hR, L], ?_, rfl, rfl, fun r h => by simp [Function.update_of_ne h]⟩
    simp [hR, L]; cases cs <;> simp
  obtain ⟨s', g, hP⟩ := CStm.Good.loop_idxC (x := x) (w := w) (e := rv rc5) (body := .pop qRkF rc5)
    cs.length P (5 * Ex.nodeCost w)
    (by
      intro j hj s1 ⟨k1, v1, p1, o1, f1⟩
      have hv : L.getD j 0 = cs[j] := by
        simp only [L]; rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hj]
      rw [hv] at v1
      have := hcs _ (List.getElem_mem hj)
      have := hcw _ (List.getElem_mem hj)
      refine ⟨by simp only [rv, Ex.Fits, v1]; omega, by simp only [rv, Ex.eval, v1]; omega, ?_⟩
      have hd : L.drop (j + 1) = L.getD (j + 1) 0 :: L.drop (j + 1 + 1) := by
        rw [List.getD_eq_getElem _ _ (by simp [L]; omega)]
        exact List.drop_eq_getElem_cons (by simp [L]; omega)
      refine ⟨_, (CStm.Good.pop (x := x) (w := w) (st := s1) qRkF rc5).mono (by omega), ?_, ?_,
        p1, o1, ?_⟩
      · simp [k1, hd]
      · simp [k1, hd]
      · intro r h; simp [Function.update_of_ne h, f1 r h])
    (by
      rintro s1 ⟨-, v1, -⟩
      have : L.getD cs.length 0 = 0 := by
        simp only [L]; rw [List.getD_eq_getElem _ _ (by simp)]; simp
      rw [this] at v1
      exact ⟨by simp only [rv, Ex.Fits, v1]; omega, by simp [rv, Ex.eval, v1]⟩)
    _ hP0
  obtain ⟨k1, -, p1, o1, f1⟩ := hP
  refine ⟨s', (g0.seq g).mono ?_, ?_, p1, o1, f1⟩
  · simp only [condCost, rv, Ex.size]; nlinarith
  · rw [k1]
    congr 1
    simp only [L]
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
      show cs.length + 1 - cs.length = 1 by omega, List.drop_one, List.tail_cons]

end Lax119563Proofs.Compiler
