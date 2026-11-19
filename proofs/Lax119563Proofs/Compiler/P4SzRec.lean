import Lax119563Proofs.Compiler.P4SzPush
import Lax119563Proofs.Compiler.PSch

/-!
# Pass `P4` (program): moving a schema record back onto `qSch`

`p4SRec` moves the record `R ++ [nE, nC]` (`|R| = rL1`) from the top of `qT` back onto
`qSch` (reversing it, so `qSch` is rebuilt), keeping `nE`, `nC` in `rNe`, `rNc`
(**`p4SRec_good`**).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-- Move one schema record from `qT` to `qSch`, keeping its last two words. -/
def p4SRec : CStm CR CQ :=
  .seq (moveN qT qSch rL1 rI rT) (.seq (.pop qT rNe) (.seq (.push qSch (rv rNe))
    (.seq (.pop qT rNc) (.push qSch (rv rNc)))))

lemma p4SRec_good {x : List Bool} {w : ℕ} (s : NSt CR CQ) (R R' : List ℕ) (b c : ℕ)
    (hT : s.stk qT = R ++ b :: c :: R') (hL : s.env rL1 = R.length)
    (hRw : ∀ v ∈ R, v < 2 ^ w) (hb : b < 2 ^ w) (hc : c < 2 ^ w) (hn : R.length + 1 < 2 ^ w) :
    ∃ s', Good x w p4SRec s s' ((R.length + 5) * (12 * Ex.nodeCost w)) ∧
      s'.stk = Function.update (Function.update s.stk qT R') qSch
        (c :: b :: R.reverse ++ s.stk qSch) ∧
      s'.env rNe = b ∧ s'.env rNc = c ∧ s'.pos = s.pos ∧ s'.out = s.out ∧
      ∀ r, r ≠ rI → r ≠ rT → r ≠ rNe → r ≠ rNc → s'.env r = s.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  obtain ⟨s1, r1, h1s, h1f⟩ := moveN_good (x := x) (w := w) (src := qT) (dst := qSch)
    (cnt := rL1) (i := rI) (t := rT) (by decide) (by decide) (by decide) (by decide) s hL
    (by rw [hT]; simp) hn (by rw [hT, List.take_left]; exact hRw)
  have e1T : s1.stk qT = b :: c :: R' := by
    rw [h1s, movedStk, Function.update_of_ne (by decide), Function.update_self, hT,
      List.drop_left]
  have e1S : s1.stk qSch = R.reverse ++ s.stk qSch := by
    rw [h1s, movedStk, Function.update_self, hT, List.take_left]
  have r2 := Good.pop (x := x) (w := w) (st := s1) qT rNe
  set s2 := (s1.setS qT (s1.stk qT).tail).set rNe ((s1.stk qT).headD 0)
  have e2N : s2.env rNe = b := by simp (config := { decide := true }) [s2, e1T]
  have r3 := Good.push (x := x) (w := w) (st := s2) (q := qSch) (e := rv rNe)
    (by simp only [Ex.Fits, rv, e2N]; exact hb)
  set s3 := s2.setS qSch ((rv rNe : Ex CR).eval s2.env :: s2.stk qSch)
  have r4 := Good.pop (x := x) (w := w) (st := s3) qT rNc
  set s4 := (s3.setS qT (s3.stk qT).tail).set rNc ((s3.stk qT).headD 0)
  have e3T : s3.stk qT = c :: R' := by
    simp (config := { decide := true }) [s3, s2, e1T, Function.update_of_ne (show qT ≠ qSch by decide)]
  have e4C : s4.env rNc = c := by simp (config := { decide := true }) [s4, e3T]
  have r5 := Good.push (x := x) (w := w) (st := s4) (q := qSch) (e := rv rNc)
    (by simp only [Ex.Fits, rv, e4C]; exact hc)
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [rv, Ex.size]; nlinarith
  · simp only [NSt.setS_stk, NSt.set_stk]
    funext q
    by_cases hq : q = qSch
    · subst hq
      simp (config := { decide := true }) [s4, s3, s2, e1S, e2N, Function.update_of_ne (show qSch ≠ qT by decide), Ex.eval,
        rv, e4C, e1T]
    · by_cases hq' : q = qT
      · subst hq'
        simp (config := { decide := true }) [s4, e3T, Function.update_of_ne hq]
      · simp only [Function.update_of_ne hq, Function.update_of_ne hq']
        simp (config := { decide := true }) [s4, s3, s2, Function.update_of_ne hq, Function.update_of_ne hq', h1s, movedStk]
  · simp (config := { decide := true }) [s4, s3, Function.update_of_ne (show rNe ≠ rNc by decide), e2N]
  · simp (config := { decide := true }) [e4C]
  · simp (config := { decide := true }) [s4, s3, s2]; exact h1f.1
  · simp (config := { decide := true }) [s4, s3, s2]; exact h1f.2.1
  · intro r h1 h2 h3 h4
    simp (config := { decide := true }) [s4, s3, s2, Function.update_of_ne h3, Function.update_of_ne h4]
    exact h1f.2.2 r (by simp (config := { decide := true }) [h1, h2])

end Lax119563Proofs.Compiler
