import Lax119563Proofs.Compiler.P4SchL2

/-!
# Pass `P4`, schema part: the column loop of section 2, the step (`p4S2_step`)
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

lemma take_succ_getElem {α : Type*} (l : List α) {r : ℕ} (hr : r < l.length) :
    l.take (r + 1) = l.take r ++ [l[r]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hr]; rfl

set_option maxHeartbeats 16000000 in
/-- **One step of the column loop of section 2.** -/
lemma p4S2_step {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (hk : 2 ≤ k) (ε : ZMod 2)
    (e : Fin I.schemas.length) (R Q : List ℕ) (s0 : NSt CR CQ)
    (hF : L2Fix I x ε e s0) (hB : L2Bnd I w ε e s0)
    (r : ℕ) (hr : r < (cL I e).length) (s : NSt CR CQ) (hI : L2Inv I w ε e R Q s0 r s) :
    ∃ s', Good x w p4C2 s s' ((k + 3) * (((rowsL (cL I e)[r]).length + 1) *
        (800 * Ex.nodeCost w))) ∧ L2Inv I w ε e R Q s0 (r + 1) s' := by
  obtain ⟨e0k, e0T, e0LB, e0E, e0D, e0R2, e0P, h0p⟩ := hF
  obtain ⟨hW, hkl, hcs, hAs, hM⟩ := hB
  obtain ⟨hEE, hR, hOB, hA, hA2, hso, eK, eH, eTP, eSP, hbd, hfr⟩ := hI
  have hentS := entB_succ I e hr
  have hEb := entBefore_get I e hr
  have hidx : (coordList (dom I e)).idxOf (cL I e)[r] = r :=
    (nodup_coordList (dom I e)).idxOf_getElem _ _
  have hRc : s.stk qRkF = codesL I e (cL I e)[r] ++ 0 ::
      (((cL I e).drop (r + 1)).flatMap (fun c => codesL I e c ++ [0]) ++ Q) := by
    rw [hR, List.drop_eq_getElem_cons hr, List.flatMap_cons]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hAc : s.stk qAns = a2C I e ((cL I e)[r], r) ++
      ((((cL I e).zipIdx.drop (r + 1)).flatMap (a2C I e)) ++ R) := by
    rw [hA, zipIdx_drop_cons _ hr, List.flatMap_cons, List.append_assoc]
  have hEt := take_succ_getElem (cL I e) hr
  have hAt := zipIdx_take_succ (cL I e) hr
  have hcD : (cL I e)[r] ∈ cL I e := List.getElem_mem hr
  have hce : (cL I e)[r] ∈ dom I e := mem_coordList.mp hcD
  generalize (cL I e)[r] = c at hentS hEb hidx hRc hAc hEt hAt hcD hce ⊢
  have hT1 : tnN (Matrix.isTern (sch I e)) ≤ 1 := by unfold tnN; split_ifs <;> omega
  have hLB := locBase_le_length I
  obtain ⟨hsec, hsum, hcolW, hsumB, htrkB, hcofB⟩ := sec_bounds I e
  have hcoef := coef_bound I e
  have hrowsR := length_rowsR_le I e
  have hentB := entB_le I e (r + 1)
  have hst := length_stepsC_rowsL c
  have hrow := rowsL_pos hk c
  have hlen := length_codesL I e c
  have hk1 : k ≤ H I := by nlinarith
  have hl1 : ℓ ≤ H I := by nlinarith
  have fk : s.env rKk = k := by rw [hfr _ (by decide), e0k]
  have fT : s.env r4Tn = tnN (Matrix.isTern (sch I e)) := by rw [hfr _ (by decide), e0T]
  have fLB : s.env rLB = locBase I := by rw [hfr _ (by decide), e0LB]
  have fE : s.env r4Eps = ε.val := by rw [hfr _ (by decide), e0E]
  have fR2 : s.env r4R2 = 2 * (rowsR I e).length := by rw [hfr _ (by decide), e0R2]
  have fP : s.env r4Prev = coefBase I e := by rw [hfr _ (by decide), e0P]
  have hεv := ZMod.val_lt ε
  obtain ⟨oU, mU, hAH, hU, hoU⟩ := ans2_hyp I hw ε e hce r (by omega) (by omega)
  have hpre : (((cL I e).take r).flatMap (colE2 I ε e)).length ≤
      ((cL I e).flatMap (colE2 I ε e)).length := ((List.take_sublist _ _).flatMap _).length_le
  have hM' : s.env r4M = s0.env r4M + (((cL I e).take r).flatMap (colE2 I ε e)).length :=
    hEE.2.1
  have hS1 : (k + 1) * (codesL I e c).length = (stepsC c).length := by rw [hlen, hst]
  have hQ2 : ∀ X ∈ codesL I e c,
      coefBase I e + (k + 1) * (2 * (rowsR I e).length) + X + 2 < 2 ^ w := by
    intro X hX
    have := codesL_lt I e hce hX
    have h2 : (k + 1) * (2 * (rowsR I e).length) = 2 * ((k + 1) * (rowsR I e).length) := by ring
    omega
  have hm12 : 12 * (codesL I e c).length * (k + 1) = 12 * (stepsC c).length := by
    rw [← hS1]; ring
  obtain ⟨s', g, hE1, hR1, hB1, hA1, hA21, hso1, eH1, eTP1, eSP1, eK1, -, hbd1, hfr1⟩ :=
    p4C2_good (x := x) hw s k (T := tnN (Matrix.isTern (sch I e)))
      (Hc := updBase I e + 4 * entB I e r) (TPc := trackBase I e + 2 * entB I e r)
      (SP := sumBase I e + 2 * r) (QB := coefBase I e) (R2 := 2 * (rowsR I e).length)
      (LB := locBase I) (K := r) (oU := oU) (mU := mU) (codesL I e c) _ _ _ (by omega)
      (codesL_pos I hk e c) hRc hOB hAc (by rw [fE]; exact hAH) fk eH eTP fT hT1 eSP fR2 fLB
      fP eK (by rw [fE]; omega) (hbd.1 _) hbd (by rw [hEE.2.2.1]; exact h0p) (by omega)
      (by omega) (by rw [hS1]; unfold updBase; omega) (by rw [hS1]; omega) (by omega) hQ2
      (by omega) (by rw [hm12, hM']; omega)
  refine ⟨s', g.mono (by rw [hlen]), ?_, ?_, hB1, ?_, ?_, ?_, eK1, ?_, ?_, ?_, hbd1, ?_⟩
  · rw [hEt, List.flatMap_append, List.flatMap_singleton]
    refine hEE.trans ?_
    have h2 := col2_eq I ε e hce r hidx (updBase I e) oU mU hU
    rw [colE2, h2, hEb]
    exact hE1
  · rw [hR1]
  · rw [hA1]
  · rw [hA21, hA2, hAt, List.flatMap_append, List.flatMap_singleton]; simp
  · intro q h1 h2 h3 h4 h5; rw [hso1 q h1 h2 h3 h4 h5, hso q h1 h2 h3 h4 h5]
  · rw [eH1, hS1, hentS]; ring
  · rw [eTP1, hS1, hentS]; ring
  · rw [eSP1]; ring
  · intro reg hreg; rw [hfr1 reg hreg, hfr reg hreg]

end Lax119563Proofs.Compiler
