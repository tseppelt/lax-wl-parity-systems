import Lax119563Proofs.Compiler.P4SchL1b
import Lax119563Proofs.Compiler.PChainSize

/-!
# Pass `P4`, schema part: the column loop of section 1, the step (`p4S1_step`)
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The fixed data of the section-1 loop of schema `e`. -/
def L1Fix (w : ℕ) (x : List Bool) (ε : ZMod 2) (e : Fin I.schemas.length) (restx : List Bool)
    (s0 : NSt CR CQ) : Prop :=
  x.drop s0.pos = encodeNats ((cL I e).flatMap cdesc) ++ restx ∧
  s0.env rL = ℓ ∧ s0.env rKk = k ∧ s0.env r4BR = blkRows (cL I e) ∧
  s0.env r4Tn = tnN (Matrix.isTern (sch I e)) ∧ s0.env rLB = locBase I ∧ s0.env r4Eps = ε.val ∧
  s0.env r4D = (cL I e).length ∧ s0.stk qOrsF = orsL (cL I e) ∧ s0.stk qOrsB = [] ∧
  s0.pos ≤ x.length

/-- The numeric bounds of the section-1 loop. -/
def L1Bnd (w : ℕ) (e : Fin I.schemas.length) (s0 : NSt CR CQ) : Prop :=
  16 * (H I + (ordL I).length + 1) ≤ 2 ^ w ∧ k * (ℓ + 1) ≤ H I ∧
  (cL I e).length ≤ H I ∧ ansBase I e + 3 * (cL I e).length ≤ 3 * H I ∧
  s0.env r4M + 3 * (ordL I).length + 16 < 2 ^ w

set_option maxHeartbeats 16000000 in
lemma p4S1_step {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (hk : 2 ≤ k) (hE : I.schemas ≠ [])
    (ε : ZMod 2) (e : Fin I.schemas.length) (R : List ℕ) (restx : List Bool) (s0 : NSt CR CQ)
    (hF : L1Fix I w x ε e restx s0) (hB : L1Bnd I w e s0)
    (hMe : ((cL I e).zipIdx.flatMap fun q => colE1 I ε e q.1 q.2).length ≤ 3 * (ordL I).length)
    (r : ℕ) (hr : r < (cL I e).length) (s : NSt CR CQ) (hI : L1Inv I w ε e R s0 r s) :
    ∃ s', Good x w p4C1 s s' (200 * ((encodeNats (cdesc (cL I e)[r])).length + ℓ +
        (k + 2) * ((rowsL (cL I e)[r]).length + 1) + 10) * Ex.nodeCost w) ∧
      L1Inv I w ε e R s0 (r + 1) s' := by
  obtain ⟨hx, e0L, e0k, e0BR, e0T, e0LB, e0E, e0D, h0F, h0B, h0p⟩ := hF
  obtain ⟨hW, hkl, hcs, hAs, hM⟩ := hB
  obtain ⟨hEM, hRk, hA, hA2, hso, eK, eD, eP, eH, eSP, eTP, hV, hbd, hpos, hout, hfr⟩ := hI
  set cs := cL I e with hcs_def
  set c := cs[r] with hc_def
  have hcD : c ∈ cs := List.getElem_mem hr
  have hce : c ∈ dom I e := mem_coordList.mp hcD
  set T := tnN (Matrix.isTern (sch I e)) with hT
  have hT1 : T ≤ 1 := by simp only [hT, tnN]; split_ifs <;> omega
  have hLB := locBase_le_length I
  obtain ⟨hsec, hsum, hcolW, hsumB, htrkB, hcofB⟩ := sec_bounds I e
  have hentB := entB_le I e (r + 1)
  have hentS := entB_succ I e hr
  have hst := length_stepsC_rowsL c
  have hrow := rowsL_pos hk c
  have hrs : r * colW I e ≤ cs.length * colW I e := Nat.mul_le_mul_right _ hr.le
  have hrs1 : (r + 1) * colW I e ≤ cs.length * colW I e := Nat.mul_le_mul_right _ hr
  have hk1 : k ≤ H I := by nlinarith
  have hl1 : ℓ ≤ H I := by nlinarith
  -- fixed registers
  have fL : s.env rL = ℓ := by rw [hfr _ (by decide), e0L]
  have fk : s.env rKk = k := by rw [hfr _ (by decide), e0k]
  have fBR : s.env r4BR = blkRows cs := by rw [hfr _ (by decide), e0BR]
  have fT : s.env r4Tn = T := by rw [hfr _ (by decide), e0T]
  have fLB : s.env rLB = locBase I := by rw [hfr _ (by decide), e0LB]
  have fE : s.env r4Eps = ε.val := by rw [hfr _ (by decide), e0E]
  have hεv := ZMod.val_lt ε
  -- input
  have hxs : x.drop s.pos = encodeNats ((c.1 : ℕ) :: blockDescription c.2) ++
      (encodeNats ((cs.drop (r + 1)).flatMap cdesc) ++ restx) := by
    rw [hpos, drop_add, hx, cdesc_split cs hr, encodeNats_append, List.append_assoc,
      List.drop_left, List.cons_append, ← encNats_cons, encodeNats_append, List.append_assoc]
  -- answers
  have hAc : s.stk qAns = ans1 T (aU I e c (ansBase I e + 3 * r))
      (aV I e c (ansBase I e + 3 * r + 1)) (aW I e c (sW I e r)) ++
      (((cs.zipIdx.drop (r + 1)).flatMap (a1C I e)) ++ R) := by
    rw [hA, zipIdx_drop_cons cs hr, List.flatMap_cons, List.append_assoc]; rfl
  have hsq : ∀ j, j ≤ 2 → ansBase I e + 3 * r + j < 2 ^ w := fun j hj => by omega
  have hsW : sW I e r < 2 ^ w := by unfold sW; split_ifs <;> omega
  have hoU := aOff_le I hE (memU I hce) (ansBase I e + 3 * r)
  have hoV := aOff_le I hE (memV I hce) (ansBase I e + 3 * r + 1)
  have hoW := aOff_le I hE (memEnd I hce) (sW I e r)
  -- the column
  have hc1 : (c.1 : ℕ) < k := c.1.2
  have hbd' : (Nat.bits (c.1 : ℕ)).length < w := bits_lt_of_le (H := H I) (by omega) (by omega)
  have hbsl : (blockDescription c.2).length = ℓ := length_blockDescription' _
  have hBR := blkRows_le cs
  have hDle : distR I e r ≤ r := by
    unfold distR; split_ifs
    · omega
    · have := dChg_le k ((cs.take r).map fun c => (c.1 : ℕ)); simp at this; omega
  have hpre : ((cs.zipIdx.take r).flatMap fun q => colE1 I ε e q.1 q.2).length ≤
      (cs.zipIdx.flatMap fun q => colE1 I ε e q.1 q.2).length :=
    ((List.take_sublist _ _).flatMap _).length_le
  -- previous block
  have hPw : s.env r4Prev < 2 ^ w := hbd.1 _
  -- the codes
  have hdist := dist1_eq cs hr (s.env r4Prev) (fun h0 => eP (by omega) h0)
  have hcodes := codesC_eq I hk e hr
  rw [← hdist] at hcodes
  have hn : (codesC k (blkRows cs) (dist1 r (distR I e r) (s.env r4Prev) (c.1 : ℕ)) (c.1 : ℕ)
      (orsL cs) (blockDescription c.2)).length = (rowsL c).length := by
    rw [hcodes]; simp [rkL]
  obtain ⟨s', g, hEM1, hRk1, hA1, hA21, hso1, eD1, eP1, eTP1, eH1, eSP1, eK1, hV1, hbd1, hp1, ho1,
      hfr1⟩ := p4C1_good (x := x) hw s (i := (c.1 : ℕ)) (k := k) (BR := blkRows cs) (K := r)
    (D := distR I e r) (P := s.env r4Prev) (H := schBase I e + r * colW I e)
    (SP := sumBase I e + 2 * r) (TP := trackBase I e + 2 * entB I e r) (T := T) (LB := locBase I)
    (blockDescription c.2) (orsL cs) _ (aU I e c (ansBase I e + 3 * r))
    (aV I e c (ansBase I e + 3 * r + 1)) (aW I e c (sW I e r)) _ hxs hbd'
    (blockDescription_le _) (orsL_le _) (by rw [length_orsL, hbsl])
    (by rw [fL, hbsl]) (by rw [hso _ (by decide) (by decide) (by decide) (by decide), h0F])
    (by rw [hso _ (by decide) (by decide) (by decide) (by decide), h0B]) hAc
    (fun _ => ansRec_ok I _ (hsq 0 (by omega)) (by omega) hw)
    (fun _ => ansRec_ok I _ (hsq 1 (by omega)) (by omega) hw)
    (ansRec_ok I _ hsW (by omega) hw)
    fk fBR eK eD rfl eH eSP eTP fT hT1 fLB (by rw [fE]; omega) hV hbd (by omega) hk hc1
    (2 ^ w - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [hsumB]; omega) (by rw [hsumB, htrkB]; omega)
    (by rw [hn, htrkB, hsumB, ← hst]; omega) (by rw [hbsl]; omega)
    (fun _ => by omega) (fun _ => by omega) (by omega)
    (by have := hEM.2; omega)
  have hidx : cs.idxOf c = r := (nodup_coordList (dom I e)).idxOf_getElem _ _
  have hLT : trackBase I e + 2 * entB I e r + 2 * ((k + 1) *
      (codesC k (blkRows cs) (dist1 r (distR I e r) (s.env r4Prev) (c.1 : ℕ)) (c.1 : ℕ)
        (orsL cs) (blockDescription c.2)).length - 1) =
      trackBase I e + 2 * (entBefore I e c + (stepsC c).length - 1) := by
    rw [hn, entBefore_get I e hr, hst]
    have : 1 ≤ (k + 1) * (rowsL c).length := by nlinarith
    omega
  have hpos' : (encodeNats ((cs.take (r + 1)).flatMap cdesc)).length =
      (encodeNats ((cs.take r).flatMap cdesc)).length +
        (encodeNats ((c.1 : ℕ) :: blockDescription c.2)).length := by
    rw [List.take_add_one, List.getElem?_eq_getElem hr]
    simp [encodeNats_append, cdesc]
  refine ⟨s', g.mono ?_, ?_, ?_, ?_, ?_, ?_, eK1, ?_, ?_, ?_, ?_, ?_, hV1, hbd1, ?_, ?_, ?_⟩
  · rw [hn, hbsl]; simp only [cdesc]; exact le_rfl
  · rw [zipIdx_take_succ cs hr, List.flatMap_append, List.flatMap_singleton]
    refine hEM.trans ?_
    rw [colE1_eq I hk ε e hce r hidx (ansBase I e + 3 * r) (ansBase I e + 3 * r + 1) (sW I e r),
      ← hLT, ← fE]
    exact hEM1
  · rw [hRk1, hRk, hcodes, List.take_add_one, List.getElem?_eq_getElem hr]
    simp [codesL]
  · exact hA1
  · rw [hA21, hA2, zipIdx_take_succ cs hr, List.flatMap_append, List.flatMap_singleton]
    simp [a1C]
  · intro q h1 h2 h3 h4; rw [hso1 q h1 h2 h3 h4, hso q h1 h2 h3 h4]
  · rw [eD1, hdist]; simp [distR]
  · intro _ _; rw [eP1]; simp
  · rw [eH1, hcolW]; ring
  · rw [eSP1]; ring
  · rw [eTP1, hn, entB_succ I e hr, hst]; ring
  · rw [hp1, hpos, hpos']; ring
  · rw [ho1, hout]
  · intro reg hreg; rw [hfr1 reg hreg, hfr reg hreg]

end Lax119563Proofs.Compiler
