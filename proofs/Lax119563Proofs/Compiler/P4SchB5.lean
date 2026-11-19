import Lax119563Proofs.Compiler.P4SchB4

/-!
# Pass `P4`, schema part: one schema (`p4Body_good`)
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

lemma notMem_of_bodyW_rd : ∀ r : Fin CR, r ∉ bodyW → r ∉ [rc1, rc2, rP, rT, r4Tn, r4D] := by
  decide
lemma notMem_of_bodyW_rec :
    ∀ r : Fin CR, r ∉ bodyW → r ∉ [rT, rP, rc1, r4R2, r4BR, r4NE, r4NC] := by decide
lemma notMem_of_bodyW_bas : ∀ r : Fin CR, r ∉ bodyW → r ∉ basW := by decide
lemma notMem_of_bodyW_c1 : ∀ r : Fin CR, r ∉ bodyW → r ∉ c1W := by decide
lemma notMem_of_bodyW_mid : ∀ r : Fin CR, r ∉ bodyW → r ∉ midW := by decide
lemma notMem_of_bodyW_c2 : ∀ r : Fin CR, r ∉ bodyW → r ∉ c2W := by decide
lemma notMem_of_bodyW_end : ∀ r : Fin CR, r ∉ bodyW → r ≠ r4SB ∧ r ≠ rJ := by decide

lemma schSize_ge (e : Fin I.schemas.length) :
    6 * nEnt I e + 2 * (cL I e).length ≤ schSize I e := by
  rw [schSize_eq' I e]; simp only [cL]; split_ifs <;> omega

lemma permsL_ge (hk : 2 ≤ k) (e : Fin I.schemas.length) :
    ℓ + 1 ≤ (encodeNats (permsL I e)).length := by
  have h1 := length_le_encodeNats (permsL I e)
  rw [length_permsL] at h1
  have ha : 2 ≤ arity (sch I e) := by unfold arity; split_ifs <;> omega
  have h2 : 1 * (ℓ + 1) ≤ arity (sch I e) * k * (ℓ + 1) :=
    Nat.mul_le_mul_right _ (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))
  rw [Nat.mul_assoc] at h2
  omega

set_option maxHeartbeats 40000000 in
/-- **One schema.** -/
theorem p4Body_good {w : ℕ} (hw : 2 ≤ w) (ε : ZMod 2) (s0 : NSt CR CQ) (hF : BFix I w ε s0)
    {j : ℕ} (hj : j < I.schemas.length) (s : NSt CR CQ) (hI : BInv I w ε s0 j s) :
    ∃ s', Good (encodeSystem I) w p4Body s s'
        (5000 * Ex.nodeCost w * ((encodeNats (schD I ⟨j, hj⟩)).length +
          schSize I ⟨j, hj⟩ + 1)) ∧
      BInv I w ε s0 (j + 1) s' := by
  obtain ⟨hE, hk, hℓ, hW16, f0L, f0k, f0LB, f0Eps, f0PL, f0M⟩ := hF
  obtain ⟨hjE, eJ, hpos, eSB, hS2, hSch, hAns, hA2, h4E, hRk, hRkF, hOF, hOB, hoth, eM, hout,
    hbd, hfr⟩ := hI
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  set e : Fin I.schemas.length := ⟨j, hj⟩ with he
  have hH : 4 * (H I + 1) ≤ 2 ^ w := by omega
  have hkl := kl_le_H I hE
  have hcl := cL_le_H I e
  have hab := ansB_le I hℓ e
  have hLB := locBase_le_length I
  have hgE := length_gEdges I ε
  have hsE := schE_le_gEdges I ε e
  have hed : (edUp I ε j).length + (schE I ε e).length ≤ (gEdges I ε).length := by
    have h := edUp_le I ε (j + 1)
    rwa [edUp_succ I ε hj, List.length_append] at h
  obtain ⟨hsec, hsum, hcolW, hsumB, htrkB, hcofB⟩ := sec_bounds I e
  have hsz := schSize_eq I e
  have hsB : sBase I j + schSize I e ≤ locBase I := by
    have h := sBase_le I (j + 1)
    rwa [sBase_succ I hj] at h
  have hsBe : schBase I e = sBase I j := rfl
  have hhub : sumBase I e = schBase I e + hubSize I e := rfl
  have hE2 := schE_eq2 I ε e
  have hE2l := congrArg List.length hE2
  rw [List.length_append] at hE2l
  have hTn : tnN (Matrix.isTern (sch I e)) ≤ 1 := by unfold tnN; split_ifs <;> omega
  have hk1 : k ≤ H I := by nlinarith
  have hl1 : ℓ + 1 ≤ H I := by nlinarith
  have hBR := blkRows_le (cL I e)
  have hp : s.pos ≤ (encodeSystem I).length := by rw [hpos]; exact schAt_le I j
  -- fixed registers of `s`
  have fL : s.env rL = ℓ := by rw [hfr _ (by decide), f0L]
  have fk : s.env rKk = k := by rw [hfr _ (by decide), f0k]
  have fLB : s.env rLB = locBase I := by rw [hfr _ (by decide), f0LB]
  have fEps : s.env r4Eps = ε.val := by rw [hfr _ (by decide), f0Eps]
  have fPL : s.env r4PL = k * (ℓ + 1) := by rw [hfr _ (by decide), f0PL]
  /- 1. the header -/
  obtain ⟨s1, g1, h1p, h1x, h1s, h1o, h1T, h1D, h1f⟩ := p4Rd_good I hw hH s hj hpos
  have hb1 := g1.bdd hw hbd hp
  /- 2. the record -/
  have h1S2 : s1.stk qS2 = orsL (cL I e) ++ blkRows (cL I e) :: nEnt I e ::
      (coefSteps I e).length :: schRecsFrom I (j + 1) := by
    rw [h1s, hS2, schRecsFrom_cons I hj, schRec]; simp <;> rfl
  obtain ⟨s2, g2, h2s, h2BR, h2NE, h2NC, h2R2, h2p, h2o, h2f⟩ := p4Rec_good
    (x := encodeSystem I) hw s1 (orsL (cL I e)) (schRecsFrom I (j + 1)) _ _ _ h1S2
    (by rw [h1f _ (by decide), fL, length_orsL]) (orsL_le _) (by rw [h1s, hOF])
    (by rw [h1s, hOB]) hb1.1 hb1.2 (by rw [length_orsL]; omega)
  have hb2 := (g1.seq g2).bdd hw hbd hp
  have e2 : ∀ r, r ∉ [rc1, rc2, rP, rT, r4Tn, r4D] → r ∉ [rT, rP, rc1, r4R2, r4BR, r4NE, r4NC] →
      s2.env r = s.env r := fun r h1 h2 => by rw [h2f r h2, h1f r h1]
  have e2s : ∀ q, q ≠ qS2 → q ≠ qOrsF → s2.stk q = s.stk q := fun q h1 h2 => by
    rw [h2s, Function.update_of_ne h2, Function.update_of_ne h1, h1s]
  /- 3. the section bases -/
  have e2SB : s2.env r4SB = sBase I j := by rw [e2 _ (by decide) (by decide), eSB]
  have e2D : s2.env r4D = (cL I e).length := by rw [h2f _ (by decide), h1D]
  have e2T : s2.env r4Tn = tnN (Matrix.isTern (sch I e)) := by rw [h2f _ (by decide), h1T]
  obtain ⟨s3, g3, h3H, h3K, h3Di, h3Su, h3Tr, h3SP, h3TP, h3s, h3p, h3o, h3f⟩ :=
    p4Bas_good (x := encodeSystem I) hw s2 e2SB e2D h2NE e2T hTn (by
      rw [← hsBe]; rw [hcolW] at hsec; nlinarith)
  have hb3 := (g1.seq (g2.seq g3)).bdd hw hbd hp
  set T := tnN (Matrix.isTern (sch I e)) with hT
  have hSu : sBase I j + (cL I e).length * (2 + 4 * T) + 4 * nEnt I e = sumBase I e := by
    rw [hsumB, hcolW, hsBe]
  have hTr : sBase I j + (cL I e).length * (2 + 4 * T) + 4 * nEnt I e + 2 * T * (cL I e).length =
      trackBase I e := by rw [hSu, htrkB, hsum]
  rw [hSu] at h3Su h3SP
  rw [hTr] at h3Tr h3TP
  have e3 : ∀ r, r ∉ bodyW → s3.env r = s.env r := fun r hr => by
    rw [h3f r (notMem_of_bodyW_bas r hr), e2 r (notMem_of_bodyW_rd r hr) (notMem_of_bodyW_rec r hr)]
  /- 4. section 1 -/
  set A1 := (cL I e).zipIdx.flatMap (a1C I e)
  set A2 := (cL I e).zipIdx.flatMap (a2C I e)
  set E1 := (cL I e).zipIdx.flatMap fun q => colE1 I ε e q.1 q.2
  set E2 := (cL I e).flatMap (colE2 I ε e)
  set codes := (cL I e).flatMap fun c => codesL I e c ++ [0]
  have hAe : (ansE I e).flatten = A1 ++ A2 := ansE_flatten I e
  have h3A : s3.stk qAns = A1 ++ (A2 ++ ansFr I (j + 1)) := by
    rw [h3s, e2s _ (by decide) (by decide), hAns, ansFr_cons I hj]
    show (ansE I e).flatten ++ _ = _
    rw [hAe, List.append_assoc]
  have hF1 : L1Fix I w (encodeSystem I) ε e
      (encodeNats (permsL I e) ++ encodeNats (schsSuf I (j + 1))) s3 := by
    refine ⟨by rw [h3p, h2p]; exact h1x, by rw [e3 _ (by decide), fL],
      by rw [e3 _ (by decide), fk], by rw [h3f _ (by decide), h2BR],
      by rw [h3f _ (by decide), e2T], by rw [e3 _ (by decide), fLB],
      by rw [e3 _ (by decide), fEps], by rw [h3f _ (by decide), e2D], ?_, ?_, hb3.2⟩
    · rw [h3s, h2s, Function.update_self]
    · rw [h3s, e2s _ (by decide) (by decide), hOB]
  have e3M : s3.env r4M = (edUp I ε j).length := by
    rw [h3f _ (by decide), e2 _ (by decide) (by decide), eM]
  have hB1 : L1Bnd I w e s3 := ⟨hW16, hkl, hcl, hab, by rw [e3M]; omega⟩
  obtain ⟨s4, g4, h4EM, h4Rk, h4A, h4A2, h4so, h4K, h4Di, h4H, h4SP, h4TP, h4V, hb4', h4p, h4o,
      h4f⟩ := p4S1_good I hw hk hE ε e (A2 ++ ansFr I (j + 1)) _ s3 hF1 hB1 (by
      rw [show ((cL I e).zipIdx.flatMap fun q => colE1 I ε e q.1 q.2) = E1 from rfl]; omega) h3K h3Di
    (by rw [h3H, hsBe]) h3SP h3TP (hb3.1.1 _) hb3.1 h3A
  have hb4 := (g1.seq (g2.seq (g3.seq g4))).bdd hw hbd hp
  have e4 : ∀ r, r ∉ bodyW → s4.env r = s.env r := fun r hr => by
    rw [h4f r (notMem_of_bodyW_c1 r hr), e3 r hr]
  have h3Rk : s3.stk qRk = [] := by rw [h3s, e2s _ (by decide) (by decide), hRk]
  have h4Rk' : s4.stk qRk = codes.reverse := by rw [h4Rk, h3Rk, List.append_nil]
  /- 5. between the sections -/
  have hx4 : (encodeSystem I).drop s4.pos =
      encodeNats (permsL I e) ++ encodeNats (schsSuf I (j + 1)) := by
    rw [h4p, drop_add, hF1.1, List.drop_left]
  obtain ⟨s5, g5, h5s, h5p, h5o, h5P, h5SP, h5TP, h5K, h5f⟩ := p4Mid_good (x := encodeSystem I)
    hw s4 (s4.stk qRk) (orsL (cL I e)) (permsL I e) (encodeNats (schsSuf I (j + 1))) rfl
    (by rw [h4so _ (by decide) (by decide) (by decide) (by decide), h3s, h2s,
      Function.update_self])
    (by rw [e4 _ (by decide), fL, length_orsL])
    (by rw [h4f _ (by decide), h3f _ (by decide), h2BR])
    (by rw [h4f _ (by decide), h3f _ (by decide), h2NE])
    (by rw [h4f _ (by decide), h3f _ (by decide), h2NC])
    (by rw [h4f _ (by decide), h3f _ (by decide), e2T]) hTn
    (by rw [e4 _ (by decide), fPL]) h4TP
    (by rw [h4f _ (by decide), h3Su]) (by rw [h4f _ (by decide), h3Tr]) hx4
    (by rw [length_permsL, arity_eq]) hb4.1 hb4.2 (by rw [length_orsL]; omega)
  have hb5 := (g1.seq (g2.seq (g3.seq (g4.seq g5)))).bdd hw hbd hp
  have e5 : ∀ r, r ∉ bodyW → s5.env r = s.env r := fun r hr => by
    rw [h5f r (notMem_of_bodyW_mid r hr), e4 r hr]
  have e5s : ∀ q, q ≠ qRk → q ≠ qRkF → q ≠ qOrsF → q ≠ qSch → s5.stk q = s4.stk q :=
    fun q h1 h2 h3 h4 => by
      rw [h5s, Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne h2,
        Function.update_of_ne h1]
  /- 6. section 2 -/
  have hF2 : L2Fix I (encodeSystem I) ε e s5 := by
    refine ⟨by rw [e5 _ (by decide), fk],
      by rw [h5f _ (by decide), h4f _ (by decide), h3f _ (by decide), e2T],
      by rw [e5 _ (by decide), fLB], by rw [e5 _ (by decide), fEps],
      by rw [h5f _ (by decide), h4f _ (by decide), h3f _ (by decide), e2D],
      by rw [h5f _ (by decide), h4f _ (by decide), h3f _ (by decide), h2R2, rowsR_len],
      by rw [h5P, hcofB], hb5.2⟩
  have e5M : s5.env r4M = (edUp I ε j).length + E1.length := by
    rw [h5f _ (by decide), h4EM.2, e3M]
  have hnE6 : 6 * nEnt I e ≤ locBase I := by omega
  have hE12 : E1.length + E2.length = (schE I ε e).length := by rw [hE2l]
  have hB2 : L2Bnd I w ε e s5 := ⟨hW16, hkl, hcl, hab, by
    rw [e5M]
    have : (edUp I ε j).length + E1.length + E2.length ≤ 3 * (ordL I).length := by omega
    have h2e : ((cL I e).flatMap (colE2 I ε e)).length = E2.length := rfl
    omega⟩
  have h5R : s5.stk qRkF = codes ++ [] := by
    rw [h5s, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self, h4Rk', h4so _ (by decide) (by decide) (by decide) (by decide), h3s,
      e2s _ (by decide) (by decide), hRkF, List.reverse_reverse]
  have h5B : s5.stk qOrsB = [] := by
    rw [e5s _ (by decide) (by decide) (by decide) (by decide),
      h4so _ (by decide) (by decide) (by decide) (by decide), h3s,
      e2s _ (by decide) (by decide), hOB]
  have h5A : s5.stk qAns = A2 ++ ansFr I (j + 1) := by
    rw [e5s _ (by decide) (by decide) (by decide) (by decide), h4A]
  obtain ⟨s6, g6, h6EE, h6R, h6B, h6A, h6A2, h6so, h6K, h6H, h6TP, h6SP, hb6', h6f⟩ :=
    p4S2_good I hw hk ε e (ansFr I (j + 1)) [] s5 hF2 hB2 h5R h5B h5A h5K
    (by rw [h5f _ (by decide), h4H]; rfl) h5TP h5SP hb5.1
  have hb6 := (g1.seq (g2.seq (g3.seq (g4.seq (g5.seq g6))))).bdd hw hbd hp
  /- 7. the end -/
  have h6J : s6.env rJ = j := by
    rw [h6f _ (by decide), h5f _ (by decide), h4f _ (by decide), h3f _ (by decide),
      e2 _ (by decide) (by decide), eJ]
  have hcoef : coefBase I e + 2 * (coefSteps I e).length = sBase I j + schSize I e := by
    rw [hcofB, htrkB, hhub, hsz, hsBe]; ring
  obtain ⟨s7, g7, h7SB, h7J, h7s, h7p, h7o, h7f⟩ := p4End_good (x := encodeSystem I) (w := w) s6
    (P := coefBase I e) (nC := (coefSteps I e).length) (j := j)
    (by rw [h6f _ (by decide), h5P, hcofB])
    (by rw [h6f _ (by decide), h5f _ (by decide), h4f _ (by decide), h3f _ (by decide), h2NC])
    h6J (by rw [hcoef]; omega) (by have := E_le I; omega)
  have hb7 := (g1.seq (g2.seq (g3.seq (g4.seq (g5.seq (g6.seq g7)))))).bdd hw hbd hp
  have e6s : ∀ q, q ≠ q4E → q ≠ qRkF → q ≠ qOrsB → q ≠ qAns → q ≠ qA2 → s7.stk q = s5.stk q :=
    fun q h1 h2 h3 h4 h5 => by rw [h7s, h6so q h1 h2 h3 h4 h5]
  have hsch : s.stk qSch = s4.stk qSch := by
    rw [h4so _ (by decide) (by decide) (by decide) (by decide), h3s,
      e2s _ (by decide) (by decide)]
  refine ⟨s7, (g1.seq (g2.seq (g3.seq (g4.seq (g5.seq (g6.seq g7)))))).mono ?_,
    by omega, h7J, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hb7.1, ?_⟩
  · -- the cost
    have hcc : condCost w (Ex.lt (rv r4K) (rv r4D) : Ex CR) = 3 * Ex.nodeCost w + 1 := by
      simp only [condCost, Ex.size]
    rw [hcc, h4Rk', List.length_reverse, length_orsL, schD_len]
    have hrk : codes.length ≤ nEnt I e := codes_len_le I hk e
    have hsz2 := schSize_ge I e
    have hpe := permsL_ge I hk e
    have key := body_arith (N := Ex.nodeCost w) (U := unitCost w) (hdr := hdrL I e)
      (co := (encodeNats ((cL I e).flatMap cdesc)).length)
      (pe := (encodeNats (permsL I e)).length) (nE := nEnt I e) (cl := (cL I e).length)
      (ℓ := ℓ) (sz := schSize I e) (rk := codes.length) hU hU' hpe hrk hsz2
    simp only [← he]
    linarith only [key]
  · rw [h7p, h6EE.2.2.1, h5p, h4p, h3p, h2p, h1p, hpos, schAt_succ I hj, schD_len]; ring
  · rw [h7SB, hcoef, sBase_succ I hj]
  · rw [e6s _ (by decide) (by decide) (by decide) (by decide) (by decide),
      e5s _ (by decide) (by decide) (by decide) (by decide),
      h4so _ (by decide) (by decide) (by decide) (by decide), h3s, h2s,
      Function.update_of_ne (by decide), Function.update_self]
  · rw [e6s _ (by decide) (by decide) (by decide) (by decide) (by decide), h5s,
      Function.update_self, ← hsch, hSch, schRecsUpTo_succ I hj, List.reverse_append, schRec]
    simp; exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [h7s, h6A]
  · rw [h7s, h6A2, e5s _ (by decide) (by decide) (by decide) (by decide), h4A2, h3s,
      e2s _ (by decide) (by decide), hA2, ansUp_succ I hj]
    show _ = (ansUp I j ++ (ansE I e).flatten).reverse
    rw [hAe]; simp <;> rfl
  · rw [h7s, h6EE.1, e5s _ (by decide) (by decide) (by decide) (by decide), h4EM.1, h3s,
      e2s _ (by decide) (by decide), h4E, edUp_succ I ε hj]
    show _ = pairsRev (edUp I ε j ++ schE I ε e) ++ _
    rw [hE2, pairsRev_append, pairsRev_append]; simp <;> rfl
  · rw [e6s _ (by decide) (by decide) (by decide) (by decide) (by decide), h5s,
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_self]
  · rw [h7s, h6R]
  · rw [e6s _ (by decide) (by decide) (by decide) (by decide) (by decide), h5s,
      Function.update_of_ne (by decide), Function.update_self]
  · rw [h7s, h6B]
  · intro q hq
    simp only [bodyQ, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ := hq
    rw [e6s q q5 q7 q9 q3 q4, e5s q q6 q7 q8 q2, h4so q q5 q6 q3 q4, h3s, e2s q q1 q8, hoth q
      (by simp [bodyQ, q1, q2, q3, q4, q5, q6, q7, q8, q9])]
  · rw [h7f _ (by decide) (by decide), h6EE.2.1, e5M, edUp_succ I ε hj, List.length_append,
      hE2l]
    ring
  · rw [h7o, h6EE.2.2.2, h5o, h4o, h3o, h2o, h1o, hout]
  · intro r hr
    obtain ⟨n1, n2⟩ := notMem_of_bodyW_end r hr
    rw [h7f r n1 n2, h6f r (notMem_of_bodyW_c2 r hr), e5 r hr, hfr r hr]

end Lax119563Proofs.Compiler
