import Lax119563Proofs.Compiler.P4SchC1b

/-!
# Pass `P4`, schema part: one column of section 1 (`p4C1_good`)

Reads the column `i, b₀ … b_{ℓ-1}` from the input, pushes its rank codes (`codesC`, then the
terminator `0`) on `qRk`, pops its answers (ternary: `U, V, W`; binary: `V`) and pushes the
junction and link edges (`col1E`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-- The edge stack and count of `st'` are those of `st` with `Es` pushed. -/
def EM (st st' : NSt CR CQ) (Es : List (ℕ × ℕ)) : Prop :=
  st'.stk q4E = pairsRev Es ++ st.stk q4E ∧ st'.env r4M = st.env r4M + Es.length

lemma EM.trans {st s₁ s₂ : NSt CR CQ} {E₁ E₂ : List (ℕ × ℕ)} (h₁ : EM st s₁ E₁)
    (h₂ : EM s₁ s₂ E₂) : EM st s₂ (E₁ ++ E₂) := by
  obtain ⟨a1, b1⟩ := h₁
  obtain ⟨a2, b2⟩ := h₂
  refine ⟨?_, ?_⟩
  · rw [a2, a1, pairsRev_append]; simp
  · rw [b2, b1, List.length_append]; ring

lemma EE.em {st st' : NSt CR CQ} {Es : List (ℕ × ℕ)} (h : EE st st' Es) : EM st st' Es :=
  ⟨h.1, h.2.1⟩

lemma EM.of_frame {st st' : NSt CR CQ} (hs : st'.stk q4E = st.stk q4E)
    (hm : st'.env r4M = st.env r4M) : EM st st' [] := ⟨by simp [pairsRev, hs], by simp [hm]⟩

/-- One column of section 1. -/
def p4C1 : CStm CR CQ :=
  .seq p4Hd (.seq p4Blk (.seq p4Bits (.seq p4LT (.seq c1Jun (.seq c1Lnk p4Adv1)))))

/-- The rank codes of a column. -/
def codesC (k BR d i : ℕ) (os bs : List ℕ) : List ℕ :=
  blkCodes k BR d i ++ (chkRk os bs BR).map rcode

/-- The junction and link edges of a column (numbers). -/
def col1E (T H SP LT LB eps : ℕ) (AU AV AW : List ℕ) : List (ℕ × ℕ) :=
  (if T = 1 then junL H SP LB (aOff AU) (ansMode eps AU) (aOff AV) (ansMode eps AV) else []) ++
    lnkL (H + 4 * T) LT LB (aOff AW) (ansMode eps AW)

/-- The answer words consumed by a column in section 1. -/
def ans1 (T : ℕ) (AU AV AW : List ℕ) : List ℕ := (if T = 1 then AU ++ AV else []) ++ AW

/-- Registers written by a column of section 1. -/
def c1W : List (Fin CR) :=
  [rc1, rc2, rc3, rc4, rc5, rc6, rc7, rc8, rP, rT, r4Dist, r4Prev, r4TP, r4H, r4SP, r4K, r4F,
    r4V, r4M]

set_option maxHeartbeats 16000000 in
/-- **One column of section 1.** -/
lemma p4C1_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s : NSt CR CQ)
    {i k BR K D P H SP TP T LB : ℕ} (bs os : List ℕ) (rest : List Bool) (AU AV AW ansRest : List ℕ)
    (hx : x.drop s.pos = encodeNats (i :: bs) ++ rest) (hi : (Nat.bits i).length < w)
    (hbs : ∀ b ∈ bs, b ≤ 1) (hos : ∀ o ∈ os, o ≤ 1) (hl : os.length = bs.length)
    (eL : s.env rL = bs.length) (hF : s.stk qOrsF = os) (hB : s.stk qOrsB = [])
    (hA : s.stk qAns = ans1 T AU AV AW ++ ansRest)
    (hU : T = 1 → AnsOK w AU) (hV : T = 1 → AnsOK w AV) (hW : AnsOK w AW)
    (ek : s.env rKk = k) (eBR : s.env r4BR = BR) (eK : s.env r4K = K) (eD : s.env r4Dist = D)
    (eP : s.env r4Prev = P) (eH : s.env r4H = H) (eSP : s.env r4SP = SP) (eTP : s.env r4TP = TP)
    (eT : s.env r4Tn = T) (hT : T ≤ 1) (eLB : s.env rLB = LB) (hE : s.env r4Eps ≤ 1)
    (hV4 : s.env r4V < 2 ^ w) (hbd : s.Bdd w) (hpos : s.pos ≤ x.length)
    (hk : 2 ≤ k) (hik : i < k)
    (B : ℕ) (hBw : B < 2 ^ w)
    (hb1 : 2 * k + 2 ≤ B) (hb2 : 2 * (D + 1) + 2 ≤ B) (hb3 : BR + 1 ≤ B) (hb4 : K + 2 ≤ B)
    (hb5 : P ≤ B) (hb6 : H + 8 ≤ B) (hb7 : SP + 4 ≤ B)
    (hb8 : TP + 2 * ((k + 1) * (codesC k BR (dist1 K D P i) i os bs).length) + 2 ≤ B)
    (hb9 : 2 * (BR + bs.length) + k + 2 ≤ B)
    (hbU : T = 1 → LB + aOff AU + 2 ≤ B) (hbV : T = 1 → LB + aOff AV + 2 ≤ B)
    (hbW : LB + aOff AW + 2 ≤ B) (hm : s.env r4M + 16 ≤ B) :
    ∃ s', Good x w p4C1 s s' (200 * ((encodeNats (i :: bs)).length + bs.length +
        (k + 2) * ((codesC k BR (dist1 K D P i) i os bs).length + 1) + 10) * Ex.nodeCost w) ∧
      EM s s' (col1E T H SP (TP + 2 * ((k + 1) * (codesC k BR (dist1 K D P i) i os bs).length - 1))
        LB (s.env r4Eps) AU AV AW) ∧
      s'.stk qRk = (codesC k BR (dist1 K D P i) i os bs ++ [0]).reverse ++ s.stk qRk ∧
      s'.stk qAns = ansRest ∧ s'.stk qA2 = (ans1 T AU AV AW).reverse ++ s.stk qA2 ∧
      (∀ q, q ≠ q4E → q ≠ qRk → q ≠ qAns → q ≠ qA2 → s'.stk q = s.stk q) ∧
      s'.env r4Dist = dist1 K D P i ∧ s'.env r4Prev = i ∧
      s'.env r4TP = TP + 2 * ((k + 1) * (codesC k BR (dist1 K D P i) i os bs).length) ∧
      s'.env r4H = H + 2 + 4 * T ∧ s'.env r4SP = SP + 2 ∧ s'.env r4K = K + 1 ∧
      s'.env r4V < 2 ^ w ∧ s'.Bdd w ∧ s'.pos = s.pos + (encodeNats (i :: bs)).length ∧
      s'.out = s.out ∧ ∀ r, r ∉ c1W → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  set d := dist1 K D P i with hd
  have hdD : d ≤ D + 1 := by simp only [hd, dist1]; split_ifs <;> omega
  -- the block
  have hx1 : x.drop s.pos = encodeNat i ++ (encodeNats bs ++ rest) := by
    rw [hx, encNats_cons, List.append_assoc]
  obtain ⟨s1, g1, e11, e1D, e1P, p1, k1, o1, f1⟩ := p4Hd_good (x := x) hw s (rest :=
    encodeNats bs ++ rest) hx1 hi eK eD eP (by omega) (by omega) (by omega)
  have q1 : ∀ r, r ∉ [rc1, rP, rT, r4Dist, r4Prev] → s1.env r = s.env r := f1
  have b1 := g1.bdd hw hbd hpos
  -- block ranks
  obtain ⟨s2, g2, k2, e22, p2, o2, f2⟩ := p4Blk_good (x := x) hw s1 (k := k) (BR := BR) (d := d)
    (i := i) e11 (by rw [q1 _ (by decide), ek]) (by rw [q1 _ (by decide), eBR]) e1D (by omega)
    (by omega) (by omega) (by omega) (by omega)
  have b2 := g2.bdd hw b1.1 b1.2
  have hblk : (blkCodes k BR d i).length ≤ k := by
    unfold blkCodes; split_ifs <;> simp <;> omega
  have hblk1 := length_blkCodes_pos k BR d i hk
  -- bits
  have hx2 : x.drop s2.pos = encodeNats bs ++ rest := by
    rw [p2, p1, drop_add, hx1, List.drop_left]
  obtain ⟨s3, g3, k3, e32, p3, o3, f3⟩ := p4Bits_good (x := x) hw os bs s2 (BR := BR)
    (n0 := (blkCodes k BR d i).length) hl hbs hos rest hx2
    (by rw [f2 _ (by decide) (by decide), q1 _ (by decide), eBR]) e22
    (by rw [f2 _ (by decide) (by decide), q1 _ (by decide), eL])
    (by rw [k2, Function.update_of_ne (by decide), k1, hF])
    (by rw [k2, Function.update_of_ne (by decide), k1, hB]) b2.1 b2.2 (by omega)
  have b3 := g3.bdd hw b2.1 b2.2
  set n := (codesC k BR d i os bs).length with hn
  have hn' : n = (blkCodes k BR d i).length + (chkRk os bs BR).length := by
    simp [hn, codesC]
  have hcl := length_chkRk_le os bs BR
  have hnk : n ≤ k + bs.length := by omega
  -- last track
  have q3 : ∀ r, r ∉ [rc1, rc2, rc3, rc4, rc5, rP, rT, r4Dist, r4Prev] → s3.env r = s.env r := by
    intro r hr
    rw [f3 r (by simp [bitW] at hr ⊢; tauto), f2 r (by simp at hr; tauto) (by simp at hr; tauto)]
    exact q1 r (by simp at hr ⊢; tauto)
  have hkn : (k + 1) * n ≤ (k + 1) * (k + bs.length) := Nat.mul_le_mul_left _ hnk
  obtain ⟨s4, g4, e41, e4TP, k4, p4, o4, f4⟩ := p4LT_good (x := x) hw s3 (k := k) (n := n)
    (TP := TP) (by rw [e32, hn']) (by rw [q3 _ (by decide), ek]) (by rw [q3 _ (by decide), eTP])
    (by omega) (by omega)
  have b4 := g4.bdd hw b3.1 b3.2
  have q4 : ∀ r, r ∉ [rc1, rc2, rc3, rc4, rc5, rP, rT, r4Dist, r4Prev, r4TP] →
      s4.env r = s.env r := by
    intro r hr
    rw [f4 r (by simp at hr ⊢; tauto)]
    exact q3 r (by simp at hr ⊢; tauto)
  -- junction
  have hA4 : s4.stk qAns = (if T = 1 then AU ++ AV else []) ++ (AW ++ ansRest) := by
    rw [k4, k3, Function.update_of_ne (by decide), k2, Function.update_of_ne (by decide), k1, hA,
      ans1, List.append_assoc]
  obtain ⟨s5, g5, ee5, k5A, k5A2, k5o, v5, f5⟩ := c1Jun_good (x := x) hw s4 (T := T) (H := H)
    (SP := SP) (LB := LB) AU AV (AW ++ ansRest) (by rw [q4 _ (by decide), eT]) hT
    (by rw [q4 _ (by decide), eH]) (by rw [q4 _ (by decide), eSP]) (by rw [q4 _ (by decide), eLB])
    (by rw [q4 _ (by decide)]; exact hE) hA4 hU hV (by omega) (by omega)
    (fun h => by have := hbU h; omega) (fun h => by have := hbV h; omega)
    (by rw [f4 _ (by decide), f3 _ (by decide), f2 _ (by decide) (by decide),
      q1 _ (by decide)]; exact hV4)
    (by rw [q4 _ (by decide)]; omega)
  have q5 : ∀ r, r ∉ [rc1, rc2, rc3, rc4, rc5, rc6, rc7, rc8, rP, rT, r4Dist, r4Prev, r4TP,
      r4F, r4V, r4M] → s5.env r = s.env r := by
    intro r hr
    rw [f5 r (by simp at hr ⊢; tauto)]
    exact q4 r (by simp at hr ⊢; tauto)
  have e5E : s5.env r4Eps = s.env r4Eps := q5 _ (by decide)
  have e4E : s4.env r4Eps = s.env r4Eps := q4 _ (by decide)
  have e5M : s5.env r4M ≤ s.env r4M + 12 := by
    rw [ee5.2.1, q4 _ (by decide)]
    split_ifs
    · have := length_junL H SP LB (aOff AU) (ansMode (s4.env r4Eps) AU) (aOff AV)
        (ansMode (s4.env r4Eps) AV)
      omega
    · simp
  have e51 : s5.env rc1 = TP + 2 * ((k + 1) * n - 1) := by rw [f5 _ (by decide), e41]
  obtain ⟨s6, g6, ee6, k6A, k6A2, k6o, v6, f6⟩ := c1Lnk_good (x := x) hw s5 (T := T) (H := H)
    (LT := TP + 2 * ((k + 1) * n - 1)) (LB := LB) AW ansRest
    (by rw [q5 _ (by decide), eT]) (by rw [q5 _ (by decide), eH]) e51
    (by rw [q5 _ (by decide), eLB]) (by rw [e5E]; exact hE) k5A hW (by omega) (by omega)
    (by omega) v5 (by omega)
  have q6 : ∀ r, r ∉ [rc1, rc2, rc3, rc4, rc5, rc6, rc7, rc8, rP, rT, r4Dist, r4Prev, r4TP,
      r4F, r4V, r4M] → s6.env r = s.env r := by
    intro r hr
    rw [f6 r (by simp at hr ⊢; tauto)]
    exact q5 r hr
  have g7 := p4Adv1_good (x := x) (w := w) s6 (H := H) (T := T) (SP := SP) (K := K)
    (by rw [q6 _ (by decide), eH]) (by rw [q6 _ (by decide), eT]) (by rw [q6 _ (by decide), eSP])
    (by rw [q6 _ (by decide), eK]) (by omega) (by omega) (by omega)
  set s7 := ((s6.set r4H (H + 2 + 4 * T)).set r4SP (SP + 2)).set r4K (K + 1)
  have b7 := (g4.seq (g5.seq (g6.seq g7))).bdd hw b3.1 b3.2
  have q76 : ∀ r, r ≠ r4H → r ≠ r4SP → r ≠ r4K → s7.env r = s6.env r := by
    intro r h1 h2 h3; simp [s7, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3]
  have e6D : s6.env r4Dist = d := by
    rw [f6 _ (by decide), f5 _ (by decide), f4 _ (by decide), f3 _ (by decide),
      f2 _ (by decide) (by decide), e1D]
  refine ⟨s7, (g1.seq (g2.seq (g3.seq (g4.seq (g5.seq (g6.seq g7)))))).mono ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, b7.1, ?_, ?_, ?_⟩
  · -- cost
    have hl1 : (encodeNats (i :: bs)).length = (encodeNat i).length + (encodeNats bs).length := by
      rw [encNats_cons, List.length_append]
    have hkn2 : (k + 2) * (n + 1) ≥ (k + 2) := by nlinarith
    rw [hl1]
    nlinarith
  · -- edges
    have e04 : EM s s4 [] := EM.of_frame (by rw [k4, k3, k2, k1]; simp +decide)
      (by rw [q4 _ (by decide)])
    have e67 : EM s6 s7 [] := EM.of_frame (by simp [s7]) (q76 _ (by decide) (by decide) (by decide))
    have := ((e04.trans ee5.em).trans ee6.em).trans e67
    rw [e4E, e5E] at this
    simpa [col1E] using this
  · simp only [s7, NSt.set_stk]
    rw [k6o _ (by decide) (by decide) (by decide), k5o _ (by decide) (by decide) (by decide), k4,
      k3, k2, k1]
    simp [codesC]
  · simp only [s7, NSt.set_stk]; exact k6A
  · simp only [s7, NSt.set_stk]
    rw [k6A2, k5A2, k4, k3, Function.update_of_ne (by decide), k2, Function.update_of_ne (by decide),
      k1, ans1]
    split_ifs <;> simp
  · intro q h1 h2 h3 h4
    simp only [s7, NSt.set_stk]
    rw [k6o q h1 h3 h4, k5o q h1 h3 h4, k4, k3, Function.update_of_ne h2, k2,
      Function.update_of_ne h2, k1]
  · rw [q76 _ (by decide) (by decide) (by decide)]; exact e6D
  · rw [q76 _ (by decide) (by decide) (by decide), f6 _ (by decide), f5 _ (by decide),
      f4 _ (by decide), f3 _ (by decide), f2 _ (by decide) (by decide), e1P]
  · rw [q76 _ (by decide) (by decide) (by decide), f6 _ (by decide), f5 _ (by decide), e4TP]
  · simp +decide [s7]
  · simp +decide [s7]
  · simp +decide [s7]
  · rw [q76 _ (by decide) (by decide) (by decide)]; exact v6
  · simp only [s7]
    show s6.pos = _
    rw [ee6.2.2.1, ee5.2.2.1, p4, p3, p2, p1, encNats_cons, List.length_append]; ring
  · simp only [s7]
    show s6.out = _
    rw [ee6.2.2.2, ee5.2.2.2, o4, o3, o2, o1]
  · intro r hr
    simp only [c1W, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [q76 r (by tauto) (by tauto) (by tauto)]
    exact q6 r (by simp; tauto)

end Lax119563Proofs.Compiler
