import Lax119563Proofs.Compiler.P4SchSpec
import Lax119563Proofs.Compiler.P4Main

/-!
# Pass `P4`, schema part: the schema loop and **`p4Sch_spec`**
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-! ## The schema loop -/

lemma sLp_arith {N φ h L E c : ℕ} (hφ : φ ≤ h + L) (hE : E ≤ h) (hc : c ≤ 4 * N) :
    5000 * N * φ + E * (5000 * N + c) + c ≤
      5000 * N * (h + L) + h * (5004 * N) + 4 * N := by
  have h1 : 5000 * N * φ ≤ 5000 * N * (h + L) := Nat.mul_le_mul_left _ hφ
  have h2 : E * (5000 * N + c) ≤ h * (5004 * N) := Nat.mul_le_mul hE (by omega)
  omega

set_option maxHeartbeats 4000000 in
/-- **The schema loop.** -/
lemma p4SLp_good {w : ℕ} (hw : 2 ≤ w) (ε : ZMod 2) (s0 : NSt CR CQ) (hF : BFix I w ε s0)
    (hE0 : s0.env rE = I.schemas.length) (hI0 : BInv I w ε s0 0 s0) :
    ∃ s', Good (encodeSystem I) w p4SLp s0 s'
        (5000 * Ex.nodeCost w * (H I + locBase I) + H I * (5004 * Ex.nodeCost w) +
          4 * Ex.nodeCost w) ∧
      BInv I w ε s0 I.schemas.length s' := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hEH := E_le I
  have hW16 := hF.2.2.2.1
  have hLB := locBase_le_length I
  obtain ⟨s', g, ⟨j, hI⟩, hc⟩ := Good.loop_var (x := encodeSystem I) (w := w)
    (e := .lt (rv rJ) (rv rE)) (body := p4Body) (fun s => ∃ j, BInv I w ε s0 j s)
    (fun s => I.schemas.length - s.env rJ) (fun s => (H I - s.pos) + (locBase I - s.env r4SB))
    (5000 * Ex.nodeCost w) (5000 * Ex.nodeCost w) (by
      rintro s ⟨j, hI⟩
      obtain ⟨hjE, eJ, hpos, eSB, -, -, -, -, -, -, -, -, -, -, -, -, -, hfr⟩ := id hI
      have eE : s.env rE = I.schemas.length := by rw [hfr _ (by decide), hE0]
      refine ⟨by simp only [Ex.Fits, rv, eJ, eE]; omega, fun hc => ?_⟩
      have hj : j < I.schemas.length := by
        by_contra h; apply hc; simp only [Ex.eval, rv, eJ, eE]; rw [if_neg h]
      obtain ⟨s', g, hI'⟩ := p4Body_good I hw ε s0 hF hj s hI
      obtain ⟨-, eJ', hpos', eSB', -⟩ := id hI'
      have h1 := schAt_succ I hj
      have h2 := schAt_le I (j + 1)
      have h3 := sBase_succ I hj
      have h4 := sBase_le I (j + 1)
      refine ⟨s', g.mono ?_, ⟨j + 1, hI'⟩, by rw [eJ', eJ]; omega, by
        rw [hpos', hpos, eSB', eSB]; omega⟩
      rw [hpos', hpos, eSB', eSB]
      have hd : H I - schAt I j + (locBase I - sBase I j) -
          (H I - schAt I (j + 1) + (locBase I - sBase I (j + 1))) =
          (encodeNats (schD I ⟨j, hj⟩)).length + schSize I ⟨j, hj⟩ := by omega
      rw [hd]; exact le_of_eq (by ring)) s0 ⟨0, hI0⟩
  obtain ⟨hjE, eJ, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hfr⟩ := id hI
  have eE : s'.env rE = I.schemas.length := by rw [hfr _ (by decide), hE0]
  have hjE' : j = I.schemas.length := by
    simp only [Ex.eval, rv, eJ, eE] at hc; split_ifs at hc with h <;> omega
  subst hjE'
  refine ⟨s', g.mono ?_, hI⟩
  have hc : condCost w (Ex.lt (rv rJ) (rv rE) : Ex CR) ≤ 4 * Ex.nodeCost w := by
    simp only [condCost, Ex.size, rv]; omega
  exact sLp_arith (by omega) (by omega) hc

/-! ## The answer words -/

lemma length_a1C (e : Fin I.schemas.length) (q : Coord k ℓ × ℕ) :
    (a1C I e q).length = 4 + 8 * tnN (Matrix.isTern (sch I e)) := by
  unfold a1C ans1 aU aV aW ansRec tnN
  cases Matrix.isTern (sch I e) <;> simp

lemma length_a2C (e : Fin I.schemas.length) (q : Coord k ℓ × ℕ) :
    (a2C I e q).length = 4 - 4 * tnN (Matrix.isTern (sch I e)) := by
  unfold a2C aU ansRec tnN
  cases Matrix.isTern (sch I e) <;> simp

lemma ansE_len (e : Fin I.schemas.length) :
    ((ansE I e).flatten).length = 4 * (arity (sch I e) * (coordList (dom I e)).length) := by
  rw [ansE_flatten, List.length_append, List.length_flatMap, List.length_flatMap]
  simp only [length_a1C, length_a2C, List.map_const', List.sum_replicate, List.length_zipIdx,
    smul_eq_mul]
  unfold arity tnN
  cases Matrix.isTern (sch I e) <;> simp <;> ring

lemma ansAll_len (hℓ : 1 ≤ ℓ) : (ansAll I).flatten.length ≤ 6 * H I := by
  have h1 := ansBase_le I I.schemas.length
  rw [← ansUp_all, ansUp, List.length_flatMap]
  have h2 : (((List.finRange I.schemas.length).take I.schemas.length).map
      fun e => ((ansE I e).flatten).length).sum = 4 * ansBase I I.schemas.length := by
    rw [ansBase, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro e _
    rw [ansE_len]
  rw [h2]
  have h3 : ansBase I I.schemas.length * 2 ≤ ansBase I I.schemas.length * (ℓ + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-! ## The specification -/

lemma spec_arith {N h L S a : ℕ} (hL : L ≤ 16 * S) (ha : a ≤ 6 * h) :
    1000 * (h + 1) * N + (5000 * N * (h + L) + h * (5004 * N) + 4 * N + (a + 1) * (10 * N)) ≤
      400000 * (h + S + 1) * N := by
  have h1 : N * L ≤ N * (16 * S) := Nat.mul_le_mul_left _ hL
  have h2 : a * N ≤ 6 * h * N := Nat.mul_le_mul_right _ ha
  nlinarith

lemma keep_notMem : ∀ r ∈ p4Keep, r ∉ bodyW ∧ r ∉ preW ∧ r ≠ rT ∧ r ≠ rP := by decide

set_option maxHeartbeats 8000000 in
/-- **The schema edge part of `P4` meets its interface.** -/
theorem p4Sch_spec (hk : 3 ≤ k) (hℓ : 1 ≤ ℓ) :
    SchSpec I (wordOf (H I) (sizeParameter I)) p4Sch
      (400000 * (H I + sizeParameter I + 1) * Ex.nodeCost (wordOf (H I) (sizeParameter I))) := by
  intro ε hε st hst
  obtain ⟨hne, hbd, hpos, hEps, hM, hTriv, hW, hL, hL1, hE, hKk, hKL, hLB, hAns, hSch, hemp⟩ :=
    hst
  have hw : 2 ≤ wordOf (H I) (sizeParameter I) := two_le_wordOf _ _
  have h2w := two_pow_word (H I) (sizeParameter I)
  have hordL := length_ordL_le I (by omega : 2 ≤ k)
  have hLBl := locBase_le_length I
  have hW16 : 16 * (H I + (ordL I).length + 1) ≤ 2 ^ wordOf (H I) (sizeParameter I) := by omega
  have hH : 4 * (H I + 1) ≤ 2 ^ wordOf (H I) (sizeParameter I) := by omega
  have hz : (st.stk qSch).length ≤ 4 * H I := by
    rw [hSch, List.length_reverse]; exact length_schRecsUpTo_le I (by omega)
  obtain ⟨s0, g0, h0p, h0o, h0s, h0J, h0SB, h0PL, h0f⟩ :=
    p4SchPre_good I hw hH (by omega) hne st hbd (by omega) hW hL1 hKk hz
  have hεv : ((ε : ℕ) : ZMod 2).val = ε := val_natCast_lt (by omega)
  have hS2 : st.stk qS2 = [] := hemp _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hp0 : st.pos ≤ (encodeSystem I).length := by rw [hpos]
  have hb0 := (g0.bdd hw hbd hp0).1
  have h0o' : ∀ q, q ≠ qSch → q ≠ qS2 → s0.stk q = st.stk q := fun q h1 h2 => by
    rw [h0s, Function.update_of_ne h2, Function.update_of_ne h1]
  have hF : BFix I (wordOf (H I) (sizeParameter I)) (ε : ZMod 2) s0 :=
    ⟨hne, by omega, hℓ, hW16, by rw [h0f _ (by decide), hL], by rw [h0f _ (by decide), hKk],
      by rw [h0f _ (by decide), hLB], by rw [h0f _ (by decide), hEps, hεv], h0PL,
      by rw [h0f _ (by decide), hM]⟩
  have hI0 : BInv I (wordOf (H I) (sizeParameter I)) (ε : ZMod 2) s0 0 s0 := by
    refine ⟨by omega, h0J, by rw [h0p, schAt_zero], by rw [h0SB]; simp [sBase], ?_, ?_, ?_, ?_,
      by simp [edUp, pairsRev], ?_, ?_, ?_, ?_, fun _ _ => rfl,
      by rw [h0f _ (by decide), hM]; simp [edUp], rfl, hb0, fun _ _ => rfl⟩
    · rw [h0s, Function.update_self, hSch, hS2, List.reverse_reverse, List.append_nil,
        schRecsFrom_zero]
    · rw [h0s, Function.update_of_ne (by decide), Function.update_self]; simp [schRecsUpTo]
    · rw [h0o' _ (by decide) (by decide), hAns, ansFr_zero]
    · rw [h0o' _ (by decide) (by decide),
        hemp _ (by decide) (by decide) (by decide) (by decide) (by decide)]
      simp [ansUp]
    · rw [h0o' _ (by decide) (by decide),
        hemp _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [h0o' _ (by decide) (by decide),
        hemp _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [h0o' _ (by decide) (by decide),
        hemp _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [h0o' _ (by decide) (by decide),
        hemp _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  obtain ⟨s1, g1, hI1⟩ := p4SLp_good I hw (ε : ZMod 2) s0 hF (by rw [h0f _ (by decide), hE]) hI0
  obtain ⟨-, -, h1p, -, h1S2, h1Sch, h1Ans, h1A2, h14E, h1Rk, h1RkF, h1OF, h1OB, h1oth, h1M, h1o,
    hb1, h1f⟩ := hI1
  obtain ⟨s2, g2, h2s, h2p, h2o, h2f⟩ := moveAllS_good (x := encodeSystem I) hw (q := qA2)
    (q' := qAns) (t := rT) (f := rP) (by decide) (by decide) s1 hb1
  refine ⟨s2, (g0.seq (g1.seq g2)).mono ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [h1A2, List.length_reverse, ansUp_all]
    have := spec_arith (N := Ex.nodeCost (wordOf (H I) (sizeParameter I))) (h := H I)
      (L := locBase I) (S := sizeParameter I) (a := (ansAll I).flatten.length)
      (locBase_le I (by omega)) (ansAll_len I hℓ)
    linarith only [this]
  · rw [h2s]
    funext q
    by_cases hq1 : q = qAns
    · subst hq1
      rw [Function.update_self, Function.update_of_ne (by decide), h1A2, h1Ans, ansUp_all,
        ansFr_all, hAns]; simp
    rw [Function.update_of_ne hq1]
    by_cases hq2 : q = qA2
    · subst hq2
      rw [Function.update_self, Function.update_of_ne (by decide),
        hemp _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    rw [Function.update_of_ne hq2]
    by_cases hq3 : q = q4E
    · subst hq3
      rw [Function.update_self, h14E, edUp_all, h0o' _ (by decide) (by decide)]
    rw [Function.update_of_ne hq3]
    by_cases hq4 : q = qS2
    · subst hq4; rw [h1S2, schRecsFrom_all, hS2]
    by_cases hq5 : q = qSch
    · subst hq5; rw [h1Sch, hSch]
    by_cases hq6 : q = qRk
    · subst hq6; rw [h1Rk, hemp _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    by_cases hq7 : q = qRkF
    · subst hq7; rw [h1RkF, hemp _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    by_cases hq8 : q = qOrsF
    · subst hq8; rw [h1OF, hemp _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    by_cases hq9 : q = qOrsB
    · subst hq9; rw [h1OB, hemp _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    rw [h1oth q (by simp [bodyQ, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9]), h0o' q hq5 hq4]
  · rw [h2f _ (by decide) (by decide), h1M, edUp_all, hM, zero_add]
  · rw [h2p, h1p, schAt_all, hpos]
  · rw [h2o, h1o, h0o]
  · intro r hr
    obtain ⟨n1, n2, n3, n4⟩ := keep_notMem r hr
    rw [h2f r n3 n4, h1f r n1, h0f r n2]

end Lax119563Proofs.Compiler
