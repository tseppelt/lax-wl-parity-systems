import Lax119563Proofs.Compiler.P4Round

/-!
# Pass `P4` (program): both rounds

`p4 SCH = r4Eps := 0; p4Round SCH; r4Eps := 1; p4Round SCH` (**`p4_good`**: output
`++ gDesc I 0 ++ gDesc I 1`), the start state from the chain (`p4Inv_of_chain`), the size
measure (`p4Z_le`) and the cost conversion for costs `K (H + S + 1) · nodeCost w`
(`cost_conv_lin`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- **Pass `P4`.** -/
def p4 (SCH : CStm CR CQ) : CStm CR CQ :=
  .seq (.set r4Eps (.const 0)) (.seq (p4Round SCH) (.seq (.set r4Eps (.const 1)) (p4Round SCH)))

lemma P4Inv_set {w : ℕ} (hw : 2 ≤ w) {st : NSt CR CQ} (hI : P4Inv I w st) {v : ℕ}
    (hv : v < 2 ^ w) : P4Inv I w (st.set r4Eps v) := by
  obtain ⟨hb, hp, a1, a2, a3, a4, a5, a6, a7, a8⟩ := hI
  refine ⟨⟨fun r => ?_, hb.2⟩, hp, ?_, ?_, ?_, ?_, ?_, a6, a7, a8⟩
  · by_cases h : r = r4Eps
    · subst h; simpa using hv
    · simpa [Function.update_of_ne h] using hb.1 r
  all_goals simp only [NSt.set_env, Function.update_of_ne (show rTriv ≠ r4Eps by decide),
    Function.update_of_ne (show rW ≠ r4Eps by decide), Function.update_of_ne (show rL ≠ r4Eps by decide),
    Function.update_of_ne (show rE ≠ r4Eps by decide), Function.update_of_ne (show rKk ≠ r4Eps by decide),
    Function.update_of_ne (show rKL ≠ r4Eps by decide), Function.update_of_ne (show rLB ≠ r4Eps by decide)]
  all_goals assumption

/-- **Pass `P4`**, given the schema edge part `SCH` (`SchSpec` with cost `C`). -/
theorem p4_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hℓ : ℓ ≤ H I)
    (hk : 1 ≤ k) (hT : (clsSizes I).sum + 8 < 2 ^ w) {SCH : CStm CR CQ} {C : ℕ}
    (hSpec : SchSpec I w SCH C) (st : NSt CR CQ) (hI : P4Inv I w st) :
    ∃ st', Good (encodeSystem I) w (p4 SCH) st st'
        (4000 * (H I + p4Z I 0 + 1) * Ex.nodeCost w + 4000 * (H I + p4Z I 1 + 1) *
          Ex.nodeCost w + 2 * C + 4 * Ex.nodeCost w) ∧
      st'.out = st.out ++ gDesc I 0 ++ gDesc I 1 ∧ P4Inv I w st' := by
  have hU := CStm.nodeCost_ge w
  have h2 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have r0 := Good.set (x := encodeSystem I) (w := w) (st := st) (r := r4Eps) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  have hI0 := P4Inv_set I hw hI (v := 0) (by omega)
  obtain ⟨s1, r1, h1o, hI1⟩ := p4Round_good I hw hH hℓ hk hT hSpec (ε := 0) (by omega) _ hI0
    (by simp (config := { decide := true }) [Ex.eval])
  have r2 := Good.set (x := encodeSystem I) (w := w) (st := s1) (r := r4Eps) (e := .const 1)
    (by simp only [Ex.Fits]; omega)
  have hI2 := P4Inv_set I hw hI1 (v := 1) h2
  obtain ⟨s3, r3, h3o, hI3⟩ := p4Round_good I hw hH hℓ hk hT hSpec (ε := 1) le_rfl _ hI2
    (by simp (config := { decide := true }) [Ex.eval])
  refine ⟨s3, (r0.seq (r1.seq (r2.seq r3))).mono ?_, ?_, hI3⟩
  · simp only [Ex.size]; omega
  · rw [h3o]; simp only [NSt.set_out]; rw [h1o]; simp (config := { decide := true }) [Ex.eval]

/-- **The start state of `P4`** from the end of the chain `P0`–`P3`. -/
lemma p4Inv_of_chain {w : ℕ} (st : NSt CR CQ) (hb : st.Bdd w) (hp : st.pos ≤ H I)
    (hL : ChainLoc I st)
    (hC : (I.schemas = [] ∧ ChainNoSch I st) ∨ (I.schemas ≠ [] ∧ ChainSch I st)) :
    P4Inv I w st := by
  obtain ⟨hTr, hW, hLl, hE, -⟩ := hL
  refine ⟨hb, hp, hTr, hW, hLl, hE, ?_, ?_, ?_, ?_⟩
  · intro hne
    rcases hC with ⟨h, -⟩ | ⟨-, hS⟩
    · exact absurd h hne
    · exact ⟨hS.2.2.2.2.2.1, hS.2.2.2.2.2.2.1, hS.2.2.2.1⟩
  · rcases hC with ⟨h, ⟨-, -, hz⟩⟩ | ⟨-, hS⟩
    · rw [hz _ (by decide)]
      have : List.finRange I.schemas.length = [] := List.eq_nil_of_length_eq_zero (by simp (config := { decide := true }) [h])
      simp (config := { decide := true }) [ansAll, this]
    · exact hS.1
  · rcases hC with ⟨h, ⟨-, -, hz⟩⟩ | ⟨-, hS⟩
    · rw [hz _ (by decide)]
      simp (config := { decide := true }) [schRecsUpTo, h]
    · exact hS.2.1
  · intro q a b c d
    rcases hC with ⟨-, ⟨-, -, hz⟩⟩ | ⟨-, hS⟩
    · exact hz q a
    · exact hS.2.2.1 q a b c d

/-! ## Sizes and the cost conversion -/

lemma length_le_sum_of_pos : ∀ l : List ℕ, (∀ v ∈ l, 1 ≤ v) → l.length ≤ l.sum
  | [], _ => le_rfl
  | a :: l, h => by
    have := length_le_sum_of_pos l (fun v hv => h v (List.mem_cons_of_mem a hv))
    have := h a (List.mem_cons_self ..)
    simp only [List.length_cons, List.sum_cons]; omega

lemma one_le_of_mem_schAll {v : ℕ} (hv : v ∈ schAll I) : 1 ≤ v := by
  simp only [schAll, List.mem_flatMap] at hv
  obtain ⟨e, -, hv⟩ := hv
  rw [schSizes_eq_szL] at hv
  simp only [szL, jlSizes, List.mem_append, List.mem_flatten, List.mem_replicate] at hv
  rcases hv with (((⟨l, ⟨-, rfl⟩, hl⟩ | ⟨-, rfl⟩) | ⟨l, ⟨-, rfl⟩, hl⟩) | ⟨-, rfl⟩) | ⟨-, rfl⟩
  all_goals first | omega | (split_ifs at hl <;> simp at hl <;> omega)

lemma one_le_of_mem_locAll {v : ℕ} (hv : v ∈ locAll I) : 1 ≤ v := by
  simp only [locAll, List.mem_flatMap, locSizes_eq_rep, List.mem_replicate] at hv
  obtain ⟨_, -, -, rfl⟩ := hv; omega

lemma length_clsSizes_le : (clsSizes I).length ≤ (ordL I).length := by
  rw [length_ordL]
  refine length_le_sum_of_pos _ fun v hv => ?_
  rw [clsSizes_eq', List.mem_append] at hv
  rcases hv with h | h
  · exact one_le_of_mem_schAll I h
  · exact one_le_of_mem_locAll I h

lemma length_schRecsUpTo_le (hk : 1 ≤ k) : (schRecsUpTo I I.schemas.length).length ≤ 4 * H I := by
  have h1 : (schRecsUpTo I I.schemas.length).length =
      ((List.finRange I.schemas.length).map fun e => (schRec I e).length).sum := by
    rw [schRecsUpTo, List.take_of_length_le (by simp), List.length_flatMap]
  have h2 : (schsDesc I).length =
      ((List.finRange I.schemas.length).map fun e => (schD I e).length).sum := by
    rw [schsDesc_eq, List.length_flatMap]
  have h3 : (schsDesc I).length ≤ H I := by
    have := length_sd_le I; rw [sd_eq] at this; simp at this; omega
  have h4 : ((List.finRange I.schemas.length).map fun e => (schRec I e).length).sum ≤
      ((List.finRange I.schemas.length).map fun e => 4 * (schD I e).length).sum := by
    refine List.sum_le_sum fun e _ => ?_
    have a := length_schemaDescription_ge I hk (sch I e)
    have b : 1 ≤ (schD I e).length := by
      rw [schD, schemaDescription_eq']; simp
    simp only [schRec, List.length_append, length_orsL, List.length_cons, List.length_nil]
    show ℓ + 3 ≤ 4 * (schemaDescription (sch I e)).length
    rw [schD] at b; omega
  rw [List.sum_map_mul_left] at h4
  omega

/-- **The size measure** of a round. -/
lemma p4Z_le (hk : 1 ≤ k) (ε : ℕ) : p4Z I ε ≤ 4 * H I + 5 * (ordL I).length := by
  have := length_schRecsUpTo_le I hk
  have := length_clsSizes_le I
  have := length_gEdges I (ε := ε)
  have := length_ordL I
  unfold p4Z; omega

/-- **Cost conversion** for costs linear in `H + S`. -/
lemma cost_conv_lin (K H S : ℕ) :
    K * (H + S + 1) * Ex.nodeCost (wordOf H S) ≤
      7744 * K * (H + S + 1) * (Nat.log 2 (H + S + 2) + 1) ^ 3 := by
  have hn := nodeCost_le_sq (a := 8) (L := Nat.log 2 (H + S + 2)) (w := wordOf H S) le_rfl
  set L := Nat.log 2 (H + S + 2)
  set N := Ex.nodeCost (wordOf H S)
  have h1 : (L + 1) ^ 2 ≤ (L + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  calc K * (H + S + 1) * N ≤ K * (H + S + 1) * (64 * (8 + 3) ^ 2 * (L + 1) ^ 2) :=
        Nat.mul_le_mul_left _ hn
    _ ≤ K * (H + S + 1) * (64 * (8 + 3) ^ 2 * (L + 1) ^ 3) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
    _ = 7744 * K * (H + S + 1) * (L + 1) ^ 3 := by ring

lemma p4_cost_arith {N h s Z0 Z1 C : ℕ} (h0 : Z0 ≤ 4 * h + 80 * s) (h1 : Z1 ≤ 4 * h + 80 * s) :
    4000 * (h + Z0 + 1) * N + 4000 * (h + Z1 + 1) * N + 2 * C + 4 * N ≤
      700000 * (h + s + 1) * N + 2 * C := by
  have a0 : (h + Z0 + 1) * N ≤ (5 * h + 80 * s + 1) * N := Nat.mul_le_mul_right _ (by omega)
  have a1 : (h + Z1 + 1) * N ≤ (5 * h + 80 * s + 1) * N := Nat.mul_le_mul_right _ (by omega)
  nlinarith

/-- **Pass `P4` after the chain** (word size `wordOf H S`): from the end state of the chain
`P0`–`P3` of a nontrivial system, `p4 SCH` appends `gDesc I 0 ++ gDesc I 1`, at cost
`700000 (H + S + 1) · nodeCost w + 2 C`. -/
theorem p4_good_chain (hk : 2 ≤ k) (ht : ¬ trivSys I) {SCH : CStm CR CQ} {C : ℕ}
    (hSpec : SchSpec I (wordOf (H I) (matrixSize I)) SCH C) (st : NSt CR CQ)
    (hb : st.Bdd (wordOf (H I) (matrixSize I))) (hp : st.pos ≤ H I) (hL : ChainLoc I st)
    (hC : (I.schemas = [] ∧ ChainNoSch I st) ∨ (I.schemas ≠ [] ∧ ChainSch I st)) :
    ∃ st', Good (encodeSystem I) (wordOf (H I) (matrixSize I)) (p4 SCH) st st'
        (700000 * (H I + matrixSize I + 1) * Ex.nodeCost (wordOf (H I) (matrixSize I)) +
          2 * C) ∧
      st'.out = st.out ++ gDesc I 0 ++ gDesc I 1 := by
  have hw := two_pow_word (H I) (matrixSize I)
  have hO := length_ordL_le I hk
  have hcl : (clsSizes I).sum = (ordL I).length := (length_ordL I).symm
  obtain ⟨st', r, ho, -⟩ := p4_good I (two_le_wordOf _ _) (by omega) (ell_le_H I (by omega) ht)
    (by omega) (by omega) hSpec st (p4Inv_of_chain I st hb hp hL hC)
  refine ⟨st', r.mono ?_, ho⟩
  have h0 := p4Z_le I (by omega) 0
  have h1 := p4Z_le I (by omega) 1
  exact p4_cost_arith (by omega) (by omega)

end Lax119563Proofs.Compiler
