import Lax119563Proofs.Compiler.P4Main
import Lax119563Proofs.Compiler.Final

/-!
# The compiler program and the final assembly

`prog SCH = pre; if rTriv then emit 0,0,0,0 else p4 SCH`, parametric in the schema edge part
`SCH` of `P4` (interface `SchSpec`, `Compiler/P4Round`).

* **`prog_good`**: if `SCH` satisfies `SchSpec I (wordOf H S) SCH (K (H + S + 1) · nodeCost w)`
  for every system with `k ≥ 3`, `ℓ ≥ 1`, then `prog SCH` satisfies the hypotheses of
  `machine_of_program` with `a = 8`, `e = 3` and constant `7744 (2K + 910010)`;
* **`machine_clause_of_schSpec`**: the machine clause of the concept;
* **`matrix_compiler_of_schSpec`**: the concept statement (via `matrix_compiler_of_machine`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix
open Lax119563.ColoredGraphs Lax119563.PebbleGame Lax119563.DeterministicTime
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Compiler

open CStm

/-- Emit a zero. -/
def emit0 : CStm CR CQ := .emit (.const 0)

/-- The output for a trivial system: `gDesc I 0 ++ gDesc I 1 = [0, 0, 0, 0]`. -/
def progTriv : CStm CR CQ := .seq emit0 (.seq emit0 (.seq emit0 emit0))

/-- **The compiler program**, given the schema edge part `SCH` of `P4`. -/
def prog (SCH : CStm CR CQ) : CStm CR CQ := .seq pre (.ite (rv rTriv) progTriv (p4 SCH))

lemma progTriv_good {x : List Bool} (w : ℕ) (st : NSt CR CQ) :
    Good x w progTriv st { st with out := st.out ++ [0, 0, 0, 0] } (8 * Ex.nodeCost w) := by
  have hU := CStm.nodeCost_ge w
  have hp : (0 : ℕ) < 2 ^ w := Nat.two_pow_pos w
  refine ⟨?_, ?_, ?_⟩
  · simp only [progTriv, emit0, CStm.Fits, Ex.Fits]; exact ⟨hp, hp, hp, hp⟩
  · simp [progTriv, emit0, CStm.exec, Ex.eval]
  · simp only [progTriv, emit0, CStm.cost, Ex.size]; omega

lemma prog_cost_arith {P N h lg Lc K A B c t : ℕ} (hP : 1 ≤ P)
    (hA : 210000 * (h + 1) * (lg + 1) * N ≤ A)
    (hB : (700010 + 2 * K) * P * N ≤ B)
    (hc : c ≤ 2 * N)
    (ht : t ≤ 700000 * P * N + 2 * (K * P * N) ∨ t ≤ 8 * N)
    (hA' : A ≤ 7744 * 210000 * P * Lc) (hB' : B ≤ 7744 * (700010 + 2 * K) * P * Lc) :
    210000 * (h + 1) * (lg + 1) * N + (c + t) ≤ 7744 * (2 * K + 910010) * P * Lc := by
  have hN : N ≤ P * N := Nat.le_mul_of_pos_left N hP
  have e1 : (700010 + 2 * K) * P * N = 700010 * (P * N) + 2 * (K * P * N) := by ring
  have e2 : 7744 * (2 * K + 910010) * P * Lc =
      7744 * 210000 * P * Lc + 7744 * (700010 + 2 * K) * P * Lc := by ring
  have : c + t ≤ B := by rcases ht with ht | ht <;> nlinarith
  omega

set_option maxHeartbeats 1000000 in
/-- **The compiler program**: the hypotheses of `machine_of_program` (`a = 8`, `e = 3`), given
a schema edge part with a uniform `SchSpec` of cost `K (H + S + 1) · nodeCost w`. -/
theorem prog_good {SCH : CStm CR CQ} {K : ℕ}
    (hSCH : ∀ k : ℕ, 3 ≤ k → ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ I : ImplicitParitySystem k ℓ,
      SchSpec I (wordOf (H I) (matrixSize I)) SCH
        (K * (H I + matrixSize I + 1) * Ex.nodeCost (wordOf (H I) (matrixSize I)))) :
    ∀ k : ℕ, 3 ≤ k → ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ I : ImplicitParitySystem k ℓ,
      let w := 8 * (Nat.log 2 (bitLength I + matrixSize I + 2) + 1)
      (prog SCH).Fits (encodeSystem I) w (NSt.zero CR CQ) ∧
      ((prog SCH).exec (encodeSystem I) (NSt.zero CR CQ)).out = gDesc I 0 ++ gDesc I 1 ∧
      (prog SCH).cost (encodeSystem I) w (NSt.zero CR CQ) ≤
        7744 * (2 * K + 910010) * (bitLength I + matrixSize I + 1) *
          (Nat.log 2 (bitLength I + matrixSize I + 2) + 1) ^ 3 := by
  intro k hk ℓ hℓ I
  show (prog SCH).Fits (encodeSystem I) (wordOf (H I) (matrixSize I)) (NSt.zero CR CQ) ∧
      ((prog SCH).exec (encodeSystem I) (NSt.zero CR CQ)).out = gDesc I 0 ++ gDesc I 1 ∧
      (prog SCH).cost (encodeSystem I) (wordOf (H I) (matrixSize I)) (NSt.zero CR CQ) ≤
        7744 * (2 * K + 910010) * (H I + matrixSize I + 1) *
          (Nat.log 2 (H I + matrixSize I + 2) + 1) ^ 3
  have hU := CStm.nodeCost_ge (wordOf (H I) (matrixSize I))
  have hA' := cost_conv 210000 (H I) (matrixSize I)
  have hB' := cost_conv_lin (700010 + 2 * K) (H I) (matrixSize I)
  have hc := condCost_rv (wordOf (H I) (matrixSize I)) rTriv
  obtain ⟨s, r, hout, hb, hp, htriv, hnt⟩ :=
    pre_good I (two_le_wordOf _ _) (by omega) (word_hS I (by omega))
  have hf : (rv rTriv : Ex CR).Fits (wordOf (H I) (matrixSize I)) s.env := hb.1 rTriv
  suffices h : ∃ s' t, Good (encodeSystem I) (wordOf (H I) (matrixSize I)) (prog SCH)
      (NSt.zero CR CQ) s' t ∧ s'.out = gDesc I 0 ++ gDesc I 1 ∧
      t ≤ 7744 * (2 * K + 910010) * (H I + matrixSize I + 1) *
          (Nat.log 2 (H I + matrixSize I + 2) + 1) ^ 3 by
    obtain ⟨s', t, ⟨hF, hE, hC⟩, ho, ht⟩ := h
    exact ⟨hF, by rw [hE, ho], hC.trans ht⟩
  by_cases ht : trivSys I
  · have e1 : s.env rTriv = 1 := (htriv ht).1
    have r' := r.seq (Good.iteT (q := p4 SCH) hf (by show s.env rTriv ≠ 0; omega)
      (progTriv_good _ s))
    refine ⟨_, _, r', ?_, prog_cost_arith (by omega) le_rfl le_rfl hc
      (Or.inr le_rfl) hA' hB'⟩
    show s.out ++ [0, 0, 0, 0] = _
    rw [hout, gDesc_triv I ht, gDesc_triv I ht]; rfl
  · obtain ⟨hL, hNo, hSch⟩ := hnt ht
    have hC : (I.schemas = [] ∧ ChainNoSch I s) ∨ (I.schemas ≠ [] ∧ ChainSch I s) := by
      by_cases hE : I.schemas = []
      · exact Or.inl ⟨hE, hNo hE⟩
      · exact Or.inr ⟨hE, hSch hE⟩
    obtain ⟨s', r4, ho⟩ := p4_good_chain I (by omega) ht (hSCH k hk ℓ hℓ I) s hb hp hL hC
    have r' := r.seq (Good.iteF (p := progTriv) hf (by show s.env rTriv = 0; exact hL.1) r4)
    refine ⟨_, _, r', by rw [ho, hout, List.nil_append], prog_cost_arith (by omega) le_rfl
      le_rfl hc (Or.inl le_rfl) hA' hB'⟩

/-- **The machine clause of the concept**, from a schema edge part with a uniform `SchSpec`. -/
theorem machine_clause_of_schSpec {SCH : CStm CR CQ} {K : ℕ}
    (hSCH : ∀ k : ℕ, 3 ≤ k → ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ I : ImplicitParitySystem k ℓ,
      SchSpec I (wordOf (H I) (matrixSize I)) SCH
        (K * (H I + matrixSize I + 1) * Ex.nodeCost (wordOf (H I) (matrixSize I)))) :
    ∃ M : Machine, Deterministic M ∧ ∃ C c : ℕ, ∀ k : ℕ, 3 ≤ k → ∀ ℓ : ℕ, 1 ≤ ℓ →
      ∀ I : ImplicitParitySystem k ℓ,
        ComputesWithin M (encodeSystem I) (encodeNats (gDesc I 0 ++ gDesc I 1))
          (C * (bitLength I + matrixSize I) *
            Nat.log 2 (bitLength I + matrixSize I + 2) ^ c) :=
  machine_of_program (prog SCH) le_rfl 8 _ 3 (by norm_num) (by norm_num) (prog_good hSCH)

end Lax119563Proofs.Compiler
