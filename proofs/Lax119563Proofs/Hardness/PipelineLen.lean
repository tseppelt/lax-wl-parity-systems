import Lax119563Proofs.Hardness.Pipeline
import Lax119563Proofs.Matrix.Main

/-!
# The pipeline with a bound on the length of the produced instance

The matrix compiler of `Matrix/Main.lean` (the explicit graphs `Compiler.compileM`) emits a
graph pair whose encoding has length `O((S + 1) log (S + 2))` (`Compiler.length_out_le_log`):
colors and edge endpoints are numbers below `3 |V|`, and there are at most `3 |V|` edges per
graph. `matrix_compiler_len` records this next to the clauses of the concept statement, and
`pipeline_len` is `pipeline` with this length bound instead of the vertex bound. This is used
for the exponential lower bound, which measures time in the length of the instance; the
concept statement of the matrix compiler does not bound the colors.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.BinaryEncodings
  Lax119563.DeterministicTime Lax119563.PebbleGame Lax119563.ImplicitSystemEncodings
  Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.PackedRepresentation
  Lax119563.WLProblems
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Hardness

/-- **The matrix compiler with the length of its output.** -/
theorem matrix_compiler_len :
    ∃ compile : ∀ {k ℓ : ℕ}, ImplicitParitySystem k ℓ → ColoredGraph × ColoredGraph,
      (∃ C : ℕ, ∀ k : ℕ, 3 ≤ k → ∃ Cₖ : ℕ, ∀ ℓ : ℕ, 1 ≤ ℓ →
        ∀ I : ImplicitParitySystem k ℓ,
          (∀ τ : ℕ, I.conflictRound = τ →
            SpoilerWinsWithin (k + 1) (Cₖ * Λ I * (τ + 1)) (compile I).1 (compile I).2) ∧
          (∀ r : ℕ, (r : ℕ∞) + 1 ≤ I.conflictRound →
            DuplicatorSurvives (k + 1) r (compile I).1 (compile I).2) ∧
          (compile I).1.n + (compile I).2.n ≤ C * matrixSize I ∧
          (compile I).1.numEdges + (compile I).2.numEdges ≤
            3 * ((compile I).1.n + (compile I).2.n)) ∧
      (∃ M : Machine, Deterministic M ∧ ∃ C c : ℕ, ∀ k : ℕ, 3 ≤ k → ∀ ℓ : ℕ, 1 ≤ ℓ →
        ∀ I : ImplicitParitySystem k ℓ,
          ComputesWithin M (encodeSystem I) (encodeGraphPair (compile I).1 (compile I).2)
            (C * (bitLength I + matrixSize I) *
              Nat.log 2 (bitLength I + matrixSize I + 2) ^ c)) ∧
      (∀ k : ℕ, 3 ≤ k → ∀ ℓ : ℕ, ∀ I : ImplicitParitySystem k ℓ,
        (encodeGraphPair (compile I).1 (compile I).2).length ≤
          3360 * (matrixSize I + 1) * (Nat.log 2 (matrixSize I + 2) + 1)) := by
  obtain ⟨M, hD, C, c, h⟩ := Compiler.machine_clause_of_schSpec (SCH := Compiler.p4Sch)
    (K := 400000) (fun _ hk _ hℓ I => Compiler.p4Sch_spec I hk hℓ)
  refine ⟨Compiler.compileM, Compiler.compileM_clauses,
    ⟨M, hD, C, c, fun k hk ℓ hℓ I => ?_⟩, fun k hk ℓ I => ?_⟩
  · rw [Compiler.encode_compileM]; exact h k hk ℓ hℓ I
  · rw [Compiler.encode_compileM]
    refine (Compiler.length_out_le_log I (by omega) 0).trans ?_
    rw [zero_add]
    calc 2 * (2 + 7 * (16 * matrixSize I)) * (2 * (Nat.log 2 (matrixSize I + 2) + 7) + 1)
        ≤ (224 * (matrixSize I + 1)) * (15 * (Nat.log 2 (matrixSize I + 2) + 1)) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring

/-- **The pipeline, with the length of the produced instance.** -/
theorem pipeline_len : ∃ c : ℕ, ∀ M : Machine, Deterministic M →
    ∃ R : Machine, Deterministic R ∧ ∃ C Cs : ℕ,
      ∀ (x : List Bool) (h s : ℕ), 2 ≤ x.length → 2 ≤ h → x.length ≤ 2 ^ h → 2 ≤ s →
        s ≤ h + 2 →
        ∃ G₀ G₁ : ColoredGraph,
          (HaltsWithin M x (2 ^ h) → (Accepts M x ↔ Distinguishes (s + 1) G₀ G₁)) ∧
          (encodeWLInstance (s + 1) G₀ G₁).length ≤ 2 * (s + 1) + 1 +
            3360 * (Cs * (h + 1) ^ 2 * (s + 1) ^ 2 * 2 ^ packedWidth x.length h s *
              (packedWidth x.length h s + 1) + 1) *
            (Nat.log 2 (Cs * (h + 1) ^ 2 * (s + 1) ^ 2 * 2 ^ packedWidth x.length h s *
              (packedWidth x.length h s + 1) + 2) + 1) ∧
          ComputesWithin R (encodeNats [h, s] ++ x) (encodeWLInstance (s + 1) G₀ G₁)
            (C * (s * 2 ^ packedWidth x.length h s * (h + 1)) ^ c) := by
  obtain ⟨cp, hpack⟩ := packed_representation
  obtain ⟨compile, ⟨Cn, hgame⟩, ⟨Mc, -, Cc, cc, hMc⟩, hlen⟩ := matrix_compiler_len
  refine ⟨(cp + 2) * (cc + 1), fun M hM => ?_⟩
  obtain ⟨sys, Cs, hsys, Rp, -, hRp⟩ := hpack M hM
  obtain ⟨Kt, hKt⟩ : ∃ K, K = 2 * Cs + 16 * Cc * (21 * Cs + 7) ^ (cc + 1) + 16 * (5 + Cs) + 19 :=
    ⟨_, rfl⟩
  refine ⟨(Main.Compose.comp Rp (withLead Mc).compile false fun _ => false).toMachine,
    Main.AMachine.toMachine_deterministic _, Kt, 5 * Cs,
    fun x h s hx hh hxh hs hsh => ?_⟩
  have hℓ1 := one_le_packedWidth x.length h s
  have hQ := length_add_two_le x.length h s
  obtain ⟨hcorr, hloc, hsch⟩ := hsys x h s hx hh hxh hs hsh
  obtain ⟨Ck, hCk⟩ := hgame (s + 1) (by omega)
  obtain ⟨hsp, hdu, -, -⟩ := hCk _ hℓ1 (sys x h s)
  have hSz : matrixSize (sys x h s) ≤ 5 * (Cs * (h + 1) ^ 2) * (s + 1) ^ 2 *
      2 ^ packedWidth x.length h s * (packedWidth x.length h s + 1) :=
    (sizeParameter_le _).trans (size_arith hloc hsch)
  refine ⟨(compile (sys x h s)).1, (compile (sys x h s)).2, fun hhalt => ?_, ?_, ?_⟩
  · exact (hcorr hhalt).symm.trans (distinguishes_iff_conflict (by omega) _ hsp hdu).symm
  · rw [encodeWLInstance_eq, List.length_append]
    have h1 := length_encodeNat_le (s + 1)
    have h2 := hlen (s + 1) (by omega) _ (sys x h s)
    obtain ⟨Sb, hSb⟩ : ∃ Sb, Sb = 5 * Cs * (h + 1) ^ 2 * (s + 1) ^ 2 *
        2 ^ packedWidth x.length h s * (packedWidth x.length h s + 1) := ⟨_, rfl⟩
    rw [← hSb]
    have hS : matrixSize (sys x h s) ≤ Sb := hSz.trans_eq (by rw [hSb]; ring)
    have h3 : 3360 * (matrixSize (sys x h s) + 1) *
        (Nat.log 2 (matrixSize (sys x h s) + 2) + 1) ≤ 3360 * (Sb + 1) * (Nat.log 2 (Sb + 2) + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
        (by have := Nat.log_mono_right (b := 2) (show matrixSize (sys x h s) + 2 ≤ Sb + 2 by omega)
            omega)
    omega
  · have h1 := hRp x h s hx hh hxh hs hsh
    have h2 := hMc (s + 1) (by omega) _ hℓ1 (sys x h s)
    rw [encodeSystem_eq] at h2
    have h3 := withLead_computesWithin h2
    rw [← encodeSystem_eq, ← encodeWLInstance_eq] at h3
    have hxin2 : 2 ≤ (encodeNats [h, s] ++ x).length := by simp; omega
    have hc := Main.Compose.compose_computesWithin Rp (withLead Mc).compile false
      (fun _ => false) hxin2 h1 h3
    refine Main.Compose.computesWithin_mono' hc ?_
    obtain ⟨hX1, hX2, hX3, -⟩ := X_facts (h := h) (show 1 ≤ s by omega)
      (show 1 ≤ 2 ^ packedWidth x.length h s by omega)
    have hxin : (encodeNats [h, s] ++ x).length ≤
        5 * (s * 2 ^ packedWidth x.length h s * (h + 1)) := by
      have e1 := length_encodeNat_le h
      have e2 := length_encodeNat_le s
      simp only [encodeNats, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.length_append]
      omega
    have hH := length_le_of_computesWithin h1
    have hl : packedWidth x.length h s + 1 ≤ 2 ^ packedWidth x.length h s :=
      Nat.lt_two_pow_self
    have ht := time_arith (Cs := Cs) (Cc := Cc) (cp := cp) (cc := cc)
      (X := s * 2 ^ packedWidth x.length h s * (h + 1)) (by omega) hxin
      (T1_le (show 1 ≤ s by omega) (by omega)) hH (S_le hSz hl (by omega)) T2_le
    rw [← hKt] at ht
    exact ht

end Lax119563Proofs.Hardness
