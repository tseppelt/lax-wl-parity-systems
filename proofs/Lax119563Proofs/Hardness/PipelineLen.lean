import Lax119563Proofs.Hardness.Pipeline

/-!
# The pipeline with a bound on the length of the produced instance

`pipeline_len` is `pipeline` with a bound on the length of the produced WL instance instead of
the vertex bound: by `Lax119563.MatrixCompiler.matrix_compiler` the encoding of the compiled
graph pair has length `O((S + 1) log (S + 2))`. This is used for the exponential lower bound,
which measures time in the length of the instance.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.BinaryEncodings
  Lax119563.DeterministicTime Lax119563.PebbleGame Lax119563.ImplicitSystemEncodings
  Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.PackedRepresentation
  Lax119563.WLProblems
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Hardness

/-- **The pipeline, with the length of the produced instance.** -/
theorem pipeline_len : ∃ c Cl : ℕ, ∀ M : Machine, Deterministic M →
    ∃ R : Machine, Deterministic R ∧ ∃ C Cs : ℕ,
      ∀ (x : List Bool) (h s : ℕ), 2 ≤ x.length → 2 ≤ h → x.length ≤ 2 ^ h → 2 ≤ s →
        s ≤ h + 2 →
        ∃ G₀ G₁ : ColoredGraph,
          (HaltsWithin M x (2 ^ h) → (Accepts M x ↔ Distinguishes (s + 1) G₀ G₁)) ∧
          (encodeWLInstance (s + 1) G₀ G₁).length ≤ 2 * (s + 1) + 1 +
            Cl * (Cs * (h + 1) ^ 2 * (s + 1) ^ 2 * 2 ^ packedWidth x.length h s *
              (packedWidth x.length h s + 1) + 1) *
            (Nat.log 2 (Cs * (h + 1) ^ 2 * (s + 1) ^ 2 * 2 ^ packedWidth x.length h s *
              (packedWidth x.length h s + 1) + 2) + 1) ∧
          ComputesWithin R (encodeNats [h, s] ++ x) (encodeWLInstance (s + 1) G₀ G₁)
            (C * (s * 2 ^ packedWidth x.length h s * (h + 1)) ^ c) := by
  obtain ⟨cp, hpack⟩ := packed_representation
  obtain ⟨compile, ⟨Cn, hgame⟩, ⟨Mc, -, Cc, cc, hMc⟩⟩ := matrix_compiler
  refine ⟨(cp + 2) * (cc + 1), Cn, fun M hM => ?_⟩
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
  obtain ⟨hsp, hdu, -, -, hlen⟩ := hCk _ hℓ1 (sys x h s)
  have hSz : matrixSize (sys x h s) ≤ 5 * (Cs * (h + 1) ^ 2) * (s + 1) ^ 2 *
      2 ^ packedWidth x.length h s * (packedWidth x.length h s + 1) :=
    (sizeParameter_le _).trans (size_arith hloc hsch)
  refine ⟨(compile (sys x h s)).1, (compile (sys x h s)).2, fun hhalt => ?_, ?_, ?_⟩
  · exact (hcorr hhalt).symm.trans (distinguishes_iff_conflict (by omega) _ hsp hdu).symm
  · rw [encodeWLInstance_eq, List.length_append]
    have h1 := length_encodeNat_le (s + 1)
    have h2 := hlen
    obtain ⟨Sb, hSb⟩ : ∃ Sb, Sb = 5 * Cs * (h + 1) ^ 2 * (s + 1) ^ 2 *
        2 ^ packedWidth x.length h s * (packedWidth x.length h s + 1) := ⟨_, rfl⟩
    rw [← hSb]
    have hS : matrixSize (sys x h s) ≤ Sb := hSz.trans_eq (by rw [hSb]; ring)
    have h3 : Cn * (matrixSize (sys x h s) + 1) *
        (Nat.log 2 (matrixSize (sys x h s) + 2) + 1) ≤ Cn * (Sb + 1) * (Nat.log 2 (Sb + 2) + 1) :=
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
