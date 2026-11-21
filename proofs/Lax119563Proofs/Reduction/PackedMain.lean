import Lax119563.PackedRepresentation
import Lax119563Proofs.Hardness.Part1
import Lax119563Proofs.Hardness.Part2

/-!
# The packed representation

The system `sys x h s = Iv M x s ℓ H` with `ℓ = packedWidth |x| h s` and
`H = max(h, ℓ)` (`Reduction/Packed`: correctness and the `O((h + 1)^2)` bounds) is computed
by the composition of two machines: the preprocessor `pkPre` (`Reduction/PkParse`), which
reads `h, s` and rewrites the input into records of fixed width (`pkInput x h s`), and the
machine of the packed generator `redGenP M` (`Reduction/PkMachine`), which emits the system
description with the number of blocks `s` read at runtime.
-/

open Lax119563.BinaryEncodings Lax119563.DeterministicTime
  Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Reduction

lemma pow37_le : ∃ D : ℕ, ∀ h : ℕ, (h + 3) ^ 37 ≤ D * (h + 1) ^ 37 :=
  ⟨3 ^ 37, fun h => by rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _⟩

/-- The arithmetic of the final time bound. -/
lemma packed_time_arith {C₁ C₂ D t₁ t₂ Q h s : ℕ} (hs : 1 ≤ s)
    (hD : (h + 3) ^ 37 ≤ D * (h + 1) ^ 37)
    (h1 : t₁ ≤ C₁ * (Q + h + 2) * (h + 1) ^ 2) (h2 : t₂ ≤ C₂ * Q * (h + 3) ^ 37) (hQ : 1 ≤ Q) :
    2 * t₁ + t₂ + 3 ≤ (6 * C₁ + D * C₂ + 3) * s * Q * (h + 1) ^ 37 := by
  have a2 : (h + 1) ^ 2 * (h + 1) ≤ (h + 1) ^ 37 := by
    rw [← pow_succ]; exact Nat.pow_le_pow_right (by omega) (by omega)
  have a3 : Q + h + 2 ≤ 3 * Q * (h + 1) := by nlinarith
  generalize (h + 1) ^ 37 = Y at hD a2 ⊢
  generalize (h + 3) ^ 37 = Z at hD h2
  have b1 : t₁ ≤ 3 * C₁ * (Q * Y) := by
    calc t₁ ≤ C₁ * (Q + h + 2) * (h + 1) ^ 2 := h1
      _ ≤ C₁ * (3 * Q * (h + 1)) * (h + 1) ^ 2 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ a3)
      _ = 3 * C₁ * (Q * ((h + 1) ^ 2 * (h + 1))) := by ring
      _ ≤ 3 * C₁ * (Q * Y) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ a2)
  have b2 : t₂ ≤ D * C₂ * (Q * Y) := by
    calc t₂ ≤ C₂ * Q * Z := h2
      _ ≤ C₂ * Q * (D * Y) := Nat.mul_le_mul_left _ hD
      _ = _ := by ring
  have hY : 1 ≤ Y := by
    have : (h + 1) ^ 2 * (h + 1) ≥ 1 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have b3 : 1 ≤ Q * Y := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have b4 : (6 * C₁ + D * C₂ + 3) * (Q * Y) ≤ (6 * C₁ + D * C₂ + 3) * s * Q * Y := by
    calc (6 * C₁ + D * C₂ + 3) * (Q * Y) = (6 * C₁ + D * C₂ + 3) * 1 * Q * Y := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hs))
  have e : (6 * C₁ + D * C₂ + 3) * (Q * Y) =
      2 * (3 * C₁ * (Q * Y)) + D * C₂ * (Q * Y) + 3 * (Q * Y) := by ring
  omega

/--
---
conclusion: Lax119563.PackedRepresentation.packed_representation
---
The system is `Iv M x s ℓ H` (the compiled code-ordered verifier program), with `ℓ` the
packed width and `H = max(h, ℓ) ≤ h + 1`; its correctness and the `O((h + 1)^2)` bounds on
locations and schemas are `packed_bounds_h`. The machine is the composition of the preprocessor
`pkPre` (`pkPre_computesWithin`: it reads `h, s` and writes the input as records of `16`
symbols carrying `x_k` and the flags `[k < |x|], [k < h], [k < s]`, in time
`O((2^ℓ + h) (h + 1)^2)`) and the machine of the packed generator `redGenP M`
(`redGenP_computesWithin`): a generator in the stack language `Gn` whose loops over blocks and
registers run up to runtime values, analysed with growth classes on two scales (`2^ℓ`
times a factor `O(h)` for the input length and the register values, and `(h + 3)^2` for the
linear quantities), in time `O(2^ℓ (h + 1)^37)`.
-/
theorem packed_representation : ∃ c : ℕ, ∀ M : Machine, Deterministic M →
    ∃ sys : (x : List Bool) → (h s : ℕ) →
        ImplicitParitySystem (s + 1) (Lax119563.PackedRepresentation.packedWidth x.length h s),
      ∃ C : ℕ,
        (∀ (x : List Bool) (h s : ℕ), 2 ≤ x.length → 2 ≤ h → x.length ≤ 2 ^ h → 2 ≤ s →
          s ≤ h + 2 →
            ((runOn M x (2 ^ h)).answer.isSome →
              ((sys x h s).conflictRound < ⊤ ↔ Accepts M x)) ∧
            (sys x h s).numLocations ≤ C * (h + 1) ^ 2 ∧
            (sys x h s).schemas.length ≤ C * (h + 1) ^ 2) ∧
        ∃ R : Machine, Deterministic R ∧
          ∀ (x : List Bool) (h s : ℕ), 2 ≤ x.length → 2 ≤ h → x.length ≤ 2 ^ h → 2 ≤ s →
            s ≤ h + 2 →
              ComputesWithin R (encodeNats [h, s] ++ x) (encodeSystem (sys x h s))
                (C * s * 2 ^ Lax119563.PackedRepresentation.packedWidth x.length h s *
                  (h + 1) ^ c) := by
  refine ⟨37, fun M _ => ?_⟩
  obtain ⟨C₀, hC₀⟩ := packed_bounds_h M
  obtain ⟨C₁, hC₁⟩ := pkPre_computesWithin
  obtain ⟨C₂, hC₂⟩ := redGenP_computesWithin M
  obtain ⟨D, hD⟩ := pow37_le
  refine ⟨fun x h s => Iv M x s (pkWidth x.length h s) (pkHorizon x.length h s),
    C₀ + (6 * C₁ + D * C₂ + 3), fun x h s hx hh hxh hs hsh => ?_, ?_⟩
  · obtain ⟨c1, c2, c3, -⟩ := hC₀ x h s hx hh hxh hs hsh
    refine ⟨c1, le_trans c2 (Nat.mul_le_mul_right _ (by omega)),
      le_trans c3 (Nat.mul_le_mul_right _ (by omega))⟩
  · refine ⟨(Main.Compose.comp (PkParse.pkPre.machine PkParse.pkPre.depth)
      (Gn.machine (Gn.redGenP M).need (Gn.redGenP M)) false fun _ => false).toMachine,
      Main.AMachine.toMachine_deterministic _, fun x h s hx hh hxh hs hsh => ?_⟩
    have h1 := hC₁ x h s hx hh hxh hs hsh
    have h2 := hC₂ x h s hx hh hxh hs hsh
    have hx2 : 2 ≤ (encodeNats [h, s] ++ x).length := by simp; omega
    have hc := Main.Compose.compose_computesWithin _ _ false (fun _ => false) hx2 h1 h2
    refine ComputesWithin.mono hc ?_
    have hT := packed_time_arith (s := s) (by omega) (hD h) le_rfl le_rfl
      (Q := 2 ^ pkWidth x.length h s) Nat.one_le_two_pow
      (C₁ := C₁) (C₂ := C₂) (h := h)
    show _ ≤ (C₀ + (6 * C₁ + D * C₂ + 3)) * s * 2 ^ pkWidth x.length h s * (h + 1) ^ 37
    refine le_trans hT ?_
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))

end Lax119563Proofs.Reduction
