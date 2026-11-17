import Lax119563Proofs.Reduction.EdgeMath

/-!
# Slot passes with arbitrary bodies

`schSlots M s b body` and `stepSlots M s b body`: the schema enumerator (and the step loops)
around the slot loops, for any body; `out_schSlots`/`out_stepSlots` give the output as the
concatenation of the body outputs, described slot by slot.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs Lax119563Proofs.Matrix

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

namespace Gn

/-- Slot loops in the schema enumerator (slot loops at depth `b + 37`). -/
def schSlots (M : Machine) (s b : ℕ) (body : Gn) : Gn :=
  schEnum M s b gH gR gN gr gp0 gEc (slotLoops s gP (violAt s b (b + 37)) body)

/-- Slot loops in the step loops in the schema enumerator (slot loops at depth `b + 41`). -/
def stepSlots (M : Machine) (s b : ℕ) (body : Gn) : Gn :=
  schEnum M s b gH gR gN gr gp0 gEc (stepLoops s (slotLoops s gP (violAt s b (b + 41)) body))

end Gn

theorem out_schSlots {ρ : List ℕ} {b : ℕ} (hρ : ρ.length = b) (hG : GlobOK M x s ℓ H ρ)
    (body : Gn) (U : ℕ → ℕ → ℕ → ℕ → List ℕ)
    (hbody : ∀ e (he : e < (Iv M x s ℓ H).schemas.length) τ,
      SchCtx M x s ℓ H b ρ τ e (sch (Iv M x s ℓ H) ⟨e, he⟩) →
      ∀ i < s + 1, ∀ v < 2 ^ ℓ, ∀ t < 4,
        body.out x (slotStk s ℓ x τ (violAt s b (b + 37)) i v t) = U e i v t) :
    (Gn.schSlots M s b body).out x ρ =
      (List.range (Iv M x s ℓ H).schemas.length).flatMap fun e => slotL s ℓ (U e) := by
  obtain ⟨T, hT, hctx⟩ := schEnum_ctx hρ hG
  rw [Gn.schSlots, hT]
  refine List.flatMap_congr fun e he => ?_
  rw [List.mem_range] at he
  have hc := hctx e he
  have hGτ : GlobOK M x s ℓ H (T e) := hG.of_take hρ hc.2.1
  have hb := hρ ▸ hG.le
  rw [out_slotLoops (bnd_glob (by omega) (by rw [hc.1]; omega)) hGτ.eP]
  unfold slotL
  refine List.flatMap_congr fun i hi => List.flatMap_congr fun v hv =>
    List.flatMap_congr fun t ht => ?_
  rw [List.mem_range] at hi hv ht
  exact hbody e he _ hc i hi v hv t ht

theorem out_stepSlots {ρ : List ℕ} {b : ℕ} (hρ : ρ.length = b) (hG : GlobOK M x s ℓ H ρ)
    (body : Gn) (U : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ)
    (hbody : ∀ e (he : e < (Iv M x s ℓ H).schemas.length) τ,
      SchCtx M x s ℓ H b ρ τ e (sch (Iv M x s ℓ H) ⟨e, he⟩) →
      ∀ q < s + 2, ∀ j < s + ℓ, ∀ i < s + 1, ∀ v < 2 ^ ℓ, ∀ t < 4,
        body.out x (slotStk s ℓ x (τ ++ [s + 2, q, s + ℓ, j]) (violAt s b (b + 41)) i v t) =
          U e (q * (s + ℓ) + j) i v t) :
    (Gn.stepSlots M s b body).out x ρ =
      (List.range (Iv M x s ℓ H).schemas.length).flatMap fun e =>
        (List.range (numSteps (s + 1) ℓ)).flatMap fun σ => slotL s ℓ (U e σ) := by
  obtain ⟨T, hT, hctx⟩ := schEnum_ctx hρ hG
  rw [Gn.stepSlots, hT]
  refine List.flatMap_congr fun e he => ?_
  rw [List.mem_range] at he
  have hc := hctx e he
  have hGτ : GlobOK M x s ℓ H (T e) := hG.of_take hρ hc.2.1
  have hb := hρ ▸ hG.le
  rw [out_stepLoops hGτ, numSteps_succ, range_mul_flatMap]
  refine List.flatMap_congr fun q hq => List.flatMap_congr fun j hj => ?_
  rw [List.mem_range] at hq hj
  have hGτ' := hGτ.append [s + 2, q, s + ℓ, j]
  have hlen : (T e ++ [s + 2, q, s + ℓ, j]).length = b + 41 := by simp [hc.1]
  rw [out_slotLoops (bnd_glob (by omega) (by rw [hlen]; omega)) hGτ'.eP]
  unfold slotL
  refine List.flatMap_congr fun i hi => List.flatMap_congr fun v hv =>
    List.flatMap_congr fun t ht => ?_
  rw [List.mem_range] at hi hv ht
  exact hbody e he _ hc q hq j hj i hi v hv t ht

end Lax119563Proofs.Reduction
