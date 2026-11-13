import Lax119563Proofs.Reduction.OutEdgeList
import Lax119563Proofs.Programs.Compile

/-!
# Ternary schemas of compiled register programs are ordered

In `R.compile p₀ a₀`, every ternary schema has the form `(A, B, Z)` with `A, B` private
locations `a1, b1` resp. `a2, b2` of a command or `u1, u2` of the detector, or the fork schema
`(out1, out2, Y_p)`. Their numbers increase with the slot number, so `locU < locV`.
-/

open Lax119563.ImplicitParitySystems Lax119563Proofs.Matrix Lax119563Proofs.Programs

namespace Lax119563Proofs.Reduction

variable {s ℓ : ℕ} (R : RegisterProgram s ℓ)

lemma loc_slot_val (j : Fin R.commands.length) (t : Slot) :
    (R.loc (.slot j t)).val = R.numLocations + (t.toFin.val + 8 * j.val) := by
  simp [RegisterProgram.loc, Role.equivFin, Role.toSum, finProdFinEquiv, finSumFinEquiv]

lemma loc_det_val (t : DetSlot) :
    (R.loc (.det t)).val = R.numLocations + R.commands.length * 8 + t.toFin.val := by
  simp [RegisterProgram.loc, Role.equivFin, Role.toSum, finSumFinEquiv]

lemma tern_ordered_mem (p₀ : Fin R.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2)
    {e : Schema (s + 1) ℓ R.compiledSize} (he : e ∈ R.compiledSchemas p₀ a₀)
    (ht : isTern e = true) : locU e < locV e := by
  rw [Fin.lt_def]
  rcases R.mem_compiledSchemas.1 he with ⟨j, he⟩ | he
  · cases hc : R.commands[j] with
    | assign p g T q =>
      rw [hc] at he
      simp only [RegisterProgram.commandSchemas, gadget, List.mem_cons, List.not_mem_nil,
        or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> simp [isTern] at ht
      simp only [locU, locV, loc_slot_val]
      simp [Slot.toFin]
    | fork p g q q' =>
      rw [hc] at he
      simp only [RegisterProgram.commandSchemas, gadget, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at he
      rcases he with ((rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)) | rfl <;>
        simp [isTern] at ht <;> simp only [locU, locV, loc_slot_val] <;> simp [Slot.toFin]
  · simp only [RegisterProgram.detectorSchemas, gadget, List.mem_cons, List.not_mem_nil,
      or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> simp [isTern] at ht
    simp only [locU, locV, loc_det_val]
    simp [DetSlot.toFin]

/-- Compiled register programs satisfy `TernOrdered`. -/
theorem ternOrdered_compile (p₀ : Fin R.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2) :
    TernOrdered (R.compile p₀ a₀) := by
  intro e ht
  exact tern_ordered_mem R p₀ a₀ (List.get_mem _ _) ht

end Lax119563Proofs.Reduction
