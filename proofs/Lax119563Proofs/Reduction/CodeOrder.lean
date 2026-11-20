import Lax119563Proofs.Circuits.TimeSimulation

/-!
# Locations in code order

`locsByCode M H = (range numLoc).filterMap decodeLoc` enumerates the locations of the verifier
program in the order of their numbers (`Loc.code`; `decodeLoc_code`, `mem_locsByCode`).
`verifierCmds'` is the command list of the verifier program in this order
(`verifierCmds'_eq`), so that the index of a command is a count of the commands at smaller
location numbers, which a generator can compute.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Programs

variable {M : Machine} {H : ℕ}

open Classical in
/-- The location with number `c`, if any. -/
noncomputable def decodeLoc (M : Machine) (H : ℕ) (c : ℕ) : Option (Loc M H) :=
  if h : ∃ L : Loc M H, (Loc.code L).val = c then some (Classical.choose h) else none

lemma decodeLoc_code (L : Loc M H) : decodeLoc M H (Loc.code L).val = some L := by
  have h : ∃ L' : Loc M H, (Loc.code L').val = (Loc.code L).val := ⟨L, rfl⟩
  rw [decodeLoc, dif_pos h]
  exact congrArg some (Loc.code_injective (Fin.ext (Classical.choose_spec h)))

lemma code_of_decodeLoc {c : ℕ} {L : Loc M H} (h : decodeLoc M H c = some L) :
    (Loc.code L).val = c := by
  unfold decodeLoc at h
  split_ifs at h with h'
  · cases h; exact Classical.choose_spec h'

/-- The locations in the order of their numbers. -/
noncomputable def locsByCode (M : Machine) (H : ℕ) : List (Loc M H) :=
  (List.range (numLoc M H)).filterMap (decodeLoc M H)

lemma mem_locsByCode (L : Loc M H) : L ∈ locsByCode M H := by
  rw [locsByCode, List.mem_filterMap]
  exact ⟨_, List.mem_range.mpr (Loc.code L).isLt, decodeLoc_code L⟩

lemma length_locsByCode_le : (locsByCode M H).length ≤ numLoc M H :=
  (List.length_filterMap_le _ _).trans (by simp)

/-- The address commands of the verifier, in code order. -/
noncomputable def verifierCmds' (M : Machine) (x : List Bool) (s ℓ H : ℕ) :
    List (ACmd (Loc M H) s) :=
  progCmds ℓ (locsByCode M H) (moves M x s ℓ H)

/-- The commands in code order: for each number `c`, the moves of the decoded location. -/
lemma verifierCmds'_eq (x : List Bool) (s ℓ : ℕ) :
    verifierCmds' M x s ℓ H = (List.range (numLoc M H)).flatMap fun c =>
      match decodeLoc M H c with
      | some L => (moves M x s ℓ H L).map (Move.toACmd ℓ L)
      | none => [] := by
  unfold verifierCmds' progCmds locsByCode
  induction (List.range (numLoc M H)) with
  | nil => rfl
  | cons c l ih =>
    rw [List.filterMap_cons, List.flatMap_cons]
    cases h : decodeLoc M H c with
    | none => simpa using ih
    | some L => simp [ih]

end Lax119563Proofs.Reduction
