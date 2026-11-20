import Lax119563Proofs.Circuits.TimeSimulation

/-!
# The time program with commands in code order

`timeProgram'` has the locations and moves of `Circuits.timeProgram`, but its command list
enumerates the locations in the order of their numbers (`Loc.code`):
`progCmds ℓ (locsByCode M H) moves` with `locsByCode = (range numLoc).filterMap decodeLoc`.
Then the index of a command is a count of the commands at smaller location numbers, which
a generator can compute. Acceptance (`timeProgram'_accepts_iff`) and the size bounds carry
over.
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

/-- The time simulation program with commands in code order. -/
noncomputable def timeProgram' (M : Machine) (s C₀ : ℕ) (x : List Bool) :
    RegisterProgram s (timeWidth C₀ x.length) :=
  compile (numLoc M (timeHorizon s C₀ x.length)) Loc.code .accept .reject
    code_accept_ne_reject
    (verifierCmds' M x s (timeWidth C₀ x.length) (timeHorizon s C₀ x.length))

/-- The query location. -/
def timeQuery' (M : Machine) (s C₀ : ℕ) (x : List Bool) :
    Fin (timeProgram' M s C₀ x).numLocations :=
  (Loc.query : Loc M (timeHorizon s C₀ x.length)).code

theorem timeProgram'_accepts_iff {s C₀ : ℕ} (hs : 2 ≤ s)
    (hC₀ : ∀ x : List Bool, (runOn M x (C₀ * x.length ^ s + C₀)).answer.isSome)
    {x : List Bool} (hx : 2 ≤ x.length) :
    (timeProgram' M s C₀ x).Accepts (timeQuery' M s C₀ x) (fun _ _ => 0) ↔ Accepts M x := by
  have P := params_of (C₀ := C₀) hs hx
  have hmask : MasksBounded s (timeWidth C₀ x.length)
      (verifierCmds' M x s (timeWidth C₀ x.length) (timeHorizon s C₀ x.length)) :=
    progCmds_masks P.hH fun src _ => moves_wf src
  unfold timeProgram' timeQuery'
  rw [compile_accepts Loc.code_injective _ hmask, addr_zero]
  unfold verifierCmds'
  rw [verifier_accepts_iff P mem_locsByCode _ (by positivity)]
  rw [accepts_iff_answer (halts_by_horizon hs hC₀ hx)]
  rfl

lemma timeProgram'_numLocations (s C₀ : ℕ) (x : List Bool) :
    (timeProgram' M s C₀ x).numLocations = numLoc M (timeHorizon s C₀ x.length) := rfl

lemma timeProgram'_commands_le (s C₀ : ℕ) (x : List Bool) :
    (timeProgram' M s C₀ x).commands.length ≤
      numLoc M (timeHorizon s C₀ x.length) * movBound M s := by
  simp only [timeProgram', compile, List.length_map, verifierCmds', progCmds]
  calc _ ≤ (locsByCode M (timeHorizon s C₀ x.length)).length * movBound M s :=
        length_flatMap_le fun L _ => by rw [List.length_map]; exact moves_length_le _ _ _ L
    _ ≤ _ := Nat.mul_le_mul_right _ length_locsByCode_le

/-- **Time simulation in code order** (as `Circuits.time_simulation`). -/
theorem time_simulation' (M : Machine) (s : ℕ) (hs : 2 ≤ s) (C₀ : ℕ)
    (hC₀ : ∀ x : List Bool, (runOn M x (C₀ * x.length ^ s + C₀)).answer.isSome) :
    ∃ C : ℕ, ∀ x : List Bool, 2 ≤ x.length →
      1 ≤ timeWidth C₀ x.length ∧
      ((timeProgram' M s C₀ x).Accepts (timeQuery' M s C₀ x) (fun _ _ => 0) ↔ Accepts M x) ∧
      x.length ≤ C * 2 ^ timeWidth C₀ x.length ∧
      2 ^ timeWidth C₀ x.length ≤ C * x.length ∧
      (timeProgram' M s C₀ x).numLocations ≤ C * Nat.log 2 x.length ^ 5 ∧
      (timeProgram' M s C₀ x).commands.length ≤ C * Nat.log 2 x.length ^ 5 := by
  obtain ⟨C, hC⟩ := time_simulation M s hs C₀ hC₀
  refine ⟨C + 16 * (s * (C₀ + 5) + cM M) ^ 5 * (movBound M s + 1), fun x hx => ?_⟩
  obtain ⟨h1, -, h3, h4, h5, -⟩ := hC x hx
  have hNL := numLoc_le (M := M) (s := s) (C₀ := C₀) (by omega) hx
  generalize hK : 16 * (s * (C₀ + 5) + cM M) ^ 5 = K at hNL ⊢
  refine ⟨h1, timeProgram'_accepts_iff hs hC₀ hx, ?_, ?_, ?_, ?_⟩
  · exact h3.trans (Nat.mul_le_mul_right _ (by omega))
  · exact h4.trans (Nat.mul_le_mul_right _ (by omega))
  · rw [timeProgram'_numLocations]
    exact hNL.trans (Nat.mul_le_mul_right _ (le_trans (Nat.le_mul_of_pos_right K (Nat.succ_pos _))
      (Nat.le_add_left _ _)))
  · calc _ ≤ numLoc M (timeHorizon s C₀ x.length) * movBound M s := timeProgram'_commands_le _ _ _
      _ ≤ K * Nat.log 2 x.length ^ 5 * movBound M s := Nat.mul_le_mul_right _ hNL
      _ = K * movBound M s * Nat.log 2 x.length ^ 5 := by ring
      _ ≤ (C + K * (movBound M s + 1)) * Nat.log 2 x.length ^ 5 :=
        Nat.mul_le_mul_right _ (le_trans (Nat.mul_le_mul_left K (Nat.le_succ _))
          (Nat.le_add_left _ _))

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
