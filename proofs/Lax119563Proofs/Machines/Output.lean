import Lax119563Proofs.Machines.Numbers

/-!
# The output convention

The input tapes are word tapes (`inputTapes_zero`, `inputTapes_ne_zero`). The routine
`finish o` erases tape `0` and copies the word on tape `o` there; combined with
`TM.computesWithin` this yields the output convention of `ComputesWithin`
(`TM.computesWithin_finish`).
-/

open Lax489179.TuringMachine (Machine)
open Lax119563.DeterministicTime

namespace Lax119563Proofs.Machines

variable {Γ : Type} [TapeAlphabet Γ] {k : ℕ}

open Function (update)

lemma inputTapes_zero (x : List Bool) :
    inputTapes (Γ := Γ) k x 0 = .ofWord [] (bitsWord x) := by
  simp [inputTapes, Tape.ofWord, bitsWord]

lemma inputTapes_ne_zero (x : List Bool) {i : Fin (k + 1)} (hi : i ≠ 0) :
    inputTapes (Γ := Γ) k x i = .ofWord [] [] := by
  simp [inputTapes, Tape.ofWord, hi]

namespace TM

variable [DecidableEq Γ]

/-- Replace the content of tape `0` by the word on tape `o`. -/
def finish (o : Fin (k + 1)) : TM (k + 1) Γ :=
  erase 0 ;; rewind o ;; copyR o 0 fun a => decide (a ≠ blank)

theorem finish_ofWord {o : Fin (k + 1)} (ho : o ≠ 0) {T : Tapes (k + 1) Γ}
    {pre rest opre orest : List Γ} (h0 : T 0 = .ofWord pre rest)
    (hw : ∀ a ∈ pre ++ rest, a ≠ blank) (hTo : T o = .ofWord opre orest)
    (hy : ∀ a ∈ opre ++ orest, a ≠ blank) :
    ∃ T' : Tapes (k + 1) Γ, (finish o).RunsWithin T
        (2 * rest.length + 2 * (pre ++ rest).length + 2 * opre.length + 2 * (opre ++ orest).length + 4) T' ∧
      T' 0 = .ofWord (opre ++ orest) [] := by
  have h₁ := erase_ofWord 0 h0 hw
  have h₂ := rewind_ofWord o (T := update T 0 (Tape.ofWord [] [])) (pre := opre) (rest := orest)
    (by simp [Function.update_of_ne ho, hTo]) (fun a ha => hy a (by simp [ha]))
  have h₃ := copyR_ofWord ho (fun a => decide (a ≠ blank)) (pre := []) (u := opre ++ orest)
    (rest := []) (dpre := []) (drest := [])
    (T := update (update T 0 (Tape.ofWord [] [])) o (Tape.ofWord [] (opre ++ orest)))
    (by simp) (fun a ha => by simpa using hy a ha) (by simp)
    (by simp [Function.update_of_ne ho.symm])
  refine ⟨_, (seq_runsWithin (seq_runsWithin h₁ h₂) h₃).mono (by simp; omega), by simp⟩

/-- **Output convention for a machine followed by `finish o`.** If `M` runs on the input
tapes of `x` within `t` transitions and leaves a blank-free word on tape `0` and the word of
`y` on tape `o`, then the compiled machine `M ;; finish o` computes `y` from `x`. -/
theorem computesWithin_finish [Fintype Γ] (M : TM (k + 1) Γ) {o : Fin (k + 1)} (ho : o ≠ 0)
    {x y : List Bool} {t : ℕ} {T : Tapes (k + 1) Γ}
    {pre rest opre orest : List Γ}
    (hM : M.RunsWithin (inputTapes k x) t T)
    (h0 : T 0 = .ofWord pre rest) (hw : ∀ a ∈ pre ++ rest, a ≠ blank)
    (hTo : T o = .ofWord opre orest) (hy : opre ++ orest = bitsWord y) :
    ComputesWithin (M ;; finish o).compile x y
      (t + 2 * rest.length + 2 * (pre ++ rest).length + 2 * opre.length +
        2 * (opre ++ orest).length + 4 + 1) := by
  obtain ⟨T', hfin, hT'⟩ := finish_ofWord ho h0 hw hTo
    (by rw [hy]; exact fun a ha => bit_ne_blank_of_mem_bitsWord ha)
  have := (M ;; finish o).computesWithin (fun _ _ => false) (x := x) (y := y)
    (seq_runsWithin hM hfin) (by rw [hT', hy]; simp [bitsWord])
  simpa [Nat.add_assoc, TM.compile] using this

end TM

end Lax119563Proofs.Machines
