import Mathlib.Data.Nat.Size
import Mathlib.Tactic.FinCases
import Mathlib.Data.Nat.Log
import Lax119563Proofs.Machines.Numbers

/-!
# Further combinators and routines

* `TM.whileM test c body`: a loop whose condition is read after running a test machine
  (`test ;; loop c (body ;; test)`), with a lemma along a sequence of tape families.
* `TM.revCopy`: copy a word in reverse order onto the end of another tape (e.g. to turn the
  little-endian digits of a number into big-endian ones).
* `TM.countLen`: add the length of a word to a counter.
-/

open Lax489179.TuringMachine (Move)

namespace Lax119563Proofs.Machines

variable {Γ : Type} {k : ℕ}

open Function (update)

namespace TM

variable [TapeAlphabet Γ]


/-- The `d` cells at and to the left of the head, read from right to left. -/
def _root_.Lax119563Proofs.Machines.Tape.leftWord (t : Tape Γ) : ℕ → List Γ
  | 0 => []
  | d + 1 => t.read :: Tape.leftWord ⟨t.head - 1, t.cells⟩ d

/-- Add the length of the word on tape `i` (from the head on) to the number on tape `c`. -/
def countLen [DecidableEq Γ] (i c : Fin k) : TM k Γ :=
  loop (fun s => decide (s i ≠ blank)) (moveR i ;; incr c)

theorem countLen_ofWord [DecidableEq Γ] {i c : Fin k} (hic : i ≠ c) (w : List Γ)
    (hw : ∀ a ∈ w, a ≠ blank) : ∀ (pre : List Γ) (m : ℕ) (T : Tapes k Γ),
    T i = .ofWord pre w → T c = .ofWord [] (natWord m) →
    (countLen i c).RunsWithin T (w.length * (4 * Nat.size (m + w.length) + 7))
      (update (update T i (.ofWord (pre ++ w) [])) c (.ofWord [] (natWord (m + w.length)))) := by
  induction w with
  | nil =>
    intro pre m T hTi hTc
    unfold countLen
    refine ((loop_runsWithin_exit (c := fun s => decide (s i ≠ blank)) (B := moveR i ;; incr c)
      (T := T) (by simp [readAll, hTi])).mono (Nat.zero_le _)).congr_right ?_
    funext l
    by_cases hl : l = c
    · subst hl; simp [hTc]
    · by_cases hl' : l = i
      · subst hl'; simp [Function.update_of_ne hl, hTi]
      · simp [Function.update_of_ne hl, Function.update_of_ne hl']
  | cons a w ih =>
    intro pre m T hTi hTc
    have ha : a ≠ blank := hw a (by simp)
    have h₁ := moveR_runsWithin i T
    rw [hTi, Tape.move_ofWord_right] at h₁
    have h₂ := incr_ofWord c m (T := update T i (Tape.ofWord (pre ++ [a]) w))
      (by simp [Function.update_of_ne hic.symm, hTc])
    have h₃ := ih (fun b hb => hw b (by simp [hb])) (pre ++ [a]) (m + 1)
      (update (update T i (Tape.ofWord (pre ++ [a]) w)) c (Tape.ofWord [] (natWord (m + 1))))
      (by simp [Function.update_of_ne hic]) (by simp)
    have h := loop_runsWithin_iter (c := fun s => decide (s i ≠ blank))
      (by simp [readAll, hTi, ha]) (seq_runsWithin h₁ h₂) h₃
    have hsize : m.bits.length ≤ Nat.size (m + (a :: w).length) := by
      rw [Nat.size_eq_bits_len]; exact Nat.size_le_size (by simp)
    refine (h.mono ?_).congr_right ?_
    · have e : m + 1 + w.length = m + (a :: w).length := by simp; ring
      rw [e]
      simp only [List.length_cons] at hsize ⊢
      nlinarith
    · rw [update_update_update_update hic]
      simp [show m + 1 + w.length = m + (w.length + 1) by ring]

end TM

end Lax119563Proofs.Machines
