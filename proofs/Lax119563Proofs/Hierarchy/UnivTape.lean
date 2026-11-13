import Lax119563Proofs.Hierarchy.UnivCode

/-!
# Tapes as left and right parts

`TapeRep T h l r`: the cells right of and at the head `h` are `r`, those left of it are `l`
(nearest first), and all others are blank.  Writing and moving acts as `tapeUpd`.
-/

namespace Lax119563Proofs.Hierarchy.Universal

open Lax489179.TuringMachine

/-- The tape `T` with head `h` is described by its left part `l` and right part `r`. -/
def TapeRep {n : ℕ} (T : ℤ → Fin (n + 3)) (h : ℤ) (l r : List ℕ) : Prop :=
  (∀ i : ℕ, (T (h + i)).val = r.getD i 0) ∧ (∀ i : ℕ, (T (h - 1 - i)).val = l.getD i 0)

lemma getD_tail (r : List ℕ) (i : ℕ) : r.tail.getD i 0 = r.getD (i + 1) 0 := by
  cases r <;> simp

lemma tapeRep_step {n : ℕ} {T : ℤ → Fin (n + 3)} {h : ℤ} {l r : List ℕ} (hT : TapeRep T h l r)
    (w : Fin (n + 3)) (mv : Move) :
    TapeRep (fun z => if z = h then w else T z) (h + mv.offset) (tapeUpd l r w.val mv).1
      (tapeUpd l r w.val mv).2 := by
  have hr : ∀ (z : ℤ) (i : ℕ), z = h + i → (T z).val = r.getD i 0 := by
    rintro z i rfl; exact hT.1 i
  have hl : ∀ (z : ℤ) (i : ℕ), z = h - 1 - i → (T z).val = l.getD i 0 := by
    rintro z i rfl; exact hT.2 i
  cases mv with
  | stay =>
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rcases i with _ | i
      · simp [tapeUpd, Move.offset]
      · simp only [tapeUpd]
        rw [if_neg (by simp only [Move.offset]; push_cast; omega), hr _ (i + 1) (by simp only [Move.offset]; push_cast; ring)]
        simp [getD_tail]
    · simp only [tapeUpd]
      rw [if_neg (by simp only [Move.offset]; omega), hl _ i (by simp only [Move.offset]; ring)]
  | right =>
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [tapeUpd]
      rw [if_neg (by simp only [Move.offset]; omega), hr _ (i + 1) (by simp only [Move.offset]; push_cast; ring), getD_tail]
    · rcases i with _ | i
      · simp [tapeUpd, Move.offset]
      · simp only [tapeUpd]
        rw [if_neg (by simp only [Move.offset]; push_cast; omega), hl _ i (by simp only [Move.offset]; push_cast; ring)]
        simp
  | left =>
    cases l with
    | nil =>
      refine ⟨fun i => ?_, fun i => ?_⟩
      · rcases i with _ | _ | i
        · simp only [tapeUpd]
          rw [if_neg (by simp only [Move.offset]; omega), hl _ 0 (by simp only [Move.offset]; ring)]; simp
        · simp [tapeUpd, Move.offset]
        · simp only [tapeUpd]
          rw [if_neg (by simp only [Move.offset]; push_cast; omega), hr _ (i + 1) (by simp only [Move.offset]; push_cast; ring)]
          simp [getD_tail]
      · simp only [tapeUpd]
        rw [if_neg (by simp only [Move.offset]; omega), hl _ (i + 1) (by simp only [Move.offset]; push_cast; ring)]; simp
    | cons c l =>
      refine ⟨fun i => ?_, fun i => ?_⟩
      · rcases i with _ | _ | i
        · simp only [tapeUpd]
          rw [if_neg (by simp only [Move.offset]; omega), hl _ 0 (by simp only [Move.offset]; ring)]; simp
        · simp [tapeUpd, Move.offset]
        · simp only [tapeUpd]
          rw [if_neg (by simp only [Move.offset]; push_cast; omega), hr _ (i + 1) (by simp only [Move.offset]; push_cast; ring)]
          simp [getD_tail]
      · simp only [tapeUpd]
        rw [if_neg (by simp only [Move.offset]; omega), hl _ (i + 1) (by simp only [Move.offset]; push_cast; ring)]; simp

end Lax119563Proofs.Hierarchy.Universal
