import Lax119563Proofs.Machines.Words

/-!
# Basic routines on word tapes

Single transitions on one or two tapes (`actOn`, `act₂`), head moves and writes, scanning
over symbols satisfying a predicate in either direction (`scanR`, `scanL`, `backTo`,
`rewind`), copying (`copyR`) and erasing (`erase`). All bounds are linear in the number of
cells passed over.
-/

open Lax489179.TuringMachine (Move)

namespace Lax119563Proofs.Machines

variable {Γ : Type} {k : ℕ}

open Function (update)

namespace TM

/-! ## One transition on one or two tapes -/

/-- One transition on tape `i` only, as a function of the symbol scanned there. -/
def actOn (i : Fin k) (f : Γ → Γ × Move) : TM k Γ :=
  act fun s => (update s i (f (s i)).1, update (fun _ => Move.stay) i (f (s i)).2)

lemma applyAll_update (T : Tapes k Γ) (i : Fin k) (a : Γ) (m : Move) :
    applyAll T (update (readAll T) i a) (update (fun _ => .stay) i m) =
      update T i ((T i).act a m) := by
  funext j
  by_cases h : j = i
  · subst h; simp [applyAll]
  · simp only [applyAll, Function.update_of_ne h]
    exact Tape.act_read_stay _

theorem actOn_runsWithin (i : Fin k) (f : Γ → Γ × Move) (T : Tapes k Γ) :
    (actOn i f).RunsWithin T 1
      (update T i ((T i).act (f (T i).read).1 (f (T i).read).2)) := by
  have := act_haltsIn
    (fun s => (update s i (f (s i)).1, update (fun _ => Move.stay) i (f (s i)).2)) T
  simp only at this
  rw [show readAll T i = (T i).read from rfl, applyAll_update] at this
  exact this.runsWithin

/-- One transition on tapes `i` and `j`, as a function of the two scanned symbols. -/
def act₂ (i j : Fin k) (f : Γ → Γ → (Γ × Move) × (Γ × Move)) : TM k Γ :=
  act fun s => (update (update s i (f (s i) (s j)).1.1) j (f (s i) (s j)).2.1,
    update (update (fun _ => Move.stay) i (f (s i) (s j)).1.2) j (f (s i) (s j)).2.2)

theorem act₂_runsWithin {i j : Fin k} (hij : i ≠ j) (f : Γ → Γ → (Γ × Move) × (Γ × Move))
    (T : Tapes k Γ) :
    (act₂ i j f).RunsWithin T 1
      (update (update T i ((T i).act (f (T i).read (T j).read).1.1
          (f (T i).read (T j).read).1.2))
        j ((T j).act (f (T i).read (T j).read).2.1 (f (T i).read (T j).read).2.2)) := by
  have h := (act_haltsIn (fun s => (update (update s i (f (s i) (s j)).1.1) j (f (s i) (s j)).2.1,
    update (update (fun _ => Move.stay) i (f (s i) (s j)).1.2) j (f (s i) (s j)).2.2)) T).runsWithin
  refine h.congr_right ?_
  funext l
  simp only [applyAll]
  by_cases hl : l = j
  · subst hl; simp [readAll]
  · by_cases hl' : l = i
    · subst hl'; simp [Function.update_of_ne hl, readAll]
    · simp only [Function.update_of_ne hl, Function.update_of_ne hl']
      exact Tape.act_read_stay (T l)

/-! ## Moves and writes -/

/-- Move the head of tape `i` right. -/
def moveR (i : Fin k) : TM k Γ := actOn i fun a => (a, .right)
/-- Move the head of tape `i` left. -/
def moveL (i : Fin k) : TM k Γ := actOn i fun a => (a, .left)
/-- Write `b` on tape `i` without moving. -/
def write (i : Fin k) (b : Γ) : TM k Γ := actOn i fun _ => (b, .stay)
/-- Write `b` on tape `i` and move right. -/
def writeR (i : Fin k) (b : Γ) : TM k Γ := actOn i fun _ => (b, .right)

theorem moveR_runsWithin (i : Fin k) (T : Tapes k Γ) :
    (moveR i).RunsWithin T 1 (update T i ((T i).move .right)) := by
  exact (actOn_runsWithin i (fun a => (a, Move.right)) T).congr_right (by rw [Tape.act_read])

theorem moveL_runsWithin (i : Fin k) (T : Tapes k Γ) :
    (moveL i).RunsWithin T 1 (update T i ((T i).move .left)) := by
  exact (actOn_runsWithin i (fun a => (a, Move.left)) T).congr_right (by rw [Tape.act_read])

theorem write_runsWithin (i : Fin k) (b : Γ) (T : Tapes k Γ) :
    (write i b).RunsWithin T 1 (update T i ((T i).act b .stay)) :=
  actOn_runsWithin i _ T

theorem writeR_runsWithin (i : Fin k) (b : Γ) (T : Tapes k Γ) :
    (writeR i b).RunsWithin T 1 (update T i ((T i).act b .right)) :=
  actOn_runsWithin i _ T

/-! ## Scanning -/

/-- Move right on tape `i` while the scanned symbol satisfies `p`. -/
def scanR (i : Fin k) (p : Γ → Bool) : TM k Γ := loop (fun s => p (s i)) (moveR i)

/-- Move left on tape `i` while the scanned symbol satisfies `p`. -/
def scanL (i : Fin k) (p : Γ → Bool) : TM k Γ := loop (fun s => p (s i)) (moveL i)

lemma update_self_tape (T : Tapes k Γ) (i : Fin k) :
    update T i ⟨(T i).head, (T i).cells⟩ = T := by
  simp

theorem scanR_raw (i : Fin k) (p : Γ → Bool) (d : ℕ) (T : Tapes k Γ)
    (hd : ∀ j < d, p ((T i).cells ((T i).head + j)) = true)
    (hend : p ((T i).cells ((T i).head + d)) = false) :
    (scanR i p).RunsWithin T (2 * d) (update T i ⟨(T i).head + d, (T i).cells⟩) := by
  unfold scanR
  induction d generalizing T with
  | zero =>
    exact (loop_runsWithin_exit (B := moveR i) (c := fun s => p (s i)) (T := T)
      (by simpa [readAll, Tape.read] using hend)).congr_right (by simp)
  | succ d ih =>
    have h0 := hd 0 (by omega)
    have := ih (update T i ((T i).move .right))
      (fun j hj => by simpa [add_assoc, add_comm (1 : ℤ)] using hd (j + 1) (by omega))
      (by simpa [add_assoc, add_comm (1 : ℤ)] using hend)
    have h := loop_runsWithin_iter (c := fun s => p (s i)) (B := moveR i)
      (by simpa [readAll, Tape.read] using h0) (moveR_runsWithin i T) this
    refine (h.mono (by omega)).congr_right ?_
    simp only [Function.update_idem, Function.update_self, Tape.move_head, Tape.move_cells,
      Move.offset_right]
    rw [show (T i).head + 1 + (d : ℤ) = (T i).head + ((d + 1 : ℕ) : ℤ) by push_cast; ring]

end TM

end Lax119563Proofs.Machines
