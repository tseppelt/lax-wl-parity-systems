import Lax119563Proofs.Machines.Routines

/-!
# Scanning, rewinding, copying and erasing word tapes

Specifications of the routines of `Routines` on tapes of the form `Tape.ofWord pre rest`.
-/

open Lax489179.TuringMachine (Move)

namespace Lax119563Proofs.Machines

variable {Γ : Type} {k : ℕ}

open Function (update)

namespace TM

theorem scanL_raw (i : Fin k) (p : Γ → Bool) (d : ℕ) (T : Tapes k Γ)
    (hd : ∀ j < d, p ((T i).cells ((T i).head - j)) = true)
    (hend : p ((T i).cells ((T i).head - d)) = false) :
    (scanL i p).RunsWithin T (2 * d) (update T i ⟨(T i).head - d, (T i).cells⟩) := by
  unfold scanL
  induction d generalizing T with
  | zero =>
    exact (loop_runsWithin_exit (B := moveL i) (c := fun s => p (s i)) (T := T)
      (by simpa [readAll, Tape.read] using hend)).congr_right (by simp)
  | succ d ih =>
    have h0 := hd 0 (by omega)
    have := ih (update T i ((T i).move .left))
      (fun j hj => by
        have := hd (j + 1) (by omega)
        simp only [Function.update_self, Tape.move_head, Tape.move_cells, Move.offset_left]
        rw [show (T i).head + -1 - (j : ℤ) = (T i).head - ((j + 1 : ℕ) : ℤ) by push_cast; ring]
        exact this)
      (by
        simp only [Function.update_self, Tape.move_head, Tape.move_cells, Move.offset_left]
        rw [show (T i).head + -1 - (d : ℤ) = (T i).head - ((d + 1 : ℕ) : ℤ) by push_cast; ring]
        exact hend)
    have h := loop_runsWithin_iter (c := fun s => p (s i)) (B := moveL i)
      (by simpa [readAll, Tape.read] using h0) (moveL_runsWithin i T) this
    refine (h.mono (by omega)).congr_right ?_
    simp only [Function.update_idem, Function.update_self, Tape.move_head, Tape.move_cells,
      Move.offset_left]
    rw [show (T i).head + -1 - (d : ℤ) = (T i).head - ((d + 1 : ℕ) : ℤ) by push_cast; ring]

end TM

/-! ## Cells of word tapes -/

variable [TapeAlphabet Γ]

lemma listCells_add (pre l : List Γ) (j : ℕ) :
    listCells (pre ++ l) ((pre.length : ℤ) + j) = l[j]?.getD blank := by
  rw [show (pre.length : ℤ) + j = ((pre.length + j : ℕ) : ℤ) by push_cast; rfl,
    listCells_natCast, List.getElem?_append_right (by omega)]
  simp

lemma listCells_of_length_le (l : List Γ) {z : ℤ} (hz : (l.length : ℤ) ≤ z) :
    listCells l z = blank := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ z)
  rw [listCells_natCast, List.getElem?_eq_none (by omega)]
  rfl

lemma listCells_of_lt (l : List Γ) {n : ℕ} (hn : n < l.length) :
    listCells l (n : ℤ) = l[n] := by
  rw [listCells_natCast, List.getElem?_eq_getElem hn]
  rfl

namespace TM

theorem scanR_ofWord (i : Fin k) (p : Γ → Bool) {T : Tapes k Γ} {pre u rest : List Γ}
    (hT : T i = .ofWord pre (u ++ rest)) (hu : ∀ a ∈ u, p a = true)
    (hr : p (rest.headD blank) = false) :
    (scanR i p).RunsWithin T (2 * u.length) (update T i (.ofWord (pre ++ u) rest)) := by
  refine (scanR_raw i p u.length T (fun j hj => ?_) ?_).congr_right ?_
  · rw [hT, Tape.ofWord_head, Tape.ofWord_cells, listCells_add,
      List.getElem?_append_left hj, List.getElem?_eq_getElem hj]
    exact hu _ (List.getElem_mem _)
  · rw [hT, Tape.ofWord_head, Tape.ofWord_cells, listCells_add, List.getElem?_append_right le_rfl]
    cases rest <;> simpa using hr
  · rw [hT]
    congr 1
    ext
    · simp
    · simp

/-- Move left to just after the nearest cell (to the left of the head) violating `p`: from
the head on the cell after `u` back to the first cell of `u`. -/
def backTo (i : Fin k) (p : Γ → Bool) : TM k Γ := moveL i ;; scanL i p ;; moveR i

theorem backTo_ofWord (i : Fin k) (p : Γ → Bool) {T : Tapes k Γ} {pre u rest : List Γ}
    (hT : T i = .ofWord (pre ++ u) rest) (hu : ∀ a ∈ u, p a = true)
    (hpre : p (pre.getLast?.getD blank) = false) :
    (backTo i p).RunsWithin T (2 * u.length + 2) (update T i (.ofWord pre (u ++ rest))) := by
  have h₁ := moveL_runsWithin i T
  set T₁ := update T i ((T i).move .left) with hT₁
  have hT₁i : T₁ i = ⟨(pre.length : ℤ) + u.length - 1, listCells (pre ++ (u ++ rest))⟩ := by
    rw [hT₁, Function.update_self, hT]
    ext
    · simp; ring
    · simp
  have h₂ := scanL_raw i p u.length T₁ (fun j hj => ?_) ?_
  · have h₃ := moveR_runsWithin i (update T₁ i ⟨(T₁ i).head - u.length, (T₁ i).cells⟩)
    refine ((seq_runsWithin (seq_runsWithin h₁ h₂) h₃).mono (by omega)).congr_right ?_
    simp only [Function.update_idem, Function.update_self, Tape.move_head, Tape.move_cells,
      Move.offset_right, hT₁i]
    rw [hT₁, Function.update_idem]
    congr 1
    ext
    · simp; ring
    · simp
  · rw [hT₁i]
    simp only
    rw [show (pre.length : ℤ) + u.length - 1 - j = (pre.length : ℤ) + ((u.length - 1 - j : ℕ) : ℤ)
      by omega,
      listCells_add, List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega)]
    exact hu _ (List.getElem_mem _)
  · rw [hT₁i]
    simp only
    rw [show (pre.length : ℤ) + u.length - 1 - u.length = (pre.length : ℤ) - 1 by ring]
    rcases List.eq_nil_or_concat pre with rfl | ⟨pre', b, rfl⟩
    · simpa [listCells_of_neg] using hpre
    · simp only [List.concat_eq_append] at hpre ⊢
      rw [show ((pre' ++ [b]).length : ℤ) - 1 = (pre'.length : ℤ) + ((0 : ℕ) : ℤ) by simp,
        List.append_assoc, listCells_add]
      simpa using hpre

/-- Move the head of tape `i` back to position `0`, over a blank-free prefix. -/
def rewind [DecidableEq Γ] (i : Fin k) : TM k Γ := backTo i fun a => decide (a ≠ blank)

theorem rewind_ofWord [DecidableEq Γ] (i : Fin k) {T : Tapes k Γ} {pre rest : List Γ}
    (hT : T i = .ofWord pre rest) (hpre : ∀ a ∈ pre, a ≠ blank) :
    (rewind i).RunsWithin T (2 * pre.length + 2) (update T i (.ofWord [] (pre ++ rest))) :=
  backTo_ofWord i _ (pre := []) (by simpa using hT) (by simpa using hpre) (by simp)

omit [TapeAlphabet Γ] in
lemma update_update_update_update {α : Type} {T : Fin k → α} {i j : Fin k} (hij : i ≠ j)
    (A B X Y : α) :
    update (update (update (update T i A) j B) i X) j Y = update (update T i X) j Y := by
  funext l
  by_cases hl : l = j
  · subst hl; simp
  · by_cases hl' : l = i
    · subst hl'; simp [Function.update_of_ne hl]
    · simp [Function.update_of_ne hl, Function.update_of_ne hl']

/-- Copy the symbols satisfying `p` from tape `i` (moving right) to tape `j` (moving
right), up to the first symbol on tape `i` violating `p`. -/
def copyR (i j : Fin k) (p : Γ → Bool) : TM k Γ :=
  loop (fun s => p (s i)) (act₂ i j fun a _ => ((a, .right), (a, .right)))

theorem copyR_ofWord {i j : Fin k} (hij : i ≠ j) (p : Γ → Bool) {T : Tapes k Γ}
    {pre u rest dpre drest : List Γ}
    (hTi : T i = .ofWord pre (u ++ rest)) (hu : ∀ a ∈ u, p a = true)
    (hr : p (rest.headD blank) = false) (hTj : T j = .ofWord dpre drest) :
    (copyR i j p).RunsWithin T (2 * u.length)
      (update (update T i (.ofWord (pre ++ u) rest)) j
        (.ofWord (dpre ++ u) (drest.drop u.length))) := by
  unfold copyR
  induction u generalizing pre dpre drest T with
  | nil =>
    refine (loop_runsWithin_exit
      (by simpa [readAll, hTi, Tape.read_ofWord] using hr)).congr_right ?_
    simp only [List.nil_append] at hTi
    simp [← hTi, ← hTj]
  | cons a u ih =>
    have h₁ := act₂_runsWithin hij (fun a _ => ((a, Move.right), (a, Move.right))) T
    simp only [hTi, hTj, List.cons_append, Tape.read_ofWord_cons, Tape.act_ofWord_right,
      List.tail_cons] at h₁
    have h₂ := ih (pre := pre ++ [a]) (dpre := dpre ++ [a]) (drest := drest.tail)
      (T := update (update T i (Tape.ofWord (pre ++ [a]) (u ++ rest))) j
        (Tape.ofWord (dpre ++ [a]) drest.tail))
      (by simp [Function.update_of_ne hij]) (fun b hb => hu b (by simp [hb])) (by simp)
    have h := loop_runsWithin_iter (c := fun s => p (s i))
      (by simpa [readAll, hTi] using hu a (by simp)) h₁ h₂
    refine (h.mono (by simp; omega)).congr_right ?_
    rw [update_update_update_update hij]
    congr 2
    · simp
    · simp
    · cases drest <;> simp

/-- Move left on tape `i`, erasing, while the scanned symbol is not blank. -/
def eraseL [DecidableEq Γ] (i : Fin k) : TM k Γ :=
  loop (fun s => decide (s i ≠ blank)) (actOn i fun _ => (blank, .left))

theorem eraseL_raw [DecidableEq Γ] (i : Fin k) (d : ℕ) (T : Tapes k Γ)
    (hd : ∀ j < d, (T i).cells ((T i).head - j) ≠ blank)
    (hend : (T i).cells ((T i).head - d) = blank) :
    (eraseL i).RunsWithin T (2 * d) (update T i ⟨(T i).head - d,
      fun z => if (T i).head - d < z ∧ z ≤ (T i).head then blank else (T i).cells z⟩) := by
  unfold eraseL
  induction d generalizing T with
  | zero =>
    refine (loop_runsWithin_exit (T := T)
      (by simp at hend; simp [readAll, Tape.read, hend])).congr_right ?_
    conv_lhs => rw [← Function.update_eq_self i T]
    congr 1
    ext z
    · simp
    · simp only [Nat.cast_zero, sub_zero]
      split_ifs with h
      · omega
      · rfl
  | succ d ih =>
    have h₁ := actOn_runsWithin i (fun _ => ((blank : Γ), Move.left)) T
    have := ih (update T i ((T i).act blank .left))
      (fun j hj => by
        have := hd (j + 1) (by omega)
        simp only [Function.update_self, Tape.act_head, Tape.act_cells, Move.offset_left]
        rw [Function.update_of_ne (by omega)]
        rw [show (T i).head + -1 - (j : ℤ) = (T i).head - ((j + 1 : ℕ) : ℤ) by push_cast; ring]
        exact this)
      (by
        simp only [Function.update_self, Tape.act_head, Tape.act_cells, Move.offset_left]
        rw [Function.update_of_ne (by omega)]
        rw [show (T i).head + -1 - (d : ℤ) = (T i).head - ((d + 1 : ℕ) : ℤ) by push_cast; ring]
        exact hend)
    have h := loop_runsWithin_iter (c := fun s => decide (s i ≠ blank))
      (by have := hd 0 (by omega); simp at this; simp [readAll, Tape.read, this]) h₁ this
    refine (h.mono (by omega)).congr_right ?_
    simp only [Function.update_idem, Function.update_self, Tape.act_head, Tape.act_cells,
      Move.offset_left]
    congr 1
    ext z
    · simp; ring
    · simp only [Function.update_apply]
      push_cast
      split_ifs <;> first | rfl | omega

/-- Erase the blank-free word on tape `i` and put the head on position `0`. -/
def erase [DecidableEq Γ] (i : Fin k) : TM k Γ :=
  scanR i (fun a => decide (a ≠ blank)) ;; moveL i ;; eraseL i ;; moveR i

theorem erase_ofWord [DecidableEq Γ] (i : Fin k) {T : Tapes k Γ} {pre rest : List Γ}
    (hT : T i = .ofWord pre rest) (hw : ∀ a ∈ pre ++ rest, a ≠ blank) :
    (erase i).RunsWithin T (2 * rest.length + 2 * (pre ++ rest).length + 2)
      (update T i (.ofWord [] [])) := by
  have h₁ := scanR_ofWord i (fun a => decide (a ≠ blank)) (T := T) (pre := pre) (u := rest)
    (rest := []) (by simpa using hT) (fun a ha => by simpa using hw a (by simp [ha])) (by simp)
  set w := pre ++ rest with hw'
  set T₁ := update T i (Tape.ofWord w []) with hT₁
  have h₂ := moveL_runsWithin i T₁
  set T₂ := update T₁ i ((T₁ i).move .left) with hT₂
  have hT₂i : T₂ i = ⟨(w.length : ℤ) - 1, listCells w⟩ := by
    rw [hT₂, Function.update_self, hT₁, Function.update_self]
    ext
    · simp; ring
    · simp
  have h₃ := eraseL_raw i w.length T₂ (fun j hj => ?_) ?_
  · have h₄ := moveR_runsWithin i (update T₂ i ⟨(T₂ i).head - w.length,
      fun z => if (T₂ i).head - w.length < z ∧ z ≤ (T₂ i).head then blank else (T₂ i).cells z⟩)
    refine ((seq_runsWithin (seq_runsWithin (seq_runsWithin h₁ h₂) h₃) h₄).mono
      (by omega)).congr_right ?_
    simp only [Function.update_idem, Function.update_self, Tape.move_head, Tape.move_cells,
      Move.offset_right, hT₂i]
    rw [hT₂, hT₁, Function.update_idem, Function.update_idem]
    congr 1
    ext z
    · simp
    · simp only [Tape.move_cells, Tape.ofWord_cells, List.append_nil, listCells_nil]
      split_ifs with h
      · rfl
      · rcases not_and_or.mp h with h | h
        · exact listCells_of_neg _ (by omega)
        · exact listCells_of_length_le _ (by omega)
  · rw [hT₂i]
    simp only
    rw [show (w.length : ℤ) - 1 - j = ((w.length - 1 - j : ℕ) : ℤ) by omega,
      listCells_of_lt _ (by omega)]
    exact hw _ (List.getElem_mem _)
  · rw [hT₂i]
    dsimp only
    exact listCells_of_neg _ (by omega)

end TM

end Lax119563Proofs.Machines
