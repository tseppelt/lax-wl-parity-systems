import Mathlib.Data.Nat.Size
import Lax119563Proofs.Machines.SortMain

/-!
# Further combinators and routines

* `TM.whileM test c body`: a loop whose condition is read after running a test machine
  (`test ;; loop c (body ;; test)`), with a lemma along a sequence of tape families.
* `TM.revCopy`: copy a word in reverse order onto the end of another tape (e.g. to turn the
  little-endian digits of a number into big-endian ones).
* `TM.sortRecords_onTapes`: the merge sort run on three tapes of a larger machine.
-/

open Lax489179.TuringMachine (Move)

namespace Lax119563Proofs.Machines

variable {Γ : Type} {k : ℕ}

open Function (update)

namespace TM

/-- `test; while c do (body; test)`. -/
def whileM (test : TM k Γ) (c : (Fin k → Γ) → Bool) (body : TM k Γ) : TM k Γ :=
  test ;; loop c (body ;; test)

/-- A `whileM` loop along tape families `f i` (before the test) and `g i` (after the test):
the condition holds after the first `n` tests and fails after the last one. -/
theorem whileM_runsWithin {test body : TM k Γ} {c : (Fin k → Γ) → Bool} (n : ℕ)
    (f g : ℕ → Tapes k Γ) (tt tb : ℕ → ℕ)
    (htest : ∀ i ≤ n, test.RunsWithin (f i) (tt i) (g i))
    (hc : ∀ i < n, c (readAll (g i)) = true) (hn : c (readAll (g n)) = false)
    (hbody : ∀ i < n, body.RunsWithin (g i) (tb i) (f (i + 1))) :
    (whileM test c body).RunsWithin (f 0)
      (tt 0 + ∑ i ∈ Finset.range n, (tb i + tt (i + 1) + 1)) (g n) :=
  seq_runsWithin (htest 0 (Nat.zero_le _))
    (loop_runsWithin n g (fun i => tb i + tt (i + 1)) hc hn
      (fun i hi => seq_runsWithin (hbody i hi) (htest (i + 1) hi)))

/-- `whileM` with uniform time bounds. -/
theorem whileM_runsWithin_const {test body : TM k Γ} {c : (Fin k → Γ) → Bool} (n : ℕ)
    (f g : ℕ → Tapes k Γ) (tt tb : ℕ)
    (htest : ∀ i ≤ n, test.RunsWithin (f i) tt (g i))
    (hc : ∀ i < n, c (readAll (g i)) = true) (hn : c (readAll (g n)) = false)
    (hbody : ∀ i < n, body.RunsWithin (g i) tb (f (i + 1))) :
    (whileM test c body).RunsWithin (f 0) (tt + n * (tb + tt + 1)) (g n) := by
  simpa using whileM_runsWithin n f g (fun _ => tt) (fun _ => tb) htest hc hn hbody

variable [TapeAlphabet Γ]

/-- Copy, moving left on tape `i` and right on tape `j`, while `p` holds on tape `i`. -/
def copyLR (i j : Fin k) (p : Γ → Bool) : TM k Γ :=
  loop (fun s => p (s i)) (act₂ i j fun a _ => ((a, .left), (a, .right)))


/-- The `d` cells at and to the left of the head, read from right to left. -/
def _root_.Lax119563Proofs.Machines.Tape.leftWord (t : Tape Γ) : ℕ → List Γ
  | 0 => []
  | d + 1 => t.read :: Tape.leftWord ⟨t.head - 1, t.cells⟩ d

omit [TapeAlphabet Γ] in
theorem copyLR_spec [TapeAlphabet Γ] {i j : Fin k} (hij : i ≠ j) (p : Γ → Bool) (d : ℕ)
    (T : Tapes k Γ) (dpre : List Γ) (hTj : T j = .ofWord dpre [])
    (hd : ∀ a ∈ (T i).leftWord d, p a = true)
    (hend : p ((T i).cells ((T i).head - d)) = false) :
    (copyLR i j p).RunsWithin T (2 * d)
      (update (update T i ⟨(T i).head - d, (T i).cells⟩) j
        (.ofWord (dpre ++ (T i).leftWord d) [])) := by
  unfold copyLR
  induction d generalizing T dpre with
  | zero =>
    refine (loop_runsWithin_exit (by simpa [readAll, Tape.read] using hend)).congr_right ?_
    funext l
    by_cases hl : l = j
    · subst hl; simp [hTj, Tape.leftWord]
    · by_cases hl' : l = i
      · subst hl'; simp [Function.update_of_ne hl]
      · simp [Function.update_of_ne hl, Function.update_of_ne hl']
  | succ d ih =>
    have h₁ := act₂_runsWithin hij (fun a _ => ((a, Move.left), (a, Move.right))) T
    simp only [hTj, Tape.act_ofWord_right, List.tail_nil] at h₁
    have hact : (T i).act (T i).read .left = ⟨(T i).head - 1, (T i).cells⟩ := by
      ext
      · simp; ring
      · simp [Tape.read]
    rw [hact] at h₁
    set T' := update (update T i ⟨(T i).head - 1, (T i).cells⟩) j
      (Tape.ofWord (dpre ++ [(T i).read]) [])
    have hT'i : T' i = ⟨(T i).head - 1, (T i).cells⟩ := by
      simp [T', Function.update_of_ne hij]
    have h₂ := ih T' (dpre ++ [(T i).read]) (by simp [T'])
      (fun a ha => hd a (by rw [hT'i] at ha; simp [Tape.leftWord, ha]))
      (by
        rw [hT'i]
        simp only
        rw [show (T i).head - 1 - (d : ℤ) = (T i).head - ((d + 1 : ℕ) : ℤ) by push_cast; ring]
        exact hend)
    have h := loop_runsWithin_iter (c := fun s => p (s i))
      (by simpa [readAll, Tape.leftWord] using hd (T i).read (by simp [Tape.leftWord])) h₁ h₂
    refine (h.mono (by omega)).congr_right ?_
    rw [hT'i, update_update_update_update hij]
    congr 2
    · rw [show (T i).head - 1 - (d : ℤ) = (T i).head - ((d + 1 : ℕ) : ℤ) by push_cast; ring]
    · simp [Tape.leftWord]

lemma leftWord_ofWord (pre u rest : List Γ) :
    (⟨((pre ++ u).length : ℤ) - 1, listCells (pre ++ u ++ rest)⟩ : Tape Γ).leftWord u.length =
      u.reverse := by
  induction u using List.reverseRecOn generalizing rest with
  | nil => rfl
  | append_singleton u x ih =>
    have := ih (x :: rest)
    rw [List.length_append (as := u) (bs := [x]), List.length_singleton, List.reverse_append,
      List.reverse_singleton, List.singleton_append, Tape.leftWord]
    congr 1
    · simp only [Tape.read]
      rw [show ((pre ++ (u ++ [x])).length : ℤ) - 1 = ((pre ++ u).length : ℤ) + ((0 : ℕ) : ℤ) by
        simp; ring, show pre ++ (u ++ [x]) ++ rest = (pre ++ u) ++ (x :: rest) by simp,
        listCells_add]
      simp
    · convert this using 3
      · simp; ring
      · simp

/-- Append the word `u` just left of the head of tape `i` (preceded by a symbol violating `p`
or by the left end) in reverse order to tape `j`; the head of tape `i` ends on the first
symbol of `u`. -/
def revCopy (i j : Fin k) (p : Γ → Bool) : TM k Γ := moveL i ;; copyLR i j p ;; moveR i

theorem revCopy_ofWord {i j : Fin k} (hij : i ≠ j) (p : Γ → Bool) {T : Tapes k Γ}
    {pre u rest dpre : List Γ} (hTi : T i = .ofWord (pre ++ u) rest)
    (hu : ∀ a ∈ u, p a = true) (hpre : p (pre.getLast?.getD blank) = false)
    (hTj : T j = .ofWord dpre []) :
    (revCopy i j p).RunsWithin T (2 * u.length + 2)
      (update (update T i (.ofWord pre (u ++ rest))) j (.ofWord (dpre ++ u.reverse) [])) := by
  have h₁ := moveL_runsWithin i T
  set T₁ := update T i ((T i).move .left) with hT₁
  have hT₁i : T₁ i = ⟨((pre ++ u).length : ℤ) - 1, listCells (pre ++ u ++ rest)⟩ := by
    rw [hT₁, Function.update_self, hTi]
    ext
    · simp; ring
    · simp
  have h₂ := copyLR_spec hij p u.length T₁ dpre (by simp [T₁, Function.update_of_ne hij.symm, hTj])
    (by rw [hT₁i, leftWord_ofWord]; intro a ha; exact hu a (List.mem_reverse.mp ha))
    (by
      rw [hT₁i]; simp only
      rw [show ((pre ++ u).length : ℤ) - 1 - u.length = (pre.length : ℤ) - 1 by simp; ring]
      rcases List.eq_nil_or_concat pre with rfl | ⟨pre', b, rfl⟩
      · simpa [listCells_of_neg] using hpre
      · simp only [List.concat_eq_append] at hpre ⊢
        rw [show ((pre' ++ [b]).length : ℤ) - 1 = (pre'.length : ℤ) + ((0 : ℕ) : ℤ) by simp,
          show pre' ++ [b] ++ u ++ rest = pre' ++ (b :: (u ++ rest)) by simp, listCells_add]
        simpa using hpre)
  rw [hT₁i, leftWord_ofWord] at h₂
  have h₃ := moveR_runsWithin i (update (update T₁ i
    ⟨((pre ++ u).length : ℤ) - 1 - u.length, listCells (pre ++ u ++ rest)⟩) j
      (Tape.ofWord (dpre ++ u.reverse) []))
  refine ((seq_runsWithin (seq_runsWithin h₁ h₂) h₃).mono (by omega)).congr_right ?_
  funext l
  by_cases hl : l = i
  · subst hl
    simp only [Function.update_self, Function.update_of_ne hij]
    ext
    · simp; ring
    · simp
  · by_cases hl' : l = j
    · subst hl'; simp [Function.update_of_ne hl]
    · simp [Function.update_of_ne hl, Function.update_of_ne hl', T₁]

/-- The merge sort run on the tapes `σ 0, σ 1, σ 2` of a larger machine. -/
theorem sortRecords_onTapes [DecidableEq Γ] (S : Seps Γ) (σ : Fin 3 ↪ Fin k)
    (rs : List (List Bool)) {U : Tapes k Γ} (h₀ : U (σ 0) = .ofWord [] (recWord S rs))
    (h₁ : U (σ 1) = .ofWord [] []) (h₂ : U (σ 2) = .ofWord [] []) :
    (onTapes σ (sortRecords S)).RunsWithin U
      (48 * ((recWord S rs).length + 1) * (Nat.clog 2 rs.length + 1))
      (updateTapes σ U (tapes3 (.ofWord [] (recWord S (rs.mergeSort recLE))) (.ofWord [] [])
        (.ofWord [] []))) := by
  apply onTapes_runsWithin
  convert sortRecords_spec S rs using 2
  funext i
  fin_cases i <;> simp [tapes3, h₀, h₁, h₂]

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
