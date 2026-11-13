import Lax119563Proofs.Machines.SortPass

/-!
# Merge sort on tapes

`TM.sortRecords S` sorts the records on tape `0` (each record a bit string followed by
`S.hash`, head on position `0`) using two empty work tapes `1` and `2`. It leaves the records
sorted by `recLE` (that is, `List.mergeSort` with `recLE`) on tape `0` and the work tapes
empty, within `48 (L + 1) (⌈log₂ m⌉ + 1)` transitions for `m` records of total encoded length
`L` (`TM.sortRecords_spec`). Use `TM.onTapes` to run it on three tapes of a larger machine.
-/

open Lax489179.TuringMachine (Move)

namespace Lax119563Proofs.Machines

variable {Γ : Type} [TapeAlphabet Γ]

open Function (update)

variable (S : Seps Γ)

/-- The data tape after the test for a second run: the head after the first `bar`. -/
def testState : List (List (List Bool)) → Tape Γ
  | [] => .ofWord [] []
  | r :: R => .ofWord (recWord S r ++ [S.bar]) (runsWord S R)

lemma testState_read [DecidableEq Γ] (R : List (List (List Bool))) :
    decide ((testState S R).read ≠ blank) = decide (2 ≤ R.length) := by
  match R with
  | [] => simp [testState]
  | [r] => simp [testState]
  | r :: r' :: R =>
    have h := read_recWord_bar S (recWord S r ++ [S.bar]) r' (runsWord S R)
    simpa [testState] using h

lemma runsWord_sortRuns_length (R : List (List (List Bool))) :
    (runsWord S (sortRuns R)).length ≤ (runsWord S R).length := by
  induction R using sortRuns.induct with
  | case1 R h => rw [sortRuns, dif_pos h]
  | case2 R h ih =>
    rw [sortRuns, dif_neg h]
    exact ih.trans (runsWord_mergePass_length S R)

lemma length_le_recWord_length (rs : List (List Bool)) : rs.length ≤ (recWord S rs).length := by
  induction rs with
  | nil => simp
  | cons r rs ih => simp; omega

lemma runsWord_singletons (rs : List (List Bool)) :
    runsWord S (rs.map fun r => [r]) = rs.flatMap fun r => bitsWord r ++ [S.hash, S.bar] := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [ih]

lemma runsWord_singletons_length (rs : List (List Bool)) :
    (runsWord S (rs.map fun r => [r])).length ≤ 2 * (recWord S rs).length := by
  have h₂ : (rs.map fun r => [r]).flatten = rs := by induction rs <;> simp_all
  have h₁ := runsWord_length S (rs.map fun r => [r])
  rw [h₂, List.length_map] at h₁
  have := length_le_recWord_length S rs
  omega

namespace TM

variable [DecidableEq Γ]

/-- Move the head of tape `0` past the first run, if any. -/
def testRuns : TM 3 Γ :=
  scanR 0 (fun a => decide (a ≠ S.bar ∧ a ≠ blank)) ;;
    ite (fun s => decide (s 0 = S.bar)) (moveR 0) nop

theorem testRuns_spec (R : List (List (List Bool))) (b c : Tape Γ) :
    (testRuns S).RunsWithin (tapes3 (.ofWord [] (runsWord S R)) b c)
      (2 * (runsWord S R).length + 1) (tapes3 (testState S R) b c) := by
  cases R with
  | nil =>
    have h₁ := scanR_ofWord 0 (fun a => decide (a ≠ S.bar ∧ a ≠ blank))
      (T := tapes3 (.ofWord [] (runsWord S [])) b c) (pre := []) (u := []) (rest := [])
      (by simp) (by simp) (by simp)
    simp only [update_tapes3_zero, List.append_nil] at h₁
    have h₂ := ite_runsWithin_false (c := fun s => decide (s 0 = S.bar)) (M₁ := moveR 0)
      (T := tapes3 (.ofWord [] []) b c) (by simp [S.bar_ne_blank.symm])
      (nop_haltsIn _).runsWithin
    exact ((seq_runsWithin h₁ h₂).mono (by simp)).congr_right (by simp [testState])
  | cons r R =>
    have h₁ := scanR_ofWord 0 (fun a => decide (a ≠ S.bar ∧ a ≠ blank))
      (T := tapes3 (.ofWord [] (runsWord S (r :: R))) b c) (pre := []) (u := recWord S r)
      (rest := S.bar :: runsWord S R) (by simp)
      (fun a ha => by simpa using And.intro (recWord_ne_bar S ha) (recWord_ne_blank S ha))
      (by simp)
    simp only [update_tapes3_zero, List.nil_append] at h₁
    have h₂ := moveR_runsWithin 0 (tapes3 (.ofWord (recWord S r) (S.bar :: runsWord S R)) b c)
    simp only [tapes3_zero, Tape.move_ofWord_right, update_tapes3_zero] at h₂
    have h₃ := ite_runsWithin_true (c := fun s => decide (s 0 = S.bar)) (M₂ := nop)
      (T := tapes3 (.ofWord (recWord S r) (S.bar :: runsWord S R)) b c) (by simp) h₂
    exact ((seq_runsWithin h₁ h₃).mono (by simp)).congr_right (by simp [testState])

theorem rewind_testState (R : List (List (List Bool))) (b c : Tape Γ) :
    (rewind 0).RunsWithin (tapes3 (testState S R) b c) (2 * (runsWord S R).length + 2)
      (tapes3 (.ofWord [] (runsWord S R)) b c) := by
  cases R with
  | nil =>
    exact ((rewind_ofWord 0 (T := tapes3 (testState S []) b c) (pre := []) (rest := [])
      (by simp [testState]) (by simp)).mono (by simp)).congr_right (by simp)
  | cons r R =>
    refine ((rewind_ofWord 0 (T := tapes3 (testState S (r :: R)) b c)
      (pre := recWord S r ++ [S.bar]) (rest := runsWord S R) (by simp [testState])
      (fun a ha => runsWord_ne_blank S (R := [r]) (by simpa using ha))).mono
      (by simp)).congr_right (by simp)

/-- Merge passes while tape `0` holds at least two runs. -/
def mainLoop : TM 3 Γ :=
  loop (fun s => decide (s 0 ≠ blank)) (rewind 0 ;; pass S ;; testRuns S)

theorem mainLoop_spec (L₀ : ℕ) (R : List (List (List Bool))) (hR : (runsWord S R).length ≤ L₀) :
    (mainLoop S).RunsWithin (tapes3 (testState S R) (.ofWord [] []) (.ofWord [] []))
      (numPasses R * (24 * L₀ + 24))
      (tapes3 (testState S (sortRuns R)) (.ofWord [] []) (.ofWord [] [])) := by
  unfold mainLoop
  induction R using numPasses.induct with
  | case1 R h =>
    rw [numPasses, dif_pos h, sortRuns, dif_pos h]
    have hc : decide ((testState S R).read ≠ blank) = false := by
      rw [testState_read]; simp; omega
    exact loop_runsWithin_exit (c := fun s => decide (s 0 ≠ blank))
      (B := rewind 0 ;; pass S ;; testRuns S)
      (T := tapes3 (testState S R) (.ofWord [] []) (.ofWord [] [])) hc |>.mono (by simp)
  | case2 R h ih =>
    rw [numPasses, dif_neg h, sortRuns, dif_neg h]
    have hM := runsWord_mergePass_length S R
    have h₁ := rewind_testState S R (.ofWord [] []) (.ofWord [] [])
    have h₂ := pass_spec S R
    have h₃ := testRuns_spec S (mergePass R) (.ofWord [] []) (.ofWord [] [])
    have h₄ := ih (hM.trans hR)
    have hc : decide ((testState S R).read ≠ blank) = true := by
      rw [testState_read]; simp; omega
    have := loop_runsWithin_iter (c := fun s => decide (s 0 ≠ blank))
      (T := tapes3 (testState S R) (.ofWord [] []) (.ofWord [] [])) hc
      (seq_runsWithin (seq_runsWithin h₁ h₂) h₃) h₄
    refine this.mono ?_
    have : numPasses (mergePass R) * (24 * L₀ + 24) + (24 * L₀ + 24) =
      (numPasses (mergePass R) + 1) * (24 * L₀ + 24) := by ring
    omega

/-- Copy each record of tape `0` to tape `1`, followed by `bar`. -/
def initLoop : TM 3 Γ :=
  loop (fun s => decide (s 0 ≠ blank)) (copyRec S 0 1 ;; writeR 1 S.bar)

theorem initLoop_spec (rs : List (List Bool)) : ∀ (PA PB : List Γ) (c : Tape Γ),
    (initLoop S).RunsWithin (tapes3 (.ofWord PA (recWord S rs)) (.ofWord PB []) c)
      (3 * (recWord S rs).length)
      (tapes3 (.ofWord (PA ++ recWord S rs) []) (.ofWord (PB ++ runsWord S (rs.map fun r => [r])) [])
        c) := by
  induction rs with
  | nil => intro PA PB c; exact (loop_runsWithin_exit (by simp)).congr_right (by simp)
  | cons r rs ih =>
    intro PA PB c
    have h₁ := copyRec_ofWord S (show (0 : Fin 3) ≠ 1 by decide) r
      (T := tapes3 (.ofWord PA (recWord S (r :: rs))) (.ofWord PB []) c) (pre := PA)
      (rest := recWord S rs) (dpre := PB) (by simp) (by simp)
    simp only [update_tapes3_zero, update_tapes3_one] at h₁
    have h₂ := writeR_runsWithin 1 S.bar (tapes3 (.ofWord (PA ++ bitsWord r ++ [S.hash]) (recWord S rs))
      (.ofWord (PB ++ bitsWord r ++ [S.hash]) []) c)
    simp only [tapes3_one, Tape.act_ofWord_right, List.tail_nil, update_tapes3_one] at h₂
    have h₃ := ih (PA ++ bitsWord r ++ [S.hash]) (PB ++ bitsWord r ++ [S.hash] ++ [S.bar]) c
    have hr := read_rec_ne_blank S PA r (recWord S rs)
    have h := loop_runsWithin_iter (c := fun s => decide (s 0 ≠ blank)) (by simp [hr])
      (seq_runsWithin h₁ h₂) h₃
    exact (h.mono (by simp [bitsWord]; omega)).congr_right (by simp)

/-- Turn the records on tape `0` into singleton runs. -/
def initRuns : TM 3 Γ :=
  initLoop S ;; erase 0 ;; rewind 1 ;; copyR 1 0 (fun a => decide (a ≠ blank)) ;; erase 1 ;;
    rewind 0

theorem initRuns_spec (rs : List (List Bool)) :
    (initRuns S).RunsWithin (tapes3 (.ofWord [] (recWord S rs)) (.ofWord [] []) (.ofWord [] []))
      (21 * (recWord S rs).length + 8)
      (tapes3 (.ofWord [] (runsWord S (rs.map fun r => [r]))) (.ofWord [] []) (.ofWord [] [])) := by
  have hW := runsWord_singletons_length S rs
  set W := runsWord S (rs.map fun r => [r])
  have hbf : ∀ a ∈ W, a ≠ blank := runsWord_blank_free S _
  have h₁ := initLoop_spec S rs [] [] (.ofWord [] [])
  simp only [List.nil_append] at h₁
  have h₂ := erase_ofWord 0 (T := tapes3 (.ofWord (recWord S rs) []) (.ofWord W []) (.ofWord [] []))
    (pre := recWord S rs) (rest := []) (by simp)
    (by simpa using fun a ha => recWord_ne_blank S ha)
  simp only [update_tapes3_zero, List.append_nil, List.length_nil] at h₂
  have h₃ := rewind_ofWord 1 (T := tapes3 (.ofWord [] []) (.ofWord W []) (.ofWord [] []))
    (pre := W) (rest := []) (by simp) hbf
  simp only [update_tapes3_one, List.append_nil] at h₃
  have h₄ := copyR_ofWord (show (1 : Fin 3) ≠ 0 by decide) (fun a => decide (a ≠ blank))
    (T := tapes3 (.ofWord [] []) (.ofWord [] W) (.ofWord [] [])) (pre := []) (u := W) (rest := [])
    (dpre := []) (drest := []) (by simp) (fun a ha => by simpa using hbf a ha) (by simp) (by simp)
  simp only [update_tapes3_one, update_tapes3_zero, List.nil_append, List.drop_nil] at h₄
  have h₅ := erase_ofWord 1 (T := tapes3 (.ofWord W []) (.ofWord W []) (.ofWord [] []))
    (pre := W) (rest := []) (by simp) (by simpa using hbf)
  simp only [update_tapes3_one, List.append_nil, List.length_nil] at h₅
  have h₆ := rewind_ofWord 0 (T := tapes3 (.ofWord W []) (.ofWord [] []) (.ofWord [] []))
    (pre := W) (rest := []) (by simp) hbf
  simp only [update_tapes3_zero, List.append_nil] at h₆
  exact (seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin h₁ h₂) h₃)
    h₄) h₅) h₆).mono (by simp; omega)

/-- Remove the final `bar` of a single run on tape `0` (head on position `0`). -/
def stripRun : TM 3 Γ :=
  scanR 0 (fun a => decide (a ≠ S.bar ∧ a ≠ blank)) ;; write 0 blank ;; rewind 0

theorem stripRun_spec (R : List (List (List Bool))) (hR : R.length ≤ 1) (b c : Tape Γ) :
    (stripRun S).RunsWithin (tapes3 (.ofWord [] (runsWord S R)) b c)
      (4 * (runsWord S R).length + 3) (tapes3 (.ofWord [] (recWord S R.flatten)) b c) := by
  match R, hR with
  | [], _ =>
    have h₁ := scanR_ofWord 0 (fun a => decide (a ≠ S.bar ∧ a ≠ blank))
      (T := tapes3 (.ofWord [] (runsWord S [])) b c) (pre := []) (u := []) (rest := [])
      (by simp) (by simp) (by simp)
    simp only [update_tapes3_zero, List.append_nil] at h₁
    have h₂ := write_runsWithin 0 blank (tapes3 (.ofWord [] []) b c)
    simp only [tapes3_zero, Tape.act_ofWord_stay, List.tail_nil, Tape.ofWord_nil_blank,
      update_tapes3_zero] at h₂
    have h₃ := rewind_ofWord 0 (T := tapes3 (.ofWord [] []) b c) (pre := []) (rest := [])
      (by simp) (by simp)
    simp only [update_tapes3_zero, List.append_nil] at h₃
    exact ((seq_runsWithin (seq_runsWithin h₁ h₂) h₃).mono (by simp)).congr_right (by simp)
  | [r], _ =>
    have h₁ := scanR_ofWord 0 (fun a => decide (a ≠ S.bar ∧ a ≠ blank))
      (T := tapes3 (.ofWord [] (runsWord S [r])) b c) (pre := []) (u := recWord S r)
      (rest := [S.bar]) (by simp)
      (fun a ha => by simpa using And.intro (recWord_ne_bar S ha) (recWord_ne_blank S ha))
      (by simp)
    simp only [update_tapes3_zero, List.nil_append] at h₁
    have h₂ := write_runsWithin 0 blank (tapes3 (.ofWord (recWord S r) [S.bar]) b c)
    simp only [tapes3_zero, Tape.act_ofWord_stay, List.tail_cons, Tape.ofWord_nil_blank,
      update_tapes3_zero] at h₂
    have h₃ := rewind_ofWord 0 (T := tapes3 (.ofWord (recWord S r) []) b c) (pre := recWord S r)
      (rest := []) (by simp) (fun a ha => recWord_ne_blank S ha)
    simp only [update_tapes3_zero, List.append_nil] at h₃
    exact ((seq_runsWithin (seq_runsWithin h₁ h₂) h₃).mono (by simp; omega)).congr_right
      (by simp)

/-- Sort the records on tape `0`, using the empty tapes `1` and `2`. -/
def sortRecords : TM 3 Γ :=
  initRuns S ;; testRuns S ;; mainLoop S ;; rewind 0 ;; stripRun S

/-- **Merge sort on tapes.** -/
theorem sortRecords_spec (rs : List (List Bool)) :
    (sortRecords S).RunsWithin (tapes3 (.ofWord [] (recWord S rs)) (.ofWord [] []) (.ofWord [] []))
      (48 * ((recWord S rs).length + 1) * (Nat.clog 2 rs.length + 1))
      (tapes3 (.ofWord [] (recWord S (rs.mergeSort recLE))) (.ofWord [] []) (.ofWord [] [])) := by
  set R₀ := rs.map fun r => [r]
  set L := (recWord S rs).length
  set W := (runsWord S R₀).length
  have hW : W ≤ 2 * L := runsWord_singletons_length S rs
  have h₁ := initRuns_spec S rs
  have h₂ := testRuns_spec S R₀ (.ofWord [] []) (.ofWord [] [])
  have h₃ := mainLoop_spec S W R₀ le_rfl
  have h₄ := rewind_testState S (sortRuns R₀) (.ofWord [] []) (.ofWord [] [])
  have hR₀ : RunsSorted R₀ := by
    intro r hr
    simp only [R₀, List.mem_map] at hr
    obtain ⟨a, -, rfl⟩ := hr
    simp
  have hR := sortRuns_spec R₀ hR₀
  have h₅ := stripRun_spec S (sortRuns R₀) hR.1 (.ofWord [] []) (.ofWord [] [])
  have hS := runsWord_sortRuns_length S R₀
  have hnp : numPasses R₀ ≤ Nat.clog 2 rs.length := by
    simpa [R₀] using numPasses_le R₀
  have hsort : (sortRuns R₀).flatten = rs.mergeSort recLE := sortRecs_eq rs
  rw [hsort] at h₅
  refine (seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin h₁ h₂) h₃) h₄) h₅).mono ?_
  have hmul : numPasses R₀ * (24 * W + 24) ≤ Nat.clog 2 rs.length * (48 * L + 48) :=
    Nat.mul_le_mul hnp (by omega)
  have : 48 * (L + 1) * (Nat.clog 2 rs.length + 1) =
    Nat.clog 2 rs.length * (48 * L + 48) + 48 * L + 48 := by ring
  rw [this]
  omega

end TM

end Lax119563Proofs.Machines
