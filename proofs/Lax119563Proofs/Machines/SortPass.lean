import Lax119563Proofs.Machines.SortMerge

/-!
# Merge sort on tapes: one pass

`mergeAll` merges the runs of tapes `1` and `2` pairwise onto tape `0`; `pass` distributes
the runs of tape `0` to tapes `1` and `2`, merges them back, and cleans up, implementing
`mergePass` in time linear in the length of the encoding.
-/

open Lax489179.TuringMachine (Move)

namespace Lax119563Proofs.Machines

variable {Γ : Type} [TapeAlphabet Γ]

open Function (update)

variable (S : Seps Γ)

lemma inRec_last_bar [DecidableEq Γ] (P : List Γ) :
    inRec S ((P ++ [S.bar]).getLast?.getD blank) = false := by
  simp [inRec]

lemma runsWord_append (R R' : List (List (List Bool))) :
    runsWord S (R ++ R') = runsWord S R ++ runsWord S R' := by simp [runsWord]

lemma runsWord_deal_length (R : List (List (List Bool))) :
    (runsWord S (deal R).1).length + (runsWord S (deal R).2).length = (runsWord S R).length := by
  rw [← List.length_append, ← runsWord_append, runsWord_length, runsWord_length,
    recWord_length_perm S (deal_perm R).flatten, (deal_perm R).length_eq]

lemma runsWord_blank_free (R : List (List (List Bool))) : ∀ a ∈ runsWord S R, a ≠ blank :=
  fun _ ha => runsWord_ne_blank S ha

namespace TM

variable [DecidableEq Γ]

/-- Merge the runs of tapes `1` and `2` pairwise onto the end of tape `0`. -/
def mergeAll : TM 3 Γ :=
  loop (fun s => decide (s 1 ≠ blank))
    (mergeRuns S ;; writeR 0 S.bar ;; moveR 1 ;;
      ite (fun s => decide (s 2 = S.bar)) (moveR 2) nop)

theorem mergeAll_spec (RB : List (List (List Bool))) : ∀ (RC : List (List (List Bool)))
    (PA PB PC : List Γ), RC.length ≤ RB.length → RB.length ≤ RC.length + 1 →
    inRec S (PB.getLast?.getD blank) = false →
    inRec S (PC.getLast?.getD blank) = false →
    (mergeAll S).RunsWithin
      (tapes3 (.ofWord PA []) (.ofWord PB (runsWord S RB)) (.ofWord PC (runsWord S RC)))
      (9 * ((runsWord S RB).length + (runsWord S RC).length))
      (tapes3 (.ofWord (PA ++ runsWord S (zipMerge RB RC)) []) (.ofWord (PB ++ runsWord S RB) [])
        (.ofWord (PC ++ runsWord S RC) [])) := by
  induction RB with
  | nil =>
    intro RC PA PB PC h₁ _ _ _
    have : RC = [] := List.eq_nil_of_length_eq_zero (by simpa using h₁)
    subst this
    exact ((loop_runsWithin_exit (by simp)).mono (Nat.zero_le _)).congr_right (by simp [zipMerge])
  | cons rb RB ih =>
    intro RC PA PB PC h₁ h₂ hPB hPC
    cases RC with
    | nil =>
      have hRB : RB = [] := List.eq_nil_of_length_eq_zero (by simpa using h₂)
      subst hRB
      have hm := mergeRuns_spec S rb [] PA PB PC [] [] hPB hPC (by simp)
      simp only [recWord_nil, List.append_nil, runsWord_cons, runsWord_nil, List.merge_right] at hm ⊢
      have hw := writeR_runsWithin 0 S.bar
        (tapes3 (.ofWord (PA ++ recWord S rb) []) (.ofWord (PB ++ recWord S rb) [S.bar]) (.ofWord PC []))
      simp only [tapes3_zero, Tape.act_ofWord_right, List.tail_nil, update_tapes3_zero] at hw
      have hmv := moveR_runsWithin 1
        (tapes3 (.ofWord (PA ++ recWord S rb ++ [S.bar]) []) (.ofWord (PB ++ recWord S rb) [S.bar])
          (.ofWord PC []))
      simp only [tapes3_one, Tape.move_ofWord_right, update_tapes3_one] at hmv
      have hite := ite_runsWithin_false (c := fun s => decide (s 2 = S.bar)) (M₁ := moveR 2)
        (T := tapes3 (.ofWord (PA ++ recWord S rb ++ [S.bar]) [])
          (.ofWord (PB ++ recWord S rb ++ [S.bar]) []) (.ofWord PC []))
        (by simp [S.bar_ne_blank.symm]) (nop_haltsIn _).runsWithin
      have hexit := loop_runsWithin_exit (c := fun s => decide (s 1 ≠ blank))
        (B := mergeRuns S ;; writeR 0 S.bar ;; moveR 1 ;;
          ite (fun s => decide (s 2 = S.bar)) (moveR 2) nop)
        (T := tapes3 (.ofWord (PA ++ recWord S rb ++ [S.bar]) [])
          (.ofWord (PB ++ recWord S rb ++ [S.bar]) []) (.ofWord PC [])) (by simp)
      have h := loop_runsWithin_iter (by simp [read_recWord_bar S PB rb []])
        (seq_runsWithin (seq_runsWithin (seq_runsWithin hm hw) hmv) hite) hexit
      refine (h.mono (by simp; omega)).congr_right (by simp [zipMerge, runsWord])
    | cons rc RC =>
      simp only [List.length_cons] at h₁ h₂
      have hm := mergeRuns_spec S rb rc PA PB PC (runsWord S RB) (S.bar :: runsWord S RC) hPB hPC
        (by simp)
      have hw := writeR_runsWithin 0 S.bar
        (tapes3 (.ofWord (PA ++ recWord S (List.merge rb rc recLE)) [])
          (.ofWord (PB ++ recWord S rb) (S.bar :: runsWord S RB))
          (.ofWord (PC ++ recWord S rc) (S.bar :: runsWord S RC)))
      simp only [tapes3_zero, Tape.act_ofWord_right, List.tail_nil, update_tapes3_zero] at hw
      have hmv := moveR_runsWithin 1
        (tapes3 (.ofWord (PA ++ recWord S (List.merge rb rc recLE) ++ [S.bar]) [])
          (.ofWord (PB ++ recWord S rb) (S.bar :: runsWord S RB))
          (.ofWord (PC ++ recWord S rc) (S.bar :: runsWord S RC)))
      simp only [tapes3_one, Tape.move_ofWord_right, update_tapes3_one] at hmv
      have hmv₂ := moveR_runsWithin 2
        (tapes3 (.ofWord (PA ++ recWord S (List.merge rb rc recLE) ++ [S.bar]) [])
          (.ofWord (PB ++ recWord S rb ++ [S.bar]) (runsWord S RB))
          (.ofWord (PC ++ recWord S rc) (S.bar :: runsWord S RC)))
      simp only [tapes3_two, Tape.move_ofWord_right, update_tapes3_two] at hmv₂
      have hite := ite_runsWithin_true (c := fun s => decide (s 2 = S.bar)) (M₂ := nop)
        (by simp) hmv₂
      have hrest := ih RC (PA ++ recWord S (List.merge rb rc recLE) ++ [S.bar])
        (PB ++ recWord S rb ++ [S.bar]) (PC ++ recWord S rc ++ [S.bar]) (by omega) (by omega)
        (inRec_last_bar S _) (inRec_last_bar S _)
      have h := loop_runsWithin_iter (by simp [read_recWord_bar S PB rb (runsWord S RB)])
        (seq_runsWithin (seq_runsWithin (seq_runsWithin hm hw) hmv) hite) hrest
      simp only [runsWord_cons, zipMerge]
      refine (h.mono (by simp; omega)).congr_right (by simp)

/-- One merge pass over the runs on tape `0`; tapes `1` and `2` are empty before and after. -/
def pass : TM 3 Γ :=
  distribute S ;; rewind 1 ;; rewind 2 ;; erase 0 ;; mergeAll S ;; erase 1 ;; erase 2 ;; rewind 0

theorem pass_spec (R : List (List (List Bool))) :
    (pass S).RunsWithin
      (tapes3 (.ofWord [] (runsWord S R)) (.ofWord [] []) (.ofWord [] []))
      (20 * (runsWord S R).length + 20)
      (tapes3 (.ofWord [] (runsWord S (mergePass R))) (.ofWord [] []) (.ofWord [] [])) := by
  have hbf := runsWord_blank_free S
  have hL := runsWord_deal_length S R
  have hM := runsWord_mergePass_length S R
  have hd := deal_length R
  have h₁ := distribute_spec S R [] [] []
  simp only [List.nil_append] at h₁
  have h₂ := rewind_ofWord 1 (T := tapes3 (.ofWord (runsWord S R) [])
    (.ofWord (runsWord S (deal R).1) []) (.ofWord (runsWord S (deal R).2) []))
    (pre := runsWord S (deal R).1) (rest := []) (by simp) (hbf _)
  simp only [update_tapes3_one, List.append_nil] at h₂
  have h₃ := rewind_ofWord 2 (T := tapes3 (.ofWord (runsWord S R) [])
    (.ofWord [] (runsWord S (deal R).1)) (.ofWord (runsWord S (deal R).2) []))
    (pre := runsWord S (deal R).2) (rest := []) (by simp) (hbf _)
  simp only [update_tapes3_two, List.append_nil] at h₃
  have h₄ := erase_ofWord 0 (T := tapes3 (.ofWord (runsWord S R) [])
    (.ofWord [] (runsWord S (deal R).1)) (.ofWord [] (runsWord S (deal R).2)))
    (pre := runsWord S R) (rest := []) (by simp) (by simpa using hbf R)
  simp only [update_tapes3_zero, List.append_nil, List.length_nil] at h₄
  have h₅ := mergeAll_spec S (deal R).1 (deal R).2 [] [] [] (by omega) (by omega)
    (by simp [inRec]) (by simp [inRec])
  simp only [List.nil_append] at h₅
  have h₆ := erase_ofWord 1 (T := tapes3 (.ofWord (runsWord S (mergePass R)) [])
    (.ofWord (runsWord S (deal R).1) []) (.ofWord (runsWord S (deal R).2) []))
    (pre := runsWord S (deal R).1) (rest := []) (by simp) (by simpa using hbf _)
  simp only [update_tapes3_one, List.append_nil, List.length_nil] at h₆
  have h₇ := erase_ofWord 2 (T := tapes3 (.ofWord (runsWord S (mergePass R)) [])
    (.ofWord [] []) (.ofWord (runsWord S (deal R).2) []))
    (pre := runsWord S (deal R).2) (rest := []) (by simp) (by simpa using hbf _)
  simp only [update_tapes3_two, List.append_nil, List.length_nil] at h₇
  have h₈ := rewind_ofWord 0 (T := tapes3 (.ofWord (runsWord S (mergePass R)) [])
    (.ofWord [] []) (.ofWord [] []))
    (pre := runsWord S (mergePass R)) (rest := []) (by simp) (hbf _)
  simp only [update_tapes3_zero, List.append_nil] at h₈
  have h := seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin
    (seq_runsWithin (seq_runsWithin h₁ h₂) h₃) h₄) (show (mergeAll S).RunsWithin _ _ _ from
      by simpa [mergePass] using h₅)) h₆) h₇) h₈
  exact h.mono (by simp; omega)

end TM

end Lax119563Proofs.Machines
