import Lax119563Proofs.Machines.SortTape

/-!
# Merge sort on tapes: merging two runs

`mergeRuns` merges the run under the head of tape `1` with the run under the head of tape `2`
(possibly empty, ending in `bar` or at the end of the word) onto the end of tape `0`, taking
the record of tape `1` whenever it is `recLE`-smaller or equal. Records are compared by a
simultaneous scan (`scanEq`), after which both heads return to the starts of their records.
-/

open Lax489179.TuringMachine (Move)

namespace Lax119563Proofs.Machines

variable {Γ : Type} [TapeAlphabet Γ]

open Function (update)

namespace TM

variable {k : ℕ} [DecidableEq Γ]

/-- Move right on tapes `i` and `j` while the scanned symbols agree and satisfy `q`. -/
def scanEq (i j : Fin k) (q : Γ → Bool) : TM k Γ :=
  loop (fun s => decide (s i = s j ∧ q (s i) = true))
    (act₂ i j fun a b => ((a, .right), (b, .right)))

theorem scanEq_ofWord {i j : Fin k} (hij : i ≠ j) (q : Γ → Bool) {T : Tapes k Γ}
    (c u v pi pj : List Γ) (hc : ∀ a ∈ c, q a = true)
    (hTi : T i = .ofWord pi (c ++ u)) (hTj : T j = .ofWord pj (c ++ v))
    (huv : u.headD blank ≠ v.headD blank ∨ q (u.headD blank) = false) :
    (scanEq i j q).RunsWithin T (2 * c.length)
      (update (update T i (.ofWord (pi ++ c) u)) j (.ofWord (pj ++ c) v)) := by
  unfold scanEq
  induction c generalizing pi pj T with
  | nil =>
    refine (loop_runsWithin_exit ?_).congr_right ?_
    · have : ¬ (u.headD blank = v.headD blank ∧ q (u.headD blank) = true) :=
        fun ⟨h₁, h₂⟩ => huv.elim (fun h => h h₁) (fun h => Bool.false_ne_true (h.symm.trans h₂))
      simpa [readAll, hTi, hTj, Tape.read_ofWord] using this
    · simp only [List.nil_append, List.append_nil] at hTi hTj ⊢
      simp [← hTi, ← hTj]
  | cons a c ih =>
    have ha : q a = true := hc a (by simp)
    have h₁ := act₂_runsWithin hij (fun a b => ((a, Move.right), (b, Move.right))) T
    simp only [hTi, hTj, List.cons_append, Tape.read_ofWord_cons, Tape.act_ofWord_right,
      List.tail_cons] at h₁
    have h₂ := ih (pi ++ [a]) (pj ++ [a]) (fun b hb => hc b (by simp [hb]))
      (T := update (update T i (Tape.ofWord (pi ++ [a]) (c ++ u))) j
        (Tape.ofWord (pj ++ [a]) (c ++ v)))
      (by simp [Function.update_of_ne hij]) (by simp)
    have h := loop_runsWithin_iter (c := fun s => decide (s i = s j ∧ q (s i) = true))
      (by simp [readAll, hTi, hTj, ha]) h₁ h₂
    refine (h.mono (by simp; omega)).congr_right ?_
    rw [update_update_update_update hij]
    simp

end TM

variable (S : Seps Γ)

/-- Symbols inside a record. -/
def inRec [DecidableEq Γ] (a : Γ) : Bool := decide (a ≠ S.hash ∧ a ≠ S.bar ∧ a ≠ blank)

/-- The loop condition of `mergeRuns`: tape `1` is not at the end of its run, or tape `2` is
not at the end of its run. -/
def mergeCond [DecidableEq Γ] (s : Fin 3 → Γ) : Bool :=
  decide (¬ (s 1 = S.bar ∧ (s 2 = S.bar ∨ s 2 = blank)))

/-- After the comparison scan: the record on tape `1` is not larger. -/
def takeFirst [DecidableEq Γ] (s : Fin 3 → Γ) : Bool :=
  decide (s 1 = S.hash ∨ (s 1 = bit false ∧ s 2 = bit true))

namespace TM

variable [DecidableEq Γ]

/-- Copy the smaller of the records under the heads of tapes `1` and `2` to tape `0`. -/
def mergeRecs : TM 3 Γ :=
  scanEq 1 2 (fun a => decide (a ≠ S.hash)) ;;
    ite (takeFirst S)
      (backTo 1 (inRec S) ;; backTo 2 (inRec S) ;; copyRec S 1 0)
      (backTo 1 (inRec S) ;; backTo 2 (inRec S) ;; copyRec S 2 0)

/-- One step of merging. -/
def mergeStep : TM 3 Γ :=
  ite (fun s => decide (s 1 = S.bar)) (copyRec S 2 0)
    (ite (fun s => decide (s 2 = S.bar ∨ s 2 = blank)) (copyRec S 1 0) (mergeRecs S))

/-- Merge the runs under the heads of tapes `1` and `2` onto the end of tape `0`. -/
def mergeRuns : TM 3 Γ := loop (mergeCond S) (mergeStep S)

end TM

omit [TapeAlphabet Γ] in
lemma exists_common_split_bool (x y : List Bool) : ∃ c u v : List Bool,
    x = c ++ u ∧ y = c ++ v ∧ (u.head? ≠ v.head? ∨ (u = [] ∧ v = [])) :=
  TM.exists_common_split x y

lemma read_rec (P : List Γ) (x : List Bool) (rest : List Γ) :
    (Tape.ofWord P (bitsWord x ++ S.hash :: rest)).read =
      match x with
      | [] => S.hash
      | b :: _ => bit b := by
  cases x <;> simp [bitsWord]

lemma read_rec_ne_bar (P : List Γ) (x : List Bool) (rest : List Γ) :
    (Tape.ofWord P (bitsWord x ++ S.hash :: rest)).read ≠ S.bar := by
  rw [read_rec]; cases x
  · exact S.hash_ne_bar
  · exact S.bit_ne_bar _

lemma read_rec_ne_blank (P : List Γ) (x : List Bool) (rest : List Γ) :
    (Tape.ofWord P (bitsWord x ++ S.hash :: rest)).read ≠ blank := by
  rw [read_rec]; cases x
  · exact S.hash_ne_blank
  · exact bit_ne_blank' _

lemma inRec_bit [DecidableEq Γ] (b : Bool) : inRec S (bit b) = true := by
  simp [inRec, S.bit_ne_hash, S.bit_ne_bar]

lemma inRec_bitsWord [DecidableEq Γ] {x : List Bool} {a : Γ} (ha : a ∈ bitsWord x) :
    inRec S a = true := by
  obtain ⟨b, rfl⟩ := mem_bitsWord ha; exact inRec_bit S b

lemma inRec_last_hash [DecidableEq Γ] (P : List Γ) :
    inRec S ((P ++ [S.hash]).getLast?.getD blank) = false := by
  simp [inRec]

lemma inRec_last_rec [DecidableEq Γ] (P : List Γ) (x : List Bool) :
    inRec S ((P ++ bitsWord x ++ [S.hash]).getLast?.getD blank) = false := by
  simp [inRec]

namespace TM

variable [DecidableEq Γ]

theorem mergeRecs_spec (x y : List Bool) (rb rc : List (List Bool)) (PA PB PC restB restC : List Γ)
    (hPB : inRec S (PB.getLast?.getD blank) = false)
    (hPC : inRec S (PC.getLast?.getD blank) = false) :
    (mergeRecs S).RunsWithin
      (tapes3 (.ofWord PA []) (.ofWord PB (bitsWord x ++ S.hash :: restB))
        (.ofWord PC (bitsWord y ++ S.hash :: restC)))
      (8 * (if recLE x y then x.length else y.length) + 5)
      (if recLE x y then
        tapes3 (.ofWord (PA ++ bitsWord x ++ [S.hash]) []) (.ofWord (PB ++ bitsWord x ++ [S.hash]) restB)
          (.ofWord PC (bitsWord y ++ S.hash :: restC))
      else
        tapes3 (.ofWord (PA ++ bitsWord y ++ [S.hash]) []) (.ofWord PB (bitsWord x ++ S.hash :: restB))
          (.ofWord (PC ++ bitsWord y ++ [S.hash]) restC)) := by
  obtain ⟨c, ux, uy, rfl, rfl, hsplit⟩ := exists_common_split_bool x y
  have hscan := scanEq_ofWord (show (1 : Fin 3) ≠ 2 by decide) (fun a => decide (a ≠ S.hash))
    (T := tapes3 (.ofWord PA []) (.ofWord PB (bitsWord (c ++ ux) ++ S.hash :: restB))
        (.ofWord PC (bitsWord (c ++ uy) ++ S.hash :: restC)))
    (bitsWord c) (bitsWord ux ++ S.hash :: restB) (bitsWord uy ++ S.hash :: restC) PB PC
    (fun a ha => by obtain ⟨b, rfl⟩ := mem_bitsWord ha; simpa using S.bit_ne_hash b)
    (by simp [bitsWord]) (by simp [bitsWord])
    (by
      rcases hsplit with h | ⟨rfl, rfl⟩
      · cases ux with
        | nil => right; simp [bitsWord]
        | cons a ux =>
          left
          cases uy with
          | nil => simpa [bitsWord] using S.bit_ne_hash a
          | cons b uy => simpa [bitsWord] using h
      · right; simp [bitsWord])
  simp only [update_tapes3_one, update_tapes3_two] at hscan
  set T₁ := tapes3 (Tape.ofWord PA []) (Tape.ofWord (PB ++ bitsWord c) (bitsWord ux ++ S.hash :: restB))
    (Tape.ofWord (PC ++ bitsWord c) (bitsWord uy ++ S.hash :: restC))
  have htake : takeFirst S (readAll T₁) = recLE (c ++ ux) (c ++ uy) := by
    rw [recLE_append_left]
    simp only [T₁, takeFirst, readAll_tapes3_one, readAll_tapes3_two, read_rec]
    rcases hsplit with h | ⟨rfl, rfl⟩
    · cases ux with
      | nil => simp
      | cons a ux =>
        cases uy with
        | nil => simp [(S.bit_ne_hash _).symm, S.bit_ne_hash]
        | cons b uy =>
          simp only [List.head?_cons, ne_eq, Option.some.injEq] at h
          cases a <;> cases b <;> simp_all [recLE_cons_cons, S.bit_ne_hash]
    · simp
  have hback : ∀ M : TM 3 Γ, ∀ t T',
      M.RunsWithin (tapes3 (Tape.ofWord PA []) (Tape.ofWord PB (bitsWord (c ++ ux) ++ S.hash :: restB))
        (Tape.ofWord PC (bitsWord (c ++ uy) ++ S.hash :: restC))) t T' →
      (backTo 1 (inRec S) ;; backTo 2 (inRec S) ;; M).RunsWithin T₁
        (2 * (bitsWord c : List Γ).length + 2 + (2 * (bitsWord c : List Γ).length + 2) + t) T' := by
    intro M t T' hM
    have b₁ := backTo_ofWord 1 (inRec S) (T := T₁) (pre := PB) (u := bitsWord c)
      (rest := bitsWord ux ++ S.hash :: restB) (by simp [T₁])
      (fun a ha => inRec_bitsWord S ha) hPB
    have b₂ := backTo_ofWord 2 (inRec S) (T := update T₁ 1 (Tape.ofWord PB (bitsWord c ++
        (bitsWord ux ++ S.hash :: restB)))) (pre := PC) (u := bitsWord c)
      (rest := bitsWord uy ++ S.hash :: restC) (by simp [T₁])
      (fun a ha => inRec_bitsWord S ha) hPC
    refine seq_runsWithin (seq_runsWithin b₁ b₂) ?_
    convert hM using 2
    simp [T₁, bitsWord]
  have hlen : (bitsWord c : List Γ).length = c.length := by simp [bitsWord]
  by_cases hle : recLE (c ++ ux) (c ++ uy) = true
  · have hcopy := copyRec_ofWord S (show (1 : Fin 3) ≠ 0 by decide) (c ++ ux)
      (T := tapes3 (Tape.ofWord PA []) (Tape.ofWord PB (bitsWord (c ++ ux) ++ S.hash :: restB))
        (Tape.ofWord PC (bitsWord (c ++ uy) ++ S.hash :: restC))) (pre := PB) (rest := restB)
      (dpre := PA) (by simp) (by simp)
    simp only [update_tapes3_one, update_tapes3_zero] at hcopy
    have hite := ite_runsWithin_true (c := takeFirst S)
      (M₂ := backTo 1 (inRec S) ;; backTo 2 (inRec S) ;; copyRec S 2 0) (T := T₁)
      (by rw [htake, hle]) (hback _ _ _ hcopy)
    refine ((seq_runsWithin hscan hite).mono ?_).congr_right ?_
    · rw [if_pos hle, hlen]; simp; omega
    · rw [if_pos hle]
  · have hcopy := copyRec_ofWord S (show (2 : Fin 3) ≠ 0 by decide) (c ++ uy)
      (T := tapes3 (Tape.ofWord PA []) (Tape.ofWord PB (bitsWord (c ++ ux) ++ S.hash :: restB))
        (Tape.ofWord PC (bitsWord (c ++ uy) ++ S.hash :: restC))) (pre := PC) (rest := restC)
      (dpre := PA) (by simp) (by simp)
    simp only [update_tapes3_two, update_tapes3_zero] at hcopy
    have hite := ite_runsWithin_false (c := takeFirst S)
      (M₁ := backTo 1 (inRec S) ;; backTo 2 (inRec S) ;; copyRec S 1 0) (T := T₁)
      (by rw [htake]; simpa using hle) (hback _ _ _ hcopy)
    refine ((seq_runsWithin hscan hite).mono ?_).congr_right ?_
    · rw [if_neg hle, hlen]; simp; omega
    · rw [if_neg hle]

end TM

end Lax119563Proofs.Machines
