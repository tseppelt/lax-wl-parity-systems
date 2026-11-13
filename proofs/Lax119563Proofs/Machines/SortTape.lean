import Mathlib.Tactic.FinCases
import Lax119563Proofs.Machines.SortModel

/-!
# Merge sort on tapes: encodings, copying records and runs, distribution

Records (bit strings) are written as `bitsWord r ++ [hash]` (`recWord`), and runs (lists of
records) as the records followed by `bar` (`runsWord`). The sorting machine works on three
tapes `0` (data), `1`, `2`, written `tapes3 a b c`.
-/

open Lax489179.TuringMachine (Move)

namespace Lax119563Proofs.Machines

variable {Γ : Type} [TapeAlphabet Γ]

open Function (update)

/-- Two separator symbols, distinct from the blank and the bits. -/
structure Seps (Γ : Type) [TapeAlphabet Γ] where
  hash : Γ
  bar : Γ
  hash_ne_blank : hash ≠ blank
  bar_ne_blank : bar ≠ blank
  hash_ne_bar : hash ≠ bar
  bit_ne_hash : ∀ b, bit b ≠ hash
  bit_ne_bar : ∀ b, bit b ≠ bar

variable (S : Seps Γ)

/-- Records, each followed by `hash`. -/
def recWord (rs : List (List Bool)) : List Γ := rs.flatMap fun r => bitsWord r ++ [S.hash]

/-- Runs of records, each followed by `bar`. -/
def runsWord (R : List (List (List Bool))) : List Γ := R.flatMap fun run => recWord S run ++ [S.bar]

@[simp] lemma recWord_nil : recWord S [] = [] := rfl
@[simp] lemma recWord_cons (r : List Bool) (rs : List (List Bool)) :
    recWord S (r :: rs) = bitsWord r ++ S.hash :: recWord S rs := by simp [recWord]
@[simp] lemma runsWord_nil : runsWord S [] = [] := rfl
@[simp] lemma runsWord_cons (run : List (List Bool)) (R : List (List (List Bool))) :
    runsWord S (run :: R) = recWord S run ++ S.bar :: runsWord S R := by simp [runsWord]

lemma recWord_append (rs ss : List (List Bool)) :
    recWord S (rs ++ ss) = recWord S rs ++ recWord S ss := by simp [recWord]

lemma mem_bitsWord {r : List Bool} {a : Γ} (ha : a ∈ bitsWord r) : ∃ b, a = bit b := by
  simp only [bitsWord, List.mem_map] at ha; obtain ⟨b, -, rfl⟩ := ha; exact ⟨b, rfl⟩

lemma mem_recWord {rs : List (List Bool)} {a : Γ} (ha : a ∈ recWord S rs) :
    (∃ b, a = bit b) ∨ a = S.hash := by
  simp only [recWord, List.mem_flatMap, List.mem_append, List.mem_singleton] at ha
  obtain ⟨r, -, ha | ha⟩ := ha
  · exact .inl (mem_bitsWord ha)
  · exact .inr ha

lemma recWord_ne_bar {rs : List (List Bool)} {a : Γ} (ha : a ∈ recWord S rs) : a ≠ S.bar := by
  rcases mem_recWord S ha with ⟨b, rfl⟩ | rfl
  · exact S.bit_ne_bar b
  · exact S.hash_ne_bar

lemma recWord_ne_blank {rs : List (List Bool)} {a : Γ} (ha : a ∈ recWord S rs) : a ≠ blank := by
  rcases mem_recWord S ha with ⟨b, rfl⟩ | rfl
  · exact bit_ne_blank' b
  · exact S.hash_ne_blank

lemma runsWord_ne_blank {R : List (List (List Bool))} {a : Γ} (ha : a ∈ runsWord S R) :
    a ≠ blank := by
  simp only [runsWord, List.mem_flatMap, List.mem_append, List.mem_singleton] at ha
  obtain ⟨run, -, ha | rfl⟩ := ha
  · exact recWord_ne_blank S ha
  · exact S.bar_ne_blank

lemma recWord_length (rs : List (List Bool)) :
    (recWord S rs).length = (rs.map fun r => r.length + 1).sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [ih, bitsWord]; ring

lemma recWord_length_perm {rs ss : List (List Bool)} (h : rs.Perm ss) :
    (recWord S rs).length = (recWord S ss).length := by
  rw [recWord_length, recWord_length, (h.map _).sum_eq]

lemma runsWord_length (R : List (List (List Bool))) :
    (runsWord S R).length = (recWord S R.flatten).length + R.length := by
  induction R with
  | nil => rfl
  | cons run R ih => simp [ih, recWord_append]; ring

lemma runsWord_mergePass_length (R : List (List (List Bool))) :
    (runsWord S (mergePass R)).length ≤ (runsWord S R).length := by
  rw [runsWord_length, runsWord_length, recWord_length_perm S (mergePass_flatten_perm R),
    mergePass_length]
  omega

lemma headD_ne_blank_of_ne_nil {l : List Γ} (hl : ∀ a ∈ l, a ≠ blank) (hne : l ≠ []) :
    l.headD blank ≠ blank := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a l => exact hl a (by simp)

/-! ## Three tapes -/

/-- The tapes of the sorting machine. -/
def tapes3 (a b c : Tape Γ) : Tapes 3 Γ := ![a, b, c]

section tapes3

variable (a b c x : Tape Γ)

@[simp] lemma tapes3_zero : tapes3 a b c 0 = a := rfl
@[simp] lemma tapes3_one : tapes3 a b c 1 = b := rfl
@[simp] lemma tapes3_two : tapes3 a b c 2 = c := rfl
@[simp] lemma update_tapes3_zero : update (tapes3 a b c) 0 x = tapes3 x b c := by
  funext i; fin_cases i <;> rfl
@[simp] lemma update_tapes3_one : update (tapes3 a b c) 1 x = tapes3 a x c := by
  funext i; fin_cases i <;> rfl
@[simp] lemma update_tapes3_two : update (tapes3 a b c) 2 x = tapes3 a b x := by
  funext i; fin_cases i <;> rfl
@[simp] lemma readAll_tapes3_zero : readAll (tapes3 a b c) 0 = a.read := rfl
@[simp] lemma readAll_tapes3_one : readAll (tapes3 a b c) 1 = b.read := rfl
@[simp] lemma readAll_tapes3_two : readAll (tapes3 a b c) 2 = c.read := rfl

end tapes3

lemma read_recWord_bar (P : List Γ) (run : List (List Bool)) (rest : List Γ) :
    (Tape.ofWord P (recWord S run ++ S.bar :: rest)).read ≠ blank := by
  rw [Tape.read_ofWord]
  cases h : recWord S run with
  | nil => simpa using S.bar_ne_blank
  | cons a w =>
    have : a ∈ recWord S run := by rw [h]; simp
    simpa using recWord_ne_blank S this

namespace TM

variable {k : ℕ} [DecidableEq Γ]

/-! ## Copying symbols, records and runs -/

/-- Copy the scanned symbol of tape `i` to tape `j`; both heads move right. -/
def copy1 (i j : Fin k) : TM k Γ := act₂ i j fun a _ => ((a, .right), (a, .right))

theorem copy1_ofWord {i j : Fin k} (hij : i ≠ j) {T : Tapes k Γ} {pre rest dpre drest : List Γ}
    {a : Γ} (hTi : T i = .ofWord pre (a :: rest)) (hTj : T j = .ofWord dpre drest) :
    (copy1 i j).RunsWithin T 1
      (update (update T i (.ofWord (pre ++ [a]) rest)) j (.ofWord (dpre ++ [a]) drest.tail)) := by
  have h := act₂_runsWithin hij (fun a _ => ((a, Move.right), (a, Move.right))) T
  refine h.congr_right ?_
  simp [hTi, hTj, Tape.act_ofWord_right]

/-- Copy a record (up to and including its `hash`) from tape `i` to the end of tape `j`. -/
def copyRec (i j : Fin k) : TM k Γ := copyR i j (fun a => decide (a ≠ S.hash)) ;; copy1 i j

theorem copyRec_ofWord {i j : Fin k} (hij : i ≠ j) (r : List Bool) {T : Tapes k Γ}
    {pre rest dpre : List Γ} (hTi : T i = .ofWord pre (bitsWord r ++ S.hash :: rest))
    (hTj : T j = .ofWord dpre []) :
    (copyRec S i j).RunsWithin T (2 * r.length + 1)
      (update (update T i (.ofWord (pre ++ bitsWord r ++ [S.hash]) rest)) j
        (.ofWord (dpre ++ bitsWord r ++ [S.hash]) [])) := by
  have h₁ := copyR_ofWord hij (fun a => decide (a ≠ S.hash)) (u := (bitsWord r : List Γ))
    (rest := S.hash :: rest) hTi
    (fun a ha => by obtain ⟨b, rfl⟩ := mem_bitsWord ha; simpa using S.bit_ne_hash b)
    (by simp) hTj
  have h₂ := copy1_ofWord hij (pre := pre ++ bitsWord r) (rest := rest) (a := S.hash)
    (dpre := dpre ++ bitsWord r) (drest := [])
    (T := update (update T i (Tape.ofWord (pre ++ bitsWord r) (S.hash :: rest))) j
      (Tape.ofWord (dpre ++ bitsWord r) ([].drop (bitsWord r : List Γ).length)))
    (by simp [Function.update_of_ne hij]) (by simp)
  refine ((seq_runsWithin h₁ h₂).mono (by simp [bitsWord])).congr_right ?_
  rw [update_update_update_update hij]
  simp

/-- Copy a run (up to and including its `bar`) from tape `i` to the end of tape `j`. -/
def copyRun (i j : Fin k) : TM k Γ := copyR i j (fun a => decide (a ≠ S.bar)) ;; copy1 i j

theorem copyRun_ofWord {i j : Fin k} (hij : i ≠ j) (run : List (List Bool)) {T : Tapes k Γ}
    {pre rest dpre : List Γ} (hTi : T i = .ofWord pre (recWord S run ++ S.bar :: rest))
    (hTj : T j = .ofWord dpre []) :
    (copyRun S i j).RunsWithin T (2 * (recWord S run).length + 1)
      (update (update T i (.ofWord (pre ++ recWord S run ++ [S.bar]) rest)) j
        (.ofWord (dpre ++ recWord S run ++ [S.bar]) [])) := by
  have h₁ := copyR_ofWord hij (fun a => decide (a ≠ S.bar)) (u := recWord S run)
    (rest := S.bar :: rest) hTi (fun a ha => by simpa using recWord_ne_bar S ha) (by simp) hTj
  have h₂ := copy1_ofWord hij (pre := pre ++ recWord S run) (rest := rest) (a := S.bar)
    (dpre := dpre ++ recWord S run) (drest := [])
    (T := update (update T i (Tape.ofWord (pre ++ recWord S run) (S.bar :: rest))) j
      (Tape.ofWord (dpre ++ recWord S run) ([].drop (recWord S run).length)))
    (by simp [Function.update_of_ne hij]) (by simp)
  refine (seq_runsWithin h₁ h₂).congr_right ?_
  rw [update_update_update_update hij]
  simp

/-! ## Distribution of runs -/

/-- Copy the runs of tape `0` alternately to the ends of tapes `1` and `2`. -/
def distribute : TM 3 Γ :=
  loop (fun s => decide (s 0 ≠ blank))
    (copyRun S 0 1 ;; ite (fun s => decide (s 0 = blank)) nop (copyRun S 0 2))

theorem distribute_spec (R : List (List (List Bool))) (PA PB PC : List Γ) :
    (distribute S).RunsWithin
      (tapes3 (.ofWord PA (runsWord S R)) (.ofWord PB []) (.ofWord PC []))
      (2 * (runsWord S R).length)
      (tapes3 (.ofWord (PA ++ runsWord S R) []) (.ofWord (PB ++ runsWord S (deal R).1) [])
        (.ofWord (PC ++ runsWord S (deal R).2) [])) := by
  induction R using deal.induct generalizing PA PB PC with
  | case1 =>
    exact (loop_runsWithin_exit (by simp)).mono (Nat.zero_le _) |>.congr_right (by simp [deal])
  | case2 r =>
    have h₁ := copyRun_ofWord S (show (0 : Fin 3) ≠ 1 by decide) r (rest := []) (pre := PA) (dpre := PB)
      (T := tapes3 (.ofWord PA (runsWord S [r])) (.ofWord PB []) (.ofWord PC [])) (by simp)
      (by simp)
    simp only [update_tapes3_zero, update_tapes3_one] at h₁
    have h₂ := ite_runsWithin_true (c := fun s => decide (s 0 = blank))
      (M₂ := copyRun S 0 2) (by simp) (nop_haltsIn
        (tapes3 (.ofWord (PA ++ recWord S r ++ [S.bar]) []) (.ofWord (PB ++ recWord S r ++ [S.bar]) [])
          (.ofWord PC []))).runsWithin
    have h₃ := loop_runsWithin_exit (c := fun s => decide (s 0 ≠ blank))
      (B := copyRun S 0 1 ;; ite (fun s => decide (s 0 = blank)) nop (copyRun S 0 2))
      (T := tapes3 (.ofWord (PA ++ recWord S r ++ [S.bar]) []) (.ofWord (PB ++ recWord S r ++ [S.bar]) [])
          (.ofWord PC [])) (by simp)
    refine ((loop_runsWithin_iter (by simpa using read_recWord_bar S PA r [])
      (seq_runsWithin h₁ h₂) h₃).mono (by simp; omega)).congr_right (by simp [deal])
  | case3 r₁ r₂ R ih =>
    have h₁ := copyRun_ofWord S (show (0 : Fin 3) ≠ 1 by decide) r₁ (rest := runsWord S (r₂ :: R))
      (pre := PA) (dpre := PB)
      (T := tapes3 (.ofWord PA (runsWord S (r₁ :: r₂ :: R))) (.ofWord PB []) (.ofWord PC []))
      (by simp) (by simp)
    simp only [update_tapes3_zero, update_tapes3_one] at h₁
    have h₂' := copyRun_ofWord S (show (0 : Fin 3) ≠ 2 by decide) r₂ (rest := runsWord S R)
      (pre := PA ++ recWord S r₁ ++ [S.bar]) (dpre := PC)
      (T := tapes3 (.ofWord (PA ++ recWord S r₁ ++ [S.bar]) (runsWord S (r₂ :: R)))
        (.ofWord (PB ++ recWord S r₁ ++ [S.bar]) []) (.ofWord PC []))
      (by simp) (by simp)
    simp only [update_tapes3_zero, update_tapes3_two] at h₂'
    have hr₂ := read_recWord_bar S (PA ++ recWord S r₁ ++ [S.bar]) r₂ (runsWord S R)
    have h₂ := ite_runsWithin_false (c := fun s => decide (s 0 = blank)) (M₁ := nop)
      (by simpa using hr₂) h₂'
    have h₃ := ih (PA ++ recWord S r₁ ++ [S.bar] ++ recWord S r₂ ++ [S.bar])
      (PB ++ recWord S r₁ ++ [S.bar]) (PC ++ recWord S r₂ ++ [S.bar])
    refine ((loop_runsWithin_iter (by simpa using read_recWord_bar S PA r₁ _)
      (seq_runsWithin h₁ h₂) h₃).mono (by simp; omega)).congr_right (by simp [deal])

end TM

end Lax119563Proofs.Machines
