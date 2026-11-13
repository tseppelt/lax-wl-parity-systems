import Mathlib.Data.Nat.Bits
import Lax119563.BinaryEncodings
import Lax119563Proofs.Machines.WordRoutines

/-!
# Binary numbers on tapes

A natural number `m` is stored on a tape as the word `natWord m`, its binary digits least
significant first (`Nat.bits m`, no leading zeros, empty for `0`), normally with the head on
position `0`. Routines: zero test (a scanned blank), increment (`incr`), equality test
(`eqScan`, followed by rewinding), and writing the self-delimiting code `encodeNat m`
(`emitNat`).
-/

open Lax489179.TuringMachine (Move)
open Lax119563.BinaryEncodings

namespace Lax119563Proofs.Machines

variable {Γ : Type} {k : ℕ}

open Function (update)

/-! ## Binary digits -/

/-- Increment on little-endian digit lists. -/
def incBits : List Bool → List Bool
  | [] => [true]
  | false :: l => true :: l
  | true :: l => false :: incBits l

lemma bits_succ (m : ℕ) : (m + 1).bits = incBits m.bits := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simpa [incBits, Nat.zero_bits] using Nat.bit1_bits 0
      · rw [Nat.bit1_bits, Nat.bit0_bits n (by omega)]
        rfl
    · rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, Nat.bit0_bits _ (by omega), Nat.bit1_bits,
        ih n (by omega)]
      rfl

lemma incBits_eq (l : List Bool) :
    incBits l = (l.takeWhile id).map (fun _ => false) ++ true :: (l.dropWhile id).tail := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [incBits, ih]

lemma bits_eq_nil_iff (m : ℕ) : m.bits = [] ↔ m = 0 := by
  constructor
  · intro h
    obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · rfl
      · rw [Nat.bit0_bits n (by omega)] at h; cases h
    · rw [Nat.bit1_bits] at h; cases h
  · rintro rfl; exact Nat.zero_bits

/-- The value of a little-endian digit list. -/
def valBits : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * valBits l

lemma valBits_bits (m : ℕ) : valBits m.bits = m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [Nat.zero_bits, valBits]
      · rw [Nat.bit0_bits n (by omega), valBits, ih n (by omega)]
        simp
    · rw [Nat.bit1_bits, valBits, ih n (by omega)]
      simp; ring

lemma bits_injective : Function.Injective Nat.bits := by
  intro a b h
  rw [← valBits_bits a, ← valBits_bits b, h]

variable [TapeAlphabet Γ]

/-- The word of the binary digits of `m`, least significant first. -/
def natWord (m : ℕ) : List Γ := (Nat.bits m).map bit

/-- The word of a list of bits. -/
def bitsWord (l : List Bool) : List Γ := l.map bit

omit [TapeAlphabet Γ] in
@[simp] lemma natWord_zero [TapeAlphabet Γ] : (natWord 0 : List Γ) = [] := by
  simp [natWord, Nat.zero_bits]

lemma bit_ne_blank_of_mem_bitsWord {l : List Bool} {a : Γ} (ha : a ∈ bitsWord l) :
    a ≠ blank := by
  simp only [bitsWord, List.mem_map] at ha
  obtain ⟨b, -, rfl⟩ := ha
  simp

lemma natWord_eq_nil_iff (m : ℕ) : (natWord m : List Γ) = [] ↔ m = 0 := by
  simp [natWord, bits_eq_nil_iff]

lemma natWord_injective : Function.Injective (natWord : ℕ → List Γ) := by
  intro a b h
  apply bits_injective
  exact List.map_injective_iff.mpr TapeAlphabet.bit_injective h

lemma mem_natWord_ne_blank {m : ℕ} {a : Γ} (ha : a ∈ natWord m) : a ≠ blank :=
  bit_ne_blank_of_mem_bitsWord ha

namespace TM

variable [DecidableEq Γ]

/-! ## Increment -/

/-- Increment the number on tape `i` (head on position `0`; the head returns there). -/
def incr (i : Fin k) : TM k Γ :=
  loop (fun s => decide (s i = bit true)) (writeR i (bit false)) ;; write i (bit true) ;;
    rewind i

theorem incrLoop_ofWord (i : Fin k) (l : List Bool) {T : Tapes k Γ} {pre : List Γ}
    (hT : T i = .ofWord pre (bitsWord l)) :
    (loop (fun s => decide (s i = bit true)) (writeR i (bit false))).RunsWithin T
      (2 * (l.takeWhile id).length)
      (update T i (.ofWord (pre ++ bitsWord ((l.takeWhile id).map fun _ => false))
        (bitsWord (l.dropWhile id)))) := by
  induction l generalizing pre T with
  | nil =>
    refine (loop_runsWithin_exit (by simp [readAll, hT, bitsWord])).congr_right ?_
    rw [eq_comm, Function.update_eq_self_iff, hT]
    simp [bitsWord]
  | cons b l ih =>
    cases b with
    | false =>
      refine (loop_runsWithin_exit (by simp [readAll, hT, bitsWord])).congr_right ?_
      rw [eq_comm, Function.update_eq_self_iff, hT]
      simp [bitsWord]
    | true =>
      have h₁ := writeR_runsWithin i (bit false) T
      rw [hT] at h₁
      simp only [bitsWord, List.map_cons, Tape.act_ofWord_right, List.tail_cons] at h₁
      have h₂ := ih (pre := pre ++ [bit false]) (T := update T i
        (Tape.ofWord (pre ++ [bit false]) (bitsWord l))) (by simp [bitsWord])
      have h := loop_runsWithin_iter (c := fun s => decide (s i = bit true))
        (by simp [readAll, hT, bitsWord]) h₁ h₂
      refine (h.mono (by simp; omega)).congr_right ?_
      simp [bitsWord]

theorem incr_ofWord (i : Fin k) (m : ℕ) {T : Tapes k Γ} (hT : T i = .ofWord [] (natWord m)) :
    (incr i).RunsWithin T (4 * (m.bits.length) + 5) (update T i (.ofWord [] (natWord (m + 1)))) := by
  have h₁ := incrLoop_ofWord i m.bits (pre := []) (by simpa [natWord, bitsWord] using hT)
  set P : List Γ := bitsWord ((m.bits.takeWhile id).map fun _ => false)
  set T₁ := update T i (Tape.ofWord ([] ++ P) (bitsWord (m.bits.dropWhile id)))
  have h₂ := write_runsWithin i (bit true) T₁
  have hT₂ : update T₁ i ((T₁ i).act (bit true) .stay) =
      update T i (Tape.ofWord P (bitsWord (true :: (m.bits.dropWhile id).tail))) := by
    simp [T₁, Tape.act_ofWord_stay, bitsWord]
  rw [hT₂] at h₂
  have h₃ := rewind_ofWord i (T := update T i
    (Tape.ofWord P (bitsWord (true :: (m.bits.dropWhile id).tail)))) (pre := P)
    (rest := bitsWord (true :: (m.bits.dropWhile id).tail)) (by simp)
    (fun a ha => by
      simp only [P, bitsWord, List.mem_map] at ha
      obtain ⟨b, -, rfl⟩ := ha; simp)
  have hlen : P.length ≤ m.bits.length := by
    simp only [P, bitsWord, List.length_map]
    exact List.Sublist.length_le (List.takeWhile_sublist _)
  have htw : (m.bits.takeWhile id).length ≤ m.bits.length :=
    List.Sublist.length_le (List.takeWhile_sublist _)
  refine ((seq_runsWithin (seq_runsWithin h₁ h₂) h₃).mono (by omega)).congr_right ?_
  rw [Function.update_idem]
  congr 2
  simp only [P, natWord, bits_succ, incBits_eq, bitsWord, List.map_append, List.map_cons]

/-! ## Equality test -/

/-- Move right on tapes `i` and `j` while their scanned symbols agree and are not blank. -/
def eqScan (i j : Fin k) : TM k Γ :=
  loop (fun s => decide (s i = s j ∧ s i ≠ blank)) (act₂ i j fun a b => ((a, .right), (b, .right)))

theorem eqScan_ofWord {i j : Fin k} (hij : i ≠ j) {T : Tapes k Γ} (c u v : List Γ)
    (pi pj : List Γ) (hc : ∀ a ∈ c, a ≠ blank)
    (hTi : T i = .ofWord pi (c ++ u)) (hTj : T j = .ofWord pj (c ++ v))
    (huv : u.headD blank ≠ v.headD blank ∨ u.headD blank = blank) :
    (eqScan i j).RunsWithin T (2 * c.length)
      (update (update T i (.ofWord (pi ++ c) u)) j (.ofWord (pj ++ c) v)) := by
  unfold eqScan
  induction c generalizing pi pj T with
  | nil =>
    refine (loop_runsWithin_exit ?_).congr_right ?_
    · have : ¬ (u.headD blank = v.headD blank ∧ u.headD blank ≠ blank) :=
        fun ⟨h₁, h₂⟩ => huv.elim (fun h => h h₁) (fun h => h₂ h)
      simpa [readAll, hTi, hTj, Tape.read_ofWord] using this
    · simp only [List.nil_append, List.append_nil] at hTi hTj ⊢
      simp [← hTi, ← hTj]
  | cons a c ih =>
    have ha : a ≠ blank := hc a (by simp)
    have h₁ := act₂_runsWithin hij (fun a b => ((a, Move.right), (b, Move.right))) T
    simp only [hTi, hTj, List.cons_append, Tape.read_ofWord_cons, Tape.act_ofWord_right,
      List.tail_cons] at h₁
    have h₂ := ih (pi ++ [a]) (pj ++ [a]) (fun b hb => hc b (by simp [hb]))
      (T := update (update T i (Tape.ofWord (pi ++ [a]) (c ++ u))) j
        (Tape.ofWord (pj ++ [a]) (c ++ v)))
      (by simp [Function.update_of_ne hij]) (by simp)
    have h := loop_runsWithin_iter (c := fun s => decide (s i = s j ∧ s i ≠ blank))
      (by simp [readAll, hTi, hTj, ha]) h₁ h₂
    refine (h.mono (by simp; omega)).congr_right ?_
    rw [update_update_update_update hij]
    simp

omit [DecidableEq Γ] [TapeAlphabet Γ] in
/-- Splitting two words after their longest common prefix. -/
lemma exists_common_split [DecidableEq Γ] (x y : List Γ) : ∃ c u v : List Γ,
    x = c ++ u ∧ y = c ++ v ∧ (u.head? ≠ v.head? ∨ (u = [] ∧ v = [])) := by
  induction x generalizing y with
  | nil =>
    cases y with
    | nil => exact ⟨[], [], [], by simp⟩
    | cons b y => exact ⟨[], [], b :: y, by simp⟩
  | cons a x ih =>
    cases y with
    | nil => exact ⟨[], a :: x, [], by simp⟩
    | cons b y =>
      by_cases hab : a = b
      · subst hab
        obtain ⟨c, u, v, rfl, rfl, h⟩ := ih y
        exact ⟨a :: c, u, v, rfl, rfl, h⟩
      · exact ⟨[], a :: x, b :: y, by simp [hab]⟩

theorem eqScan_split {i j : Fin k} (hij : i ≠ j) {T : Tapes k Γ} {x y : List Γ}
    (hx : ∀ a ∈ x, a ≠ blank) (hy : ∀ a ∈ y, a ≠ blank)
    (hTi : T i = .ofWord [] x) (hTj : T j = .ofWord [] y) :
    ∃ c u v : List Γ, x = c ++ u ∧ y = c ++ v ∧
      (decide ((Tape.ofWord c u).read = blank ∧ (Tape.ofWord c v).read = blank) = true ↔
        x = y) ∧
      (eqScan i j).RunsWithin T (2 * c.length)
        (update (update T i (.ofWord c u)) j (.ofWord c v)) := by
  obtain ⟨c, u, v, rfl, rfl, h⟩ := exists_common_split x y
  refine ⟨c, u, v, rfl, rfl, ?_, ?_⟩
  · simp only [Tape.read_ofWord, decide_eq_true_eq, List.append_cancel_left_eq]
    constructor
    · rintro ⟨hu, hv⟩
      cases u with
      | nil => cases v with
        | nil => rfl
        | cons b v => exact absurd hv (hy b (by simp))
      | cons a u => exact absurd hu (hx a (by simp))
    · rintro rfl
      rcases h with h | ⟨rfl, -⟩
      · exact absurd rfl h
      · simp
  · refine (eqScan_ofWord hij c u v [] [] (fun a ha => hx a (by simp [ha])) (by simpa using hTi)
      (by simpa using hTj) ?_).congr_right (by simp)
    rcases h with h | ⟨rfl, rfl⟩
    · cases u with
      | nil => right; rfl
      | cons a u =>
        left
        cases v with
        | nil => simpa using hx a (by simp)
        | cons b v => simpa using h
    · right; rfl

/-- Branch on the equality of the blank-free words on tapes `i` and `j` (heads on position
`0`, where they return before the branch is taken). -/
def ifEq (i j : Fin k) (M₁ M₂ : TM k Γ) : TM k Γ :=
  eqScan i j ;; ite (fun s => decide (s i = blank ∧ s j = blank))
    (rewind i ;; rewind j ;; M₁) (rewind i ;; rewind j ;; M₂)

theorem ifEq_runsWithin {i j : Fin k} (hij : i ≠ j) {T T' : Tapes k Γ} {x y : List Γ}
    {M₁ M₂ : TM k Γ} {t : ℕ}
    (hx : ∀ a ∈ x, a ≠ blank) (hy : ∀ a ∈ y, a ≠ blank)
    (hTi : T i = .ofWord [] x) (hTj : T j = .ofWord [] y)
    (h₁ : x = y → M₁.RunsWithin T t T') (h₂ : x ≠ y → M₂.RunsWithin T t T') :
    (ifEq i j M₁ M₂).RunsWithin T (6 * x.length + 4 + t) T' := by
  obtain ⟨c, u, v, rfl, rfl, hiff, hscan⟩ := eqScan_split hij hx hy hTi hTj
  set T₁ := update (update T i (Tape.ofWord c u)) j (Tape.ofWord c v)
  have hr : ∀ M : TM k Γ, M.RunsWithin T t T' →
      (rewind i ;; rewind j ;; M).RunsWithin T₁ (2 * c.length + 2 + (2 * c.length + 2) + t) T' := by
    intro M hM
    have hc : ∀ a ∈ c, a ≠ blank := fun a ha => hx a (by simp [ha])
    have r₁ := rewind_ofWord i (T := T₁) (pre := c) (rest := u) (by simp [T₁, Function.update_of_ne hij]) hc
    have r₂ := rewind_ofWord j (T := update T₁ i (Tape.ofWord [] (c ++ u))) (pre := c) (rest := v) (by simp [T₁, Function.update_of_ne hij.symm]) hc
    refine seq_runsWithin (seq_runsWithin r₁ r₂) ?_
    convert hM using 1
    simp only [T₁, Function.update_idem]
    rw [Function.update_comm hij, Function.update_idem, Function.update_comm hij.symm,
      ← hTi, ← hTj]
    simp
  have hread : readAll T₁ i = (Tape.ofWord c u).read ∧ readAll T₁ j = (Tape.ofWord c v).read := by
    simp [readAll, T₁, Function.update_of_ne hij]
  have hlen : c.length ≤ (c ++ u).length := by simp
  by_cases hxy : c ++ u = c ++ v
  · have := ite_runsWithin_true (c := fun s => decide (s i = blank ∧ s j = blank))
      (M₂ := rewind i ;; rewind j ;; M₂) (by simpa [hread.1, hread.2] using hiff.mpr hxy)
      (hr M₁ (h₁ hxy))
    exact (seq_runsWithin hscan this).mono (by omega)
  · have := ite_runsWithin_false (c := fun s => decide (s i = blank ∧ s j = blank))
      (M₁ := rewind i ;; rewind j ;; M₁)
      (by
        have : ¬ (decide ((Tape.ofWord c u).read = blank ∧ (Tape.ofWord c v).read = blank) = true) :=
          fun h => hxy (hiff.mp h)
        simpa [hread.1, hread.2] using this)
      (hr M₂ (h₂ hxy))
    exact (seq_runsWithin hscan this).mono (by omega)

/-! ## Writing codes -/

/-- Append `encodeNat m` to the word on tape `o` (head after its end), where `m` is the
number on tape `i` (head on position `0`, where it returns). -/
def emitNat (i o : Fin k) : TM k Γ :=
  loop (fun s => decide (s i ≠ blank))
      (writeR o (bit true) ;; act₂ i o fun a _ => ((a, .right), (a, .right))) ;;
    writeR o (bit false) ;; rewind i

theorem emitLoop_ofWord {i o : Fin k} (hio : i ≠ o) (l : List Bool) {T : Tapes k Γ}
    {pre opre : List Γ} (hTi : T i = .ofWord pre (bitsWord l)) (hTo : T o = .ofWord opre []) :
    (loop (fun s => decide (s i ≠ blank))
        (writeR o (bit true) ;; act₂ i o fun a _ => ((a, .right), (a, .right)))).RunsWithin T
      (3 * l.length)
      (update (update T i (.ofWord (pre ++ bitsWord l) []))
        o (.ofWord (opre ++ bitsWord (l.flatMap fun d => [true, d])) [])) := by
  induction l generalizing pre opre T with
  | nil =>
    refine (loop_runsWithin_exit (by simp [readAll, hTi, bitsWord])).congr_right ?_
    simp only [bitsWord, List.map_nil, List.append_nil, List.flatMap_nil] at hTi ⊢
    simp [← hTi, ← hTo]
  | cons d l ih =>
    have h₁ := writeR_runsWithin o (bit true) T
    rw [hTo, Tape.act_ofWord_right] at h₁
    have h₂ := act₂_runsWithin hio (fun a _ => ((a, Move.right), (a, Move.right)))
      (update T o (Tape.ofWord (opre ++ [bit true]) []))
    simp only [Function.update_of_ne hio, Function.update_self, hTi, bitsWord, List.map_cons,
      Tape.read_ofWord_cons, Tape.act_ofWord_right, List.tail_cons, List.tail_nil] at h₂
    have h₃ := ih (pre := pre ++ [bit d]) (opre := opre ++ [bit true] ++ [bit d])
      (T := update (update (update T o (Tape.ofWord (opre ++ [bit true]) [])) i
        (Tape.ofWord (pre ++ [bit d]) (bitsWord l))) o
        (Tape.ofWord (opre ++ [bit true] ++ [bit d]) []))
      (by simp [Function.update_of_ne hio, bitsWord]) (by simp)
    have h := loop_runsWithin_iter (c := fun s => decide (s i ≠ blank))
      (by simp [readAll, hTi, bitsWord]) (seq_runsWithin h₁ h₂) h₃
    refine (h.mono (by simp; omega)).congr_right ?_
    funext x
    by_cases hx : x = o
    · subst hx; simp [bitsWord]
    · by_cases hx' : x = i
      · subst hx'; simp [Function.update_of_ne hx, bitsWord]
      · simp [Function.update_of_ne hx, Function.update_of_ne hx']

theorem emitNat_ofWord {i o : Fin k} (hio : i ≠ o) (m : ℕ) {T : Tapes k Γ} {opre : List Γ}
    (hTi : T i = .ofWord [] (natWord m)) (hTo : T o = .ofWord opre []) :
    (emitNat i o).RunsWithin T (5 * m.bits.length + 3)
      (update T o (.ofWord (opre ++ bitsWord (encodeNat m)) [])) := by
  have h₁ := emitLoop_ofWord hio m.bits (pre := []) (opre := opre) (by simpa [natWord, bitsWord] using hTi) hTo
  have h₂ := writeR_runsWithin o (bit false) (update (update T i
    (Tape.ofWord ([] ++ bitsWord m.bits) [])) o
    (Tape.ofWord (opre ++ bitsWord (m.bits.flatMap fun d => [true, d])) []))
  simp only [Function.update_self, Tape.act_ofWord_right, List.tail_nil,
    Function.update_idem] at h₂
  have h₃ := rewind_ofWord i (pre := bitsWord m.bits) (rest := [])
    (T := update (update T i (Tape.ofWord ([] ++ bitsWord m.bits) [])) o
      (Tape.ofWord (opre ++ bitsWord (m.bits.flatMap fun d => [true, d]) ++ [bit false]) []))
    (by simp [Function.update_of_ne hio]) (fun a ha => bit_ne_blank_of_mem_bitsWord ha)
  refine ((seq_runsWithin (seq_runsWithin h₁ h₂) h₃).mono (by simp [bitsWord]; omega)).congr_right ?_
  funext x
  by_cases hx : x = o
  · subst hx; simp [Function.update_of_ne hio.symm, encodeNat, bitsWord]
  · by_cases hx' : x = i
    · subst hx'; simp [Function.update_of_ne hx, hTi, natWord, bitsWord]
    · simp [Function.update_of_ne hx, Function.update_of_ne hx']

end TM

end Lax119563Proofs.Machines
