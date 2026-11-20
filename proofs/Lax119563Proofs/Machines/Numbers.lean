import Mathlib.Data.Nat.Bits
import Lax119563.BinaryEncodings
import Lax119563Proofs.Machines.WordRoutines

/-!
# Binary numbers on tapes

A natural number `m` is stored on a tape as the word `natWord m`, its binary digits least
significant first (`Nat.bits m`, no leading zeros, empty for `0`), normally with the head on
position `0`. Routine: increment (`incr`).
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

lemma bit_ne_blank_of_mem_bitsWord {l : List Bool} {a : Γ} (ha : a ∈ bitsWord l) :
    a ≠ blank := by
  simp only [bitsWord, List.mem_map] at ha
  obtain ⟨b, -, rfl⟩ := ha
  simp

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

/-! ## Writing codes -/

end TM

end Lax119563Proofs.Machines
