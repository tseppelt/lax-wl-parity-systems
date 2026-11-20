import Lax119563Proofs.Bridges.TM2Sim.Phases

/-!
# Simulating archive multitape machines by mathlib stack machines: tape representation

A tape with head `h` and cells `cells` is represented by stacks `L`, `Rl` when
`cells (h + i)` is the symbol of entry `i` of `Rl` and `cells (h - 1 - i)` that of entry `i`
of `L` (missing entries are blank). On tape `0` the flags mark position `0`, which lies in the
explicitly stored range (`OriginRep`). Both are preserved by `applyTape`.
-/

open Lax489179.TuringMachine (Machine Config Move Instruction)

namespace Lax119563Proofs.Bridges.TM2Sim

variable {R : Machine}

/-- Stacks `L`, `Rl` represent the tape with head `h` and cells `cells`. -/
def TapeRep (h : ℤ) (cells : ℤ → Sym R) (L Rl : List (G R)) : Prop :=
  (∀ i : ℕ, cells (h + i) = (Rl.getD i (g0 R)).1) ∧
    (∀ i : ℕ, cells (h - 1 - i) = (L.getD i (g0 R)).1)

/-- The flags of `L`, `Rl` mark position `0`, and position `0` is stored. -/
def OriginRep (h : ℤ) (L Rl : List (G R)) : Prop :=
  (∀ i (hi : i < Rl.length), (Rl[i]).2 = decide (h + i = 0)) ∧
    (∀ i (hi : i < L.length), (L[i]).2 = decide (h - 1 - i = 0)) ∧
    h - L.length ≤ 0 ∧ 0 < h + Rl.length

lemma getD_tail (l : List (G R)) (i : ℕ) : l.tail.getD i (g0 R) = l.getD (i + 1) (g0 R) := by
  cases l <;> simp

lemma getD_head (l : List (G R)) : l.head?.getD (g0 R) = l.getD 0 (g0 R) := by
  cases l <;> simp

lemma applyTape_rep {h : ℤ} {cells : ℤ → Sym R} {L Rl : List (G R)} (H : TapeRep h cells L Rl)
    (w : Sym R) (m : Move) :
    TapeRep (h + m.offset) (fun z => if z = h then w else cells z)
      (applyTape L Rl w m).1 (applyTape L Rl w m).2 := by
  obtain ⟨H1, H2⟩ := H
  cases m with
  | right =>
    rw [show Move.right.offset = 1 from rfl]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [applyTape]
      rw [if_neg (by omega), getD_tail]
      have := H1 (i + 1); push_cast at this; rw [← this]; congr 1; omega
    · simp only [applyTape]
      rcases i with _ | i
      · simp
      · rw [if_neg (by omega)]
        simp only [List.getD_cons_succ]
        have := H2 i; rw [← this]; congr 1 <;> push_cast <;> omega
  | stay =>
    rw [show Move.stay.offset = 0 from rfl]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [applyTape]
      rcases i with _ | i
      · simp
      · rw [if_neg (by omega)]
        simp only [List.getD_cons_succ, getD_tail]
        have := H1 (i + 1); rw [← this]; congr 1 <;> push_cast <;> omega
    · simp only [applyTape]
      rw [if_neg (by omega)]
      have := H2 i; rw [← this]; congr 1; omega
  | left =>
    rw [show Move.left.offset = -1 from rfl]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [applyTape]
      rcases i with _ | _ | i
      · rw [if_neg (by omega)]
        simp only [List.getD_cons_zero, getD_head]
        have := H2 0; rw [← this]; congr 1
      · simp
      · rw [if_neg (by omega)]
        simp only [List.getD_cons_succ, getD_tail]
        have := H1 (i + 1); rw [← this]; congr 1 <;> push_cast <;> omega
    · simp only [applyTape]
      rw [if_neg (by omega), getD_tail]
      have := H2 (i + 1); rw [← this]; congr 1 <;> push_cast <;> omega

lemma applyTape_length (L Rl : List (G R)) (w : Sym R) (m : Move) :
    (applyTape L Rl w m).1.length + (applyTape L Rl w m).2.length ≤ L.length + Rl.length + 2 := by
  cases m <;> simp only [applyTape, List.length_cons, List.length_tail] <;> omega

lemma flag_head {h : ℤ} {L Rl : List (G R)} (H : OriginRep h L Rl) :
    (Rl.head?.map Prod.snd).getD false = decide (h = 0) := by
  obtain ⟨H1, -, -, H4⟩ := H
  cases Rl with
  | nil =>
    simp only [List.length_nil, Nat.cast_zero, add_zero] at H4
    simp; omega
  | cons a Rl =>
    have := H1 0 (by simp)
    simpa using this

lemma applyTape_origin {h : ℤ} {L Rl : List (G R)} (H : OriginRep h L Rl)
    (w : Sym R) (m : Move) :
    OriginRep (h + m.offset) (applyTape L Rl w m).1 (applyTape L Rl w m).2 := by
  have hf := flag_head H
  obtain ⟨H1, H2, H3, H4⟩ := H
  cases m with
  | right =>
    refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩
    · simp only [applyTape, List.getElem_tail, Move.offset] at hi ⊢
      rw [H1 (i + 1) (by simp at hi; omega)]
      congr 1; apply propext; push_cast; constructor <;> intro <;> omega
    · simp only [applyTape, Move.offset] at hi ⊢
      rcases i with _ | i
      · simp only [List.getElem_cons_zero, hf]; congr 1; apply propext; constructor <;> intro <;> omega
      · simp only [List.getElem_cons_succ]
        rw [H2 i (by simp at hi; omega)]
        congr 1; apply propext; push_cast; constructor <;> intro <;> omega
    · simp only [applyTape, Move.offset, List.length_cons, List.length_tail]; push_cast
      rcases Rl with _ | ⟨a, Rl⟩ <;> simp at H4 ⊢ <;> omega
    · simp only [applyTape, Move.offset, List.length_tail]
      rcases Rl with _ | ⟨a, Rl⟩
      · simp at H4 hf ⊢; omega
      · simp at H4 ⊢; omega
  | stay =>
    refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩
    · simp only [applyTape, Move.offset] at hi ⊢
      rcases i with _ | i
      · simp only [List.getElem_cons_zero, hf]; congr 1; apply propext; constructor <;> intro <;> omega
      · simp only [List.getElem_cons_succ, List.getElem_tail]
        rw [H1 (i + 1) (by simp at hi; omega)]
        congr 1; apply propext; push_cast; constructor <;> intro <;> omega
    · simp only [applyTape, Move.offset] at hi ⊢
      rw [H2 i hi]; congr 1; apply propext; constructor <;> intro <;> omega
    · simp only [applyTape, Move.offset]; omega
    · simp only [applyTape, Move.offset, List.length_cons, List.length_tail]; push_cast
      rcases Rl with _ | ⟨a, Rl⟩ <;> simp at H4 ⊢ <;> omega
  | left =>
    refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩
    · simp only [applyTape, Move.offset] at hi ⊢
      rcases i with _ | _ | i
      · simp only [List.getElem_cons_zero]
        rcases L with _ | ⟨a, L⟩
        · simp only [List.length_nil, Nat.cast_zero, sub_zero] at H3
          simp [g0]; omega
        · have := H2 0 (by simp)
          simp only [List.head?_cons, Option.getD_some]
          simp at this ⊢; rw [this]; constructor <;> intro <;> omega
      · simp only [List.getElem_cons_succ, List.getElem_cons_zero, hf]
        congr 1; apply propext; constructor <;> intro <;> omega
      · simp only [List.getElem_cons_succ, List.getElem_tail]
        rw [H1 (i + 1) (by simp at hi; omega)]
        congr 1; apply propext; push_cast; constructor <;> intro <;> omega
    · simp only [applyTape, List.getElem_tail, Move.offset] at hi ⊢
      rw [H2 (i + 1) (by simp at hi; omega)]
      congr 1; apply propext; push_cast; constructor <;> intro <;> omega
    · simp only [applyTape, Move.offset, List.length_tail]
      rcases L with _ | ⟨a, L⟩
      · simp at H3 ⊢; omega
      · simp at H3 ⊢; omega
    · simp only [applyTape, Move.offset, List.length_cons, List.length_tail]; push_cast
      rcases Rl with _ | ⟨a, Rl⟩ <;> simp at H4 ⊢ <;> omega

/-! ## The whole explicitly stored part of a tape -/

lemma gathered_rep {h : ℤ} {cells : ℤ → Sym R} {L Rl : List (G R)} (H : TapeRep h cells L Rl)
    (i : ℕ) : cells (h - L.length + i) = ((L.reverse ++ Rl).getD i (g0 R)).1 := by
  obtain ⟨H1, H2⟩ := H
  by_cases hi : i < L.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hi),
      List.getElem?_reverse hi]
    have := H2 (L.length - 1 - i)
    rw [List.getD_eq_getElem?_getD] at this
    rw [← this]; congr 1; push_cast [Nat.sub_sub, Nat.cast_sub (show 1 + i ≤ L.length by omega)]
    ring
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
    have := H1 (i - L.length)
    rw [List.getD_eq_getElem?_getD] at this
    simp only [List.length_reverse]
    rw [← this]; congr 1; push_cast [Nat.cast_sub (show L.length ≤ i by omega)]; ring

lemma gathered_origin {h : ℤ} {L Rl : List (G R)} (H : OriginRep h L Rl)
    (i : ℕ) (hi : i < (L.reverse ++ Rl).length) :
    ((L.reverse ++ Rl)[i]).2 = decide (h - L.length + i = 0) := by
  obtain ⟨H1, H2, -, -⟩ := H
  by_cases hiL : i < L.length
  · rw [List.getElem_append_left (by simpa using hiL), List.getElem_reverse]
    rw [H2 _ (by omega)]
    congr 1; apply propext; push_cast [Nat.sub_sub, Nat.cast_sub (show 1 + i ≤ L.length by omega)]
    constructor <;> intro <;> omega
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.length_reverse]
    rw [H1 _ (by simp at hi; omega)]
    congr 1; apply propext; push_cast [Nat.cast_sub (show L.length ≤ i by omega)]
    constructor <;> intro <;> omega

end Lax119563Proofs.Bridges.TM2Sim
