import Lax119563Proofs.Computability.SimExtract
import Lax119563Proofs.Main.ComposeMain

/-!
# Simulating a machine by a structured statement

The complete simulators:
* `simNat M ρ κ`: runs `M` on `encodeNat k`, where `k` is the value of the register `inp`;
* `simIn M ρ κ`: runs `M` on the input `x` of the statement.

If `M` computes `encodeNat v`, they leave `v` in the register `out` and the halting time of
`M` in `clk`, empty all their stacks, and change no register outside the range of `ρ` and
no stack outside the range of `κ` (`simNat_good`, `simIn_good`). The cost is linear in the
halting time and the input length, with a factor depending on `M` and on the word size.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler
open Lax119563.DeterministicTime
open Lax489179.TuringMachine (Machine Config Instruction Move)

namespace Lax119563Proofs.Computability

open CStm

variable {R Q : ℕ} {x : List Bool} {w : ℕ} {M : Machine}
variable (ρ : Rg (M.tapes + 1) ↪ Fin R) (κ : Sk (M.tapes + 1) ↪ Fin Q)

/-! ## The statements -/

/-- All stacks of the simulator. -/
noncomputable def allSk (n : ℕ) : List (Sk n) := (Finset.univ : Finset (Sk n)).toList

lemma mem_allSk {n : ℕ} (g : Sk n) : g ∈ allSk n := Finset.mem_toList.mpr (Finset.mem_univ _)

variable (M) in
/-- Empty all stacks of the simulator. -/
noncomputable def clearAll : CStm R Q :=
  seqL ((allSk (M.tapes + 1)).map fun g => clrS (κ g) (ρ .tmp) (ρ .flg))

variable (M) in
/-- Load `encodeNat (inp)` onto the stack of tape `0`. -/
def loadNat : CStm R Q :=
  seqL [.set (ρ .tmp) (.var (ρ .inp)), pushBits (κ .aux) (ρ .tmp), .push (κ .aux) (.const 1),
    moveAllS (κ .aux) (κ (.R 0)) (ρ .tmp) (ρ .flg)]

variable (M) in
/-- Load the input onto the stack of tape `0`. -/
def loadIn : CStm R Q :=
  seqL [.rst, readIn (κ .aux) (ρ .tmp), moveAllS (κ .aux) (κ (.R 0)) (ρ .tmp) (ρ .flg)]

variable (M) in
/-- Simulation, output and cleanup. -/
noncomputable def simTail : CStm R Q := seqL [core M ρ κ, extract M ρ κ, clearAll M ρ κ]

variable (M) in
/-- **The simulator on a number**: run `M` on `encodeNat (inp)`. -/
noncomputable def simNat : CStm R Q := .seq (loadNat M ρ κ) (simTail M ρ κ)

variable (M) in
/-- **The simulator on the input**: run `M` on the input of the statement. -/
noncomputable def simIn : CStm R Q := .seq (loadIn M ρ κ) (simTail M ρ κ)

/-! ## Frames -/

section Frame

variable {r : Fin R} {q : Fin Q}

lemma wReg_seqL_map {α : Type} (f : α → CStm R Q) (l : List α)
    (h : ∀ a ∈ l, wReg r (f a) = false) : wReg r (seqL (l.map f)) = false := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, seqL, wReg, Bool.or_eq_false_iff]
    exact ⟨h a (by simp), ih fun b hb => h b (by simp [hb])⟩

lemma wStk_seqL_map {α : Type} (f : α → CStm R Q) (l : List α)
    (h : ∀ a ∈ l, wStk q (f a) = false) : wStk q (seqL (l.map f)) = false := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, seqL, wStk, Bool.or_eq_false_iff]
    exact ⟨h a (by simp), ih fun b hb => h b (by simp [hb])⟩

lemma wOut_seqL_map {α : Type} (f : α → CStm R Q) (l : List α)
    (h : ∀ a ∈ l, wOut (f a) = false) : wOut (seqL (l.map f)) = false := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, seqL, wOut, Bool.or_eq_false_iff]
    exact ⟨h a (by simp), ih fun b hb => h b (by simp [hb])⟩

lemma wPos_seqL_map {α : Type} (f : α → CStm R Q) (l : List α)
    (h : ∀ a ∈ l, wPos (f a) = false) : wPos (seqL (l.map f)) = false := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, seqL, wPos, Bool.or_eq_false_iff]
    exact ⟨h a (by simp), ih fun b hb => h b (by simp [hb])⟩

lemma wReg_chain (l : List (Key M)) (h : ∀ p, wReg r (leaf M ρ κ p : CStm R Q) = false) :
    wReg r (chain M ρ κ l : CStm R Q) = false := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [chain_cons]; simp [wReg, h p, ih]

lemma wStk_chain (l : List (Key M)) (h : ∀ p, wStk q (leaf M ρ κ p : CStm R Q) = false) :
    wStk q (chain M ρ κ l : CStm R Q) = false := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [chain_cons]; simp [wStk, h p, ih]

lemma wOut_chain (l : List (Key M)) (h : ∀ p, wOut (leaf M ρ κ p : CStm R Q) = false) :
    wOut (chain M ρ κ l : CStm R Q) = false := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [chain_cons]; simp [wOut, h p, ih]

lemma wPos_chain (l : List (Key M)) (h : ∀ p, wPos (leaf M ρ κ p : CStm R Q) = false) :
    wPos (chain M ρ κ l : CStm R Q) = false := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [chain_cons]; simp [wPos, h p, ih]

variable (hr : ∀ g, ρ g ≠ r) (hq : ∀ g, κ g ≠ q)
include hr

lemma wReg_core : wReg r (core M ρ κ : CStm R Q) = false := by
  have hleaf : ∀ p, wReg r (leaf M ρ κ p : CStm R Q) = false := by
    intro p
    unfold leaf
    split
    · simp only [wReg, Bool.or_eq_false_iff, decide_eq_false_iff_not]
      exact ⟨hr _, wReg_seqL_map _ _ fun j _ => by simp [pushT, wReg]⟩
    · simp only [wReg, Bool.or_eq_false_iff, decide_eq_false_iff_not]
      refine ⟨hr _, wReg_seqL_map _ _ fun j _ => ?_⟩
      unfold opT; split <;> simp [wReg, hr]
  simp only [core, body, wReg, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  exact ⟨hr _, hr _, hr _, wReg_seqL_map _ _ fun j _ => by simp [popT, wReg, hr],
    wReg_chain ρ κ _ hleaf, hr _⟩

lemma wReg_tail : wReg r (simTail M ρ κ : CStm R Q) = false := by
  simp only [simTail, seqL, wReg, Bool.or_eq_false_iff]
  refine ⟨wReg_core ρ κ hr, ?_, ?_, trivial⟩
  · simp [extract, seqL, wReg, moveAllS, skipZ, parseB, hr]
  · exact wReg_seqL_map _ _ fun g _ => by simp [clrS, wReg, hr]

lemma wReg_simNat : wReg r (simNat M ρ κ : CStm R Q) = false := by
  simp only [simNat, wReg, Bool.or_eq_false_iff]
  refine ⟨?_, wReg_tail ρ κ hr⟩
  simp [loadNat, seqL, wReg, pushBits, moveAllS, hr]

lemma wReg_simIn : wReg r (simIn M ρ κ : CStm R Q) = false := by
  simp only [simIn, wReg, Bool.or_eq_false_iff]
  refine ⟨?_, wReg_tail ρ κ hr⟩
  simp [loadIn, seqL, wReg, readIn, moveAllS, hr]

omit hr
include hq

lemma wStk_core : wStk q (core M ρ κ : CStm R Q) = false := by
  have hleaf : ∀ p, wStk q (leaf M ρ κ p : CStm R Q) = false := by
    intro p
    unfold leaf
    split
    · simp only [wStk, Bool.or_eq_false_iff]
      exact ⟨trivial, wStk_seqL_map _ _ fun j _ => by simp [pushT, wStk, hq]⟩
    · simp only [wStk, Bool.or_eq_false_iff]
      refine ⟨trivial, wStk_seqL_map _ _ fun j _ => ?_⟩
      unfold opT; split <;> simp [wStk, hq]
  simp only [core, body, wStk, Bool.or_eq_false_iff]
  exact ⟨trivial, trivial, trivial, wStk_seqL_map _ _ fun j _ => by simp [popT, wStk, hq],
    wStk_chain ρ κ _ hleaf, trivial⟩

lemma wStk_tail : wStk q (simTail M ρ κ : CStm R Q) = false := by
  simp only [simTail, seqL, wStk, Bool.or_eq_false_iff]
  refine ⟨wStk_core ρ κ hq, ?_, ?_, trivial⟩
  · simp [extract, seqL, wStk, moveAllS, skipZ, parseB, hq]
  · exact wStk_seqL_map _ _ fun g _ => by simp [clrS, wStk, hq]

lemma wStk_simNat : wStk q (simNat M ρ κ : CStm R Q) = false := by
  simp only [simNat, wStk, Bool.or_eq_false_iff]
  refine ⟨?_, wStk_tail ρ κ hq⟩
  simp [loadNat, seqL, wStk, pushBits, moveAllS, hq]

lemma wStk_simIn : wStk q (simIn M ρ κ : CStm R Q) = false := by
  simp only [simIn, wStk, Bool.or_eq_false_iff]
  refine ⟨?_, wStk_tail ρ κ hq⟩
  simp [loadIn, seqL, wStk, readIn, moveAllS, hq]

omit hq

lemma wOut_core : wOut (core M ρ κ : CStm R Q) = false := by
  have hleaf : ∀ p, wOut (leaf M ρ κ p : CStm R Q) = false := by
    intro p
    unfold leaf
    split
    · simp only [wOut, Bool.or_eq_false_iff]
      exact ⟨trivial, wOut_seqL_map _ _ fun j _ => rfl⟩
    · simp only [wOut, Bool.or_eq_false_iff]
      refine ⟨trivial, wOut_seqL_map _ _ fun j _ => ?_⟩
      unfold opT; split <;> rfl
  simp only [core, body, wOut, Bool.or_eq_false_iff]
  exact ⟨trivial, trivial, trivial, wOut_seqL_map _ _ fun j _ => rfl, wOut_chain ρ κ _ hleaf, trivial⟩

lemma wPos_core : wPos (core M ρ κ : CStm R Q) = false := by
  have hleaf : ∀ p, wPos (leaf M ρ κ p : CStm R Q) = false := by
    intro p
    unfold leaf
    split
    · simp only [wPos, Bool.or_eq_false_iff]
      exact ⟨trivial, wPos_seqL_map _ _ fun j _ => rfl⟩
    · simp only [wPos, Bool.or_eq_false_iff]
      refine ⟨trivial, wPos_seqL_map _ _ fun j _ => ?_⟩
      unfold opT; split <;> rfl
  simp only [core, body, wPos, Bool.or_eq_false_iff]
  exact ⟨trivial, trivial, trivial, wPos_seqL_map _ _ fun j _ => rfl, wPos_chain ρ κ _ hleaf, trivial⟩

lemma wOut_tail : wOut (simTail M ρ κ : CStm R Q) = false := by
  simp only [simTail, seqL, wOut, Bool.or_eq_false_iff]
  refine ⟨wOut_core ρ κ, by simp [extract, seqL, wOut, moveAllS, skipZ, parseB],
    wOut_seqL_map _ _ fun g _ => by simp [clrS, wOut], trivial⟩

lemma wPos_tail : wPos (simTail M ρ κ : CStm R Q) = false := by
  simp only [simTail, seqL, wPos, Bool.or_eq_false_iff]
  refine ⟨wPos_core ρ κ, by simp [extract, seqL, wPos, moveAllS, skipZ, parseB],
    wPos_seqL_map _ _ fun g _ => by simp [clrS, wPos], trivial⟩

lemma wOut_simNat : wOut (simNat M ρ κ : CStm R Q) = false := by
  simp only [simNat, wOut, Bool.or_eq_false_iff]
  exact ⟨by simp [loadNat, seqL, wOut, pushBits, moveAllS], wOut_tail ρ κ⟩

lemma wPos_simNat : wPos (simNat M ρ κ : CStm R Q) = false := by
  simp only [simNat, wPos, Bool.or_eq_false_iff]
  exact ⟨by simp [loadNat, seqL, wPos, pushBits, moveAllS], wPos_tail ρ κ⟩

lemma wOut_simIn : wOut (simIn M ρ κ : CStm R Q) = false := by
  simp only [simIn, wOut, Bool.or_eq_false_iff]
  exact ⟨by simp [loadIn, seqL, wOut, readIn, moveAllS], wOut_tail ρ κ⟩

end Frame

end Lax119563Proofs.Computability
