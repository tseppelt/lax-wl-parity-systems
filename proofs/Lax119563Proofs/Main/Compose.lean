import Mathlib.Tactic.DeriveFintype
import Lax119563Proofs.Main.AbstractMachine

/-!
# Composing a reduction with a decider

Given deterministic machines `R` (a reduction, computing `y` from `x` on tape `0`) and `D`
(a decider), we build one deterministic machine that, on input `x`,

1. inspects the first two input cells and answers directly on inputs of length `< 2`
   (the answers are fixed parameters), and otherwise marks the origin on an extra tape;
2. simulates `R` on its own tapes, moving the head of the marker tape together with the
   head of tape `0` and remembering on which side of the origin that head is;
3. once `R` halts (its answer is ignored), moves the head of tape `0` back to the origin;
4. simulates `D` on tape `0` and fresh tapes of its own, returning `D`'s answer.

If `R` computes `y` within `t₁` steps and `D` decides `P` on `y` within `t₂` steps, the
composed machine decides `P` on `x` within `2 t₁ + t₂ + 3` steps.
-/

open Lax489179.TuringMachine (Machine Config Move Instruction init step run Deterministic)
open Lax119563.DeterministicTime

namespace Lax119563Proofs.Main.Compose

open AMachine

/-- Control states of the composed machine other than the initial one. -/
inductive St (R D : Machine) : Type
  | chk (b : Bool)
  | sim (q : Fin (R.states + 1)) (sg : Bool)
  | rew (sg : Bool)
  | dec (q : Fin (D.states + 1))
  deriving DecidableEq, Fintype

/-- Tapes of the composed machine other than tape `0`: the tapes `1, …` of `R`, a marker
tape, and the tapes `1, …` of `D`. -/
inductive Tp (R D : Machine) : Type
  | r (j : Fin R.tapes)
  | mk
  | d (j : Fin D.tapes)
  deriving DecidableEq, Fintype

variable (R D : Machine)

/-- The alphabet size parameter of the composed machine. -/
abbrev S : ℕ := max R.symbols D.symbols

/-- Reading a symbol of a larger alphabet in a smaller one (unused symbols become blank). -/
def clamp {m : ℕ} (n : ℕ) (v : Fin m) : Fin (n + 3) :=
  if h : v.val < n + 3 then ⟨v.val, h⟩ else 0

theorem clamp_castLE {n m : ℕ} (h : n + 3 ≤ m) (v : Fin (n + 3)) :
    clamp n (Fin.castLE h v) = v := by
  simp [clamp, v.isLt]

def embR : Fin (R.symbols + 3) → Fin (S R D + 3) :=
  Fin.castLE (Nat.add_le_add_right (le_max_left _ _) 3)

def embD : Fin (D.symbols + 3) → Fin (S R D + 3) :=
  Fin.castLE (Nat.add_le_add_right (le_max_right _ _) 3)

/-- Tape `j` of `R` as a tape of the composed machine. -/
def rT (j : Fin (R.tapes + 1)) : Option (Tp R D) := Fin.cases none (fun j => some (.r j)) j

/-- Tape `j` of `D` as a tape of the composed machine. -/
def dT (j : Fin (D.tapes + 1)) : Option (Tp R D) := Fin.cases none (fun j => some (.d j)) j

@[simp] theorem rT_zero : rT R D 0 = none := rfl
@[simp] theorem rT_succ (j : Fin R.tapes) : rT R D j.succ = some (.r j) := rfl
@[simp] theorem dT_zero : dT R D 0 = none := rfl
@[simp] theorem dT_succ (j : Fin D.tapes) : dT R D j.succ = some (.d j) := rfl

/-- The marker symbol. -/
def mark : Fin (S R D + 3) := 1

/-- The contents of the marker tape: a mark at the origin. -/
def mkTape : ℤ → Fin (S R D + 3) := fun z => if z = 0 then mark R D else 0

theorem mark_ne_zero : mark R D ≠ 0 := by
  simp [mark]

theorem mkTape_eq_mark_iff (z : ℤ) : mkTape R D z = mark R D ↔ z = 0 := by
  unfold mkTape
  split_ifs with h
  · simp [h]
  · simp [h, (mark_ne_zero R D).symm]

variable {R D}

/-- Whether a move goes to the right. -/
def isRight : Move → Bool
  | .right => true
  | _ => false

/-- Writes of a simulated step of `R`. -/
def rWrite (w : Fin (R.tapes + 1) → Fin (R.symbols + 3))
    (sc : Option (Tp R D) → Fin (S R D + 3)) : Option (Tp R D) → Fin (S R D + 3)
  | none => embR R D (w 0)
  | some (.r j) => embR R D (w j.succ)
  | some .mk => sc (some .mk)
  | some (.d j) => sc (some (.d j))

/-- Moves of a simulated step of `R`; the marker head moves with the head of tape `0`. -/
def rMove (m : Fin (R.tapes + 1) → Move) : Option (Tp R D) → Move
  | none => m 0
  | some (.r j) => m j.succ
  | some .mk => m 0
  | some (.d _) => .stay

/-- Writes of a simulated step of `D`. -/
def dWrite (w : Fin (D.tapes + 1) → Fin (D.symbols + 3))
    (sc : Option (Tp R D) → Fin (S R D + 3)) : Option (Tp R D) → Fin (S R D + 3)
  | none => embD R D (w 0)
  | some (.r j) => sc (some (.r j))
  | some .mk => sc (some .mk)
  | some (.d j) => embD R D (w j.succ)

/-- Moves of a simulated step of `D`. -/
def dMove (m : Fin (D.tapes + 1) → Move) : Option (Tp R D) → Move
  | none => m 0
  | some (.r _) => .stay
  | some .mk => .stay
  | some (.d j) => m j.succ

theorem rWrite_rT (w : Fin (R.tapes + 1) → Fin (R.symbols + 3))
    (sc : Option (Tp R D) → Fin (S R D + 3)) (j : Fin (R.tapes + 1)) :
    rWrite w sc (rT R D j) = embR R D (w j) := by
  cases j using Fin.cases <;> rfl

theorem rMove_rT (m : Fin (R.tapes + 1) → Move) (j : Fin (R.tapes + 1)) :
    rMove (D := D) m (rT R D j) = m j := by
  cases j using Fin.cases <;> rfl

theorem dWrite_dT (w : Fin (D.tapes + 1) → Fin (D.symbols + 3))
    (sc : Option (Tp R D) → Fin (S R D + 3)) (j : Fin (D.tapes + 1)) :
    dWrite w sc (dT R D j) = embD R D (w j) := by
  cases j using Fin.cases <;> rfl

theorem dMove_dT (m : Fin (D.tapes + 1) → Move) (j : Fin (D.tapes + 1)) :
    dMove (R := R) m (dT R D j) = m j := by
  cases j using Fin.cases <;> rfl

/-- The transition function of the composed machine; `a₀` and `a₁ b` are the answers on the
inputs `[]` and `[b]`. -/
def δ (a₀ : Bool) (a₁ : Bool → Bool) :
    Option (St R D) → (Option (Tp R D) → Fin (S R D + 3)) → AInstr (St R D) (Tp R D) (S R D)
  | none, sc =>
    if sc none = 0 then .halt a₀
    else .next (some (.chk (decide (sc none = 2))))
      (fun o => if o = some .mk then mark R D else sc o)
      (fun o => if o = none then .right else .stay)
  | some (.chk b), sc =>
    if sc none = 0 then .halt (a₁ b)
    else .next (some (.sim 0 true)) sc (fun o => if o = none then .left else .stay)
  | some (.sim q sg), sc =>
    match R.transition q (fun j => clamp R.symbols (sc (rT R D j))) false with
    | .halt _ => .next (some (.rew sg)) sc (fun _ => .stay)
    | .next q' w m =>
      .next (some (.sim q' (if sc (some .mk) = mark R D then isRight (m 0) else sg)))
        (rWrite w sc) (rMove m)
  | some (.rew sg), sc =>
    if sc (some .mk) = mark R D then .next (some (.dec 0)) sc (fun _ => .stay)
    else .next (some (.rew sg)) sc
      (fun o => if o = none ∨ o = some .mk then (if sg then .left else .right) else .stay)
  | some (.dec q), sc =>
    match D.transition q (fun j => clamp D.symbols (sc (dT R D j))) false with
    | .halt b => .halt b
    | .next q' w m => .next (some (.dec q')) (dWrite w sc) (dMove m)

variable (R D) in
/-- The composed machine, as a structured machine. -/
def comp (a₀ : Bool) (a₁ : Bool → Bool) : AMachine (St R D) (Tp R D) (S R D) := ⟨δ a₀ a₁⟩

end Lax119563Proofs.Main.Compose
