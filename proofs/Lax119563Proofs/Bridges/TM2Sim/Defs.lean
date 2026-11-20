import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Tactic.DeriveFintype
import Lax119563.DeterministicTime

/-!
# Simulating archive multitape machines by mathlib stack machines: the machine

Given a machine `R` of the archive model `Lax489179.TuringMachine` we build a bundled mathlib
stack machine (`Turing.FinTM2`) simulating it. The stack machine has an input/output stack
`io` over an arbitrary finite alphabet `A`; the conversion between words over `A` and the
bit strings read and written by `R` is done by two finite-state transducers:

* an *input transducer* `InTransducer A` emitting at most two bits per input symbol (and at most
  two bits at the end of the input);
* an *output transducer* `OutTransducer A` emitting at most one symbol per output bit.

For binary words both are the identity; for the three-letter alphabet of
`Lax759944.BinaryWordEncoding` they translate between the two encodings of lists of natural
numbers (see `Bridges/ToTM2`).

Each tape `j` of `R` is kept as two stacks: `R j` holds the cells from the head rightwards
(the scanned cell on top) and `L j` the cells left of the head (the nearest on top). Missing
cells are blank. A stack entry is a pair of a tape symbol and a flag; on tape `0` the flag marks
the cell at position `0`, which is needed at the end to locate the output.

The phases (labels `Lbl`):
1. `inPop`: pop the input symbols, push the transducer output (reversed) on `tmp`;
2. `inRev`: move `tmp` onto `R 0`, so that `R 0` holds the binary input from its first bit;
3. `mark`: flag the cell at the head (position `0`);
4. `sim`: one transition of `R` per stack-machine step: scan all tapes, then either halt
   (go to `gather`) or write and move on all tapes and change the state;
5. `gather`: move `L 0` onto `R 0`; `seek`: pop `R 0` up to the flagged cell;
6. `feed`: read the output bits from position `0` until a non-bit, push the output
   transducer's symbols on `outRev`;
7. `outRev`: move `outRev` onto `io`;
8. `clear`: empty all tape stacks; `done`: reset the variables and halt.
-/

open Lax489179.TuringMachine (Machine Config Move Instruction)
open Turing

namespace Lax119563Proofs.Bridges.TM2Sim

/-- A finite-state transducer from words over `A` to bit strings, emitting at most two bits per
symbol and at most two bits at the end. -/
structure InTransducer (A : Type) where
  Q : Type
  [fin : Fintype Q]
  start : Q
  δ : Q → A → Q × List Bool
  final : Q → List Bool
  δ_len : ∀ q a, (δ q a).2.length ≤ 2
  final_len : ∀ q, (final q).length ≤ 2

attribute [instance] InTransducer.fin

/-- The output of an input transducer from state `q`. -/
def InTransducer.run {A : Type} (τ : InTransducer A) : τ.Q → List A → List Bool
  | q, [] => τ.final q
  | q, a :: u => (τ.δ q a).2 ++ τ.run (τ.δ q a).1 u

/-- A finite-state transducer from bit strings to words over `A`, emitting at most one symbol
per bit. -/
structure OutTransducer (A : Type) where
  Q : Type
  [fin : Fintype Q]
  start : Q
  δ : Q → Bool → Q × Option A

attribute [instance] OutTransducer.fin

/-- The output of an output transducer from state `q`. -/
def OutTransducer.run {A : Type} (τ : OutTransducer A) : τ.Q → List Bool → List A
  | _, [] => []
  | q, b :: y => (τ.δ q b).2.toList ++ τ.run (τ.δ q b).1 y

variable (R : Machine)

/-- Tape symbols of `R`. -/
abbrev Sym := Fin (R.symbols + 3)

/-- Entries of the tape stacks: a symbol and a flag. -/
abbrev G := Sym R × Bool

/-- The blank entry. -/
def g0 : G R := (0, false)

/-- The tape symbol of a bit. -/
def bitSym (b : Bool) : Sym R := if b then 2 else 1

/-- Whether a tape symbol is a bit. -/
def isBit (s : Sym R) : Bool := s = 1 || s = 2

-- Preserve definition unfolding in the generated Fintype instances.
set_option backward.isDefEq.respectTransparency false in
/-- The stacks. -/
inductive Stk (n : ℕ)
  | io
  | outRev
  | tmp
  | L (j : Fin n)
  | R (j : Fin n)
  deriving DecidableEq, Fintype

/-- The stack alphabets: `A` on `io` and `outRev`, tape entries elsewhere. -/
@[reducible] def Γ' (A : Type) : Stk (R.tapes + 1) → Type
  | .io => A
  | .outRev => A
  | .tmp => G R
  | .L _ => G R
  | .R _ => G R

set_option backward.isDefEq.respectTransparency false in
/-- The labels. -/
inductive Lbl
  | inPop | inRev | mark | sim | gather | seek | feed | outRev | clear | done
  deriving DecidableEq, Fintype

variable (A : Type) (τi : InTransducer A) (τo : OutTransducer A)

/-- The variables of the stack machine. -/
structure Var where
  q : Fin (R.states + 1)
  scanned : Fin (R.tapes + 1) → Sym R
  cell : Option (G R)
  qi : τi.Q
  inSym : Option A
  qo : τo.Q
  outSym : Option A
  flag : Bool

/-- `Var` as a product, for finiteness. -/
def Var.equiv : Var R A τi τo ≃
    Fin (R.states + 1) × (Fin (R.tapes + 1) → Sym R) × Option (G R) × τi.Q × Option A ×
      τo.Q × Option A × Bool where
  toFun v := (v.q, v.scanned, v.cell, v.qi, v.inSym, v.qo, v.outSym, v.flag)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
    p.2.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance [Fintype A] : Fintype (Var R A τi τo) := by
  classical
  exact Fintype.ofEquiv _ (Var.equiv R A τi τo).symm

/-- The initial variables. -/
def Var.init : Var R A τi τo :=
  ⟨0, fun _ => 0, none, τi.start, none, τo.start, none, false⟩

variable {R A τi τo}

/-- The instruction of `R` for the current state and scanned symbols. -/
def instr (v : Var R A τi τo) : Instruction (R.tapes + 1) (R.symbols + 3) (R.states + 1) :=
  R.transition v.q v.scanned false

/-- Whether an instruction halts. -/
def isHalt {a b c : ℕ} : Instruction a b c → Bool
  | .halt _ => true
  | .next .. => false

/-- The symbol written on tape `j`. -/
def wr (v : Var R A τi τo) (j : Fin (R.tapes + 1)) : Sym R :=
  match instr v with
  | .next _ w _ => w j
  | .halt _ => 0

/-- The move on tape `j`. -/
def mv (v : Var R A τi τo) (j : Fin (R.tapes + 1)) : Move :=
  match instr v with
  | .next _ _ m => m j
  | .halt _ => .stay

/-- The next control state. -/
def nextQ (v : Var R A τi τo) : Fin (R.states + 1) :=
  match instr v with
  | .next q _ _ => q
  | .halt _ => v.q

/-- Whether a move goes left. -/
def isLeft : Move → Bool
  | .left => true
  | _ => false

/-- Whether a move goes right. -/
def isRight : Move → Bool
  | .right => true
  | _ => false

/-- The current input-transducer step (or its final output when the input is exhausted). -/
def inStep (v : Var R A τi τo) : τi.Q × List Bool :=
  match v.inSym with
  | some a => τi.δ v.qi a
  | none => (v.qi, τi.final v.qi)

/-- The bit of the current cell. -/
def cellBit (v : Var R A τi τo) : Bool := (v.cell.getD (g0 R)).1 = 2

/-- The entry written on a tape: the written symbol, keeping the flag of the old cell. -/
def newCell (v : Var R A τi τo) (j : Fin (R.tapes + 1)) : G R :=
  (wr v j, (v.cell.map Prod.snd).getD false)

/-- Statements of the stack machine. -/
abbrev Stmt' (R : Machine) (A : Type) (τi : InTransducer A) (τo : OutTransducer A) :=
  TM2.Stmt (Γ' R A) Lbl (Var R A τi τo)

open TM2.Stmt

/-- Push a bit on `tmp` if there is one. -/
def pushOpt (g : Var R A τi τo → Option Bool) (next : Stmt' R A τi τo) :
    Stmt' R A τi τo :=
  branch (fun v => (g v).isSome)
    (push (Γ := Γ' R A) Stk.tmp (fun v => ((bitSym R ((g v).getD false), false) : G R)) next) next

/-- Scan the tapes in `js`. -/
def scanAll : List (Fin (R.tapes + 1)) → Stmt' R A τi τo →
    Stmt' R A τi τo
  | [], next => next
  | j :: js, next =>
    peek (Γ := Γ' R A) (Stk.R j)
      (fun v o => { v with scanned := Function.update v.scanned j (o.getD (g0 R) : G R).1 })
      (scanAll js next)

/-- Write and move on tape `j`. -/
def applyOne (j : Fin (R.tapes + 1)) (next : Stmt' R A τi τo) :
    Stmt' R A τi τo :=
  pop (Γ := Γ' R A) (Stk.R j) (fun v o => { v with cell := o })
    (branch (fun v => isRight (mv v j))
      (push (Γ := Γ' R A) (Stk.L j) (fun v => newCell v j) next)
      (push (Γ := Γ' R A) (Stk.R j) (fun v => newCell v j)
        (branch (fun v => isLeft (mv v j))
          (pop (Γ := Γ' R A) (Stk.L j) (fun v o => { v with cell := o })
            (push (Γ := Γ' R A) (Stk.R j) (fun v => v.cell.getD (g0 R)) next))
          next)))

/-- Write and move on the tapes in `js`. -/
def applyAllStmt : List (Fin (R.tapes + 1)) → Stmt' R A τi τo →
    Stmt' R A τi τo
  | [], next => next
  | j :: js, next => applyOne j (applyAllStmt js next)

/-- Pop once from `L j` and `R j` for `j ∈ js`, recording in `flag` whether anything was
popped. -/
def popAll : List (Fin (R.tapes + 1)) → Stmt' R A τi τo →
    Stmt' R A τi τo
  | [], next => next
  | j :: js, next =>
    pop (Γ := Γ' R A) (Stk.L j) (fun v o => { v with flag := v.flag || o.isSome })
      (pop (Γ := Γ' R A) (Stk.R j) (fun v o => { v with flag := v.flag || o.isSome })
        (popAll js next))

variable [Inhabited A]

/-- The program. -/
def prog : Lbl → Stmt' R A τi τo
  | .inPop =>
    pop (Γ := Γ' R A) Stk.io (fun v o => { v with inSym := o })
      (pushOpt (fun v => (inStep v).2[0]?) (pushOpt (fun v => (inStep v).2[1]?)
        (branch (fun v => v.inSym.isSome)
          (load (fun v => { v with qi := (inStep v).1 }) (goto fun _ => .inPop))
          (goto fun _ => .inRev))))
  | .inRev =>
    pop (Γ := Γ' R A) Stk.tmp (fun v o => { v with cell := o })
      (branch (fun v => v.cell.isSome)
        (push (Γ := Γ' R A) (Stk.R 0) (fun v => v.cell.getD (g0 R)) (goto fun _ => .inRev))
        (goto fun _ => .mark))
  | .mark =>
    pop (Γ := Γ' R A) (Stk.R 0) (fun v o => { v with cell := o })
      (push (Γ := Γ' R A) (Stk.R 0) (fun v => (((v.cell.getD (g0 R)).1, true) : G R))
        (goto fun _ => .sim))
  | .sim =>
    scanAll (List.finRange (R.tapes + 1))
      (branch (fun v => isHalt (instr v))
        (goto fun _ => .gather)
        (applyAllStmt (List.finRange (R.tapes + 1))
          (load (fun v => { v with q := nextQ v }) (goto fun _ => .sim))))
  | .gather =>
    pop (Γ := Γ' R A) (Stk.L 0) (fun v o => { v with cell := o })
      (branch (fun v => v.cell.isSome)
        (push (Γ := Γ' R A) (Stk.R 0) (fun v => v.cell.getD (g0 R)) (goto fun _ => .gather))
        (goto fun _ => .seek))
  | .seek =>
    pop (Γ := Γ' R A) (Stk.R 0) (fun v o => { v with cell := o })
      (branch (fun v => (v.cell.map Prod.snd).getD false)
        (goto fun _ => .feed)
        (branch (fun v => v.cell.isSome) (goto fun _ => .seek) (goto fun _ => .outRev)))
  | .feed =>
    branch (fun v => isBit R (v.cell.getD (g0 R)).1)
      (branch (fun v => (τo.δ v.qo (cellBit v)).2.isSome)
        (push (Γ := Γ' R A) Stk.outRev (fun v => (τo.δ v.qo (cellBit v)).2.getD default)
          (load (fun v => { v with qo := (τo.δ v.qo (cellBit v)).1 })
            (pop (Γ := Γ' R A) (Stk.R 0) (fun v o => { v with cell := o })
              (goto fun _ => .feed))))
        (load (fun v => { v with qo := (τo.δ v.qo (cellBit v)).1 })
          (pop (Γ := Γ' R A) (Stk.R 0) (fun v o => { v with cell := o })
            (goto fun _ => .feed))))
      (goto fun _ => .outRev)
  | .outRev =>
    pop (Γ := Γ' R A) Stk.outRev (fun v o => { v with outSym := o })
      (branch (fun v => v.outSym.isSome)
        (push (Γ := Γ' R A) Stk.io (fun v => v.outSym.getD default) (goto fun _ => .outRev))
        (goto fun _ => .clear))
  | .clear =>
    load (fun v => { v with flag := false })
      (popAll (List.finRange (R.tapes + 1))
        (branch (fun v => v.flag) (goto fun _ => .clear) (goto fun _ => .done)))
  | .done => load (fun _ => Var.init R A τi τo) halt

variable (R τi τo) in
/-- The bundled stack machine. -/
noncomputable def tm [Fintype A] : FinTM2 where
  K := Stk (R.tapes + 1)
  k₀ := Stk.io
  k₁ := Stk.io
  Γ := Γ' R A
  Λ := Lbl
  main := .inPop
  σ := Var R A τi τo
  initialState := Var.init R A τi τo
  Γk₀Fin := (inferInstance : Fintype A)
  m := prog

end Lax119563Proofs.Bridges.TM2Sim
