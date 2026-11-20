import Lax119563Proofs.Hierarchy.Programs

/-!
# The universal simulator as a stack program

Tokens, stack names and the program `Universal.sim`.  See `Plan.lean` for the layout of the
code of a machine and of its configurations on the stacks.
-/

namespace Lax119563Proofs.Hierarchy.Universal

open Prog

/-- Tokens. -/
abbrev Tok := Fin 15

abbrev tT : Tok := 1
/-- Unary unit and end of a number. -/
abbrev tU : Tok := 2
abbrev tS : Tok := 3
/-- End of a tape record. -/
abbrev tR : Tok := 4
/-- End of a key, end of a table entry. -/
abbrev tM : Tok := 5
abbrev tE : Tok := 6
/-- Instruction heads: continue, halt with `false`/`true`. -/
abbrev tN : Tok := 7
abbrev tH0 : Tok := 8
abbrev tH1 : Tok := 9
/-- Head moves. -/
abbrev tL : Tok := 10
abbrev tZ : Tok := 11
abbrev tRt : Tok := 12
/-- Block separator and end of the code. -/
abbrev tSep : Tok := 13
abbrev tEnd : Tok := 14

/-- The stacks of the simulator. -/
abbrev Stk := Fin 16

abbrev IN : Stk := 0
abbrev Y : Stk := 1
abbrev P : Stk := 2
abbrev LS : Stk := 3
abbrev RS : Stk := 4
abbrev LS2 : Stk := 5
abbrev RS2 : Stk := 6
abbrev QS : Stk := 7
abbrev KEY : Stk := 8
abbrev KEY2 : Stk := 9
abbrev TBL : Stk := 10
abbrev TBL2 : Stk := 11
abbrev INS : Stk := 12
abbrev TMP : Stk := 13
abbrev DONE : Stk := 14
abbrev FLG : Stk := 15

attribute [simp] IN Y P LS RS LS2 RS2 QS KEY KEY2 TBL TBL2 INS TMP DONE FLG
attribute [simp] tT tU tS tR tM tE tN tH0 tH1 tL tZ tRt tSep tEnd

/-- Programs of the simulator. -/
abbrev SProg := Prog 16 13

/-- Top-symbol conditions. -/
abbrev Cond := (Stk → Option Tok) → Bool

def isTop (i : Stk) (a : Tok) : Cond := fun r => r i == some a
def nonempty (i : Stk) : Cond := fun r => (r i).isSome
def isEmpty (i : Stk) : Cond := fun r => (r i).isNone

/-! ## Parsing the code -/

/-- The token with a 4-bit code `v`, or `none` for the end of the code. -/
def tokOf (v : ℕ) : Option Tok := if h : v < 12 then some ⟨v + 2, by omega⟩ else none

/-- Read `k` bits from `IN` (keeping them on `Y`), then emit the token of the accumulated
value: push it on `P`, or flag the end of the code on `FLG`. -/
def readBits : ℕ → ℕ → SProg
  | 0, acc =>
    match tokOf acc with
    | some t => push P t
    | none => push FLG 0
  | k + 1, acc =>
    ite (isTop IN tT) (seq (moveOne IN Y) (readBits k (2 * acc + 1)))
      (seq (moveOne IN Y) (readBits k (2 * acc)))

/-- Parse the code into `P` (reversed) and move the rest of the input to `Y`. -/
def parse : SProg :=
  seq (loop (isEmpty FLG) (readBits 4 0)) (seq (moveAll IN Y) (pop FLG))

/-- Encode the input bits on `Y` (reversed) as the right part of tape `0` on `RS`. -/
def inputToRS : SProg :=
  loop (nonempty Y)
    (seq (ite (isTop Y tT) (seq (push RS tS) (seq (push RS tU) (push RS tU)))
      (seq (push RS tS) (push RS tU))) (pop Y))

/-- Initialisation. -/
def init : SProg :=
  seq parse
    (seq (moveAll P TBL)
      (seq (moveWhileNot TBL LS tSep)
        (seq (pop TBL)
          (seq (moveWhileNot TBL RS tSep)
            (seq (pop TBL) (seq (push RS tR) inputToRS))))))

/-! ## One simulated step -/

/-- Copy the scanned symbol of the top record of `RS` to `KEY` (blank if the record's right part
is empty). -/
def copyScanned : SProg :=
  ite (isTop RS tR) (push KEY tS) (seq (moveThrough RS TMP tS) (dupAll TMP RS KEY))

/-- Build the key: scanned symbols of all tapes, then the state. -/
def buildKey : SProg :=
  seq (loop (nonempty RS) (seq copyScanned (moveThrough RS RS2 tR)))
    (seq (moveAll RS2 RS) (seq (push KEY tS) (seq (dupAll QS TMP KEY) (moveAll TMP QS))))

/-- Duplicate tokens from `i` onto `j` and `k` while the top of `i` is not `a`. -/
def dupWhileNot (i j k : Stk) (a : Tok) : SProg :=
  loop (fun r => (r i).isSome && r i != some a)
    (seq (pushTopOf i j (List.finRange 15)) (seq (pushTopOf i k (List.finRange 15)) (pop i)))

/-- Compare `KEY` with the key of the current table entry. -/
def compare : SProg :=
  loop (fun r => (r KEY).isSome && r KEY == r TBL) (seq (moveOne KEY KEY2) (moveOne TBL TBL2))

/-- Examine one table entry: on a match copy its instruction to `INS` and flag it. -/
def examine : SProg :=
  seq compare
    (seq (ite (fun r => (r KEY).isNone && r TBL == some tM)
        (seq (push FLG 0) (seq (moveOne TBL TBL2) (dupWhileNot TBL TBL2 INS tE)))
        (moveThrough TBL TBL2 tE))
      (moveAll KEY2 KEY))

/-- Look the key up in the table. -/
def lookup : SProg :=
  seq (loop (fun r => (r TBL).isSome && (r FLG).isNone) examine)
    (seq (moveAll TBL2 TBL) (seq (pop FLG) (clear KEY)))

/-- Erase the scanned symbol of the top record of `RS` (if any). -/
def eraseScanned : SProg :=
  ite (isTop RS tR) skip (seq (moveThrough RS TMP tS) (clear TMP))

/-- Write the next symbol of the instruction on top of `RS`. -/
def writeSym : SProg := seq (moveThrough INS TMP tS) (moveAll TMP RS)

/-- Move the head of the top record according to the next token of the instruction. -/
def moveHead : SProg :=
  ite (isTop INS tL)
    (seq (pop INS)
      (ite (isTop LS tR) (push RS tS) (seq (moveThrough LS TMP tS) (moveAll TMP RS))))
    (ite (isTop INS tRt)
      (seq (pop INS) (seq (moveThrough RS TMP tS) (moveAll TMP LS)))
      (pop INS))

/-- Apply a `next` instruction. -/
def applyNext : SProg :=
  seq (pop INS)
    (seq (clear QS) (seq (moveWhileNot INS QS tS) (seq (pop INS)
      (seq (loop (nonempty RS)
          (seq eraseScanned (seq writeSym (seq moveHead
            (seq (moveThrough LS LS2 tR) (moveThrough RS RS2 tR))))))
        (seq (moveAll LS2 LS) (moveAll RS2 RS))))))

/-- Apply the instruction on `INS`. -/
def apply : SProg :=
  ite (fun r => r INS == some tH0 || r INS == some tH1) (moveOne INS DONE) applyNext

/-- One simulated step. -/
def simStep : SProg := seq buildKey (seq lookup apply)

/-- The simulator. -/
def sim : SProg := seq init (loop (isEmpty DONE) simStep)

/-- The answer of the simulator: the negation of the simulated answer. -/
def simAns (r : Stk → Option Tok) : Bool := r DONE == some tH0

end Lax119563Proofs.Hierarchy.Universal
