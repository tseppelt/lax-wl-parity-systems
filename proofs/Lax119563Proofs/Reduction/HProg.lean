import Mathlib.Data.Fintype.Basic
import Lax119563.BinaryEncodings
import Lax119563Proofs.Reduction.Bits

/-!
# Register programs with binary registers

A small structured programming language for writing the reduction machine. A program has
registers `Fin R` holding natural numbers, reads its input `x` through a cursor `pos`, and
emits natural numbers; the output of a run is the list `out` of emitted numbers, which the
compiled machine writes as `encodeNats out`.

Instructions: `clr r` (`r := 0`), `one r` (`r := 2r + 1`), `dbl r` (`r := 2r`), `half r`
(`r := r / 2`), `copy r s` (`s := r`), `add r s` (`r := r + s`), `lt f a b`
(`f := [a < b]`), `emit r`, `rd r` (`r := x[pos] + 1`, or `0` at the end of the input;
advance the cursor), `rst` (cursor back to `0`), and sequencing, conditionals and while
loops whose conditions inspect, for every register, whether it is zero and its parity.

The big-step semantics `HRuns x w p st st' t` fixes a *word size* `w`: every primitive
instruction requires the registers it touches to stay below `2 ^ w` and costs
`unitCost w = 64 (w + 1)` (`rst` costs `unitCost w * (pos + 1)`); control costs one unit per
test. The compiled stack program (`Reduction.HCompile`) runs within the same cost.
-/

open Lax119563.BinaryEncodings

namespace Lax119563Proofs.Reduction

/-- The view of a register used by conditions: `none` for `0`, else `some` of its parity. -/
abbrev RView (R : ℕ) := Fin R → Option Bool

/-- Programs over registers `Fin R`. -/
inductive HProg (R : ℕ) where
  | clr (r : Fin R)
  | one (r : Fin R)
  | dbl (r : Fin R)
  | half (r : Fin R)
  | copy (r s : Fin R)
  | add (r s : Fin R)
  | lt (f a b : Fin R)
  | emit (r : Fin R)
  | rd (r : Fin R)
  | rst
  | seq (p q : HProg R)
  | ite (c : RView R → Bool) (p q : HProg R)
  | loop (c : RView R → Bool) (p : HProg R)

/-- States: registers, input cursor, emitted numbers. -/
@[ext]
structure HSt (R : ℕ) where
  env : Fin R → ℕ
  pos : ℕ
  out : List ℕ

namespace HSt

variable {R : ℕ}

/-- The view of the registers. -/
def view (st : HSt R) : RView R := fun r => if st.env r = 0 then none else some (st.env r % 2 == 1)

/-- Set a register. -/
def set (st : HSt R) (r : Fin R) (v : ℕ) : HSt R := { st with env := Function.update st.env r v }

@[simp] lemma set_env (st : HSt R) (r : Fin R) (v : ℕ) :
    (st.set r v).env = Function.update st.env r v := rfl
@[simp] lemma set_pos (st : HSt R) (r : Fin R) (v : ℕ) : (st.set r v).pos = st.pos := rfl
@[simp] lemma set_out (st : HSt R) (r : Fin R) (v : ℕ) : (st.set r v).out = st.out := rfl

end HSt

/-- The cost of a primitive instruction for word size `w`. -/
def unitCost (w : ℕ) : ℕ := 64 * (w + 1)

/-- The value read at cursor position `pos`. -/
def inBit (x : List Bool) (pos : ℕ) : ℕ := rdVal (x.drop pos)

variable {R : ℕ}

/-- Big-step semantics with word size `w` on input `x`. -/
inductive HRuns (x : List Bool) (w : ℕ) : HProg R → HSt R → HSt R → ℕ → Prop
  | clr {r st} : st.env r < 2 ^ w → HRuns x w (.clr r) st (st.set r 0) (unitCost w)
  | one {r st} : 2 * st.env r + 1 < 2 ^ w →
      HRuns x w (.one r) st (st.set r (2 * st.env r + 1)) (unitCost w)
  | dbl {r st} : 2 * st.env r < 2 ^ w → HRuns x w (.dbl r) st (st.set r (2 * st.env r)) (unitCost w)
  | half {r st} : st.env r < 2 ^ w → HRuns x w (.half r) st (st.set r (st.env r / 2)) (unitCost w)
  | copy {r s st} : r ≠ s → st.env r < 2 ^ w → st.env s < 2 ^ w →
      HRuns x w (.copy r s) st (st.set s (st.env r)) (unitCost w)
  | add {r s st} : r ≠ s → st.env r + st.env s < 2 ^ w →
      HRuns x w (.add r s) st (st.set r (st.env r + st.env s)) (unitCost w)
  | lt {f a b st} : f ≠ a → f ≠ b → a ≠ b → st.env f < 2 ^ w → st.env a < 2 ^ w →
      st.env b < 2 ^ w →
      HRuns x w (.lt f a b) st (st.set f (if st.env a < st.env b then 1 else 0)) (unitCost w)
  | emit {r st} : st.env r < 2 ^ w →
      HRuns x w (.emit r) st { st with out := st.out ++ [st.env r] } (unitCost w)
  | rd {r st} : st.env r < 2 ^ w → st.pos ≤ x.length →
      HRuns x w (.rd r) st
        { (st.set r (inBit x st.pos)) with pos := min (st.pos + 1) x.length } (unitCost w)
  | rst {st} : st.pos ≤ x.length →
      HRuns x w .rst st { st with pos := 0 } (unitCost w * (st.pos + 1))
  | seq {p q st₁ st₂ st₃ t₁ t₂} : HRuns x w p st₁ st₂ t₁ → HRuns x w q st₂ st₃ t₂ →
      HRuns x w (.seq p q) st₁ st₃ (t₁ + t₂)
  | iteT {c p q st st' t} : c st.view = true → HRuns x w p st st' t →
      HRuns x w (.ite c p q) st st' (t + 1)
  | iteF {c p q st st' t} : c st.view = false → HRuns x w q st st' t →
      HRuns x w (.ite c p q) st st' (t + 1)
  | loopF {c p st} : c st.view = false → HRuns x w (.loop c p) st st 1
  | loopT {c p st₁ st₂ st₃ t₁ t₂} : c st₁.view = true → HRuns x w p st₁ st₂ t₁ →
      HRuns x w (.loop c p) st₂ st₃ t₂ → HRuns x w (.loop c p) st₁ st₃ (t₁ + t₂ + 1)

/-- The cursor stays within the input. -/
lemma HRuns.pos_le {x : List Bool} {w : ℕ} {p : HProg R} {st st' : HSt R} {t : ℕ}
    (h : HRuns x w p st st' t) (hp : st.pos ≤ x.length) : st'.pos ≤ x.length := by
  induction h with
  | rd => simp
  | rst => simp
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hp)
  | iteT _ _ ih => exact ih hp
  | iteF _ _ ih => exact ih hp
  | loopF => exact hp
  | loopT _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ hp)
  | _ => simpa using hp

end Lax119563Proofs.Reduction
