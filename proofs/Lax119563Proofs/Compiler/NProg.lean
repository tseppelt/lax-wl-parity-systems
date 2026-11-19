import Lax119563Proofs.Reduction.HProg

/-!
# Register programs with number stacks

`NProg R Q` extends the register language `Reduction.HProg R` by `Q` *number stacks*, each
holding a list of naturals (top first):
* `spush q r`: push the value of register `r` onto stack `q`;
* `spop q r`: pop the top of the nonempty stack `q` into register `r`;
* conditions of `ite`/`loop` see the zero/parity view of the registers and whether each
  stack is nonempty (`NSt.view`).

Semantics `NRuns x w p st st' t` with the uniform word size `w` of `HRuns`: every primitive
requires the values it touches (registers, the pushed or popped number) to be `< 2^w` and
costs `unitCost w`. The compiler (`Compiler.NCompile`) simulates runs within the same cost;
stacks are stored as `bs (encodeNats vs)` (`Compiler.NumStack`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

/-- The view used by conditions: registers (zero / parity) and stacks (nonempty). -/
abbrev NView (R Q : ℕ) := (Fin R → Option Bool) × (Fin Q → Bool)

/-- Programs over registers `Fin R` and number stacks `Fin Q`. -/
inductive NProg (R Q : ℕ) where
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
  | spush (q : Fin Q) (r : Fin R)
  | spop (q : Fin Q) (r : Fin R)
  | seq (p q : NProg R Q)
  | ite (c : NView R Q → Bool) (p q : NProg R Q)
  | loop (c : NView R Q → Bool) (p : NProg R Q)

/-- States: registers, number stacks, input cursor, emitted numbers. -/
@[ext]
structure NSt (R Q : ℕ) where
  env : Fin R → ℕ
  stk : Fin Q → List ℕ
  pos : ℕ
  out : List ℕ

namespace NSt

variable {R Q : ℕ}

/-- The view of a state. -/
def view (st : NSt R Q) : NView R Q :=
  (fun r => if st.env r = 0 then none else some (st.env r % 2 == 1),
    fun q => !(st.stk q).isEmpty)

/-- Set a register. -/
def set (st : NSt R Q) (r : Fin R) (v : ℕ) : NSt R Q :=
  { st with env := Function.update st.env r v }

/-- Replace a stack. -/
def setS (st : NSt R Q) (q : Fin Q) (l : List ℕ) : NSt R Q :=
  { st with stk := Function.update st.stk q l }

@[simp] lemma set_env (st : NSt R Q) (r : Fin R) (v : ℕ) :
    (st.set r v).env = Function.update st.env r v := rfl
@[simp] lemma set_stk (st : NSt R Q) (r : Fin R) (v : ℕ) : (st.set r v).stk = st.stk := rfl
@[simp] lemma set_pos (st : NSt R Q) (r : Fin R) (v : ℕ) : (st.set r v).pos = st.pos := rfl
@[simp] lemma set_out (st : NSt R Q) (r : Fin R) (v : ℕ) : (st.set r v).out = st.out := rfl
@[simp] lemma setS_env (st : NSt R Q) (q : Fin Q) (l : List ℕ) : (st.setS q l).env = st.env := rfl
@[simp] lemma setS_stk (st : NSt R Q) (q : Fin Q) (l : List ℕ) :
    (st.setS q l).stk = Function.update st.stk q l := rfl
@[simp] lemma setS_pos (st : NSt R Q) (q : Fin Q) (l : List ℕ) : (st.setS q l).pos = st.pos := rfl
@[simp] lemma setS_out (st : NSt R Q) (q : Fin Q) (l : List ℕ) : (st.setS q l).out = st.out := rfl

end NSt

variable {R Q : ℕ}

/-- Big-step semantics with word size `w` on input `x`. -/
inductive NRuns (x : List Bool) (w : ℕ) : NProg R Q → NSt R Q → NSt R Q → ℕ → Prop
  | clr {r st} : st.env r < 2 ^ w → NRuns x w (.clr r) st (st.set r 0) (unitCost w)
  | one {r st} : 2 * st.env r + 1 < 2 ^ w →
      NRuns x w (.one r) st (st.set r (2 * st.env r + 1)) (unitCost w)
  | dbl {r st} : 2 * st.env r < 2 ^ w → NRuns x w (.dbl r) st (st.set r (2 * st.env r)) (unitCost w)
  | half {r st} : st.env r < 2 ^ w → NRuns x w (.half r) st (st.set r (st.env r / 2)) (unitCost w)
  | copy {r s st} : r ≠ s → st.env r < 2 ^ w → st.env s < 2 ^ w →
      NRuns x w (.copy r s) st (st.set s (st.env r)) (unitCost w)
  | add {r s st} : r ≠ s → st.env r + st.env s < 2 ^ w →
      NRuns x w (.add r s) st (st.set r (st.env r + st.env s)) (unitCost w)
  | lt {f a b st} : f ≠ a → f ≠ b → a ≠ b → st.env f < 2 ^ w → st.env a < 2 ^ w →
      st.env b < 2 ^ w →
      NRuns x w (.lt f a b) st (st.set f (if st.env a < st.env b then 1 else 0)) (unitCost w)
  | emit {r st} : st.env r < 2 ^ w →
      NRuns x w (.emit r) st { st with out := st.out ++ [st.env r] } (unitCost w)
  | rd {r st} : st.env r < 2 ^ w → st.pos ≤ x.length →
      NRuns x w (.rd r) st
        { (st.set r (inBit x st.pos)) with pos := min (st.pos + 1) x.length } (unitCost w)
  | rst {st} : st.pos ≤ x.length →
      NRuns x w .rst st { st with pos := 0 } (unitCost w * (st.pos + 1))
  | spush {q r st} : st.env r < 2 ^ w →
      NRuns x w (.spush q r) st (st.setS q (st.env r :: st.stk q)) (unitCost w)
  | spop {q r st v vs} : st.env r < 2 ^ w → st.stk q = v :: vs → v < 2 ^ w →
      NRuns x w (.spop q r) st ((st.setS q vs).set r v) (unitCost w)
  | seq {p q st₁ st₂ st₃ t₁ t₂} : NRuns x w p st₁ st₂ t₁ → NRuns x w q st₂ st₃ t₂ →
      NRuns x w (.seq p q) st₁ st₃ (t₁ + t₂)
  | iteT {c p q st st' t} : c st.view = true → NRuns x w p st st' t →
      NRuns x w (.ite c p q) st st' (t + 1)
  | iteF {c p q st st' t} : c st.view = false → NRuns x w q st st' t →
      NRuns x w (.ite c p q) st st' (t + 1)
  | loopF {c p st} : c st.view = false → NRuns x w (.loop c p) st st 1
  | loopT {c p st₁ st₂ st₃ t₁ t₂} : c st₁.view = true → NRuns x w p st₁ st₂ t₁ →
      NRuns x w (.loop c p) st₂ st₃ t₂ → NRuns x w (.loop c p) st₁ st₃ (t₁ + t₂ + 1)

/-- The cursor stays within the input. -/
lemma NRuns.pos_le {x : List Bool} {w : ℕ} {p : NProg R Q} {st st' : NSt R Q} {t : ℕ}
    (h : NRuns x w p st st' t) (hp : st.pos ≤ x.length) : st'.pos ≤ x.length := by
  induction h with
  | rd => simp
  | rst => simp
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hp)
  | iteT _ _ ih => exact ih hp
  | iteF _ _ ih => exact ih hp
  | loopF => exact hp
  | loopT _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ hp)
  | _ => simpa using hp

end Lax119563Proofs.Compiler
