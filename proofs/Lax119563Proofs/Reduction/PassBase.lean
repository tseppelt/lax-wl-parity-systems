import Lax119563Proofs.Reduction.DomGen

/-!
# Infrastructure of the system generator

* `Iv M x s ℓ H`: the compiled code-ordered time program (as in `out_schEnum`);
* `globs`: the global values at the stack levels `0 … 13` (computed by the prelude), and
  `GlobOK` (the stack starts with them);
* `schEnum_ctx`: the schema enumerator as `(range E).flatMap` over contexts `SchCtx`;
* `violAt`: the domain test of the schema of a schema stack at a coordinate
  (`violAt_nil_iff`);
* `shiftX`: the shift `shiftVal s ℓ m i` of a permutation described by a mask.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs

/-! ## The system -/

/-- The code-ordered verifier program for the width `ℓ` and horizon `H`. -/
noncomputable abbrev APv (M : Machine) (x : List Bool) (s ℓ H : ℕ) : RegisterProgram s ℓ :=
  AP (ℓ := ℓ) (N := numLoc M H) Loc.code Loc.accept Loc.reject code_accept_ne_reject
    (verifierCmds' M x s ℓ H)

/-- Its compiled implicit parity system. -/
noncomputable def Iv (M : Machine) (x : List Bool) (s ℓ H : ℕ) :
    ImplicitParitySystem (s + 1) ℓ :=
  (APv M x s ℓ H).compile (Loc.query : Loc M H).code (fun _ _ => 0)

lemma Iv_schemas {M : Machine} {x : List Bool} {s ℓ H : ℕ} : (Iv M x s ℓ H).schemas =
    (APv M x s ℓ H).compiledSchemas (Loc.query : Loc M H).code (fun _ _ => 0) := rfl

/-! ## Globals -/

/-- The global values, at the stack levels `0 … 13` (`2^ℓ` at level `13`, so that the
`loopX` over register values has a limit of class `P 1 0`). -/
noncomputable def globs (M : Machine) (x : List Bool) (s ℓ H : ℕ) : List ℕ :=
  [x.length, Nat.log 2 x.length, ℓ, H, radix M H, numLoc M H, (verifierCmds' M x s ℓ H).length,
    ((verifierCmds' M x s ℓ H).map cmdSz).sum, (Loc.code (Loc.query : Loc M H)).val,
    (Loc.code (Loc.accept : Loc M H)).val, (Iv M x s ℓ H).schemas.length,
    (Iv M x s ℓ H).numLocations, numLoc M H + 8 * (verifierCmds' M x s ℓ H).length + 3, 2 ^ ℓ]

/-- The stack starts with the globals. -/
def GlobOK (M : Machine) (x : List Bool) (s ℓ H : ℕ) (ρ : List ℕ) : Prop :=
  ρ.take 14 = globs M x s ℓ H

/-- Global expressions. -/
abbrev gℓ : Xp := var 2
abbrev gH : Xp := var 3
abbrev gR : Xp := var 4
abbrev gN : Xp := var 5
abbrev gr : Xp := var 6
abbrev gEc : Xp := var 7
abbrev gp0 : Xp := var 8
abbrev gacc : Xp := var 9
abbrev gE : Xp := var 10
abbrev gW : Xp := var 11
abbrev gdet : Xp := var 12
abbrev gP : Xp := var 13

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

section GlobEval

variable {ρ : List ℕ} (h : GlobOK M x s ℓ H ρ)
include h

end GlobEval

/-! ## Stacks -/

lemma getD_app (τ l : List ℕ) (k : ℕ) : (τ ++ l).getD (τ.length + k) 0 = l.getD k 0 := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  congr 1; omega

/-! ## The schema enumerator as a loop over schema indices -/

/-- The context of the body of the schema enumerator for schema `e`. -/
def SchCtx (M : Machine) (x : List Bool) (s ℓ H b : ℕ) (ρ : List ℕ) (τ : List ℕ) (e : ℕ)
    (sc : Schema (s + 1) ℓ (Iv M x s ℓ H).numLocations) : Prop :=
  τ.length = b + 37 ∧ τ.take b = ρ ∧ τ.getD (b + 27) 0 = e ∧
    SchRec M x s ℓ H sc (τ.drop (b + 28))

lemma flatMap_eq_range {α β : Type} (l : List α) (d : α) (f : α → List β) :
    l.flatMap f = (List.range l.length).flatMap fun e => f (l.getD e d) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, ih, List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map]
    simp

lemma forall₂_getD {α β : Type} {R : α → β → Prop} (d : β) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ i (h₁ : i < l₁.length),
      R l₁[i] (l₂.getD i d)
  | _ :: _, _ :: _, List.Forall₂.cons h _, 0, _ => h
  | _ :: _, _ :: _, List.Forall₂.cons _ t, i + 1, h₁ => by
    simpa using forall₂_getD d t i (by simpa using h₁)

lemma getD_of_map_eq_range {α : Type} (f : α → ℕ) (d : α) {l : List α}
    (h : l.map f = List.range l.length) {i : ℕ} (hi : i < l.length) : f (l.getD i d) = i := by
  have := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, List.getElem?_range hi, List.getElem?_eq_getElem hi,
    Option.map_some, Option.some.injEq] at this
  rw [List.getD_eq_getElem _ _ hi]
  exact this

/-! ## Register values of block coordinates -/

lemma regVal_toBlk {v : ℕ} (hv : v < 2 ^ ℓ) : Circuits.regVal (toBlk ℓ v) = v := by
  rw [toBlk, regVal_ofAddr]
  simp [Circuits.field, Nat.mod_eq_of_lt hv]

/-! ## The domain test -/

/-- The domain violations of the schema of a schema stack (record at `b + 28 …`) at the
coordinate `(i, v)` of loops over `i ≤ s` and `v < 2^ℓ` (by `loopX`) entered at depth `d`
(stack `τ' ++ [s + 1, i, 2^ℓ, v, inBit x v, 0]`). -/
def violAt (s b d : ℕ) : Gn :=
  violGen s (d + 6) (var (d + 1)) (var (d + 3)) (var (d + 4)) (var (b + 33)) (var (b + 34))
    (var (b + 35)) (var (b + 36)) gℓ gH

/-! ## The shift of a permutation described by a mask -/

/-- `field m k ℓ`. -/
def fieldmX (mX kX : Xp) : Xp := xorM (shr mX kX) (const 0) gℓ

/-- `xorFields ℓ k m`. -/
def xfX (mX : Xp) : ℕ → Xp
  | 0 => const 0
  | k + 1 => xorM (xfX mX k) (fieldmX mX (mulC k gℓ)) gℓ

/-- `shiftVal s ℓ m i`. -/
def shiftX (s : ℕ) (mX iX : Xp) : Xp :=
  add (mul (fieldmX mX (mul iX gℓ)) (lt iX (const s))) (mul (xfX mX s) (Xp.not (lt iX (const s))))

section Eval

variable {σ : List ℕ} (hG : GlobOK M x s ℓ H σ)
include hG

end Eval

end Lax119563Proofs.Reduction
