import Lax119563Proofs.Reduction.DomGen

/-!
# Infrastructure of the system generator

* `Iv M x s ℓ H`: the compiled code-ordered time program (as in `out_schEnum`);
* `schEnum_ctx`: the schema enumerator as `(range E).flatMap` over contexts `SchCtx`.
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

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

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

/-! ## The shift of a permutation described by a mask -/

end Lax119563Proofs.Reduction
