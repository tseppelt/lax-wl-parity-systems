import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fintype

/-!
# Register programs (local copy of the shared interface)

This file copies the agreed interface of `Lax119563Proofs.Programs.RegisterProgram`, which is
developed separately. At merge time this file is to be deleted and the namespace
`Lax119563Proofs.Circuits.Stub` replaced by the shared one.

A register program has `s` registers over `𝔽₂^ℓ`, finitely many control locations among which
`accept` and `reject`, and a list of guarded commands. Acceptance is the least predicate closed
under: the accepting location accepts; an assignment at a location other than `accept`,
`reject` whose guard holds accepts if its successor configuration accepts; a fork whose guard
holds accepts if both branches accept.
-/

namespace Lax119563Proofs.Circuits.Stub

/-- A guard `⋀ᵢ aᵢ ∈ Dᵢ`. -/
structure Guard (s ℓ : ℕ) where
  sets : Fin s → Finset (Fin ℓ → ZMod 2)

/-- The guard holds for the valuation `a`. -/
def Guard.Holds {s ℓ : ℕ} (g : Guard s ℓ) (a : Fin s → Fin ℓ → ZMod 2) : Prop :=
  ∀ i, a i ∈ g.sets i

/-- An update `T(a)ᵢ = a_{σ i} + δᵢ`. -/
structure Update (s ℓ : ℕ) where
  σ : Equiv.Perm (Fin s)
  δ : Fin s → Fin ℓ → ZMod 2

/-- Applying an update. -/
def Update.apply {s ℓ : ℕ} (T : Update s ℓ) (a : Fin s → Fin ℓ → ZMod 2) :
    Fin s → Fin ℓ → ZMod 2 :=
  fun i => a (T.σ i) + T.δ i

/-- Guarded commands at a location. -/
inductive Command (s ℓ w : ℕ)
  | assign (loc : Fin w) (guard : Guard s ℓ) (update : Update s ℓ) (next : Fin w)
  | fork (loc : Fin w) (guard : Guard s ℓ) (left right : Fin w)

/-- A register program with `s` registers over `𝔽₂^ℓ`. -/
structure RegisterProgram (s ℓ : ℕ) where
  numLocations : ℕ
  accept : Fin numLocations
  reject : Fin numLocations
  accept_ne_reject : accept ≠ reject
  commands : List (Command s ℓ numLocations)

/-- Acceptance of a configuration. -/
inductive RegisterProgram.Accepts {s ℓ : ℕ} (P : RegisterProgram s ℓ) :
    Fin P.numLocations → (Fin s → Fin ℓ → ZMod 2) → Prop
  | accept (a) : RegisterProgram.Accepts P P.accept a
  | assign {p : Fin P.numLocations} {g : Guard s ℓ} {T : Update s ℓ}
      {q : Fin P.numLocations} {a : Fin s → Fin ℓ → ZMod 2} :
      Command.assign p g T q ∈ P.commands → p ≠ P.accept → p ≠ P.reject → g.Holds a →
      RegisterProgram.Accepts P q (T.apply a) → RegisterProgram.Accepts P p a
  | fork {p : Fin P.numLocations} {g : Guard s ℓ} {q r : Fin P.numLocations}
      {a : Fin s → Fin ℓ → ZMod 2} :
      Command.fork p g q r ∈ P.commands → p ≠ P.accept → p ≠ P.reject → g.Holds a →
      RegisterProgram.Accepts P q a → RegisterProgram.Accepts P r a →
      RegisterProgram.Accepts P p a

end Lax119563Proofs.Circuits.Stub
