import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Defs

/-!
# Register programs

A register program has `s` registers over `A = 𝔽₂^ℓ`, a finite set of control locations
`{0, …, numLocations - 1}` containing distinct locations `accept` and `reject`, and a list of
guarded commands, each attached to a location:

* `when at p and ⋀ᵢ aᵢ ∈ Dᵢ: a ← T(a); goto q`, where `T(a)ᵢ = a_{σ(i)} + δᵢ` for a
  permutation `σ` of the registers and offsets `δ ∈ A^s`;
* `when at p and ⋀ᵢ aᵢ ∈ Dᵢ: fork q and r`.

A configuration `(p, a)` accepts if `p = accept`, or if `p ∉ {accept, reject}` and some command
at `p` whose guard holds for `a` leads to acceptance: an assignment if `(q, T(a))` accepts, a
fork if both `(q, a)` and `(r, a)` accept. Acceptance is the least such predicate, i.e. the
existence of a finite derivation tree. Commands attached to `accept` or `reject` are never
executed.
-/

namespace Lax119563Proofs.Programs

/-- A guard `⋀ᵢ aᵢ ∈ Dᵢ` on `s` registers over `𝔽₂^ℓ`. -/
structure Guard (s ℓ : ℕ) where
  /-- The sets `Dᵢ`. -/
  sets : Fin s → Finset (Fin ℓ → ZMod 2)

/-- The guard holds for the register valuation `a`. -/
def Guard.Holds {s ℓ : ℕ} (g : Guard s ℓ) (a : Fin s → Fin ℓ → ZMod 2) : Prop :=
  ∀ i, a i ∈ g.sets i

/-- A register update `T(a)ᵢ = a_{σ(i)} + δᵢ`. -/
structure Update (s ℓ : ℕ) where
  /-- The permutation `σ` of the registers. -/
  σ : Equiv.Perm (Fin s)
  /-- The offsets `δ`. -/
  δ : Fin s → Fin ℓ → ZMod 2

/-- Apply the update `T` to the valuation `a`. -/
def Update.apply {s ℓ : ℕ} (T : Update s ℓ) (a : Fin s → Fin ℓ → ZMod 2) :
    Fin s → Fin ℓ → ZMod 2 :=
  fun i => a (T.σ i) + T.δ i

/-- A guarded command of a register program with `n` control locations. -/
inductive Command (s ℓ n : ℕ)
  /-- `when at loc and guard: a ← update(a); goto next`. -/
  | assign (loc : Fin n) (guard : Guard s ℓ) (update : Update s ℓ) (next : Fin n)
  /-- `when at loc and guard: fork left and right`. -/
  | fork (loc : Fin n) (guard : Guard s ℓ) (left right : Fin n)

/-- A register program with `s` registers over `𝔽₂^ℓ`. -/
structure RegisterProgram (s ℓ : ℕ) where
  /-- The number of control locations; the locations are `0, …, numLocations - 1`. -/
  numLocations : ℕ
  /-- The accepting location. -/
  accept : Fin numLocations
  /-- The rejecting location. -/
  reject : Fin numLocations
  accept_ne_reject : accept ≠ reject
  /-- The guarded commands. -/
  commands : List (Command s ℓ numLocations)

namespace RegisterProgram

variable {s ℓ : ℕ}

/-- The configuration `(p, a)` accepts: the least predicate that holds at `accept` and is
closed under executing a command at a location other than `accept` and `reject`. -/
inductive Accepts (R : RegisterProgram s ℓ) :
    Fin R.numLocations → (Fin s → Fin ℓ → ZMod 2) → Prop
  | accept (a : Fin s → Fin ℓ → ZMod 2) : Accepts R R.accept a
  | assign {p q : Fin R.numLocations} {g : Guard s ℓ} {T : Update s ℓ}
      {a : Fin s → Fin ℓ → ZMod 2} :
      Command.assign p g T q ∈ R.commands → p ≠ R.accept → p ≠ R.reject → g.Holds a →
      Accepts R q (T.apply a) → Accepts R p a
  | fork {p q r : Fin R.numLocations} {g : Guard s ℓ} {a : Fin s → Fin ℓ → ZMod 2} :
      Command.fork p g q r ∈ R.commands → p ≠ R.accept → p ≠ R.reject → g.Holds a →
      Accepts R q a → Accepts R r a → Accepts R p a

/-- The rejecting location accepts no valuation. -/
theorem not_accepts_reject (R : RegisterProgram s ℓ) (a : Fin s → Fin ℓ → ZMod 2) :
    ¬ R.Accepts R.reject a := by
  intro h
  generalize hp : R.reject = p at h
  induction h with
  | accept => exact R.accept_ne_reject hp.symm
  | assign _ _ hrej => exact hrej hp.symm
  | fork _ _ hrej => exact hrej hp.symm

end RegisterProgram

end Lax119563Proofs.Programs
