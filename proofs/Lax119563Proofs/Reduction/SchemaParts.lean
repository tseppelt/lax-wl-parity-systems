import Lax119563Proofs.Circuits.AddrProgram
import Lax119563Proofs.Programs.Compile

/-!
# Parts of schemas and register values

The accessors of equation schemas (kind, argument locations and permutations, where the
"end" of a schema is its last argument) and basic facts on `regVal` (bounded, injective, with
an inverse `toBlk` on `[0, 2^ℓ)`), as used by the schema enumerator and the system generator.
-/

open Lax119563.ImplicitParitySystems

namespace Lax119563Proofs.Reduction

variable {k ℓ w : ℕ}

/-! ## Schema accessors -/

/-- Whether a schema is ternary. -/
def isTern : Schema k ℓ w → Bool
  | .binary .. => false
  | .ternary .. => true

/-- The first argument location. -/
def locU : Schema k ℓ w → Fin w
  | .binary u .. => u
  | .ternary u .. => u

/-- The first argument permutation. -/
def permU : Schema k ℓ w → BlockPerm k ℓ
  | .binary _ _ _ σ _ => σ
  | .ternary _ _ _ _ σ _ _ => σ

/-- The second argument location. -/
def locV : Schema k ℓ w → Fin w
  | .binary _ v .. => v
  | .ternary _ v .. => v

/-- The second argument permutation. -/
def permV : Schema k ℓ w → BlockPerm k ℓ
  | .binary _ _ _ _ τ => τ
  | .ternary _ _ _ _ _ τ _ => τ

/-- The last argument location. -/
def locEnd : Schema k ℓ w → Fin w
  | .binary _ v .. => v
  | .ternary _ _ w' .. => w'

/-- The last argument permutation. -/
def permEnd : Schema k ℓ w → BlockPerm k ℓ
  | .binary _ _ _ _ τ => τ
  | .ternary _ _ _ _ _ _ π => π

/-! ## Register values -/

lemma regVal_lt (b : BlockCoord ℓ) : Circuits.regVal b < 2 ^ ℓ := by
  unfold Circuits.regVal
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [Circuits.testBit_ofBits]
  simp; omega

lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma regVal_injective : Function.Injective (Circuits.regVal (ℓ := ℓ)) := by
  intro b b' h
  funext t
  have := congrArg (fun n => n.testBit t) h
  simp only [Circuits.regVal, Circuits.testBit_ofBits, t.isLt, decide_true, Bool.true_and,
    dif_pos] at this
  have h1 := zmod2_cases (b t)
  have h2 := zmod2_cases (b' t)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp_all

/-- The block coordinate with register value `v`. -/
def toBlk (ℓ v : ℕ) : BlockCoord ℓ := (Circuits.ofAddr v : Fin 1 → Fin ℓ → ZMod 2) 0

/-! ## Location numbers of compiled programs -/

section Locs

open Lax119563Proofs.Programs

variable {s : ℕ} (R : RegisterProgram s ℓ)

lemma loc_det_val (t : DetSlot) :
    (R.loc (.det t)).val = R.numLocations + R.commands.length * 8 + t.toFin.val := by
  simp [RegisterProgram.loc, Role.equivFin, Role.toSum, finSumFinEquiv]

end Locs

end Lax119563Proofs.Reduction
