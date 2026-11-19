import Lax119563Proofs.Compiler.P4SchL1d
import Lax119563Proofs.Compiler.P4SchGlue2

/-!
# Pass `P4`, schema part: the column loop of section 2, invariant and step
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The column loop of section 2. -/
def p4S2 : CStm CR CQ := .loop (.lt (rv r4K) (rv r4D)) p4C2

/-- The update hub base of schema `e`. -/
noncomputable def updBase (e : Fin I.schemas.length) : ℕ :=
  schBase I e + (cL I e).length * colW I e

/-- The update edges of column `c`. -/
noncomputable def colE2 (ε : ZMod 2) (e : Fin I.schemas.length) (c : Coord k ℓ) :
    List (ℕ × ℕ) :=
  (stepsC c).zipIdx.flatMap fun q => hubE I ε (.upd e q.1 c) bits2
    (updBase I e + 4 * (entBefore I e c + q.2))

/-- The state of the column loop of section 2 after `r` columns. -/
def L2Inv (w : ℕ) (x : List Bool) (ε : ZMod 2) (e : Fin I.schemas.length) (R Q : List ℕ)
    (s0 : NSt CR CQ) (r : ℕ) (s : NSt CR CQ) : Prop :=
  EE s0 s (((cL I e).take r).flatMap (colE2 I ε e)) ∧
  s.stk qRkF = ((cL I e).drop r).flatMap (fun c => codesL I e c ++ [0]) ++ Q ∧
  s.stk qOrsB = [] ∧
  s.stk qAns = ((cL I e).zipIdx.drop r).flatMap (a2C I e) ++ R ∧
  s.stk qA2 = (((cL I e).zipIdx.take r).flatMap (a2C I e)).reverse ++ s0.stk qA2 ∧
  (∀ q, q ≠ q4E → q ≠ qRkF → q ≠ qOrsB → q ≠ qAns → q ≠ qA2 → s.stk q = s0.stk q) ∧
  s.env r4K = r ∧ s.env r4H = updBase I e + 4 * entB I e r ∧
  s.env r4TP = trackBase I e + 2 * entB I e r ∧ s.env r4SP = sumBase I e + 2 * r ∧
  s.env r4V < 2 ^ w ∧ s.Bdd w ∧ s.pos ≤ x.length ∧
  ∀ reg, reg ∉ c2W → s.env reg = s0.env reg

end Lax119563Proofs.Compiler
