import Lax119563.ImplicitParitySystems
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Lax119563Proofs.Programs.RegisterProgram

/-!
# Encoding register valuations as addresses

A valuation `a ∈ A^s` of `s` registers over `A = 𝔽₂^ℓ` is encoded as the checksum address
`E(a) = (a_1, …, a_s, ∑ᵢ aᵢ)` with `k = s + 1` blocks. A register update
`T(a)ᵢ = a_{σ(i)} + δᵢ` becomes a block-induced permutation `π_T` with `π_T E(a) = E(T(a))`,
and a guard `⋀ᵢ aᵢ ∈ Dᵢ` becomes the coordinate domain `⋃ᵢ {i} × Dᵢ ∪ {k} × A`, whose
allowed addresses are exactly the encodings of the valuations satisfying the guard.
-/

open Lax119563.ImplicitParitySystems

namespace Lax119563Proofs.Programs

variable {s ℓ : ℕ}

/-- The checksum address `E(a) = (a_1, …, a_s, ∑ᵢ aᵢ)`. -/
def encode (a : Fin s → BlockCoord ℓ) : Fin (s + 1) → BlockCoord ℓ :=
  Fin.lastCases (∑ i, a i) a

/-- The register valuation read off the first `s` blocks of an array. -/
def decode (x : Fin (s + 1) → BlockCoord ℓ) : Fin s → BlockCoord ℓ :=
  fun i => x i.castSucc

@[simp] theorem encode_last (a : Fin s → BlockCoord ℓ) : encode a (Fin.last s) = ∑ i, a i := by
  simp [encode]

@[simp] theorem encode_castSucc (a : Fin s → BlockCoord ℓ) (i : Fin s) :
    encode a i.castSucc = a i := by
  simp [encode]

@[simp] theorem decode_encode (a : Fin s → BlockCoord ℓ) : decode (encode a) = a := by
  funext i
  simp [decode]

theorem add_self_blockCoord (b : BlockCoord ℓ) : b + b = 0 := by
  funext t
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize b t = z
  fin_cases z <;> decide

theorem isAddress_encode (a : Fin s → BlockCoord ℓ) : IsAddress (encode a) := by
  rw [IsAddress, Fin.sum_univ_castSucc]
  simp [add_self_blockCoord]

/-- A permutation of `Fin s`, extended to `Fin (s + 1)` by fixing the last element. -/
def liftPerm (σ : Equiv.Perm (Fin s)) : Equiv.Perm (Fin (s + 1)) where
  toFun := Fin.lastCases (Fin.last s) fun i => (σ i).castSucc
  invFun := Fin.lastCases (Fin.last s) fun i => (σ.symm i).castSucc
  left_inv j := by
    induction j using Fin.lastCases <;> simp
  right_inv j := by
    induction j using Fin.lastCases <;> simp

@[simp] theorem liftPerm_last (σ : Equiv.Perm (Fin s)) : liftPerm σ (Fin.last s) = Fin.last s := by
  simp [liftPerm]

@[simp] theorem liftPerm_castSucc (σ : Equiv.Perm (Fin s)) (i : Fin s) :
    liftPerm σ i.castSucc = (σ i).castSucc := by
  simp [liftPerm]

/-- The identity block-induced permutation. -/
def idPerm (s ℓ : ℕ) : BlockPerm (s + 1) ℓ where
  perm := 1
  shift := 0
  sum_shift := by simp

@[simp] theorem idPerm_act (x : Fin (s + 1) → BlockCoord ℓ) : (idPerm s ℓ).act x = x := by
  funext j
  simp [BlockPerm.act, idPerm]; rfl

/-- The block-induced permutation `π_T` of the update `T`: block `σ(i)` moves to block `i` with
shift `δᵢ`, and the checksum block is shifted by `∑ᵢ δᵢ`. -/
def updatePerm (T : Update s ℓ) : BlockPerm (s + 1) ℓ where
  perm := (liftPerm T.σ).symm
  shift := Fin.lastCases (∑ i, T.δ i) fun m => T.δ (T.σ.symm m)
  sum_shift := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
    rw [Equiv.sum_comp T.σ.symm T.δ, add_self_blockCoord]

theorem updatePerm_act_castSucc (T : Update s ℓ) (x : Fin (s + 1) → BlockCoord ℓ) (i : Fin s) :
    (updatePerm T).act x i.castSucc = x (T.σ i).castSucc + T.δ i := by
  simp [BlockPerm.act, updatePerm]

theorem decode_updatePerm_act (T : Update s ℓ) (x : Fin (s + 1) → BlockCoord ℓ) :
    decode ((updatePerm T).act x) = T.apply (decode x) := by
  funext i
  simp [decode, Update.apply, updatePerm_act_castSucc]

theorem updatePerm_act_encode (T : Update s ℓ) (a : Fin s → BlockCoord ℓ) :
    (updatePerm T).act (encode a) = encode (T.apply a) := by
  funext j
  induction j using Fin.lastCases with
  | last =>
    simp only [BlockPerm.act, updatePerm, Equiv.symm_symm, liftPerm_last, encode_last,
      Fin.lastCases_last, Update.apply, Finset.sum_add_distrib]
    rw [Equiv.sum_comp T.σ (fun i => a i)]
  | cast i =>
    rw [updatePerm_act_castSucc, encode_castSucc, encode_castSucc]
    rfl

/-- The coordinate domain `⋃ᵢ {i} × Dᵢ ∪ {k} × A` of a guard; if `active` is false, the
checksum block is removed as well, so that no address is allowed. -/
def guardDomain (g : Guard s ℓ) (active : Bool) : Finset (Coord (s + 1) ℓ) :=
  Finset.univ.filter fun c =>
    Fin.lastCases (motive := fun _ => Bool) active (fun i => decide (c.2 ∈ g.sets i)) c.1 = true

theorem supp_subset_guardDomain_iff (g : Guard s ℓ) (active : Bool)
    (x : Fin (s + 1) → BlockCoord ℓ) :
    supp x ⊆ guardDomain g active ↔ g.Holds (decode x) ∧ active = true := by
  simp only [supp, guardDomain, Finset.image_subset_iff, Finset.mem_univ, Finset.mem_filter,
    true_and, forall_const]
  rw [Fin.forall_fin_succ']
  simp [Guard.Holds, decode]

end Lax119563Proofs.Programs
