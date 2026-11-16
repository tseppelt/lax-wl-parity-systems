import Lax119563Proofs.Reduction.OutEdgeList

/-!
# Explicit formulas for the matrix construction

The entry `ent σ c` of the check row processed by step `σ`, for `k = s + 1` blocks: row
`j = σ % (s + ℓ)` is the block-parity check of block `j` (entries `1` on blocks `j` and `s`)
if `j < s`, and the checksum check of bit `j - s` otherwise.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563Proofs.Matrix

namespace Lax119563Proofs.Reduction

variable {s ℓ : ℕ}

lemma ent_eq (h : 0 < s + ℓ) (σ : ℕ) (c : Coord (s + 1) ℓ) :
    ent σ c = if hj : σ % (s + ℓ) < s then (if c.1.val = σ % (s + ℓ) ∨ c.1.val = s then 1 else 0)
      else c.2 ⟨σ % (s + ℓ) - s, by have := Nat.mod_lt σ h; omega⟩ := by
  have hM : 0 < s + 1 - 1 + ℓ := by omega
  unfold ent
  rw [dif_pos hM]
  have hm : σ % (s + 1 - 1 + ℓ) = σ % (s + ℓ) := by congr 1
  by_cases hj : σ % (s + ℓ) < s
  · rw [dif_pos hj]
    have hrow : stepRow hM σ = .inl ⟨σ % (s + ℓ), by omega⟩ := by
      unfold stepRow
      have e : (⟨σ % (s + 1 - 1 + ℓ), Nat.mod_lt _ hM⟩ : Fin (s + 1 - 1 + ℓ)) =
          Fin.castAdd ℓ (⟨σ % (s + ℓ), by omega⟩ : Fin (s + 1 - 1)) := Fin.ext (by simp [hm])
      rw [e, finSumFinEquiv_symm_apply_castAdd]
    rw [hrow]
    simp [checkMatrix]
  · rw [dif_neg hj]
    have hrow : stepRow hM σ = .inr ⟨σ % (s + ℓ) - s, by have := Nat.mod_lt σ h; omega⟩ := by
      unfold stepRow
      have e : (⟨σ % (s + 1 - 1 + ℓ), Nat.mod_lt _ hM⟩ : Fin (s + 1 - 1 + ℓ)) =
          Fin.natAdd (s + 1 - 1) (⟨σ % (s + ℓ) - s, by have := Nat.mod_lt σ h; omega⟩ : Fin ℓ) :=
        Fin.ext (by simp [hm]; omega)
      rw [e, finSumFinEquiv_symm_apply_natAdd]
    rw [hrow]
    simp [checkMatrix]

end Lax119563Proofs.Reduction
