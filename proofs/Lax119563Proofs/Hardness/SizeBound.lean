import Lax119563.MatrixCompiler

/-!
# The size parameter of an implicit parity system

Every coordinate domain has at most `k 2^ℓ` coordinates, and `nnz(B_e) ≤ (2 + ℓ) k 2^ℓ`: the
`k - 1` block-parity rows have at most `|𝔠_e| + 2^ℓ (k - 1) ≤ 2 k 2^ℓ` nonzero entries on
`𝔠_e` (a coordinate of block `i < k - 1` meets only row `i`, those of the last block meet all
of them), and the `ℓ` checksum rows at most `ℓ k 2^ℓ`. Hence
`S ≤ |W| k 2^ℓ + (k + 1) |𝓔| (2 + ℓ) k 2^ℓ` (`sizeParameter_le`).
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler

namespace Lax119563Proofs.Hardness

variable {k ℓ w : ℕ}

lemma card_coord : Fintype.card (Coord k ℓ) = k * 2 ^ ℓ := by
  simp [Coord, BlockCoord, Fintype.card_prod, ZMod.card]

lemma card_domain_le (D : Finset (Coord k ℓ)) : D.card ≤ k * 2 ^ ℓ :=
  card_coord (k := k) (ℓ := ℓ) ▸ D.card_le_univ

/-- The injection used to count the nonzero entries of `B_e`. -/
def nnzMap (k ℓ : ℕ) : (Fin (k - 1) ⊕ Fin ℓ) × Coord k ℓ → (Fin 2 ⊕ Fin ℓ) × Coord k ℓ
  | (.inl i, c) => if (c.1 : ℕ) = i then (.inl 0, c) else (.inl 1, (⟨i, by omega⟩, c.2))
  | (.inr t, c) => (.inr t, c)

open Classical in
lemma nnz_le (e : Schema k ℓ w) : nnz e ≤ (2 + ℓ) * (k * 2 ^ ℓ) := by
  unfold nnz
  have hcard : Fintype.card ((Fin 2 ⊕ Fin ℓ) × Coord k ℓ) = (2 + ℓ) * (k * 2 ^ ℓ) := by
    rw [Fintype.card_prod, Fintype.card_sum, card_coord]; simp
  rw [← hcard, ← Finset.card_univ]
  refine Finset.card_le_card_of_injOn (nnzMap k ℓ) (fun _ _ => Finset.mem_coe.mpr
    (Finset.mem_univ _)) ?_
  rintro ⟨r, c⟩ hx ⟨r', c'⟩ hx' heq
  simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_univ, true_and,
    Set.mem_ofPred_eq] at hx hx'
  rcases r with i | t <;> rcases r' with i' | t'
  · simp only [checkMatrix, Matrix.of_apply, ne_eq, ite_eq_right_iff, one_ne_zero,
      imp_false, not_not] at hx hx'
    simp only [nnzMap] at heq
    split_ifs at heq with h1 h2 h2
    · simp only [Prod.mk.injEq, true_and] at heq
      subst heq
      have : i = i' := Fin.ext (by omega)
      subst this; rfl
    · simp at heq
    · simp at heq
    · simp only [Prod.mk.injEq, Fin.mk.injEq, true_and] at heq
      obtain ⟨hii, hc2⟩ := heq
      have hi : i = i' := Fin.ext hii
      subst hi
      have hc1 : c.1 = c'.1 := Fin.ext (by omega)
      have : c = c' := Prod.ext hc1 hc2
      subst this; rfl
  · simp only [nnzMap] at heq; split_ifs at heq <;> simp at heq
  · simp only [nnzMap] at heq; split_ifs at heq <;> simp at heq
  · simp only [nnzMap, Prod.mk.injEq, Sum.inr.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq; rfl

/-- **The size parameter.** -/
theorem sizeParameter_le (I : ImplicitParitySystem k ℓ) :
    matrixSize I ≤ I.numLocations * (k * 2 ^ ℓ) +
      (k + 1) * (I.schemas.length * ((2 + ℓ) * (k * 2 ^ ℓ))) := by
  unfold matrixSize
  have h1 : ∑ v, (I.domain v).card ≤ I.numLocations * (k * 2 ^ ℓ) := by
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin I.numLocations))
      (fun v => (I.domain v).card) (k * 2 ^ ℓ) (fun v _ => card_domain_le _)
    simpa using this
  have h2 : (I.schemas.map nnz).sum ≤ I.schemas.length * ((2 + ℓ) * (k * 2 ^ ℓ)) := by
    have := List.sum_le_card_nsmul (I.schemas.map nnz) ((2 + ℓ) * (k * 2 ^ ℓ))
      (fun x hx => by
        obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
        exact nnz_le e)
    simpa using this
  have := Nat.mul_le_mul_left (k + 1) h2
  omega

end Lax119563Proofs.Hardness
