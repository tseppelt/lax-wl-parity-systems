import Lax119563.MatrixCompiler
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lax119563Proofs.Programs.Compile

/-!
# Size of the compiled implicit parity system

The compiled system `R.compile p₀ a₀` of a register program with `w` control locations and `r`
commands has exactly `w + 8r + 4` locations, all with the full coordinate domain, and at most
`9r + 4` schemas. Since every schema has `nnz(B_e) ≤ nnz(B) = 2(k-1)·2^ℓ + kℓ·2^ℓ`, the size
parameter of the matrix compiler is `O((s+1)·2^ℓ·w + (s+1)²·2^ℓ·ℓ·(r+1))`.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler

namespace Lax119563Proofs.Programs

variable {s ℓ : ℕ}

theorem card_blockCoord : Fintype.card (BlockCoord ℓ) = 2 ^ ℓ := by
  simp [BlockCoord]

theorem card_coord (k : ℕ) : Fintype.card (Coord k ℓ) = k * 2 ^ ℓ := by
  simp [Coord]

/-- The coordinates in a fixed block. -/
theorem card_filter_block_le (k n : ℕ) :
    (Finset.univ.filter fun c : Coord k ℓ => (c.1 : ℕ) = n).card ≤ 2 ^ ℓ := by
  have hsub : (Finset.univ.filter fun c : Coord k ℓ => (c.1 : ℕ) = n) ⊆
      (Finset.univ.filter fun b : Fin k => (b : ℕ) = n) ×ˢ Finset.univ := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    simp [hc]
  have hone : (Finset.univ.filter fun b : Fin k => (b : ℕ) = n).card ≤ 1 :=
    Finset.card_le_one.2 fun a ha b hb => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact Fin.ext (ha.trans hb.symm)
  calc _ ≤ _ := Finset.card_le_card hsub
    _ = _ := by rw [Finset.card_product, Finset.card_univ, card_blockCoord]
    _ ≤ 1 * 2 ^ ℓ := Nat.mul_le_mul_right _ hone
    _ = 2 ^ ℓ := one_mul _

/-- `nnz(B_e) ≤ nnz(B) ≤ 2(k-1)·2^ℓ + ℓk·2^ℓ`. -/
theorem nnz_le {k N : ℕ} (e : Schema k ℓ N) :
    nnz e ≤ (k - 1) * (2 * 2 ^ ℓ) + ℓ * (k * 2 ^ ℓ) := by
  classical
  have hrow : ∀ row, (Finset.univ.filter fun c : Coord k ℓ =>
      checkMatrix k ℓ row c ≠ 0).card ≤
        Sum.elim (fun _ => 2 * 2 ^ ℓ) (fun _ => k * 2 ^ ℓ) row := by
    rintro (i | t)
    · have hsub : (Finset.univ.filter fun c : Coord k ℓ => checkMatrix k ℓ (.inl i) c ≠ 0) ⊆
          (Finset.univ.filter fun c : Coord k ℓ => (c.1 : ℕ) = i) ∪
            (Finset.univ.filter fun c : Coord k ℓ => (c.1 : ℕ) = k - 1) := by
        intro c hc
        simp only [checkMatrix, Matrix.of_apply, Finset.mem_filter, Finset.mem_univ,
          true_and, ne_eq, ite_eq_right_iff, Classical.not_imp] at hc
        simpa using hc.1
      calc _ ≤ _ := Finset.card_le_card hsub
        _ ≤ _ := Finset.card_union_le _ _
        _ ≤ 2 ^ ℓ + 2 ^ ℓ := Nat.add_le_add (card_filter_block_le _ _) (card_filter_block_le _ _)
        _ = _ := by simp; ring
    · calc _ ≤ (Finset.univ : Finset (Coord k ℓ)).card := Finset.card_filter_le _ _
        _ = _ := by simp
  calc nnz e ≤ (Finset.univ.filter fun x : (Fin (k - 1) ⊕ Fin ℓ) × Coord k ℓ =>
        checkMatrix k ℓ x.1 x.2 ≠ 0).card := by
        unfold nnz
        exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
    _ = ∑ row, (Finset.univ.filter fun c : Coord k ℓ => checkMatrix k ℓ row c ≠ 0).card := by
        rw [Finset.card_filter, Fintype.sum_prod_type]
        simp only [Finset.card_filter]
    _ ≤ ∑ row, Sum.elim (fun _ => 2 * 2 ^ ℓ) (fun _ => k * 2 ^ ℓ) row :=
        Finset.sum_le_sum fun row _ => hrow row
    _ = _ := by simp [Fintype.sum_sum_type]

theorem nnz_le_of_one_le {N : ℕ} (hℓ : 1 ≤ ℓ) (e : Schema (s + 1) ℓ N) :
    nnz e ≤ 3 * (s + 1) * ℓ * 2 ^ ℓ := by
  refine (nnz_le e).trans ?_
  rw [Nat.add_sub_cancel]
  generalize 2 ^ ℓ = Q
  have h : s * (2 * Q) * 1 ≤ (s + 1) * (2 * Q) * ℓ :=
    Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.le_succ s)) hℓ
  calc s * (2 * Q) + ℓ * ((s + 1) * Q) ≤ (s + 1) * (2 * Q) * ℓ + ℓ * ((s + 1) * Q) := by
        rw [mul_one] at h; omega
    _ = _ := by ring

/-- The arithmetic of the size bound: `(w + 8r + 4)·kQ + (k+1)·n ≤ 100·(kQw + k²Qℓ(r+1))`
for `k = s + 1`, `ℓ ≥ 1` and `n ≤ (9r + 4)·3kℓQ`. -/
theorem size_arith {w r Q n : ℕ} (hℓ : 1 ≤ ℓ)
    (hnnz : n ≤ (9 * r + 4) * (3 * (s + 1) * ℓ * Q)) :
    (w + 8 * r + 4) * ((s + 1) * Q) + (s + 1 + 1) * n ≤
      100 * ((s + 1) * Q * w + (s + 1) ^ 2 * Q * ℓ * (r + 1)) := by
  have h1 : (8 * r + 4) * ((s + 1) * Q) ≤ 8 * ((s + 1) ^ 2 * Q * ℓ * (r + 1)) := by
    have : (s + 1) * Q * 1 * 1 ≤ (s + 1) * Q * (s + 1) * ℓ :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hℓ
    nlinarith
  have h2 : (s + 1 + 1) * ((9 * r + 4) * (3 * (s + 1) * ℓ * Q)) ≤
      54 * ((s + 1) ^ 2 * Q * ℓ * (r + 1)) := by
    have ha : s + 1 + 1 ≤ 2 * (s + 1) := by omega
    have hb : 9 * r + 4 ≤ 9 * (r + 1) := by omega
    calc _ ≤ (2 * (s + 1)) * ((9 * (r + 1)) * (3 * (s + 1) * ℓ * Q)) :=
          Nat.mul_le_mul ha (Nat.mul_le_mul_right _ hb)
      _ = _ := by ring
  have h3 : (s + 1 + 1) * n ≤ (s + 1 + 1) * ((9 * r + 4) * (3 * (s + 1) * ℓ * Q)) :=
    Nat.mul_le_mul_left _ hnnz
  rw [show (w + 8 * r + 4) * ((s + 1) * Q) = (s + 1) * Q * w + (8 * r + 4) * ((s + 1) * Q) by
    ring]
  generalize (s + 1) * Q * w = A at *
  generalize (s + 1) ^ 2 * Q * ℓ * (r + 1) = X at *
  generalize (8 * r + 4) * ((s + 1) * Q) = B at *
  generalize (s + 1 + 1) * n = C at *
  generalize (s + 1 + 1) * ((9 * r + 4) * (3 * (s + 1) * ℓ * Q)) = E at *
  omega

namespace RegisterProgram

variable (R : RegisterProgram s ℓ) (p₀ : Fin R.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2)

theorem compile_numLocations :
    (R.compile p₀ a₀).numLocations = R.numLocations + 8 * R.commands.length + 4 := by
  simp only [compile, compiledSize]
  ring

theorem compile_domain (v : Fin (R.compile p₀ a₀).numLocations) :
    (R.compile p₀ a₀).domain v = Finset.univ :=
  rfl

theorem commandSchemas_length (j : Fin R.commands.length) (c : Command s ℓ R.numLocations) :
    (R.commandSchemas j c).length ≤ 9 := by
  cases c <;> simp [commandSchemas, gadget]

theorem compile_schemas_length :
    (R.compile p₀ a₀).schemas.length ≤ 9 * R.commands.length + 4 := by
  simp only [compile, compiledSchemas, List.length_append, List.length_flatMap, detectorSchemas,
    gadget, List.length_cons, List.length_nil]
  have := List.sum_le_card_nsmul
    ((List.finRange R.commands.length).map fun j => (R.commandSchemas j R.commands[j]).length) 9
    (by simp only [List.mem_map]; rintro _ ⟨j, -, rfl⟩; exact R.commandSchemas_length j _)
  simp only [List.length_map, List.length_finRange, smul_eq_mul] at this

  omega

/-- **Size of the compiled system.** For `ℓ ≥ 1`, the size parameter of the matrix compiler is
`O((s+1)·2^ℓ·w + (s+1)²·2^ℓ·ℓ·(r+1))` with an absolute constant. -/
theorem sizeParameter_compile_le (hℓ : 1 ≤ ℓ) :
    sizeParameter (R.compile p₀ a₀) ≤
      100 * ((s + 1) * 2 ^ ℓ * R.numLocations +
        (s + 1) ^ 2 * 2 ^ ℓ * ℓ * (R.commands.length + 1)) := by
  have hdom : ∑ v, ((R.compile p₀ a₀).domain v).card =
      (R.numLocations + 8 * R.commands.length + 4) * ((s + 1) * 2 ^ ℓ) := by
    simp only [compile_domain, Finset.card_univ, card_coord, Finset.sum_const, smul_eq_mul]
    rw [Fintype.card_fin, compile_numLocations]
  have hnnz : ((R.compile p₀ a₀).schemas.map nnz).sum ≤
      (9 * R.commands.length + 4) * (3 * (s + 1) * ℓ * 2 ^ ℓ) := by
    have hle := List.sum_le_card_nsmul ((R.compile p₀ a₀).schemas.map nnz)
      (3 * (s + 1) * ℓ * 2 ^ ℓ) (by
        simp only [List.mem_map]
        rintro _ ⟨e, -, rfl⟩
        exact nnz_le_of_one_le hℓ e)
    rw [List.length_map, smul_eq_mul] at hle
    exact hle.trans (Nat.mul_le_mul_right _ (R.compile_schemas_length p₀ a₀))
  unfold sizeParameter
  rw [hdom]
  exact size_arith hℓ hnnz

end RegisterProgram

end Lax119563Proofs.Programs
