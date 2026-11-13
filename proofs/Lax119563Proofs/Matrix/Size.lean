import Lax119563Proofs.Matrix.SpoilerMain

/-!
# Size of the matrix graphs

Each graph has at most `16 S` vertices (Lemma "Matrix size"), and at most three times as
many edges as vertices: every edge contains exactly one hub, and hubs have degree at most
three.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

/-! ### Counting vertices -/

lemma length_flatMap_eq {α β : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup)
    (f : α → List β) : (l.flatMap f).length = ∑ x ∈ l.toFinset, (f x).length := by
  rw [List.length_flatMap, List.sum_toFinset _ hl]

lemma toFinset_coordList (D : Finset (Coord k ℓ)) : (coordList D).toFinset = D := by
  ext c; simp

lemma length_coordVerts (v : Fin I.numLocations) :
    (coordVerts I v).length ≤ 2 * (I.domain v).card := by
  rw [coordVerts, length_flatMap_eq (nodup_coordList _), toFinset_coordList, mul_comm,
    ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun c _ => ?_
  split <;> simp [bits1]

lemma length_columnVerts (e : Fin I.schemas.length) (c : Coord k ℓ) :
    (columnVerts I e c).length ≤ 8 := by
  unfold columnVerts
  split <;> simp [bits1, bits2]

lemma length_stepVerts (e : Fin I.schemas.length) (σ : ℕ) :
    (stepVerts I e σ).length =
      2 * hit e σ + 6 * ((dom I e).filter fun c => ent σ c ≠ 0).card := by
  classical
  unfold stepVerts
  rw [List.length_append, length_flatMap_eq ((nodup_coordList _).filter _)]
  have : ((coordList (dom I e)).filter fun c => decide (ent σ c ≠ 0)).toFinset =
      (dom I e).filter fun c => ent σ c ≠ 0 := by
    ext c; simp
  rw [this]
  simp only [List.length_append, List.length_map, bits1, bits2, List.length_cons,
    List.length_nil, Finset.sum_const, smul_eq_mul]
  congr 1
  · unfold hit; split <;> simp
  · ring

lemma sum_ent_card (hk : 2 ≤ k) (e : Fin I.schemas.length) :
    ∑ σ ∈ Finset.range (numSteps k ℓ), ((dom I e).filter fun c => ent σ c ≠ 0).card =
      (k + 1) * nnz (sch I e) := by
  classical
  have hM : 0 < k - 1 + ℓ := by omega
  let f : ℕ → ℕ := fun j => if h : j < k - 1 + ℓ then
    ((dom I e).filter fun c => checkMatrix k ℓ (finSumFinEquiv.symm ⟨j, h⟩) c ≠ 0).card else 0
  have h1 : ∀ σ, ((dom I e).filter fun c => ent σ c ≠ 0).card = f (σ % (k - 1 + ℓ)) := by
    intro σ
    simp only [f, dif_pos (Nat.mod_lt σ hM), ent_eq hk, stepRow]
  simp_rw [h1]
  rw [numSteps, sum_range_mul_mod f _ hM (k + 1)]
  congr 1
  rw [Finset.sum_range]
  simp only [f, Fin.is_lt, dif_pos]
  rw [Equiv.sum_comp finSumFinEquiv.symm
    (fun j => ((dom I e).filter fun c => checkMatrix k ℓ j c ≠ 0).card)]
  rw [nnz, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.card_filter]
  rfl

lemma card_dom_le_nnz (hk : 2 ≤ k) (e : Fin I.schemas.length) :
    (dom I e).card ≤ nnz (sch I e) := by
  classical
  let row : Coord k ℓ → Fin (k - 1) ⊕ Fin ℓ := fun c =>
    if h : (c.1 : ℕ) < k - 1 then .inl ⟨c.1, h⟩ else .inl ⟨0, by omega⟩
  refine Finset.card_le_card_of_injOn (fun c => (row c, c)) (fun c hc => ?_)
    (fun c _ c' _ h => congrArg Prod.snd h)
  simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, Finset.mem_univ,
    true_and]
  refine ⟨hc, ?_⟩
  simp only [row]
  split
  · next h => simp [checkMatrix_inl]
  · next h =>
    have : (c.1 : ℕ) = k - 1 := by have := c.1.2; omega
    simp [checkMatrix_inl, this]

lemma numRows_le_nnz (e : Fin I.schemas.length) : numRows (sch I e) ≤ nnz (sch I e) := by
  classical
  unfold numRows nnz
  refine Finset.card_le_card_of_surjOn Prod.fst fun j hj => ?_
  simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hj
  obtain ⟨c, hc, hjc⟩ := hj
  exact ⟨(j, c), by simp [hc, hjc], rfl⟩

lemma length_schemaVerts (hk : 2 ≤ k) (e : Fin I.schemas.length) :
    (schemaVerts I e).length ≤ 16 * (k + 1) * nnz (sch I e) := by
  classical
  unfold schemaVerts
  rw [List.length_append, length_flatMap_eq (nodup_coordList _), toFinset_coordList,
    length_flatMap_eq List.nodup_range, List.toFinset_range]
  simp_rw [length_stepVerts]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_ent_card hk,
    show ∑ σ ∈ Finset.range (numSteps k ℓ), hit e σ = (k + 1) * numRows (sch I e) from
      sum_hit hk e]
  have h1 : ∑ c ∈ dom I e, (columnVerts I e c).length ≤ 8 * (dom I e).card := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun c _ => length_columnVerts e c
  have h2 := card_dom_le_nnz hk e
  have h3 := numRows_le_nnz e
  nlinarith

lemma sum_get_eq {α : Type*} (l : List α) (f : α → ℕ) :
    ∑ e : Fin l.length, f (l.get e) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Fin.sum_univ_succ]

/-- **Matrix size.** -/
theorem card_vertexList_le (hk : 2 ≤ k) : (vertexList I).length ≤ 16 * sizeParameter I := by
  classical
  unfold vertexList
  rw [List.length_append, length_flatMap_eq (List.nodup_finRange _),
    length_flatMap_eq (List.nodup_finRange _), List.toFinset_finRange, List.toFinset_finRange]
  have h1 : ∑ v, (coordVerts I v).length ≤ 2 * ∑ v, (I.domain v).card := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun v _ => length_coordVerts v
  have h2 : ∑ e, (schemaVerts I e).length ≤ 16 * (k + 1) * (I.schemas.map nnz).sum := by
    rw [← sum_get_eq, Finset.mul_sum]
    exact Finset.sum_le_sum fun e _ => length_schemaVerts hk e
  unfold sizeParameter
  calc _ ≤ 2 * ∑ v, (I.domain v).card + 16 * (k + 1) * (I.schemas.map nnz).sum :=
        Nat.add_le_add h1 h2
    _ ≤ _ := by ring_nf; omega

end Lax119563Proofs.Matrix
