import Lax119563Proofs.Witness.RelaySystem
import Lax119563.RowSpaceCompiler

/-!
# Size of the relay counter (Lemma relay-size, size part)

The size parameter `∑_v |𝔠_v| + (k+1) ∑_e (|𝔠_e| + 2^{rank B_e})` of the relay counter is
`O_k(2^ℓ)`. In the domain `𝔠'_j`, the first `r_j = j / (k-1)` bits of every block coordinate
are zero, so `|𝔠'_j| ≤ k 2^{ℓ - r_j}` and the first `r_j` checksum rows of the check matrix
vanish on `𝔠'_j`, giving `rank B_e ≤ k - 1 + ℓ - r_j`. Each value of `r_j` occurs for `k - 1`
positions `j`, and the sum of `2^{ℓ - r}` is geometric.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.RowSpaceCompiler

namespace Lax119563Proofs.Witness

open Finset

variable {k ℓ : ℕ}

/-- All coordinates in `D` have their first `r` bits zero. -/
def ZeroOn (D : Finset (Coord k ℓ)) (r : ℕ) : Prop :=
  ∀ c ∈ D, ∀ t : Fin ℓ, (t : ℕ) < r → c.2 t = 0

theorem card_tail_le (r : ℕ) : Fintype.card {t : Fin ℓ // r ≤ (t : ℕ)} ≤ ℓ - r := by
  refine (Fintype.card_le_of_injective (fun t => (⟨t.1 - r, by omega⟩ : Fin (ℓ - r))) ?_).trans
    (by simp)
  intro t t' h
  simp only [Fin.mk.injEq] at h
  have := t.2; have := t'.2
  exact Subtype.ext (Fin.ext (by omega))

theorem card_le_of_zeroOn {D : Finset (Coord k ℓ)} {r : ℕ} (hD : ZeroOn D r) :
    D.card ≤ k * 2 ^ (ℓ - r) := by
  classical
  have hsub : D ⊆ univ ×ˢ (univ.filter fun b : BlockCoord ℓ => ∀ t : Fin ℓ, (t : ℕ) < r → b t = 0) := by
    intro c hc
    simp only [mem_product, mem_univ, mem_filter, true_and]
    exact hD c hc
  refine (card_le_card hsub).trans ?_
  rw [card_product, card_univ, Fintype.card_fin]
  refine Nat.mul_le_mul_left _ ?_
  let f : BlockCoord ℓ → ({t : Fin ℓ // r ≤ (t : ℕ)} → ZMod 2) := fun b t => b t.1
  have hinj : Set.InjOn f (univ.filter fun b : BlockCoord ℓ => ∀ t : Fin ℓ, (t : ℕ) < r → b t = 0) := by
    intro b hb b' hb' h
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hb hb'
    funext t
    by_cases ht : (t : ℕ) < r
    · rw [hb t ht, hb' t ht]
    · exact congrFun h ⟨t, by omega⟩
  refine (card_le_card_of_injOn f (fun _ _ => mem_univ _) hinj).trans ?_
  rw [card_univ, Fintype.card_fun, ZMod.card]
  exact Nat.pow_le_pow_right (by norm_num) (card_tail_le r)

/-- The rows of the check matrix that may be nonzero on a domain with `r` leading zero bits. -/
abbrev RowsR (k ℓ r : ℕ) := Fin (k - 1) ⊕ {t : Fin ℓ // r ≤ (t : ℕ)}

/-- The embedding of these rows into all rows. -/
def embR {r : ℕ} : RowsR k ℓ r → Fin (k - 1) ⊕ Fin ℓ := Sum.map id Subtype.val

theorem embR_inj {r : ℕ} {ρ ρ' : RowsR k ℓ r} : embR ρ = embR ρ' ↔ ρ = ρ' := by
  constructor
  · intro h
    rcases ρ with i | t <;> rcases ρ' with i' | t' <;> simp_all [embR, Subtype.ext_iff]
  · rintro rfl; rfl

theorem rank_le_of_zeroOn {D : Finset (Coord k ℓ)} {r : ℕ} (hD : ZeroOn D r) :
    (Matrix.of fun row (c : D) => checkMatrix k ℓ row c).rank ≤ (k - 1) + (ℓ - r) := by
  classical
  let M' : Matrix (RowsR k ℓ r) D (ZMod 2) := Matrix.of fun ρ c => checkMatrix k ℓ (embR ρ) c
  let P : Matrix (Fin (k - 1) ⊕ Fin ℓ) (RowsR k ℓ r) (ZMod 2) :=
    Matrix.of fun row ρ => if embR ρ = row then 1 else 0
  have hPM : (Matrix.of fun row (c : D) => checkMatrix k ℓ row c) = P * M' := by
    ext row c
    rw [Matrix.mul_apply, Matrix.of_apply]
    have hterm : ∀ ρ, P row ρ * M' ρ c = if embR ρ = row then checkMatrix k ℓ (embR ρ) c else 0 := by
      intro ρ
      show (if embR ρ = row then (1 : ZMod 2) else 0) * checkMatrix k ℓ (embR ρ) c = _
      split_ifs <;> simp
    simp only [hterm]
    by_cases hrow : ∃ ρ0 : RowsR k ℓ r, embR ρ0 = row
    · obtain ⟨ρ0, rfl⟩ := hrow
      simp only [embR_inj]
      rw [Finset.sum_ite_eq' Finset.univ ρ0, if_pos (Finset.mem_univ _)]
    · rw [Finset.sum_eq_zero fun ρ _ => if_neg fun h => hrow ⟨ρ, h⟩]
      rcases row with i | t
      · exact absurd ⟨Sum.inl i, rfl⟩ hrow
      · have ht : ¬ r ≤ (t : ℕ) := fun ht => hrow ⟨Sum.inr ⟨t, ht⟩, rfl⟩
        show c.1.2 t = 0
        exact hD c.1 c.2 t (by omega)
  rw [hPM]
  refine (Matrix.rank_mul_le_right P M').trans ((Matrix.rank_le_card_height M').trans ?_)
  simp only [RowsR, Fintype.card_sum, Fintype.card_fin]
  exact Nat.add_le_add_left (card_tail_le r) _

theorem zeroOn_relayDom (j : ℕ) : ZeroOn (relayDom (k := k) (ℓ := ℓ) j) (j / (k - 1)) := by
  intro c hc t ht
  simp only [relayDom, mem_filter, mem_univ, true_and] at hc
  split_ifs at hc with hi
  · apply hc.1 t
    have h1 : ((t : ℕ) + 1) * (k - 1) ≤ j / (k - 1) * (k - 1) := Nat.mul_le_mul_right _ ht
    have h2 := Nat.div_mul_le_self j (k - 1)
    nlinarith
  · exact hc t ht

theorem zeroOn_zero (D : Finset (Coord k ℓ)) : ZeroOn D 0 := fun _ _ _ ht => absurd ht (by omega)

theorem sum_geom_div (K : ℕ) (hK : 0 < K) :
    ∀ ℓ, ∑ j ∈ range (K * ℓ), 2 ^ (ℓ - j / K) ≤ K * 2 ^ (ℓ + 1) := by
  intro ℓ
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    rw [show K * (ℓ + 1) = K + K * ℓ by ring, sum_range_add]
    have h1 : ∑ j ∈ range K, 2 ^ (ℓ + 1 - j / K) = K * 2 ^ (ℓ + 1) := by
      rw [sum_congr rfl fun j hj => by rw [Nat.div_eq_of_lt (mem_range.mp hj), Nat.sub_zero],
        sum_const, card_range, smul_eq_mul]
    have h2 : ∑ j ∈ range (K * ℓ), 2 ^ (ℓ + 1 - (K + j) / K) = ∑ j ∈ range (K * ℓ), 2 ^ (ℓ - j / K) := by
      refine sum_congr rfl fun j _ => ?_
      rw [show K + j = j + K * 1 by ring, Nat.add_mul_div_left _ _ hK]
      congr 1; omega
    rw [h1, h2]
    have : K * 2 ^ (ℓ + 1 + 1) = 2 * (K * 2 ^ (ℓ + 1)) := by ring
    omega

theorem sum_map_flatMap {α β : Type*} (L : List α) (f : α → List β) (g : β → ℕ) :
    ((L.flatMap f).map g).sum = (L.map fun a => ((f a).map g).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, ih]

/-- The summand `|𝔠_e| + 2^{rank B_e}` of a schema. -/
noncomputable def schemaCost {w : ℕ} (e : Schema k ℓ w) : ℕ := e.domain.card + 2 ^ rowRank e

theorem schemaCost_le {w : ℕ} (e : Schema k ℓ w) {r : ℕ} (hz : ZeroOn e.domain r) :
    schemaCost e ≤ (k + 2 ^ (k - 1)) * 2 ^ (ℓ - r) := by
  unfold schemaCost
  have h1 := card_le_of_zeroOn hz
  have h2 : 2 ^ rowRank e ≤ 2 ^ (k - 1) * 2 ^ (ℓ - r) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (rank_le_of_zeroOn hz)
  nlinarith

theorem gate_cost (j : Fin (nbits k ℓ)) :
    ((gate j).map schemaCost).sum ≤ 4 * ((k + 2 ^ (k - 1)) * 2 ^ (ℓ - (j : ℕ) / (k - 1))) := by
  have h := fun (e : Schema k ℓ (nlocs k ℓ)) (he : e.domain = relayDom j) =>
    schemaCost_le e (he ▸ zeroOn_relayDom (k := k) (ℓ := ℓ) j)
  simp only [gate, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have := h (.binary (loc k ℓ (.inl 0)) (loc k ℓ (.inr (j, 0))) (relayDom j) idP idP) rfl
  have := h (.binary (loc k ℓ (.inl 0)) (loc k ℓ (.inr (j, 1))) (relayDom j) idP idP) rfl
  have := h (.ternary (loc k ℓ (.inr (j, 0))) (loc k ℓ (.inr (j, 1)))
    (loc k ℓ (.inr (j, 2))) (relayDom j) idP idP idP) rfl
  have := h (.binary (loc k ℓ (.inr (j, 2))) (loc k ℓ (.inl 0)) (relayDom j) idP (decP j)) rfl
  omega

theorem card_supp_le (a : Fin k → BlockCoord ℓ) : (supp a).card ≤ k := by
  unfold supp
  exact card_image_le.trans (by simp)

theorem endpoints_cost : ((endpoints k ℓ).map schemaCost).sum ≤ 2 * (k + 2 ^ (k - 1) * 2 ^ ℓ) := by
  simp only [endpoints, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have h : ∀ a : Fin k → BlockCoord ℓ, schemaCost (Schema.binary (loc k ℓ (.inl 1))
      (loc k ℓ (.inl 0)) (supp a) idP idP) ≤ k + 2 ^ (k - 1) * 2 ^ ℓ ∧
      schemaCost (Schema.binary (loc k ℓ (.inl 2))
      (loc k ℓ (.inl 0)) (supp a) idP idP) ≤ k + 2 ^ (k - 1) * 2 ^ ℓ := by
    intro a
    have h2 : ∀ e : Schema k ℓ (nlocs k ℓ), 2 ^ rowRank e ≤ 2 ^ (k - 1) * 2 ^ ℓ := fun e => by
      have := rank_le_of_zeroOn (zeroOn_zero e.domain)
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by simpa [rowRank] using this)
    exact ⟨Nat.add_le_add (card_supp_le a) (h2 _), Nat.add_le_add (card_supp_le a) (h2 _)⟩
  have := (h (sAddr k ℓ)).1
  have := (h 0).2
  omega

/-- The constant of the size bound. -/
def sizeConst (k : ℕ) : ℕ :=
  k + 2 * k + 3 * k * (2 * (k - 1)) +
    (k + 1) * (2 * k + 2 * 2 ^ (k - 1) + 4 * (k + 2 ^ (k - 1)) * (2 * (k - 1)))

/-- **Size of the relay counter.** For `k ≥ 2`, the size parameter of the relay counter is at
most `sizeConst k · 2^ℓ`. -/
theorem relay_size (hk : 2 ≤ k) :
    Lax119563.RowSpaceCompiler.rowSpaceSize (relay k ℓ) ≤ sizeConst k * 2 ^ ℓ := by
  set X := 2 ^ ℓ with hX
  have hX1 : 1 ≤ X := Nat.one_le_two_pow
  set A := ∑ j : Fin (nbits k ℓ), 2 ^ (ℓ - (j : ℕ) / (k - 1)) with hA
  have hAle : A ≤ 2 * (k - 1) * X := by
    have h1 : A = ∑ j ∈ range ((k - 1) * ℓ), 2 ^ (ℓ - j / (k - 1)) := by
      rw [hA]; exact Fin.sum_univ_eq_sum_range (fun j => 2 ^ (ℓ - j / (k - 1))) _
    have h2 := sum_geom_div (k - 1) (by omega) ℓ
    have h3 : (k - 1) * 2 ^ (ℓ + 1) = 2 * (k - 1) * X := by rw [hX]; ring
    omega
  -- locations
  have hloc : ∑ x, ((relay k ℓ).domain x).card ≤ k * X + k + k + 3 * (k * A) := by
    have e1 : ∑ x, ((relay k ℓ).domain x).card = ∑ σ, (domS k ℓ σ).card := by
      simp only [relay]
      exact Equiv.sum_comp (locEquiv _).symm (fun σ => (domS k ℓ σ).card)
    rw [e1, Fintype.sum_sum_type, Fin.sum_univ_three, Fintype.sum_prod_type]
    simp only [domS, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    have h0 : (univ : Finset (Coord k ℓ)).card = k * X := by
      simp [hX, Fintype.card_prod, Fintype.card_fun, ZMod.card]
    rw [Finset.card_univ] at h0
    have h3 : ∑ j : Fin (nbits k ℓ), 3 * (relayDom (k := k) (ℓ := ℓ) j).card ≤ 3 * (k * A) := by
      rw [hA, mul_sum, mul_sum]
      exact sum_le_sum fun j _ => by
        have := card_le_of_zeroOn (zeroOn_relayDom (k := k) (ℓ := ℓ) j)
        nlinarith
    have := card_supp_le (sAddr k ℓ)
    have := card_supp_le (0 : Fin k → BlockCoord ℓ)
    omega
  -- schemas
  have hsch : ((relay k ℓ).schemas.map fun e => e.domain.card + 2 ^ rowRank e).sum ≤
      2 * (k + 2 ^ (k - 1) * X) + 4 * (k + 2 ^ (k - 1)) * A := by
    change ((relaySchemas k ℓ).map schemaCost).sum ≤ _
    rw [relaySchemas, List.map_append, List.sum_append, sum_map_flatMap, ← Fin.sum_univ_def]
    have hg : ∑ j : Fin (nbits k ℓ), ((gate j).map schemaCost).sum ≤
        4 * (k + 2 ^ (k - 1)) * A := by
      rw [hA, mul_sum]
      exact sum_le_sum fun j _ => (gate_cost j).trans (le_of_eq (by ring))
    have := endpoints_cost (k := k) (ℓ := ℓ)
    rw [← hX] at this
    omega
  unfold Lax119563.RowSpaceCompiler.rowSpaceSize
  calc ∑ x, ((relay k ℓ).domain x).card +
        (k + 1) * ((relay k ℓ).schemas.map fun e => e.domain.card + 2 ^ rowRank e).sum
      ≤ (k * X + k + k + 3 * (k * A)) +
        (k + 1) * (2 * (k + 2 ^ (k - 1) * X) + 4 * (k + 2 ^ (k - 1)) * A) := by gcongr
    _ ≤ (k * X + k * X + k * X + 3 * (k * (2 * (k - 1) * X))) +
        (k + 1) * (2 * (k * X + 2 ^ (k - 1) * X) + 4 * (k + 2 ^ (k - 1)) * (2 * (k - 1) * X)) := by
      have hkX : k ≤ k * X := Nat.le_mul_of_pos_right _ hX1
      gcongr
    _ = sizeConst k * X := by unfold sizeConst; ring

end Lax119563Proofs.Witness
