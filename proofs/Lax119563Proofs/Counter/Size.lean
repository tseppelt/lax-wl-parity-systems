import Lax119563.RowSpaceCompiler
import Lax119563Proofs.Counter.Rounds

/-!
# The size parameter of the counter

For the increment at position `j`, all coordinates of `𝔠'_j` have fixed bits in the rows
`t < ⌊j / K⌋`. Hence `|𝔠'_j| ≤ (K+1) 2^{ℓ - ⌊j/K⌋}`, and the columns of the check matrix
indexed by `𝔠'_j` lie in the span of `K + 1` block vectors and `ℓ - ⌊j/K⌋` unit vectors,
so `rank B_e ≤ K + 1 + ℓ - ⌊j/K⌋`. Summing the geometric series over the rows gives
`sizeParameter = O_K(2^ℓ)`.
-/

open Lax119563.ImplicitParitySystems Lax119563.RowSpaceCompiler
open Lax119563.MatrixCompiler (checkMatrix)

namespace Lax119563Proofs.Counter

variable {K ℓ : ℕ}

/-- The fixed bit value of block `i` in a row lying entirely below the increment position. -/
def fixBit (K : ℕ) (i : Fin (K + 1)) : ZMod 2 := if i = Fin.last K then (K : ZMod 2) else 1

/-- All coordinates of `D` have the fixed bits in the rows `t < r`. -/
def FixedRows (r : ℕ) (D : Finset (Coord (K + 1) ℓ)) : Prop :=
  ∀ c ∈ D, ∀ t : Fin ℓ, (t : ℕ) < r → c.2 t = fixBit K c.1

theorem fixedRows_zero (D : Finset (Coord (K + 1) ℓ)) : FixedRows 0 D :=
  fun _ _ _ ht => absurd ht (Nat.not_lt_zero _)

theorem fixedRows_dom (j : ℕ) : FixedRows (j / K) (dom K ℓ j) := by
  rintro ⟨i, b⟩ hc t ht
  have hg := mem_dom.mp hc
  have hKt : K * ((t : ℕ) + 1) ≤ j :=
    (Nat.mul_le_mul_left K (Nat.succ_le_of_lt ht)).trans (Nat.mul_div_le j K)
  induction i using Fin.lastCases with
  | last =>
    simp only [fixBit]
    exact hg.2 rfl t hKt
  | cast i =>
    simp only [fixBit, if_neg (Fin.castSucc_lt_last i).ne]
    have hlt : (pos K ℓ (t, i) : ℕ) < j := by
      rw [pos_val]; dsimp
      have := i.2
      nlinarith
    have := hg.1 (pos K ℓ (t, i)) hlt.le (by simp)
    simpa [hlt] using this

theorem card_fixed_le (r : ℕ) (z : ZMod 2) :
    (Finset.univ.filter fun b : BlockCoord ℓ => ∀ t : Fin ℓ, (t : ℕ) < r → b t = z).card ≤
      2 ^ (ℓ - r) := by
  have : (Finset.univ : Finset (Fin (ℓ - r) → ZMod 2)).card = 2 ^ (ℓ - r) := by
    simp [Finset.card_univ, ZMod.card]
  rw [← this]
  refine Finset.card_le_card_of_injOn (fun b u => b ⟨r + u, by omega⟩)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_
  intro b hb b' hb' h
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hb hb'
  funext t
  by_cases ht : (t : ℕ) < r
  · rw [hb t ht, hb' t ht]
  · have := congrFun h ⟨t - r, by omega⟩
    simp only at this
    have e : (⟨r + (t - r), by omega⟩ : Fin ℓ) = t := Fin.ext (by simp; omega)
    rwa [e] at this

theorem card_le_of_fixedRows {r : ℕ} {D : Finset (Coord (K + 1) ℓ)} (hD : FixedRows r D) :
    D.card ≤ (K + 1) * 2 ^ (ℓ - r) := by
  classical
  have hsub : D ⊆ Finset.univ.biUnion fun i : Fin (K + 1) =>
      (Finset.univ.filter fun b : BlockCoord ℓ => ∀ t : Fin ℓ, (t : ℕ) < r → b t = fixBit K i).image
        fun b => (i, b) := by
    rintro ⟨i, b⟩ hc
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_filter, Prod.mk.injEq]
    exact ⟨i, b, fun t ht => hD _ hc t ht, rfl, rfl⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  calc ∑ i : Fin (K + 1), _ ≤ ∑ _i : Fin (K + 1), 2 ^ (ℓ - r) :=
        Finset.sum_le_sum fun i _ => Finset.card_image_le.trans (card_fixed_le r _)
    _ = (K + 1) * 2 ^ (ℓ - r) := by simp

theorem card_filter_ge (r : ℕ) :
    (Finset.univ.filter fun t : Fin ℓ => r ≤ (t : ℕ)).card ≤ ℓ - r := by
  have : (Finset.Ico r ℓ).card = ℓ - r := Nat.card_Ico r ℓ
  rw [← this]
  refine Finset.card_le_card_of_injOn (fun t => (t : ℕ)) ?_ (fun a _ b _ h => Fin.ext h)
  intro t ht
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ht
  simp [ht, t.2]

/-- The block coordinate with the fixed bits of block `i` in the rows `t < r` and zeros
elsewhere. -/
def fixT (K ℓ r : ℕ) (i : Fin (K + 1)) : BlockCoord ℓ :=
  fun t => if (t : ℕ) < r then fixBit K i else 0

/-- A column of the check matrix splits into the column of `fixT` and unit vectors of the
free rows. -/
theorem col_decomp (r : ℕ) (x : Coord (K + 1) ℓ)
    (hb : ∀ t : Fin ℓ, (t : ℕ) < r → x.2 t = fixBit K x.1) :
    (fun row => checkMatrix (K + 1) ℓ row x) =
      (fun row => checkMatrix (K + 1) ℓ row (x.1, fixT K ℓ r x.1)) +
        ∑ t ∈ Finset.univ.filter (fun t : Fin ℓ => r ≤ (t : ℕ)),
          x.2 t • (Pi.single (Sum.inr t) (1 : ZMod 2) : Fin (K + 1 - 1) ⊕ Fin ℓ → ZMod 2) := by
  obtain ⟨i, b⟩ := x
  funext row
  rw [Pi.add_apply, Finset.sum_apply]
  rcases row with i₀ | t₀
  · simp [checkMatrix]
  · simp only [checkMatrix, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      Sum.inr.injEq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_filter, Finset.mem_univ, true_and, fixT]
    by_cases ht : (t₀ : ℕ) < r
    · rw [if_pos ht, if_neg (by omega), add_zero]
      exact hb t₀ ht
    · rw [if_neg ht, if_pos (by omega), zero_add]

/-- The column of the check matrix at `(i, fixT i)`. -/
def blockVec (K ℓ r : ℕ) (i : Fin (K + 1)) : Fin (K + 1 - 1) ⊕ Fin ℓ → ZMod 2 :=
  fun row => checkMatrix (K + 1) ℓ row (i, fixT K ℓ r i)

/-- The unit vector of checksum row `t`. -/
noncomputable def unitVec (K ℓ : ℕ) (t : Fin ℓ) : Fin (K + 1 - 1) ⊕ Fin ℓ → ZMod 2 :=
  Pi.single (Sum.inr t) 1

/-- The free rows `t ≥ r`. -/
def freeRows (ℓ r : ℕ) : Finset (Fin ℓ) := Finset.univ.filter fun t => r ≤ (t : ℕ)

open Classical in
/-- The spanning set of `K + 1` block vectors and `ℓ - r` unit vectors. -/
noncomputable def spanSet (K ℓ r : ℕ) : Finset (Fin (K + 1 - 1) ⊕ Fin ℓ → ZMod 2) :=
  Finset.univ.image (blockVec K ℓ r) ∪ (freeRows ℓ r).image (unitVec K ℓ)

theorem card_spanSet (r : ℕ) : (spanSet K ℓ r).card ≤ K + 1 + (ℓ - r) := by
  classical
  unfold spanSet
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
  · exact Finset.card_image_le.trans (by simp)
  · exact Finset.card_image_le.trans (card_filter_ge r)

theorem col_mem_span (r : ℕ) (x : Coord (K + 1) ℓ)
    (hb : ∀ t : Fin ℓ, (t : ℕ) < r → x.2 t = fixBit K x.1) :
    (fun row => checkMatrix (K + 1) ℓ row x) ∈
      Submodule.span (ZMod 2) (spanSet K ℓ r : Set (Fin (K + 1 - 1) ⊕ Fin ℓ → ZMod 2)) := by
  classical
  rw [col_decomp r x hb]
  refine Submodule.add_mem _ (Submodule.subset_span ?_) (Submodule.sum_mem _ fun t ht => ?_)
  · show blockVec K ℓ r x.1 ∈ (spanSet K ℓ r : Set _)
    unfold spanSet
    exact Finset.mem_coe.mpr (Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (Finset.mem_univ x.1)))
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    show unitVec K ℓ t ∈ (spanSet K ℓ r : Set _)
    unfold spanSet
    exact Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ht))

/-- **Rank bound.** If all coordinates of the domain have fixed bits in the rows `t < r`, then
`rank B_e ≤ K + 1 + (ℓ - r)`. -/
theorem rank_le_of_fixedRows {r : ℕ} (D : Finset (Coord (K + 1) ℓ)) (hD : FixedRows r D) :
    (Matrix.of fun row (c : D) => checkMatrix (K + 1) ℓ row c).rank ≤ K + 1 + (ℓ - r) := by
  have hspan : Submodule.span (ZMod 2)
      (Set.range (Matrix.of fun row (c : D) => checkMatrix (K + 1) ℓ row c).col) ≤
        Submodule.span (ZMod 2) (spanSet K ℓ r : Set _) := by
    rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    have hc : (Matrix.of fun row (c : D) => checkMatrix (K + 1) ℓ row c).col c =
        fun row => checkMatrix (K + 1) ℓ row c.1 := rfl
    rw [hc]
    exact col_mem_span r c.1 (fun t ht => hD _ c.2 t ht)
  rw [Matrix.rank_eq_finrank_span_cols]
  exact (Submodule.finrank_mono hspan).trans
    ((finrank_span_finset_le_card (spanSet K ℓ r)).trans (card_spanSet r))

/-! ### Summation -/

theorem sum_pow_sub (ℓ : ℕ) : ∑ t ∈ Finset.range ℓ, 2 ^ (ℓ - t) + 2 = 2 ^ (ℓ + 1) := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    rw [Finset.sum_range_succ']
    have : ∀ t ∈ Finset.range ℓ, 2 ^ (ℓ + 1 - (t + 1)) = 2 ^ (ℓ - t) := fun t _ => by
      congr 1; omega
    rw [Finset.sum_congr rfl this, Nat.sub_zero, pow_succ 2 (ℓ + 1)]
    omega

theorem sum_pow_rows (hK : 0 < K) :
    ∑ j : Fin (ℓ * K), 2 ^ (ℓ - (j : ℕ) / K) ≤ K * 2 ^ (ℓ + 1) := by
  rw [← (pos K ℓ).sum_comp]
  have h1 : ∀ x : Fin ℓ × Fin K, ((pos K ℓ x : ℕ) / K) = x.1 := by
    intro x
    rw [pos_val, Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt x.2.2, zero_add]
  simp only [h1]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [← Finset.mul_sum]
  gcongr
  rw [Fin.sum_univ_eq_sum_range (fun t => 2 ^ (ℓ - t)) ℓ]
  have := sum_pow_sub ℓ
  omega

theorem sum_domN (M : ℕ) (f : ℕ → ℕ) :
    ∑ n ∈ Finset.range (3 + 2 * M), f n =
      f 0 + f 1 + f 2 + ∑ j ∈ Finset.range M, (f (3 + 2 * j) + f (4 + 2 * j)) := by
  induction M with
  | zero => simp [Finset.sum_range_succ]
  | succ M ih =>
    rw [show 3 + 2 * (M + 1) = 3 + 2 * M + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring_nf

theorem card_supp_le (a : Arr K ℓ) : (supp a).card ≤ K + 1 :=
  Finset.card_image_le.trans (by simp)

theorem rowRank_le_of_fixedRows {w r : ℕ} (e : Schema (K + 1) ℓ w) (hD : FixedRows r e.domain) :
    rowRank e ≤ K + 1 + (ℓ - r) :=
  rank_le_of_fixedRows e.domain hD

/-- The contribution of a single schema. -/
theorem schema_bound (x : SchIdx K ℓ) :
    (schemaOf x).domain.card + 2 ^ rowRank (schemaOf x) ≤
      match x with
      | .inl _ => (K + 1) + 2 ^ (K + 1) * 2 ^ ℓ
      | .inr (j, _) => (K + 1 + 2 ^ (K + 1)) * 2 ^ (ℓ - (j : ℕ) / K) := by
  rcases x with b | ⟨j, c⟩
  · have hdom : ∃ a : Arr K ℓ, (schemaOf (.inl b)).domain = supp a := by
      cases b
      · exact ⟨0, rfl⟩
      · exact ⟨top K ℓ, rfl⟩
    obtain ⟨a, ha⟩ := hdom
    have h1 := rowRank_le_of_fixedRows (schemaOf (K := K) (ℓ := ℓ) (.inl b)) (fixedRows_zero _)
    have h2 : 2 ^ rowRank (schemaOf (K := K) (ℓ := ℓ) (.inl b)) ≤ 2 ^ (K + 1) * 2 ^ ℓ := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [ha]
    have := card_supp_le a
    dsimp only
    omega
  · have hdom : (schemaOf (.inr (j, c))).domain = dom K ℓ j := by
      fin_cases c <;> rfl
    have hfix : FixedRows ((j : ℕ) / K) (schemaOf (K := K) (ℓ := ℓ) (.inr (j, c))).domain := by
      rw [hdom]; exact fixedRows_dom j
    have h1 := rowRank_le_of_fixedRows _ hfix
    have h2 : 2 ^ rowRank (schemaOf (K := K) (ℓ := ℓ) (.inr (j, c))) ≤
        2 ^ (K + 1) * 2 ^ (ℓ - (j : ℕ) / K) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) h1
    have h3 := card_le_of_fixedRows hfix
    dsimp only
    rw [add_mul]
    omega

/-- **Size of the counter.** `sizeParameter(𝓘_ctr) ≤ C_K 2^ℓ`. -/
theorem sizeParameter_le (hK : 0 < K) : ∃ C : ℕ, ∀ ℓ : ℕ,
    sizeParameter (counter K ℓ) ≤ C * 2 ^ ℓ := by
  refine ⟨(K + 1) + 2 * (K + 1) + 2 * (K + 1) * (2 * K) +
    (K + 2) * (2 * (K + 1) + 2 * 2 ^ (K + 1) + 3 * (K + 1 + 2 ^ (K + 1)) * (2 * K)), fun ℓ => ?_⟩
  set A := 2 ^ ℓ with hA
  have hA1 : 1 ≤ A := Nat.one_le_two_pow
  set G := ∑ j : Fin (ℓ * K), 2 ^ (ℓ - (j : ℕ) / K) with hG
  have hGle : G ≤ 2 * K * A := by
    have := sum_pow_rows (ℓ := ℓ) hK
    rw [pow_succ] at this
    calc G ≤ K * (A * 2) := this
      _ = 2 * K * A := by ring
  -- the locations
  have hv : ∑ v : Fin (numLoc K ℓ), (domN K ℓ v).card ≤ (K + 1) * A + 2 * (K + 1) + 2 * (K + 1) * G := by
    rw [Fin.sum_univ_eq_sum_range (fun n => (domN K ℓ n).card), sum_domN]
    simp only [domN_p, domN_q]
    have h0 : (domN K ℓ 0).card = (K + 1) * A := by
      simp [domN, Finset.card_univ, ZMod.card, hA]
    have h1 : (domN K ℓ 1).card ≤ K + 1 := by simp only [domN]; simpa using card_supp_le _
    have h2 : (domN K ℓ 2).card ≤ K + 1 := by simp only [domN]; simpa using card_supp_le _
    have h3 : ∑ j ∈ Finset.range (ℓ * K), ((dom K ℓ j).card + (dom K ℓ j).card) ≤ 2 * (K + 1) * G := by
      rw [hG, ← Fin.sum_univ_eq_sum_range (fun j => (dom K ℓ j).card + (dom K ℓ j).card),
        Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => by
        have := card_le_of_fixedRows (fixedRows_dom (K := K) (ℓ := ℓ) j)
        nlinarith
    omega
  -- the schemas
  have hs : ((counter K ℓ).schemas.map fun e => e.domain.card + 2 ^ rowRank e).sum ≤
      2 * ((K + 1) + 2 ^ (K + 1) * A) + 3 * ((K + 1 + 2 ^ (K + 1)) * G) := by
    show (((Finset.univ : Finset (SchIdx K ℓ)).toList.map schemaOf).map
      fun e => e.domain.card + 2 ^ rowRank e).sum ≤ _
    rw [List.map_map, Finset.sum_map_toList]
    refine (Finset.sum_le_sum fun x _ => schema_bound x).trans (le_of_eq ?_)
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp [Finset.sum_const, Finset.card_univ, hG, Finset.mul_sum]
    ring
  have hP : 1 ≤ 2 ^ (K + 1) := Nat.one_le_two_pow
  have hv' : ∑ v : Fin (numLoc K ℓ), (domN K ℓ v).card ≤
      ((K + 1) + 2 * (K + 1) + 2 * (K + 1) * (2 * K)) * A := by
    calc _ ≤ (K + 1) * A + 2 * (K + 1) + 2 * (K + 1) * G := hv
      _ ≤ (K + 1) * A + 2 * (K + 1) * A + 2 * (K + 1) * (2 * K * A) :=
          Nat.add_le_add (Nat.add_le_add le_rfl (Nat.le_mul_of_pos_right _ hA1))
            (Nat.mul_le_mul_left _ hGle)
      _ = _ := by ring
  have hs' : ((counter K ℓ).schemas.map fun e => e.domain.card + 2 ^ rowRank e).sum ≤
      (2 * (K + 1) + 2 * 2 ^ (K + 1) + 3 * (K + 1 + 2 ^ (K + 1)) * (2 * K)) * A := by
    calc _ ≤ 2 * ((K + 1) + 2 ^ (K + 1) * A) + 3 * ((K + 1 + 2 ^ (K + 1)) * G) := hs
      _ ≤ 2 * ((K + 1) * A + 2 ^ (K + 1) * A) + 3 * ((K + 1 + 2 ^ (K + 1)) * (2 * K * A)) :=
          Nat.add_le_add
            (Nat.mul_le_mul_left 2 (Nat.add_le_add_right (Nat.le_mul_of_pos_right _ hA1) _))
            (Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left _ hGle))
      _ = _ := by ring
  calc sizeParameter (counter K ℓ)
      = ∑ v : Fin (numLoc K ℓ), (domN K ℓ v).card + (K + 1 + 1) *
          ((counter K ℓ).schemas.map fun e => e.domain.card + 2 ^ rowRank e).sum := rfl
    _ ≤ ((K + 1) + 2 * (K + 1) + 2 * (K + 1) * (2 * K)) * A + (K + 1 + 1) *
          ((2 * (K + 1) + 2 * 2 ^ (K + 1) + 3 * (K + 1 + 2 ^ (K + 1)) * (2 * K)) * A) :=
        Nat.add_le_add hv' (Nat.mul_le_mul_left _ hs')
    _ = _ := by ring

end Lax119563Proofs.Counter
