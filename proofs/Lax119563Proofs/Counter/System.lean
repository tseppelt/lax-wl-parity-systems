import Lax119563Proofs.Counter.Bits

/-!
# The counter implicit parity system

Locations (with `m = ℓ K` data positions): the main location `0` with the full coordinate
domain, the endpoint locations `1` (initialized `0`, domain `supp 0`) and `2` (initialized
`1`, domain `supp t`), and for every data position `j < m` the private locations
`p_j = 3 + 2j` and `q_j = 4 + 2j` with domain `𝔠'_j`. The schemas are
`X_{1,a} = X_{0,a}`, `X_{2,a} = X_{0,a}` and, for every `j`,
`X_{0,a} = X_{p_j,a} = X_{q_j,a} = X_{0,a+δ_j}` for the addresses `a` supported in `𝔠'_j`,
which are exactly the addresses with data prefix `1^j 0`.
-/

open Lax119563.ImplicitParitySystems

namespace Lax119563Proofs.Counter

variable {K ℓ : ℕ}

/-- The coordinates allowed for the increment at position `j`: data coordinates have the bits
of a `1^j 0` prefix at the data positions `≤ j` of their block, and the checksum coordinate
has bit `K` in every row lying entirely below `j`. -/
def GoodCoord (K ℓ j : ℕ) (c : Coord (K + 1) ℓ) : Prop :=
  (∀ p : Fin (ℓ * K), (p : ℕ) ≤ j → Fin.castSucc ((pos K ℓ).symm p).2 = c.1 →
      c.2 ((pos K ℓ).symm p).1 = if (p : ℕ) < j then 1 else 0) ∧
    (c.1 = Fin.last K → ∀ t : Fin ℓ, K * ((t : ℕ) + 1) ≤ j → c.2 t = (K : ZMod 2))

open Classical in
/-- The coordinate domain `𝔠'_j`. -/
noncomputable def dom (K ℓ j : ℕ) : Finset (Coord (K + 1) ℓ) :=
  Finset.univ.filter (GoodCoord K ℓ j)

theorem mem_dom {j : ℕ} {c : Coord (K + 1) ℓ} : c ∈ dom K ℓ j ↔ GoodCoord K ℓ j c := by
  simp [dom]

theorem supp_subset_iff (a : Arr K ℓ) (D : Finset (Coord (K + 1) ℓ)) :
    supp a ⊆ D ↔ ∀ i, (i, a i) ∈ D := by
  simp [supp, Finset.image_subset_iff]

theorem eq_of_supp_subset {a c : Arr K ℓ} (h : supp a ⊆ supp c) : a = c := by
  rw [supp_subset_iff] at h
  funext i
  have := h i
  simp only [supp, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq] at this
  obtain ⟨i', rfl, h'⟩ := this
  exact h'.symm

/-- The addresses supported in `𝔠'_j` are those with data prefix `1^j 0`. -/
theorem supp_subset_dom_iff {j : ℕ} {a : Arr K ℓ} (ha : IsAddress a) :
    supp a ⊆ dom K ℓ j ↔ Prefix j a := by
  rw [supp_subset_iff]
  constructor
  · intro h p hp
    have := (mem_dom.mp (h (Fin.castSucc ((pos K ℓ).symm p).2))).1 p hp rfl
    exact this
  · intro h i
    refine mem_dom.mpr ⟨?_, ?_⟩
    · intro p hp hi
      dsimp only at hi ⊢
      rw [← hi]
      exact h p hp
    · intro hi t ht
      dsimp only at hi ⊢
      rw [hi, last_eq_of_isAddress ha]
      have : ∀ i' : Fin K, a (Fin.castSucc i') t = 1 := by
        intro i'
        rw [← dbit_pos a t i', h _ (by rw [pos_val]; dsimp; nlinarith [i'.2]),
          if_pos (by rw [pos_val]; dsimp; nlinarith [i'.2])]
      simp [Finset.sum_apply, this]

theorem prefix_add_shift {j : ℕ} {a : Arr K ℓ} (ha : Prefix j a) :
    ∀ p : Fin (ℓ * K), (p : ℕ) ≤ j →
      dbit (a + shift K ℓ j) p = if (p : ℕ) < j then 0 else 1 := by
  intro p hp
  rw [dbit_add, dbit_shift, ha p hp, if_pos hp]
  split_ifs <;> decide

end Lax119563Proofs.Counter
