import Lax119563Proofs.RowSpace.Extension

/-!
# Counting exposed variables and equations

For a set `A` of at most `k + 1` classes: at most four variables are exposed (Lemma
"Exposure" (i): at most one per location, each needs `k` coordinates, and every class
contributes coordinates to at most three locations), and at most one equation is exposed.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler
open Lax119563Proofs.Matrix

namespace Lax119563Proofs.RowSpace

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

/-- The variables exposed for `A`. -/
noncomputable def varSet (A : Finset (ICls I)) :
    Finset (Fin I.numLocations × (Fin k → BlockCoord ℓ)) := by
  classical
  exact Finset.univ.filter fun γ => IsAddress γ.2 ∧ supp γ.2 ⊆ Iloc A γ.1

lemma mem_varSet {A : Finset (ICls I)} {γ : Fin I.numLocations × (Fin k → BlockCoord ℓ)} :
    γ ∈ varSet A ↔ IsAddress γ.2 ∧ supp γ.2 ⊆ Iloc A γ.1 := by
  classical
  simp [varSet]

/-- Every schema has at most three arguments. -/
lemma arity_le_three {w : ℕ} (s : Lax119563.ImplicitParitySystems.Schema k ℓ w) :
    arity s ≤ 3 := by
  cases s <;> simp [arity]

lemma sum_card_argContrib_le (e : Fin I.schemas.length) (c : Coord k ℓ) :
    ∑ v, (argContrib I e c v).card ≤ 3 := by
  classical
  calc ∑ v, (argContrib I e c v).card
      ≤ ∑ v, (Finset.univ.filter fun i => argLoc (sch I e) i = v).card :=
        Finset.sum_le_sum fun v _ => Finset.card_image_le
    _ = (Finset.univ : Finset (Fin (arity (sch I e)))).card :=
        (Finset.card_eq_sum_card_fiberwise fun _ _ => Finset.mem_univ _).symm
    _ ≤ 3 := by simpa using arity_le_three (sch I e)

/-- Each class contributes at most three coordinates over all locations. -/
lemma sum_card_locContrib_le (X : ICls I) : ∑ v, (locContrib X v).card ≤ 3 := by
  classical
  cases hi : Lax119563Proofs.Matrix.inner X with
  | some p =>
    obtain ⟨e, c⟩ := p
    simp only [locContrib_of_inner hi]
    exact sum_card_argContrib_le e c
  | none =>
    rcases inner_none hi with ⟨v', c, rfl⟩ | ⟨e, σ, rfl⟩
    · simp [locContrib, apply_ite]
    · simp [locContrib]

lemma sum_card_Iloc_le (A : Finset (ICls I)) : ∑ v, (Iloc A v).card ≤ 3 * A.card := by
  calc ∑ v, (Iloc A v).card ≤ ∑ v, ∑ X ∈ A, (locContrib X v).card :=
        Finset.sum_le_sum fun v _ => Finset.card_biUnion_le
    _ = ∑ X ∈ A, ∑ v, (locContrib X v).card := Finset.sum_comm
    _ ≤ ∑ X ∈ A, 3 := Finset.sum_le_sum fun X _ => sum_card_locContrib_le X
    _ = 3 * A.card := by simp [mul_comm]

/-- The pebbled coordinates of schema `e` come from classes internal to `e`. -/
lemma card_Isch_le_filter (A : Finset (ICls I)) (e : Fin I.schemas.length) :
    (Isch A e).card ≤
      (A.filter fun X => ∃ c, Lax119563Proofs.Matrix.inner X = some (e, c)).card := by
  classical
  set S := A.filter fun X => ∃ c, Lax119563Proofs.Matrix.inner X = some (e, c)
  refine (Finset.card_le_card (t := S.biUnion fun X => schContrib X e) ?_).trans
    (card_biUnion_le_card fun X => card_schContrib_le X e)
  intro c hc
  obtain ⟨X, hX, h⟩ := mem_Isch.mp hc
  refine Finset.mem_biUnion.mpr ⟨X, Finset.mem_filter.mpr ⟨hX, c, h⟩, ?_⟩
  simp [schContrib_of_inner h]

/-- At most four variables are exposed. -/
theorem card_varSet_le (hk : 3 ≤ k) {A : Finset (ICls I)} (hA : A.card ≤ k + 1) :
    (varSet A).card ≤ 4 := by
  classical
  have hinj : Set.InjOn Prod.fst
      ((varSet A : Finset (Fin I.numLocations × (Fin k → BlockCoord ℓ))) :
        Set (Fin I.numLocations × (Fin k → BlockCoord ℓ))) := by
    intro γ hγ δ hδ h
    rw [Finset.mem_coe, mem_varSet] at hγ hδ
    have h2 : γ.2 = δ.2 := address_unique hγ.1 hδ.1 ((card_Iloc_le A γ.1).trans hA) hγ.2
      (h ▸ hδ.2)
    exact Prod.ext h h2
  rw [← Finset.card_image_of_injOn hinj]
  set V := (varSet A).image Prod.fst
  have hV : ∀ v ∈ V, k ≤ (Iloc A v).card := by
    intro v hv
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hv
    rw [mem_varSet] at hγ
    simpa [card_supp] using Finset.card_le_card hγ.2
  have hsum : V.card * k ≤ 3 * (k + 1) :=
    calc V.card * k = ∑ v ∈ V, k := by simp
      _ ≤ ∑ v ∈ V, (Iloc A v).card := Finset.sum_le_sum hV
      _ ≤ ∑ v, (Iloc A v).card := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ ≤ 3 * A.card := sum_card_Iloc_le A
      _ ≤ 3 * (k + 1) := by omega
  by_contra hc
  have : 5 * k ≤ V.card * k := Nat.mul_le_mul_right _ (by omega)
  omega

/-- At most one equation is exposed. -/
theorem exposed_unique (hk : 2 ≤ k) {A : Finset (ICls I)} (hA : A.card ≤ k + 1)
    {e e' : Fin I.schemas.length} {a a' : Fin k → BlockCoord ℓ} (ha : IsAddress a)
    (ha' : IsAddress a') (hs : supp a ⊆ Isch A e) (hs' : supp a' ⊆ Isch A e') :
    e = e' ∧ a = a' := by
  classical
  have hee : e = e' := by
    by_contra hne
    have h1 := (Finset.card_le_card hs).trans (card_Isch_le_filter A e)
    have h2 := (Finset.card_le_card hs').trans (card_Isch_le_filter A e')
    rw [card_supp] at h1 h2
    have hdisj : Disjoint
        (A.filter fun X => ∃ c, Lax119563Proofs.Matrix.inner X = some (e, c))
        (A.filter fun X => ∃ c, Lax119563Proofs.Matrix.inner X = some (e', c)) := by
      refine Finset.disjoint_filter.mpr fun X _ ⟨c, hc⟩ ⟨c', hc'⟩ => hne ?_
      rw [hc] at hc'
      exact congrArg Prod.fst (Option.some.inj hc')
    have h3 := Finset.card_union_of_disjoint hdisj
    have h4 := Finset.card_le_card (Finset.union_subset
      (Finset.filter_subset (fun X => ∃ c, Lax119563Proofs.Matrix.inner X = some (e, c)) A)
      (Finset.filter_subset (fun X => ∃ c, Lax119563Proofs.Matrix.inner X = some (e', c)) A))
    omega
  subst hee
  exact ⟨rfl, address_unique ha ha' ((card_Isch_le A e).trans hA) hs hs'⟩

end Lax119563Proofs.RowSpace
