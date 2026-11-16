import Lax119563Proofs.Reduction.EntNum

/-!
# Validity of names, kind by kind

Unfolded forms of `Valid I (X, l)` for each kind of class, and `coef_valid`: if the domain
of schema `e` contains the whole checksum block `s`, every coefficient class `coef e σ` with
`σ < numSteps` is valid.
-/

open Lax119563.ImplicitParitySystems Lax119563Proofs.Matrix

namespace Lax119563Proofs.Reduction

variable {s ℓ : ℕ} (I : ImplicitParitySystem (s + 1) ℓ)

lemma valid_upd_iff {e : Fin I.schemas.length} {σ : ℕ} {c : Coord (s + 1) ℓ} {l : Lab} :
    Valid I (.upd e σ c, l) ↔ σ < numSteps (s + 1) ℓ ∧ c ∈ dom I e ∧ ent σ c ≠ 0 := by
  simp [Valid, ClsValid, LabelOK, twoBit, isSingleton]

lemma valid_junc_iff {e : Fin I.schemas.length} {c : Coord (s + 1) ℓ} {l : Lab} :
    Valid I (.junc e c, l) ↔ isTern (sch I e) = true ∧ c ∈ dom I e := by
  simp [Valid, ClsValid, LabelOK, twoBit, isSingleton]

lemma valid_link_iff {e : Fin I.schemas.length} {c : Coord (s + 1) ℓ} {l : Lab} :
    Valid I (.link e c, l) ↔ c ∈ dom I e ∧ l.2 = 0 := by
  simp [Valid, ClsValid, LabelOK, twoBit, isSingleton]

lemma valid_sum_iff {e : Fin I.schemas.length} {c : Coord (s + 1) ℓ} {l : Lab} :
    Valid I (.sum e c, l) ↔ (isTern (sch I e) = true ∧ c ∈ dom I e) ∧ l.2 = 0 := by
  simp [Valid, ClsValid, LabelOK, twoBit, isSingleton]

lemma valid_track_iff {e : Fin I.schemas.length} {σ : ℕ} {c : Coord (s + 1) ℓ} {l : Lab} :
    Valid I (.track e σ c, l) ↔ (σ < numSteps (s + 1) ℓ ∧ c ∈ dom I e ∧ ent σ c ≠ 0) ∧ l.2 = 0 := by
  simp [Valid, ClsValid, LabelOK, twoBit, isSingleton]

lemma valid_coord_iff {v : Fin I.numLocations} {c : Coord (s + 1) ℓ} {l : Lab} :
    Valid I (.coord v c, l) ↔
      c ∈ I.domain v ∧ l.2 = 0 ∧ ((I.init v).isSome = true → l.1 = 0) := by
  simp [Valid, ClsValid, LabelOK, twoBit, isSingleton]

lemma valid_coef_iff {e : Fin I.schemas.length} {σ : ℕ} {l : Lab} :
    Valid I (.coef e σ, l) ↔ (σ < numSteps (s + 1) ℓ ∧ ∃ c ∈ dom I e, ent σ c ≠ 0) ∧ l.2 = 0 := by
  simp [Valid, ClsValid, LabelOK, twoBit, isSingleton]

/-- Coefficient classes are present as soon as the domain contains the checksum block. -/
lemma coef_exists (hs : 1 ≤ s) {e : Fin I.schemas.length}
    (hdom : ∀ b : BlockCoord ℓ, ((Fin.last s, b) : Coord (s + 1) ℓ) ∈ dom I e) (σ : ℕ) :
    ∃ c ∈ dom I e, ent σ c ≠ 0 := by
  have h : 0 < s + ℓ := by omega
  by_cases hj : σ % (s + ℓ) < s
  · refine ⟨(Fin.last s, 0), hdom 0, ?_⟩
    rw [ent_eq h, dif_pos hj]
    simp
  · have hlt : σ % (s + ℓ) - s < ℓ := by have := Nat.mod_lt σ h; omega
    refine ⟨(Fin.last s, fun t => if t.val = σ % (s + ℓ) - s then 1 else 0), hdom _, ?_⟩
    rw [ent_eq h, dif_neg hj]
    simp

end Lax119563Proofs.Reduction
