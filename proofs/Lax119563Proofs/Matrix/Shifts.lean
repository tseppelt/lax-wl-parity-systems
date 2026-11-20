import Lax119563Proofs.Matrix.Semantics
import Lax119563Proofs.Matrix.VertexList

/-!
# Descriptions and the induced translations

A *description* consists of total seeds `z_v` and coefficient bits `λ_{e,σ}`. It translates
the labels of every class; the translation `phi` is a class-preserving involution on names,
and it is an isomorphism between the graphs on every set of classes on which it is
*consistent* (initialized seeds and the mask-sum condition at the links).
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ}

/-! ### Steps -/

lemma ent_eq_one {σ : ℕ} {c : Coord k ℓ} (h : ent σ c ≠ 0) : ent σ c = 1 :=
  (zmod2_ne_zero_iff _).mp h

lemma prevStep_none {c : Coord k ℓ} {σ : ℕ} (h : prevStep c σ = none) :
    ∀ σ' < σ, ent σ' c = 0 := by
  induction σ with
  | zero => intro σ' h'; omega
  | succ σ ih =>
    simp only [prevStep] at h
    split at h
    · simp at h
    · next hne =>
      intro σ' hσ'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hσ' with h' | rfl
      · exact ih h σ' h'
      · exact not_not.mp hne

lemma prevStep_some {c : Coord k ℓ} {σ σ' : ℕ} (h : prevStep c σ = some σ') :
    σ' < σ ∧ ent σ' c ≠ 0 ∧ ∀ σ'', σ' < σ'' → σ'' < σ → ent σ'' c = 0 := by
  induction σ with
  | zero => simp [prevStep] at h
  | succ σ ih =>
    simp only [prevStep] at h
    split at h
    · next hne =>
      cases h
      exact ⟨Nat.lt_succ_self _, hne, fun σ'' h1 h2 => by omega⟩
    · next hne =>
      obtain ⟨h1, h2, h3⟩ := ih h
      refine ⟨by omega, h2, fun σ'' h4 h5 => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp h5 with h6 | rfl
      · exact h3 σ'' h4 h6
      · exact not_not.mp hne

lemma trackAt_succ (I : ImplicitParitySystem k ℓ) (e : Fin I.schemas.length) (c : Coord k ℓ)
    (σ : ℕ) : trackAt I e c (σ + 1) = if ent σ c ≠ 0 then .track e σ c else trackAt I e c σ := by
  by_cases h : ent σ c = 0 <;> simp [trackAt, prevStep, h]

/-! ### Descriptions -/

variable (I : ImplicitParitySystem k ℓ)

/-- A description: total seeds and coefficient bits. -/
structure Desc where
  /-- The seed of each location. -/
  z : Fin I.numLocations → Vec k ℓ
  /-- The coefficient bit of each step of each schema. -/
  lam : Fin I.schemas.length → ℕ → ZMod 2

variable {I}

/-- The initial track bit `t_{e,0}(c)`. -/
def t0 (D : Desc I) (e : Fin I.schemas.length) (c : Coord k ℓ) : ZMod 2 :=
  D.z (locU (sch I e)) ((permU (sch I e)).apply c) +
    if isTern (sch I e) then D.z (locV (sch I e)) ((permV (sch I e)).apply c) else 0

/-- The track bit of column `c` at stage `σ`. -/
def T (D : Desc I) (e : Fin I.schemas.length) (c : Coord k ℓ) (σ : ℕ) : ZMod 2 :=
  t0 D e c + ∑ σ' ∈ Finset.range σ, D.lam e σ' * ent σ' c

/-- The translation of each class. -/
def shift (D : Desc I) : ICls I → Lab
  | .coord v c => (D.z v c, 0)
  | .sum e c => (t0 D e c, 0)
  | .junc e c => (D.z (locU (sch I e)) ((permU (sch I e)).apply c),
      D.z (locV (sch I e)) ((permV (sch I e)).apply c))
  | .link e c => (T D e c (numSteps k ℓ), 0)
  | .track e σ c => (T D e c (σ + 1), 0)
  | .upd e σ c => (T D e c σ, T D e c (σ + 1))
  | .coef e σ => (D.lam e σ, 0)

/-- The map induced by a description on vertex names. -/
def phi (D : Desc I) (x : VName I) : VName I :=
  if isSingleton I x.1 then x else (x.1, x.2 + shift D x.1)

/-- The seeds of initialized locations are the initial seeds. -/
def InitOK (D : Desc I) : Prop := ∀ v, (I.init v).isSome → D.z v = initSeed I v

/-- The mask-sum condition at column `c` of schema `e`. -/
def MS (D : Desc I) (e : Fin I.schemas.length) (c : Coord k ℓ) : Prop :=
  T D e c (numSteps k ℓ) = D.z (locEnd (sch I e)) ((permEnd (sch I e)).apply c)

lemma T_succ (D : Desc I) (e : Fin I.schemas.length) (c : Coord k ℓ) (σ : ℕ) :
    T D e c (σ + 1) = T D e c σ + D.lam e σ * ent σ c := by
  simp [T, Finset.sum_range_succ, add_assoc]

lemma T_zero (D : Desc I) (e : Fin I.schemas.length) (c : Coord k ℓ) : T D e c 0 = t0 D e c := by
  simp [T]

lemma shift_startCls (D : Desc I) (e : Fin I.schemas.length) (c : Coord k ℓ) :
    (shift D (startCls I e c)).1 = t0 D e c := by
  unfold startCls t0
  split
  · next h => simp [shift, t0, h]
  · simp [shift]

lemma T_eq_of_zero (D : Desc I) (e : Fin I.schemas.length) (c : Coord k ℓ) {σ σ' : ℕ}
    (hle : σ ≤ σ') (h : ∀ σ'', σ ≤ σ'' → σ'' < σ' → ent σ'' c = 0) : T D e c σ' = T D e c σ := by
  induction hle with
  | refl => rfl
  | step hle ih =>
    rw [T_succ, h _ hle (Nat.lt_succ_self _), mul_zero, add_zero]
    exact ih fun σ'' h1 h2 => h σ'' h1 (Nat.lt_succ_of_lt h2)

lemma shift_trackAt (D : Desc I) (e : Fin I.schemas.length) (c : Coord k ℓ) (σ : ℕ) :
    (shift D (trackAt I e c σ)).1 = T D e c σ := by
  unfold trackAt
  split
  · next h =>
    rw [shift_startCls, T_eq_of_zero D e c (Nat.zero_le σ) fun σ'' _ h2 => prevStep_none h σ'' h2,
      T_zero]
  · next σ' h =>
    obtain ⟨h1, -, h3⟩ := prevStep_some h
    exact (T_eq_of_zero D e c h1 fun σ'' h4 h5 => h3 σ'' h4 h5).symm

/-! ### `phi` -/

@[simp] lemma phi_fst (D : Desc I) (x : VName I) : (phi D x).1 = x.1 := by
  unfold phi; split <;> rfl

lemma phi_phi (D : Desc I) (x : VName I) : phi D (phi D x) = x := by
  by_cases h : isSingleton I x.1 = true
  · simp [phi, h]
  · obtain ⟨X, l⟩ := x
    simp only at h
    simp only [phi, h, Bool.false_eq_true, if_false]
    ext <;> simp [add_assoc, zmod2_add_self]

lemma shift_snd (D : Desc I) {X : ICls I} (h : twoBit I X = false) : (shift D X).2 = 0 := by
  cases X <;> simp_all [twoBit, shift]

lemma valid_phi (D : Desc I) {x : VName I} (hx : Valid I x) : Valid I (phi D x) := by
  unfold phi
  split
  · exact hx
  · next hs =>
    refine ⟨hx.1, fun h2 => ?_, fun h => absurd h hs⟩
    simp only [Prod.snd_add, hx.2.1 h2, shift_snd D h2, add_zero]

lemma initBit_eq_zero_of_not_singleton {X : ICls I} (h : ¬ isSingleton I X = true) :
    initBit I X = 0 := by
  cases X with
  | coord v c =>
    simp only [isSingleton, Option.isSome_iff_ne_none, ne_eq, not_not] at h
    simp [initBit, initSeed, h]
  | _ => rfl

lemma eff_phi (D : Desc I) (hD : InitOK D) {x : VName I} (hx : Valid I x) :
    eff I 1 (phi D x) = eff I 0 x + shift D x.1 := by
  obtain ⟨X, l⟩ := x
  unfold phi eff
  split
  · next hs =>
    cases X with
    | coord v c =>
      have h1 : l.1 = 0 := hx.2.2 hs
      have h2 : l.2 = 0 := hx.2.1 rfl
      simp only [isSingleton] at hs
      simp [shift, initBit, hD v hs, h1, h2]
    | _ => simp [isSingleton] at hs
  · next hs =>
    simp [initBit_eq_zero_of_not_singleton hs]
    rfl

/-! ### Invariance of the hub relation -/

lemma and_decide_congr {Y A : ICls I} {P Q : Prop} [Decidable P] [Decidable Q]
    (h : Y = A → (P ↔ Q)) : (decide (Y = A) && decide P) = (decide (Y = A) && decide Q) := by
  by_cases hY : Y = A
  · simp [hY, h hY]
  · simp [hY]

/-- The hub relation is invariant under the translation, provided the mask-sum condition holds
at links and updates are valid. -/
lemma hubB_shift (D : Desc I) {X : ICls I} (hX : ClsValid I X)
    (hms : ∀ e c, X = .link e c → MS D e c) (l m : Lab) (Y : ICls I) :
    hubB I X (l + shift D X) Y (m + shift D Y) = hubB I X l Y m := by
  cases X with
  | upd e σ c =>
    have hent : ent σ c = 1 := ent_eq_one hX.2.2
    simp only [hubB]
    congr 1
    · congr 1
      · refine and_decide_congr fun hY => ?_
        subst hY
        rw [Prod.fst_add, Prod.fst_add, shift_trackAt]
        exact add_left_inj (T D e c σ)
      · refine and_decide_congr fun hY => ?_
        subst hY
        rw [Prod.fst_add, Prod.snd_add]
        exact add_left_inj (T D e c (σ + 1))
    · refine and_decide_congr fun hY => ?_
      subst hY
      simp only [Prod.fst_add, Prod.snd_add, shift, T_succ, hent, mul_one]
      constructor
      · intro h
        have : m.1 + D.lam e σ = l.1 + l.2 + D.lam e σ := by
          rw [h]; ring_nf; rw [show (2 : ZMod 2) = 0 from rfl]; ring
        exact add_right_cancel this
      · intro h
        rw [h]; ring_nf; rw [show (2 : ZMod 2) = 0 from rfl]; ring
  | junc e c =>
    simp only [hubB]
    congr 1
    · congr 1
      · refine and_decide_congr fun hY => ?_
        subst hY
        rw [Prod.fst_add, Prod.fst_add]
        exact add_left_inj (D.z (locU (sch I e)) ((permU (sch I e)).apply c))
      · refine and_decide_congr fun hY => ?_
        subst hY
        rw [Prod.fst_add, Prod.snd_add]
        exact add_left_inj (D.z (locV (sch I e)) ((permV (sch I e)).apply c))
    · refine and_decide_congr fun hY => ?_
      subst hY
      have ht : isTern (sch I e) = true := hX.1
      simp only [Prod.fst_add, Prod.snd_add, shift, t0, ht, if_true]
      constructor
      · intro h
        have := h
        refine add_right_cancel (b := D.z (locU (sch I e)) ((permU (sch I e)).apply c) +
          D.z (locV (sch I e)) ((permV (sch I e)).apply c)) ?_
        rw [this]; ring
      · intro h; rw [h]; ring
  | link e c =>
    have hm := hms e c rfl
    simp only [hubB]
    congr 1
    · refine and_decide_congr fun hY => ?_
      subst hY
      rw [Prod.fst_add, Prod.fst_add, shift_trackAt]
      exact add_left_inj (T D e c (numSteps k ℓ))
    · refine and_decide_congr fun hY => ?_
      subst hY
      rw [Prod.fst_add, Prod.fst_add]
      rw [MS] at hm
      show m.1 + D.z (locEnd (sch I e)) ((permEnd (sch I e)).apply c) =
        l.1 + T D e c (numSteps k ℓ) ↔ _
      rw [hm]
      exact add_left_inj _
  | coord => rfl
  | sum => rfl
  | track => rfl
  | coef => rfl

/-- The translation preserves adjacency between valid names whose classes satisfy the
consistency conditions. -/
lemma adjN_phi (D : Desc I) (hD : InitOK D) {x y : VName I} (hx : Valid I x) (hy : Valid I y)
    (hmsx : ∀ e c, x.1 = .link e c → MS D e c) (hmsy : ∀ e c, y.1 = .link e c → MS D e c) :
    adjN I 0 x y ↔ adjN I 1 (phi D x) (phi D y) := by
  unfold adjN
  rw [eff_phi D hD hx, eff_phi D hD hy, phi_fst, phi_fst, hubB_shift D hx.1 hmsx,
    hubB_shift D hy.1 hmsy]

end Lax119563Proofs.Matrix
