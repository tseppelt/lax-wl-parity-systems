import Lax119563Proofs.RowSpace.Extension

/-!
# The size of the row-space graphs

Each graph has `(names I).card` vertices, at most `10 S` with the size parameter
`S = ∑_v |𝔠_v| + (k + 1) ∑_e (|𝔠_e| + 2^{rank B_e})`.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.RowSpaceCompiler
open Lax119563Proofs.Matrix

namespace Lax119563Proofs.RowSpace

variable {k ℓ : ℕ}

/-- The mask set of `e` has at most `2 ^ rank B_e` elements: restricting to `𝔠_e` embeds it
into the column space of `B_eᵀ`. -/
lemma card_maskSet_le (I : ImplicitParitySystem k ℓ) (e : Fin I.schemas.length) :
    (maskSet I e).card ≤ 2 ^ rowRank (sch I e) := by
  classical
  set B : Matrix (Row k ℓ) (sch I e).domain (ZMod 2) :=
    Matrix.of fun row (c : (sch I e).domain) => checkMatrix k ℓ row c with hB
  let W := LinearMap.range B.transpose.mulVecLin
  have hW : Nat.card W = 2 ^ rowRank (sch I e) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    show _ = 2 ^ B.rank
    rw [← Matrix.rank_transpose]; rfl
  let g : maskSet I e → W := fun x => ⟨fun c => x.1 c.1, by
    obtain ⟨μ, -, hμ⟩ := Finset.mem_image.mp x.2
    refine ⟨μ, ?_⟩
    funext c
    rw [← hμ]
    simp [Matrix.vecMul, dotProduct, maskOf, dom, c.2, hB]⟩
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    funext c
    by_cases hc : c ∈ dom I e
    · exact congrFun (congrArg Subtype.val h) ⟨c, hc⟩
    · rw [maskSet_supp I x.2 hc, maskSet_supp I y.2 hc]
  rw [← hW, ← Nat.card_eq_finsetCard]
  exact Nat.card_le_card_of_injective g hg

lemma sum_union_le' {α : Type*} [DecidableEq α] (s t : Finset α) (f : α → ℕ) :
    ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  rw [← Finset.sum_union_inter]; exact Nat.le_add_right _ _

lemma sum_biUnion_le' {ι α : Type*} [DecidableEq ι] [DecidableEq α] (s : Finset ι)
    (t : ι → Finset α) (f : α → ℕ) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    exact (sum_union_le' _ _ f).trans (Nat.add_le_add_left ih _)

lemma sum_image_le' {β α : Type*} [DecidableEq β] [DecidableEq α] (s : Finset β) (g : β → α)
    (f : α → ℕ) : ∑ x ∈ s.image g, f x ≤ ∑ y ∈ s, f (g y) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.image_insert, Finset.sum_insert hi]
    refine le_trans ?_ (Nat.add_le_add_left ih _)
    by_cases h : g i ∈ s.image g
    · rw [Finset.insert_eq_of_mem h]; exact Nat.le_add_left _ _
    · rw [Finset.sum_insert h]

lemma card_lab1 : (lab1 : Finset (RLab k ℓ)).card ≤ 2 :=
  (Finset.card_insert_le _ _).trans (by simp)

lemma card_lab2 : (lab2 : Finset (RLab k ℓ)).card ≤ 4 := by
  refine (Finset.card_insert_le _ _).trans ?_
  refine Nat.add_le_add_right ((Finset.card_insert_le _ _).trans ?_) 1
  refine Nat.add_le_add_right ((Finset.card_insert_le _ _).trans ?_) 1
  simp

lemma sum_coordClasses_le (I : ImplicitParitySystem k ℓ) :
    ∑ X ∈ coordClasses I, (labs I X).card ≤ 2 * ∑ v, (I.domain v).card := by
  classical
  unfold coordClasses
  refine (sum_biUnion_le' _ _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => (sum_image_le' _ _ _).trans ?_
  rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun c _ => ?_
  simp only [labs]
  split
  · simp
  · exact card_lab1

lemma sum_schemaClasses_le (hk : 3 ≤ k) (I : ImplicitParitySystem k ℓ)
    (e : Fin I.schemas.length) :
    ∑ X ∈ schemaClasses I e, (labs I X).card ≤
      10 * (k + 1) * ((sch I e).domain.card + 2 ^ rowRank (sch I e)) := by
  classical
  have hm := card_maskSet_le I e
  set d := (dom I e).card with hd
  have h1 : ∑ X ∈ (if isTern (sch I e) then (dom I e).image (Cls.sum e) ∪
      (dom I e).image (Cls.junc e) else ∅), (labs I X).card ≤ 6 * d := by
    split
    · refine (sum_union_le' _ _ _).trans ?_
      refine (Nat.add_le_add (sum_image_le' _ _ _) (sum_image_le' _ _ _)).trans ?_
      have a : ∑ c ∈ dom I e, (labs I (Cls.sum e c)).card ≤ ∑ c ∈ dom I e, 2 :=
        Finset.sum_le_sum fun _ _ => card_lab1
      have b : ∑ c ∈ dom I e, (labs I (Cls.junc e c)).card ≤ ∑ c ∈ dom I e, 4 :=
        Finset.sum_le_sum fun _ _ => card_lab2
      simp only [Finset.sum_const, smul_eq_mul] at a b
      omega
    · simp
  have h2 : ∑ X ∈ (Finset.Icc 1 (k + 1) ×ˢ dom I e).image (fun p => Cls.track e p.1 p.2),
      (labs I X).card ≤ 2 * ((k + 1) * d) := by
    refine (sum_image_le' _ _ _).trans ?_
    refine (Finset.sum_le_sum fun _ _ => card_lab1).trans ?_
    simp [Finset.card_product, hd, mul_comm]
  have h3 : ∑ X ∈ (Finset.Icc 1 (k + 2) ×ˢ dom I e).image (fun p => Cls.upd e p.1 p.2),
      (labs I X).card ≤ 4 * ((k + 2) * d) := by
    refine (sum_image_le' _ _ _).trans ?_
    refine (Finset.sum_le_sum fun _ _ => card_lab2).trans ?_
    simp [Finset.card_product, hd, mul_comm]
  have h4 : ∑ X ∈ (Finset.Icc 1 (k + 2)).image (Cls.coef e), (labs I X).card ≤
      (k + 2) * 2 ^ rowRank (sch I e) := by
    refine (sum_image_le' _ _ _).trans ?_
    refine (Finset.sum_le_sum fun _ _ => (Finset.card_image_le).trans hm).trans ?_
    simp
  unfold schemaClasses
  refine (sum_union_le' _ _ _).trans ?_
  refine (Nat.add_le_add (sum_union_le' _ _ _) (sum_union_le' _ _ _)).trans ?_
  have : (sch I e).domain.card = d := rfl
  rw [this]
  nlinarith

lemma sum_get_eq' {α : Type*} (l : List α) (f : α → ℕ) :
    ∑ e : Fin l.length, f (l.get e) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Fin.sum_univ_succ]

/-- **Size bound.** -/
theorem card_names_le (hk : 3 ≤ k) (I : ImplicitParitySystem k ℓ) :
    (names I).card ≤ 10 * Lax119563.RowSpaceCompiler.rowSpaceSize I := by
  classical
  have h0 : (names I).card ≤ ∑ X ∈ classes I, (labs I X).card := by
    unfold names
    exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_image_le)
  have h1 : ∑ X ∈ classes I, (labs I X).card ≤ 2 * ∑ v, (I.domain v).card +
      ∑ e, 10 * (k + 1) * ((sch I e).domain.card + 2 ^ rowRank (sch I e)) := by
    unfold classes
    refine (sum_union_le' _ _ _).trans (Nat.add_le_add (sum_coordClasses_le I) ?_)
    exact (sum_biUnion_le' _ _ _).trans
      (Finset.sum_le_sum fun e _ => sum_schemaClasses_le hk I e)
  have h2 : ∑ e : Fin I.schemas.length, 10 * (k + 1) *
      ((sch I e).domain.card + 2 ^ rowRank (sch I e)) =
      10 * (k + 1) * (I.schemas.map fun e => e.domain.card + 2 ^ rowRank e).sum := by
    rw [← Finset.mul_sum]
    congr 1
    exact sum_get_eq' I.schemas (fun e => e.domain.card + 2 ^ rowRank e)
  unfold Lax119563.RowSpaceCompiler.rowSpaceSize
  rw [h2] at h1
  rw [mul_add, ← mul_assoc]; omega

end Lax119563Proofs.RowSpace
