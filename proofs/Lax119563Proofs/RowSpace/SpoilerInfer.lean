import Lax119563Proofs.RowSpace.SpoilerStage

/-!
# Following an inference

Lemma "Following an inference": from a discrepant conclusion of an equation of schema `e`,
Spoiler moves through the gadget of `e` (sweeping its `k + 2` stages and using the junctions
of a ternary schema) to a discrepant premise, in `O(k²)` rounds.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ParitySystems
open Lax119563.ColoredGraphs Lax119563.PebbleGame
open Lax119563Proofs.Matrix

namespace Lax119563Proofs.RowSpace

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

local notation "G₀" => rsGraph I 0
local notation "G₁" => rsGraph I 1

/-! ### Discrepant facts -/

/-- The representatives hold the coordinate classes of the variable `X`, and the observed
value disagrees with `b`. -/
def RDisc (S : RSt I) (X : Fin I.numLocations × (Fin k → BlockCoord ℓ)) (b : ZMod 2) : Prop :=
  ∃ g : Fin k → Coord k ℓ, Function.Injective g ∧ Finset.univ.image g = supp X.2 ∧
    ∃ lab : Fin k → RLab k ℓ, RHolds S (fun i => .coord X.1 (g i)) lab ∧
      ∑ i, (lab i).1 = b + 1 ∧ IsPartialIso G₀ G₁ S

variable {e : Fin I.schemas.length} {a : Fin k → BlockCoord ℓ}

lemma rdisc_to_cols (ha : IsAddress a) (hsa : supp a ⊆ dom I e) {S : RSt I}
    {x : Fin I.numLocations} {P : BlockPerm k ℓ} {b : ZMod 2} (hD : RDisc S (x, P.act a) b) :
    ∃ g, Cols e g ∧ Finset.univ.image g = supp a ∧ ∃ lab : Fin k → RLab k ℓ,
      RHolds S (fun i => .coord x (P.apply (g i))) lab ∧ ∑ i, (lab i).1 = b + 1 ∧
      IsPartialIso G₀ G₁ S := by
  obtain ⟨g, hg, himg, lab, hH, hs, hPI⟩ := hD
  simp only at himg hH
  have himg' : Finset.univ.image (fun i => (bpEquiv P).symm (g i)) = supp a := by
    ext c
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      have : g i ∈ supp (P.act a) := himg ▸ Finset.mem_image_of_mem g (Finset.mem_univ i)
      rw [supp_act] at this
      obtain ⟨c, hc, hci⟩ := Finset.mem_image.mp this
      rw [← hci, ← bpEquiv_apply, Equiv.symm_apply_apply]
      exact hc
    · intro hc
      have : P.apply c ∈ supp (P.act a) := by
        rw [supp_act]; exact Finset.mem_image_of_mem _ hc
      rw [← himg] at this
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp this
      exact ⟨i, by rw [hi, ← bpEquiv_apply, Equiv.symm_apply_apply]⟩
  refine ⟨fun i => (bpEquiv P).symm (g i), ⟨⟨a, ha, hsa, himg'⟩,
    fun i j h => hg ((bpEquiv P).symm.injective h)⟩, himg', lab, hH.congr_cls fun i => ?_, hs,
    hPI⟩
  simp [← bpEquiv_apply]

lemma cols_to_rdisc {S : RSt I} {x : Fin I.numLocations} {P : BlockPerm k ℓ} {b : ZMod 2}
    {g : Fin k → Coord k ℓ} (hg : Function.Injective g) (himg : Finset.univ.image g = supp a)
    {lab : Fin k → RLab k ℓ} (hH : RHolds S (fun i => .coord x (P.apply (g i))) lab)
    (hs : ∑ i, (lab i).1 = b + 1) (hPI : IsPartialIso G₀ G₁ S) : RDisc S (x, P.act a) b := by
  refine ⟨fun i => P.apply (g i), fun i j h => hg (bp_apply_injective P h), ?_, lab, hH, hs, hPI⟩
  simp only
  rw [supp_act, ← himg, Finset.image_image]
  rfl

/-! ### Through a gadget -/

variable {g : Fin k → Coord k ℓ}

/-- The cost of one inference step. -/
def stepCostR (k : ℕ) : ℕ := stripCostR k + 4 * k

lemma rbin_fwd (hk : 0 < k) (ht : isTern (sch I e) = false) (hg : Cols e g) {S : RSt I}
    {lab : Fin k → RLab k ℓ} (hH : RHolds S (fun i => coordU e (g i)) lab)
    (hPI : IsPartialIso G₀ G₁ S) :
    Forces (stepCostR k) S fun S' => ∃ lab' : Fin k → RLab k ℓ,
      RHolds S' (fun i => endCls I e (g i)) lab' ∧ ∑ i, (lab' i).1 = ∑ i, (lab i).1 ∧
      IsPartialIso G₀ G₁ S' :=
  Forces.mono (by unfold stepCostR; omega)
    (rstrip_full_fwd hk hg (hH.congr_cls fun i => (startCls_bin ht _).symm) hPI)

lemma rbin_bwd (hk : 0 < k) (ht : isTern (sch I e) = false) (hg : Cols e g) {S : RSt I}
    {lab : Fin k → RLab k ℓ} (hH : RHolds S (fun i => endCls I e (g i)) lab)
    (hPI : IsPartialIso G₀ G₁ S) :
    Forces (stepCostR k) S fun S' => ∃ lab' : Fin k → RLab k ℓ,
      RHolds S' (fun i => coordU e (g i)) lab' ∧ ∑ i, (lab' i).1 = ∑ i, (lab i).1 ∧
      IsPartialIso G₀ G₁ S' :=
  Forces.mono (by unfold stepCostR; omega) ((rstrip_full_bwd hk hg hH hPI).weaken
    fun _ ⟨lab', h1, h2, h3⟩ => ⟨lab', h1.congr_cls fun _ => startCls_bin ht _, h2, h3⟩)

/-- From the end coordinate classes of a ternary schema to a discrepant first or second
argument. -/
lemma rtern_end (hk : 0 < k) (ht : isTern (sch I e) = true) (hg : Cols e g) (b₁ : ZMod 2)
    {S : RSt I} {lab : Fin k → RLab k ℓ} (hH : RHolds S (fun i => endCls I e (g i)) lab)
    (hPI : IsPartialIso G₀ G₁ S) :
    Forces (stepCostR k) S fun S' =>
      (∃ lab' : Fin k → RLab k ℓ, RHolds S' (fun i => coordU e (g i)) lab' ∧
        ∑ i, (lab' i).1 = b₁ + 1 ∧ IsPartialIso G₀ G₁ S') ∨
      (∃ lab' : Fin k → RLab k ℓ, RHolds S' (fun i => coordV e (g i)) lab' ∧
        ∑ i, (lab' i).1 = ∑ i, (lab i).1 + b₁ ∧ IsPartialIso G₀ G₁ S') := by
  have hvS : ∀ i, (Cls.sum e (g i) : ICls I) ∈ classes I := fun i =>
    mem_classes_sum.mpr ⟨ht, hg.mem i⟩
  refine Forces.mono (show stripCostR k + (2 * k + 2 * k) ≤ stepCostR k by
    unfold stepCostR; omega) ((rstrip_full_bwd hk hg hH hPI).bind
      fun S2 ⟨lab2, hH2, hs2, hPI2⟩ => ?_)
  have hH2' : RHolds S2 (fun i => if true then Cls.sum e (g i) else Cls.junc e (g i)) lab2 :=
    hH2.congr_cls fun i => by rw [startCls_tern ht]; rfl
  refine (rjunc_move ht hg true _ (fun i => Or.inr (Or.inr rfl)) hvS (fun l => l.1 + l.2.1)
    (fun i l => ⟨fun h => by simp [coordU] at h, fun h => by simp [coordV] at h, fun _ => rfl⟩)
    hH2' hPI2).bind fun S3 ⟨lab3, hR3, hH3, hPI3⟩ => ?_
  simp only [if_true] at hR3 hH3
  by_cases hb : ∑ i, (lab3 i).1 = b₁
  · refine (rjunc_move ht hg false (fun i => coordV e (g i)) (fun i => Or.inr (Or.inl rfl))
      (fun i => coordV_mem e (hg.mem i)) (fun l => l.2.1)
      (fun i l => ⟨fun h => absurd h.symm (coordU_ne_coordV ht _), fun _ => rfl,
        fun h => by simp [coordV] at h⟩) (hH3.congr_cls fun i => by simp) hPI3).weaken
      fun S4 ⟨lab4, hR4, hH4, hPI4⟩ => Or.inr ⟨lab4, hH4.congr_cls fun i => by simp, ?_, hPI4⟩
    simp only [Bool.false_eq_true, if_false] at hR4
    have : ∀ i, (lab4 i).1 = (lab3 i).1 + (lab2 i).1 := by
      intro i
      rw [hR4 i, ← hR3 i]
      ring_nf; rw [show (2 : ZMod 2) = 0 from rfl]; ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, hb, hs2, add_comm]
  · refine (rjunc_move ht hg false (fun i => coordU e (g i)) (fun i => Or.inl rfl)
      (fun i => coordU_mem e (hg.mem i)) (fun l => l.1)
      (fun i l => ⟨fun _ => rfl, fun h => absurd h (coordU_ne_coordV ht _),
        fun h => by simp [coordU] at h⟩) (hH3.congr_cls fun i => by simp) hPI3).weaken
      fun S4 ⟨lab4, hR4, hH4, hPI4⟩ => Or.inl ⟨lab4, hH4.congr_cls fun i => by simp, ?_, hPI4⟩
    simp only [Bool.false_eq_true, if_false] at hR4
    simp_rw [hR4]
    exact sum_eq_or _ _ hb

/-- From the coordinate classes of an argument next to the junctions (`first = true`: the
first argument, otherwise the second) to the other one or the end of the strip. -/
lemma rtern_side (hk : 0 < k) (ht : isTern (sch I e) = true) (hg : Cols e g) (first : Bool)
    (b' : ZMod 2) {S : RSt I} {lab : Fin k → RLab k ℓ}
    (hH : RHolds S (fun i => if first then coordU e (g i) else coordV e (g i)) lab)
    (hPI : IsPartialIso G₀ G₁ S) :
    Forces (stepCostR k) S fun S' =>
      (∃ lab' : Fin k → RLab k ℓ,
        RHolds S' (fun i => if first then coordV e (g i) else coordU e (g i)) lab' ∧
        ∑ i, (lab' i).1 = b' + 1 ∧ IsPartialIso G₀ G₁ S') ∨
      (∃ lab' : Fin k → RLab k ℓ, RHolds S' (fun i => endCls I e (g i)) lab' ∧
        ∑ i, (lab' i).1 = ∑ i, (lab i).1 + b' ∧ IsPartialIso G₀ G₁ S') := by
  have hvS : ∀ i, (Cls.sum e (g i) : ICls I) ∈ classes I := fun i =>
    mem_classes_sum.mpr ⟨ht, hg.mem i⟩
  let own : RLab k ℓ → ZMod 2 := fun l => if first then l.1 else l.2.1
  let oth : RLab k ℓ → ZMod 2 := fun l => if first then l.2.1 else l.1
  have hvOwn : ∀ i, (if first then coordU e (g i) else coordV e (g i)) ∈ classes I :=
    fun i => by
      split
      · exact coordU_mem e (hg.mem i)
      · exact coordV_mem e (hg.mem i)
  have hvOth : ∀ i, (if first then coordV e (g i) else coordU e (g i)) ∈ classes I :=
    fun i => by
      split
      · exact coordV_mem e (hg.mem i)
      · exact coordU_mem e (hg.mem i)
  have hH' : RHolds S (fun i => if true then (if first then coordU e (g i) else coordV e (g i))
      else Cls.junc e (g i)) lab := hH.congr_cls fun i => rfl
  refine Forces.mono (show 2 * k + (2 * k + stripCostR k) ≤ stepCostR k by
    unfold stepCostR; omega) ((rjunc_move ht hg true _ (fun i => by cases first <;> simp)
    hvOwn own (fun i l => by
      cases first <;> refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
        simp only [if_true, Bool.false_eq_true, if_false, own] at h ⊢ <;>
        first | rfl | exact absurd h (coordU_ne_coordV ht _) |
          exact absurd h.symm (coordU_ne_coordV ht _) | simp [coordU, coordV] at h) hH' hPI).bind
    fun S1 ⟨lab1, hR1, hH1, hPI1⟩ => ?_)
  simp only [if_true] at hR1 hH1
  by_cases hb : ∑ i, oth (lab1 i) = b'
  · -- go to the sums and sweep the strip
    refine (rjunc_move ht hg false (fun i => Cls.sum e (g i)) (fun i => Or.inr (Or.inr rfl)) hvS
      (fun l => l.1 + l.2.1) (fun i l => ⟨fun h => by simp [coordU] at h,
        fun h => by simp [coordV] at h, fun _ => rfl⟩) (hH1.congr_cls fun i => by simp)
      hPI1).bind fun S2 ⟨lab2, hR2, hH2, hPI2⟩ => ?_
    simp only [Bool.false_eq_true, if_false] at hR2 hH2
    have hsum2 : ∑ i, (lab2 i).1 = ∑ i, (lab i).1 + b' := by
      have : ∀ i, (lab2 i).1 = own (lab1 i) + oth (lab1 i) := by
        intro i; rw [hR2 i]; simp only [own, oth]; cases first <;> simp [add_comm]
      simp_rw [this]
      rw [Finset.sum_add_distrib, hb]
      congr 1
      exact Finset.sum_congr rfl fun i _ => hR1 i
    refine (rstrip_full_fwd hk hg (hH2.congr_cls fun i => (startCls_tern ht _).symm)
      hPI2).weaken fun S3 ⟨lab3, hH3, hs3, hPI3⟩ =>
        Or.inr ⟨lab3, hH3, by rw [hs3, hsum2], hPI3⟩
  · -- go to the other argument
    refine Forces.mono (Nat.le_add_right _ _) ((rjunc_move ht hg false
      (fun i => if first then coordV e (g i) else coordU e (g i))
      (fun i => by cases first <;> simp) hvOth oth (fun i l => by
      cases first <;> refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
        simp only [if_true, Bool.false_eq_true, if_false, oth] at h ⊢ <;>
        first | rfl | exact absurd h (coordU_ne_coordV ht _) |
          exact absurd h.symm (coordU_ne_coordV ht _) | simp [coordU, coordV] at h)
      (hH1.congr_cls fun i => by simp) hPI1).weaken fun S2 ⟨lab2, hR2, hH2, hPI2⟩ =>
        Or.inl ⟨lab2, hH2.congr_cls fun i => by simp, ?_, hPI2⟩)
    simp only [Bool.false_eq_true, if_false] at hR2
    simp_rw [hR2]
    exact sum_eq_or _ _ hb

/-- **Following an inference.** From a discrepant conclusion of an equation of schema `e`,
Spoiler reaches a discrepant premise. -/
lemma rstep (hk : 0 < k) {S : RSt I} {e : Fin I.schemas.length} {a : Fin k → BlockCoord ℓ}
    (ha : IsAddress a) (hsa : supp a ⊆ dom I e) (i₀ : Fin (arity (sch I e)))
    (bf : Fin (arity (sch I e)) → ZMod 2)
    (hD : RDisc S (argVar I e i₀ a) (∑ j ∈ Finset.univ.erase i₀, bf j)) :
    Forces (stepCostR k) S fun S' => ∃ i, i ≠ i₀ ∧ RDisc S' (argVar I e i a) (bf i) := by
  rcases arg_cases (sch I e) i₀ bf with
    ⟨ht, hl, hp, i, hi, hl', hp', hsum⟩ | ⟨ht, hl, hp, i, hi, hl', hp', hsum⟩ |
    ⟨ht, hl, hp, i, i', hi, hi', hl1, hp1, hl2, hp2, hsum⟩ |
    ⟨ht, hl, hp, i, i', hi, hi', hl1, hp1, hl2, hp2, hsum⟩ |
    ⟨ht, hl, hp, i, i', hi, hi', hl1, hp1, hl2, hp2, hsum⟩
  · rw [argVar_eq hl hp] at hD
    obtain ⟨g, hg, himg, lab, hH, hs, hPI⟩ := rdisc_to_cols ha hsa hD
    refine (rbin_fwd hk ht hg hH hPI).weaken fun S' ⟨lab', hH', hs', hPI'⟩ => ⟨i, hi, ?_⟩
    rw [argVar_eq hl' hp']
    exact cols_to_rdisc hg.inj himg hH' (by rw [hs', hs, hsum]) hPI'
  · rw [argVar_eq hl hp] at hD
    obtain ⟨g, hg, himg, lab, hH, hs, hPI⟩ := rdisc_to_cols ha hsa hD
    refine (rbin_bwd hk ht hg hH hPI).weaken fun S' ⟨lab', hH', hs', hPI'⟩ => ⟨i, hi, ?_⟩
    rw [argVar_eq hl' hp']
    exact cols_to_rdisc hg.inj himg hH' (by rw [hs', hs, hsum]) hPI'
  · rw [argVar_eq hl hp] at hD
    obtain ⟨g, hg, himg, lab, hH, hs, hPI⟩ := rdisc_to_cols ha hsa hD
    refine (rtern_end hk ht hg (bf i) hH hPI).weaken fun S' h => ?_
    rcases h with ⟨lab', hH', hs', hPI'⟩ | ⟨lab', hH', hs', hPI'⟩
    · refine ⟨i, hi, ?_⟩
      rw [argVar_eq hl1 hp1]
      exact cols_to_rdisc hg.inj himg hH' hs' hPI'
    · refine ⟨i', hi', ?_⟩
      rw [argVar_eq hl2 hp2]
      refine cols_to_rdisc hg.inj himg hH' ?_ hPI'
      rw [hs', hs, hsum]; ring_nf; rw [show (2 : ZMod 2) = 0 from rfl]; ring
  · rw [argVar_eq hl hp] at hD
    obtain ⟨g, hg, himg, lab, hH, hs, hPI⟩ := rdisc_to_cols ha hsa hD
    refine (rtern_side hk ht hg true (bf i) (hH.congr_cls fun j => by simp [coordU]) hPI).weaken
      fun S' h => ?_
    rcases h with ⟨lab', hH', hs', hPI'⟩ | ⟨lab', hH', hs', hPI'⟩
    · refine ⟨i, hi, ?_⟩
      rw [argVar_eq hl1 hp1]
      exact cols_to_rdisc hg.inj himg (hH'.congr_cls fun j => by simp [coordV]) hs' hPI'
    · refine ⟨i', hi', ?_⟩
      rw [argVar_eq hl2 hp2]
      refine cols_to_rdisc hg.inj himg hH' ?_ hPI'
      rw [hs', hs, hsum]; ring_nf; rw [show (2 : ZMod 2) = 0 from rfl]; ring
  · rw [argVar_eq hl hp] at hD
    obtain ⟨g, hg, himg, lab, hH, hs, hPI⟩ := rdisc_to_cols ha hsa hD
    refine (rtern_side hk ht hg false (bf i) (hH.congr_cls fun j => by simp [coordV]) hPI).weaken
      fun S' h => ?_
    rcases h with ⟨lab', hH', hs', hPI'⟩ | ⟨lab', hH', hs', hPI'⟩
    · refine ⟨i, hi, ?_⟩
      rw [argVar_eq hl1 hp1]
      exact cols_to_rdisc hg.inj himg (hH'.congr_cls fun j => by simp [coordU]) hs' hPI'
    · refine ⟨i', hi', ?_⟩
      rw [argVar_eq hl2 hp2]
      refine cols_to_rdisc hg.inj himg hH' ?_ hPI'
      rw [hs', hs, hsum]; ring_nf; rw [show (2 : ZMod 2) = 0 from rfl]; ring

end Lax119563Proofs.RowSpace
