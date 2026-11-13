import Lax119563Proofs.Matrix.SpoilerGadget

/-!
# Spoiler's strategy

Spoiler follows a derivation of a conflict backwards: from a discrepant fact he moves
through the gadget of an inference to a discrepant premise derived in an earlier round, until
an initial fact contradicts the singleton coordinate classes (Theorem "Matrix compiler",
part (I)).
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ParitySystems
open Lax119563.ColoredGraphs Lax119563.PebbleGame

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

local notation "G₀" => matrixGraph I 0
local notation "G₁" => matrixGraph I 1

/-! ### Discrepant facts -/

/-- The representatives hold the coordinate classes of the variable `X`, and the observed
value disagrees with `b`. -/
def Disc (S : St I) (X : Fin I.numLocations × (Fin k → BlockCoord ℓ)) (b : ZMod 2) : Prop :=
  ∃ g : Fin k → Coord k ℓ, Function.Injective g ∧ Finset.univ.image g = supp X.2 ∧
    ∃ lab : Fin k → Lab, Holds S (fun i => .coord X.1 (g i)) lab ∧ ∑ i, (lab i).1 = b + 1 ∧
      IsPartialIso G₀ G₁ S

variable {e : Fin I.schemas.length} {a : Fin k → BlockCoord ℓ}

lemma disc_to_cols (ha : IsAddress a) (hsa : supp a ⊆ dom I e) {S : St I}
    {x : Fin I.numLocations} {P : BlockPerm k ℓ} {b : ZMod 2} (hD : Disc S (x, P.act a) b) :
    ∃ g, Cols e g ∧ Finset.univ.image g = supp a ∧ ∃ lab : Fin k → Lab,
      Holds S (fun i => .coord x (P.apply (g i))) lab ∧ ∑ i, (lab i).1 = b + 1 ∧
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

lemma cols_to_disc {S : St I} {x : Fin I.numLocations} {P : BlockPerm k ℓ} {b : ZMod 2}
    {g : Fin k → Coord k ℓ} (hg : Function.Injective g) (himg : Finset.univ.image g = supp a)
    {lab : Fin k → Lab} (hH : Holds S (fun i => .coord x (P.apply (g i))) lab)
    (hs : ∑ i, (lab i).1 = b + 1) (hPI : IsPartialIso G₀ G₁ S) : Disc S (x, P.act a) b := by
  refine ⟨fun i => P.apply (g i), fun i j h => hg (bp_apply_injective P h), ?_, lab, hH, hs, hPI⟩
  simp only
  rw [supp_act, ← himg, Finset.image_image]
  rfl

/-! ### Following an inference through a gadget -/

variable {g : Fin k → Coord k ℓ}

lemma trackAt_zero (e : Fin I.schemas.length) (c : Coord k ℓ) : trackAt I e c 0 = startCls I e c :=
  rfl

lemma startCls_bin (ht : isTern (sch I e) = false) (c : Coord k ℓ) :
    startCls I e c = coordU e c := by
  simp [startCls, ht, coordU]

lemma startCls_tern (ht : isTern (sch I e) = true) (c : Coord k ℓ) :
    startCls I e c = .sum e c := by
  simp [startCls, ht]

/-- The cost of one inference step. -/
def stepCost (e : Fin I.schemas.length) : ℕ := stripCost e + 8 * k

lemma bin_fwd (hk : 2 ≤ k) (ht : isTern (sch I e) = false) (hg : Cols e g) {S : St I}
    {lab : Fin k → Lab} (hH : Holds S (fun i => coordU e (g i)) lab)
    (hPI : IsPartialIso G₀ G₁ S) :
    Forces (stepCost e) S fun S' => ∃ lab' : Fin k → Lab,
      Holds S' (fun i => endCls I e (g i)) lab' ∧ ∑ i, (lab' i).1 = ∑ i, (lab i).1 ∧
      IsPartialIso G₀ G₁ S' := by
  have h1 := strip_fwd hk hg (numSteps k ℓ) le_rfl S lab
    (hH.congr_cls fun i => by rw [trackAt_zero, startCls_bin ht]) hPI
  refine Forces.mono (by unfold stepCost stripCost; omega) (h1.bind fun S1 ⟨lab1, hH1, hs1, hPI1⟩ =>
    (link_fwd hg hH1 hPI1).weaken fun S2 ⟨lab2, hH2, hs2, hPI2⟩ =>
      ⟨lab2, hH2, hs2.trans hs1, hPI2⟩)

lemma bin_bwd (hk : 2 ≤ k) (ht : isTern (sch I e) = false) (hg : Cols e g) {S : St I}
    {lab : Fin k → Lab} (hH : Holds S (fun i => endCls I e (g i)) lab)
    (hPI : IsPartialIso G₀ G₁ S) :
    Forces (stepCost e) S fun S' => ∃ lab' : Fin k → Lab,
      Holds S' (fun i => coordU e (g i)) lab' ∧ ∑ i, (lab' i).1 = ∑ i, (lab i).1 ∧
      IsPartialIso G₀ G₁ S' := by
  refine Forces.mono (by unfold stepCost stripCost; omega) ((link_bwd hg hH hPI).bind
    fun S1 ⟨lab1, hH1, hs1, hPI1⟩ => (strip_bwd hk hg (numSteps k ℓ) le_rfl S1 lab1 hH1
      hPI1).weaken fun S2 ⟨lab2, hH2, hs2, hPI2⟩ => ⟨lab2, hH2.congr_cls fun i => by
        rw [trackAt_zero, startCls_bin ht], hs2.trans hs1, hPI2⟩)

lemma sum_eq_or (x b : ZMod 2) (h : x ≠ b) : x = b + 1 := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;> rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
    first | exact absurd rfl h | rfl

/-- From the end coordinate classes of a ternary schema to a discrepant first or second
argument. -/
lemma tern_end (hk : 2 ≤ k) (ht : isTern (sch I e) = true) (hg : Cols e g) (b₁ : ZMod 2)
    {S : St I} {lab : Fin k → Lab} (hH : Holds S (fun i => endCls I e (g i)) lab)
    (hPI : IsPartialIso G₀ G₁ S) :
    Forces (stepCost e) S fun S' =>
      (∃ lab' : Fin k → Lab, Holds S' (fun i => coordU e (g i)) lab' ∧
        ∑ i, (lab' i).1 = b₁ + 1 ∧ IsPartialIso G₀ G₁ S') ∨
      (∃ lab' : Fin k → Lab, Holds S' (fun i => coordV e (g i)) lab' ∧
        ∑ i, (lab' i).1 = ∑ i, (lab i).1 + b₁ ∧ IsPartialIso G₀ G₁ S') := by
  have hvS : ∀ i, ClsValid I (Cls.sum e (g i) : ICls I) := fun i => ⟨ht, hg.mem i⟩
  refine Forces.mono (show 2 * k + 2 * k + (stripCost e + (2 * k + 2 * k)) ≤ stepCost e by
    unfold stepCost; omega) ((link_bwd hg hH hPI).bind fun S1 ⟨lab1, hH1, hs1, hPI1⟩ =>
      (strip_bwd hk hg (numSteps k ℓ) le_rfl S1 lab1 hH1 hPI1).bind
        fun S2 ⟨lab2, hH2, hs2, hPI2⟩ => ?_)
  have hH2' : Holds S2 (fun i => if true then Cls.sum e (g i) else Cls.junc e (g i)) lab2 :=
    hH2.congr_cls fun i => by rw [trackAt_zero, startCls_tern ht]; rfl
  refine (junc_move ht hg true _ (fun i => Or.inr (Or.inr rfl)) hvS (fun l => l.1 + l.2)
    (fun i l => ⟨fun h => by simp [coordU] at h, fun h => by simp [coordV] at h, fun _ => rfl⟩)
    hH2' hPI2).bind fun S3 ⟨lab3, hR3, hH3, hPI3⟩ => ?_
  simp only [if_true] at hR3 hH3
  by_cases hb : ∑ i, (lab3 i).1 = b₁
  · refine (junc_move ht hg false (fun i => coordV e (g i)) (fun i => Or.inr (Or.inl rfl))
      (fun i => valid_coordV e (hg.mem i)) (fun l => l.2)
      (fun i l => ⟨fun h => absurd h.symm (coordU_ne_coordV ht _), fun _ => rfl,
        fun h => by simp [coordV] at h⟩) (hH3.congr_cls fun i => by simp) hPI3).weaken
      fun S4 ⟨lab4, hR4, hH4, hPI4⟩ => Or.inr ⟨lab4, hH4.congr_cls fun i => by simp, ?_, hPI4⟩
    simp only [Bool.false_eq_true, if_false] at hR4
    have : ∀ i, (lab4 i).1 = (lab3 i).1 + (lab2 i).1 := by
      intro i
      rw [hR4 i, ← hR3 i]
      ring_nf; rw [show (2 : ZMod 2) = 0 from rfl]; ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, hb, hs2, hs1, add_comm]
  · refine (junc_move ht hg false (fun i => coordU e (g i)) (fun i => Or.inl rfl)
      (fun i => valid_coordU e (hg.mem i)) (fun l => l.1)
      (fun i l => ⟨fun _ => rfl, fun h => absurd h (coordU_ne_coordV ht _),
        fun h => by simp [coordU] at h⟩) (hH3.congr_cls fun i => by simp) hPI3).weaken
      fun S4 ⟨lab4, hR4, hH4, hPI4⟩ => Or.inl ⟨lab4, hH4.congr_cls fun i => by simp, ?_, hPI4⟩
    simp only [Bool.false_eq_true, if_false] at hR4
    simp_rw [hR4]
    exact sum_eq_or _ _ hb

/-- From the coordinate classes of an argument next to the junctions (`first = true`: the
first argument, otherwise the second) to the other one or the end of the strip. -/
lemma tern_side (hk : 2 ≤ k) (ht : isTern (sch I e) = true) (hg : Cols e g) (first : Bool)
    (b' : ZMod 2) {S : St I} {lab : Fin k → Lab}
    (hH : Holds S (fun i => if first then coordU e (g i) else coordV e (g i)) lab)
    (hPI : IsPartialIso G₀ G₁ S) :
    Forces (stepCost e) S fun S' =>
      (∃ lab' : Fin k → Lab, Holds S' (fun i => if first then coordV e (g i) else coordU e (g i))
        lab' ∧ ∑ i, (lab' i).1 = b' + 1 ∧ IsPartialIso G₀ G₁ S') ∨
      (∃ lab' : Fin k → Lab, Holds S' (fun i => endCls I e (g i)) lab' ∧
        ∑ i, (lab' i).1 = ∑ i, (lab i).1 + b' ∧ IsPartialIso G₀ G₁ S') := by
  have hvS : ∀ i, ClsValid I (Cls.sum e (g i) : ICls I) := fun i => ⟨ht, hg.mem i⟩
  -- the neighbor classes in the order (held, other)
  let own : Lab → ZMod 2 := fun l => if first then l.1 else l.2
  let oth : Lab → ZMod 2 := fun l => if first then l.2 else l.1
  have hvOwn : ∀ i, ClsValid I (if first then coordU e (g i) else coordV e (g i)) := fun i => by
    split
    · exact valid_coordU e (hg.mem i)
    · exact valid_coordV e (hg.mem i)
  have hvOth : ∀ i, ClsValid I (if first then coordV e (g i) else coordU e (g i)) := fun i => by
    split
    · exact valid_coordV e (hg.mem i)
    · exact valid_coordU e (hg.mem i)
  have hH' : Holds S (fun i => if true then (if first then coordU e (g i) else coordV e (g i))
      else Cls.junc e (g i)) lab := hH.congr_cls fun i => rfl
  refine Forces.mono (show 2 * k + (2 * k + (stripCost e + (2 * k + 2 * k))) ≤ stepCost e by
    unfold stepCost; omega) ((junc_move ht hg true _ (fun i => by cases first <;> simp)
    hvOwn own (fun i l => by
      cases first <;> refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
        simp only [if_true, Bool.false_eq_true, if_false, own] at h ⊢ <;>
        first | rfl | exact absurd h (coordU_ne_coordV ht _) |
          exact absurd h.symm (coordU_ne_coordV ht _) | simp [coordU, coordV] at h) hH' hPI).bind
    fun S1 ⟨lab1, hR1, hH1, hPI1⟩ => ?_)
  simp only [if_true] at hR1 hH1
  by_cases hb : ∑ i, oth (lab1 i) = b'
  · -- go to the sums and sweep the strip
    refine (junc_move ht hg false (fun i => Cls.sum e (g i)) (fun i => Or.inr (Or.inr rfl)) hvS
      (fun l => l.1 + l.2) (fun i l => ⟨fun h => by simp [coordU] at h,
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
    refine (strip_fwd hk hg (numSteps k ℓ) le_rfl S2 lab2
      (hH2.congr_cls fun i => by rw [trackAt_zero, startCls_tern ht]) hPI2).bind
      fun S3 ⟨lab3, hH3, hs3, hPI3⟩ => (link_fwd hg hH3 hPI3).weaken
        fun S4 ⟨lab4, hH4, hs4, hPI4⟩ => Or.inr ⟨lab4, hH4, by rw [hs4, hs3, hsum2], hPI4⟩
  · -- go to the other argument
    refine Forces.mono (Nat.le_add_right _ _) ((junc_move ht hg false
      (fun i => if first then coordV e (g i) else coordU e (g i))
      (fun i => by cases first <;> simp) hvOth oth (fun i l => by
      cases first <;> refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
        simp only [if_true, Bool.false_eq_true, if_false, oth] at h ⊢ <;>
        first | rfl | exact absurd h (coordU_ne_coordV ht _) |
          exact absurd h.symm (coordU_ne_coordV ht _) | simp [coordU, coordV] at h) (hH1.congr_cls fun i => by simp)
      hPI1).weaken fun S2 ⟨lab2, hR2, hH2, hPI2⟩ =>
        Or.inl ⟨lab2, hH2.congr_cls fun i => by simp, ?_, hPI2⟩)
    simp only [Bool.false_eq_true, if_false] at hR2
    simp_rw [hR2]
    exact sum_eq_or _ _ hb

end Lax119563Proofs.Matrix
