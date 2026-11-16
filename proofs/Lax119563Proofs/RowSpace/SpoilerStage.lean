import Lax119563Proofs.RowSpace.SpoilerBasics

/-!
# Sweeping stages and junctions

Lemma "Sweeping one stage": the representatives on the track classes of the columns of an
allowed address at index `n` move to index `n + 1` (or back), preserving the observed value,
in `4k + 1` rounds. The mask of the stage, checked with the spare pebble, lies in the row space
of `B_e` and is hence orthogonal to the address. Sweeping the whole strip, and the junction
moves of ternary schemas.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ParitySystems
open Lax119563.ColoredGraphs Lax119563.PebbleGame
open Lax119563Proofs.Matrix

namespace Lax119563Proofs.RowSpace

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

local notation "G₀" => rsGraph I 0
local notation "G₁" => rsGraph I 1

/-! ### Classes -/

section classes

variable (e : Fin I.schemas.length)

lemma startCls_mem {c : Coord k ℓ} (hc : c ∈ dom I e) : startCls I e c ∈ classes I := by
  unfold startCls
  split
  · next h => exact mem_classes_sum.mpr ⟨h, hc⟩
  · exact mem_classes_coord.mpr (valid_coordU e hc)

lemma endCls_mem {c : Coord k ℓ} (hc : c ∈ dom I e) : endCls I e c ∈ classes I :=
  mem_classes_coord.mpr (valid_endCls e hc)

lemma coordU_mem {c : Coord k ℓ} (hc : c ∈ dom I e) : coordU e c ∈ classes I :=
  mem_classes_coord.mpr (valid_coordU e hc)

lemma coordV_mem {c : Coord k ℓ} (hc : c ∈ dom I e) : coordV e c ∈ classes I :=
  mem_classes_coord.mpr (valid_coordV e hc)

lemma trackCls_mem {c : Coord k ℓ} (hc : c ∈ dom I e) {n : ℕ} (hn : n ≤ k + 2) :
    trackCls I e c n ∈ classes I := by
  unfold trackCls
  split_ifs with h0 h1
  · exact startCls_mem e hc
  · exact endCls_mem e hc
  · exact mem_classes_track.mpr ⟨⟨by omega, by omega⟩, hc⟩

lemma trackCls_injective (c : Coord k ℓ) : Function.Injective (trackCls I e c) := by
  intro n m h
  have hU := locU_ne_locEnd e
  have hs : startCls I e c ≠ Cls.coord (locEnd (sch I e)) ((permEnd (sch I e)).apply c) :=
    fun h' => by
      rcases startCls_cases e c with h'' | h'' <;> rw [h''] at h' <;> simp at h'
      exact hU h'.1
  unfold trackCls endCls at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 <;> first
    | omega
    | exact h
    | exact absurd h hs
    | exact absurd h.symm hs
    | (rcases startCls_cases e c with h' | h' <;> rw [h'] at h <;> simp at h)
    | (simp at h; done)
    | (simp at h; omega)

lemma trackCls_ne_coef (c : Coord k ℓ) (n h : ℕ) : trackCls I e c n ≠ .coef e h := by
  unfold trackCls
  split_ifs
  · rcases startCls_cases e c with h' | h' <;> rw [h'] <;> simp
  · simp [endCls]
  · simp

lemma hubR_upd_succ {n : ℕ} {c : Coord k ℓ} {l m : RLab k ℓ} {Y : ICls I} :
    hubR I (.upd e (n + 1) c) l Y m ↔ (Y = trackCls I e c n ∧ m.1 = l.1) ∨
      (Y = trackCls I e c (n + 1) ∧ m.1 = l.2.1) ∨ (Y = .coef e (n + 1) ∧ m.2.2 c = l.1 + l.2.1) := by
  simp only [hubR, Nat.add_sub_cancel]

lemma hubR_junc' {c : Coord k ℓ} {l m : RLab k ℓ} {Y : ICls I} :
    hubR I (.junc e c) l Y m ↔ (Y = coordU e c ∧ m.1 = l.1) ∨
      (Y = coordV e c ∧ m.1 = l.2.1) ∨ (Y = .sum e c ∧ m.1 = l.1 + l.2.1) :=
  Iff.rfl

end classes

/-- The label of a mask vertex of `G₁` lies in the row space. -/
lemma coef_label {e : Fin I.schemas.length} {h : ℕ} {q : Fin (rsGraph I 1).n}
    (hq : (vx q).1 = .coef e h) : (vx q).2.2.2 ∈ maskSet I e := by
  have := vx_mem q
  rw [mem_verts, mem_names] at this
  obtain ⟨-, hl⟩ := this
  simp only [hq, labs, off, smul_zero, add_zero, Finset.mem_image] at hl
  obtain ⟨x, hx, hxe⟩ := hl
  rw [← hxe]
  exact hx

variable {e : Fin I.schemas.length} {g : Fin k → Coord k ℓ}

/-- Masks in the row space are orthogonal to the columns of an allowed address. -/
lemma cols_sum_mask (hk : 0 < k) (hg : Cols e g) {x : Vec k ℓ} (hx : x ∈ maskSet I e) :
    ∑ i, x (g i) = 0 := by
  obtain ⟨a, ha, hs, himg⟩ := hg.addr
  rw [← Finset.sum_image (f := x) fun i _ j _ h => hg.inj h, himg, ← dot_ind_eq_sum_supp]
  exact maskSet_dot hx hk ha hs

lemma z2_aux1 (x y : ZMod 2) : x = y + (y + x) := by
  rw [← add_assoc, zmod2_self_add, zero_add]

lemma z2_aux2 (x y : ZMod 2) : x = y + (x + y) := by
  rw [add_comm x y]; exact z2_aux1 x y

/-! ### Sweeping one stage -/

/-- **Sweeping one stage**, forwards (`dir = true`, from index `n` to `n + 1`) or backwards. -/
lemma rsweep (hk : 0 < k) (hg : Cols e g) {n : ℕ} (hn : n < k + 2) (dir : Bool) {S : RSt I}
    {lab : Fin k → RLab k ℓ}
    (hH : RHolds S (fun i => trackCls I e (g i) (if dir then n else n + 1)) lab)
    (hPI : IsPartialIso G₀ G₁ S) :
    Forces (4 * k + 1) S fun S' => ∃ lab' : Fin k → RLab k ℓ,
      RHolds S' (fun i => trackCls I e (g i) (if dir then n + 1 else n)) lab' ∧
      ∑ i, (lab' i).1 = ∑ i, (lab i).1 ∧ IsPartialIso G₀ G₁ S' := by
  classical
  have hvU : ∀ i, (Cls.upd e (n + 1) (g i) : ICls I) ∈ classes I := fun i =>
    mem_classes_upd.mpr ⟨⟨by omega, by omega⟩, hg.mem i⟩
  have hvC : (Cls.coef e (n + 1) : ICls I) ∈ classes I := mem_classes_coef.mpr ⟨by omega, by omega⟩
  have hne : ∀ c, trackCls I e c n ≠ trackCls I e c (n + 1) := fun c h => by
    have := trackCls_injective e c h; omega
  -- the label of the update recorded from the old track
  let Rin : Fin k → RLab k ℓ → RLab k ℓ → Prop := fun _ l l' =>
    (if dir then l'.1 else l'.2.1) = l.1
  refine Forces.mono (show 2 * k + (1 + 2 * k) ≤ 4 * k + 1 by omega)
    ((rforces_replaceEvery hH hPI (fun i => .upd e (n + 1) (g i)) hvU Rin
      fun S1 i q hHi hs hPI1 => ?_).bind fun S1 ⟨lab1, hR1, hH1, hPI1⟩ => ?_)
  · have h0 : hubR I (.upd e (n + 1) (g i)) 0
        (trackCls I e (g i) (if dir then n else n + 1)) 0 := by
      rw [hubR_upd_succ]
      cases dir
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inl ⟨rfl, rfl⟩
    have := (rforced_hub hPI1 hHi (hvU i) hs trivial).mp h0
    rw [hubR_upd_succ] at this
    cases dir
    · simp only [Rin, Bool.false_eq_true, if_false] at this ⊢
      rcases this with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd h.symm (hne _)
      · exact h.symm
      · exact absurd h (trackCls_ne_coef e _ _ _)
    · simp only [Rin, if_true] at this ⊢
      rcases this with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact h.symm
      · exact absurd h (hne _)
      · exact absurd h (trackCls_ne_coef e _ _ _)
  -- check the mask
  refine (rforces_spare S1 (.coef e (n + 1)) hvC).bind fun S2 ⟨η', hS2, hPI2⟩ => ?_
  have hsη : S2 spare = some (rzv (.coef e (n + 1)) hvC, η') := by
    rw [hS2]; exact Function.update_self ..
  have hμ : (vx η').2.2.2 ∈ maskSet I e := by
    refine coef_label (h := n + 1) ?_
    rw [rspare_vx hPI2 hvC hsη]
  have hH2 : RHolds S2 (fun i => .upd e (n + 1) (g i)) lab1 := by
    rw [hS2]; exact hH1.update_spare _
  have hη : ∀ i, (vx η').2.2.2 (g i) = (lab1 i).1 + (lab1 i).2.1 := by
    intro i
    have := (rforced_nonhub hPI2 (hH2 i) hvC hsη trivial).mp
      (by rw [hubR_upd_succ]; exact Or.inr (Or.inr ⟨rfl, by simp⟩))
    rw [hubR_upd_succ] at this
    rcases this with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h.symm (trackCls_ne_coef e _ _ _)
    · exact absurd h.symm (trackCls_ne_coef e _ _ _)
    · exact h
  -- move to the new tracks
  have hvN : ∀ i, trackCls I e (g i) (if dir then n + 1 else n) ∈ classes I := fun i =>
    trackCls_mem e (hg.mem i) (by split <;> omega)
  let Rout : Fin k → RLab k ℓ → RLab k ℓ → Prop := fun _ l l' =>
    l'.1 = if dir then l.2.1 else l.1
  refine (rforces_replaceEvery hH2 hPI2 _ hvN Rout fun S3 i q hHi hs hPI3 => ?_).weaken
    fun S3 ⟨lab3, hR3, hH3, hPI3⟩ => ⟨lab3, hH3, ?_, hPI3⟩
  · have h0 : hubR I (.upd e (n + 1) (g i)) 0
        (trackCls I e (g i) (if dir then n + 1 else n)) 0 := by
      rw [hubR_upd_succ]
      cases dir
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    have := (rforced_nonhub hPI3 hHi (hvN i) hs trivial).mp h0
    rw [hubR_upd_succ] at this
    cases dir
    · simp only [Rout, Bool.false_eq_true, if_false] at this ⊢
      rcases this with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h (hne _)
      · exact absurd h (trackCls_ne_coef e _ _ _)
    · simp only [Rout, if_true] at this ⊢
      rcases this with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd h.symm (hne _)
      · exact h
      · exact absurd h (trackCls_ne_coef e _ _ _)
  · -- the observed value is preserved
    have hlab : ∀ i, (lab3 i).1 = (lab i).1 + (vx η').2.2.2 (g i) := by
      intro i
      have h1 := hR1 i
      have h3 := hR3 i
      rw [hη i]
      cases dir
      · simp only [Rin, Rout, Bool.false_eq_true, if_false] at h1 h3
        rw [h3, ← h1]
        exact z2_aux2 _ _
      · simp only [Rin, Rout, if_true] at h1 h3
        rw [h3, ← h1]
        exact z2_aux1 _ _
    simp_rw [hlab]
    rw [Finset.sum_add_distrib, cols_sum_mask hk hg hμ, add_zero]

/-! ### The strip -/

/-- The cost of sweeping a strip. -/
def stripCostR (k : ℕ) : ℕ := (4 * k + 1) * (k + 2)

/-- Sweeping the strip forwards, from index `0` to index `n`. -/
lemma rstrip_fwd (hk : 0 < k) (hg : Cols e g) :
    ∀ n ≤ k + 2, ∀ (S : RSt I) (lab : Fin k → RLab k ℓ),
      RHolds S (fun i => trackCls I e (g i) 0) lab → IsPartialIso G₀ G₁ S →
      Forces ((4 * k + 1) * n) S fun S' => ∃ lab' : Fin k → RLab k ℓ,
        RHolds S' (fun i => trackCls I e (g i) n) lab' ∧ ∑ i, (lab' i).1 = ∑ i, (lab i).1 ∧
        IsPartialIso G₀ G₁ S'
  | 0, _, S, lab, hH, hPI => Forces.ret ⟨lab, hH, rfl, hPI⟩
  | n + 1, hn, S, lab, hH, hPI => by
    refine Forces.mono (le_of_eq (Nat.mul_succ _ _).symm)
      ((rstrip_fwd hk hg n (by omega) S lab hH hPI).bind fun S1 ⟨lab1, hH1, hs1, hPI1⟩ => ?_)
    refine (rsweep hk hg (n := n) (by omega) true (hH1.congr_cls fun i => by simp) hPI1).weaken
      fun S2 ⟨lab2, hH2, hs2, hPI2⟩ => ⟨lab2, hH2.congr_cls fun i => by simp, hs2.trans hs1, hPI2⟩

/-- Sweeping the strip backwards, from index `n` to index `0`. -/
lemma rstrip_bwd (hk : 0 < k) (hg : Cols e g) :
    ∀ n ≤ k + 2, ∀ (S : RSt I) (lab : Fin k → RLab k ℓ),
      RHolds S (fun i => trackCls I e (g i) n) lab → IsPartialIso G₀ G₁ S →
      Forces ((4 * k + 1) * n) S fun S' => ∃ lab' : Fin k → RLab k ℓ,
        RHolds S' (fun i => trackCls I e (g i) 0) lab' ∧ ∑ i, (lab' i).1 = ∑ i, (lab i).1 ∧
        IsPartialIso G₀ G₁ S'
  | 0, _, S, lab, hH, hPI => Forces.ret ⟨lab, hH, rfl, hPI⟩
  | n + 1, hn, S, lab, hH, hPI => by
    have h1 := rsweep hk hg (n := n) (by omega) false (hH.congr_cls fun i => by simp) hPI
    refine Forces.mono (le_of_eq (by rw [Nat.mul_succ, Nat.add_comm]))
      (h1.bind fun S1 ⟨lab1, hH1, hs1, hPI1⟩ =>
        (rstrip_bwd hk hg n (by omega) S1 lab1 (hH1.congr_cls fun i => by simp) hPI1).weaken
          fun S2 ⟨lab2, hH2, hs2, hPI2⟩ => ⟨lab2, hH2, hs2.trans hs1, hPI2⟩)

/-- Sweeping the whole strip forwards. -/
lemma rstrip_full_fwd (hk : 0 < k) (hg : Cols e g) {S : RSt I} {lab : Fin k → RLab k ℓ}
    (hH : RHolds S (fun i => startCls I e (g i)) lab) (hPI : IsPartialIso G₀ G₁ S) :
    Forces (stripCostR k) S fun S' => ∃ lab' : Fin k → RLab k ℓ,
      RHolds S' (fun i => endCls I e (g i)) lab' ∧ ∑ i, (lab' i).1 = ∑ i, (lab i).1 ∧
      IsPartialIso G₀ G₁ S' :=
  (rstrip_fwd hk hg (k + 2) le_rfl S lab (hH.congr_cls fun _ => (trackCls_zero I e _).symm)
    hPI).weaken fun _ ⟨lab', h1, h2, h3⟩ =>
      ⟨lab', h1.congr_cls fun _ => trackCls_last I e _, h2, h3⟩

/-- Sweeping the whole strip backwards. -/
lemma rstrip_full_bwd (hk : 0 < k) (hg : Cols e g) {S : RSt I} {lab : Fin k → RLab k ℓ}
    (hH : RHolds S (fun i => endCls I e (g i)) lab) (hPI : IsPartialIso G₀ G₁ S) :
    Forces (stripCostR k) S fun S' => ∃ lab' : Fin k → RLab k ℓ,
      RHolds S' (fun i => startCls I e (g i)) lab' ∧ ∑ i, (lab' i).1 = ∑ i, (lab i).1 ∧
      IsPartialIso G₀ G₁ S' :=
  (rstrip_bwd hk hg (k + 2) le_rfl S lab (hH.congr_cls fun _ => (trackCls_last I e _).symm)
    hPI).weaken fun _ ⟨lab', h1, h2, h3⟩ =>
      ⟨lab', h1.congr_cls fun _ => trackCls_zero I e _, h2, h3⟩

/-! ### Junctions -/

/-- A junction move: all representatives move between a junction class and one of its
neighbor classes. -/
lemma rjunc_move (ht : isTern (sch I e) = true) (hg : Cols e g) (toJunc : Bool)
    (nb : Fin k → ICls I) (hnb : ∀ i, nb i = coordU e (g i) ∨ nb i = coordV e (g i) ∨
      nb i = .sum e (g i))
    (hval : ∀ i, nb i ∈ classes I) (f : RLab k ℓ → ZMod 2)
    (hf : ∀ i l, (nb i = coordU e (g i) → f l = l.1) ∧ (nb i = coordV e (g i) → f l = l.2.1) ∧
      (nb i = .sum e (g i) → f l = l.1 + l.2.1))
    {S : RSt I} {lab : Fin k → RLab k ℓ}
    (hH : RHolds S (fun i => if toJunc then nb i else .junc e (g i)) lab)
    (hPI : IsPartialIso G₀ G₁ S) :
    Forces (2 * k) S fun S' => ∃ lab' : Fin k → RLab k ℓ,
      (∀ i, if toJunc then f (lab' i) = (lab i).1 else (lab' i).1 = f (lab i)) ∧
      RHolds S' (fun i => if toJunc then .junc e (g i) else nb i) lab' ∧
      IsPartialIso G₀ G₁ S' := by
  have hvJ : ∀ i, (Cls.junc e (g i) : ICls I) ∈ classes I := fun i =>
    mem_classes_junc.mpr ⟨ht, hg.mem i⟩
  have hvN : ∀ i, (if toJunc then Cls.junc e (g i) else nb i) ∈ classes I := by
    intro i; split
    · exact hvJ i
    · exact hval i
  have hz : ∀ i, hubR I (.junc e (g i)) 0 (nb i) 0 := by
    intro i
    rw [hubR_junc']
    rcases hnb i with h | h | h
    · exact Or.inl ⟨h, rfl⟩
    · exact Or.inr (Or.inl ⟨h, rfl⟩)
    · exact Or.inr (Or.inr ⟨h, by simp⟩)
  have hrel : ∀ i l m, hubR I (.junc e (g i)) l (nb i) m → m.1 = f l := by
    intro i l m h
    rw [hubR_junc'] at h
    have hU := (hf i l).1
    have hV := (hf i l).2.1
    have hS := (hf i l).2.2
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2, hU h1]
    · rw [h2, hV h1]
    · rw [h2, hS h1]
  refine (rforces_replaceEvery hH hPI _ hvN
    (fun _ l l' => if toJunc then f l' = l.1 else l'.1 = f l) fun S1 i q hHi hs hPI1 => ?_).weaken
    fun S' ⟨lab', h1, h2, h3⟩ => ⟨lab', h1, h2, h3⟩
  cases toJunc
  · simp only [Bool.false_eq_true, if_false] at hHi hs ⊢
    exact hrel i _ _ ((rforced_nonhub hPI1 hHi (hval i) hs trivial).mp (hz i))
  · simp only [if_true] at hHi hs ⊢
    exact (hrel i _ _ ((rforced_hub hPI1 hHi (hvJ i) hs trivial).mp (hz i))).symm

end Lax119563Proofs.RowSpace
