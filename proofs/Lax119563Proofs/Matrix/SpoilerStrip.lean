import Lax119563Proofs.Matrix.SpoilerBasics

/-!
# Spoiler's moves through a strip

Sweeping one check row (Lemma "Sweeping one check row"), the whole strip, the link to the end
coordinate class, and the junction moves of ternary schemas. Representatives follow the
columns `g i` of an allowed address; observed values are preserved.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ParitySystems
open Lax119563.ColoredGraphs Lax119563.PebbleGame

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

local notation "G₀" => matrixGraph I 0
local notation "G₁" => matrixGraph I 1

/-! ### The hub relation, slot by slot -/

lemma hubB_upd {e : Fin I.schemas.length} {σ : ℕ} {c : Coord k ℓ} {l m : Lab} {Y : ICls I} :
    hubB I (.upd e σ c) l Y m = true ↔ (Y = trackAt I e c σ ∧ m.1 = l.1) ∨
      (Y = .track e σ c ∧ m.1 = l.2) ∨ (Y = .coef e σ ∧ m.1 = l.1 + l.2) := by
  simp [hubB, or_assoc]

lemma hubB_junc {e : Fin I.schemas.length} {c : Coord k ℓ} {l m : Lab} {Y : ICls I} :
    hubB I (.junc e c) l Y m = true ↔
      (Y = .coord (locU (sch I e)) ((permU (sch I e)).apply c) ∧ m.1 = l.1) ∨
      (Y = .coord (locV (sch I e)) ((permV (sch I e)).apply c) ∧ m.1 = l.2) ∨
      (Y = .sum e c ∧ m.1 = l.1 + l.2) := by
  simp [hubB, or_assoc]

lemma hubB_link {e : Fin I.schemas.length} {c : Coord k ℓ} {l m : Lab} {Y : ICls I} :
    hubB I (.link e c) l Y m = true ↔
      (Y = trackAt I e c (numSteps k ℓ) ∧ m.1 = l.1) ∨ (Y = endCls I e c ∧ m.1 = l.1) := by
  simp [hubB]

/-! ### Distinct classes -/

lemma trackAt_cases (e : Fin I.schemas.length) (c : Coord k ℓ) (σ : ℕ) :
    trackAt I e c σ = startCls I e c ∨ ∃ σ' < σ, trackAt I e c σ = .track e σ' c := by
  unfold trackAt
  split
  · exact Or.inl rfl
  · next σ' h => exact Or.inr ⟨σ', (prevStep_some h).1, rfl⟩

lemma startCls_cases (e : Fin I.schemas.length) (c : Coord k ℓ) :
    startCls I e c = .sum e c ∨
      startCls I e c = .coord (locU (sch I e)) ((permU (sch I e)).apply c) := by
  unfold startCls; split <;> simp

lemma trackAt_ne_track (e : Fin I.schemas.length) (c : Coord k ℓ) (σ : ℕ) :
    trackAt I e c σ ≠ .track e σ c := by
  rcases trackAt_cases e c σ with h | ⟨σ', hσ', h⟩ <;> rw [h]
  · rcases startCls_cases e c with h' | h' <;> rw [h'] <;> simp
  · simp; omega

lemma trackAt_ne_coef (e : Fin I.schemas.length) (c : Coord k ℓ) (σ σ' : ℕ) :
    trackAt I e c σ ≠ .coef e σ' := by
  rcases trackAt_cases e c σ with h | ⟨σ'', -, h⟩ <;> rw [h]
  · rcases startCls_cases e c with h' | h' <;> rw [h'] <;> simp
  · simp

lemma locU_ne_locEnd (e : Fin I.schemas.length) : locU (sch I e) ≠ locEnd (sch I e) := by
  have h := sch_wf I e
  revert h
  cases sch I e <;> simp [Schema.WellFormed, locU, locEnd] <;> tauto

lemma locU_ne_locV (e : Fin I.schemas.length) (ht : isTern (sch I e) = true) :
    locU (sch I e) ≠ locV (sch I e) := by
  have h := sch_wf I e
  revert h ht
  cases sch I e <;> simp [Schema.WellFormed, locU, locV, isTern]
  tauto

lemma trackAt_ne_endCls (e : Fin I.schemas.length) (c : Coord k ℓ) (σ : ℕ) :
    trackAt I e c σ ≠ endCls I e c := by
  rcases trackAt_cases e c σ with h | ⟨σ', -, h⟩ <;> rw [h]
  · rcases startCls_cases e c with h' | h' <;> rw [h']
    · simp [endCls]
    · simp only [endCls, ne_eq, Cls.coord.injEq, not_and]
      exact fun h => absurd h (locU_ne_locEnd e)
  · simp [endCls]

/-! ### Valid classes -/

variable (e : Fin I.schemas.length)

lemma valid_startCls {c : Coord k ℓ} (hc : c ∈ dom I e) : ClsValid I (startCls I e c) := by
  unfold startCls
  split
  · next h => exact ⟨h, hc⟩
  · obtain ⟨i, h1, h2⟩ := exists_arg_U (sch I e)
    show (permU (sch I e)).apply c ∈ I.domain (locU (sch I e))
    rw [← h1, ← h2]
    exact argPerm_mem (sch_wf I e) hc i

lemma valid_endCls {c : Coord k ℓ} (hc : c ∈ dom I e) : ClsValid I (endCls I e c) := by
  obtain ⟨i, h1, h2⟩ := exists_arg_End (sch I e)
  show (permEnd (sch I e)).apply c ∈ I.domain (locEnd (sch I e))
  rw [← h1, ← h2]
  exact argPerm_mem (sch_wf I e) hc i

lemma valid_coordU {c : Coord k ℓ} (hc : c ∈ dom I e) :
    ClsValid I (.coord (locU (sch I e)) ((permU (sch I e)).apply c)) := by
  obtain ⟨i, h1, h2⟩ := exists_arg_U (sch I e)
  show (permU (sch I e)).apply c ∈ I.domain (locU (sch I e))
  rw [← h1, ← h2]
  exact argPerm_mem (sch_wf I e) hc i

lemma valid_coordV {c : Coord k ℓ} (hc : c ∈ dom I e) :
    ClsValid I (.coord (locV (sch I e)) ((permV (sch I e)).apply c)) := by
  obtain ⟨i, h1, h2⟩ := exists_arg_V (sch I e)
  show (permV (sch I e)).apply c ∈ I.domain (locV (sch I e))
  rw [← h1, ← h2]
  exact argPerm_mem (sch_wf I e) hc i

lemma valid_trackAt {c : Coord k ℓ} (hc : c ∈ dom I e) {σ : ℕ} (hσ : σ ≤ numSteps k ℓ) :
    ClsValid I (trackAt I e c σ) := by
  unfold trackAt
  split
  · exact valid_startCls e hc
  · next σ' h =>
    obtain ⟨h1, h2, -⟩ := prevStep_some h
    exact ⟨by omega, hc, h2⟩

/-! ### Sweeping one check row -/

/-- The steps whose row is nonzero on the domain of `e`. -/
def hit (σ : ℕ) : ℕ := if ∃ c ∈ dom I e, ent σ c ≠ 0 then 1 else 0

variable {e}

/-- Columns of an allowed address. -/
structure Cols (e : Fin I.schemas.length) (g : Fin k → Coord k ℓ) : Prop where
  addr : ∃ a, IsAddress a ∧ supp a ⊆ dom I e ∧ Finset.univ.image g = supp a
  inj : Function.Injective g

lemma Cols.mem {g : Fin k → Coord k ℓ} (h : Cols e g) (i : Fin k) : g i ∈ dom I e := by
  obtain ⟨a, -, hs, himg⟩ := h.addr
  exact hs (himg ▸ Finset.mem_image_of_mem g (Finset.mem_univ i))

lemma Cols.sum_ent (hk : 2 ≤ k) {g : Fin k → Coord k ℓ} (h : Cols e g) (σ : ℕ) :
    ∑ i, ent σ (g i) = 0 := by
  obtain ⟨a, ha, -, himg⟩ := h.addr
  rw [← Finset.sum_image (f := fun c => ent σ c) fun x _ y _ hxy => h.inj hxy, himg, supp,
    Finset.sum_image fun x _ y _ hxy => congrArg Prod.fst hxy]
  exact sum_ent_supp hk ha σ

lemma Holds.congr_cls {S : St I} {cls cls' : Fin k → ICls I} {lab : Fin k → Lab}
    (h : Holds S cls lab) (hc : ∀ i, cls i = cls' i) : Holds S cls' lab := by
  rwa [show cls = cls' from funext hc] at h

/-- The representatives in the support of the row of step `σ`. -/
def rowList (g : Fin k → Coord k ℓ) (σ : ℕ) : List (Fin k) :=
  (List.finRange k).filter fun i => ent σ (g i) ≠ 0

lemma mem_rowList {g : Fin k → Coord k ℓ} {σ : ℕ} {i : Fin k} :
    i ∈ rowList g σ ↔ ent σ (g i) ≠ 0 := by
  simp [rowList]

lemma nodup_rowList (g : Fin k → Coord k ℓ) (σ : ℕ) : (rowList g σ).Nodup :=
  (List.nodup_finRange k).filter _

lemma length_rowList_le (g : Fin k → Coord k ℓ) (σ : ℕ) : (rowList g σ).length ≤ k :=
  (List.length_filter_le _ _).trans (by simp)

/-- **Sweeping one check row**, forwards (`dir = true`) or backwards. -/
lemma sweep (hk : 2 ≤ k) {g : Fin k → Coord k ℓ} (hg : Cols e g) {σ : ℕ}
    (hσ : σ < numSteps k ℓ) (dir : Bool) {S : St I} {lab : Fin k → Lab}
    (hH : Holds S (fun i => trackAt I e (g i) (if dir then σ else σ + 1)) lab)
    (hPI : IsPartialIso G₀ G₁ S) :
    Forces ((4 * k + 1) * hit e σ) S fun S' => ∃ lab' : Fin k → Lab,
      Holds S' (fun i => trackAt I e (g i) (if dir then σ + 1 else σ)) lab' ∧
      ∑ i, (lab' i).1 = ∑ i, (lab i).1 ∧ IsPartialIso G₀ G₁ S' := by
  classical
  set T := rowList g σ
  have hstay : ∀ i, i ∉ T → trackAt I e (g i) (σ + 1) = trackAt I e (g i) σ := by
    intro i hi
    rw [trackAt_succ, if_neg (by rwa [mem_rowList] at hi)]
  have hmove : ∀ i, i ∈ T → trackAt I e (g i) (σ + 1) = .track e σ (g i) := by
    intro i hi
    rw [trackAt_succ, if_pos (mem_rowList.mp hi)]
  by_cases hT : T = []
  · refine Forces.mono (Nat.zero_le _) (Forces.ret ⟨lab, hH.congr_cls fun i => ?_, rfl, hPI⟩)
    have := hstay i (by rw [hT]; simp)
    cases dir <;> simp [this]
  obtain ⟨i₀, hi₀⟩ := List.exists_mem_of_ne_nil T hT
  have hhit : hit e σ = 1 := by
    simp only [hit]
    rw [if_pos ⟨g i₀, hg.mem i₀, mem_rowList.mp hi₀⟩]
  rw [hhit, mul_one]
  have hvalU : ∀ i ∈ T, ClsValid I (.upd e σ (g i)) := fun i hi =>
    ⟨hσ, hg.mem i, mem_rowList.mp hi⟩
  have hvalC : ClsValid I (.coef e σ : ICls I) := ⟨hσ, g i₀, hg.mem i₀, mem_rowList.mp hi₀⟩
  set old := fun i => trackAt I e (g i) (if dir then σ else σ + 1)
  have hold_ne_upd : ∀ i, i ∈ T → hubB I (.upd e σ (g i)) (0, 0) (old i) (0, 0) = true := by
    intro i hi
    rw [hubB_upd]
    cases dir
    · refine Or.inr (Or.inl ⟨?_, rfl⟩)
      simp only [old, Bool.false_eq_true, if_false, hmove i hi]
    · exact Or.inl ⟨by simp [old], rfl⟩
  -- the label of the update recorded in the old track
  let Rin : Fin k → Lab → Lab → Prop := fun _ l l' => (if dir then l'.1 else l'.2) = l.1
  have hA := forces_replaceAll T (nodup_rowList g σ) hH hPI (fun i => .upd e σ (g i)) hvalU Rin
    fun S1 i q hi hHi hs hPI1 => by
      have := (forced_hub hPI1 hHi (hvalU i hi) hs rfl).mp (hold_ne_upd i hi)
      rw [hubB_upd] at this
      cases dir
      · simp only [old, Bool.false_eq_true, if_false, hmove i hi] at this
        simp only [Rin, Bool.false_eq_true, if_false]
        rcases this with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
        · exact absurd h.symm (trackAt_ne_track e (g i) σ)
        · exact h.symm
        · exact absurd h (by simp)
      · simp only [old, if_true] at this
        simp only [Rin, if_true]
        rcases this with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · exact h.symm
        · exact absurd h (trackAt_ne_track e (g i) σ)
        · exact absurd h (trackAt_ne_coef e (g i) σ σ)
  have hTl : T.length ≤ k := length_rowList_le g σ
  refine Forces.mono (show 2 * T.length + (1 + 2 * T.length) ≤ 4 * k + 1 by omega) (hA.bind fun S1 ⟨lab1, hR1, hN1, hH1, hPI1⟩ => ?_)
  -- check the coefficient
  refine (forces_spare S1 (.coef e σ) hvalC).bind fun S2 ⟨η', hS2, hPI2⟩ => ?_
  set η := (eff I 1 (nm η')).1
  have hH2 : Holds S2 (fun i => if i ∈ T then .upd e σ (g i) else old i) lab1 := by
    rw [hS2]; exact hH1.update_spare _
  have hη : ∀ i ∈ T, η = (lab1 i).1 + (lab1 i).2 := by
    intro i hi
    have hHi := hH2 i
    simp only [if_pos hi] at hHi
    have := (forced_nonhub hPI2 hHi hvalC (q := η') (by rw [hS2]; exact Function.update_self ..)
      rfl).mp
      (by rw [hubB_upd]; exact Or.inr (Or.inr ⟨rfl, by simp⟩))
    rw [hubB_upd] at this
    rcases this with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h.symm (trackAt_ne_coef e (g i) σ σ)
    · exact absurd h (by simp)
    · exact h
  -- move to the new tracks
  set new := fun i => trackAt I e (g i) (if dir then σ + 1 else σ)
  have hvalN : ∀ i ∈ T, ClsValid I (new i) := fun i _ => by
    simp only [new]
    exact valid_trackAt e (hg.mem i) (by split <;> omega)
  let Rout : Fin k → Lab → Lab → Prop := fun _ l l' => l'.1 = if dir then l.2 else l.1
  have hC := forces_replaceAll T (nodup_rowList g σ) hH2 hPI2 new hvalN Rout
    fun S3 i q hi hHi hs hPI3 => by
      simp only [if_pos hi] at hHi
      have := (forced_nonhub hPI3 hHi (hvalN i hi) hs rfl).mp (by
        rw [hubB_upd]
        cases dir
        · exact Or.inl ⟨by simp [new], rfl⟩
        · exact Or.inr (Or.inl ⟨by simp [new, hmove i hi], rfl⟩))
      rw [hubB_upd] at this
      cases dir
      · simp only [new, Bool.false_eq_true, if_false] at this
        simp only [Rout, Bool.false_eq_true, if_false]
        rcases this with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · exact h
        · exact absurd h (trackAt_ne_track e (g i) σ)
        · exact absurd h (trackAt_ne_coef e (g i) σ σ)
      · simp only [new, if_true, hmove i hi] at this
        simp only [Rout, if_true]
        rcases this with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
        · exact absurd h.symm (trackAt_ne_track e (g i) σ)
        · exact h
        · exact absurd h (by simp)
  refine hC.weaken fun S3 ⟨lab3, hR3, hN3, hH3, hPI3⟩ => ⟨lab3, hH3.congr_cls fun i => ?_, ?_, hPI3⟩
  · by_cases hi : i ∈ T
    · simp [hi, new]
    · simp only [hi, if_false, old, new]
      cases dir <;> simp [hstay i hi]
  · -- the observed value is preserved
    have hlab : ∀ i, (lab3 i).1 = (lab i).1 + ent σ (g i) * η := by
      intro i
      by_cases hi : i ∈ T
      · have h1 := hR1 i hi
        have h3 := hR3 i hi
        have h2 := hη i hi
        rw [ent_eq_one (mem_rowList.mp hi), one_mul]
        simp only [Rin, Rout] at h1 h3
        cases dir
        · simp only [Bool.false_eq_true, if_false] at h1 h3
          rw [h3, h2, ← h1]
          ring_nf; rw [show (2 : ZMod 2) = 0 from rfl]; ring
        · simp only [if_true] at h1 h3
          rw [h3, h2, ← h1]
          ring_nf; rw [show (2 : ZMod 2) = 0 from rfl]; ring
      · rw [hN3 i hi, hN1 i hi]
        have : ent σ (g i) = 0 := by
          by_contra h; exact hi (mem_rowList.mpr h)
        rw [this, zero_mul, add_zero]
    simp_rw [hlab]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hg.sum_ent hk, zero_mul, add_zero]

end Lax119563Proofs.Matrix
