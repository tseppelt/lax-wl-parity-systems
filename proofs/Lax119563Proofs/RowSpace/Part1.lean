import Lax119563.ColoredHomomorphisms
import Lax119563.ContradictionTrees
import Lax119563.RowSpaceCompiler
import Lax119563Proofs.Matrix.Part1
import Lax228581.Treewidth
import Mathlib

/-! ### Formerly `Lax119563Proofs.Matrix.SpoilerMain` -/

section Matrix_SpoilerMain

/-!
# Spoiler wins

The walk along a derivation and the resulting bound `O_k(Λ (τ + 1))`.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ParitySystems
open Lax119563.ColoredGraphs Lax119563.PebbleGame

namespace Lax119563Proofs.Matrix

variable {k ℓ w : ℕ}

/-- The roles of the arguments of a schema in its gadget. -/
lemma arg_cases (s : Schema k ℓ w) (i₀ : Fin (arity s)) (bf : Fin (arity s) → ZMod 2) :
    (isTern s = false ∧ argLoc s i₀ = locU s ∧ argPerm s i₀ = permU s ∧
      ∃ i, i ≠ i₀ ∧ argLoc s i = locEnd s ∧ argPerm s i = permEnd s ∧
        ∑ j ∈ Finset.univ.erase i₀, bf j = bf i) ∨
    (isTern s = false ∧ argLoc s i₀ = locEnd s ∧ argPerm s i₀ = permEnd s ∧
      ∃ i, i ≠ i₀ ∧ argLoc s i = locU s ∧ argPerm s i = permU s ∧
        ∑ j ∈ Finset.univ.erase i₀, bf j = bf i) ∨
    (isTern s = true ∧ argLoc s i₀ = locEnd s ∧ argPerm s i₀ = permEnd s ∧
      ∃ i i', i ≠ i₀ ∧ i' ≠ i₀ ∧ argLoc s i = locU s ∧ argPerm s i = permU s ∧
        argLoc s i' = locV s ∧ argPerm s i' = permV s ∧
        ∑ j ∈ Finset.univ.erase i₀, bf j = bf i + bf i') ∨
    (isTern s = true ∧ argLoc s i₀ = locU s ∧ argPerm s i₀ = permU s ∧
      ∃ i i', i ≠ i₀ ∧ i' ≠ i₀ ∧ argLoc s i = locV s ∧ argPerm s i = permV s ∧
        argLoc s i' = locEnd s ∧ argPerm s i' = permEnd s ∧
        ∑ j ∈ Finset.univ.erase i₀, bf j = bf i + bf i') ∨
    (isTern s = true ∧ argLoc s i₀ = locV s ∧ argPerm s i₀ = permV s ∧
      ∃ i i', i ≠ i₀ ∧ i' ≠ i₀ ∧ argLoc s i = locU s ∧ argPerm s i = permU s ∧
        argLoc s i' = locEnd s ∧ argPerm s i' = permEnd s ∧
        ∑ j ∈ Finset.univ.erase i₀, bf j = bf i + bf i') := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  cases s with
  | binary u v D σ τ =>
    fin_cases i₀
    · left
      refine ⟨rfl, rfl, rfl, 1, (by simp), rfl, rfl, ?_⟩
      simp [Fin.sum_univ_two]; try abel
    · right; left
      refine ⟨rfl, rfl, rfl, 0, (by simp), rfl, rfl, ?_⟩
      simp [Fin.sum_univ_two]; try abel
  | ternary u v w' D σ τ π =>
    fin_cases i₀
    · right; right; right; left
      refine ⟨rfl, rfl, rfl, 1, 2, (by simp), (by simp), rfl, rfl, rfl, rfl, ?_⟩
      simp [Fin.sum_univ_three]; try abel
    · right; right; right; right
      refine ⟨rfl, rfl, rfl, 0, 2, (by simp), (by simp), rfl, rfl, rfl, rfl, ?_⟩
      simp [Fin.sum_univ_three]; try abel
    · right; right; left
      refine ⟨rfl, rfl, rfl, 0, 1, (by simp), (by simp), rfl, rfl, rfl, rfl, ?_⟩
      have h2 : (⟨2, by decide⟩ : Fin 3) = 2 := rfl
      simp [Fin.sum_univ_three, h2]

variable {I : ImplicitParitySystem k ℓ}

local notation "G₀" => matrixGraph I 0
local notation "G₁" => matrixGraph I 1

lemma argVar_eq {e : Fin I.schemas.length} {i : Fin (arity (sch I e))}
    {x : Fin I.numLocations} {P : BlockPerm k ℓ} (hx : argLoc (sch I e) i = x)
    (hP : argPerm (sch I e) i = P) (a : Fin k → BlockCoord ℓ) : argVar I e i a = (x, P.act a) := by
  simp [argVar, hx, hP]

/-- **Following an inference.** From a discrepant conclusion of an equation of schema `e`,
Spoiler reaches a discrepant premise. -/
lemma step (hk : 2 ≤ k) {S : St I} {e : Fin I.schemas.length} {a : Fin k → BlockCoord ℓ}
    (ha : IsAddress a) (hsa : supp a ⊆ dom I e) (i₀ : Fin (arity (sch I e)))
    (bf : Fin (arity (sch I e)) → ZMod 2)
    (hD : Disc S (argVar I e i₀ a) (∑ j ∈ Finset.univ.erase i₀, bf j)) :
    Forces (stepCost e) S fun S' => ∃ i, i ≠ i₀ ∧ Disc S' (argVar I e i a) (bf i) := by
  rcases arg_cases (sch I e) i₀ bf with
    ⟨ht, hl, hp, i, hi, hl', hp', hsum⟩ | ⟨ht, hl, hp, i, hi, hl', hp', hsum⟩ |
    ⟨ht, hl, hp, i, i', hi, hi', hl1, hp1, hl2, hp2, hsum⟩ |
    ⟨ht, hl, hp, i, i', hi, hi', hl1, hp1, hl2, hp2, hsum⟩ |
    ⟨ht, hl, hp, i, i', hi, hi', hl1, hp1, hl2, hp2, hsum⟩
  · rw [argVar_eq hl hp] at hD
    obtain ⟨g, hg, himg, lab, hH, hs, hPI⟩ := disc_to_cols ha hsa hD
    refine (bin_fwd hk ht hg hH hPI).weaken fun S' ⟨lab', hH', hs', hPI'⟩ => ⟨i, hi, ?_⟩
    rw [argVar_eq hl' hp']
    exact cols_to_disc hg.inj himg hH' (by rw [hs', hs, hsum]) hPI'
  · rw [argVar_eq hl hp] at hD
    obtain ⟨g, hg, himg, lab, hH, hs, hPI⟩ := disc_to_cols ha hsa hD
    refine (bin_bwd hk ht hg hH hPI).weaken fun S' ⟨lab', hH', hs', hPI'⟩ => ⟨i, hi, ?_⟩
    rw [argVar_eq hl' hp']
    exact cols_to_disc hg.inj himg hH' (by rw [hs', hs, hsum]) hPI'
  · rw [argVar_eq hl hp] at hD
    obtain ⟨g, hg, himg, lab, hH, hs, hPI⟩ := disc_to_cols ha hsa hD
    refine (tern_end hk ht hg (bf i) hH hPI).weaken fun S' h => ?_
    rcases h with ⟨lab', hH', hs', hPI'⟩ | ⟨lab', hH', hs', hPI'⟩
    · refine ⟨i, hi, ?_⟩
      rw [argVar_eq hl1 hp1]
      exact cols_to_disc hg.inj himg hH' hs' hPI'
    · refine ⟨i', hi', ?_⟩
      rw [argVar_eq hl2 hp2]
      refine cols_to_disc hg.inj himg hH' ?_ hPI'
      rw [hs', hs, hsum]; ring_nf; rw [show (2 : ZMod 2) = 0 from rfl]; ring
  · rw [argVar_eq hl hp] at hD
    obtain ⟨g, hg, himg, lab, hH, hs, hPI⟩ := disc_to_cols ha hsa hD
    refine (tern_side hk ht hg true (bf i) (hH.congr_cls fun j => by simp [coordU]) hPI).weaken
      fun S' h => ?_
    rcases h with ⟨lab', hH', hs', hPI'⟩ | ⟨lab', hH', hs', hPI'⟩
    · refine ⟨i, hi, ?_⟩
      rw [argVar_eq hl1 hp1]
      exact cols_to_disc hg.inj himg (hH'.congr_cls fun j => by simp [coordV]) hs' hPI'
    · refine ⟨i', hi', ?_⟩
      rw [argVar_eq hl2 hp2]
      refine cols_to_disc hg.inj himg hH' ?_ hPI'
      rw [hs', hs, hsum]; ring_nf; rw [show (2 : ZMod 2) = 0 from rfl]; ring
  · rw [argVar_eq hl hp] at hD
    obtain ⟨g, hg, himg, lab, hH, hs, hPI⟩ := disc_to_cols ha hsa hD
    refine (tern_side hk ht hg false (bf i) (hH.congr_cls fun j => by simp [coordV]) hPI).weaken
      fun S' h => ?_
    rcases h with ⟨lab', hH', hs', hPI'⟩ | ⟨lab', hH', hs', hPI'⟩
    · refine ⟨i, hi, ?_⟩
      rw [argVar_eq hl1 hp1]
      exact cols_to_disc hg.inj himg (hH'.congr_cls fun j => by simp [coordU]) hs' hPI'
    · refine ⟨i', hi', ?_⟩
      rw [argVar_eq hl2 hp2]
      refine cols_to_disc hg.inj himg hH' ?_ hPI'
      rw [hs', hs, hsum]; ring_nf; rw [show (2 : ZMod 2) = 0 from rfl]; ring

/-- An initial fact cannot be discrepant: the singleton coordinate classes force the
initialized value. -/
lemma not_disc_initial (hk : 0 < k) {S : St I} {X : Fin I.numLocations × (Fin k → BlockCoord ℓ)}
    {b : ZMod 2} (hX : (X, b) ∈ I.toParitySystem.known 0) (hD : Disc S X b) : False := by
  obtain ⟨ι, hι, rfl, ha, hs⟩ := hX
  simp only at hι ha hs
  obtain ⟨g, hg, himg, lab, hH, hsum, -⟩ := hD
  have hlab : ∀ i, (lab i).1 = initSeed I X.1 (g i) := by
    intro i
    obtain ⟨p, q, -, -, h3, h4⟩ := hH i
    have hv := nm_valid q
    have h1 : (nm q).2.1 = 0 := hv.2.2 (by rw [h3]; simp [isSingleton, hι])
    rw [← h4]
    simp only [eff]
    rw [h3, h1]
    simp [initBit]
  simp_rw [hlab] at hsum
  have : ∑ i, initSeed I X.1 (g i) = dot (ind X.2) (initSeed I X.1) := by
    rw [dot_ind_eq_sum_supp, ← himg, Finset.sum_image fun x _ y _ h => hg h]
  rw [this, dot_initSeed hι hk] at hsum
  have h' : b + 1 = b + 0 := by rw [← hsum, add_zero]
  exact one_ne_zero (add_left_cancel h')

/-- **Spoiler's walk.** From a discrepant fact derived in round `ρ`, Spoiler wins within
`C ρ` rounds, where `C` bounds the cost of one inference step. -/
theorem walk (hk : 2 ≤ k) (C : ℕ) (hC : ∀ e, stepCost (I := I) e ≤ C) :
    ∀ (ρ : ℕ) (S : St I) (X : Fin I.numLocations × (Fin k → BlockCoord ℓ)) (b : ZMod 2),
      (X, b) ∈ I.toParitySystem.known ρ → Disc S X b → SWins (C * ρ) S
  | 0, S, X, b, hX, hD => absurd (not_disc_initial (by omega) hX hD) id
  | ρ + 1, S, X, b, hX, hD => by
    rcases known_succ_cases I hX with hX | ⟨e, a, ha, hsa, i₀, rfl, bf, hbf, rfl⟩
    · exact (walk hk C hC ρ S X b hX hD).mono (Nat.mul_le_mul_left _ (Nat.le_succ ρ))
    · have := step hk ha hsa i₀ bf hD (C * ρ) fun S' ⟨i, hi, hD'⟩ =>
        walk hk C hC ρ S' _ _ (hbf i hi) hD'
      exact this.mono (by rw [Nat.mul_succ]; exact Nat.add_le_add_left (hC e) _)

/-! ### The start -/

/-- Placing the representatives on the zero vertices of the classes `cls`. -/
lemma forces_fill (T : List (Fin k)) (hT : T.Nodup) {S : St I} (hPI : IsPartialIso G₀ G₁ S)
    (cls : Fin k → ICls I) (hval : ∀ i, ClsValid I (cls i)) :
    Forces (2 * T.length) S fun S' => (∀ i ∈ T, ∃ l, HoldsAt S' i.castSucc (cls i) l) ∧
      (∀ i, i ∉ T → S' i.castSucc = S i.castSucc) ∧ IsPartialIso G₀ G₁ S' := by
  induction T generalizing S with
  | nil => exact Forces.ret ⟨by simp, fun _ _ => rfl, hPI⟩
  | cons i T ih =>
    obtain ⟨hiT, hT'⟩ := List.nodup_cons.mp hT
    refine Forces.mono (show 2 + 2 * T.length ≤ 2 * (i :: T).length by simp; omega)
      ((forces_replace S i (cls i) (hval i)).bind fun S1 ⟨q, hPI1, hS1, hPI1'⟩ =>
        (ih hT' hPI1').weaken fun S' ⟨h1, h2, h3⟩ => ⟨fun j hj => ?_, fun j hj => ?_, h3⟩)
    · rcases List.mem_cons.mp hj with rfl | hj
      · refine ⟨eff I 1 (nm q), zv (cls j) (hval j), q, ?_, by simp, ?_, rfl⟩
        · rw [h2 j hiT, hS1]; simp
        · exact spare_cls (hY := hval j) hPI1 (Function.update_self ..)
      · exact h1 j hj
    · have hji : j ≠ i := fun h => hj (h ▸ List.mem_cons_self)
      rw [h2 j fun h => hj (List.mem_cons_of_mem _ h), hS1,
        Function.update_of_ne (fun h => hji (Fin.castSucc_injective _ h)),
        Function.update_of_ne (castSucc_ne_spare j)]

/-! ### Counting the steps of a strip -/

lemma sum_range_mul_mod (f : ℕ → ℕ) (M : ℕ) (hM : 0 < M) :
    ∀ n, ∑ σ ∈ Finset.range (n * M), f (σ % M) = n * ∑ j ∈ Finset.range M, f j
  | 0 => by simp
  | n + 1 => by
    rw [Nat.succ_mul, Finset.sum_range_add, sum_range_mul_mod f M hM n, Nat.succ_mul]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Finset.mem_range.mp hj)]

lemma hit_eq (hk : 2 ≤ k) (e : Fin I.schemas.length) (σ : ℕ) :
    hit e σ = if ∃ c ∈ dom I e, checkMatrix k ℓ (stepRow (by omega) σ) c ≠ 0 then 1 else 0 := by
  simp only [hit, ent_eq hk]

lemma sum_hit (hk : 2 ≤ k) (e : Fin I.schemas.length) :
    ∑ σ ∈ Finset.range (numSteps k ℓ), hit e σ = (k + 1) * numRows (sch I e) := by
  classical
  have hM : 0 < k - 1 + ℓ := by omega
  let f : ℕ → ℕ := fun j => if h : j < k - 1 + ℓ then
    (if ∃ c ∈ dom I e, checkMatrix k ℓ (finSumFinEquiv.symm ⟨j, h⟩) c ≠ 0 then 1 else 0) else 0
  have h1 : ∀ σ, hit e σ = f (σ % (k - 1 + ℓ)) := by
    intro σ
    rw [hit_eq hk]
    simp only [f, dif_pos (Nat.mod_lt σ hM), stepRow]
    rfl
  simp_rw [h1]
  rw [numSteps, sum_range_mul_mod f _ hM (k + 1)]
  congr 1
  rw [Finset.sum_range]
  simp only [f, Fin.is_lt, dif_pos]
  rw [Equiv.sum_comp finSumFinEquiv.symm
    (fun j => if ∃ c ∈ dom I e, checkMatrix k ℓ j c ≠ 0 then 1 else 0)]
  rw [numRows, Finset.card_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : ∃ c ∈ (sch I e).domain, checkMatrix k ℓ j c ≠ 0 <;> simp [h, dom]

lemma stripCost_le (hk : 2 ≤ k) (e : Fin I.schemas.length) :
    stripCost e = (4 * k + 1) * ((k + 1) * numRows (sch I e)) := by
  rw [stripCost, ← Finset.mul_sum, sum_hit hk]

lemma le_foldr_max {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

lemma numRows_lt_Λ (e : Fin I.schemas.length) : numRows (sch I e) + 1 ≤ Λ I := by
  have := le_foldr_max (List.mem_map_of_mem (f := numRows) (sch_mem I e))
  unfold Λ; omega

lemma one_le_Λ : 1 ≤ Λ I := by unfold Λ; omega

/-- The constant of one inference step. -/
def stepConst (k : ℕ) : ℕ := (4 * k + 1) * (k + 1) + 8 * k

lemma stepCost_le (hk : 2 ≤ k) (e : Fin I.schemas.length) :
    stepCost (I := I) e ≤ stepConst k * Λ I := by
  rw [stepCost, stripCost_le hk]
  have h := numRows_lt_Λ (I := I) e
  calc (4 * k + 1) * ((k + 1) * numRows (sch I e)) + 8 * k
      ≤ stepConst k * (numRows (sch I e) + 1) := by unfold stepConst; nlinarith
    _ ≤ stepConst k * Λ I := Nat.mul_le_mul_left _ h

/-- **Part (I) of the matrix compiler.** -/
theorem spoilerWins (hk : 2 ≤ k) {τ : ℕ} (hτ : I.conflictRound = τ) :
    SpoilerWinsWithin (k + 1) ((2 * k + stepConst k) * Λ I * (τ + 1)) G₀ G₁ := by
  classical
  obtain ⟨X, h0, h1⟩ := hasConflict_of_conflictRound I hτ
  obtain ⟨ha, hs⟩ := known_valid I h0
  let cls : Fin k → ICls I := fun i => .coord X.1 (i, X.2 i)
  have hval : ∀ i, ClsValid I (cls i) := fun i => hs (mem_supp_iff.mpr rfl)
  have hfill := forces_fill (List.finRange k) (List.nodup_finRange k)
    (S := fun _ => none) (fun _ _ _ _ _ _ h => by simp at h) cls hval
  rw [List.length_finRange] at hfill
  have hwin := hfill (stepConst k * Λ I * τ) fun S' ⟨h1', _, hPI⟩ => by
    choose lab hlab using fun i => h1' i (List.mem_finRange i)
    have hdisc : Disc S' X (∑ i, (lab i).1 + 1) := by
      refine ⟨fun i => (i, X.2 i), fun i j h => congrArg Prod.fst h, rfl, lab, hlab, ?_, hPI⟩
      ring_nf; rw [show (2 : ZMod 2) = 0 from rfl]; ring
    have hfact : (X, ∑ i, (lab i).1 + 1) ∈ I.toParitySystem.known τ := by
      rcases zmod2_eq_zero_or_one (∑ i, (lab i).1 + 1) with h | h <;> rw [h] <;> assumption
    exact walk hk _ (fun e => stepCost_le hk e) τ S' X _ hfact hdisc
  intro hsurv
  apply hwin.mono _ hsurv.2
  have h1 : 2 * k ≤ 2 * k * (Λ I * (τ + 1)) :=
    Nat.le_mul_of_pos_right _ (Nat.mul_pos one_le_Λ (Nat.succ_pos τ))
  have h2 : (2 * k + stepConst k) * Λ I * (τ + 1) =
      stepConst k * Λ I * τ + 2 * k * (Λ I * (τ + 1)) + stepConst k * Λ I := by ring
  omega

end Lax119563Proofs.Matrix

end Matrix_SpoilerMain

/-! ### Formerly `Lax119563Proofs.Matrix.Size` -/

section Matrix_Size

/-!
# Size of the matrix graphs

Each graph has at most `16 S` vertices (Lemma "Matrix size"), and at most three times as
many edges as vertices: every edge contains exactly one hub, and hubs have degree at most
three.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

/-! ### Counting vertices -/

lemma length_flatMap_eq {α β : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup)
    (f : α → List β) : (l.flatMap f).length = ∑ x ∈ l.toFinset, (f x).length := by
  rw [List.length_flatMap, List.sum_toFinset _ hl]

lemma toFinset_coordList (D : Finset (Coord k ℓ)) : (coordList D).toFinset = D := by
  ext c; simp

lemma length_coordVerts (v : Fin I.numLocations) :
    (coordVerts I v).length ≤ 2 * (I.domain v).card := by
  rw [coordVerts, length_flatMap_eq (nodup_coordList _), toFinset_coordList, mul_comm,
    ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun c _ => ?_
  split <;> simp [bits1]

lemma length_columnVerts (e : Fin I.schemas.length) (c : Coord k ℓ) :
    (columnVerts I e c).length ≤ 8 := by
  unfold columnVerts
  split <;> simp [bits1, bits2]

lemma length_stepVerts (e : Fin I.schemas.length) (σ : ℕ) :
    (stepVerts I e σ).length =
      2 * hit e σ + 6 * ((dom I e).filter fun c => ent σ c ≠ 0).card := by
  classical
  unfold stepVerts
  rw [List.length_append, length_flatMap_eq ((nodup_coordList _).filter _)]
  have : ((coordList (dom I e)).filter fun c => decide (ent σ c ≠ 0)).toFinset =
      (dom I e).filter fun c => ent σ c ≠ 0 := by
    ext c; simp
  rw [this]
  simp only [List.length_append, List.length_map, bits1, bits2, List.length_cons,
    List.length_nil, Finset.sum_const, smul_eq_mul]
  congr 1
  · unfold hit; split <;> simp
  · ring

lemma sum_ent_card (hk : 2 ≤ k) (e : Fin I.schemas.length) :
    ∑ σ ∈ Finset.range (numSteps k ℓ), ((dom I e).filter fun c => ent σ c ≠ 0).card =
      (k + 1) * nnz (sch I e) := by
  classical
  have hM : 0 < k - 1 + ℓ := by omega
  let f : ℕ → ℕ := fun j => if h : j < k - 1 + ℓ then
    ((dom I e).filter fun c => checkMatrix k ℓ (finSumFinEquiv.symm ⟨j, h⟩) c ≠ 0).card else 0
  have h1 : ∀ σ, ((dom I e).filter fun c => ent σ c ≠ 0).card = f (σ % (k - 1 + ℓ)) := by
    intro σ
    simp only [f, dif_pos (Nat.mod_lt σ hM), ent_eq hk, stepRow]
  simp_rw [h1]
  rw [numSteps, sum_range_mul_mod f _ hM (k + 1)]
  congr 1
  rw [Finset.sum_range]
  simp only [f, Fin.is_lt, dif_pos]
  rw [Equiv.sum_comp finSumFinEquiv.symm
    (fun j => ((dom I e).filter fun c => checkMatrix k ℓ j c ≠ 0).card)]
  rw [nnz, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.card_filter]
  rfl

lemma card_dom_le_nnz (hk : 2 ≤ k) (e : Fin I.schemas.length) :
    (dom I e).card ≤ nnz (sch I e) := by
  classical
  let row : Coord k ℓ → Fin (k - 1) ⊕ Fin ℓ := fun c =>
    if h : (c.1 : ℕ) < k - 1 then .inl ⟨c.1, h⟩ else .inl ⟨0, by omega⟩
  refine Finset.card_le_card_of_injOn (fun c => (row c, c)) (fun c hc => ?_)
    (fun c _ c' _ h => congrArg Prod.snd h)
  simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, Finset.mem_univ,
    true_and]
  refine ⟨hc, ?_⟩
  simp only [row]
  split
  · next h => simp [checkMatrix_inl]
  · next h =>
    have : (c.1 : ℕ) = k - 1 := by have := c.1.2; omega
    simp [checkMatrix_inl, this]

lemma numRows_le_nnz (e : Fin I.schemas.length) : numRows (sch I e) ≤ nnz (sch I e) := by
  classical
  unfold numRows nnz
  refine Finset.card_le_card_of_surjOn Prod.fst fun j hj => ?_
  simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hj
  obtain ⟨c, hc, hjc⟩ := hj
  exact ⟨(j, c), by simp [hc, hjc], rfl⟩

lemma length_schemaVerts (hk : 2 ≤ k) (e : Fin I.schemas.length) :
    (schemaVerts I e).length ≤ 16 * (k + 1) * nnz (sch I e) := by
  classical
  unfold schemaVerts
  rw [List.length_append, length_flatMap_eq (nodup_coordList _), toFinset_coordList,
    length_flatMap_eq List.nodup_range, List.toFinset_range]
  simp_rw [length_stepVerts]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_ent_card hk,
    show ∑ σ ∈ Finset.range (numSteps k ℓ), hit e σ = (k + 1) * numRows (sch I e) from
      sum_hit hk e]
  have h1 : ∑ c ∈ dom I e, (columnVerts I e c).length ≤ 8 * (dom I e).card := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun c _ => length_columnVerts e c
  have h2 := card_dom_le_nnz hk e
  have h3 := numRows_le_nnz e
  nlinarith

lemma sum_get_eq {α : Type*} (l : List α) (f : α → ℕ) :
    ∑ e : Fin l.length, f (l.get e) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Fin.sum_univ_succ]

/-- **Matrix size.** -/
theorem card_vertexList_le (hk : 2 ≤ k) : (vertexList I).length ≤ 16 * matrixSize I := by
  classical
  unfold vertexList
  rw [List.length_append, length_flatMap_eq (List.nodup_finRange _),
    length_flatMap_eq (List.nodup_finRange _), List.toFinset_finRange, List.toFinset_finRange]
  have h1 : ∑ v, (coordVerts I v).length ≤ 2 * ∑ v, (I.domain v).card := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun v _ => length_coordVerts v
  have h2 : ∑ e, (schemaVerts I e).length ≤ 16 * (k + 1) * (I.schemas.map nnz).sum := by
    rw [← sum_get_eq, Finset.mul_sum]
    exact Finset.sum_le_sum fun e _ => length_schemaVerts hk e
  unfold matrixSize
  calc _ ≤ 2 * ∑ v, (I.domain v).card + 16 * (k + 1) * (I.schemas.map nnz).sum :=
        Nat.add_le_add h1 h2
    _ ≤ _ := by ring_nf; omega

end Lax119563Proofs.Matrix

end Matrix_Size

/-! ### Formerly `Lax119563Proofs.Matrix.Edges` -/

section Matrix_Edges

/-!
# Edges of the matrix graphs

Every edge joins a hub (update, junction, link) with a non-hub, and a hub has at most one
neighbor in each of its at most three neighbor classes. Hence each graph has at most three
times as many edges as vertices.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

/-- The neighbor classes of a hub. -/
def slots : ICls I → Finset (ICls I)
  | .upd e σ c => {trackAt I e c σ, .track e σ c, .coef e σ}
  | .junc e c => {coordU e c, coordV e c, .sum e c}
  | .link e c => {trackAt I e c (numSteps k ℓ), endCls I e c}
  | _ => ∅

lemma card_slots_le (X : ICls I) : (slots X).card ≤ 3 := by
  cases X <;> simp only [slots] <;>
    first
    | exact (Finset.card_insert_le _ _).trans
        (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))
    | exact (Finset.card_insert_le _ _).trans (by simp)
    | simp

lemma mem_slots {X Y : ICls I} {l m : Lab} (h : hubB I X l Y m = true) : Y ∈ slots X := by
  cases X with
  | upd e σ c =>
    rw [hubB_upd] at h
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [slots]
  | junc e c =>
    rw [hubB_junc'] at h
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [slots]
  | link e c =>
    rw [hubB_link] at h
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [slots]
  | coord => simp [hubB] at h
  | sum => simp [hubB] at h
  | track => simp [hubB] at h
  | coef => simp [hubB] at h

/-- A hub prescribes the label of its neighbor in each neighbor class. -/
lemma hubB_label_unique {X Y : ICls I} (hX : ClsValid I X) {l m m' : Lab}
    (h : hubB I X l Y m = true) (h' : hubB I X l Y m' = true) : m.1 = m'.1 := by
  cases X with
  | upd e σ c =>
    rw [hubB_upd] at h h'
    rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
    rcases h' with ⟨h1, h'⟩ | ⟨h1, h'⟩ | ⟨h1, h'⟩ <;>
    first
    | exact h.trans h'.symm
    | exact absurd h1 (trackAt_ne_track e c σ)
    | exact absurd h1.symm (trackAt_ne_track e c σ)
    | exact absurd h1 (trackAt_ne_coef e c σ σ)
    | exact absurd h1.symm (trackAt_ne_coef e c σ σ)
    | simp at h1
  | junc e c =>
    have ht : isTern (sch I e) = true := hX.1
    rw [hubB_junc'] at h h'
    rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
    rcases h' with ⟨h1, h'⟩ | ⟨h1, h'⟩ | ⟨h1, h'⟩ <;>
    first
    | exact h.trans h'.symm
    | exact absurd h1 (coordU_ne_coordV ht c)
    | exact absurd h1.symm (coordU_ne_coordV ht c)
    | simp [coordU, coordV] at h1
  | link e c =>
    rw [hubB_link] at h h'
    rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
    rcases h' with ⟨-, h'⟩ | ⟨-, h'⟩ <;> exact h.trans h'.symm
  | coord => simp [hubB] at h
  | sum => simp [hubB] at h
  | track => simp [hubB] at h
  | coef => simp [hubB] at h

lemma twoBit_of_not_hub {X : ICls I} (h : isHub I X = false) : twoBit I X = false := by
  cases X <;> simp_all [isHub, twoBit]

/-- A valid name of a non-hub class is determined by its effective label. -/
lemma name_unique (ε : ZMod 2) {x y : VName I} (hx : Valid I x) (hy : Valid I y)
    (hc : x.1 = y.1) (hhub : isHub I x.1 = false) (he : (eff I ε x).1 = (eff I ε y).1) :
    x = y := by
  obtain ⟨X, l⟩ := x
  obtain ⟨Y, m⟩ := y
  simp only at hc
  subst hc
  have h2 : l.2 = 0 := hx.2.1 (twoBit_of_not_hub hhub)
  have h2' : m.2 = 0 := hy.2.1 (twoBit_of_not_hub hhub)
  simp only [eff] at he
  have h1 : l.1 = m.1 := add_right_cancel he
  ext <;> simp [h1, h2, h2']

instance (ε : ZMod 2) : DecidableRel (matrixGraph I ε).graph.Adj := fun i j =>
  inferInstanceAs (Decidable (adjN I ε (nm i) (nm j)))

lemma degree_hub_le (ε : ZMod 2) (p : Fin (nV I)) (hp : isHub I (nm p).1 = true) :
    (matrixGraph I ε).graph.degree p ≤ 3 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine (Finset.card_le_card_of_injOn (fun q => (nm q).1) (fun q hq => ?_)
    (fun q hq q' hq' hqq => ?_)).trans (card_slots_le (nm p).1)
  · rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hq
    exact mem_slots ((adjN_iff_hub ε hp).mp hq)
  · rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hq hq'
    have h1 : hubB I (nm p).1 (eff I ε (nm p)) (nm q).1 (eff I ε (nm q)) = true :=
      (adjN_iff_hub ε hp).mp hq
    have h2 : hubB I (nm p).1 (eff I ε (nm p)) (nm q').1 (eff I ε (nm q')) = true :=
      (adjN_iff_hub ε hp).mp hq'
    simp only at hqq
    rw [hqq] at h1
    have hl := hubB_label_unique (nm_valid p).1 h1 h2
    have hnh := (hubB_hub I h2).2
    exact nm_injective (name_unique ε (nm_valid q) (nm_valid q') hqq (hqq ▸ hnh) hl)

/-- **Edge bound.** -/
theorem numEdges_le (ε : ZMod 2) : (matrixGraph I ε).numEdges ≤ 3 * nV I := by
  classical
  let G := (matrixGraph I ε).graph
  let hubs : Finset (Fin (nV I)) := Finset.univ.filter fun p => isHub I (nm p).1 = true
  have hsub : G.edgeFinset ⊆ hubs.biUnion fun p => G.incidenceFinset p := by
    intro s hs
    induction s using Sym2.ind with
    | h p q =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hs
      rw [Finset.mem_biUnion]
      rcases hs with h | h
      · have h' : hubB I (nm p).1 (eff I ε (nm p)) (nm q).1 (eff I ε (nm q)) = true := h
        refine ⟨p, by simp [hubs, (hubB_hub I h').1], ?_⟩
        rw [SimpleGraph.mem_incidenceFinset]
        exact ⟨Or.inl h, Sym2.mem_mk_left _ _⟩
      · have h' : hubB I (nm q).1 (eff I ε (nm q)) (nm p).1 (eff I ε (nm p)) = true := h
        refine ⟨q, by simp [hubs, (hubB_hub I h').1], ?_⟩
        rw [SimpleGraph.mem_incidenceFinset]
        exact ⟨Or.inr h, Sym2.mem_mk_right _ _⟩
  have : (matrixGraph I ε).numEdges = G.edgeFinset.card := by
    rw [ColoredGraph.numEdges, SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]
  rw [this]
  calc G.edgeFinset.card ≤ ∑ p ∈ hubs, (G.incidenceFinset p).card :=
        (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ p ∈ hubs, 3 := Finset.sum_le_sum fun p hp => by
        rw [SimpleGraph.card_incidenceFinset_eq_degree]
        exact degree_hub_le ε p (Finset.mem_filter.mp hp).2
    _ ≤ 3 * nV I := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
        exact Nat.mul_le_mul_left _ ((Finset.card_le_univ _).trans (by simp))

end Lax119563Proofs.Matrix

end Matrix_Edges

/-! ### Formerly `Lax119563Proofs.RowSpace.Construction` -/

section RowSpace_Construction

/-!
# The row-space construction

The graphs `rsGraph I 0, rsGraph I 1` of the row-space compiler.

## Classes

We reuse the class type `ICls I` of the matrix compiler:
* `coord v c` (`c ∈ 𝔠_v`): coordinate classes;
* `sum e c`, `junc e c` (`e` ternary, `c ∈ 𝔠_e`): sum pairs and junctions;
* `track e h c` (`1 ≤ h ≤ k + 1`, `c ∈ 𝔠_e`): internal track classes;
* `upd e h c` (`1 ≤ h ≤ k + 2`, `c ∈ 𝔠_e`): update classes of stage `h`;
* `coef e h` (`1 ≤ h ≤ k + 2`): the mask class of stage `h`.
The class `link` is unused. The track class at index `h` (`trackCls`) is the start class
(`coord u (σ c)` resp. `sum e c`) for `h = 0`, the end class `coord w (π c)` for `h = k + 2`,
and `track e h c` otherwise.

## Vertices

A vertex is a pair of a class and a label in `RLab k ℓ = 𝔽₂ × 𝔽₂ × 𝔽₂^𝔠`: one-bit classes
use labels `(s, 0, 0)`, two-bit classes (`junc`, `upd`) labels `(s, t, 0)` (standing for the
junction vertex `(s, t, s + t)` resp. the update vertex `(s, t)`), mask classes labels
`(0, 0, x)` for `x` in the row space of `B_e` (extended by zero outside `𝔠_e`). The vertices of
`G_ε` carry their *effective* labels: the names `names I` (the vertices of `G₀`) translated by
`ε • off X`, where `off` is the initial seed on singleton coordinate classes.

## Edges

Every edge joins a hub (update or junction) with a vertex of a neighboring class, subject to
one linear condition on the labels (`hubR`).

## Colors

The color of a vertex is an injective code of its class.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs
open Lax119563Proofs.Matrix

namespace Lax119563Proofs.RowSpace

variable {k ℓ : ℕ}

/-- Labels. -/
abbrev RLab (k ℓ : ℕ) := ZMod 2 × ZMod 2 × Vec k ℓ

instance (k ℓ : ℕ) : DecidableEq (Vec k ℓ) := Fintype.decidablePiFintype

lemma zmod2_self_add (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;> decide

lemma rlab_add_self (l : RLab k ℓ) : l + l = 0 := by
  obtain ⟨a, b, x⟩ := l
  refine Prod.ext (zmod2_self_add a) (Prod.ext (zmod2_self_add b) ?_)
  funext c
  exact zmod2_self_add (x c)

lemma rlab_add_add_cancel (l d : RLab k ℓ) : l + d + d = l := by
  rw [add_assoc, rlab_add_self, add_zero]

variable (I : ImplicitParitySystem k ℓ)

/-! ### Masks -/

/-- The mask `μᵀ B_e`, extended by zero outside `𝔠_e`. -/
def maskOf (e : Fin I.schemas.length) (μ : Row k ℓ → ZMod 2) : Vec k ℓ :=
  fun c => if c ∈ dom I e then ∑ j, μ j * checkMatrix k ℓ j c else 0

/-- The row space of `B_e`, as vectors extended by zero. -/
def maskSet (e : Fin I.schemas.length) : Finset (Vec k ℓ) :=
  Finset.univ.image (maskOf I e)

lemma maskOf_add (e : Fin I.schemas.length) (μ μ' : Row k ℓ → ZMod 2) :
    maskOf I e (μ + μ') = maskOf I e μ + maskOf I e μ' := by
  funext c
  simp only [maskOf, Pi.add_apply]
  split
  · simp [add_mul, Finset.sum_add_distrib]
  · simp

lemma maskOf_zero (e : Fin I.schemas.length) : maskOf I e 0 = 0 := by
  funext c; simp [maskOf]

lemma zero_mem_maskSet (e : Fin I.schemas.length) : (0 : Vec k ℓ) ∈ maskSet I e :=
  Finset.mem_image.mpr ⟨0, Finset.mem_univ _, maskOf_zero I e⟩

lemma add_mem_maskSet {e : Fin I.schemas.length} {x y : Vec k ℓ} (hx : x ∈ maskSet I e)
    (hy : y ∈ maskSet I e) : x + y ∈ maskSet I e := by
  obtain ⟨μ, -, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨μ', -, rfl⟩ := Finset.mem_image.mp hy
  exact Finset.mem_image.mpr ⟨μ + μ', Finset.mem_univ _, maskOf_add I e μ μ'⟩

lemma maskSet_supp {e : Fin I.schemas.length} {x : Vec k ℓ} (hx : x ∈ maskSet I e) {c : Coord k ℓ}
    (hc : c ∉ dom I e) : x c = 0 := by
  obtain ⟨μ, -, rfl⟩ := Finset.mem_image.mp hx
  simp [maskOf, hc]

/-! ### Track classes -/

/-- The track class of column `c` at index `h ∈ [0, k + 2]`. -/
def trackCls (e : Fin I.schemas.length) (c : Coord k ℓ) (h : ℕ) : ICls I :=
  if h = 0 then startCls I e c else if h = k + 2 then endCls I e c else .track e h c

lemma trackCls_zero (e : Fin I.schemas.length) (c : Coord k ℓ) :
    trackCls I e c 0 = startCls I e c := by simp [trackCls]

lemma trackCls_last (e : Fin I.schemas.length) (c : Coord k ℓ) :
    trackCls I e c (k + 2) = endCls I e c := by simp [trackCls]

/-! ### Classes and labels -/

/-- The coordinate classes. -/
def coordClasses : Finset (ICls I) :=
  Finset.univ.biUnion fun v => (I.domain v).image (Cls.coord v)

/-- The classes of the gadget of schema `e`. -/
def schemaClasses (e : Fin I.schemas.length) : Finset (ICls I) :=
  ((if isTern (sch I e) then (dom I e).image (Cls.sum e) ∪ (dom I e).image (Cls.junc e) else ∅) ∪
    (Finset.Icc 1 (k + 1) ×ˢ dom I e).image (fun p => Cls.track e p.1 p.2)) ∪
    ((Finset.Icc 1 (k + 2) ×ˢ dom I e).image (fun p => Cls.upd e p.1 p.2) ∪
    (Finset.Icc 1 (k + 2)).image (Cls.coef e))

/-- All classes. -/
def classes : Finset (ICls I) :=
  coordClasses I ∪ Finset.univ.biUnion (schemaClasses I)

/-- One-bit labels. -/
def lab1 : Finset (RLab k ℓ) := {0, (1, 0, 0)}

/-- Two-bit labels. -/
def lab2 : Finset (RLab k ℓ) := {0, (1, 0, 0), (0, 1, 0), (1, 1, 0)}

/-- The labels of the vertices of a class in `G₀`. -/
def labs : ICls I → Finset (RLab k ℓ)
  | .coord v _ => if (I.init v).isSome then {0} else lab1
  | .sum .. => lab1
  | .track .. => lab1
  | .junc .. => lab2
  | .upd .. => lab2
  | .coef e _ => (maskSet I e).image fun x => (0, 0, x)
  | .link .. => ∅

/-- The vertex names of `G₀`. -/
def names : Finset (ICls I × RLab k ℓ) :=
  (classes I).biUnion fun X => (labs I X).image (Prod.mk X)

/-- The label offset of a class in `G₁`. -/
def off : ICls I → RLab k ℓ
  | .coord v c => (initSeed I v c, 0, 0)
  | _ => 0

/-- The vertices of `G_ε`. -/
def verts (ε : ZMod 2) : Finset (ICls I × RLab k ℓ) :=
  (names I).image fun x => (x.1, x.2 + ε • off I x.1)

lemma mem_names {x : ICls I × RLab k ℓ} : x ∈ names I ↔ x.1 ∈ classes I ∧ x.2 ∈ labs I x.1 := by
  obtain ⟨X, l⟩ := x
  simp only [names, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨Y, hY, l', hl', h⟩
    cases h
    exact ⟨hY, hl'⟩
  · rintro ⟨hX, hl⟩
    exact ⟨X, hX, l, hl, rfl⟩

lemma mem_verts {ε : ZMod 2} {x : ICls I × RLab k ℓ} :
    x ∈ verts I ε ↔ (x.1, x.2 + ε • off I x.1) ∈ names I := by
  obtain ⟨X, l⟩ := x
  simp only [verts, Finset.mem_image]
  constructor
  · rintro ⟨⟨Y, l'⟩, hy, h⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa [rlab_add_add_cancel] using hy
  · intro h
    exact ⟨_, h, by simp [rlab_add_add_cancel]⟩

lemma verts_zero : verts I 0 = names I := by
  simp [verts]

lemma card_verts (ε : ZMod 2) : (verts I ε).card = (names I).card := by
  refine Finset.card_image_of_injective _ fun x y h => ?_
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have := congrArg (· + ε • off I x.1) h2
  simp only [rlab_add_add_cancel] at this
  rw [h1, rlab_add_add_cancel] at this
  exact Prod.ext h1 this

/-! ### Adjacency -/

/-- A hub of class `X` with label `l` is adjacent to the vertex of class `Y` with label `m`. -/
def hubR : ICls I → RLab k ℓ → ICls I → RLab k ℓ → Prop
  | .upd e h c, l, Y, m =>
      (Y = trackCls I e c (h - 1) ∧ m.1 = l.1) ∨ (Y = trackCls I e c h ∧ m.1 = l.2.1) ∨
      (Y = .coef e h ∧ m.2.2 c = l.1 + l.2.1)
  | .junc e c, l, Y, m =>
      (Y = .coord (locU (sch I e)) ((permU (sch I e)).apply c) ∧ m.1 = l.1) ∨
      (Y = .coord (locV (sch I e)) ((permV (sch I e)).apply c) ∧ m.1 = l.2.1) ∨
      (Y = .sum e c ∧ m.1 = l.1 + l.2.1)
  | _, _, _, _ => False

/-- Adjacency of vertices (in both graphs). -/
def radj (x y : ICls I × RLab k ℓ) : Prop :=
  hubR I x.1 x.2 y.1 y.2 ∨ hubR I y.1 y.2 x.1 x.2

/-- Hubs. -/
def isHubR : ICls I → Prop
  | .upd .. => True
  | .junc .. => True
  | _ => False

lemma trackCls_not_hub (e : Fin I.schemas.length) (c : Coord k ℓ) (h : ℕ) :
    ¬ isHubR I (trackCls I e c h) := by
  unfold trackCls startCls endCls
  split_ifs <;> simp [isHubR]

lemma hubR_hub {X Y : ICls I} {l m : RLab k ℓ} (h : hubR I X l Y m) :
    isHubR I X ∧ ¬ isHubR I Y := by
  cases X with
  | upd e σ c =>
    refine ⟨trivial, ?_⟩
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact trackCls_not_hub I e c _
    · exact trackCls_not_hub I e c _
    · simp [isHubR]
  | junc e c =>
    refine ⟨trivial, ?_⟩
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [isHubR]
  | coord => exact h.elim
  | sum => exact h.elim
  | link => exact h.elim
  | track => exact h.elim
  | coef => exact h.elim

lemma radj_symm (x y : ICls I × RLab k ℓ) (h : radj I x y) : radj I y x := h.symm

lemma radj_irrefl (x : ICls I × RLab k ℓ) : ¬ radj I x x := by
  rintro (h | h) <;> exact (hubR_hub I h).2 (hubR_hub I h).1

lemma radj_iff_hub {x y : ICls I × RLab k ℓ} (hx : isHubR I x.1) :
    radj I x y ↔ hubR I x.1 x.2 y.1 y.2 := by
  refine ⟨fun h => h.elim id fun h => absurd hx (hubR_hub I h).2, Or.inl⟩

/-! ### Colors -/

/-- An injective encoding of classes. -/
def clsKey {w E : ℕ} : Cls k ℓ w E → ℕ × ℕ × ℕ × Option (Coord k ℓ)
  | .coord v c => (0, v, 0, some c)
  | .sum e c => (1, e, 0, some c)
  | .junc e c => (2, e, 0, some c)
  | .link e c => (3, e, 0, some c)
  | .track e σ c => (4, e, σ, some c)
  | .upd e σ c => (5, e, σ, some c)
  | .coef e σ => (6, e, σ, none)

lemma clsKey_injective {w E : ℕ} : Function.Injective (clsKey (k := k) (ℓ := ℓ) (w := w) (E := E)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [clsKey, Fin.ext_iff]

instance {w E : ℕ} : Countable (Cls k ℓ w E) := clsKey_injective.countable

/-- The color code of a class. -/
noncomputable def code : ICls I → ℕ := Classical.choose (exists_injective_nat (ICls I))

lemma code_injective : Function.Injective (code I) :=
  Classical.choose_spec (exists_injective_nat (ICls I))

/-! ### The graphs -/

/-- **The row-space graph** `G_ε`. -/
noncomputable abbrev rsGraph (ε : ZMod 2) : ColoredGraph where
  n := (verts I ε).card
  graph :=
    { Adj := fun i j => radj I ((verts I ε).equivFin.symm i).1 ((verts I ε).equivFin.symm j).1
      symm := ⟨fun _ _ h => radj_symm I _ _ h⟩
      loopless := ⟨fun _ h => radj_irrefl I _ h⟩ }
  color := fun i => code I ((verts I ε).equivFin.symm i).1.1

variable {I}

/-- The vertex of `G_ε` with index `i`. -/
noncomputable def vx {ε : ZMod 2} (i : Fin (rsGraph I ε).n) : ICls I × RLab k ℓ :=
  ((verts I ε).equivFin.symm i).1

lemma vx_mem {ε : ZMod 2} (i : Fin (rsGraph I ε).n) : vx i ∈ verts I ε :=
  ((verts I ε).equivFin.symm i).2

/-- The index of a vertex of `G_ε`. -/
noncomputable def ix (ε : ZMod 2) (x : ICls I × RLab k ℓ) (hx : x ∈ verts I ε) :
    Fin (rsGraph I ε).n :=
  (verts I ε).equivFin ⟨x, hx⟩

@[simp] lemma vx_ix {ε : ZMod 2} (x : ICls I × RLab k ℓ) (hx : x ∈ verts I ε) :
    vx (ix ε x hx) = x := by
  simp [vx, ix]

@[simp] lemma ix_vx {ε : ZMod 2} (i : Fin (rsGraph I ε).n) : ix ε (vx i) (vx_mem i) = i := by
  simp [vx, ix]

lemma vx_injective {ε : ZMod 2} : Function.Injective (vx (I := I) (ε := ε)) := by
  intro i j h
  rw [← ix_vx i, ← ix_vx j]
  simp only [ix]
  congr 2

lemma rs_adj {ε : ZMod 2} (i j : Fin (rsGraph I ε).n) :
    (rsGraph I ε).graph.Adj i j ↔ radj I (vx i) (vx j) := Iff.rfl

lemma rs_color {ε : ZMod 2} (i : Fin (rsGraph I ε).n) : (rsGraph I ε).color i = code I (vx i).1 :=
  rfl

lemma rs_color_eq {ε ε' : ZMod 2} (i : Fin (rsGraph I ε).n) (j : Fin (rsGraph I ε').n) :
    (rsGraph I ε).color i = (rsGraph I ε').color j ↔ (vx i).1 = (vx j).1 :=
  (code_injective I).eq_iff

lemma rs_n (ε : ZMod 2) : (rsGraph I ε).n = (names I).card := card_verts I ε

end Lax119563Proofs.RowSpace

end RowSpace_Construction

/-! ### Formerly `Lax119563Proofs.RowSpace.OneVertex` -/

section RowSpace_OneVertex

/-!
# One-vertex tree decompositions (Abramsky–Jakl–Paine, Theorem 3.4)

Every graph of treewidth at most `k` has a tree decomposition of width at most `k`, rooted at a
node with empty bag, in which every other node introduces exactly one vertex. Identifying each
non-root node with the vertex it introduces turns the decomposition tree into a rooted forest on
the vertices; we record it as `OneVertexForest`.

The proof roots the decomposition tree at some node `r`. Each vertex `v` gets its topmost node
`top v` (the node of least depth whose bag contains `v`), which is an ancestor of every node whose
bag contains `v`. Ordering vertices by the depth of their topmost node, the bag of `v` is the part
of the bag of `top v` that comes no later than `v`, and the parent of `v` is the latest other
vertex of that bag.
-/

open Lax228581.Treewidth SimpleGraph

namespace Lax119563Proofs.RowSpace

/-- A one-vertex tree decomposition of width at most `k`, as a rooted forest on the vertices:
`bag p` is the bag of the node introducing `p`, and `(bag p).erase p` is contained in the bag of
the parent (and empty at roots). -/
structure OneVertexForest {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) where
  /-- The parent of a vertex in the forest (`none` at roots). -/
  parent : Fin n → Option (Fin n)
  /-- A depth function witnessing that `parent` is acyclic. -/
  depth : Fin n → ℕ
  depth_lt : ∀ p q, parent p = some q → depth q < depth p
  /-- The bag of the node introducing `p`. -/
  bag : Fin n → Finset (Fin n)
  mem_bag : ∀ p, p ∈ bag p
  card_bag : ∀ p, (bag p).card ≤ k + 1
  bag_sub : ∀ p q, parent p = some q → (bag p).erase p ⊆ bag q
  bag_root : ∀ p, parent p = none → (bag p).erase p = ∅
  adj_mem : ∀ p q, G.Adj p q → q ∈ (bag p).erase p ∨ p ∈ (bag q).erase q

namespace OneVertex

section RootedTree

variable {N : Type*} [DecidableEq N] {T : SimpleGraph N}

omit [DecidableEq N] in
lemma path_eq (hT : T.IsTree) {u v : N} {p q : T.Walk u v} (hp : p.IsPath) (hq : q.IsPath) :
    p = q := by
  have := (hT.isAcyclic.subsingleton_path u v).elim ⟨p, hp⟩ ⟨q, hq⟩
  exact congrArg Subtype.val this

lemma length_eq_dist (hT : T.IsTree) {u v : N} {p : T.Walk u v} (hp : p.IsPath) :
    p.length = T.dist u v := by
  obtain ⟨q, hq⟩ := hT.connected.exists_walk_length_eq_dist u v
  have h1 : q.bypass = p := path_eq hT (q.bypass_isPath) hp
  have h2 := q.length_bypass_le_length
  have h3 := T.dist_le p
  rw [h1] at h2
  omega

lemma dist_add_of_mem (hT : T.IsTree) {x y z : N} {p : T.Walk x y} (hp : p.IsPath)
    (hz : z ∈ p.support) : T.dist x z + T.dist z y = T.dist x y := by
  rw [← length_eq_dist hT (hp.takeUntil hz), ← length_eq_dist hT (hp.dropUntil hz),
    ← length_eq_dist hT hp, ← Walk.length_append, Walk.take_spec]

/-- `a` is an ancestor of `i` in `T` rooted at `r`: `a` lies on the path from `r` to `i`. -/
def Anc (T : SimpleGraph N) (r a i : N) : Prop := ∃ p : T.Walk r i, p.IsPath ∧ a ∈ p.support

omit [DecidableEq N] in
lemma anc_of_mem (hT : T.IsTree) {r a i : N} {p : T.Walk r i} (hp : p.IsPath)
    (ha : Anc T r a i) : a ∈ p.support := by
  obtain ⟨q, hq, haq⟩ := ha
  rwa [path_eq hT hp hq]

lemma anc_self (hT : T.IsTree) (r i : N) : Anc T r i i := by
  obtain ⟨p⟩ := hT.connected r i
  exact ⟨p.toPath, p.toPath.2, Walk.end_mem_support _⟩

lemma anc_dist (hT : T.IsTree) {r a i : N} (ha : Anc T r a i) :
    T.dist r a + T.dist a i = T.dist r i := by
  obtain ⟨p, hp, hap⟩ := ha
  exact dist_add_of_mem hT hp hap

lemma anc_le (hT : T.IsTree) {r a i : N} (ha : Anc T r a i) : T.dist r a ≤ T.dist r i := by
  have := anc_dist hT ha; omega

lemma anc_eq (hT : T.IsTree) {r a i : N} (ha : Anc T r a i) (h : T.dist r i ≤ T.dist r a) :
    a = i := by
  have := anc_dist hT ha
  exact (hT.connected.dist_eq_zero_iff).1 (by omega)

lemma anc_trans (hT : T.IsTree) {r a b c : N} (hab : Anc T r a b) (hbc : Anc T r b c) :
    Anc T r a c := by
  obtain ⟨p, hp, hbp⟩ := hbc
  exact ⟨p, hp, p.support_takeUntil_subset_support hbp (anc_of_mem hT (hp.takeUntil hbp) hab)⟩

lemma anc_total (hT : T.IsTree) {r a b i : N} (ha : Anc T r a i) (hb : Anc T r b i) :
    Anc T r a b ∨ Anc T r b a := by
  obtain ⟨p, hp, hap⟩ := ha
  have hbp := anc_of_mem hT hp hb
  by_cases h1 : b ∈ (p.takeUntil a hap).support
  · exact Or.inr ⟨_, hp.takeUntil hap, h1⟩
  by_cases h2 : a ∈ (p.takeUntil b hbp).support
  · exact Or.inl ⟨_, hp.takeUntil hbp, h2⟩
  have h1' : b ∈ (p.dropUntil a hap).support := by
    have := hbp; rw [← p.take_spec hap, Walk.mem_support_append_iff] at this; tauto
  have h2' : a ∈ (p.dropUntil b hbp).support := by
    have := hap; rw [← p.take_spec hbp, Walk.mem_support_append_iff] at this; tauto
  have e1 := dist_add_of_mem hT (hp.dropUntil hap) h1'
  have e2 := dist_add_of_mem hT (hp.dropUntil hbp) h2'
  have hab : T.dist a b = 0 := by rw [T.dist_comm (u := b) (v := a)] at e2; omega
  rw [hT.connected.dist_eq_zero_iff] at hab
  subst hab
  exact Or.inl (anc_self hT r a)

/-- If `a` is an ancestor of `b` and `b` of `c`, then `b` lies on the path from `a` to `c`. -/
lemma anc_path (hT : T.IsTree) {r a b c : N} (hab : Anc T r a b) (hbc : Anc T r b c) :
    ∃ q : T.Walk a c, q.IsPath ∧ b ∈ q.support := by
  obtain ⟨p, hp, hbp⟩ := hbc
  have hap : a ∈ p.support :=
    p.support_takeUntil_subset_support hbp (anc_of_mem hT (hp.takeUntil hbp) hab)
  refine ⟨p.dropUntil a hap, hp.dropUntil hap, ?_⟩
  have := hbp
  rw [← p.take_spec hap, Walk.mem_support_append_iff] at this
  rcases this with h | h
  · have hba : b = a := anc_eq hT ⟨_, hp.takeUntil hap, h⟩ (anc_le hT hab)
    subst hba
    exact Walk.start_mem_support _
  · exact h

/-- `p` is the parent of `x` in `T` rooted at `r`. -/
def Par (T : SimpleGraph N) (r p x : N) : Prop := T.Adj p x ∧ Anc T r p x

lemma par_dist (hT : T.IsTree) {r p x : N} (h : Par T r p x) :
    T.dist r p + 1 = T.dist r x := by
  have := anc_dist hT h.2
  rwa [dist_eq_one_iff_adj.2 h.1] at this

lemma adj_par (hT : T.IsTree) (r : N) {x y : N} (h : T.Adj x y) : Par T r x y ∨ Par T r y x := by
  obtain ⟨p⟩ := hT.connected r x
  by_cases hy : y ∈ p.toPath.1.support
  · exact Or.inr ⟨h.symm, _, p.toPath.2, hy⟩
  · exact Or.inl ⟨h, _, p.toPath.2.concat hy h, by simp⟩

lemma par_unique (hT : T.IsTree) {r p q x : N} (hp : Par T r p x) (hq : Par T r q x) : p = q := by
  have e1 := par_dist hT hp
  have e2 := par_dist hT hq
  rcases anc_total hT hp.2 hq.2 with h | h
  · exact anc_eq hT h (by omega)
  · exact (anc_eq hT h (by omega)).symm

/-- A path from `x` that avoids the parent of `x` stays below `x`. -/
lemma anc_or_par_mem (hT : T.IsTree) (r : N) {x y : N} (q : T.Walk x y) (hq : q.IsPath) :
    Anc T r x y ∨ ∃ p ∈ q.support, Par T r p x := by
  induction q with
  | nil => exact Or.inl (anc_self hT r _)
  | @cons x x' y h q ih =>
    rw [Walk.cons_isPath_iff] at hq
    rcases adj_par hT r h with hp | hp
    · rcases ih hq.1 with h' | ⟨p, hpq, hpp⟩
      · exact Or.inl (anc_trans hT hp.2 h')
      · exact absurd (par_unique hT hpp hp ▸ hpq) hq.2
    · exact Or.inr ⟨x', by simp, hp⟩

end RootedTree

/-- A vertex in the bags at both ends of a path of the decomposition tree is in every bag along
the path. -/
lemma mem_bag_of_mem_path {V : Type} {G : SimpleGraph V} (D : TreeDecomposition G)
    [DecidableEq D.Node] {v : V} {a b c : D.Node} (ha : v ∈ D.bag a) (hb : v ∈ D.bag b)
    {q : D.tree.Walk a b} (hq : q.IsPath) (hc : c ∈ q.support) : v ∈ D.bag c := by
  obtain ⟨w⟩ := (D.bag_indices_connected v).preconnected ⟨a, ha⟩ ⟨b, hb⟩
  have h1 := path_eq D.isTree
    (w.map (Embedding.induce {i : D.Node | v ∈ D.bag i}).toHom).bypass_isPath hq
  have h2 := Walk.support_bypass_subset_support
    (w.map (Embedding.induce {i : D.Node | v ∈ D.bag i}).toHom) (h1 ▸ hc)
  rw [Walk.support_map, List.mem_map] at h2
  obtain ⟨x, -, rfl⟩ := h2
  exact x.2

end OneVertex

open OneVertex in
/-- **Abramsky–Jakl–Paine, Theorem 3.4.** A graph of treewidth at most `k` has a one-vertex tree
decomposition of width at most `k`. -/
theorem oneVertexForest_of_treewidth {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ}
    (h : HasTreewidthAtMost G k) : Nonempty (OneVertexForest G k) := by
  classical
  obtain ⟨D, hD⟩ := h
  have hT := D.isTree
  obtain ⟨r⟩ := hT.connected.nonempty
  have hex : ∀ v, ∃ t, v ∈ D.bag t ∧
      ∀ j, v ∈ D.bag j → D.tree.dist r t ≤ D.tree.dist r j := by
    intro v
    obtain ⟨i, hi⟩ := D.vertex_mem_bag v
    obtain ⟨t, ht, hmin⟩ := (InvImage.wf (fun j => D.tree.dist r j) wellFounded_lt).has_min
      {j | v ∈ D.bag j} ⟨i, hi⟩
    exact ⟨t, ht, fun j hj => not_lt.1 (hmin j hj)⟩
  choose top htop hmin using hex
  have hanc : ∀ v i, v ∈ D.bag i → Anc D.tree r (top v) i := by
    intro v i hi
    obtain ⟨q⟩ := hT.connected (top v) i
    rcases anc_or_par_mem hT r q.toPath.1 q.toPath.2 with h | ⟨p, hp, hpar⟩
    · exact h
    · have h1 := hmin v p (mem_bag_of_mem_path D (htop v) hi q.toPath.2 hp)
      have h2 := par_dist hT hpar
      omega
  have hM : ∀ u w i, u ∈ D.bag i → w ∈ D.bag i →
      D.tree.dist r (top u) ≤ D.tree.dist r (top w) → u ∈ D.bag (top w) := by
    intro u w i hu hw hle
    rcases anc_total hT (hanc u i hu) (hanc w i hw) with h | h
    · obtain ⟨q, hq, hmem⟩ := anc_path hT h (hanc w i hw)
      exact mem_bag_of_mem_path D (htop u) hu hq hmem
    · rw [anc_eq hT h hle]
      exact htop u
  obtain ⟨key, hinj, hmono⟩ : ∃ key : Fin n → ℕ, Function.Injective key ∧
      ∀ u v, key u ≤ key v → D.tree.dist r (top u) ≤ D.tree.dist r (top v) := by
    have mono : ∀ u v : Fin n, D.tree.dist r (top u) * n + u.val ≤
        D.tree.dist r (top v) * n + v.val → D.tree.dist r (top u) ≤ D.tree.dist r (top v) := by
      intro u v h
      by_contra hlt
      have h1 : (D.tree.dist r (top v) + 1) * n ≤ D.tree.dist r (top u) * n :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 := v.isLt
      rw [Nat.add_mul, one_mul] at h1
      omega
    refine ⟨fun v => D.tree.dist r (top v) * n + v.val, fun u v h => ?_, mono⟩
    have e := le_antisymm (mono u v h.le) (mono v u h.ge)
    simp only [e] at h
    exact Fin.ext (by omega)
  let B : Fin n → Finset (Fin n) := fun v => (D.bag (top v)).filter (fun u => key u ≤ key v)
  have hpar : ∀ v, ∃ o : Option (Fin n), (o = none ∧ (B v).erase v = ∅) ∨
      ∃ w, o = some w ∧ w ∈ (B v).erase v ∧ ∀ u ∈ (B v).erase v, key u ≤ key w := by
    intro v
    rcases ((B v).erase v).eq_empty_or_nonempty with h | h
    · exact ⟨none, Or.inl ⟨rfl, h⟩⟩
    · obtain ⟨w, hw, hmax⟩ := ((B v).erase v).exists_max_image key h
      exact ⟨some w, Or.inr ⟨w, rfl, hw, hmax⟩⟩
  choose parent hparent using hpar
  have hsome : ∀ p q, parent p = some q →
      q ∈ (B p).erase p ∧ ∀ u ∈ (B p).erase p, key u ≤ key q := by
    intro p q h
    rcases hparent p with ⟨h1, -⟩ | ⟨w, h1, hw, hmax⟩
    · simp [h1] at h
    · rw [h1, Option.some_inj] at h
      subst h
      exact ⟨hw, hmax⟩
  refine ⟨⟨parent, key, ?_, B, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro p q h
    have hq := (hsome p q h).1
    simp only [B, Finset.mem_erase, Finset.mem_filter] at hq
    exact lt_of_le_of_ne hq.2.2 (fun e => hq.1 (hinj e))
  · intro p
    simp [B, htop p]
  · intro p
    exact (Finset.card_filter_le _ _).trans (hD _)
  · intro p q h u hu
    obtain ⟨hq, hmax⟩ := hsome p q h
    have hku := hmax u hu
    simp only [B, Finset.mem_erase, Finset.mem_filter] at hu hq ⊢
    exact ⟨hM u q (top p) hu.2.1 hq.2.1 (hmono _ _ hku), hku⟩
  · intro p h
    rcases hparent p with ⟨-, h1⟩ | ⟨w, h1, -⟩
    · exact h1
    · simp [h1] at h
  · intro p q hpq
    obtain ⟨i, hp, hq⟩ := D.edge_mem_bag hpq
    simp only [B, Finset.mem_erase, Finset.mem_filter]
    rcases le_total (key p) (key q) with h | h
    · exact Or.inr ⟨G.ne_of_adj hpq, hM p q i hp hq (hmono _ _ h), h⟩
    · exact Or.inl ⟨(G.ne_of_adj hpq).symm, hM q p i hq hp (hmono _ _ h), h⟩

end Lax119563Proofs.RowSpace

end RowSpace_OneVertex

/-! ### Formerly `Lax119563Proofs.RowSpace.Shifts` -/

section RowSpace_Shifts

/-!
# Descriptions and translations

A *description* consists of total seeds `z_v` and masks `x_{e,h}`. It translates every class
(`rshift`); the translation `tr D` maps the vertices of `G₀` to those of `G₁` as soon as the
seeds of initialized locations are the initial seeds and the masks lie in the row spaces, and
it preserves adjacency between two classes as soon as the mask-sum condition holds at the
coordinates of the update classes of the last stage involved.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler
open Lax119563Proofs.Matrix

namespace Lax119563Proofs.RowSpace

variable {k ℓ : ℕ}

variable (I : ImplicitParitySystem k ℓ) in
/-- A description: total seeds and masks. -/
structure RDesc where
  /-- The seed of each location. -/
  z : Fin I.numLocations → Vec k ℓ
  /-- The mask of stage `h` of schema `e`. -/
  x : Fin I.schemas.length → ℕ → Vec k ℓ

variable {I : ImplicitParitySystem k ℓ}

/-- The initial track bit `t_{e,0}(c)`. -/
def rt0 (D : RDesc I) (e : Fin I.schemas.length) (c : Coord k ℓ) : ZMod 2 :=
  D.z (locU (sch I e)) ((permU (sch I e)).apply c) +
    if isTern (sch I e) then D.z (locV (sch I e)) ((permV (sch I e)).apply c) else 0

/-- The sum of the masks of stages `1, …, h` at `c`. -/
def msum (D : RDesc I) (e : Fin I.schemas.length) (c : Coord k ℓ) (h : ℕ) : ZMod 2 :=
  ∑ i ∈ Finset.range h, D.x e (i + 1) c

/-- The track bit `t_{e,h}(c)`. -/
def TT (D : RDesc I) (e : Fin I.schemas.length) (c : Coord k ℓ) (h : ℕ) : ZMod 2 :=
  rt0 D e c + msum D e c h

/-- The translation of each class. -/
def rshift (D : RDesc I) : ICls I → RLab k ℓ
  | .coord v c => (D.z v c, 0, 0)
  | .sum e c => (rt0 D e c, 0, 0)
  | .junc e c => (D.z (locU (sch I e)) ((permU (sch I e)).apply c),
      D.z (locV (sch I e)) ((permV (sch I e)).apply c), 0)
  | .track e h c => (TT D e c h, 0, 0)
  | .upd e h c => (TT D e c (h - 1), TT D e c h, 0)
  | .coef e h => (0, 0, D.x e h)
  | .link .. => 0

/-- The translation of a vertex. -/
def tr (D : RDesc I) (x : ICls I × RLab k ℓ) : ICls I × RLab k ℓ := (x.1, x.2 + rshift D x.1)

@[simp] lemma tr_fst (D : RDesc I) (x : ICls I × RLab k ℓ) : (tr D x).1 = x.1 := rfl

lemma tr_tr (D : RDesc I) (x : ICls I × RLab k ℓ) : tr D (tr D x) = x := by
  simp [tr, rlab_add_add_cancel]

/-- The seeds of initialized locations are the initial seeds. -/
def InitOK (D : RDesc I) : Prop := ∀ v, (I.init v).isSome → D.z v = initSeed I v

/-- The masks lie in the row spaces. -/
def MaskOK (D : RDesc I) : Prop := ∀ e h, D.x e h ∈ maskSet I e

/-- The sum of the seeds at the argument coordinates of `c`. -/
def bsum (D : RDesc I) (e : Fin I.schemas.length) (c : Coord k ℓ) : ZMod 2 :=
  ∑ i, D.z (argLoc (sch I e) i) ((argPerm (sch I e) i).apply c)

/-- The mask-sum condition at column `c` of schema `e`. -/
def MS (D : RDesc I) (e : Fin I.schemas.length) (c : Coord k ℓ) : Prop :=
  msum D e c (k + 2) = bsum D e c

lemma rt0_add_end (D : RDesc I) (e : Fin I.schemas.length) (c : Coord k ℓ) :
    rt0 D e c + D.z (locEnd (sch I e)) ((permEnd (sch I e)).apply c) = bsum D e c := by
  rw [bsum, sum_args (sch I e) fun v P => D.z v (P.apply c), rt0]

lemma TT_last (D : RDesc I) {e : Fin I.schemas.length} {c : Coord k ℓ} (h : MS D e c) :
    TT D e c (k + 2) = D.z (locEnd (sch I e)) ((permEnd (sch I e)).apply c) := by
  rw [TT, h, ← rt0_add_end, ← add_assoc, zmod2_self_add, zero_add]

lemma TT_succ (D : RDesc I) (e : Fin I.schemas.length) (c : Coord k ℓ) (h : ℕ) :
    TT D e c (h + 1) = TT D e c h + D.x e (h + 1) c := by
  simp [TT, msum, Finset.sum_range_succ, add_assoc]

lemma TT_zero (D : RDesc I) (e : Fin I.schemas.length) (c : Coord k ℓ) :
    TT D e c 0 = rt0 D e c := by simp [TT, msum]

/-! ### Labels -/

lemma mem_lab1 {l : RLab k ℓ} : l ∈ lab1 ↔ l.2.1 = 0 ∧ l.2.2 = 0 := by
  obtain ⟨a, b, x⟩ := l
  simp only [lab1, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, Prod.fst_zero,
    Prod.snd_zero]
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> simp

lemma mem_lab2 {l : RLab k ℓ} : l ∈ lab2 ↔ l.2.2 = 0 := by
  obtain ⟨a, b, x⟩ := l
  simp only [lab2, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, Prod.fst_zero,
    Prod.snd_zero]
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
    simp

lemma initSeed_none {v : Fin I.numLocations} (h : I.init v = none) (c : Coord k ℓ) :
    initSeed I v c = 0 := by simp [initSeed, h]

/-- The translation maps the vertices of `G₀` to those of `G₁`. -/
lemma tr_mem (D : RDesc I) (hD : InitOK D) (hM : MaskOK D) {x : ICls I × RLab k ℓ}
    (hx : x ∈ names I) : tr D x ∈ verts I 1 := by
  rw [mem_verts, one_smul]
  rw [mem_names] at hx ⊢
  obtain ⟨X, l⟩ := x
  obtain ⟨hX, hl⟩ := hx
  refine ⟨hX, ?_⟩
  simp only [tr] at hl ⊢
  cases X with
  | coord v c =>
    simp only [labs] at hl ⊢
    cases hv : I.init v with
    | some b =>
      have hz := hD v (by simp [hv])
      simp only [hv, Option.isSome_some, if_true, Finset.mem_singleton] at hl ⊢
      subst hl
      simp [rshift, off, hz, zmod2_self_add]
    | none =>
      simp only [hv, Option.isSome_none, Bool.false_eq_true, if_false, mem_lab1] at hl ⊢
      simp [rshift, off, initSeed_none hv, hl]
  | sum e c => simp only [labs, mem_lab1] at hl ⊢; simp [rshift, off, hl]
  | track e h c => simp only [labs, mem_lab1] at hl ⊢; simp [rshift, off, hl]
  | junc e c => simp only [labs, mem_lab2] at hl ⊢; simp [rshift, off, hl]
  | upd e h c => simp only [labs, mem_lab2] at hl ⊢; simp [rshift, off, hl]
  | coef e h =>
    simp only [labs, Finset.mem_image] at hl ⊢
    obtain ⟨y, hy, rfl⟩ := hl
    exact ⟨y + D.x e h, add_mem_maskSet I hy (hM e h), by simp [rshift, off]⟩
  | link e c => simp [labs] at hl

lemma tr_mem' (D : RDesc I) (hD : InitOK D) (hM : MaskOK D) {x : ICls I × RLab k ℓ}
    (hx : x ∈ verts I 1) : tr D x ∈ names I := by
  rw [mem_verts, one_smul] at hx
  rw [mem_names] at hx ⊢
  obtain ⟨X, l⟩ := x
  obtain ⟨hX, hl⟩ := hx
  refine ⟨hX, ?_⟩
  simp only [tr] at hl ⊢
  cases X with
  | coord v c =>
    simp only [labs] at hl ⊢
    cases hv : I.init v with
    | some b =>
      have hz := hD v (by simp [hv])
      simp only [hv, Option.isSome_some, if_true, Finset.mem_singleton] at hl ⊢
      have : l = (initSeed I v c, 0, 0) := by
        have := congrArg (· + ((initSeed I v c, 0, 0) : RLab k ℓ)) hl
        simpa [off, rlab_add_add_cancel] using this
      subst this
      simp [rshift, hz, zmod2_self_add]
    | none =>
      simp only [hv, Option.isSome_none, Bool.false_eq_true, if_false, mem_lab1] at hl ⊢
      simpa [rshift, off, initSeed_none hv] using hl
  | sum e c => simp only [labs, mem_lab1] at hl ⊢; simpa [rshift, off] using hl
  | track e h c => simp only [labs, mem_lab1] at hl ⊢; simpa [rshift, off] using hl
  | junc e c => simp only [labs, mem_lab2] at hl ⊢; simpa [rshift, off] using hl
  | upd e h c => simp only [labs, mem_lab2] at hl ⊢; simpa [rshift, off] using hl
  | coef e h =>
    simp only [labs, Finset.mem_image] at hl ⊢
    obtain ⟨y, hy, hyl⟩ := hl
    simp only [off, add_zero] at hyl
    subst hyl
    exact ⟨y + D.x e h, add_mem_maskSet I hy (hM e h), by simp [rshift]⟩
  | link e c => simp [labs] at hl

/-! ### Adjacency -/

/-- The conditions on a description needed at a hub class. -/
def EdgeOK (D : RDesc I) : ICls I → Prop
  | .upd e h c => 1 ≤ h ∧ h ≤ k + 2 ∧ MS D e c
  | .junc e c => isTern (sch I e) = true
  | _ => True

lemma rshift_trackCls (D : RDesc I) (e : Fin I.schemas.length) (c : Coord k ℓ) {h : ℕ}
    (hh : h ≤ k + 2) (hms : h = k + 2 → MS D e c) :
    (rshift D (trackCls I e c h)).1 = TT D e c h := by
  unfold trackCls
  split_ifs with h0 h1
  · subst h0
    rw [TT_zero]
    unfold startCls rt0
    split <;> simp_all [rshift, rt0]
  · subst h1
    rw [TT_last D (hms rfl)]
    rfl
  · rfl

lemma add_iff_of_eq {a b c d : ZMod 2} (h : c = d) : a + c = b + d ↔ a = b := by
  subst h; exact add_left_inj c

lemma hubR_tr (D : RDesc I) {X Y : ICls I} (hX : EdgeOK D X) (l m : RLab k ℓ) :
    hubR I X l Y m ↔ hubR I X (l + rshift D X) Y (m + rshift D Y) := by
  cases X with
  | upd e h c =>
    obtain ⟨h1, h2, hms⟩ := hX
    simp only [hubR]
    apply or_congr
    · apply and_congr_right
      rintro rfl
      exact (add_iff_of_eq (rshift_trackCls D e c (by omega) (by omega))).symm
    apply or_congr
    · apply and_congr_right
      rintro rfl
      exact (add_iff_of_eq (rshift_trackCls D e c h2 fun _ => hms)).symm
    · apply and_congr_right
      rintro rfl
      have hx : D.x e h c = TT D e c (h - 1) + TT D e c h := by
        obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
        rw [Nat.add_sub_cancel, TT_succ, ← add_assoc, zmod2_self_add, zero_add]
      simp only [rshift, Prod.fst_add, Prod.snd_add, Pi.add_apply]
      rw [hx, show l.1 + TT D e c (h - 1) + (l.2.1 + TT D e c h) =
        l.1 + l.2.1 + (TT D e c (h - 1) + TT D e c h) by ring]
      exact (add_iff_of_eq rfl).symm
  | junc e c =>
    simp only [hubR]
    apply or_congr
    · apply and_congr_right
      rintro rfl
      exact (add_iff_of_eq rfl).symm
    apply or_congr
    · apply and_congr_right
      rintro rfl
      exact (add_iff_of_eq rfl).symm
    · apply and_congr_right
      rintro rfl
      simp only [rshift, Prod.fst_add, Prod.snd_add, rt0, show isTern (sch I e) = true from hX,
        if_true]
      rw [show l.1 + D.z (locU (sch I e)) ((permU (sch I e)).apply c) +
        (l.2.1 + D.z (locV (sch I e)) ((permV (sch I e)).apply c)) =
        l.1 + l.2.1 + (D.z (locU (sch I e)) ((permU (sch I e)).apply c) +
          D.z (locV (sch I e)) ((permV (sch I e)).apply c)) by ring]
      exact (add_iff_of_eq rfl).symm
  | coord => simp [hubR]
  | sum => simp [hubR]
  | link => simp [hubR]
  | track => simp [hubR]
  | coef => simp [hubR]

lemma radj_tr (D : RDesc I) {x y : ICls I × RLab k ℓ} (hx : EdgeOK D x.1) (hy : EdgeOK D y.1) :
    radj I x y ↔ radj I (tr D x) (tr D y) :=
  or_congr (hubR_tr D hx _ _) (hubR_tr D hy _ _)

end Lax119563Proofs.RowSpace

end RowSpace_Shifts

/-! ### Formerly `Lax119563Proofs.RowSpace.Extension` -/

section RowSpace_Extension

/-!
# Seed descriptions and the local extension lemma

`DGood A D`: the description `D` is a seed description for the set of classes `A`
(initialized seeds, masks in the row spaces, the mask-sum condition on the pebbled schema
coordinates, partial seeds annihilating block-even codewords). `Realizes A D val`: the
description realizes the values `val` on the variables exposed for `A`.

**Local extension** (paper, Lemma "Local extension"): if `|A| ≤ k` and `val` satisfies the
equations exposed for `A ∪ {X}` and agrees with the initialization, a description realizing
`val` on `A` extends to one on `A ∪ {X}` realizing `val` and keeping the translation of every
class of `A`. No propagation rounds are involved.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler
open Lax119563Proofs.Matrix

namespace Lax119563Proofs.RowSpace

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

/-! ### Classes -/

lemma mem_ite_empty {α : Type*} {p : Prop} [Decidable p] {s : Finset α} {x : α} :
    x ∈ (if p then s else ∅) ↔ p ∧ x ∈ s := by
  split <;> simp_all

lemma mem_classes_coord {v : Fin I.numLocations} {c : Coord k ℓ} :
    (Cls.coord v c : ICls I) ∈ classes I ↔ c ∈ I.domain v := by
  simp [classes, coordClasses, schemaClasses, mem_ite_empty]

lemma mem_classes_sum {e : Fin I.schemas.length} {c : Coord k ℓ} :
    (Cls.sum e c : ICls I) ∈ classes I ↔ isTern (sch I e) = true ∧ c ∈ dom I e := by
  simp [classes, coordClasses, schemaClasses, mem_ite_empty]

lemma mem_classes_junc {e : Fin I.schemas.length} {c : Coord k ℓ} :
    (Cls.junc e c : ICls I) ∈ classes I ↔ isTern (sch I e) = true ∧ c ∈ dom I e := by
  simp [classes, coordClasses, schemaClasses, mem_ite_empty]

lemma mem_classes_track {e : Fin I.schemas.length} {h : ℕ} {c : Coord k ℓ} :
    (Cls.track e h c : ICls I) ∈ classes I ↔ (1 ≤ h ∧ h ≤ k + 1) ∧ c ∈ dom I e := by
  simp [classes, coordClasses, schemaClasses, mem_ite_empty]
  constructor
  · rintro ⟨a, b, h, rfl⟩; exact h
  · intro h; exact ⟨c.1, c.2, h, rfl⟩

lemma mem_classes_upd {e : Fin I.schemas.length} {h : ℕ} {c : Coord k ℓ} :
    (Cls.upd e h c : ICls I) ∈ classes I ↔ (1 ≤ h ∧ h ≤ k + 2) ∧ c ∈ dom I e := by
  simp [classes, coordClasses, schemaClasses, mem_ite_empty]
  constructor
  · rintro ⟨a, b, h, rfl⟩; exact h
  · intro h; exact ⟨c.1, c.2, h, rfl⟩

lemma mem_classes_coef {e : Fin I.schemas.length} {h : ℕ} :
    (Cls.coef e h : ICls I) ∈ classes I ↔ 1 ≤ h ∧ h ≤ k + 2 := by
  simp [classes, coordClasses, schemaClasses, mem_ite_empty]

lemma link_not_mem {e : Fin I.schemas.length} {c : Coord k ℓ} :
    (Cls.link e c : ICls I) ∉ classes I := by
  simp [classes, coordClasses, schemaClasses, mem_ite_empty]

lemma inner_dom {X : ICls I} (hX : X ∈ classes I) {e : Fin I.schemas.length} {c : Coord k ℓ}
    (h : Lax119563Proofs.Matrix.inner X = some (e, c)) : c ∈ dom I e := by
  cases X <;> simp only [Lax119563Proofs.Matrix.inner, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  · exact (mem_classes_sum.mp hX).2
  · exact (mem_classes_junc.mp hX).2
  · exact absurd hX link_not_mem
  · exact (mem_classes_track.mp hX).2
  · exact (mem_classes_upd.mp hX).2

lemma Isch_sub_dom {A : Finset (ICls I)} (hA : A ⊆ classes I) (e : Fin I.schemas.length) :
    Isch A e ⊆ dom I e := by
  intro c hc
  obtain ⟨X, hX, h⟩ := mem_Isch.mp hc
  exact inner_dom (hA hX) h

lemma Iloc_sub_dom {A : Finset (ICls I)} (hA : A ⊆ classes I) (v : Fin I.numLocations) :
    Iloc A v ⊆ I.domain v := by
  intro d hd0
  obtain ⟨X, hX, hd⟩ := Finset.mem_biUnion.mp hd0
  cases hi : Lax119563Proofs.Matrix.inner X with
  | some p =>
    obtain ⟨e, c⟩ := p
    rw [locContrib_of_inner hi] at hd
    obtain ⟨i, rfl, rfl⟩ := mem_argContrib.mp hd
    exact argPerm_mem (sch_wf I e) (inner_dom (hA hX) hi) i
  | none =>
    rcases inner_none hi with ⟨v', c, rfl⟩ | ⟨e, σ, rfl⟩
    · simp only [locContrib] at hd
      split at hd
      · next h => subst h; rw [Finset.mem_singleton] at hd; subst hd
                  exact mem_classes_coord.mp (hA hX)
      · simp at hd
    · simp [locContrib] at hd

/-! ### Descriptions for sets of classes -/

/-- Values of the variables `X_{v,a}`. -/
abbrev Val (I : ImplicitParitySystem k ℓ) := Fin I.numLocations × (Fin k → BlockCoord ℓ) → ZMod 2

/-- `D` is a seed description for the classes `A`. -/
structure DGood (A : Finset (ICls I)) (D : RDesc I) : Prop where
  init : InitOK D
  mask : MaskOK D
  ms : ∀ e, ∀ c ∈ Isch A e, MS D e c
  even : ∀ v, EvenKills (D.z v) (Iloc A v)

/-- `D` realizes `val` on the variables exposed for `A`. -/
def Realizes (A : Finset (ICls I)) (D : RDesc I) (val : Val I) : Prop :=
  ∀ v a, IsAddress a → supp a ⊆ Iloc A v → dot (ind a) (D.z v) = val (v, a)

/-- `val` satisfies the equations exposed for `A`. -/
def SatEqs (A : Finset (ICls I)) (val : Val I) : Prop :=
  ∀ e a, IsAddress a → supp a ⊆ Isch A e → ∑ i, val (argVar I e i a) = 0

/-- `val` agrees with the initialization on the variables exposed for `A`. -/
def InitAgree (A : Finset (ICls I)) (val : Val I) : Prop :=
  ∀ v a b, I.init v = some b → IsAddress a → supp a ⊆ Iloc A v → val (v, a) = b

lemma DGood.mono {A B : Finset (ICls I)} {D : RDesc I} (h : DGood A D) (hB : B ⊆ A) :
    DGood B D where
  init := h.init
  mask := h.mask
  ms e c hc := h.ms e c (Isch_mono hB e hc)
  even v := (h.even v).mono (Iloc_mono hB v)

lemma Realizes.mono {A B : Finset (ICls I)} {D : RDesc I} {val : Val I} (h : Realizes A D val)
    (hB : B ⊆ A) : Realizes B D val :=
  fun v a ha hs => h v a ha (hs.trans (Iloc_mono hB v))

/-- The initial description. -/
def rdesc0 (I : ImplicitParitySystem k ℓ) : RDesc I where
  z v := initSeed I v
  x _ _ := 0

lemma dgood_empty : DGood (∅ : Finset (ICls I)) (rdesc0 I) where
  init _ _ := rfl
  mask _ _ := zero_mem_maskSet I _
  ms e c hc := by simp [Isch] at hc
  even v := initSeed_evenKills v _

lemma realizes_empty (hk : 0 < k) (D : RDesc I) (val : Val I) :
    Realizes (∅ : Finset (ICls I)) D val := by
  intro v a _ hs
  exfalso
  have : (supp a).card = 0 := by
    rw [Finset.card_eq_zero]; simpa [Iloc] using hs
  rw [card_supp] at this; omega

/-! ### Translations depend only on the pebbled coordinates -/

lemma arg_mem_Iloc {A : Finset (ICls I)} {e : Fin I.schemas.length} {c : Coord k ℓ}
    (hc : c ∈ Isch A e) : (permU (sch I e)).apply c ∈ Iloc A (locU (sch I e)) ∧
      (permV (sch I e)).apply c ∈ Iloc A (locV (sch I e)) := by
  obtain ⟨i, h1, h2⟩ := exists_arg_U (sch I e)
  obtain ⟨j, h3, h4⟩ := exists_arg_V (sch I e)
  have := Isch_args hc i
  have := Isch_args hc j
  simp_all

lemma rt0_congr {D D' : RDesc I} {A : Finset (ICls I)}
    (hz : ∀ v, ∀ c ∈ Iloc A v, D'.z v c = D.z v c) {e : Fin I.schemas.length} {c : Coord k ℓ}
    (hc : c ∈ Isch A e) : rt0 D' e c = rt0 D e c := by
  simp only [rt0, hz _ _ (arg_mem_Iloc hc).1, hz _ _ (arg_mem_Iloc hc).2]

lemma bsum_congr {D D' : RDesc I} {A : Finset (ICls I)}
    (hz : ∀ v, ∀ c ∈ Iloc A v, D'.z v c = D.z v c) {e : Fin I.schemas.length} {c : Coord k ℓ}
    (hc : c ∈ Isch A e) : bsum D' e c = bsum D e c :=
  Finset.sum_congr rfl fun i _ => hz _ _ (Isch_args hc i)

lemma msum_congr {D D' : RDesc I} {e : Fin I.schemas.length} {c : Coord k ℓ}
    (hx : ∀ h, D'.x e h c = D.x e h c) (n : ℕ) : msum D' e c n = msum D e c n :=
  Finset.sum_congr rfl fun i _ => hx _

lemma rshift_congr {A : Finset (ICls I)} {D D' : RDesc I}
    (hz : ∀ v, ∀ c ∈ Iloc A v, D'.z v c = D.z v c)
    (hx : ∀ e h, ∀ c ∈ Isch A e, D'.x e h c = D.x e h c)
    (hc : ∀ e h, Cls.coef e h ∈ A → D'.x e h = D.x e h) {Y : ICls I} (hY : Y ∈ A) :
    rshift D' Y = rshift D Y := by
  have hin : ∀ e c, Lax119563Proofs.Matrix.inner Y = some (e, c) → c ∈ Isch A e :=
    fun e c h => mem_Isch.mpr ⟨Y, hY, h⟩
  cases Y with
  | coord v c =>
    have : c ∈ Iloc A v := Finset.mem_biUnion.mpr ⟨_, hY, by simp [locContrib]⟩
    simp [rshift, hz v c this]
  | sum e c => simp [rshift, rt0_congr hz (hin e c rfl)]
  | junc e c =>
    have h := arg_mem_Iloc (hin e c rfl)
    simp [rshift, hz _ _ h.1, hz _ _ h.2]
  | track e h c =>
    have h' := hin e c rfl
    simp [rshift, TT, rt0_congr hz h', msum_congr (fun h => hx e h c h')]
  | upd e h c =>
    have h' := hin e c rfl
    simp [rshift, TT, rt0_congr hz h', msum_congr (fun h => hx e h c h')]
  | coef e h => simp [rshift, hc e h hY]
  | link => rfl

/-! ### Extending one seed -/

/-- Extending the seed of one location from `J` to `J' ⊇ J` with `|J' \ J| ≤ 1`, prescribing
the values `f` on the addresses supported in `J'`. -/
lemma extend_seed_loc (hk : 0 < k) {v : Fin I.numLocations} {J J' : Finset (Coord k ℓ)}
    (hJ : J ⊆ J') (hJ1 : (J' \ J).card ≤ 1) (hcard : J'.card ≤ k + 1) {z : Vec k ℓ}
    (hz : (I.init v).isSome → z = initSeed I v) (heven : EvenKills z J)
    (f : (Fin k → BlockCoord ℓ) → ZMod 2)
    (hreal : ∀ a, IsAddress a → supp a ⊆ J → dot (ind a) z = f a)
    (hinit : ∀ a b, I.init v = some b → IsAddress a → supp a ⊆ J' → f a = b) :
    ∃ z' : Vec k ℓ, (∀ c ∈ J, z' c = z c) ∧ ((I.init v).isSome → z' = initSeed I v) ∧
      EvenKills z' J' ∧ ∀ a, IsAddress a → supp a ⊆ J' → dot (ind a) z' = f a := by
  classical
  cases hv : I.init v with
  | some b =>
    have hz' := hz (by simp [hv])
    refine ⟨z, fun _ _ => rfl, fun _ => hz', hz' ▸ initSeed_evenKills v _, fun a ha hs => ?_⟩
    rw [hz', dot_initSeed hv hk, hinit a b hv ha hs]
  | none =>
    by_cases hJJ : J' ⊆ J
    · have : J' = J := Finset.Subset.antisymm hJJ hJ
      subst this
      exact ⟨z, fun _ _ => rfl, fun h => by simp [hv] at h, heven, hreal⟩
    obtain ⟨d, hdJ', hdJ⟩ := Finset.not_subset.mp hJJ
    have hJ'eq : J' = insert d J := by
      refine Finset.Subset.antisymm (fun c hc => ?_) (Finset.insert_subset hdJ' hJ)
      by_cases hcJ : c ∈ J
      · exact Finset.mem_insert_of_mem hcJ
      · have h1 : c ∈ J' \ J := Finset.mem_sdiff.mpr ⟨hc, hcJ⟩
        have h2 : d ∈ J' \ J := Finset.mem_sdiff.mpr ⟨hdJ', hdJ⟩
        rw [Finset.card_le_one.mp hJ1 c h1 d h2]
        exact Finset.mem_insert_self _ _
    subst hJ'eq
    let p : ZMod 2 := if h : ∃ a, IsAddress a ∧ supp a ⊆ insert d J ∧ d ∈ supp a
      then f h.choose else 0
    obtain ⟨β, hβ1, hβ2⟩ := extend_seed hk hdJ hcard heven p
    have hagree : ∀ c ∈ J, Function.update z d β c = z c :=
      fun c hc => Function.update_of_ne (fun h => hdJ (by rw [← h]; exact hc)) _ _
    refine ⟨Function.update z d β, hagree, fun h => by simp [hv] at h, hβ1, fun a ha hs => ?_⟩
    by_cases hda : d ∈ supp a
    · have hex : ∃ a, IsAddress a ∧ supp a ⊆ insert d J ∧ d ∈ supp a := ⟨a, ha, hs, hda⟩
      rw [hβ2 a ha hs hda]
      simp only [p, dif_pos hex]
      rw [address_unique hex.choose_spec.1 ha hcard hex.choose_spec.2.1 hs]
    · have hsJ : supp a ⊆ J := fun c hc => by
        rcases Finset.mem_insert.mp (hs hc) with rfl | h
        · exact absurd hc hda
        · exact h
      rw [dot_congr_suppIn (suppIn_ind.mpr hsJ) (z' := z) hagree]
      exact hreal a ha hsJ

/-! ### Exposed equations -/

lemma maskSet_dot {e : Fin I.schemas.length} {x : Vec k ℓ} (hx : x ∈ maskSet I e) (hk : 0 < k)
    {a : Fin k → BlockCoord ℓ} (ha : IsAddress a) (hs : supp a ⊆ dom I e) :
    dot (ind a) x = 0 := by
  obtain ⟨μ, -, rfl⟩ := Finset.mem_image.mp hx
  rw [dot_ind_left]
  have : ∀ i, maskOf I e μ (i, a i) = ∑ j, μ j * checkMatrix k ℓ j (i, a i) := fun i => by
    have hi : ((i, a i) : Coord k ℓ) ∈ dom I e :=
      hs ((mem_supp_iff (a := a) (c := (i, a i))).mpr rfl)
    simp only [maskOf, if_pos hi]
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← Finset.mul_sum, sum_row_supp hk ha, mul_zero]

/-- The sum of the argument values at an address equals its sum of `bsum`. -/
lemma sum_args_dot (D : RDesc I) (e : Fin I.schemas.length) (a : Fin k → BlockCoord ℓ) :
    ∑ i, dot (ind ((argPerm (sch I e) i).act a)) (D.z (argLoc (sch I e) i)) =
      dot (ind a) (bsum D e) := by
  simp_rw [dot_ind_act, dot_ind_left, bsum]
  exact Finset.sum_comm

/-- A description satisfies the equations of the addresses at which the mask-sum condition
holds. -/
lemma eq_of_MS (hk : 0 < k) {D : RDesc I} (hM : MaskOK D) {e : Fin I.schemas.length}
    {a : Fin k → BlockCoord ℓ} (ha : IsAddress a) (hs : supp a ⊆ dom I e)
    (hms : ∀ c ∈ supp a, MS D e c) :
    ∑ i, dot (ind ((argPerm (sch I e) i).act a)) (D.z (argLoc (sch I e) i)) = 0 := by
  rw [sum_args_dot, dot_ind_eq_sum_supp]
  rw [Finset.sum_congr rfl fun c hc => (hms c hc).symm]
  simp only [msum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← dot_ind_eq_sum_supp]
  exact maskSet_dot (hM e _) hk ha hs

/-- Realized values satisfy the equations exposed for `A`. -/
lemma Realizes.sat (hk : 0 < k) {A : Finset (ICls I)} {D : RDesc I} {val : Val I}
    (hG : DGood A D) (hA : A ⊆ classes I) (hR : Realizes A D val) : SatEqs A val := by
  intro e a ha hs
  rw [← eq_of_MS hk hG.mask ha (hs.trans (Isch_sub_dom hA e)) fun c hc => hG.ms e c (hs hc)]
  refine Finset.sum_congr rfl fun i _ => (hR _ _ (isAddress_act _ ha) ?_).symm
  rw [supp_act]
  intro d hd
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hd
  exact Isch_args (hs hc) i

/-! ### The mask repair -/

lemma isCode_even_or_odd (hk : 0 < k) {y : Vec k ℓ} (hy : IsCode y) :
    (∀ i, blockSum y i = 0) ∨ ∀ i, blockSum y i = 1 := by
  rcases zmod2_eq_zero_or_one (blockSum y ⟨0, hk⟩) with h | h
  · exact Or.inl fun i => (hy.blockSum_eq hk i ⟨0, hk⟩).trans h
  · exact Or.inr fun i => (hy.blockSum_eq hk i ⟨0, hk⟩).trans h

/-- `bsum` of the extended seeds is orthogonal to every codeword supported in the new schema
coordinate set. -/
lemma bsum_orth (hk : 0 < k) {A' : Finset (ICls I)} {D : RDesc I} {val : Val I}
    (heven : ∀ v, EvenKills (D.z v) (Iloc A' v)) (hR : Realizes A' D val) (hsat : SatEqs A' val)
    (e : Fin I.schemas.length) (hcard : (Isch A' e).card ≤ k + 1) :
    ∀ y, IsCode y → SuppIn y (Isch A' e) → dot y (bsum D e) = 0 := by
  intro y hy hs
  rcases isCode_even_or_odd hk hy with he | ho
  · have : dot y (bsum D e) =
        ∑ i, dot (permVec (argPerm (sch I e) i) y) (D.z (argLoc (sch I e) i)) := by
      simp_rw [dot_permVec, dot, bsum, Finset.mul_sum]
      exact Finset.sum_comm
    rw [this]
    refine Finset.sum_eq_zero fun i _ => heven _ _ (isCode_permVec hk _ hy)
      (fun i' => by rw [blockSum_permVec', he]) ?_
    intro d hd
    apply suppIn_permVec _ hs
    intro hd'
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hd'
    exact hd (Isch_args hc i)
  · obtain ⟨a, ha, rfl⟩ := exists_address_of_odd hk hy ho hs hcard
    have hsa := suppIn_ind.mp hs
    rw [← sum_args_dot, ← hsat e a ha hsa]
    refine Finset.sum_congr rfl fun i _ => hR _ _ (isAddress_act _ ha) ?_
    rw [supp_act]
    intro d hd
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hd
    exact Isch_args (hsa hc) i

/-- A mask in the row space correcting the mask sum at the new coordinate. -/
lemma exists_gamma {e : Fin I.schemas.length} {J : Finset (Coord k ℓ)} {c : Coord k ℓ}
    (hJ : insert c J ⊆ dom I e) {D : RDesc I} (hM : MaskOK D)
    (hms : ∀ c' ∈ J, MS D e c')
    (horth : ∀ y, IsCode y → SuppIn y (insert c J) → dot y (bsum D e) = 0) :
    ∃ γ ∈ maskSet I e, (∀ c' ∈ J, γ c' = 0) ∧ γ c = bsum D e c + msum D e c (k + 2) := by
  obtain ⟨μ, hμ⟩ := exists_rowComb (insert c J) (bsum D e) horth
  let xs : Vec k ℓ := ∑ i ∈ Finset.range (k + 2), D.x e (i + 1)
  have hxs : xs ∈ maskSet I e := by
    simp only [xs]
    induction (k + 2) with
    | zero => simpa using zero_mem_maskSet I e
    | succ n ih => rw [Finset.sum_range_succ]; exact add_mem_maskSet I ih (hM e _)
  have hxs_apply : ∀ c', xs c' = msum D e c' (k + 2) := fun c' => by
    simp [xs, msum, Finset.sum_apply]
  have hmask : ∀ c' ∈ insert c J, maskOf I e μ c' = bsum D e c' := fun c' hc' => by
    simp [maskOf, hJ hc', hμ c' hc']
  refine ⟨maskOf I e μ + xs, add_mem_maskSet I (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    hxs, fun c' hc' => ?_, ?_⟩
  · rw [Pi.add_apply, hmask c' (Finset.mem_insert_of_mem hc'), hxs_apply, hms c' hc',
      zmod2_self_add]
  · rw [Pi.add_apply, hmask c (Finset.mem_insert_self _ _), hxs_apply]

/-- Some stage of `e` has no pebbled mask class. -/
lemma exists_free_stage {A : Finset (ICls I)} (hcard : A.card ≤ k) (e : Fin I.schemas.length) :
    ∃ h, 1 ≤ h ∧ h ≤ k + 2 ∧ Cls.coef e h ∉ A := by
  by_contra hno
  push Not at hno
  have hsub : (Finset.Icc 1 (k + 2)).image (Cls.coef e) ⊆ A := by
    intro X hX
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hh
    exact hno h h1 h2
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (fun a b h => by cases h; rfl)] at this
  simp at this
  omega

/-! ### Local extension -/

lemma card_Iloc_insert (A : Finset (ICls I)) (X : ICls I) (v : Fin I.numLocations) :
    (Iloc (insert X A) v \ Iloc A v).card ≤ 1 := by
  rw [Iloc_insert]
  refine (Finset.card_le_card fun d hd => ?_).trans (card_locContrib_le X v)
  rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hd).1 with h | h
  · exact h
  · exact absurd h (Finset.mem_sdiff.mp hd).2

/-- **Local extension.** -/
theorem local_extend (hk : 2 ≤ k) {A : Finset (ICls I)} {X : ICls I} {D : RDesc I}
    (hG : DGood A D) (hA : A ⊆ classes I) (hX : X ∈ classes I) (hcard : A.card ≤ k)
    (val : Val I) (hreal : Realizes A D val) (hsat : SatEqs (insert X A) val)
    (hinit : InitAgree (insert X A) val) :
    ∃ D', DGood (insert X A) D' ∧ Realizes (insert X A) D' val ∧
      ∀ Y ∈ A, rshift D' Y = rshift D Y := by
  classical
  have hk0 : 0 < k := by omega
  have hA' : insert X A ⊆ classes I := Finset.insert_subset hX hA
  have hcard' : (insert X A).card ≤ k + 1 := (Finset.card_insert_le _ _).trans (by omega)
  -- seeds
  have hseed := fun v => extend_seed_loc (I := I) (v := v) hk0 (Iloc_mono (Finset.subset_insert X A) v)
    (card_Iloc_insert A X v) ((card_Iloc_le _ v).trans hcard') (hG.init v) (hG.even v)
    (fun a => val (v, a)) (fun a ha hs => hreal v a ha hs) (fun a b hb ha hs => hinit v a b hb ha hs)
  choose z' hz1 hz2 hz3 hz4 using hseed
  let D1 : RDesc I := ⟨z', D.x⟩
  have hD1init : InitOK D1 := fun v hv => hz2 v hv
  have hR1 : Realizes (insert X A) D1 val := fun v a ha hs => hz4 v a ha hs
  -- old mask-sum conditions survive the seed extension
  have hms1 : ∀ e, ∀ c ∈ Isch A e, MS D1 e c := fun e c hc => by
    have := hG.ms e c hc
    simp only [MS] at this ⊢
    rw [bsum_congr (D := D) (D' := D1) hz1 hc]
    exact this
  -- does `X` add a new schema coordinate?
  by_cases hnew : ∃ e c, Lax119563Proofs.Matrix.inner X = some (e, c) ∧ c ∉ Isch A e
  · obtain ⟨e, c, hXi, hcA⟩ := hnew
    have hIsch : ∀ e', Isch (insert X A) e' = if e = e' then insert c (Isch A e') else Isch A e' := by
      intro e'
      rw [Isch_insert, schContrib_of_inner hXi]
      by_cases he : e = e'
      · subst he; rw [if_pos rfl, if_pos rfl, Finset.insert_eq]
      · rw [if_neg he, if_neg he, Finset.empty_union]
    have hJe : Isch (insert X A) e = insert c (Isch A e) := by rw [hIsch e, if_pos rfl]
    obtain ⟨γ, hγ, hγ0, hγc⟩ := exists_gamma (D := D1) (c := c) (J := Isch A e)
      (hJe ▸ Isch_sub_dom hA' e) hG.mask (hms1 e)
      (hJe ▸ bsum_orth hk0 hz3 hR1 hsat e (hJe ▸ (card_Isch_le _ e).trans hcard'))
    obtain ⟨h₀, h₀1, h₀2, h₀A⟩ := exists_free_stage hcard e
    let x' : Fin I.schemas.length → ℕ → Vec k ℓ :=
      Function.update D.x e (Function.update (D.x e) h₀ (D.x e h₀ + γ))
    let D' : RDesc I := ⟨z', x'⟩
    have hx'e : ∀ h c', x' e h c' = D.x e h c' + if h = h₀ then γ c' else 0 := by
      intro h c'
      by_cases hh : h = h₀
      · subst hh; simp [x']
      · simp [x', hh]
    have hx'ne : ∀ e', e' ≠ e → x' e' = D.x e' := fun e' he => by simp [x', he]
    have hmsum : ∀ c', msum D' e c' (k + 2) = msum D e c' (k + 2) + γ c' := by
      intro c'
      simp only [msum, D', hx'e, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single (h₀ - 1) (fun b _ hb => by rw [if_neg (by omega)])
        (fun h => by simp at h; omega), if_pos (by omega)]
    refine ⟨D', ⟨hD1init, fun e' h => ?_, fun e' c' hc' => ?_, hz3⟩, hR1, fun Y hY => ?_⟩
    · show x' e' h ∈ maskSet I e'
      by_cases he : e' = e
      · subst he
        by_cases hh : h = h₀
        · subst hh; simp only [x', Function.update_self]
          exact add_mem_maskSet I (hG.mask _ _) hγ
        · simp only [x', Function.update_self, Function.update_of_ne hh]; exact hG.mask _ _
      · rw [hx'ne e' he]; exact hG.mask _ _
    · rw [hIsch e'] at hc'
      by_cases he : e = e'
      · subst he
        rw [if_pos rfl] at hc'
        simp only [MS, hmsum]
        show _ = bsum D1 e c'
        rcases Finset.mem_insert.mp hc' with rfl | hc'
        · rw [hγc, ← add_assoc, show msum D e c' (k + 2) = msum D1 e c' (k + 2) from rfl,
            add_comm (msum D1 e c' (k + 2)), add_assoc, zmod2_self_add, add_zero]
        · rw [hγ0 c' hc', add_zero]
          exact hms1 e c' hc'
      · rw [if_neg he] at hc'
        have := hms1 e' c' hc'
        simp only [MS] at this ⊢
        rw [msum_congr (D := D1) (D' := D') (fun h => by simp [D', hx'ne e' (Ne.symm he), D1])]
        exact this
    · refine rshift_congr hz1 (fun e' h c' hc' => ?_) (fun e' h hc => ?_) hY
      · by_cases he : e' = e
        · subst he; show x' e' h c' = _; rw [hx'e, hγ0 c' hc']; simp
        · simp [D', hx'ne e' he]
      · by_cases he : e' = e
        · subst he
          have hh : h ≠ h₀ := fun hh => h₀A (hh ▸ hc)
          simp [D', x', hh]
        · simp [D', hx'ne e' he]
  · push Not at hnew
    have hIsch : ∀ e', Isch (insert X A) e' = Isch A e' := by
      intro e'
      rw [Isch_insert]
      cases hXi : Lax119563Proofs.Matrix.inner X with
      | none => rw [schContrib_of_inner_none hXi]; simp
      | some p =>
        obtain ⟨e, c⟩ := p
        rw [schContrib_of_inner hXi]
        split
        · next he => subst he; simp [hnew e c hXi]
        · simp
    refine ⟨D1, ⟨hD1init, hG.mask, fun e c hc => hms1 e c (hIsch e ▸ hc), hz3⟩, hR1,
      fun Y hY => rshift_congr (D := D) (D' := D1) hz1 (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) hY⟩

end Lax119563Proofs.RowSpace

end RowSpace_Extension

/-! ### Formerly `Lax119563Proofs.RowSpace.Duplicator` -/

section RowSpace_Duplicator

/-!
# Duplicator's strategy on the row-space graphs

Duplicator maintains a seed description `D` for the pebbled classes whose realized values agree
with `K_r` (`r` rounds remaining); the pebble pairs follow the translation `tr D`. After a lift,
for every class `X` the description is extended to `X` by the local extension lemma, after
choosing values for the newly exposed variables consistent with `K_{r-1}`.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ParitySystems
open Lax119563.ColoredGraphs Lax119563.PebbleGame
open Lax119563Proofs.Matrix

namespace Lax119563Proofs.RowSpace

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

/-! ### Agreement with known facts -/

/-- The values realized by `D` on the variables exposed for `A` agree with `K_r`. -/
def Agree (r : ℕ) (A : Finset (ICls I)) (D : RDesc I) : Prop :=
  ∀ v a b, IsAddress a → supp a ⊆ Iloc A v →
    ((v, a), b) ∈ I.toParitySystem.known r → dot (ind a) (D.z v) = b

lemma Agree.mono {r r' : ℕ} {A B : Finset (ICls I)} {D : RDesc I} (h : Agree r A D)
    (hr : r' ≤ r) (hB : B ⊆ A) : Agree r' B D :=
  fun v a b ha hs hb => h v a b ha (hs.trans (Iloc_mono hB v)) (known_mono I hr hb)

lemma agree_empty (hk : 0 < k) (r : ℕ) (D : RDesc I) : Agree r (∅ : Finset (ICls I)) D := by
  intro v a b _ hs _
  exfalso
  have : (supp a).card = 0 := by
    rw [Finset.card_eq_zero]; simpa [Iloc] using hs
  rw [card_supp] at this; omega

/-! ### Values for the newly exposed equation -/

/-- **Extending exposed values** (row-space version of `choose_values`): values for the
variables newly exposed at the argument locations, consistent with `K_r` and with the newly
exposed equation. -/
lemma choose_vals_rs {r : ℕ} {A : Finset (ICls I)} {D : RDesc I} (hag : Agree (r + 1) A D)
    (hnc1 : ¬ I.toParitySystem.HasConflict (r + 1)) (hA : A ⊆ classes I)
    (hcard : A.card ≤ k) (e : Fin I.schemas.length) {c : Coord k ℓ} (hc : c ∉ Isch A e)
    (hcd : c ∈ dom I e) :
    ∃ p : Fin (arity (sch I e)) → ZMod 2,
      (∀ i a b, IsAddress a →
        supp a ⊆ insert ((argPerm (sch I e) i).apply c) (Iloc A (argLoc (sch I e) i)) →
        (argPerm (sch I e) i).apply c ∈ supp a →
        (argPerm (sch I e) i).apply c ∉ Iloc A (argLoc (sch I e) i) →
        ((argLoc (sch I e) i, a), b) ∈ I.toParitySystem.known r → p i = b) ∧
      (∀ a, IsAddress a → supp a ⊆ insert c (Isch A e) → c ∈ supp a →
        ∑ i, (if (argPerm (sch I e) i).apply c ∈ Iloc A (argLoc (sch I e) i) then
          dot (ind ((argPerm (sch I e) i).act a)) (D.z (argLoc (sch I e) i)) else p i) = 0) := by
  classical
  set s := sch I e
  set L := argLoc s
  set P := argPerm s
  set d : Fin (arity s) → Coord k ℓ := fun i => (P i).apply c
  set J : Fin (arity s) → Finset (Coord k ℓ) := fun i => Iloc A (L i)
  have hnc : ¬ I.toParitySystem.HasConflict r :=
    fun h => hnc1 (hasConflict_mono I (Nat.le_succ r) h)
  -- facts about new addresses
  let NewFact : Fin (arity s) → ZMod 2 → Prop := fun i b => ∃ a, IsAddress a ∧
    supp a ⊆ insert (d i) (J i) ∧ d i ∈ supp a ∧ ((L i, a), b) ∈ I.toParitySystem.known r
  have hnf_unique : ∀ i b b', NewFact i b → NewFact i b' → b = b' := by
    rintro i b b' ⟨a, ha, hs, -, hb⟩ ⟨a', ha', hs', -, hb'⟩
    have := address_unique ha ha' (card_insert_Iloc hcard _ _) hs hs'
    subst this
    exact fact_unique hnc hb hb'
  let p0 : Fin (arity s) → ZMod 2 := fun i => if h : ∃ b, NewFact i b then h.choose else 0
  have hp0 : ∀ i b, NewFact i b → p0 i = b := by
    intro i b hb
    have h : ∃ b, NewFact i b := ⟨b, hb⟩
    simp only [p0, dif_pos h]
    exact hnf_unique i _ _ h.choose_spec hb
  have hP1 : ∀ p : Fin (arity s) → ZMod 2, (∀ i, (∃ b, NewFact i b) → p i = p0 i) →
      ∀ i a b, IsAddress a → supp a ⊆ insert (d i) (J i) → d i ∈ supp a → d i ∉ J i →
        ((L i, a), b) ∈ I.toParitySystem.known r → p i = b := by
    intro p hp i a b ha hs hda _ hb
    have hnf : NewFact i b := ⟨a, ha, hs, hda, hb⟩
    rw [hp i ⟨b, hnf⟩, hp0 i b hnf]
  by_cases hex : ∃ a, IsAddress a ∧ supp a ⊆ insert c (Isch A e) ∧ c ∈ supp a
  swap
  · push Not at hex
    exact ⟨p0, hP1 p0 fun _ _ => rfl, fun a ha hs hca => absurd hca (hex a ha hs)⟩
  obtain ⟨a, ha, hsa, hca⟩ := hex
  have hJcard := card_insert_Isch hcard e c
  have hdom : insert c (Isch A e) ⊆ dom I e :=
    Finset.insert_subset hcd (Isch_sub_dom hA e)
  -- the only address of the newly exposed equation
  have huniq : ∀ a', IsAddress a' → supp a' ⊆ insert c (Isch A e) → a' = a :=
    fun a' ha' hs' => address_unique ha' ha hJcard hs' hsa
  have hsi : ∀ i, supp ((P i).act a) ⊆ insert (d i) (J i) := fun i => supp_arg_subset hsa i
  have hai : ∀ i, IsAddress ((P i).act a) := fun i => isAddress_act _ ha
  -- old variables are covered by the old coordinate set
  have hold_supp : ∀ i, d i ∈ J i → supp ((P i).act a) ⊆ J i := by
    intro i hi
    have := hsi i
    rwa [Finset.insert_eq_of_mem hi] at this
  -- at most one argument variable was exposed before
  have hone : ∀ i j, i ≠ j → d i ∈ J i → d j ∈ J j → False := by
    intro i j hij hi hj
    exact hc (geometry hcard e hij (hold_supp i hi) (hold_supp j hj) hca)
  -- a fact at a new location is a fact about the equation's variable
  have hnf_eq : ∀ i b, NewFact i b → ((L i, (P i).act a), b) ∈ I.toParitySystem.known r := by
    rintro i b ⟨a', ha', hs', -, hb⟩
    have := address_unique ha' (hai i) (card_insert_Iloc hcard _ _) hs' (hsi i)
    rwa [this] at hb
  let val : (Fin (arity s) → ZMod 2) → Fin (arity s) → ZMod 2 := fun p i =>
    if d i ∈ J i then dot (ind ((P i).act a)) (D.z (L i)) else p i
  have hP2 : ∀ p : Fin (arity s) → ZMod 2, ∑ i, val p i = 0 →
      ∀ a', IsAddress a' → supp a' ⊆ insert c (Isch A e) → c ∈ supp a' →
        ∑ i, (if d i ∈ J i then dot (ind ((P i).act a')) (D.z (L i)) else p i) = 0 := by
    intro p hp a' ha' hs' _
    rw [huniq a' ha' hs']
    exact hp
  by_cases hfree : ∃ i₀, d i₀ ∉ J i₀ ∧ ¬ ∃ b, NewFact i₀ b
  · obtain ⟨i₀, hi₀, hnf₀⟩ := hfree
    let p := Function.update p0 i₀ (∑ i ∈ Finset.univ.erase i₀, val p0 i)
    refine ⟨p, hP1 p fun i hi => ?_, hP2 p ?_⟩
    · have : i ≠ i₀ := by rintro rfl; exact hnf₀ hi
      simp [p, Function.update_of_ne this]
    · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
      have h1 : val p i₀ = ∑ i ∈ Finset.univ.erase i₀, val p0 i := by
        simp [val, hi₀, p]
      have h2 : ∑ i ∈ Finset.univ.erase i₀, val p i = ∑ i ∈ Finset.univ.erase i₀, val p0 i :=
        Finset.sum_congr rfl fun i hi => by
          simp [val, p, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      rw [h1, h2, zmod2_add_self]
  · push Not at hfree
    refine ⟨p0, hP1 p0 fun _ _ => rfl, hP2 p0 ?_⟩
    -- every new variable has a fact in `K_r`
    have hfacts : ∀ i, d i ∉ J i → ((L i, (P i).act a), p0 i) ∈ I.toParitySystem.known r := by
      intro i hi
      obtain ⟨b, hb⟩ := hfree i hi
      rw [hp0 i b hb]
      exact hnf_eq i b hb
    by_cases hold : ∃ i₁, d i₁ ∈ J i₁
    · obtain ⟨i₁, hi₁⟩ := hold
      have hnew : ∀ i, i ≠ i₁ → d i ∉ J i := fun i hi h => hone i i₁ hi h hi₁
      have hinf := infer I e ha (hsa.trans hdom) i₁ (val p0)
        (r := r) fun i hi => by
          simp only [val, if_neg (hnew i hi)]
          exact hfacts i (hnew i hi)
      have hval := hag (L i₁) _ _ (hai i₁) (hold_supp i₁ hi₁) hinf
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₁)]
      have : val p0 i₁ = dot (ind ((P i₁).act a)) (D.z (L i₁)) := by simp [val, hi₁]
      rw [this, hval, zmod2_add_self]
    · push Not at hold
      let i₀ : Fin (arity s) := ⟨0, arity_pos s⟩
      have hinf := infer I e ha (hsa.trans hdom) i₀ (val p0) (r := r) fun i _ => by
        simp only [val, if_neg (hold i)]
        exact hfacts i (hold i)
      have h0 : ((L i₀, (P i₀).act a), val p0 i₀) ∈ I.toParitySystem.known (r + 1) := by
        simp only [val, if_neg (hold i₀)]
        exact known_mono I (Nat.le_succ r) (hfacts i₀ (hold i₀))
      have := fact_unique hnc1 hinf h0
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), ← this, zmod2_add_self]

/-! ### Choosing values -/

lemma mem_Isch_insert {X : ICls I} {A : Finset (ICls I)} {e : Fin I.schemas.length}
    {c : Coord k ℓ} :
    c ∈ Isch (insert X A) e ↔ Lax119563Proofs.Matrix.inner X = some (e, c) ∨ c ∈ Isch A e := by
  rw [mem_Isch, mem_Isch]
  simp only [Finset.mem_insert, exists_eq_or_imp]

/-- The values realized by `D` on the variables exposed for `A`, and `q` elsewhere. -/
def mkVal (A : Finset (ICls I)) (D : RDesc I) (q : Val I) : Val I := fun x =>
  if supp x.2 ⊆ Iloc A x.1 then dot (ind x.2) (D.z x.1) else q x

lemma mkVal_argVar (A : Finset (ICls I)) (D : RDesc I) (q : Val I) (e : Fin I.schemas.length)
    (i : Fin (arity (sch I e))) (a : Fin k → BlockCoord ℓ) :
    mkVal A D q (argVar I e i a) =
      if supp ((argPerm (sch I e) i).act a) ⊆ Iloc A (argLoc (sch I e) i) then
        dot (ind ((argPerm (sch I e) i).act a)) (D.z (argLoc (sch I e) i))
      else q (argVar I e i a) := rfl

lemma mkVal_props (hk : 0 < k) {r : ℕ} {A : Finset (ICls I)} {D : RDesc I} {X : ICls I}
    (hG : DGood A D) (hA : A ⊆ classes I) (hX : X ∈ classes I) (hag : Agree (r + 1) A D)
    (q : Val I)
    (hq1 : ∀ v a b, IsAddress a → supp a ⊆ Iloc (insert X A) v → ¬ supp a ⊆ Iloc A v →
      ((v, a), b) ∈ I.toParitySystem.known r → q (v, a) = b)
    (hq2 : ∀ e a, IsAddress a → supp a ⊆ Isch (insert X A) e → ¬ supp a ⊆ Isch A e →
      ∑ i, mkVal A D q (argVar I e i a) = 0) :
    Realizes A D (mkVal A D q) ∧ SatEqs (insert X A) (mkVal A D q) ∧
      InitAgree (insert X A) (mkVal A D q) ∧
      ∀ v a b, IsAddress a → supp a ⊆ Iloc (insert X A) v →
        ((v, a), b) ∈ I.toParitySystem.known r → mkVal A D q (v, a) = b := by
  classical
  have hR : Realizes A D (mkVal A D q) := fun v a _ hs => by simp only [mkVal, if_pos hs]
  have hK : ∀ v a b, IsAddress a → supp a ⊆ Iloc (insert X A) v →
      ((v, a), b) ∈ I.toParitySystem.known r → mkVal A D q (v, a) = b := by
    intro v a b ha hs hb
    by_cases ho : supp a ⊆ Iloc A v
    · simp only [mkVal, if_pos ho]
      exact hag v a b ha ho (known_mono I (Nat.le_succ r) hb)
    · simp only [mkVal, if_neg ho]
      exact hq1 v a b ha hs ho hb
  refine ⟨hR, fun e a ha hs => ?_, fun v a b hv ha hs => ?_, hK⟩
  · by_cases ho : supp a ⊆ Isch A e
    · exact Realizes.sat hk hG hA hR e a ha ho
    · exact hq2 e a ha hs ho
  · have h0 : ((v, a), b) ∈ I.toParitySystem.known 0 :=
      ⟨b, hv, rfl, ha, hs.trans (Iloc_sub_dom (Finset.insert_subset hX hA) v)⟩
    exact hK v a b ha hs (known_mono I (Nat.zero_le r) h0)

/-- **Value choice.** Given a seed description of `A` whose realized values agree with
`K_{r+1}`, and a class `X`, there are values realizing `D` on `A`, satisfying the equations
and the initialization exposed for `A ∪ {X}`, and agreeing with `K_r` on the variables exposed
for `A ∪ {X}`. -/
theorem choose_val (hk : 0 < k) {r : ℕ} {A : Finset (ICls I)} {D : RDesc I} (hG : DGood A D)
    (hA : A ⊆ classes I) (hcard : A.card ≤ k) (hag : Agree (r + 1) A D)
    (hnc1 : ¬ I.toParitySystem.HasConflict (r + 1)) {X : ICls I} (hX : X ∈ classes I) :
    ∃ val : Val I, Realizes A D val ∧ SatEqs (insert X A) val ∧ InitAgree (insert X A) val ∧
      ∀ v a b, IsAddress a → supp a ⊆ Iloc (insert X A) v →
        ((v, a), b) ∈ I.toParitySystem.known r → val (v, a) = b := by
  classical
  have hnc : ¬ I.toParitySystem.HasConflict r :=
    fun h => hnc1 (hasConflict_mono I (Nat.le_succ r) h)
  let kr : Val I := fun x => if h : ∃ b, (x, b) ∈ I.toParitySystem.known r then h.choose else 0
  have hkr : ∀ x b, (x, b) ∈ I.toParitySystem.known r → kr x = b := by
    intro x b hb
    have h : ∃ b, (x, b) ∈ I.toParitySystem.known r := ⟨b, hb⟩
    simp only [kr, dif_pos h]
    exact fact_unique hnc h.choose_spec hb
  -- a newly exposed equation contains the schema coordinate of `X`
  have hnewc : ∀ e a, supp a ⊆ Isch (insert X A) e → ¬ supp a ⊆ Isch A e →
      ∃ c, Lax119563Proofs.Matrix.inner X = some (e, c) ∧ c ∉ Isch A e ∧
        supp a ⊆ insert c (Isch A e) ∧ c ∈ supp a := by
    intro e a hs ho
    obtain ⟨c, hca, hcA⟩ := Finset.not_subset.mp ho
    have hXc : Lax119563Proofs.Matrix.inner X = some (e, c) :=
      (mem_Isch_insert.mp (hs hca)).resolve_right hcA
    refine ⟨c, hXc, hcA, fun c' hc' => ?_, hca⟩
    rcases mem_Isch_insert.mp (hs hc') with h | h
    · rw [hXc] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem h
  by_cases hnew : ∃ e c a, Lax119563Proofs.Matrix.inner X = some (e, c) ∧ c ∉ Isch A e ∧
      IsAddress a ∧ supp a ⊆ insert c (Isch A e) ∧ c ∈ supp a
  · obtain ⟨e, c, a, hXc, hcA, ha, hsa, hca⟩ := hnew
    have hcd : c ∈ dom I e := inner_dom hX hXc
    obtain ⟨p, hp1, hp2⟩ := choose_vals_rs hag hnc1 hA hcard e hcA hcd
    let q : Val I := fun x => if h : ∃ i, argVar I e i a = x then p h.choose else kr x
    have hqi : ∀ i, q (argVar I e i a) = p i := by
      intro i
      have h : ∃ i', argVar I e i' a = argVar I e i a := ⟨i, rfl⟩
      simp only [q, dif_pos h]
      rw [argVar_injective I e a h.choose_spec]
    refine ⟨mkVal A D q, mkVal_props hk hG hA hX hag q ?_ ?_⟩
    · intro v a' b ha' hs ho hb
      by_cases hi : ∃ i, argVar I e i a = (v, a')
      · obtain ⟨i, hi⟩ := hi
        rw [← hi, hqi]
        simp only [argVar, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        refine hp1 i _ b ha' (supp_arg_subset hsa i) (mem_supp_arg hca i) (fun hd => ho ?_) hb
        have := supp_arg_subset hsa i
        rwa [Finset.insert_eq_of_mem hd] at this
      · simp only [q, dif_neg hi]
        exact hkr _ b hb
    · intro e' a' ha' hs ho
      obtain ⟨c', hXc', hc'A, hs', hc'a⟩ := hnewc e' a' hs ho
      rw [hXc] at hXc'
      simp only [Option.some.injEq, Prod.mk.injEq] at hXc'
      obtain ⟨rfl, rfl⟩ := hXc'
      have : a' = a := address_unique ha' ha (card_insert_Isch hcard e c) hs' hsa
      subst this
      rw [← hp2 a' ha' hsa hca]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mkVal_argVar, hqi]
      by_cases hd : (argPerm (sch I e) i).apply c ∈ Iloc A (argLoc (sch I e) i)
      · have hsub : supp ((argPerm (sch I e) i).act a') ⊆ Iloc A (argLoc (sch I e) i) := by
          have := supp_arg_subset hsa i
          rwa [Finset.insert_eq_of_mem hd] at this
        rw [if_pos hd, if_pos hsub]
      · rw [if_neg hd, if_neg fun h => hd (h (mem_supp_arg hca i))]
  · refine ⟨mkVal A D kr, mkVal_props hk hG hA hX hag kr (fun v a b _ _ _ hb => hkr _ b hb) ?_⟩
    intro e a ha hs ho
    obtain ⟨c, hXc, hcA, hs', hca⟩ := hnewc e a hs ho
    exact absurd ⟨e, c, a, hXc, hcA, ha, hs', hca⟩ hnew

/-- **Extension by one class**, consistent with `K_r`. -/
theorem extend_cls (hk : 2 ≤ k) {r : ℕ} {A : Finset (ICls I)} {D : RDesc I} (hG : DGood A D)
    (hA : A ⊆ classes I) (hcard : A.card ≤ k) (hag : Agree (r + 1) A D)
    (hnc1 : ¬ I.toParitySystem.HasConflict (r + 1)) {X : ICls I} (hX : X ∈ classes I) :
    ∃ D', DGood (insert X A) D' ∧ Agree r (insert X A) D' ∧
      ∀ Y ∈ A, rshift D' Y = rshift D Y := by
  obtain ⟨val, hR, hsat, hinit, hK⟩ := choose_val (by omega) hG hA hcard hag hnc1 hX
  obtain ⟨D', hG', hR', hsh⟩ := local_extend hk hG hA hX hcard val hR hsat hinit
  exact ⟨D', hG', fun v a b ha hs hb => (hR' v a ha hs).trans (hK v a b ha hs hb), hsh⟩

/-! ### Game states -/

lemma vx_mem_names (p : Fin (rsGraph I 0).n) : vx p ∈ names I := by
  have := vx_mem p
  rwa [verts_zero] at this

lemma vx_cls (p : Fin (rsGraph I 0).n) : (vx p).1 ∈ classes I :=
  ((mem_names I).mp (vx_mem_names p)).1

/-- The classes of the vertices of `G₀` carrying a pebble. -/
noncomputable def rclsOf {m : ℕ} (S : GameState m (rsGraph I 0) (rsGraph I 1)) :
    Finset (ICls I) :=
  Finset.univ.biUnion fun j => match S j with
    | some (p, _) => {(vx p).1}
    | none => ∅

lemma mem_rclsOf {m : ℕ} {S : GameState m (rsGraph I 0) (rsGraph I 1)} {X : ICls I} :
    X ∈ rclsOf S ↔ ∃ j p q, S j = some (p, q) ∧ (vx p).1 = X := by
  simp only [rclsOf, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    split at hj
    · next p q h => exact ⟨j, p, q, h, (Finset.mem_singleton.mp hj).symm⟩
    · simp at hj
  · rintro ⟨j, p, q, h, rfl⟩
    exact ⟨j, by simp [h]⟩

lemma rclsOf_sub {m : ℕ} (S : GameState m (rsGraph I 0) (rsGraph I 1)) :
    rclsOf S ⊆ classes I := by
  intro X hX
  obtain ⟨j, p, q, -, rfl⟩ := mem_rclsOf.mp hX
  exact vx_cls p

lemma card_rclsOf_lift {m : ℕ} (S : GameState (m + 1) (rsGraph I 0) (rsGraph I 1))
    (i : Fin (m + 1)) : (rclsOf (Function.update S i none)).card ≤ m := by
  classical
  refine (Finset.card_biUnion_le).trans ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self, Finset.card_empty, zero_add]
  calc _ ≤ ∑ j ∈ Finset.univ.erase i, 1 := Finset.sum_le_sum fun j _ => by
          split <;> simp
    _ = m := by simp

lemma rclsOf_lift_subset {m : ℕ} (S : GameState m (rsGraph I 0) (rsGraph I 1)) (i : Fin m) :
    rclsOf (Function.update S i none) ⊆ rclsOf S := by
  intro X hX
  obtain ⟨j, p, q, h, rfl⟩ := mem_rclsOf.mp hX
  by_cases hji : j = i
  · subst hji; simp at h
  · rw [Function.update_of_ne hji] at h
    exact mem_rclsOf.mpr ⟨j, p, q, h, rfl⟩

lemma rclsOf_place {m : ℕ} (S : GameState m (rsGraph I 0) (rsGraph I 1)) (i : Fin m)
    (p : Fin (rsGraph I 0).n) (q : Fin (rsGraph I 1).n) :
    rclsOf (Function.update S i (some (p, q))) =
      insert (vx p).1 (rclsOf (Function.update S i none)) := by
  ext X
  simp only [mem_rclsOf, Finset.mem_insert]
  constructor
  · rintro ⟨j, p', q', h, rfl⟩
    by_cases hji : j = i
    · subst hji; simp at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inl rfl
    · rw [Function.update_of_ne hji] at h
      exact Or.inr ⟨j, p', q', by rw [Function.update_of_ne hji]; exact h, rfl⟩
  · rintro (rfl | ⟨j, p', q', h, rfl⟩)
    · exact ⟨i, p, q, by simp, rfl⟩
    · by_cases hji : j = i
      · subst hji; simp at h
      · exact ⟨j, p', q', by rw [Function.update_of_ne hji] at h ⊢; exact h, rfl⟩

/-- The pebble pairs follow the translation of `D`. -/
def RMatches {m : ℕ} (D : RDesc I) (S : GameState m (rsGraph I 0) (rsGraph I 1)) : Prop :=
  ∀ j p q, S j = some (p, q) → vx q = tr D (vx p)

lemma edgeOK_of {A : Finset (ICls I)} {D : RDesc I} (hG : DGood A D) (hA : A ⊆ classes I)
    {Y : ICls I} (hY : Y ∈ A) : EdgeOK D Y := by
  cases Y with
  | upd e h c =>
    obtain ⟨⟨h1, h2⟩, -⟩ := mem_classes_upd.mp (hA hY)
    exact ⟨h1, h2, hG.ms e c (mem_Isch.mpr ⟨_, hY, rfl⟩)⟩
  | junc e c => exact (mem_classes_junc.mp (hA hY)).1
  | coord => trivial
  | sum => trivial
  | link => trivial
  | track => trivial
  | coef => trivial

/-- Seed descriptions give partial isomorphisms. -/
lemma partialIso_of_rgood {m : ℕ} {D : RDesc I} {S : GameState m (rsGraph I 0) (rsGraph I 1)}
    (hG : DGood (rclsOf S) D) (hM : RMatches D S) :
    IsPartialIso (rsGraph I 0) (rsGraph I 1) S := by
  intro i j p q p' q' hi hj
  have hpA : (vx p).1 ∈ rclsOf S := mem_rclsOf.mpr ⟨i, p, q, hi, rfl⟩
  have hp'A : (vx p').1 ∈ rclsOf S := mem_rclsOf.mpr ⟨j, p', q', hj, rfl⟩
  have e1 := hM i p q hi
  have e2 := hM j p' q' hj
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ?_, ?_⟩
  · subst h; exact vx_injective (e1.trans e2.symm)
  · apply vx_injective
    calc vx p = tr D (tr D (vx p)) := (tr_tr D _).symm
      _ = tr D (vx q) := by rw [e1]
      _ = tr D (vx q') := by rw [h]
      _ = vx p' := by rw [e2, tr_tr]
  · show radj I (vx p) (vx p') ↔ radj I (vx q) (vx q')
    rw [e1, e2]
    exact radj_tr D (edgeOK_of hG (rclsOf_sub S) hpA) (edgeOK_of hG (rclsOf_sub S) hp'A)
  · exact (rs_color_eq p q).mpr (by rw [e1]; rfl)

/-- Duplicator's invariant on game states. -/
def RInv {m : ℕ} (r : ℕ) (S : GameState m (rsGraph I 0) (rsGraph I 1)) : Prop :=
  ∃ D : RDesc I, DGood (rclsOf S) D ∧ Agree r (rclsOf S) D ∧ RMatches D S

/-- **Duplicator's strategy.** -/
theorem rsurvivesFrom_of_inv (hk : 2 ≤ k) :
    ∀ (r : ℕ), ¬ I.toParitySystem.HasConflict r →
      ∀ (S : GameState (k + 1) (rsGraph I 0) (rsGraph I 1)), RInv r S →
        SurvivesFrom (rsGraph I 0) (rsGraph I 1) r S
  | 0, _, _, _ => trivial
  | r + 1, hnc, S, ⟨D, hG, hag, hM⟩ => by
    classical
    intro i
    set A₀ := rclsOf (Function.update S i none)
    have hsub := rclsOf_lift_subset S i
    have hG₀ : DGood A₀ D := hG.mono hsub
    have hag₀ : Agree (r + 1) A₀ D := hag.mono le_rfl hsub
    have hA₀ : A₀ ⊆ classes I := rclsOf_sub _
    have hcard := card_rclsOf_lift S i
    have hext : ∀ X : ICls I, ∃ D' : RDesc I, InitOK D' ∧ MaskOK D' ∧ (X ∈ classes I →
        DGood (insert X A₀) D' ∧ Agree r (insert X A₀) D' ∧
          ∀ Y ∈ A₀, rshift D' Y = rshift D Y) := by
      intro X
      by_cases hX : X ∈ classes I
      · obtain ⟨D', h1, h2, h3⟩ := extend_cls hk hG₀ hA₀ hcard hag₀ hnc hX
        exact ⟨D', h1.init, h1.mask, fun _ => ⟨h1, h2, h3⟩⟩
      · exact ⟨D, hG.init, hG.mask, fun h => absurd h hX⟩
    choose DX hDi hDm hDX using hext
    let f : Fin (rsGraph I 0).n → Fin (rsGraph I 1).n := fun p =>
      ix 1 (tr (DX (vx p).1) (vx p)) (tr_mem _ (hDi _) (hDm _) (vx_mem_names p))
    let g : Fin (rsGraph I 1).n → Fin (rsGraph I 0).n := fun q =>
      ix 0 (tr (DX (vx q).1) (vx q))
        (by rw [verts_zero]; exact tr_mem' _ (hDi _) (hDm _) (vx_mem q))
    have hfv : ∀ p, vx (f p) = tr (DX (vx p).1) (vx p) := fun p => vx_ix _ _
    have hgv : ∀ q, vx (g q) = tr (DX (vx q).1) (vx q) := fun q => vx_ix _ _
    let F : Fin (rsGraph I 0).n ≃ Fin (rsGraph I 1).n :=
      { toFun := f
        invFun := g
        left_inv := fun p => vx_injective (by rw [hgv, hfv, tr_fst, tr_tr])
        right_inv := fun q => vx_injective (by rw [hfv, hgv, tr_fst, tr_tr]) }
    refine ⟨F, fun p => ?_⟩
    have hp := hDX (vx p).1 (vx_cls p)
    set S' := Function.update S i (some (p, F p))
    have hcls : rclsOf S' = insert (vx p).1 A₀ := rclsOf_place S i p _
    have hM' : RMatches (DX (vx p).1) S' := by
      intro j p' q' hj
      by_cases hji : j = i
      · subst hji
        simp only [S', Function.update_self, Option.some.injEq, Prod.mk.injEq] at hj
        obtain ⟨rfl, rfl⟩ := hj
        exact hfv p
      · rw [show S' j = S j from Function.update_of_ne hji _ _] at hj
        have hY : (vx p').1 ∈ A₀ :=
          mem_rclsOf.mpr ⟨j, p', q', by rw [Function.update_of_ne hji]; exact hj, rfl⟩
        rw [hM j p' q' hj]
        simp only [tr, hp.2.2 _ hY]
    have hG' : DGood (rclsOf S') (DX (vx p).1) := hcls ▸ hp.1
    have hag' : Agree r (rclsOf S') (DX (vx p).1) := hcls ▸ hp.2.1
    exact ⟨partialIso_of_rgood hG' hM', rsurvivesFrom_of_inv hk r
      (fun h => hnc (hasConflict_mono I (Nat.le_succ r) h)) S' ⟨_, hG', hag', hM'⟩⟩

/-- **Part (2) of the row-space compiler.** Duplicator survives `r` rounds as long as `K_r` is
conflict-free. -/
theorem duplicatorSurvives (hk : 3 ≤ k) {r : ℕ} (hnc : ¬ I.toParitySystem.HasConflict r) :
    DuplicatorSurvives (k + 1) r (rsGraph I 0) (rsGraph I 1) := by
  have h0 : rclsOf (I := I) (fun _ : Fin (k + 1) => none) = ∅ := by
    ext X; simp [mem_rclsOf]
  refine ⟨(card_verts I 0).trans (card_verts I 1).symm,
    rsurvivesFrom_of_inv (by omega) r hnc _ ⟨rdesc0 I, ?_, ?_, fun _ _ _ h => by simp at h⟩⟩
  · rw [h0]; exact dgood_empty
  · rw [h0]; exact agree_empty (by omega) r _

end Lax119563Proofs.RowSpace

end RowSpace_Duplicator

/-! ### Formerly `Lax119563Proofs.RowSpace.Exposed` -/

section RowSpace_Exposed

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

end RowSpace_Exposed

/-! ### Formerly `Lax119563Proofs.RowSpace.Size` -/

section RowSpace_Size

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

end RowSpace_Size

/-! ### Formerly `Lax119563Proofs.RowSpace.SpoilerBasics` -/

section RowSpace_SpoilerBasics

/-!
# Spoiler's moves on the row-space graphs

Spoiler always places pebbles on zero vertices `(X, 0)` of `G₀`. Pebbles `0, …, k - 1` hold
*representatives*; pebble `k` is the spare. Replacing a representative costs two rounds: the
spare is placed on the new vertex, then the representative is moved onto the same vertex,
where Duplicator has to answer with the same image.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ParitySystems
open Lax119563.ColoredGraphs Lax119563.PebbleGame
open Lax119563Proofs.Matrix

namespace Lax119563Proofs.RowSpace

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

local notation "G₀" => rsGraph I 0
local notation "G₁" => rsGraph I 1

/-- Game states of the `(k + 1)`-pebble game on the row-space graphs. -/
abbrev RSt (I : ImplicitParitySystem k ℓ) := GameState (k + 1) (rsGraph I 0) (rsGraph I 1)

/-! ### Zero vertices -/

lemma zero_mem_labs {X : ICls I} (hX : X ∈ classes I) : (0 : RLab k ℓ) ∈ labs I X := by
  cases X with
  | coord v c => simp only [labs]; split <;> simp [lab1]
  | sum => simp [labs, lab1]
  | junc => simp [labs, lab2]
  | link => exact absurd hX link_not_mem
  | track => simp [labs, lab1]
  | upd => simp [labs, lab2]
  | coef e h =>
    simp only [labs, Finset.mem_image]
    exact ⟨0, zero_mem_maskSet I e, rfl⟩

lemma zero_mem_verts {X : ICls I} (hX : X ∈ classes I) : (X, (0 : RLab k ℓ)) ∈ verts I 0 := by
  rw [verts_zero, mem_names]
  exact ⟨hX, zero_mem_labs hX⟩

/-- The zero vertex of a class in `G₀`. -/
noncomputable def rzv (X : ICls I) (hX : X ∈ classes I) : Fin (rsGraph I 0).n :=
  ix 0 (X, 0) (zero_mem_verts hX)

@[simp] lemma vx_rzv (X : ICls I) (hX : X ∈ classes I) : vx (rzv X hX) = (X, 0) := vx_ix _ _

/-- Pebble `j` holds the zero vertex of class `X`, matched with the vertex `(X, l)` of `G₁`. -/
def RHoldsAt (S : RSt I) (j : Fin (k + 1)) (X : ICls I) (l : RLab k ℓ) : Prop :=
  ∃ p q, S j = some (p, q) ∧ vx p = (X, 0) ∧ vx q = (X, l)

/-- The representatives hold the classes `cls` with labels `lab`. -/
def RHolds (S : RSt I) (cls : Fin k → ICls I) (lab : Fin k → RLab k ℓ) : Prop :=
  ∀ i, RHoldsAt S i.castSucc (cls i) (lab i)

lemma RHoldsAt.update_ne {S : RSt I} {j j' : Fin (k + 1)} {X : ICls I} {l : RLab k ℓ}
    (h : RHoldsAt S j X l) (hj : j ≠ j') (v : Option (Fin (rsGraph I 0).n × Fin (rsGraph I 1).n)) :
    RHoldsAt (Function.update S j' v) j X l := by
  obtain ⟨p, q, h1, h2⟩ := h
  exact ⟨p, q, by rw [Function.update_of_ne hj]; exact h1, h2⟩

lemma RHolds.update_spare {S : RSt I} {cls : Fin k → ICls I} {lab : Fin k → RLab k ℓ}
    (h : RHolds S cls lab) (v : Option (Fin (rsGraph I 0).n × Fin (rsGraph I 1).n)) :
    RHolds (Function.update S spare v) cls lab :=
  fun i => (h i).update_ne (castSucc_ne_spare i) v

lemma RHolds.congr_cls {S : RSt I} {cls cls' : Fin k → ICls I} {lab : Fin k → RLab k ℓ}
    (h : RHolds S cls lab) (hc : ∀ i, cls i = cls' i) : RHolds S cls' lab := by
  rwa [show cls = cls' from funext hc] at h

/-! ### Partial isomorphisms -/

lemma rpi_adj {S : RSt I} (hPI : IsPartialIso G₀ G₁ S) {j j' : Fin (k + 1)}
    {p p' : Fin (rsGraph I 0).n} {q q' : Fin (rsGraph I 1).n}
    (hj : S j = some (p, q)) (hj' : S j' = some (p', q')) :
    radj I (vx p) (vx p') ↔ radj I (vx q) (vx q') :=
  (hPI j j' p q p' q' hj hj').2.1

lemma rpi_cls {S : RSt I} (hPI : IsPartialIso G₀ G₁ S) {j : Fin (k + 1)}
    {p : Fin (rsGraph I 0).n} {q : Fin (rsGraph I 1).n}
    (hj : S j = some (p, q)) : (vx q).1 = (vx p).1 :=
  ((rs_color_eq p q).mp (hPI j j p q p q hj hj).2.2).symm

lemma rpi_eq {S : RSt I} (hPI : IsPartialIso G₀ G₁ S) {j j' : Fin (k + 1)}
    {p : Fin (rsGraph I 0).n} {q q' : Fin (rsGraph I 1).n}
    (hj : S j = some (p, q)) (hj' : S j' = some (p, q')) : q = q' :=
  (hPI j j' p q p q' hj hj').1.mp rfl

lemma rspare_vx {S : RSt I} (hPI : IsPartialIso G₀ G₁ S) {Y : ICls I} (hY : Y ∈ classes I)
    {q : Fin (rsGraph I 1).n} (hs : S spare = some (rzv Y hY, q)) : vx q = (Y, (vx q).2) := by
  have h := rpi_cls hPI hs
  rw [vx_rzv] at h
  exact Prod.ext h rfl

/-- What Duplicator's answer `q` on the spare reveals, for a hub class `Y` placed next to a
held class `X`. -/
lemma rforced_hub {S : RSt I} (hPI : IsPartialIso G₀ G₁ S) {j : Fin (k + 1)} {X : ICls I}
    {l : RLab k ℓ} (hj : RHoldsAt S j X l) {Y : ICls I} (hY : Y ∈ classes I)
    {q : Fin (rsGraph I 1).n} (hs : S spare = some (rzv Y hY, q)) (hYhub : isHubR I Y) :
    hubR I Y 0 X 0 ↔ hubR I Y (vx q).2 X l := by
  obtain ⟨p, q', h1, h2, h3⟩ := hj
  have := rpi_adj hPI hs h1
  rw [vx_rzv, h2, h3, rspare_vx hPI hY hs, radj_iff_hub I hYhub, radj_iff_hub I hYhub] at this
  exact this

/-- The same, for a hub `X` held by a representative and a non-hub class `Y` on the spare. -/
lemma rforced_nonhub {S : RSt I} (hPI : IsPartialIso G₀ G₁ S) {j : Fin (k + 1)} {X : ICls I}
    {l : RLab k ℓ} (hj : RHoldsAt S j X l) {Y : ICls I} (hY : Y ∈ classes I)
    {q : Fin (rsGraph I 1).n} (hs : S spare = some (rzv Y hY, q)) (hXhub : isHubR I X) :
    hubR I X 0 Y 0 ↔ hubR I X l Y (vx q).2 := by
  obtain ⟨p, q', h1, h2, h3⟩ := hj
  have := rpi_adj hPI h1 hs
  rw [vx_rzv, h2, h3, rspare_vx hPI hY hs, radj_iff_hub I hXhub, radj_iff_hub I hXhub] at this
  exact this

/-! ### Moves -/

/-- Placing the spare on the zero vertex of `Y`. -/
lemma rforces_spare (S : RSt I) (Y : ICls I) (hY : Y ∈ classes I) :
    Forces 1 S fun S' => ∃ q, S' = Function.update S spare (some (rzv Y hY, q)) ∧
      IsPartialIso G₀ G₁ S' :=
  Forces.place S spare (rzv Y hY)

/-- Replacing representative `i` by the zero vertex of `Y`. -/
lemma rforces_replace (S : RSt I) (i : Fin k) (Y : ICls I) (hY : Y ∈ classes I) :
    Forces 2 S fun S' => ∃ q, IsPartialIso G₀ G₁ (Function.update S spare (some (rzv Y hY, q))) ∧
      S' = Function.update (Function.update S spare (some (rzv Y hY, q))) i.castSucc
        (some (rzv Y hY, q)) ∧ IsPartialIso G₀ G₁ S' := by
  refine Forces.mono (le_refl (1 + 1)) ((rforces_spare S Y hY).bind fun S1 ⟨q, hS1, hPI1⟩ => ?_)
  refine (Forces.place S1 i.castSucc (rzv Y hY)).weaken fun S2 ⟨q2, hS2, hPI2⟩ => ?_
  have hq : q2 = q := by
    refine rpi_eq hPI2 (p := rzv Y hY) (j := i.castSucc) (j' := spare) ?_ ?_
    · rw [hS2]; simp
    · rw [hS2, Function.update_of_ne (castSucc_ne_spare i).symm, hS1]; simp
  subst hq hS1
  exact ⟨q2, hPI1, hS2, hPI2⟩

/-- Replacing representative `i` by class `Y`, where the answer satisfies `R`. -/
lemma rforces_step {S : RSt I} {cls : Fin k → ICls I} {lab : Fin k → RLab k ℓ}
    (hH : RHolds S cls lab) (i : Fin k) (Y : ICls I) (hY : Y ∈ classes I) (R : RLab k ℓ → Prop)
    (hR : ∀ q, IsPartialIso G₀ G₁ (Function.update S spare (some (rzv Y hY, q))) →
      R (vx q).2) :
    Forces 2 S fun S' => ∃ l, R l ∧ RHolds S' (Function.update cls i Y)
      (Function.update lab i l) ∧ IsPartialIso G₀ G₁ S' := by
  refine (rforces_replace S i Y hY).weaken fun S' ⟨q, hPI1, hS', hPI'⟩ => ?_
  refine ⟨(vx q).2, hR q hPI1, fun j => ?_, hPI'⟩
  by_cases hji : j = i
  · subst hji
    refine ⟨rzv Y hY, q, by rw [hS']; simp, by simp, ?_⟩
    rw [Function.update_self, Function.update_self]
    exact rspare_vx hPI1 hY (Function.update_self _ _ _)
  · rw [Function.update_of_ne hji, Function.update_of_ne hji, hS']
    exact ((hH j).update_ne (castSucc_ne_spare j) _).update_ne
      (fun h => hji (Fin.castSucc_injective _ h)) _

/-- Replacing the representatives in the list `T` one after the other. -/
lemma rforces_replaceAll (T : List (Fin k)) (hT : T.Nodup) {S : RSt I} {cls : Fin k → ICls I}
    {lab : Fin k → RLab k ℓ} (hH : RHolds S cls lab) (hPI : IsPartialIso G₀ G₁ S)
    (newCls : Fin k → ICls I) (hval : ∀ i ∈ T, newCls i ∈ classes I)
    (R : Fin k → RLab k ℓ → RLab k ℓ → Prop)
    (hR : ∀ (S1 : RSt I) i q (hi : i ∈ T), RHoldsAt S1 i.castSucc (cls i) (lab i) →
      S1 spare = some (rzv (newCls i) (hval i hi), q) → IsPartialIso G₀ G₁ S1 →
      R i (lab i) (vx q).2) :
    Forces (2 * T.length) S fun S' => ∃ lab' : Fin k → RLab k ℓ,
      (∀ i ∈ T, R i (lab i) (lab' i)) ∧ (∀ i, i ∉ T → lab' i = lab i) ∧
      RHolds S' (fun i => if i ∈ T then newCls i else cls i) lab' ∧ IsPartialIso G₀ G₁ S' := by
  induction T generalizing S cls lab with
  | nil =>
    refine Forces.ret ⟨lab, by simp, fun _ _ => rfl, by simpa using hH, hPI⟩
  | cons i T ih =>
    obtain ⟨hiT, hT'⟩ := List.nodup_cons.mp hT
    have hstep := rforces_step hH i (newCls i) (hval i List.mem_cons_self) (R i (lab i))
      fun q hPI => hR _ i q List.mem_cons_self ((hH i).update_ne (castSucc_ne_spare i) _)
        (Function.update_self ..) hPI
    refine Forces.mono (show 2 + 2 * T.length ≤ 2 * (i :: T).length by simp; omega)
      (hstep.bind fun S1 ⟨l, hl, hH1, hPI1⟩ => ?_)
    refine (ih hT' hH1 hPI1 (fun j hj => hval j (List.mem_cons_of_mem _ hj))
      fun S2 j q hj hj2 hs hPI2 => ?_).weaken
      fun S' ⟨lab', h1, h2, h3, h4⟩ => ?_
    · have hji : j ≠ i := fun h => hiT (h ▸ hj)
      rw [Function.update_of_ne hji] at hj2 ⊢
      rw [Function.update_of_ne hji] at hj2
      exact hR S2 j q (List.mem_cons_of_mem _ hj) hj2 hs hPI2
    · refine ⟨lab', fun j hj => ?_, fun j hj => ?_, ?_, h4⟩
      · rcases List.mem_cons.mp hj with rfl | hj
        · rw [h2 j hiT]; simpa using hl
        · have hji : j ≠ i := fun h => hiT (h ▸ hj)
          have := h1 j hj
          rwa [Function.update_of_ne hji] at this
      · have hji : j ≠ i := fun h => hj (h ▸ List.mem_cons_self)
        rw [h2 j fun h => hj (List.mem_cons_of_mem _ h), Function.update_of_ne hji]
      · convert h3 using 2 with j
        by_cases hji : j = i
        · subst hji; simp [hiT]
        · simp [hji]

/-- Replacing every representative. -/
lemma rforces_replaceEvery {S : RSt I} {cls : Fin k → ICls I} {lab : Fin k → RLab k ℓ}
    (hH : RHolds S cls lab) (hPI : IsPartialIso G₀ G₁ S) (newCls : Fin k → ICls I)
    (hval : ∀ i, newCls i ∈ classes I) (R : Fin k → RLab k ℓ → RLab k ℓ → Prop)
    (hR : ∀ (S1 : RSt I) i q, RHoldsAt S1 i.castSucc (cls i) (lab i) →
      S1 spare = some (rzv (newCls i) (hval i), q) → IsPartialIso G₀ G₁ S1 →
      R i (lab i) (vx q).2) :
    Forces (2 * k) S fun S' => ∃ lab' : Fin k → RLab k ℓ, (∀ i, R i (lab i) (lab' i)) ∧
      RHolds S' newCls lab' ∧ IsPartialIso G₀ G₁ S' := by
  have := rforces_replaceAll (List.finRange k) (List.nodup_finRange k) hH hPI newCls
    (fun i _ => hval i) R fun S1 i q _ h1 h2 h3 => hR S1 i q h1 h2 h3
  rw [List.length_finRange] at this
  exact this.weaken fun S' ⟨lab', h1, _, h3, h4⟩ =>
    ⟨lab', fun i => h1 i (List.mem_finRange i), h3.congr_cls fun i => by simp, h4⟩

/-- Placing the representatives on the zero vertices of the classes `cls`. -/
lemma rforces_fill (T : List (Fin k)) (hT : T.Nodup) {S : RSt I} (hPI : IsPartialIso G₀ G₁ S)
    (cls : Fin k → ICls I) (hval : ∀ i, cls i ∈ classes I) :
    Forces (2 * T.length) S fun S' => (∀ i ∈ T, ∃ l, RHoldsAt S' i.castSucc (cls i) l) ∧
      (∀ i, i ∉ T → S' i.castSucc = S i.castSucc) ∧ IsPartialIso G₀ G₁ S' := by
  induction T generalizing S with
  | nil => exact Forces.ret ⟨by simp, fun _ _ => rfl, hPI⟩
  | cons i T ih =>
    obtain ⟨hiT, hT'⟩ := List.nodup_cons.mp hT
    refine Forces.mono (show 2 + 2 * T.length ≤ 2 * (i :: T).length by simp; omega)
      ((rforces_replace S i (cls i) (hval i)).bind fun S1 ⟨q, hPI1, hS1, hPI1'⟩ =>
        (ih hT' hPI1').weaken fun S' ⟨h1, h2, h3⟩ => ⟨fun j hj => ?_, fun j hj => ?_, h3⟩)
    · rcases List.mem_cons.mp hj with rfl | hj
      · refine ⟨(vx q).2, rzv (cls j) (hval j), q, ?_, by simp, ?_⟩
        · rw [h2 j hiT, hS1]; simp
        · exact rspare_vx hPI1 (hval j) (Function.update_self ..)
      · exact h1 j hj
    · have hji : j ≠ i := fun h => hj (h ▸ List.mem_cons_self)
      rw [h2 j fun h => hj (List.mem_cons_of_mem _ h), hS1,
        Function.update_of_ne (fun h => hji (Fin.castSucc_injective _ h)),
        Function.update_of_ne (castSucc_ne_spare j)]

end Lax119563Proofs.RowSpace

end RowSpace_SpoilerBasics

/-! ### Formerly `Lax119563Proofs.RowSpace.SpoilerStage` -/

section RowSpace_SpoilerStage

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

end RowSpace_SpoilerStage

/-! ### Formerly `Lax119563Proofs.RowSpace.Affine` -/

section RowSpace_Affine

/-!
# The affine dichotomy

Adjacency in the row-space graphs is given by linear conditions on the labels, so labels of
homomorphisms can be added: if some homomorphism `F → G₁` exists, adding its labels is a
bijection from homomorphisms `F → G₀` to homomorphisms `F → G₁`. Hence
`hom(F, G₁) ∈ {0, hom(F, G₀)}`.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs
open Lax119563.ColoredHomomorphisms
open Lax119563Proofs.Matrix

namespace Lax119563Proofs.RowSpace

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

/-- Adjacency conditions add up (for hubs of valid classes). -/
lemma hubR_add {X Y : ICls I} (hX : X ∈ classes I) {l m l' m' : RLab k ℓ} (h : hubR I X l Y m)
    (h' : hubR I X l' Y m') : hubR I X (l + l') Y (m + m') := by
  cases X with
  | upd e σ c =>
    obtain ⟨⟨hσ, -⟩, -⟩ := mem_classes_upd.mp hX
    obtain ⟨n, rfl⟩ : ∃ n, σ = n + 1 := ⟨σ - 1, by omega⟩
    rw [hubR_upd_succ] at h h' ⊢
    have hne : trackCls I e c n ≠ trackCls I e c (n + 1) := fun h => by
      have := trackCls_injective e c h; omega
    have h1 := trackCls_ne_coef e c n (n + 1)
    have h2 := trackCls_ne_coef e c (n + 1) (n + 1)
    rcases h with ⟨rfl, ha⟩ | ⟨rfl, ha⟩ | ⟨rfl, ha⟩ <;>
      rcases h' with ⟨hY, hb⟩ | ⟨hY, hb⟩ | ⟨hY, hb⟩ <;>
      first
        | exact absurd hY hne | exact absurd hY.symm hne | exact absurd hY h1
        | exact absurd hY.symm h1 | exact absurd hY h2 | exact absurd hY.symm h2
        | skip
    · exact Or.inl ⟨rfl, by simp only [Prod.fst_add, ha, hb]⟩
    · exact Or.inr (Or.inl ⟨rfl, by simp only [Prod.fst_add, Prod.snd_add, ha, hb]⟩)
    · refine Or.inr (Or.inr ⟨rfl, ?_⟩)
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, ha, hb]
      ring
  | junc e c =>
    have hne := coordU_ne_coordV (mem_classes_junc.mp hX).1 c
    have h1 : coordU e c ≠ (Cls.sum e c : ICls I) := by simp [coordU]
    have h2 : coordV e c ≠ (Cls.sum e c : ICls I) := by simp [coordV]
    rw [hubR_junc'] at h h' ⊢
    rcases h with ⟨rfl, ha⟩ | ⟨rfl, ha⟩ | ⟨rfl, ha⟩ <;>
      rcases h' with ⟨hY, hb⟩ | ⟨hY, hb⟩ | ⟨hY, hb⟩ <;>
      first
        | exact absurd hY hne | exact absurd hY.symm hne | exact absurd hY h1
        | exact absurd hY.symm h1 | exact absurd hY h2 | exact absurd hY.symm h2
        | skip
    · exact Or.inl ⟨rfl, by simp only [Prod.fst_add, ha, hb]⟩
    · exact Or.inr (Or.inl ⟨rfl, by simp only [Prod.fst_add, Prod.snd_add, ha, hb]⟩)
    · refine Or.inr (Or.inr ⟨rfl, ?_⟩)
      simp only [Prod.fst_add, Prod.snd_add, ha, hb]
      ring
  | coord => exact h.elim
  | sum => exact h.elim
  | link => exact h.elim
  | track => exact h.elim
  | coef => exact h.elim

/-- Adjacency conditions hold for zero labels. -/
lemma hubR_zero {X Y : ICls I} {l m : RLab k ℓ} (h : hubR I X l Y m) : hubR I X 0 Y 0 := by
  cases X with
  | upd e σ c => rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [hubR]
  | junc e c => rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [hubR]
  | coord => exact h.elim
  | sum => exact h.elim
  | link => exact h.elim
  | track => exact h.elim
  | coef => exact h.elim

/-- Adjacent vertices have adjacent zero vertices. -/
lemma radj_zero {x y : ICls I × RLab k ℓ} (h : radj I x y) : radj I (x.1, 0) (y.1, 0) :=
  h.imp hubR_zero hubR_zero

/-- Adjacency of vertices of valid classes adds up. -/
lemma radj_add {X Y : ICls I} (hX : X ∈ classes I) (hY : Y ∈ classes I) {a b a' b' : RLab k ℓ}
    (h : radj I (X, a) (Y, b)) (h' : radj I (X, a') (Y, b')) :
    radj I (X, a + a') (Y, b + b') := by
  rcases h with h | h <;> rcases h' with h' | h'
  · exact Or.inl (hubR_add hX h h')
  · exact absurd (hubR_hub I h').1 (hubR_hub I h).2
  · exact absurd (hubR_hub I h').1 (hubR_hub I h).2
  · exact Or.inr (hubR_add hY h h')

/-- The label sets are closed under addition. -/
lemma labs_add {X : ICls I} {a b : RLab k ℓ} (ha : a ∈ labs I X) (hb : b ∈ labs I X) :
    a + b ∈ labs I X := by
  cases X with
  | coord v c =>
    simp only [labs] at ha hb ⊢
    by_cases hv : (I.init v).isSome
    · simp only [hv, if_true, Finset.mem_singleton] at ha hb ⊢; simp [ha, hb]
    · simp only [hv, Bool.false_eq_true, if_false, mem_lab1] at ha hb ⊢; simp [ha, hb]
  | sum => simp only [labs, mem_lab1] at ha hb ⊢; simp [ha, hb]
  | track => simp only [labs, mem_lab1] at ha hb ⊢; simp [ha, hb]
  | junc => simp only [labs, mem_lab2] at ha hb ⊢; simp [ha, hb]
  | upd => simp only [labs, mem_lab2] at ha hb ⊢; simp [ha, hb]
  | coef e h =>
    simp only [labs, Finset.mem_image] at ha hb ⊢
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact ⟨x + y, add_mem_maskSet I hx hy, by simp⟩
  | link => simp [labs] at ha

lemma mem_verts_one {x : ICls I × RLab k ℓ} :
    x ∈ verts I 1 ↔ x.1 ∈ classes I ∧ x.2 + off I x.1 ∈ labs I x.1 := by
  rw [mem_verts, one_smul, mem_names]

lemma mem_verts_zero {x : ICls I × RLab k ℓ} :
    x ∈ verts I 0 ↔ x.1 ∈ classes I ∧ x.2 ∈ labs I x.1 := by
  rw [verts_zero, mem_names]


/-- Color-preserving homomorphisms into `G_ε`. -/
abbrev RHom (I : ImplicitParitySystem k ℓ) (F : ColoredGraph) (ε : ZMod 2) :=
  {h : F.graph →g (rsGraph I ε).graph // ∀ v, (rsGraph I ε).color (h v) = F.color v}

lemma rhom_cls {F : ColoredGraph} {ε ε' : ZMod 2} (φ : RHom I F ε) (ψ : RHom I F ε')
    (p : Fin F.n) : (vx (φ.1 p)).1 = (vx (ψ.1 p)).1 :=
  (rs_color_eq _ _).mp ((φ.2 p).trans (ψ.2 p).symm)

/-- Adding the labels of a fixed homomorphism `ψ : F → G₁`. -/
noncomputable def fwdHom {F : ColoredGraph} (ψ : RHom I F 1) (φ : RHom I F 0) : RHom I F 1 :=
  ⟨⟨fun p => ix 1 ((vx (φ.1 p)).1, (vx (φ.1 p)).2 + (vx (ψ.1 p)).2) (by
      have h0 := mem_verts_zero.mp (vx_mem (φ.1 p))
      have h1 := mem_verts_one.mp (vx_mem (ψ.1 p))
      rw [← rhom_cls φ ψ p] at h1
      refine mem_verts_one.mpr ⟨h0.1, ?_⟩
      simpa only [add_assoc] using labs_add h0.2 h1.2),
    fun {p q} hpq => by
      rw [rs_adj, vx_ix, vx_ix]
      have h0 := (φ.1.map_rel hpq : (rsGraph I 0).graph.Adj _ _)
      have h1 := (ψ.1.map_rel hpq : (rsGraph I 1).graph.Adj _ _)
      rw [rs_adj] at h0 h1
      have hcp := rhom_cls φ ψ p
      have hcq := rhom_cls φ ψ q
      have hp := (mem_verts_zero.mp (vx_mem (φ.1 p))).1
      have hq := (mem_verts_zero.mp (vx_mem (φ.1 q))).1
      rw [← Prod.mk.eta (p := vx (φ.1 p)), ← Prod.mk.eta (p := vx (φ.1 q))] at h0
      rw [← Prod.mk.eta (p := vx (ψ.1 p)), ← Prod.mk.eta (p := vx (ψ.1 q)), ← hcp, ← hcq] at h1
      exact radj_add hp hq h0 h1⟩,
    fun p => by
      rw [rs_color]; change code I (vx (ix _ _ _)).1 = _; rw [vx_ix]; exact φ.2 p⟩

/-- Subtracting the labels of a fixed homomorphism `ψ : F → G₁`. -/
noncomputable def bwdHom {F : ColoredGraph} (ψ : RHom I F 1) (φ : RHom I F 1) : RHom I F 0 :=
  ⟨⟨fun p => ix 0 ((vx (φ.1 p)).1, (vx (φ.1 p)).2 + (vx (ψ.1 p)).2) (by
      have h0 := mem_verts_one.mp (vx_mem (φ.1 p))
      have h1 := mem_verts_one.mp (vx_mem (ψ.1 p))
      rw [← rhom_cls φ ψ p] at h1
      refine mem_verts_zero.mpr ⟨h0.1, ?_⟩
      have := labs_add h0.2 h1.2
      have e : (vx (φ.1 p)).2 + off I (vx (φ.1 p)).1 + ((vx (ψ.1 p)).2 + off I (vx (φ.1 p)).1) =
          (vx (φ.1 p)).2 + (vx (ψ.1 p)).2 := by
        rw [add_comm (vx (ψ.1 p)).2, ← add_assoc, rlab_add_add_cancel]
      rwa [e] at this),
    fun {p q} hpq => by
      rw [rs_adj, vx_ix, vx_ix]
      have h0 := (φ.1.map_rel hpq : (rsGraph I 1).graph.Adj _ _)
      have h1 := (ψ.1.map_rel hpq : (rsGraph I 1).graph.Adj _ _)
      rw [rs_adj] at h0 h1
      have hcp := rhom_cls φ ψ p
      have hcq := rhom_cls φ ψ q
      have hp := (mem_verts_one.mp (vx_mem (φ.1 p))).1
      have hq := (mem_verts_one.mp (vx_mem (φ.1 q))).1
      rw [← Prod.mk.eta (p := vx (φ.1 p)), ← Prod.mk.eta (p := vx (φ.1 q))] at h0
      rw [← Prod.mk.eta (p := vx (ψ.1 p)), ← Prod.mk.eta (p := vx (ψ.1 q)), ← hcp, ← hcq] at h1
      exact radj_add hp hq h0 h1⟩,
    fun p => by
      rw [rs_color]; change code I (vx (ix _ _ _)).1 = _; rw [vx_ix]; exact φ.2 p⟩

/-- Adding the labels of a homomorphism `F → G₁` is a bijection. -/
noncomputable def addEquiv {F : ColoredGraph} (ψ : RHom I F 1) : RHom I F 0 ≃ RHom I F 1 where
  toFun := fwdHom ψ
  invFun := bwdHom ψ
  left_inv φ := by
    refine Subtype.ext (RelHom.ext fun p => vx_injective ?_)
    simp [bwdHom, fwdHom, rlab_add_add_cancel]
  right_inv φ := by
    refine Subtype.ext (RelHom.ext fun p => vx_injective ?_)
    simp [bwdHom, fwdHom, rlab_add_add_cancel]

/-- **Affine dichotomy.** -/
theorem hom_dichotomy (F : ColoredGraph) (hne : hom F (rsGraph I 0) ≠ hom F (rsGraph I 1)) :
    hom F (rsGraph I 1) = 0 ∧
      Nonempty {h : F.graph →g (rsGraph I 0).graph // ∀ v, (rsGraph I 0).color (h v) = F.color v} := by
  have h1 : hom F (rsGraph I 1) = 0 := by
    by_contra h
    obtain ⟨⟨ψ⟩, -⟩ := Nat.card_ne_zero.mp h
    exact hne (Nat.card_congr (addEquiv ψ))
  refine ⟨h1, (Nat.card_ne_zero.mp ?_).1⟩
  rw [h1] at hne
  exact hne

end Lax119563Proofs.RowSpace

end RowSpace_Affine

/-! ### Formerly `Lax119563Proofs.RowSpace.Realize` -/

section RowSpace_Realize

/-!
# Local realization

Let `F` admit a homomorphism to `G₀` (which fixes the class `cl p` of every vertex) and a
one-vertex tree decomposition of width at most `k`. Values `α_p` on the variables exposed at
the bags, agreeing along the forest, satisfying the exposed equations and the initialization,
give a homomorphism `F → G₁` (paper, Lemma "Local realization"): top-down along the forest we
extend seed descriptions with the local extension lemma, and map every vertex to the image of
the zero vertex of its class under the description of its bag.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs
open Lax119563.ColoredHomomorphisms
open Lax119563Proofs.Matrix

namespace Lax119563Proofs.RowSpace

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ} {F : ColoredGraph}

/-- The classes of a set of vertices. -/
def AS (cl : Fin F.n → ICls I) (S : Finset (Fin F.n)) : Finset (ICls I) := S.image cl

/-- The bag of `p` without `p`. -/
def bagm {F : ColoredGraph} (T : OneVertexForest F.graph k) (p : Fin F.n) : Finset (Fin F.n) :=
  (T.bag p).erase p

variable (T : OneVertexForest F.graph k) (cl : Fin F.n → ICls I)

lemma AS_bag (p : Fin F.n) : AS cl (T.bag p) = insert (cl p) (AS cl (bagm T p)) := by
  rw [AS, AS, bagm, ← Finset.image_insert, Finset.insert_erase (T.mem_bag p)]

lemma AS_bagm_sub {p q : Fin F.n} (h : T.parent p = some q) :
    AS cl (bagm T p) ⊆ AS cl (T.bag q) :=
  Finset.image_subset_image (T.bag_sub p q h)

lemma card_AS_bagm (p : Fin F.n) : (AS cl (bagm T p)).card ≤ k := by
  refine Finset.card_image_le.trans ?_
  rw [bagm, Finset.card_erase_of_mem (T.mem_bag p)]
  have := T.card_bag p
  omega

lemma bagm_root {p : Fin F.n} (h : T.parent p = none) : bagm T p = ∅ := T.bag_root p h

/-- The invariant of the descriptions at a vertex. -/
def RealInv (α : Fin F.n → Val I) (D : Fin F.n → RDesc I) (p : Fin F.n) : Prop :=
  DGood (AS cl (T.bag p)) (D p) ∧ Realizes (AS cl (T.bag p)) (D p) (α p) ∧
    ∀ q, T.parent p = some q → ∀ Y ∈ AS cl (bagm T p), rshift (D p) Y = rshift (D q) Y

section
variable {T cl}
variable (hk : 3 ≤ k) (hcl : ∀ p, cl p ∈ classes I) (α : Fin F.n → Val I)
  (hagree : ∀ p q, T.parent p = some q → ∀ v a, IsAddress a →
    supp a ⊆ Iloc (AS cl (bagm T p)) v → α p (v, a) = α q (v, a))
  (hsat : ∀ p, SatEqs (AS cl (T.bag p)) (α p))
  (hinit : ∀ p, InitAgree (AS cl (T.bag p)) (α p))
include hk hcl hagree hsat hinit

omit hk hagree hsat hinit in
lemma AS_sub (S : Finset (Fin F.n)) : AS cl S ⊆ classes I := by
  intro X hX
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hX
  exact hcl p

/-- One step: extending the description of the parent. -/
lemma real_step (p : Fin F.n) (Dq : RDesc I)
    (hq : ∀ q, T.parent p = some q →
      DGood (AS cl (T.bag q)) Dq ∧ Realizes (AS cl (T.bag q)) Dq (α q)) :
    ∃ Dp, DGood (AS cl (T.bag p)) Dp ∧ Realizes (AS cl (T.bag p)) Dp (α p) ∧
      (∀ q, T.parent p = some q → ∀ Y ∈ AS cl (bagm T p), rshift Dp Y = rshift Dq Y) := by
  have hA := AS_sub hcl (bagm T p)
  -- the base description on the classes of `bagm p`
  obtain ⟨D0, hG0, hR0, hsh⟩ : ∃ D0, DGood (AS cl (bagm T p)) D0 ∧
      Realizes (AS cl (bagm T p)) D0 (α p) ∧
      ∀ q, T.parent p = some q → D0 = Dq := by
    cases hp : T.parent p with
    | none =>
      have : AS cl (bagm T p) = ∅ := by rw [bagm_root T hp]; rfl
      rw [this]
      exact ⟨rdesc0 I, dgood_empty, realizes_empty (by omega) _ _, fun q h => by simp at h⟩
    | some q =>
      obtain ⟨hG, hR⟩ := hq q hp
      refine ⟨Dq, hG.mono (AS_bagm_sub T cl hp), fun v a ha hs => ?_, fun _ _ => rfl⟩
      rw [hR.mono (AS_bagm_sub T cl hp) v a ha hs, hagree p q hp v a ha hs]
  have hsat' := hsat p
  have hinit' := hinit p
  rw [AS_bag] at hsat' hinit' ⊢
  obtain ⟨D', h1, h2, h3⟩ := local_extend (by omega) hG0 hA (hcl p) (card_AS_bagm T cl p)
    (α p) hR0 hsat' hinit'
  exact ⟨D', h1, h2, fun q hq Y hY => (h3 Y hY).trans (by rw [hsh q hq])⟩

/-- Descriptions satisfying the invariant at all vertices of depth below `N`. -/
lemma real_upto (N : ℕ) : ∃ D : Fin F.n → RDesc I, ∀ p, T.depth p < N → RealInv T cl α D p := by
  induction N with
  | zero => exact ⟨fun _ => rdesc0 I, fun p h => absurd h (Nat.not_lt_zero _)⟩
  | succ N ih =>
    classical
    obtain ⟨D, hD⟩ := ih
    have hstep : ∀ p, ∃ Dp, T.depth p = N →
        DGood (AS cl (T.bag p)) Dp ∧ Realizes (AS cl (T.bag p)) Dp (α p) ∧
        (∀ q, T.parent p = some q → ∀ Y ∈ AS cl (bagm T p), rshift Dp Y = rshift (D q) Y) := by
      intro p
      by_cases hp : T.depth p = N
      · cases hpar : T.parent p with
        | none =>
          obtain ⟨Dp, h⟩ := real_step hk hcl α hagree hsat hinit p (rdesc0 I)
            (fun q h => by rw [hpar] at h; simp at h)
          exact ⟨Dp, fun _ => ⟨h.1, h.2.1, fun q h' => by simp at h'⟩⟩
        | some q =>
          have hq := hD q (by have := T.depth_lt p q hpar; omega)
          obtain ⟨Dp, h⟩ := real_step hk hcl α hagree hsat hinit p (D q)
            (fun q' h' => by rw [hpar] at h'; cases h'; exact ⟨hq.1, hq.2.1⟩)
          refine ⟨Dp, fun _ => ⟨h.1, h.2.1, fun q' h' => ?_⟩⟩
          cases Option.some.inj h'
          exact h.2.2 q hpar
      · exact ⟨D p, fun h => absurd h hp⟩
    choose Dn hDn using hstep
    refine ⟨fun p => if T.depth p < N then D p else Dn p, fun p hp => ?_⟩
    have hpar : ∀ q, T.parent p = some q → T.depth q < N := fun q h => by
      have := T.depth_lt p q h; omega
    by_cases hlt : T.depth p < N
    · obtain ⟨h1, h2, h3⟩ := hD p hlt
      refine ⟨by simpa [hlt] using h1, by simpa [hlt] using h2, fun q hq Y hY => ?_⟩
      simp only [hlt, if_true, hpar q hq]
      exact h3 q hq Y hY
    · obtain ⟨h1, h2, h3⟩ := hDn p (by omega)
      refine ⟨by simpa [hlt] using h1, by simpa [hlt] using h2, fun q hq Y hY => ?_⟩
      simp only [hlt, if_false, hpar q hq, if_true]
      exact h3 q hq Y hY

lemma real_all : ∃ D : Fin F.n → RDesc I, ∀ p, RealInv T cl α D p := by
  obtain ⟨D, hD⟩ := real_upto hk hcl α hagree hsat hinit (Finset.univ.sup T.depth + 1)
  exact ⟨D, fun p => hD p (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ p)))⟩

end

/-- Translations of the classes of a bag agree with those at the vertex introducing them. -/
lemma rshift_chain {α : Fin F.n → Val I} {D : Fin F.n → RDesc I}
    (hD : ∀ p, RealInv T cl α D p) :
    ∀ n p r, T.depth p < n → r ∈ bagm T p → rshift (D p) (cl r) = rshift (D r) (cl r) := by
  intro n
  induction n with
  | zero => intro p r h; omega
  | succ n ih =>
    intro p r hp hr
    cases hpar : T.parent p with
    | none => rw [bagm_root T hpar] at hr; simp at hr
    | some q =>
      rw [(hD p).2.2 q hpar (cl r) (Finset.mem_image_of_mem _ hr)]
      have hrq : r ∈ T.bag q := T.bag_sub p q hpar hr
      by_cases hrq' : r = q
      · rw [hrq']
      · exact ih q r (by have := T.depth_lt p q hpar; omega) (Finset.mem_erase.mpr ⟨hrq', hrq⟩)

/-- **Local realization.** -/
theorem local_realization (hk : 3 ≤ k) (T : OneVertexForest F.graph k) (h₀ : RHom I F 0)
    (α : Fin F.n → Val I)
    (hagree : ∀ p q, T.parent p = some q → ∀ v a, IsAddress a →
      supp a ⊆ Iloc (AS (fun p => (vx (h₀.1 p)).1) (bagm T p)) v → α p (v, a) = α q (v, a))
    (hsat : ∀ p, SatEqs (AS (fun p => (vx (h₀.1 p)).1) (T.bag p)) (α p))
    (hinit : ∀ p, InitAgree (AS (fun p => (vx (h₀.1 p)).1) (T.bag p)) (α p)) :
    Nonempty (RHom I F 1) := by
  set cl : Fin F.n → ICls I := fun p => (vx (h₀.1 p)).1 with hcl_def
  have hcl : ∀ p, cl p ∈ classes I := fun p => (mem_verts_zero.mp (vx_mem (h₀.1 p))).1
  obtain ⟨D, hD⟩ := real_all hk hcl α hagree hsat hinit
  have hmem : ∀ p, tr (D p) (cl p, 0) ∈ verts I 1 := fun p =>
    tr_mem (D p) (hD p).1.init (hD p).1.mask
      ((mem_names I).mpr ⟨hcl p, zero_mem_labs (hcl p)⟩)
  let ψ : Fin F.n → Fin (rsGraph I 1).n := fun p => ix 1 _ (hmem p)
  have hAsub : ∀ p, AS cl (T.bag p) ⊆ classes I := fun p X hX => by
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hX
    exact hcl r
  -- the image of `r ∈ bagm p` is also given by the description of `p`
  have hchain : ∀ p r, r ∈ bagm T p → vx (ψ r) = tr (D p) (cl r, 0) := by
    intro p r hr
    simp only [ψ, vx_ix, tr]
    rw [rshift_chain T cl hD _ p r (Nat.lt_succ_self _) hr]
  have hadj : ∀ p r, r ∈ bagm T p → F.graph.Adj p r →
      (rsGraph I 1).graph.Adj (ψ p) (ψ r) := by
    intro p r hr hpr
    rw [rs_adj, hchain p r hr]
    have hp : vx (ψ p) = tr (D p) (cl p, 0) := by simp [ψ]
    rw [hp]
    have hpb : cl p ∈ AS cl (T.bag p) := Finset.mem_image_of_mem _ (T.mem_bag p)
    have hrb : cl r ∈ AS cl (T.bag p) :=
      Finset.mem_image_of_mem _ (Finset.mem_of_mem_erase hr)
    have h0 := (h₀.1.map_rel hpr : (rsGraph I 0).graph.Adj _ _)
    rw [rs_adj] at h0
    exact (radj_tr (D p) (x := (cl p, 0)) (y := (cl r, 0)) (edgeOK_of (hD p).1 (hAsub p) hpb)
      (edgeOK_of (hD p).1 (hAsub p) hrb)).mp (radj_zero h0)
  refine ⟨⟨⟨ψ, fun {p r} hpr => ?_⟩, fun p => ?_⟩⟩
  · rcases T.adj_mem p r hpr with h | h
    · exact hadj p r h hpr
    · exact (hadj r p h hpr.symm).symm
  · rw [← h₀.2 p, rs_color, rs_color]
    show code I (vx (ix 1 _ (hmem p))).1 = code I (vx (h₀.1 p)).1
    rw [vx_ix]
    rfl

end Lax119563Proofs.RowSpace

end RowSpace_Realize

/-! ### Formerly `Lax119563Proofs.RowSpace.SpoilerInfer` -/

section RowSpace_SpoilerInfer

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

end RowSpace_SpoilerInfer

/-! ### Formerly `Lax119563Proofs.RowSpace.Spoiler` -/

section RowSpace_Spoiler

/-!
# Spoiler's strategy on the row-space graphs

Spoiler follows a derivation of the conflict backwards; each schema gadget is traversed by
sweeping its `k + 2` stages (`O(k)` rounds each), so following an inference costs `O(k²)`
rounds independently of `ℓ`.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ParitySystems
open Lax119563.ColoredGraphs Lax119563.PebbleGame
open Lax119563Proofs.Matrix

namespace Lax119563Proofs.RowSpace

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

local notation "G₀" => rsGraph I 0
local notation "G₁" => rsGraph I 1

/-- An initial fact cannot be discrepant: the singleton coordinate classes force the
initialized value. -/
lemma not_rdisc_initial (hk : 0 < k) {S : RSt I}
    {X : Fin I.numLocations × (Fin k → BlockCoord ℓ)} {b : ZMod 2}
    (hX : (X, b) ∈ I.toParitySystem.known 0) (hD : RDisc S X b) : False := by
  obtain ⟨ι, hι, rfl, ha, hs⟩ := hX
  simp only at hι ha hs
  obtain ⟨g, hg, himg, lab, hH, hsum, -⟩ := hD
  have hlab : ∀ i, (lab i).1 = initSeed I X.1 (g i) := by
    intro i
    obtain ⟨p, q, -, -, h3⟩ := hH i
    have hm := vx_mem q
    rw [mem_verts, mem_names, h3] at hm
    obtain ⟨-, hl⟩ := hm
    simp only [labs, off, hι, Option.isSome_some, if_true, Finset.mem_singleton, one_smul] at hl
    have h1 : (lab i).1 + initSeed I X.1 (g i) = 0 := congrArg Prod.fst hl
    calc (lab i).1 = (lab i).1 + (initSeed I X.1 (g i) + initSeed I X.1 (g i)) := by
          rw [zmod2_self_add, add_zero]
      _ = ((lab i).1 + initSeed I X.1 (g i)) + initSeed I X.1 (g i) := by ring
      _ = initSeed I X.1 (g i) := by rw [h1, zero_add]
  simp_rw [hlab] at hsum
  have : ∑ i, initSeed I X.1 (g i) = dot (ind X.2) (initSeed I X.1) := by
    rw [dot_ind_eq_sum_supp, ← himg, Finset.sum_image fun x _ y _ h => hg h]
  rw [this, dot_initSeed hι hk] at hsum
  have h' : b + 1 = b + 0 := by rw [← hsum, add_zero]
  exact one_ne_zero (add_left_cancel h')

/-- **Spoiler's walk.** From a discrepant fact derived in round `ρ`, Spoiler wins within
`stepCostR k * ρ` rounds. -/
theorem rwalk (hk : 0 < k) :
    ∀ (ρ : ℕ) (S : RSt I) (X : Fin I.numLocations × (Fin k → BlockCoord ℓ)) (b : ZMod 2),
      (X, b) ∈ I.toParitySystem.known ρ → RDisc S X b → SWins (stepCostR k * ρ) S
  | 0, S, X, b, hX, hD => absurd (not_rdisc_initial hk hX hD) id
  | ρ + 1, S, X, b, hX, hD => by
    rcases known_succ_cases I hX with hX | ⟨e, a, ha, hsa, i₀, rfl, bf, hbf, rfl⟩
    · exact (rwalk hk ρ S X b hX hD).mono (Nat.mul_le_mul_left _ (Nat.le_succ ρ))
    · have := rstep hk ha hsa i₀ bf hD (stepCostR k * ρ) fun S' ⟨i, hi, hD'⟩ =>
        rwalk hk ρ S' _ _ (hbf i hi) hD'
      exact this.mono (by rw [Nat.mul_succ])

/-- The round constant of Spoiler's strategy (depends only on `k`):
`(4k + 1)(k + 2) + 6k`. -/
def spoilerConst (k : ℕ) : ℕ := stepCostR k + 2 * k

/-- **Part (1) of the row-space compiler.** -/
theorem spoilerWins (hk : 3 ≤ k) {τ : ℕ} (hτ : I.conflictRound = τ) :
    SpoilerWinsWithin (k + 1) (spoilerConst k * (τ + 1)) (rsGraph I 0) (rsGraph I 1) := by
  classical
  obtain ⟨X, h0, h1⟩ := hasConflict_of_conflictRound I hτ
  obtain ⟨ha, hs⟩ := known_valid I h0
  let cls : Fin k → ICls I := fun i => .coord X.1 (i, X.2 i)
  have hval : ∀ i, cls i ∈ classes I := fun i =>
    mem_classes_coord.mpr (hs (mem_supp_iff.mpr rfl))
  have hfill := rforces_fill (List.finRange k) (List.nodup_finRange k)
    (S := fun _ => none) (fun _ _ _ _ _ _ h => by simp at h) cls hval
  rw [List.length_finRange] at hfill
  have hwin := hfill (stepCostR k * τ) fun S' ⟨h1', _, hPI⟩ => by
    choose lab hlab using fun i => h1' i (List.mem_finRange i)
    have hdisc : RDisc S' X (∑ i, (lab i).1 + 1) := by
      refine ⟨fun i => (i, X.2 i), fun i j h => congrArg Prod.fst h, rfl, lab, hlab, ?_, hPI⟩
      rw [add_assoc, zmod2_self_add, add_zero]
    have hfact : (X, ∑ i, (lab i).1 + 1) ∈ I.toParitySystem.known τ := by
      rcases zmod2_eq_zero_or_one (∑ i, (lab i).1 + 1) with h | h <;> rw [h] <;> assumption
    exact rwalk (by omega) τ S' X _ hfact hdisc
  intro hsurv
  apply hwin.mono _ hsurv.2
  have h2 : spoilerConst k * (τ + 1) = stepCostR k * τ + 2 * k + (stepCostR k + 2 * k * τ) := by
    unfold spoilerConst; ring
  omega

end Lax119563Proofs.RowSpace

end RowSpace_Spoiler

/-! ### Formerly `Lax119563Proofs.RowSpace.TreeLike` -/

section RowSpace_TreeLike

/-!
# Tree-like linear systems and contradiction trees

A list of equations is *tree-like* if every equation shares at most one variable with the
equations after it in the list (so its incidence graph is a forest). If a tree-like system of
equations of a parity system `P`, together with a set `U` of initial facts of `P`, has no
solution over `𝔽₂`, then `P` has a contradiction tree with at most
`1 + #equations + #U` nodes. Contradiction trees also transfer along maps of parity systems
that send equations injectively onto equations and initial facts to initial facts.
-/

open Lax119563.ParitySystems Lax119563.ContradictionTrees

namespace Lax119563Proofs.RowSpace

/-- The union of a list of finite sets. -/
def unionAll {V : Type*} [DecidableEq V] (hs : List (Finset V)) : Finset V :=
  hs.foldr (· ∪ ·) ∅

/-- Every equation shares at most one variable with the later ones. -/
inductive TreeLike {V : Type*} [DecidableEq V] : List (Finset V) → Prop
  | nil : TreeLike []
  | cons {h : Finset V} {hs : List (Finset V)} :
      (h ∩ unionAll hs).card ≤ 1 → TreeLike hs → TreeLike (h :: hs)

/-- Size bounds of contradiction trees are monotone. -/
theorem HasContradictionWithin.mono {V : Type*} [DecidableEq V] {P : ParitySystem V}
    {s s' : ℕ} (h : HasContradictionWithin P s) (hss : s ≤ s') :
    HasContradictionWithin P s' := by
  obtain ⟨X, s₀, s₁, h₀, h₁, hs⟩ := h
  exact ⟨X, s₀, s₁, h₀, h₁, hs.trans hss⟩

theorem subset_unionAll {V : Type*} [DecidableEq V] {hs : List (Finset V)} {g : Finset V}
    (hg : g ∈ hs) : g ⊆ unionAll hs := by
  induction hs with
  | nil => simp at hg
  | cons a t ih =>
    show g ⊆ a ∪ unionAll t
    rcases List.mem_cons.mp hg with rfl | hg
    · exact Finset.subset_union_left
    · exact (ih hg).trans Finset.subset_union_right

theorem zmod2_cases : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide

theorem zmod2_add_self : ∀ b : ZMod 2, b + b = 0 := by decide

/-- Two derivable facts `(X, 0), (X, 1) ∈ U` give a contradiction tree. -/
theorem hasContradiction_of_pair {V : Type*} [DecidableEq V] {P : ParitySystem V}
    {U : Finset (V × ZMod 2)} {sz : V × ZMod 2 → ℕ}
    (hU : ∀ u ∈ U, HasDerivationWithin P u (sz u)) {X : V} (h0 : (X, 0) ∈ U)
    (h1 : (X, 1) ∈ U) : HasContradictionWithin P (1 + ∑ u ∈ U, sz u) := by
  refine ⟨X, sz (X, 0), sz (X, 1), hU _ h0, hU _ h1, ?_⟩
  have hne : (X, (0 : ZMod 2)) ≠ (X, 1) := by simp
  have hsub : ({(X, 0), (X, 1)} : Finset (V × ZMod 2)) ⊆ U := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl <;> assumption
  have := Finset.sum_le_sum_of_subset (f := sz) hsub
  rw [Finset.sum_pair hne] at this
  omega

/-- Facts without a conflict are satisfiable. -/
theorem solve_facts {V : Type*} [DecidableEq V] (U : Finset (V × ZMod 2))
    (hU : ¬ ∃ X, (X, 0) ∈ U ∧ (X, 1) ∈ U) :
    ∀ u ∈ U, (fun X => if (X, (1 : ZMod 2)) ∈ U then (1 : ZMod 2) else 0) u.1 = u.2 := by
  rintro ⟨X, b⟩ hu
  rcases zmod2_cases b with rfl | rfl
  · show (if (X, (1 : ZMod 2)) ∈ U then (1 : ZMod 2) else 0) = 0
    rw [if_neg]
    intro h1
    exact hU ⟨X, hu, h1⟩
  · show (if (X, (1 : ZMod 2)) ∈ U then (1 : ZMod 2) else 0) = 1
    rw [if_pos hu]

/-- Generalization of `hasContradiction_of_unsolvable` to derivable facts with sizes. -/
theorem hasContradiction_aux {V : Type*} [DecidableEq V] (P : ParitySystem V)
    {hs : List (Finset V)} (htl : TreeLike hs) :
    ∀ (U : Finset (V × ZMod 2)) (sz : V × ZMod 2 → ℕ), (∀ h ∈ hs, h ∈ P.equations) →
      (∀ u ∈ U, HasDerivationWithin P u (sz u)) →
      (¬ ∃ y : V → ZMod 2, (∀ h ∈ hs, ∑ x ∈ h, y x = 0) ∧ ∀ u ∈ U, y u.1 = u.2) →
      HasContradictionWithin P (1 + hs.length + ∑ u ∈ U, sz u) := by
  induction htl with
  | nil =>
    intro U sz _ hU hun
    by_cases hc : ∃ X, (X, 0) ∈ U ∧ (X, 1) ∈ U
    · obtain ⟨X, h0, h1⟩ := hc
      exact HasContradictionWithin.mono (hasContradiction_of_pair hU h0 h1) (by simp)
    · exact absurd ⟨fun X => if (X, (1 : ZMod 2)) ∈ U then (1 : ZMod 2) else 0, by simp,
        solve_facts U hc⟩ hun
  | @cons h rest hcard _ ih =>
    intro U sz hmem hU hun
    have hh : h ∈ P.equations := hmem h List.mem_cons_self
    have hmem' : ∀ g ∈ rest, g ∈ P.equations := fun g hg => hmem g (List.mem_cons_of_mem _ hg)
    obtain ⟨x, hxh, hpriv⟩ : ∃ x ∈ h, ∀ Y ∈ h.erase x, Y ∉ unionAll rest := by
      by_cases hS : ∃ z ∈ h, z ∈ unionAll rest
      · obtain ⟨z, hzh, hzr⟩ := hS
        refine ⟨z, hzh, fun Y hY hYr => ?_⟩
        have := Finset.card_le_one.mp hcard Y
          (Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase hY, hYr⟩) z
          (Finset.mem_inter.mpr ⟨hzh, hzr⟩)
        exact Finset.ne_of_mem_erase hY this
      · have hne : h.Nonempty := by
          rw [← Finset.card_pos]; rcases P.card_equation h hh with h2 | h3 <;> omega
        obtain ⟨x, hx⟩ := hne
        exact ⟨x, hx, fun Y hY hYr => hS ⟨Y, Finset.mem_of_mem_erase hY, hYr⟩⟩
    have hprivg : ∀ g ∈ rest, ∀ z ∈ g, z ∉ h.erase x := fun g hg z hz hzh =>
      hpriv z hzh (subset_unionAll hg hz)
    have hlen : (h :: rest).length = rest.length + 1 := rfl
    rw [hlen]
    by_cases hA : ∃ Y ∈ h.erase x, (Y, 0) ∈ U ∧ (Y, 1) ∈ U
    · obtain ⟨Y, -, h0, h1⟩ := hA
      exact HasContradictionWithin.mono (hasContradiction_of_pair hU h0 h1) (by omega)
    by_cases hB : ∃ Y ∈ h.erase x, (Y, 0) ∉ U ∧ (Y, 1) ∉ U
    · obtain ⟨Y, hY, h0, h1⟩ := hB
      refine HasContradictionWithin.mono (ih U sz hmem' hU ?_) (by omega)
      rintro ⟨y, hyr, hyU⟩
      apply hun
      have hYh := Finset.mem_of_mem_erase hY
      refine ⟨Function.update y Y (∑ z ∈ h.erase Y, y z), ?_, ?_⟩
      · intro g hg
        rcases List.mem_cons.mp hg with hgh | hg
        · rw [hgh, ← Finset.add_sum_erase _ _ hYh, Function.update_self]
          have : ∑ z ∈ h.erase Y, Function.update y Y (∑ z ∈ h.erase Y, y z) z
              = ∑ z ∈ h.erase Y, y z :=
            Finset.sum_congr rfl (fun z hz =>
              Function.update_of_ne (Finset.ne_of_mem_erase hz) _ _)
          rw [this]
          exact zmod2_add_self _
        · rw [← hyr g hg]
          exact Finset.sum_congr rfl (fun z hz =>
            Function.update_of_ne (fun (hzY : z = Y) => hprivg g hg z hz (hzY ▸ hY)) _ _)
      · rintro ⟨Z, c⟩ hu
        have hZY : Z ≠ Y := by
          rintro rfl
          rcases zmod2_cases c with rfl | rfl
          · exact h0 hu
          · exact h1 hu
        rw [Function.update_of_ne hZY]
        exact hyU _ hu
    push Not at hA hB
    obtain ⟨b, hbmem, hbuniq⟩ : ∃ b : V → ZMod 2, (∀ Y ∈ h.erase x, (Y, b Y) ∈ U) ∧
        ∀ u ∈ U, u.1 ∈ h.erase x → u.2 = b u.1 := by
      refine ⟨fun Y => if (Y, (1 : ZMod 2)) ∈ U then 1 else 0, ?_, ?_⟩
      · intro Y hY
        by_cases h1 : (Y, (1 : ZMod 2)) ∈ U
        · simp only [if_pos h1]; exact h1
        · simp only [if_neg h1]; by_contra h0; exact h1 (hB Y hY h0)
      · rintro ⟨Z, c⟩ hu hZ
        rcases zmod2_cases c with rfl | rfl
        · show (0 : ZMod 2) = if (Z, (1 : ZMod 2)) ∈ U then 1 else 0
          rw [if_neg (hA Z hZ hu)]
        · show (1 : ZMod 2) = if (Z, (1 : ZMod 2)) ∈ U then 1 else 0
          rw [if_pos hu]
    obtain ⟨c, hc⟩ : ∃ c : ZMod 2, c = ∑ Y ∈ h.erase x, b Y := ⟨_, rfl⟩
    obtain ⟨d, hd⟩ : ∃ d : ℕ, d = 1 + ∑ Y ∈ h.erase x, sz (Y, b Y) := ⟨_, rfl⟩
    have hder : HasDerivationWithin P (x, c) d := by
      rw [hc, hd]
      exact .infer b (fun Y => sz (Y, b Y)) hh hxh (fun Y hY => hU _ (hbmem Y hY)) le_rfl
    obtain ⟨U', hU'⟩ : ∃ U' : Finset (V × ZMod 2),
        U' = U.filter (fun u => u.1 ∉ h.erase x ∧ u ≠ (x, c)) := ⟨_, rfl⟩
    have hmemU' : ∀ u, u ∈ U' ↔ u ∈ U ∧ u.1 ∉ h.erase x ∧ u ≠ (x, c) := by
      intro u; rw [hU', Finset.mem_filter]
    let sz' : V × ZMod 2 → ℕ := fun u => if u = (x, c) then d else sz u
    have hxc : (x, c) ∉ U' := fun hm => ((hmemU' _).mp hm).2.2 rfl
    have hU'' : ∀ u ∈ insert (x, c) U', HasDerivationWithin P u (sz' u) := by
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · simp only [sz', if_pos rfl]; exact hder
      · have hu' := (hmemU' u).mp hu
        simp only [sz', if_neg hu'.2.2]; exact hU u hu'.1
    have hun'' : ¬ ∃ y : V → ZMod 2, (∀ g ∈ rest, ∑ z ∈ g, y z = 0) ∧
        ∀ u ∈ insert (x, c) U', y u.1 = u.2 := by
      rintro ⟨y, hyr, hyU⟩
      apply hun
      have hyx : y x = c := hyU (x, c) (Finset.mem_insert_self _ _)
      refine ⟨fun Z => if Z ∈ h.erase x then b Z else y Z, ?_, ?_⟩
      · intro g hg
        rcases List.mem_cons.mp hg with hgh | hg
        · rw [hgh, ← Finset.add_sum_erase _ _ hxh]
          have e1 : (if x ∈ h.erase x then b x else y x) = c := by
            rw [if_neg (Finset.notMem_erase x h), hyx]
          have e2 : ∑ z ∈ h.erase x, (if z ∈ h.erase x then b z else y z) = c := by
            rw [hc]; exact Finset.sum_congr rfl (fun z hz => if_pos hz)
          simp only [e1, e2]
          exact zmod2_add_self _
        · rw [← hyr g hg]
          exact Finset.sum_congr rfl (fun z hz => if_neg (hprivg g hg z hz))
      · intro u hu
        by_cases hux : u.1 ∈ h.erase x
        · simp only [if_pos hux]; exact (hbuniq u hu hux).symm
        · simp only [if_neg hux]
          by_cases hxc' : u = (x, c)
          · subst hxc'; exact hyx
          · exact hyU u (Finset.mem_insert_of_mem ((hmemU' u).mpr ⟨hu, hux, hxc'⟩))
    refine HasContradictionWithin.mono (ih (insert (x, c) U') sz' hmem' hU'' hun'') ?_
    rw [Finset.sum_insert hxc]
    have h1 : sz' (x, c) = d := if_pos rfl
    have h2 : ∑ u ∈ U', sz' u = ∑ u ∈ U', sz u :=
      Finset.sum_congr rfl (fun u hu => if_neg ((hmemU' u).mp hu).2.2)
    have hT : ∑ u ∈ (h.erase x).image (fun Y => (Y, b Y)), sz u
        = ∑ Y ∈ h.erase x, sz (Y, b Y) :=
      Finset.sum_image (fun Y _ Z _ hYZ => congrArg Prod.fst hYZ)
    have hdisj : Disjoint ((h.erase x).image (fun Y => (Y, b Y))) U' := by
      rw [Finset.disjoint_left]
      intro u huT huU
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp huT
      exact ((hmemU' _).mp huU).2.1 hY
    have hsub : (h.erase x).image (fun Y => (Y, b Y)) ∪ U' ⊆ U := by
      intro u hu
      rcases Finset.mem_union.mp hu with hu | hu
      · obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hu; exact hbmem Y hY
      · exact ((hmemU' u).mp hu).1
    have := Finset.sum_le_sum_of_subset (f := sz) hsub
    rw [Finset.sum_union hdisj, hT] at this
    rw [h1, h2]
    omega

/-- **Unsolvable tree-like systems give contradiction trees.** -/
theorem hasContradiction_of_unsolvable {V : Type*} [DecidableEq V] (P : ParitySystem V)
    {hs : List (Finset V)} (htl : TreeLike hs) (hmem : ∀ h ∈ hs, h ∈ P.equations)
    (U : Finset (V × ZMod 2)) (hU : ∀ u ∈ U, u ∈ P.initial)
    (hun : ¬ ∃ y : V → ZMod 2, (∀ h ∈ hs, ∑ x ∈ h, y x = 0) ∧ ∀ u ∈ U, y u.1 = u.2) :
    HasContradictionWithin P (1 + hs.length + U.card) := by
  have := hasContradiction_aux P htl U (fun _ => 1) hmem
    (fun u hu => .initial (hU u hu) le_rfl) hun
  simpa using this

/-- Derivation trees transfer along maps as in `HasContradictionWithin.map`. -/
theorem HasDerivationWithin.map {V W : Type*} [DecidableEq V] [DecidableEq W]
    {P : ParitySystem V} {Q : ParitySystem W} (f : V → W)
    (heq : ∀ h ∈ P.equations, Set.InjOn f (h : Set V) ∧ h.image f ∈ Q.equations)
    (hinit : ∀ u ∈ P.initial, (f u.1, u.2) ∈ Q.initial) {u : V × ZMod 2} {s : ℕ}
    (hd : HasDerivationWithin P u s) : HasDerivationWithin Q (f u.1, u.2) s := by
  induction hd with
  | initial hf hs => exact .initial (hinit _ hf) hs
  | @infer X h s b size hh hX children hs ih =>
    obtain ⟨hinj, hQ⟩ := heq h hh
    have : Nonempty V := ⟨X⟩
    obtain ⟨g, hg⟩ : ∃ g : W → V, g = Function.invFunOn f (h : Set V) := ⟨_, rfl⟩
    have key : ∀ Y ∈ h, g (f Y) = Y := fun Y hY => by
      rw [hg]; exact hinj.leftInvOn_invFunOn hY
    have hE : (h.image f).erase (f X) = (h.erase X).image f := by
      ext Z
      simp only [Finset.mem_erase, Finset.mem_image]
      constructor
      · rintro ⟨hne, Y, hY, rfl⟩
        exact ⟨Y, ⟨fun hYX => hne (congrArg f hYX), hY⟩, rfl⟩
      · rintro ⟨Y, ⟨hYX, hY⟩, rfl⟩
        exact ⟨fun he => hYX (hinj hY hX he), Y, hY, rfl⟩
    have hinj' : Set.InjOn f ((h.erase X : Finset V) : Set V) :=
      hinj.mono (fun Y hY => Finset.mem_of_mem_erase hY)
    have e1 : ∑ Y ∈ h.erase X, b Y = ∑ Z ∈ (h.image f).erase (f X), b (g Z) := by
      rw [hE, Finset.sum_image hinj']
      exact Finset.sum_congr rfl (fun Y hY => by rw [key Y (Finset.mem_of_mem_erase hY)])
    have e2 : ∑ Y ∈ h.erase X, size Y = ∑ Z ∈ (h.image f).erase (f X), size (g Z) := by
      rw [hE, Finset.sum_image hinj']
      exact Finset.sum_congr rfl (fun Y hY => by rw [key Y (Finset.mem_of_mem_erase hY)])
    show HasDerivationWithin Q (f X, ∑ Y ∈ h.erase X, b Y) s
    rw [e1]
    refine .infer (fun Z => b (g Z)) (fun Z => size (g Z)) hQ (Finset.mem_image_of_mem f hX)
      ?_ (e2 ▸ hs)
    intro Z hZ
    rw [hE] at hZ
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hZ
    have hk := key Y (Finset.mem_of_mem_erase hY)
    show HasDerivationWithin Q (f Y, b (g (f Y))) (size (g (f Y)))
    rw [hk]
    exact ih Y hY

/-- **Transfer of contradiction trees** along a map sending every equation injectively onto an
equation and every initial fact to an initial fact. -/
theorem HasContradictionWithin.map {V W : Type*} [DecidableEq V] [DecidableEq W]
    {P : ParitySystem V} {Q : ParitySystem W} (f : V → W)
    (heq : ∀ h ∈ P.equations, Set.InjOn f (h : Set V) ∧ h.image f ∈ Q.equations)
    (hinit : ∀ u ∈ P.initial, (f u.1, u.2) ∈ Q.initial) {s : ℕ}
    (h : HasContradictionWithin P s) : HasContradictionWithin Q s := by
  obtain ⟨X, s₀, s₁, h₀, h₁, hs⟩ := h
  exact ⟨f X, s₀, s₁, HasDerivationWithin.map f heq hinit h₀,
    HasDerivationWithin.map f heq hinit h₁, hs⟩

end Lax119563Proofs.RowSpace

end RowSpace_TreeLike
