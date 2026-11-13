import Lax119563Proofs.Matrix.SpoilerWalk

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
