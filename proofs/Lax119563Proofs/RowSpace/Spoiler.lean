import Lax119563Proofs.RowSpace.SpoilerInfer

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
