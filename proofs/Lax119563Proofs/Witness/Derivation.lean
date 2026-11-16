import Mathlib
import Lax119563.ContradictionTrees

/-!
# Derivation trees, weights, and rounds

Generic facts about a parity system `P`:

* a *weight* on facts that is at most `1` on initial facts and subadditive along every
  inference bounds the size of every derivation tree from below; if opposite facts have
  weights summing to at least `M`, every contradiction tree has more than `M` nodes;
* a fact known after round `r` has a derivation tree with at most `2^(r+1) - 1` nodes, so a
  conflict in round `r` gives a contradiction tree with at most `2^(r+2) - 1` nodes;
* the conflict round is `Nat.find` of the existence of a conflict.
-/

open Lax119563.ParitySystems Lax119563.ContradictionTrees

namespace Lax119563Proofs.Witness

variable {V : Type*} [DecidableEq V]

theorem hasDerivationWithin_mono {P : ParitySystem V} {f : V × ZMod 2} {s s' : ℕ}
    (h : HasDerivationWithin P f s) (hs : s ≤ s') : HasDerivationWithin P f s' := by
  cases h with
  | initial hf h1 => exact .initial hf (by omega)
  | infer b size hh hX ch hs0 => exact .infer b size hh hX ch (by omega)

section Weight

variable (P : ParitySystem V) (w : V × ZMod 2 → ℕ)

/-- A weight on facts which is at most `1` on initial facts and does not increase along
inferences bounds the size of derivation trees from below. -/
theorem weight_le_of_derivation (hinit : ∀ f ∈ P.initial, w f ≤ 1)
    (hinfer : ∀ h ∈ P.equations, ∀ X ∈ h, ∀ b : V → ZMod 2,
      w (X, ∑ Y ∈ h.erase X, b Y) ≤ ∑ Y ∈ h.erase X, w (Y, b Y))
    {f : V × ZMod 2} {s : ℕ} (hd : HasDerivationWithin P f s) : w f ≤ s := by
  induction hd with
  | initial hf hs => exact (hinit _ hf).trans hs
  | @infer X h s b size hh hX children hs ih =>
    calc w (X, ∑ Y ∈ h.erase X, b Y) ≤ ∑ Y ∈ h.erase X, w (Y, b Y) := hinfer _ hh _ hX b
      _ ≤ ∑ Y ∈ h.erase X, size Y := Finset.sum_le_sum fun Y hY => ih Y hY
      _ ≤ s := by omega

/-- With such a weight, if opposite facts have weights summing to at least `M`, every
contradiction tree has more than `M` nodes. -/
theorem lt_of_hasContradictionWithin (hinit : ∀ f ∈ P.initial, w f ≤ 1)
    (hinfer : ∀ h ∈ P.equations, ∀ X ∈ h, ∀ b : V → ZMod 2,
      w (X, ∑ Y ∈ h.erase X, b Y) ≤ ∑ Y ∈ h.erase X, w (Y, b Y))
    (M : ℕ) (hM : ∀ X, M ≤ w (X, 0) + w (X, 1)) {s : ℕ} (h : HasContradictionWithin P s) :
    M < s := by
  obtain ⟨X, s₀, s₁, h₀, h₁, hs⟩ := h
  have := weight_le_of_derivation P w hinit hinfer h₀
  have := weight_le_of_derivation P w hinit hinfer h₁
  have := hM X
  omega

end Weight

section Rounds

variable (P : ParitySystem V)

theorem known_mono {r s : ℕ} (h : r ≤ s) : P.known r ⊆ P.known s := by
  induction s, h using Nat.le_induction with
  | base => exact le_rfl
  | succ s _ ih => exact ih.trans fun f hf => Or.inl hf

theorem derivation_of_known :
    ∀ r : ℕ, ∀ f ∈ P.known r, HasDerivationWithin P f (2 ^ (r + 1) - 1) := by
  intro r
  induction r with
  | zero =>
    intro f hf
    exact .initial hf (by norm_num)
  | succ r ih =>
    intro f hf
    rcases hf with hf | ⟨h, hh, hX, b, hb, hval⟩
    · exact hasDerivationWithin_mono (ih f hf)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) (by omega)) 1)
    · obtain ⟨X, c⟩ := f
      simp only at hX hb hval
      subst hval
      refine .infer b (fun _ => 2 ^ (r + 1) - 1) hh hX (fun Y hY => ?_) ?_
      · exact ih _ (hb Y (Finset.mem_of_mem_erase hY) (Finset.ne_of_mem_erase hY))
      · rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hX]
        have hc : h.card ≤ 3 := by rcases P.card_equation h hh with h2 | h3 <;> omega
        have hp : 1 ≤ 2 ^ (r + 1) := Nat.one_le_two_pow
        have : (h.card - 1) * (2 ^ (r + 1) - 1) ≤ 2 * (2 ^ (r + 1) - 1) :=
          Nat.mul_le_mul_right _ (by omega)
        rw [pow_succ 2 (r + 1)]
        omega

theorem hasContradictionWithin_of_hasConflict {r : ℕ} (h : P.HasConflict r) :
    HasContradictionWithin P (2 ^ (r + 2) - 1) := by
  obtain ⟨X, h₀, h₁⟩ := h
  refine ⟨X, _, _, derivation_of_known P r _ h₀, derivation_of_known P r _ h₁, ?_⟩
  have hp : 1 ≤ 2 ^ (r + 1) := Nat.one_le_two_pow
  rw [pow_succ 2 (r + 1)]
  omega

theorem exists_conflictRound_eq (h : ∃ r, P.HasConflict r) :
    ∃ τ : ℕ, P.conflictRound = τ ∧ P.HasConflict τ := by
  classical
  refine ⟨Nat.find h, ?_, Nat.find_spec h⟩
  unfold ParitySystem.conflictRound
  apply le_antisymm
  · exact iInf₂_le _ (Nat.find_spec h)
  · exact le_iInf₂ fun r hr => by exact_mod_cast Nat.find_min' h hr

end Rounds

end Lax119563Proofs.Witness
