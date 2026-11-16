import Mathlib
import Lax119563.ParitySystems

/-!
# Unit propagation along binary equations

Generic facts about unit propagation used for the counter: monotonicity, propagation along a
binary equation, a potential argument bounding the conflict round from below for systems of
binary equations, and the conflict round of a system that has some conflict.
-/

open Lax119563.ParitySystems

namespace Lax119563Proofs.Counter

variable {V : Type*} [DecidableEq V] (P : ParitySystem V)

theorem known_mono {r r' : ℕ} (h : r ≤ r') : P.known r ⊆ P.known r' := by
  induction r', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans Set.subset_union_left

/-- Propagation along a binary equation `X = Y`. -/
theorem known_succ_of_pair {X Y : V} (hXY : X ≠ Y) (hh : ({X, Y} : Finset V) ∈ P.equations)
    {r : ℕ} {b : ZMod 2} (hY : (Y, b) ∈ P.known r) : (X, b) ∈ P.known (r + 1) := by
  refine Or.inr ⟨{X, Y}, hh, Finset.mem_insert_self _ _, fun _ => b, ?_, ?_⟩
  · intro Z hZ hZX
    simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
    rcases hZ with rfl | rfl
    · exact absurd rfl hZX
    · exact hY
  · rw [Finset.erase_insert (by simpa using hXY)]
    simp

/-- **Potential bound.** If every equation consists of two variables whose potentials differ
by at most one, the initial facts with value `0` have potential `0` and those with value `1`
have potential at least `D`, then after `r` rounds every fact `X = 0` has potential at most
`r` and every fact `X = 1` has potential at least `D - r`. -/
theorem known_potential (Φ : V → ℕ) (D : ℕ)
    (heq : ∀ h ∈ P.equations, ∃ X Y, X ≠ Y ∧ h = {X, Y} ∧ Φ X ≤ Φ Y + 1 ∧ Φ Y ≤ Φ X + 1)
    (hinit : ∀ f ∈ P.initial, (f.2 = 0 ∧ Φ f.1 = 0) ∨ (f.2 = 1 ∧ D ≤ Φ f.1)) :
    ∀ r, ∀ f ∈ P.known r, (f.2 = 0 ∧ Φ f.1 ≤ r) ∨ (f.2 = 1 ∧ D ≤ Φ f.1 + r) := by
  intro r
  induction r with
  | zero =>
    intro f hf
    rcases hinit f hf with h | h
    · exact Or.inl ⟨h.1, by omega⟩
    · exact Or.inr ⟨h.1, by omega⟩
  | succ r ih =>
    intro f hf
    rcases hf with hf | ⟨h, hh, hfh, b, hb, hsum⟩
    · rcases ih f hf with h | h
      · exact Or.inl ⟨h.1, by omega⟩
      · exact Or.inr ⟨h.1, by omega⟩
    · obtain ⟨X, Y, hXY, rfl, h1, h2⟩ := heq h hh
      -- the fact concerns one of the two variables; the other one is known
      have key : ∀ A B : V, A ≠ B → Φ A ≤ Φ B + 1 → Φ B ≤ Φ A + 1 →
          f.1 = A → ({A, B} : Finset V) = {X, Y} →
          (f.2 = 0 ∧ Φ f.1 ≤ r + 1) ∨ (f.2 = 1 ∧ D ≤ Φ f.1 + (r + 1)) := by
        intro A B hAB hA hB hfA hAB'
        have hBmem : B ∈ ({X, Y} : Finset V) := by rw [← hAB']; simp
        have hBk := hb B hBmem (by rw [hfA]; exact Ne.symm hAB)
        have hf2 : f.2 = b B := by
          rw [hsum, hfA, ← hAB', Finset.erase_insert (by simpa using hAB)]
          simp
        rcases ih _ hBk with h' | h'
        · exact Or.inl ⟨hf2.trans h'.1, by rw [hfA]; dsimp at h'; omega⟩
        · exact Or.inr ⟨hf2.trans h'.1, by rw [hfA]; dsimp at h'; omega⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hfh
      rcases hfh with hfX | hfY
      · exact key X Y hXY h1 h2 hfX rfl
      · exact key Y X (Ne.symm hXY) h2 h1 hfY (Finset.pair_comm _ _)

theorem conflict_bound (Φ : V → ℕ) (D : ℕ)
    (heq : ∀ h ∈ P.equations, ∃ X Y, X ≠ Y ∧ h = {X, Y} ∧ Φ X ≤ Φ Y + 1 ∧ Φ Y ≤ Φ X + 1)
    (hinit : ∀ f ∈ P.initial, (f.2 = 0 ∧ Φ f.1 = 0) ∨ (f.2 = 1 ∧ D ≤ Φ f.1))
    {r : ℕ} (hc : P.HasConflict r) : D ≤ 2 * r := by
  obtain ⟨X, h0, h1⟩ := hc
  rcases known_potential P Φ D heq hinit r _ h0 with h | h
  · rcases known_potential P Φ D heq hinit r _ h1 with h' | h'
    · exact absurd h'.1 (by simp)
    · dsimp at h h'; omega
  · exact absurd h.1 (by simp)

open Classical in
theorem conflictRound_eq_find (h : ∃ r, P.HasConflict r) :
    P.conflictRound = (Nat.find h : ℕ∞) := by
  classical
  unfold ParitySystem.conflictRound
  apply le_antisymm
  · exact iInf₂_le (Nat.find h) (Nat.find_spec h)
  · exact le_iInf₂ fun r hr => by exact_mod_cast Nat.find_min' h hr

end Lax119563Proofs.Counter
