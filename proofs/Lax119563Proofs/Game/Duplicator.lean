import Lax119563Proofs.Game.Colors
import Lax119563.PebbleGame

/-!
# Duplicator's strategy from equal Weisfeiler–Leman colors

If `k`-WL does not distinguish `G` and `H` after `r` rounds, then Duplicator survives `r`
rounds of `BP_{k+1}(G, H)` from the empty game state.

Duplicator maintains the following invariant with `s` rounds remaining: for every pebble
index `i` that Spoiler may lift, the remaining `k` pebble indices `i.succAbove m` can be
read as slots of a pair of `k`-tuples `a`, `b` with equal round-`s` colors, where every
placed pebble pair `i.succAbove m` sits on `(a m, b m)` (unplaced pebbles impose nothing).
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.PebbleGame

namespace Lax119563Proofs.Game

variable {k : ℕ} {G H : ColoredGraph}

/-- Duplicator's invariant with `s` rounds remaining. -/
def DupInv (k s : ℕ) (G H : ColoredGraph) (S : GameState (k + 1) G H) : Prop :=
  ∀ i : Fin (k + 1), ∃ a : Fin k → Fin G.n, ∃ b : Fin k → Fin H.n,
    color G s a = color H s b ∧ ∀ m pq, S (i.succAbove m) = some pq → pq = (a m, b m)

/-- Two tuples with equal atomic types give a partial-isomorphism condition on any two
of their slots. -/
theorem pi_cond_of_atp_eq {x : Fin k → Fin G.n} {y : Fin k → Fin H.n}
    (h : atp G x = atp H y) (u v : Fin k) :
    (x u = x v ↔ y u = y v) ∧ (G.graph.Adj (x u) (x v) ↔ H.graph.Adj (y u) (y v)) ∧
      G.color (x u) = H.color (y u) :=
  atp_eq_iff.mp h u v

/-- Duplicator survives `s` rounds from any state satisfying the invariant. -/
theorem survivesFrom_of_dupInv (hk : 2 ≤ k) :
    ∀ (s : ℕ) (S : GameState (k + 1) G H), DupInv k s G H S → SurvivesFrom G H s S
  | 0, _, _ => trivial
  | s + 1, S, hS => by
    classical
    intro i
    obtain ⟨a, b, hab, hcomp⟩ := hS i
    have hab0 : color G s a = color H s b := color_eq_of_color_succ_eq hab
    obtain ⟨f, hf⟩ := exists_equiv_of_map_univ_eq _ _ (multiset_eq_of_color_succ_eq hab)
    have hf' : ∀ q l, color G s (Function.update a l q) =
        color H s (Function.update b l (f q)) := fun q l => (congrFun (hf q) l).symm
    refine ⟨f, fun q => ⟨?_, survivesFrom_of_dupInv hk s _ ?_⟩⟩
    · -- the new state is a partial isomorphism
      -- every placed pair other than pebble `i` sits in the slots of `a`, `b`
      have hother : ∀ j p p', j ≠ i →
          Function.update S i (some (q, f q)) j = some (p, p') →
            ∃ m, p = a m ∧ p' = b m := by
        intro j p p' hj h
        obtain ⟨m, rfl⟩ := Fin.exists_succAbove_eq hj
        rw [Function.update_of_ne hj] at h
        have := hcomp m _ h
        simp only [Prod.mk.injEq] at this
        exact ⟨m, this.1, this.2⟩
      have hself : ∀ p p', Function.update S i (some (q, f q)) i = some (p, p') →
          p = q ∧ p' = f q := by
        intro p p' h
        simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨h.1.symm, h.2.symm⟩
      have hatp : ∀ l, atp G (Function.update a l q) = atp H (Function.update b l (f q)) :=
        fun l => atp_eq_of_color_eq (hf' q l)
      -- a slot different from a given one
      have hother_slot : ∀ m : Fin k, ∃ l, l ≠ m := by
        intro m
        by_cases hm : m.val = 0
        · exact ⟨⟨1, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
        · exact ⟨⟨0, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
      intro j1 j2 p1 q1 p2 q2 h1 h2
      by_cases hj1 : j1 = i <;> by_cases hj2 : j2 = i
      · subst hj1 hj2
        obtain ⟨rfl, rfl⟩ := hself _ _ h1
        obtain ⟨rfl, rfl⟩ := hself _ _ h2
        have := pi_cond_of_atp_eq (hatp ⟨0, by omega⟩) ⟨0, by omega⟩ ⟨0, by omega⟩
        simpa using this
      · subst hj1
        obtain ⟨rfl, rfl⟩ := hself _ _ h1
        obtain ⟨m2, rfl, rfl⟩ := hother _ _ _ hj2 h2
        obtain ⟨l, hl⟩ := hother_slot m2
        have := pi_cond_of_atp_eq (hatp l) l m2
        simpa [Function.update_of_ne hl.symm] using this
      · subst hj2
        obtain ⟨m1, rfl, rfl⟩ := hother _ _ _ hj1 h1
        obtain ⟨rfl, rfl⟩ := hself _ _ h2
        obtain ⟨l, hl⟩ := hother_slot m1
        have := pi_cond_of_atp_eq (hatp l) m1 l
        simpa [Function.update_of_ne hl.symm] using this
      · obtain ⟨m1, rfl, rfl⟩ := hother _ _ _ hj1 h1
        obtain ⟨m2, rfl, rfl⟩ := hother _ _ _ hj2 h2
        exact pi_cond_of_atp_eq (atp_eq_of_color_eq hab0) m1 m2
    · -- the invariant is preserved
      intro i'
      by_cases hi : i' = i
      · subst hi
        refine ⟨a, b, hab0, fun m pq h => ?_⟩
        rw [Function.update_of_ne (Fin.succAbove_ne _ _)] at h
        exact hcomp m pq h
      · obtain ⟨l0, hl0⟩ := Fin.exists_succAbove_eq hi
        let g : Fin k → Fin k := fun m =>
          if h : i'.succAbove m = i then l0
          else Classical.choose (Fin.exists_succAbove_eq h)
        refine ⟨Function.update a l0 q ∘ g, Function.update b l0 (f q) ∘ g,
          color_comp_eq g (hf' q l0), fun m pq h => ?_⟩
        by_cases hm : i'.succAbove m = i
        · rw [hm, Function.update_self] at h
          simp only [Option.some.injEq] at h
          subst h
          simp [g, hm]
        · have hspec := Classical.choose_spec (Fin.exists_succAbove_eq hm)
          set m' := Classical.choose (Fin.exists_succAbove_eq hm)
          have hgm : g m = m' := by simp [g, hm, m']
          have hm' : m' ≠ l0 := by
            rintro rfl
            rw [hl0] at hspec
            exact Fin.succAbove_ne i' m hspec.symm
          rw [Function.update_of_ne hm, ← hspec] at h
          simp only [Function.comp_apply, hgm, Function.update_of_ne hm']
          exact hcomp m' pq h

/-- Duplicator survives from any state if both graphs are empty. -/
theorem survivesFrom_of_n_eq_zero (hG : G.n = 0) (hH : H.n = 0) {m : ℕ} :
    ∀ (s : ℕ) (S : GameState m G H), SurvivesFrom G H s S
  | 0, _ => trivial
  | _ + 1, _ => fun _ => ⟨finCongr (hG.trans hH.symm), fun p => absurd p.isLt (by omega)⟩

/-- Equal color counts in round `r` give fiberwise bijections between the color classes. -/
theorem fiber_equivs_of_not_distinguishesAfter {r : ℕ} (h : ¬ DistinguishesAfter k r G H)
    (c : Color k r) :
    Nonempty ({p : Fin k → Fin G.n // color G r p = c} ≃
      {q : Fin k → Fin H.n // color H r q = c}) := by
  classical
  simp only [DistinguishesAfter, not_exists, not_not] at h
  exact ⟨Fintype.equivOfCardEq (by simpa [Nat.card_eq_fintype_card] using h c)⟩

/-- If `k`-WL does not distinguish `G` and `H` after `r` rounds, Duplicator survives `r`
rounds of `BP_{k+1}(G, H)`. -/
theorem duplicatorSurvives_of_not_distinguishesAfter (hk : 2 ≤ k) {r : ℕ}
    (h : ¬ DistinguishesAfter k r G H) : DuplicatorSurvives (k + 1) r G H := by
  have e := fun c => (fiber_equivs_of_not_distinguishesAfter h c).some
  have hn : G.n = H.n := by
    have := Fintype.card_congr (Equiv.ofFiberEquiv e)
    simp only [Fintype.card_fun, Fintype.card_fin] at this
    exact Nat.pow_left_injective (by omega) this
  refine ⟨hn, ?_⟩
  by_cases hG : G.n = 0
  · exact survivesFrom_of_n_eq_zero hG (hn ▸ hG) _ _
  · refine survivesFrom_of_dupInv hk r _ fun i => ?_
    let a : Fin k → Fin G.n := fun _ => ⟨0, by omega⟩
    let b := e (color G r a) ⟨a, rfl⟩
    exact ⟨a, b.1, b.2.symm, fun m pq h => by simp at h⟩

end Lax119563Proofs.Game
