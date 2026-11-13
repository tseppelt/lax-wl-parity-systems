import Lax119563Proofs.Game.Colors
import Lax119563.PebbleGame

/-!
# Spoiler's strategy from a Weisfeiler–Leman distinction

If `k`-WL distinguishes `G` and `H` after `r` rounds, then Spoiler wins `BP_{k+1}(G, H)`
within `r + k` rounds: in the first `k` rounds he places pebbles `0, …, k-1` so that the
numbers of extensions with a fixed round-`r` color keep differing, ending in two
`k`-tuples with different round-`r` colors; from there `r` further rounds suffice.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.PebbleGame

namespace Lax119563Proofs.Game

variable {k : ℕ} {G H : ColoredGraph}

/-- Surviving `s + 1` rounds implies surviving `s` rounds. -/
theorem survivesFrom_of_succ {m : ℕ} :
    ∀ (s : ℕ) (S : GameState m G H), SurvivesFrom G H (s + 1) S → SurvivesFrom G H s S
  | 0, _, _ => trivial
  | s + 1, _, h => fun i =>
    let ⟨f, hf⟩ := h i
    ⟨f, fun p => ⟨(hf p).1, survivesFrom_of_succ s _ (hf p).2⟩⟩

/-- If pebbles `σ m` carry tuples `a`, `b` with different round-`s` colors, then the state
is not a partial isomorphism from which Duplicator survives `s` rounds. -/
theorem not_survivesFrom_of_color_ne :
    ∀ (s : ℕ) (S : GameState (k + 1) G H) (σ : Fin k → Fin (k + 1)), Function.Injective σ →
      ∀ (a : Fin k → Fin G.n) (b : Fin k → Fin H.n), (∀ m, S (σ m) = some (a m, b m)) →
        color G s a ≠ color H s b → ¬ (IsPartialIso G H S ∧ SurvivesFrom G H s S)
  | 0, S, σ, _, a, b, hS, hne, ⟨hPI, _⟩ =>
    hne (atp_eq_iff.mpr fun u v => hPI (σ u) (σ v) _ _ _ _ (hS u) (hS v))
  | s + 1, S, σ, hσ, a, b, hS, hne, ⟨hPI, hsurv⟩ => by
    classical
    by_cases h0 : color G s a = color H s b
    swap
    · exact not_survivesFrom_of_color_ne s S σ hσ a b hS h0
        ⟨hPI, survivesFrom_of_succ s S hsurv⟩
    have hmul : (Finset.univ : Finset (Fin G.n)).val.map
          (fun q l => color G s (Function.update a l q)) ≠
        (Finset.univ : Finset (Fin H.n)).val.map
          (fun q l => color H s (Function.update b l q)) := fun hm => hne (Prod.ext h0 hm)
    -- a pebble index not used by `σ`
    obtain ⟨i0, hi0⟩ : ∃ i0, ∀ m, σ m ≠ i0 := by
      by_contra hcon
      push Not at hcon
      have := Fintype.card_le_of_surjective σ fun i => (hcon i).imp fun _ h => h
      simp at this
    obtain ⟨f, hf⟩ := hsurv i0
    obtain ⟨q, hq⟩ : ∃ q, (fun l => color G s (Function.update a l q)) ≠
        (fun l => color H s (Function.update b l (f q))) := by
      by_contra hcon
      push Not at hcon
      apply hmul
      rw [show (fun q l => color G s (Function.update a l q)) =
          (fun q l => color H s (Function.update b l q)) ∘ f from funext hcon,
        ← Multiset.map_map, Multiset.map_univ_val_equiv]
    obtain ⟨l, hl⟩ := Function.ne_iff.mp hq
    refine not_survivesFrom_of_color_ne s (Function.update S i0 (some (q, f q)))
      (Function.update σ l i0) ?_ (Function.update a l q) (Function.update b l (f q)) ?_ hl
      (hf q)
    · intro u v huv
      by_cases hu : u = l <;> by_cases hv : v = l
      · rw [hu, hv]
      · subst hu
        simp only [Function.update_self, Function.update_of_ne hv] at huv
        exact absurd huv.symm (hi0 v)
      · subst hv
        simp only [Function.update_self, Function.update_of_ne hu] at huv
        exact absurd huv (hi0 u)
      · simp only [Function.update_of_ne hu, Function.update_of_ne hv] at huv
        exact hσ huv
    · intro m
      by_cases hm : m = l
      · subst hm; simp
      · simp only [Function.update_of_ne hm, Function.update_of_ne (hi0 m)]
        exact hS m

/-- The number of `k`-tuples of `G` that agree with `a` on the first `j` entries and have
round-`s` color `c`. -/
noncomputable def prefixCount (G : ColoredGraph) (s j : ℕ) (a : Fin k → Fin G.n)
    (c : Color k s) : ℕ := by
  classical
  exact (Finset.univ.filter fun p : Fin k → Fin G.n =>
    (∀ m : Fin k, m.val < j → p m = a m) ∧ color G s p = c).card

/-- Splitting the prefix count according to entry `j`. -/
theorem prefixCount_eq_sum (s j : ℕ) (a : Fin k → Fin G.n) (c : Color k s) (m0 : Fin k)
    (hm0 : m0.val = j) :
    prefixCount G s j a c = ∑ q, prefixCount G s (j + 1) (Function.update a m0 q) c := by
  classical
  unfold prefixCount
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p => p m0) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.filter_filter]
  congr 1
  refine Finset.filter_congr fun p _ => ?_
  constructor
  · rintro ⟨⟨hpre, hc⟩, hq⟩
    refine ⟨fun m hm => ?_, hc⟩
    by_cases hmm : m = m0
    · subst hmm; simpa using hq
    · rw [Function.update_of_ne hmm]
      exact hpre m (by have : m.val ≠ j := fun h => hmm (Fin.ext (h.trans hm0.symm)); omega)
  · rintro ⟨hpre, hc⟩
    refine ⟨⟨fun m hm => ?_, hc⟩, ?_⟩
    · have hmm : m ≠ m0 := fun h => by subst h; omega
      simpa [Function.update_of_ne hmm] using hpre m (by omega)
    · simpa using hpre m0 (by omega)

open Classical in
/-- The prefix count over all entries is the indicator of the color of the tuple. -/
theorem prefixCount_full (s : ℕ) (a : Fin k → Fin G.n) (c : Color k s) :
    prefixCount G s k a c = if color G s a = c then 1 else 0 := by
  classical
  unfold prefixCount
  have hfa : ∀ p : Fin k → Fin G.n, (∀ m : Fin k, m.val < k → p m = a m) ↔ p = a :=
    fun p => ⟨fun h => funext fun m => h m m.isLt, fun h m _ => h ▸ rfl⟩
  simp only [hfa]
  split_ifs with h
  · rw [Finset.card_eq_one]
    exact ⟨a, Finset.ext fun p => by simp only [Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_singleton]; exact ⟨fun h' => h'.1, fun h' => ⟨h', h' ▸ h⟩⟩⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro p - ⟨rfl, h'⟩
    exact h h'

/-- If, after the first `j` pebbles are placed on prefixes of `a` and `b`, some round-`s`
color has different numbers of extensions, then Duplicator does not survive the remaining
`s + t` rounds, where `j + t = k`. -/
theorem not_survivesFrom_of_prefixCount_ne (s : ℕ) :
    ∀ (t j : ℕ), j + t = k → ∀ (S : GameState (k + 1) G H) (a : Fin k → Fin G.n)
      (b : Fin k → Fin H.n), (∀ m : Fin k, m.val < j → S m.castSucc = some (a m, b m)) →
      (∃ c, prefixCount G s j a c ≠ prefixCount H s j b c) →
      ¬ (IsPartialIso G H S ∧ SurvivesFrom G H (s + t) S)
  | 0, j, hj, S, a, b, hS, ⟨c, hc⟩ => by
    have hjk : j = k := by omega
    subst j
    refine not_survivesFrom_of_color_ne s S Fin.castSucc (Fin.castSucc_injective k) a b
      (fun m => hS m m.isLt) fun heq => hc ?_
    rw [prefixCount_full, prefixCount_full, heq]
  | t + 1, j, hj, S, a, b, hS, ⟨c, hc⟩ => by
    rintro ⟨_, hsurv⟩
    let m0 : Fin k := ⟨j, by omega⟩
    obtain ⟨f, hf⟩ := hsurv m0.castSucc
    obtain ⟨q, hq⟩ : ∃ q, prefixCount G s (j + 1) (Function.update a m0 q) c ≠
        prefixCount H s (j + 1) (Function.update b m0 (f q)) c := by
      by_contra hcon
      push Not at hcon
      apply hc
      rw [prefixCount_eq_sum s j a c m0 rfl, prefixCount_eq_sum s j b c m0 rfl,
        ← Equiv.sum_comp f]
      exact Finset.sum_congr rfl fun q _ => hcon q
    refine not_survivesFrom_of_prefixCount_ne s t (j + 1) (by omega) _
      (Function.update a m0 q) (Function.update b m0 (f q)) (fun m hm => ?_) ⟨c, hq⟩ (hf q)
    by_cases hmm : m = m0
    · subst hmm; simp
    · have hne : m.castSucc ≠ m0.castSucc := fun h => hmm (Fin.castSucc_injective k h)
      rw [Function.update_of_ne hne, Function.update_of_ne hmm, Function.update_of_ne hmm]
      exact hS m (by have : m.val ≠ j := fun h => hmm (Fin.ext h); omega)

/-- If `k`-WL distinguishes `G` and `H` after `r` rounds, Spoiler wins `BP_{k+1}(G, H)`
within `r + k` rounds. -/
theorem spoilerWinsWithin_of_distinguishesAfter' (hk : 1 ≤ k) {r : ℕ}
    (h : DistinguishesAfter k r G H) : SpoilerWinsWithin (k + 1) (r + k) G H := by
  classical
  rintro ⟨hn, hsurv⟩
  obtain ⟨c, hc⟩ := h
  by_cases hG : G.n = 0
  · have h0 : ∀ {n : ℕ}, n = 0 → ∀ P : (Fin k → Fin n) → Prop, Nat.card {p // P p} = 0 := by
      intro n hn0 P
      rw [Nat.card_eq_zero]
      left
      exact ⟨fun p => absurd (p.1 ⟨0, hk⟩).isLt (by omega)⟩
    exact hc ((h0 hG _).trans (h0 (hn ▸ hG) _).symm)
  refine not_survivesFrom_of_prefixCount_ne r k 0 (by omega) (fun _ => none)
    (fun _ => ⟨0, by omega⟩) (fun _ => ⟨0, by omega⟩) (fun m hm => absurd hm (by omega))
    ⟨c, ?_⟩ ⟨fun _ _ _ _ _ _ h => by simp at h, hsurv⟩
  simpa [prefixCount, Nat.card_eq_fintype_card, Fintype.card_subtype] using hc

end Lax119563Proofs.Game
