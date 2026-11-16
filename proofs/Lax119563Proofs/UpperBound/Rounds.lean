import Lax119563.WeisfeilerLeman
import Lax119563.Stabilization

/-!
# Distinguishing rounds are bounded by the stabilization round

If `k`-WL stabilizes after `r` rounds on both `G` and `H` and distinguishes them, then it
distinguishes them after at most `r + 1` rounds (paper, fact `wl-compare`).

The argument: if both graphs are stable after `s` rounds and `G`, `H` are not distinguished
after `s + 1` rounds, then any two tuples (of `G` or `H`) with the same round-`s` color have the
same round-`(s+1)` color. Hence round-`(s+1)` colors determine round-`(s+2)` colors uniformly
across both graphs, and `G`, `H` are not distinguished after `s + 2` rounds either.
Stability persists, so by induction `G`, `H` are never distinguished after a round `> r + 1`.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.Stabilization

namespace Lax119563Proofs.UpperBound

/-- Transporting a multiset equality along a relation of the mapping functions. -/
theorem multiset_map_eq_of_map_eq {α β γ δ : Type*} {f : α → γ} {g : β → γ} {f' : α → δ}
    {g' : β → δ} (h : ∀ a b, f a = g b → f' a = g' b) :
    ∀ (s : Multiset α) (t : Multiset β), s.map f = t.map g → s.map f' = t.map g' := by
  classical
  intro s
  induction s using Multiset.induction_on with
  | empty =>
    intro t ht
    have : t = 0 := by simpa [eq_comm] using ht
    simp [this]
  | cons a s ih =>
    intro t ht
    rw [Multiset.map_cons] at ht
    have hmem : f a ∈ t.map g := ht ▸ Multiset.mem_cons_self _ _
    obtain ⟨b, hb, hfb⟩ := Multiset.mem_map.1 hmem
    rw [← Multiset.cons_erase hb] at ht ⊢
    rw [Multiset.map_cons, hfb] at ht
    have ht' := (Multiset.cons_inj_right _).1 ht
    rw [Multiset.map_cons, Multiset.map_cons, ih _ ht', h a b hfb.symm]

theorem not_distinguishesAfter_self (k r : ℕ) (A : ColoredGraph) :
    ¬ DistinguishesAfter k r A A := fun ⟨_, hc⟩ => hc rfl

theorem not_distinguishesAfter_symm {k r : ℕ} {A B : ColoredGraph}
    (h : ¬ DistinguishesAfter k r A B) : ¬ DistinguishesAfter k r B A :=
  fun ⟨c, hc⟩ => h ⟨c, Ne.symm hc⟩

theorem card_eq_of_not_distinguishesAfter {k r : ℕ} {A B : ColoredGraph}
    (h : ¬ DistinguishesAfter k r A B) (c : Color k r) :
    Nat.card {p : Fin k → Fin A.n // color A r p = c} =
      Nat.card {q : Fin k → Fin B.n // color B r q = c} :=
  not_not.1 fun hc => h ⟨c, hc⟩

/-- A tuple of `B` with color `c` yields a tuple of `A` with color `c`. -/
theorem exists_color_eq {k r : ℕ} {A B : ColoredGraph} (h : ¬ DistinguishesAfter k r A B)
    (y : Fin k → Fin B.n) : ∃ x : Fin k → Fin A.n, color A r x = color B r y := by
  have hy : Nat.card {q : Fin k → Fin B.n // color B r q = color B r y} ≠ 0 :=
    Nat.card_ne_zero.2 ⟨⟨⟨y, rfl⟩⟩, inferInstance⟩
  rw [← card_eq_of_not_distinguishesAfter h] at hy
  obtain ⟨⟨x, hx⟩⟩ := (Nat.card_ne_zero.1 hy).1
  exact ⟨x, hx⟩

/-- If `A` is stable after `s` rounds and `A`, `B` are not distinguished after `s + 1` rounds,
then tuples of `A` and `B` with equal round-`s` colors have equal round-`(s+1)` colors. -/
theorem color_succ_eq {k s : ℕ} {A B : ColoredGraph} (hA : StabilizesAfter k s A)
    (hAB : ¬ DistinguishesAfter k (s + 1) A B) {x : Fin k → Fin A.n} {y : Fin k → Fin B.n}
    (h : color A s x = color B s y) : color A (s + 1) x = color B (s + 1) y := by
  obtain ⟨x', hx'⟩ := exists_color_eq hAB y
  have h1 : color A s x' = color B s y := congrArg Prod.fst hx'
  rw [← hx']
  exact (hA x x').1 (h.trans h1.symm)

/-- Under the same hypotheses, equal round-`(s+1)` colors give equal round-`(s+2)` colors. -/
theorem color_succ_succ_eq {k s : ℕ} {A B : ColoredGraph} (hA : StabilizesAfter k s A)
    (hAB : ¬ DistinguishesAfter k (s + 1) A B) {p : Fin k → Fin A.n} {q : Fin k → Fin B.n}
    (h : color A (s + 1) p = color B (s + 1) q) : color A (s + 2) p = color B (s + 2) q := by
  have h2 : (Finset.univ : Finset (Fin A.n)).val.map
      (fun v i => color A s (Function.update p i v)) =
      (Finset.univ : Finset (Fin B.n)).val.map
      (fun v i => color B s (Function.update q i v)) := congrArg Prod.snd h
  change (color A (s + 1) p, (Finset.univ : Finset (Fin A.n)).val.map
      fun v i => color A (s + 1) (Function.update p i v)) =
    (color B (s + 1) q, (Finset.univ : Finset (Fin B.n)).val.map
      fun v i => color B (s + 1) (Function.update q i v))
  rw [h]
  congr 1
  exact multiset_map_eq_of_map_eq
    (fun v w hvw => funext fun i => color_succ_eq hA hAB (congrFun hvw i)) _ _ h2

/-- Stability persists. -/
theorem stabilizesAfter_succ {k s : ℕ} {A : ColoredGraph} (hA : StabilizesAfter k s A) :
    StabilizesAfter k (s + 1) A := fun _ _ =>
  ⟨fun h => color_succ_succ_eq hA (not_distinguishesAfter_self _ _ _) h,
    fun h => congrArg Prod.fst h⟩

theorem stabilizesAfter_add {k s : ℕ} {A : ColoredGraph} (hA : StabilizesAfter k s A) :
    ∀ j, StabilizesAfter k (s + j) A
  | 0 => hA
  | j + 1 => stabilizesAfter_succ (stabilizesAfter_add hA j)

theorem stabilizesAfter_mono {k s t : ℕ} {A : ColoredGraph} (hA : StabilizesAfter k s A)
    (hst : s ≤ t) : StabilizesAfter k t A := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hst
  exact stabilizesAfter_add hA j

/-- The induction step: not distinguished after `s + 1` rounds implies not distinguished after
`s + 2` rounds, when both graphs are stable after `s` rounds. -/
theorem not_distinguishesAfter_succ {k s : ℕ} {G H : ColoredGraph}
    (hG : StabilizesAfter k s G) (hH : StabilizesAfter k s H)
    (hGH : ¬ DistinguishesAfter k (s + 1) G H) : ¬ DistinguishesAfter k (s + 2) G H := by
  rintro ⟨e, he⟩
  by_cases hp : ∃ p, color G (s + 2) p = e
  · obtain ⟨p₀, rfl⟩ := hp
    obtain ⟨q₀, hq₀⟩ := exists_color_eq (not_distinguishesAfter_symm hGH) p₀
    have hpq : color G (s + 2) p₀ = color H (s + 2) q₀ :=
      color_succ_succ_eq hG hGH hq₀.symm
    have eG : Nat.card {p : Fin k → Fin G.n // color G (s + 2) p = color G (s + 2) p₀} =
        Nat.card {p : Fin k → Fin G.n // color G (s + 1) p = color G (s + 1) p₀} :=
      Nat.card_congr <| Equiv.subtypeEquivRight fun p =>
        ⟨fun h => congrArg Prod.fst h,
          fun h => color_succ_succ_eq hG (not_distinguishesAfter_self _ _ _) h⟩
    have eH : Nat.card {q : Fin k → Fin H.n // color H (s + 2) q = color G (s + 2) p₀} =
        Nat.card {q : Fin k → Fin H.n // color H (s + 1) q = color G (s + 1) p₀} := by
      rw [hpq, ← hq₀]
      exact Nat.card_congr <| Equiv.subtypeEquivRight fun q =>
        ⟨fun h => congrArg Prod.fst h,
          fun h => color_succ_succ_eq hH (not_distinguishesAfter_self _ _ _) h⟩
    exact he (by rw [eG, eH]; exact card_eq_of_not_distinguishesAfter hGH _)
  · push Not at hp
    have h0 : Nat.card {p : Fin k → Fin G.n // color G (s + 2) p = e} = 0 :=
      Nat.card_eq_zero.2 (Or.inl ⟨fun ⟨p, hp'⟩ => hp p hp'⟩)
    rw [h0] at he
    obtain ⟨⟨q₀, rfl⟩⟩ := (Nat.card_ne_zero.1 he.symm).1
    obtain ⟨p, hp'⟩ := exists_color_eq hGH q₀
    exact hp p (color_succ_succ_eq hG hGH hp')

/-- **Fact (wl-compare).** If `k`-WL stabilizes after `r` rounds on `G` and on `H` and
distinguishes `G` and `H`, then it distinguishes them after at most `r + 1` rounds. -/
theorem exists_distinguishesAfter_le {k r : ℕ} {G H : ColoredGraph}
    (hG : StabilizesAfter k r G) (hH : StabilizesAfter k r H) (hD : Distinguishes k G H) :
    ∃ R ≤ r + 1, DistinguishesAfter k R G H := by
  obtain ⟨R, hR⟩ := hD
  by_cases hRr : R ≤ r + 1
  · exact ⟨R, hRr, hR⟩
  by_cases h : DistinguishesAfter k (r + 1) G H
  · exact ⟨r + 1, le_rfl, h⟩
  exfalso
  have key : ∀ j, ¬ DistinguishesAfter k (r + 1 + j) G H := by
    intro j
    induction j with
    | zero => simpa using h
    | succ j ih =>
      have e1 : r + 1 + (j + 1) = r + j + 2 := by omega
      have e2 : r + 1 + j = r + j + 1 := by omega
      rw [e1]
      rw [e2] at ih
      exact not_distinguishesAfter_succ (stabilizesAfter_add hG j) (stabilizesAfter_add hH j) ih
  have e : R = r + 1 + (R - (r + 1)) := by omega
  rw [e] at hR
  exact key _ hR

end Lax119563Proofs.UpperBound
