import Mathlib
import Lax119563.WeisfeilerLeman

/-!
# Basic facts about Weisfeiler–Leman colors

* the round-`r` color of a tuple determines its atomic type;
* the round-`r` color of a reindexed tuple `x ∘ g` is a function of the color of `x`;
* equal multisets over the vertex sets yield a color-preserving bijection.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman

namespace Lax119563Proofs.Game

/-- Two maps on finite types with equal value multisets are related by a bijection. -/
theorem exists_equiv_of_map_univ_eq {α β γ : Type*} [Fintype α] [Fintype β]
    (F : α → γ) (F' : β → γ)
    (h : (Finset.univ : Finset α).val.map F = (Finset.univ : Finset β).val.map F') :
    ∃ e : α ≃ β, ∀ a, F' (e a) = F a := by
  classical
  have hfib : ∀ c, Nonempty ({a // F a = c} ≃ {b // F' b = c}) := by
    intro c
    refine ⟨Fintype.equivOfCardEq ?_⟩
    have hc := congrArg (Multiset.count c) h
    simp only [Multiset.count_map] at hc
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa [Finset.card, Finset.filter_val, eq_comm] using hc
  exact ⟨Equiv.ofFiberEquiv (fun c => (hfib c).some), fun a => Equiv.ofFiberEquiv_map _ a⟩

variable {k : ℕ}

/-- The color in round `r + 1` determines the color in round `r`. -/
theorem color_eq_of_color_succ_eq {G H : ColoredGraph} {r : ℕ} {x : Fin k → Fin G.n}
    {y : Fin k → Fin H.n} (h : color G (r + 1) x = color H (r + 1) y) :
    color G r x = color H r y :=
  congrArg Prod.fst h

/-- Equal colors in round `r + 1` give equal multisets of substituted color tuples. -/
theorem multiset_eq_of_color_succ_eq {G H : ColoredGraph} {r : ℕ} {x : Fin k → Fin G.n}
    {y : Fin k → Fin H.n} (h : color G (r + 1) x = color H (r + 1) y) :
    (Finset.univ : Finset (Fin G.n)).val.map
        (fun q i => color G r (Function.update x i q)) =
      (Finset.univ : Finset (Fin H.n)).val.map
        (fun q i => color H r (Function.update y i q)) :=
  congrArg Prod.snd h

/-- The color in any round determines the atomic type. -/
theorem atp_eq_of_color_eq {G H : ColoredGraph} :
    ∀ {r : ℕ} {x : Fin k → Fin G.n} {y : Fin k → Fin H.n},
      color G r x = color H r y → atp G x = atp H y
  | 0, _, _, h => h
  | _ + 1, _, _, h => atp_eq_of_color_eq (color_eq_of_color_succ_eq h)

/-- Unpacking equality of atomic types. -/
theorem atp_eq_iff {G H : ColoredGraph} {x : Fin k → Fin G.n} {y : Fin k → Fin H.n} :
    atp G x = atp H y ↔ ∀ u v : Fin k, (x u = x v ↔ y u = y v) ∧
      (G.graph.Adj (x u) (x v) ↔ H.graph.Adj (y u) (y v)) ∧ G.color (x u) = H.color (y u) := by
  constructor
  · intro h u v
    have h1 := congrFun (congrFun (congrArg AtomicType.eq h) u) v
    have h2 := congrFun (congrFun (congrArg AtomicType.adj h) u) v
    have h3 := congrFun (congrArg AtomicType.color h) u
    simp only [atp, decide_eq_decide] at h1 h2 h3
    exact ⟨h1, h2, h3⟩
  · intro h
    simp only [atp, AtomicType.mk.injEq]
    refine ⟨funext fun u => funext fun v => ?_, funext fun u => funext fun v => ?_,
      funext fun u => (h u u).2.2⟩
    · exact decide_eq_decide.mpr (h u v).1
    · exact decide_eq_decide.mpr (h u v).2.1

/-- Substituting into a reindexed tuple is reindexing a substituted tuple. -/
theorem exists_update_comp (g : Fin k → Fin k) (j : Fin k) :
    ∃ l : Fin k, ∃ g' : Fin k → Fin k, ∀ {V : Type} (x : Fin k → V) (q : V),
      Function.update (x ∘ g) j q = Function.update x l q ∘ g' := by
  classical
  by_cases hl : ∃ l, ∀ m, g m ≠ l
  · obtain ⟨l, hl⟩ := hl
    refine ⟨l, Function.update g j l, fun x q => funext fun m => ?_⟩
    by_cases hm : m = j
    · subst hm; simp
    · simp [Function.update_of_ne hm, Function.update_of_ne (hl m)]
  · push Not at hl
    have hinj : Function.Injective g := Finite.injective_iff_surjective.mpr hl
    refine ⟨g j, g, fun x q => funext fun m => ?_⟩
    by_cases hm : m = j
    · subst hm; simp
    · simp [Function.update_of_ne hm, Function.update_of_ne (hinj.ne hm)]

/-- The color of a reindexed tuple `x ∘ g` is a function of the color of `x`. -/
theorem exists_color_comp :
    ∀ (r : ℕ) (g : Fin k → Fin k), ∃ F : Color k r → Color k r,
      ∀ (G : ColoredGraph) (x : Fin k → Fin G.n), color G r (x ∘ g) = F (color G r x)
  | 0, g => ⟨fun t => ⟨fun i j => t.eq (g i) (g j), fun i j => t.adj (g i) (g j),
      fun i => t.color (g i)⟩, fun G x => by simp only [color, atp]; congr⟩
  | r + 1, g => by
    obtain ⟨F0, hF0⟩ := exists_color_comp r g
    choose l g' hg using exists_update_comp g
    choose F hF using fun j => exists_color_comp r (g' j)
    refine ⟨fun c => (F0 c.1, c.2.map fun t j => F j (t (l j))), fun G x => ?_⟩
    refine Prod.ext (hF0 G x) ?_
    rw [color, color]
    dsimp only
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun q _ => funext fun j => ?_
    simp only [Function.comp_apply, hg, hF]

/-- Reindexing preserves equality of colors. -/
theorem color_comp_eq {G H : ColoredGraph} {r : ℕ} (g : Fin k → Fin k)
    {x : Fin k → Fin G.n} {y : Fin k → Fin H.n} (h : color G r x = color H r y) :
    color G r (x ∘ g) = color H r (y ∘ g) := by
  obtain ⟨F, hF⟩ := exists_color_comp r g
  rw [hF, hF, h]

end Lax119563Proofs.Game
