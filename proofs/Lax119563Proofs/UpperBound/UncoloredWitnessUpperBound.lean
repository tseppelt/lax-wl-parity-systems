import Lax119563.HomomorphismCharacterization
import Lax119563.UncoloredWitnessUpperBound
import Lax119563.WitnessUpperBound

/-!
# The witness size upper bound for uncolored graphs

An uncolored graph is viewed as a colored graph all of whose vertices have color `0` (after
transporting its vertex set to `Fin n`). Homomorphism counts between such graphs are the
uncolored ones, and a colored graph with a vertex of nonzero color has no homomorphism into
them, so a colored witness is effectively an uncolored one.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.ColoredHomomorphisms
  Lax871432.HomomorphismCounts Lax871432.HomomorphismIndistinguishability
  Lax871432.IsomorphismRelaxations Lax119563.TreewidthClasses

namespace Lax119563Proofs.UpperBound

/-- An uncolored graph as a colored graph on `Fin (card V)` with all colors `0`. -/
noncomputable def ofGraph {V : Type} [Fintype V] (G : SimpleGraph V) : ColoredGraph :=
  ⟨Fintype.card V, G.map (Fintype.equivFin V).toEmbedding, fun _ => 0⟩

/-- A graph on `Fin m` as a colored graph with all colors `0`. -/
def ofFinGraph {m : ℕ} (F : SimpleGraph (Fin m)) : ColoredGraph := ⟨m, F, fun _ => 0⟩

theorem hom_eq_homCount {F G : ColoredGraph} (hF : ∀ v, F.color v = 0)
    (hG : ∀ v, G.color v = 0) : hom F G = homCount F.graph G.graph :=
  Nat.card_congr (Equiv.subtypeUnivEquiv fun _ v => by rw [hF, hG])

theorem hom_eq_zero_of_color_ne {F G : ColoredGraph} (hG : ∀ v, G.color v = 0) (v : Fin F.n)
    (hv : F.color v ≠ 0) : hom F G = 0 :=
  Nat.card_eq_zero.2 (Or.inl ⟨fun ⟨_, hh⟩ => hv ((hh v).symm.trans (hG _))⟩)

theorem homCount_ofGraph {m : ℕ} (F : SimpleGraph (Fin m)) {V : Type} [Fintype V]
    (G : SimpleGraph V) : homCount F (ofGraph G).graph = homCount F G := by
  let e : G ≃g (ofGraph G).graph := SimpleGraph.Iso.map (Fintype.equivFin V) G
  exact Nat.card_congr
    { toFun f := e.symm.toHom.comp f
      invFun f := e.toHom.comp f
      left_inv _ := by ext a; simp
      right_inv _ := by ext a; simp }

/--
---
conclusion: Lax119563.UncoloredWitnessUpperBound.uncolored_witness_upper_bound
---
Give `G` and `H` the constant color `0` (on vertex sets `Fin |V|`, `Fin |W|`); homomorphism
counts from graphs with constant color `0` are the uncolored ones. A graph `F` of treewidth at
most `k` with `hom(F, G) ≠ hom(F, H)` therefore shows, via the homomorphism characterization of
`k`-WL, that `k`-WL distinguishes the colored versions. The colored witness size upper bound
yields a colored witness `F'` of treewidth at most `k` with at most
`2^{C n^{k-1} log₂ n}` vertices. Every vertex of `F'` has color `0`, since otherwise
`hom(F', G) = 0 = hom(F', H)`; so the underlying graph of `F'` is the required witness.
-/
theorem uncolored_witness_upper_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℕ, ∀ n : ℕ, 2 ≤ n →
      ∀ {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W),
        Fintype.card V ≤ n → Fintype.card W ≤ n → ¬ (G ≡[treewidthClass k] H) →
        ∃ (m : ℕ) (F : SimpleGraph (Fin m)), (treewidthClass k).Mem F ∧
          homCount F G ≠ homCount F H ∧ m ≤ 2 ^ (C * n ^ (k - 1) * Nat.log 2 n) := by
  obtain ⟨C, hC⟩ := Lax119563.WitnessUpperBound.witness_upper_bound k hk
  refine ⟨C, fun n hn V W _ _ G H hV hW hnot => ?_⟩
  change ¬ ∀ ⦃m : ℕ⦄ (F : SimpleGraph (Fin m)), (treewidthClass k).Mem F →
    homCount F G = homCount F H at hnot
  push Not at hnot
  obtain ⟨m, F, hF, hne⟩ := hnot
  have hG0 : ∀ v, (ofGraph G).color v = 0 := fun _ => rfl
  have hH0 : ∀ v, (ofGraph H).color v = 0 := fun _ => rfl
  have hD : Distinguishes k (ofGraph G) (ofGraph H) := by
    refine (Lax119563.HomomorphismCharacterization.distinguishes_iff_exists_hom_ne hk _ _).2
      ⟨ofFinGraph F, hF, ?_⟩
    rw [hom_eq_homCount (fun _ => rfl) hG0, hom_eq_homCount (fun _ => rfl) hH0]
    simpa only [ofFinGraph, homCount_ofGraph] using hne
  obtain ⟨F', htw, hne', hsize⟩ := hC n hn _ _ hV hW hD
  have hc : ∀ v, F'.color v = 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨v, hv⟩ := hc
    exact hne' (by rw [hom_eq_zero_of_color_ne hG0 v hv, hom_eq_zero_of_color_ne hH0 v hv])
  rw [hom_eq_homCount hc hG0, hom_eq_homCount hc hH0, homCount_ofGraph, homCount_ofGraph]
    at hne'
  exact ⟨F'.n, F'.graph, htw, hne', hsize⟩

end Lax119563Proofs.UpperBound
