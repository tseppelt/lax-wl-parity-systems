import Mathlib
import Lax119563.PebbleGame

/-!
# Colored graphs given by a list of vertex names

A colored graph whose vertices are the entries of a duplicate-free list of names: vertex `i`
is the `i`-th name, adjacency is a relation on names, and the color of a vertex is the
position of the first name of its class in the list. In particular colors are bounded by the
number of vertices, and two vertices have the same color iff their names have the same class.
-/

open Lax119563.ColoredGraphs

namespace Lax119563Proofs.Matrix

variable {α β : Type*} [DecidableEq β]

/-- The colored graph on the names of `L`. -/
@[reducible] def listGraph (L : List α) (adj : α → α → Prop) [DecidableRel adj] (hsymm : ∀ x y, adj x y → adj y x)
    (hirr : ∀ x, ¬ adj x x) (cls : α → β) : ColoredGraph where
  n := L.length
  graph :=
    { Adj := fun i j => adj L[i] L[j]
      symm := ⟨fun _ _ h => hsymm _ _ h⟩
      loopless := ⟨fun _ h => hirr _ h⟩ }
  color := fun i => L.findIdx fun x => decide (cls x = cls L[i])

variable (L : List α) (adj : α → α → Prop) [DecidableRel adj]
  (hsymm : ∀ x y, adj x y → adj y x) (hirr : ∀ x, ¬ adj x x) (cls : α → β)

@[simp] lemma listGraph_n : (listGraph L adj hsymm hirr cls).n = L.length := rfl

lemma listGraph_color_eq_iff (i j : Fin (listGraph L adj hsymm hirr cls).n) :
    (listGraph L adj hsymm hirr cls).color i = (listGraph L adj hsymm hirr cls).color j ↔
      cls (L[(i : ℕ)]'i.2) = cls (L[(j : ℕ)]'j.2) := by
  constructor
  · intro h
    change List.findIdx _ L = List.findIdx _ L at h
    have hi := List.findIdx_lt_length_of_exists
      (p := fun x => decide (cls x = cls (L[(i : ℕ)]'i.2)))
      ⟨L[(i : ℕ)]'i.2, List.getElem_mem _, by simp⟩
    have h1 := List.findIdx_getElem (w := hi)
    have h2 := List.findIdx_getElem (p := fun x => decide (cls x = cls (L[(j : ℕ)]'j.2)))
      (w := h ▸ hi)
    simp only [decide_eq_true_eq] at h1 h2
    have : L[L.findIdx fun x => decide (cls x = cls (L[(i : ℕ)]'i.2))]'hi =
        L[L.findIdx fun x => decide (cls x = cls (L[(j : ℕ)]'j.2))]'(h ▸ hi) := by
      congr 1
    rw [← h1, ← h2, this]
  · intro h
    simp only [listGraph, Fin.getElem_fin]
    exact congrArg (fun b => L.findIdx fun x => decide (cls x = b)) h

end Lax119563Proofs.Matrix
