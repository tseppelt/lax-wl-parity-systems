import Lax228581.Treewidth
import Lax871432.GraphClasses

/-!
---
title: Graphs of bounded treewidth
type: definition
---
For $k \geq 0$, the class $\mathcal T_k$ consists of all finite simple graphs of treewidth at
most $k$. It is closed under isomorphism, so it is a graph class.

# Implementation notes

Tree decompositions and treewidth are those of `Lax228581.Treewidth`, and graph classes those
of `Lax871432.GraphClasses`. Isomorphism invariance holds since an isomorphism carries a tree
decomposition to one with the same tree and bags of the same sizes.
-/

open Lax228581.Treewidth Lax871432.GraphClasses

namespace Lax119563.TreewidthClasses

/-- An isomorphism `e : F ≃g F'` carries a tree decomposition of `F` to one of `F'` with the
same tree and the images of the bags. -/
def mapTreeDecomposition {V W : Type} {F : SimpleGraph V} {F' : SimpleGraph W} (e : F ≃g F')
    (D : TreeDecomposition F) : TreeDecomposition F' where
  Node := D.Node
  nodeFintype := D.nodeFintype
  tree := D.tree
  isTree := D.isTree
  bag i := (D.bag i).map e.toEquiv.toEmbedding
  vertex_mem_bag v := by
    obtain ⟨i, hi⟩ := D.vertex_mem_bag (e.symm v)
    exact ⟨i, Finset.mem_map.2 ⟨e.symm v, hi, by simp⟩⟩
  edge_mem_bag u v huv := by
    obtain ⟨i, hu, hv⟩ := D.edge_mem_bag (e.symm.map_adj_iff.2 huv)
    exact ⟨i, Finset.mem_map.2 ⟨e.symm u, hu, by simp⟩, Finset.mem_map.2 ⟨e.symm v, hv, by simp⟩⟩
  bag_indices_connected v := by
    have h : {i | v ∈ (D.bag i).map e.toEquiv.toEmbedding} = {i | e.symm v ∈ D.bag i} := by
      ext i
      simp only [Set.mem_ofPred_eq, Finset.mem_map_equiv]
      rfl
    rw [h]
    exact D.bag_indices_connected (e.symm v)

theorem hasTreewidthAtMost_congr {V W : Type} {F : SimpleGraph V} {F' : SimpleGraph W}
    (e : F ≃g F') (w : ℕ) : HasTreewidthAtMost F w → HasTreewidthAtMost F' w := by
  rintro ⟨D, hD⟩
  exact ⟨mapTreeDecomposition e D, fun i => by
    simpa [mapTreeDecomposition] using hD i⟩

/-- The class `𝒯_k` of finite simple graphs of treewidth at most `k`. -/
def treewidthClass (k : ℕ) : GraphClass where
  Mem F := HasTreewidthAtMost F k
  mem_congr := by
    rintro V W _ _ F F' ⟨e⟩
    exact ⟨hasTreewidthAtMost_congr e k, hasTreewidthAtMost_congr e.symm k⟩

end Lax119563.TreewidthClasses
