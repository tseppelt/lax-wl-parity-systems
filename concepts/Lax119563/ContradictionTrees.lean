import Lax119563.ParitySystems

/-!
---
title: Derivation and contradiction trees
type: definition
---
Fix a parity system $\mathcal P = (V, \mathcal H, K_0)$. A *derivation tree* of a fact
$(X, b) \in V \times \mathbb F_2$ is a finite rooted tree whose nodes are labeled by facts and
whose root is labeled $(X, b)$. It is either a single node with $(X, b) \in K_0$, or its root
uses an equation $h \in \mathcal H$ with $X \in h$ and has one child for every
$Y \in h \setminus \{X\}$, rooting a derivation tree of some fact $(Y, b_Y)$, such that
$b = \sum_{Y \in h \setminus \{X\}} b_Y$. A *contradiction tree* has a new root with two
children rooting derivation trees of $(X, 0)$ and $(X, 1)$ for some $X \in V$. The *size* of
either kind of tree is its number of nodes, including the new root in the contradiction case.

# Implementation notes

Only the sizes of trees matter here, so instead of the trees themselves we define when a fact
has a derivation tree with at most $s$ nodes, and when $\mathcal P$ has a contradiction tree
with at most $s$ nodes.
-/

namespace Lax119563.ContradictionTrees

open Lax119563.ParitySystems

variable {V : Type*} [DecidableEq V]

/-- The fact `f` has a derivation tree in `P` with at most `s` nodes. Either `f` is an initial
fact, or `f = (X, ∑_{Y ∈ h \ {X}} b_Y)` is inferred from an equation `h ∋ X` and derivation
trees of the facts `(Y, b_Y)` with at most `s_Y` nodes each, where `1 + ∑_Y s_Y ≤ s`. -/
inductive HasDerivationWithin (P : ParitySystem V) : V × ZMod 2 → ℕ → Prop
  | initial {f : V × ZMod 2} {s : ℕ} (hf : f ∈ P.initial) (hs : 1 ≤ s) :
      HasDerivationWithin P f s
  | infer {X : V} {h : Finset V} {s : ℕ} (b : V → ZMod 2) (size : V → ℕ)
      (hh : h ∈ P.equations) (hX : X ∈ h)
      (children : ∀ Y ∈ h.erase X, HasDerivationWithin P (Y, b Y) (size Y))
      (hs : 1 + ∑ Y ∈ h.erase X, size Y ≤ s) :
      HasDerivationWithin P (X, ∑ Y ∈ h.erase X, b Y) s

/-- `P` has a contradiction tree with at most `s` nodes: derivation trees of `(X, 0)` and
`(X, 1)` for some variable `X`, with at most `s - 1` nodes in total. -/
def HasContradictionWithin (P : ParitySystem V) (s : ℕ) : Prop :=
  ∃ X : V, ∃ s₀ s₁ : ℕ, HasDerivationWithin P (X, 0) s₀ ∧ HasDerivationWithin P (X, 1) s₁ ∧
    1 + s₀ + s₁ ≤ s

end Lax119563.ContradictionTrees
