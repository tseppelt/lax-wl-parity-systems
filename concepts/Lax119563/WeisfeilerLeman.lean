import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.SetTheory.Cardinal.Finite
import Lax119563.ColoredGraphs

/-!
---
title: The Weisfeiler–Leman algorithm
type: definition
---
Fix $k \geq 2$ and a colored graph $G$. For $\bar p = (p_1, \dots, p_k) \in V(G)^k$ and
$q \in V(G)$, let $\bar p[q/i]$ be the tuple obtained by replacing the $i$-th entry by $q$.

The *atomic type* $\operatorname{atp}_G(\bar p)$ of $\bar p$ records which entries are equal,
which entries are adjacent, and the colors of the entries; thus
$\operatorname{atp}_G(\bar p) = \operatorname{atp}_H(\bar q)$ if and only if
$p_i \mapsto q_i$ is a partial isomorphism.

The *$k$-dimensional Weisfeiler–Leman algorithm* ($k$-WL) computes colorings
$\chi^{(r)}_k[G]$ of $V(G)^k$ for $r \geq 0$, starting from
$\chi^{(0)}_k[G](\bar p) = \operatorname{atp}_G(\bar p)$ and setting
$$\chi^{(r+1)}_k[G](\bar p) = \Bigl(\chi^{(r)}_k[G](\bar p),\;
\{\{ (\chi^{(r)}_k[G](\bar p[q/1]), \dots, \chi^{(r)}_k[G](\bar p[q/k])) : q \in V(G) \}\}\Bigr),$$
where $\{\{\cdot\}\}$ denotes a multiset. Colors are defined syntactically, so colors of
tuples in different graphs can be compared.

For colored graphs $G, H$ and $r \geq 0$, $k$-WL *distinguishes $G$ and $H$ after $r$ rounds*
if some color $c$ satisfies
$$\bigl|\{\bar p \in V(G)^k : \chi^{(r)}_k[G](\bar p) = c\}\bigr| \neq
\bigl|\{\bar q \in V(H)^k : \chi^{(r)}_k[H](\bar q) = c\}\bigr|,$$
and $k$-WL *distinguishes* $G$ and $H$ if it does so after some number of rounds.

Each coloring $\chi^{(r+1)}_k[G]$ refines $\chi^{(r)}_k[G]$. We say that $k$-WL
*stabilizes after $r$ rounds* on $G$ if $\chi^{(r)}_k[G]$ and $\chi^{(r+1)}_k[G]$ induce the
same partition of $V(G)^k$.

# Implementation notes

The definitions are stated for every $k$; they are the $k$-WL algorithm for $k \geq 2$. For
$k \in \{0, 1\}$ they are not the usual algorithms (for $k = 1$, the atomic type of a single
vertex records no adjacency, so this is not color refinement); statements about $k$-WL assume
$k \geq 2$ where it matters, and the problems in `Lax119563.WLProblems` include these
degenerate dimensions only as inputs.
-/

open Lax119563.ColoredGraphs

namespace Lax119563.WeisfeilerLeman

/-- The atomic type of a `k`-tuple: which entries are equal, which entries are adjacent,
and the colors of the entries. -/
structure AtomicType (k : ℕ) where
  eq : Fin k → Fin k → Bool
  adj : Fin k → Fin k → Bool
  color : Fin k → ℕ

open Classical in
/-- The atomic type `atp_G(p̄)` of a tuple of vertices. -/
noncomputable def atp (G : ColoredGraph) {k : ℕ} (p : Fin k → Fin G.n) : AtomicType k :=
    { eq := fun i j => decide (p i = p j)
      adj := fun i j => decide (G.graph.Adj (p i) (p j))
      color := fun i => G.color (p i) }

/-- The colors used by `k`-WL in round `r`. -/
def Color (k : ℕ) : ℕ → Type
  | 0 => AtomicType k
  | r + 1 => Color k r × Multiset (Fin k → Color k r)

/-- The coloring `χ^{(r)}_k[G]` of `k`-tuples computed by `k`-WL in round `r`.
The tuple `Function.update p i q` is `p̄[q/i]`. -/
noncomputable def color (G : ColoredGraph) {k : ℕ} : (r : ℕ) → (Fin k → Fin G.n) → Color k r
  | 0, p => atp G p
  | r + 1, p =>
      (color G r p,
        (Finset.univ : Finset (Fin G.n)).val.map fun q i => color G r (Function.update p i q))

/-- `k`-WL distinguishes `G` and `H` after `r` rounds: some color of round `r` occurs a
different number of times among the `k`-tuples of `G` and of `H`. -/
def DistinguishesAfter (k r : ℕ) (G H : ColoredGraph) : Prop :=
  ∃ c : Color k r,
    Nat.card {p : Fin k → Fin G.n // color G r p = c} ≠
      Nat.card {q : Fin k → Fin H.n // color H r q = c}

/-- `k`-WL distinguishes `G` and `H`. -/
def Distinguishes (k : ℕ) (G H : ColoredGraph) : Prop :=
  ∃ r, DistinguishesAfter k r G H

/-- `k`-WL stabilizes after `r` rounds on `G`: the colorings of rounds `r` and `r + 1`
induce the same partition of the `k`-tuples of vertices. -/
def StabilizesAfter (k r : ℕ) (G : ColoredGraph) : Prop :=
  ∀ p q : Fin k → Fin G.n, color G r p = color G r q ↔ color G (r + 1) p = color G (r + 1) q

end Lax119563.WeisfeilerLeman
