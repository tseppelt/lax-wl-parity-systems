import Mathlib.Data.Nat.Bits
import Mathlib.Data.List.FinRange
import Lax119563.ColoredGraphs

/-!
---
title: Binary encodings of graph pairs
type: definition
---
Inputs of Turing machines are bit strings. We encode a natural number $m$ by its binary
digits $d_0, d_1, \dots$, least significant first, writing each digit $d$ as the two bits
$1 d$ and terminating with a single $0$; this code is self-delimiting and has length
$2 \lceil \log_2 (m + 1) \rceil + 1$. A list of natural numbers is encoded by concatenating
the codes of its entries.

A colored graph $G$ with $n$ vertices and $m$ edges is described by the list
$$n,\ \chi_G(0), \dots, \chi_G(n - 1),\ m,\ u_1, v_1, \dots, u_m, v_m,$$
where $u_1 v_1, \dots, u_m v_m$ are its edges with $u_j < v_j$, in lexicographic order. A pair
$(G, H)$ is encoded by the code of the description of $G$ followed by that of $H$. For graphs
with $N$ vertices, $E$ edges, and colors below $N$, the encoding has length
$O((N + E) \log (N + 2))$.
-/

open Lax119563.ColoredGraphs

namespace Lax119563.BinaryEncodings

/-- The self-delimiting binary code of a natural number: its binary digits `d`, least
significant first, each written as `true, d`, followed by `false`. -/
def encodeNat (m : ℕ) : List Bool :=
  (Nat.bits m).flatMap (fun d => [true, d]) ++ [false]

/-- The code of a list of natural numbers: the concatenation of the codes of its entries. -/
def encodeNats (l : List ℕ) : List Bool :=
  l.flatMap encodeNat

/-- The edges `(u, v)` with `u < v` of a colored graph, in lexicographic order. -/
noncomputable def edgeList (G : ColoredGraph) : List (ℕ × ℕ) := by
  classical
  exact (List.finRange G.n).flatMap fun u =>
    ((List.finRange G.n).filter fun v => u < v ∧ G.graph.Adj u v).map fun v => ((u : ℕ), (v : ℕ))

/-- The description `n, χ(0), …, χ(n-1), m, u₁, v₁, …, u_m, v_m` of a colored graph. -/
noncomputable def graphDescription (G : ColoredGraph) : List ℕ :=
  G.n :: (List.finRange G.n).map G.color ++
    (edgeList G).length :: (edgeList G).flatMap fun e => [e.1, e.2]

/-- The binary encoding of a pair of colored graphs. -/
noncomputable def encodeGraphPair (G H : ColoredGraph) : List Bool :=
  encodeNats (graphDescription G ++ graphDescription H)

end Lax119563.BinaryEncodings
