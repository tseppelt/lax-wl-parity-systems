import Lax434930.ExponentialTime
import Lax888481.ParameterizedComplexity
import Lax119563.BinaryEncodings
import Lax119563.WeisfeilerLeman

/-!
---
title: WL Distinguishing as a language and as a parameterized problem
type: definition
---
The problem $\textsc{WL Distinguishing}$ asks, given an integer $k$ and two colored graphs
$G$ and $H$, whether $k$-WL distinguishes $G$ and $H$. Here $k$ is part of the input.

* As a **language** of bit strings, an instance $(k, G, H)$ is the binary code of the list of
  natural numbers
  $$k,\ \text{description of } G,\ \text{description of } H,$$
  i.e. the code of $k$ followed by the binary encoding of the pair $(G, H)$, with the
  number and graph encodings of the binary encodings of graph pairs.
* As a **parameterized problem** in the sense of parameterized complexity, the instance is
  that list of natural numbers itself, and the parameter is its first entry $k$.

# Implementation notes
The language is a `Lax434930.PolynomialTime.Language` (a set of `List Bool`), as used by the
archive's classes `EXPTIME` and many-one reductions. The parameterized problem is a
`Lax888481.ParameterizedComplexity.Problem` on words `List ℕ`, as used by the archive's
fpt-reductions (`Lax496464`), which run on word RAMs; its admissible words are exactly the
lists `k :: (description of G ++ description of H)`. Both encodings carry the same list: the
language is the image of the admissible words under the bit code `encodeNats`.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.BinaryEncodings

namespace Lax119563.WLProblems

/-- The instance `k, description of G, description of H` as a list of natural numbers. -/
noncomputable def wlWord (k : ℕ) (G H : ColoredGraph) : List ℕ :=
  k :: (graphDescription G ++ graphDescription H)

/-- The binary encoding of the instance `(k, G, H)`: the code of `k` followed by the binary
encoding of the pair `(G, H)`. -/
noncomputable def encodeWLInstance (k : ℕ) (G H : ColoredGraph) : List Bool :=
  encodeNats (wlWord k G H)

/-- **WL Distinguishing** as a language: the encodings of instances `(k, G, H)` such that
`k`-WL distinguishes `G` and `H`. -/
def WLDistinguishing : Lax434930.PolynomialTime.Language :=
  {w | ∃ (k : ℕ) (G H : ColoredGraph), w = encodeWLInstance k G H ∧ Distinguishes k G H}

/-- **WL Distinguishing** as a parameterized problem, with parameter `k`. -/
def wlProblem : Lax888481.ParameterizedComplexity.Problem where
  Domain := {x | ∃ (k : ℕ) (G H : ColoredGraph), x = wlWord k G H}
  Yes x := ∃ (k : ℕ) (G H : ColoredGraph), x = wlWord k G H ∧ Distinguishes k G H
  param x := x.headD 0

end Lax119563.WLProblems
