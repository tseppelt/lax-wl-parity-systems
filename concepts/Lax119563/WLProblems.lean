import Lax434930.ExponentialTime
import Lax119563.BinaryEncodings
import Lax119563.ParameterizedComplexity
import Lax119563.WeisfeilerLeman

/-!
---
title: WL Distinguishing as a language and as a parameterized problem
type: definition
---
The problem WL Distinguishing asks, given an integer $k$ and two colored graphs
$G$ and $H$, whether $k$-WL distinguishes $G$ and $H$. Here $k$ is part of the input.

* As a **language** of bit strings, an instance $(k, G, H)$ is the binary code of the list of
  natural numbers
  $$k,\ \text{description of } G,\ \text{description of } H,$$
  i.e. the code of $k$ followed by the binary encoding of the pair $(G, H)$, with the
  number and graph encodings of the binary encodings of graph pairs.
* As a **parameterized problem**, it is this language with the parameter $k$: the number
  whose code begins the input string.

# Implementation notes
* The language is a `Lax434930.PolynomialTime.Language` (a set of `List Bool`), as used by the
  archive's class `EXPTIME` and its many-one reductions.
* The parameterization must be defined on all bit strings. It reads the leading number code:
  pairs of bits `1 d` give the binary digits `d`, least significant first, until the first
  pair that does not begin with `1`. On encoded instances, this is `k`.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.BinaryEncodings
open Lax119563.ParameterizedComplexity

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

/-- The number whose code `encodeNat` begins a bit string. -/
def leadingNat : List Bool → ℕ
  | true :: d :: rest => (if d then 1 else 0) + 2 * leadingNat rest
  | _ => 0

/-- **WL Distinguishing** as a parameterized problem, with parameter `k`. -/
def paramWLProblem : ParameterizedProblem where
  L := WLDistinguishing
  κ := leadingNat

end Lax119563.WLProblems
