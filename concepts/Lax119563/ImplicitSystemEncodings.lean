import Mathlib.Data.Finset.Sort
import Lax119563.BinaryEncodings
import Lax119563.ImplicitParitySystems

/-!
---
title: Binary encodings of implicit parity systems
type: definition
---
An implicit parity system $\mathcal I = (W, \mathfrak C, (\mathfrak C_v)_{v \in W},
\mathcal E, \iota)$ with coordinates $\mathfrak C = [k] \times \mathbb F_2^\ell$ is given to a
Turing machine explicitly, as a list of natural numbers encoded as in the binary encodings of
graph pairs.

* A block coordinate $b \in \mathbb F_2^\ell$ is the number $\sum_{t < \ell} b_t 2^t$, and a
  coordinate $(i, b)$ is the number $i \cdot 2^\ell + b$.
* A coordinate domain $D \subseteq \mathfrak C$ is described by $|D|$ followed by the numbers
  of its coordinates in increasing order.
* A block-induced permutation $\pi(i, b) = (f(i), b + \delta_i)$ is described by
  $f(0), \dots, f(k - 1)$ followed by $\delta_0, \dots, \delta_{k - 1}$.
* A binary schema $(u, v, \mathfrak C_e, \sigma, \tau)$ is described by $2, u, v$, the
  domain $\mathfrak C_e$, and the permutations $\sigma, \tau$; a ternary schema
  $(u, v, w, \mathfrak C_e, \sigma, \tau, \pi)$ by $3, u, v, w$, the domain, and
  $\sigma, \tau, \pi$.
* The initialization value $\star$ is written $0$, and the values $0, 1$ are written $1, 2$.

The system is described by $k, \ell, |W|$, then for each location $v = 0, \dots, |W| - 1$
its initialization value followed by its domain $\mathfrak C_v$, then $|\mathcal E|$, and
finally the descriptions of the schemas in order. Its *bit length* $H$ is the length of the
binary code of this list; it accounts for the explicit domains, argument maps and
initializations, including their indices.
-/

open Lax119563.ImplicitParitySystems Lax119563.BinaryEncodings

namespace Lax119563.ImplicitSystemEncodings

variable {k ℓ w : ℕ}

/-- The number `∑_t b_t 2^t` of a block coordinate. -/
def blockNum (b : BlockCoord ℓ) : ℕ :=
  ∑ t : Fin ℓ, (b t).val * 2 ^ (t : ℕ)

/-- The number `i · 2^ℓ + b` of a coordinate `(i, b)`. -/
def coordNum (c : Coord k ℓ) : ℕ :=
  (c.1 : ℕ) * 2 ^ ℓ + blockNum c.2

/-- The description `|D|, c₁, …, c_{|D|}` of a coordinate domain, with the coordinate numbers
in increasing order. -/
def domainDescription (D : Finset (Coord k ℓ)) : List ℕ :=
  let l := (D.image coordNum).sort (· ≤ ·)
  l.length :: l

/-- The description `f(0), …, f(k-1), δ₀, …, δ_{k-1}` of a block-induced permutation. -/
def permDescription (π : BlockPerm k ℓ) : List ℕ :=
  (List.finRange k).map (fun i => (π.perm i : ℕ)) ++
    (List.finRange k).map (fun i => blockNum (π.shift i))

/-- The description of an equation schema. -/
def schemaDescription : Schema k ℓ w → List ℕ
  | .binary u v D σ τ =>
      [2, (u : ℕ), (v : ℕ)] ++ domainDescription D ++ permDescription σ ++ permDescription τ
  | .ternary u v w' D σ τ π =>
      [3, (u : ℕ), (v : ℕ), (w' : ℕ)] ++ domainDescription D ++ permDescription σ ++
        permDescription τ ++ permDescription π

/-- The number of an initialization value: `⋆ ↦ 0`, `0 ↦ 1`, `1 ↦ 2`. -/
def initNum : Option (ZMod 2) → ℕ
  | none => 0
  | some b => b.val + 1

/-- The description of an implicit parity system as a list of natural numbers. -/
def systemDescription (I : ImplicitParitySystem k ℓ) : List ℕ :=
  [k, ℓ, I.numLocations] ++
    (List.finRange I.numLocations).flatMap
      (fun v => initNum (I.init v) :: domainDescription (I.domain v)) ++
    I.schemas.length :: I.schemas.flatMap schemaDescription

/-- The binary encoding of an implicit parity system. -/
def encodeSystem (I : ImplicitParitySystem k ℓ) : List Bool :=
  encodeNats (systemDescription I)

/-- The bit length `H` of an implicit parity system. -/
def bitLength (I : ImplicitParitySystem k ℓ) : ℕ :=
  (encodeSystem I).length

end Lax119563.ImplicitSystemEncodings
