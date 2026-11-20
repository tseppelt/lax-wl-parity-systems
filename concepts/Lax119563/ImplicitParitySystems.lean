import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fintype
import Lax119563.ParitySystems

/-!
---
title: Implicit parity systems
type: definition
---
Fix $k \geq 3$ and $\ell \geq 1$. The *coordinates* $\mathfrak C = [k] \times \mathbb F_2^\ell$
consist of $k$ *blocks*, each a copy of $\mathbb F_2^\ell$, whose elements are the *block
coordinates*. An *address* is a codeword with exactly one $1$ per block whose block
coordinates sum to zero; we represent it by the array $a = (a_1, \dots, a_k)$ of the block
coordinates of its ones, subject to $a_1 + \dots + a_k = 0$. Its *support* is
$\operatorname{supp}(a) = \{(i, a_i) : i \in [k]\}$.

A permutation $\pi$ of $\mathfrak C$ is *block-induced* if there are a permutation
$f$ of $[k]$ and $\delta_1, \dots, \delta_k \in \mathbb F_2^\ell$ with
$\sum_i \delta_i = 0$ such that $\pi(i, b) = (f(i), b + \delta_i)$. It maps an address $a$ to
the address $\pi a$ with $\operatorname{supp}(\pi a) = \pi(\operatorname{supp}(a))$, i.e.,
$(\pi a)_{f(i)} = a_i + \delta_i$.

Let $W$ be a finite set of *locations*, each with a *coordinate domain*
$\mathfrak C_v \subseteq \mathfrak C$. A *ternary equation schema*
$e = (u, v, w, \mathfrak C_e, \sigma, \tau, \pi)$ consists of three distinct locations, a
coordinate domain $\mathfrak C_e \subseteq \mathfrak C$, and block-induced permutations with
$\sigma(\mathfrak C_e) \subseteq \mathfrak C_u$, $\tau(\mathfrak C_e) \subseteq \mathfrak C_v$
and $\pi(\mathfrak C_e) \subseteq \mathfrak C_w$. For every *allowed* address $a$, i.e., with
$\operatorname{supp}(a) \subseteq \mathfrak C_e$, it gives the equation
$X_{u, \sigma a} + X_{v, \tau a} + X_{w, \pi a} = 0$. A *binary equation schema*
$(u, v, \mathfrak C_e, \sigma, \tau)$ analogously gives $X_{u, \sigma a} + X_{v, \tau a} = 0$.

An *implicit parity system* $\mathcal I = (W, \mathfrak C, (\mathfrak C_v)_{v \in W},
\mathcal E, \iota)$ consists of locations $W$ with coordinate domains, a finite set
$\mathcal E$ of binary or ternary equation schemas whose sets of locations pairwise intersect
in at most one element, and an *initialization* $\iota \colon W \to \{0, 1, \star\}$. It
defines a parity system: its variables are the $X_{v, a}$ for $v \in W$ and addresses $a$ with
$\operatorname{supp}(a) \subseteq \mathfrak C_v$; its equations are those given by the
schemas; and for every $v$ with $\iota(v) \in \{0, 1\}$ it has the initial facts
$X_{v, a} = \iota(v)$ for all these addresses $a$. We write $\tau(\mathcal I)$ for the conflict
round of this parity system.

# Implementation notes

The locations are $W = \{0, \dots, w-1\}$, the initialization value $\star$ is `none`, and
the schemas are given as a list. The parity system has a variable $X_{v, a}$ for every
location $v$ and every array $a$; those with $a$ not an address or with
$\operatorname{supp}(a) \not\subseteq \mathfrak C_v$ occur in no equation and in no initial
fact, so they do not affect unit propagation.
-/

open Lax119563.ParitySystems

namespace Lax119563.ImplicitParitySystems

/-- Block coordinates `𝔽₂^ℓ`. -/
abbrev BlockCoord (ℓ : ℕ) := Fin ℓ → ZMod 2

/-- Coordinates `ℭ = [k] × 𝔽₂^ℓ`. -/
abbrev Coord (k ℓ : ℕ) := Fin k × BlockCoord ℓ

variable {k ℓ w : ℕ}

/-- An array `(a_1, …, a_k)` of block coordinates is an *address* if its entries sum to zero. -/
def IsAddress (a : Fin k → BlockCoord ℓ) : Prop :=
  ∑ i, a i = 0

/-- The support `{(i, a_i) : i ∈ [k]}` of the address with array `a`. -/
def supp (a : Fin k → BlockCoord ℓ) : Finset (Coord k ℓ) :=
  Finset.univ.image fun i => (i, a i)

/-- A *block-induced* permutation `(i, b) ↦ (f(i), b + δ_i)` of `ℭ`, where `∑ δ_i = 0`. -/
structure BlockPerm (k ℓ : ℕ) where
  /-- The permutation `f` of the blocks. -/
  perm : Equiv.Perm (Fin k)
  /-- The shifts `δ_i`. -/
  shift : Fin k → BlockCoord ℓ
  sum_shift : ∑ i, shift i = 0

/-- The block-induced permutation acting on a coordinate. -/
def BlockPerm.apply (π : BlockPerm k ℓ) (c : Coord k ℓ) : Coord k ℓ :=
  (π.perm c.1, c.2 + π.shift c.1)

/-- The block-induced permutation acting on an address: `(π a)_{f(i)} = a_i + δ_i`. -/
def BlockPerm.act (π : BlockPerm k ℓ) (a : Fin k → BlockCoord ℓ) : Fin k → BlockCoord ℓ :=
  fun j => a (π.perm.symm j) + π.shift (π.perm.symm j)

/-- A binary or ternary *equation schema* over the locations `{0, …, w-1}`. -/
inductive Schema (k ℓ w : ℕ)
  /-- The binary schema `(u, v, ℭ_e, σ, τ)`. -/
  | binary (u v : Fin w) (domain : Finset (Coord k ℓ)) (σ τ : BlockPerm k ℓ)
  /-- The ternary schema `(u, v, w, ℭ_e, σ, τ, π)`. -/
  | ternary (u v w' : Fin w) (domain : Finset (Coord k ℓ)) (σ τ π : BlockPerm k ℓ)

namespace Schema

/-- The coordinate domain `ℭ_e` of a schema. -/
def domain : Schema k ℓ w → Finset (Coord k ℓ)
  | binary _ _ D _ _ => D
  | ternary _ _ _ D _ _ _ => D

/-- The set of locations of a schema. -/
def locations : Schema k ℓ w → Finset (Fin w)
  | binary u v _ _ _ => {u, v}
  | ternary u v w' _ _ _ _ => {u, v, w'}

/-- The locations of a schema are distinct, and its permutations map its coordinate domain
into the coordinate domains of the respective locations. -/
def WellFormed (dom : Fin w → Finset (Coord k ℓ)) : Schema k ℓ w → Prop
  | binary u v D σ τ => u ≠ v ∧ D.image σ.apply ⊆ dom u ∧ D.image τ.apply ⊆ dom v
  | ternary u v w' D σ τ π => u ≠ v ∧ u ≠ w' ∧ v ≠ w' ∧
      D.image σ.apply ⊆ dom u ∧ D.image τ.apply ⊆ dom v ∧ D.image π.apply ⊆ dom w'

/-- The equation given by a schema for the address `a`, as its set of variables `X_{v, a'}`,
written as pairs `(v, a')`. -/
def equation : Schema k ℓ w → (Fin k → BlockCoord ℓ) → Finset (Fin w × (Fin k → BlockCoord ℓ))
  | binary u v _ σ τ, a => {(u, σ.act a), (v, τ.act a)}
  | ternary u v w' _ σ τ π, a => {(u, σ.act a), (v, τ.act a), (w', π.act a)}

end Schema

/-- An *implicit parity system* with coordinates `[k] × 𝔽₂^ℓ`. -/
structure ImplicitParitySystem (k ℓ : ℕ) where
  /-- The number of locations; the locations are `0, …, numLocations - 1`. -/
  numLocations : ℕ
  /-- The coordinate domain `ℭ_v` of each location. -/
  domain : Fin numLocations → Finset (Coord k ℓ)
  /-- The equation schemas. -/
  schemas : List (Schema k ℓ numLocations)
  /-- The initialization `ι`; `none` stands for `⋆`. -/
  init : Fin numLocations → Option (ZMod 2)
  schema_wellFormed : ∀ e ∈ schemas, e.WellFormed domain
  /-- The sets of locations of distinct schemas intersect in at most one location. -/
  schemas_meet : schemas.Pairwise fun e e' => (e.locations ∩ e'.locations).card ≤ 1

namespace ImplicitParitySystem

/-- The parity system defined by an implicit parity system. -/
def toParitySystem (I : ImplicitParitySystem k ℓ) :
    ParitySystem (Fin I.numLocations × (Fin k → BlockCoord ℓ)) where
  equations := {h | ∃ e ∈ I.schemas, ∃ a, IsAddress a ∧ supp a ⊆ e.domain ∧ h = e.equation a}
  card_equation := by
    rintro h ⟨e, he, a, -, -, rfl⟩
    have hwf := I.schema_wellFormed e he
    cases e with
    | binary u v D σ τ =>
      left
      exact Finset.card_pair fun h => hwf.1 (congrArg Prod.fst h)
    | ternary u v w' D σ τ π =>
      right
      obtain ⟨huv, huw, hvw, -⟩ := hwf
      have h₁ : (u, σ.act a) ∉ ({(v, τ.act a), (w', π.act a)} : Finset _) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => huv (congrArg Prod.fst h), fun h => huw (congrArg Prod.fst h)⟩
      rw [Schema.equation, Finset.card_insert_of_notMem h₁,
        Finset.card_pair fun h => hvw (congrArg Prod.fst h)]
  initial := {f | ∃ b, I.init f.1.1 = some b ∧ f.2 = b ∧
    IsAddress f.1.2 ∧ supp f.1.2 ⊆ I.domain f.1.1}

/-- The conflict round `τ(I)` of an implicit parity system. -/
noncomputable def conflictRound (I : ImplicitParitySystem k ℓ) : ℕ∞ :=
  I.toParitySystem.conflictRound

end ImplicitParitySystem

end Lax119563.ImplicitParitySystems
