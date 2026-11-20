import Lax119563Proofs.Matrix.Seeds
import Lax119563Proofs.Matrix.ListGraph

/-!
# The matrix construction

The explicit graph pair `matrixGraph I 0, matrixGraph I 1` of the matrix compiler.

## Parameters

* `M = k - 1 + ℓ` check rows; row `j < k - 1` is the block-parity check comparing block `j`
  with block `k - 1`, row `k - 1 + t` is the checksum check of bit `t`
  (`finSumFinEquiv` order of `Fin (k - 1) ⊕ Fin ℓ`).
* `R = k + 1` repetitions, hence `N = R * M` *steps*; step `σ < N` processes row `σ % M`.
  `ent σ c` is the entry of that row at the coordinate `c`.

## Vertex classes and names

A vertex name is a pair `(X, (s, t))` of a class `X : Cls` and a label `(s, t)`; classes with
one bit use labels `(s, 0)`.

* `coord v c` (`c ∈ 𝔠_v`): labels `(0,0), (1,0)`; only `(0,0)` if `v` is initialized.
* `sum e c`, `junc e c` (`e` ternary, `c ∈ 𝔠_e`): one and two bits; `junc e c` with label
  `(s, t)` is the junction vertex `(s, t, s + t)`.
* `link e c` (`c ∈ 𝔠_e`): one bit.
* `track e σ c`, `upd e σ c` (`σ < N`, `c ∈ 𝔠_e`, `ent σ c = 1`): one and two bits; the update
  with label `(s, t)` is the update vertex `(s, t, s + t)`, and `track e σ c` is the track
  leaving it.
* `coef e σ` (`σ < N`, row of `σ` nonzero on `𝔠_e`): one bit.

The track of column `c` at stage `σ` (`trackAt`) is `track e σ' c` for the last step
`σ' < σ` with `ent σ' c = 1`, and the start class (`coord u (σ_e c)` for binary `e`,
`sum e c` for ternary `e`) if there is none.

## Edges

Every edge joins a *hub* (update, junction, link) with a vertex of one of its neighbor
classes whose label is prescribed:
* `upd e σ c` `(s, t)`: `trackAt e c σ` with label `s`, `track e σ c` with label `t`,
  `coef e σ` with label `s + t`;
* `junc e c` `(s, t)`: `coord u (σ_e c)` with label `s`, `coord v (τ_e c)` with label `t`,
  `sum e c` with label `s + t`;
* `link e c` `(s)`: `trackAt e c N` and the end class `coord w (π_e c)` (resp.
  `coord v (τ_e c)` for binary `e`), both with label `s`.

Labels are compared as *effective labels*: in `G_ε`, the single vertex of an initialized
coordinate class `coord v c` has effective label `ε · ι(v)` if `c` lies in block `0` and `0`
otherwise.

## Numbering

The vertices of both graphs are the entries of `vertexList I`, in this order:
1. for each location `v` and each `c ∈ 𝔠_v` (in the order of `coordList`): its coordinate
   vertices;
2. for each schema `e` (in list order): for each `c ∈ 𝔠_e`: `sum`, `junc` (ternary only) and
   `link` vertices; then for each step `σ < N`: the `coef` vertices (if present), and for each
   `c ∈ 𝔠_e` with `ent σ c = 1` the `track` and the `upd` vertices.
Labels are listed as `(0,0), (1,0)` resp. `(0,0), (0,1), (1,0), (1,1)`. The color of a vertex
is the position in this list of the first vertex of its class.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs

namespace Lax119563Proofs.Matrix

variable {k ℓ w : ℕ}

/-! ### Schema accessors -/

/-- Whether a schema is ternary. -/
def isTern : Schema k ℓ w → Bool
  | .binary .. => false
  | .ternary .. => true

/-- The first argument location. -/
def locU : Schema k ℓ w → Fin w
  | .binary u .. => u
  | .ternary u .. => u

/-- The first argument permutation. -/
def permU : Schema k ℓ w → BlockPerm k ℓ
  | .binary _ _ _ σ _ => σ
  | .ternary _ _ _ _ σ _ _ => σ

/-- The second argument location. -/
def locV : Schema k ℓ w → Fin w
  | .binary _ v .. => v
  | .ternary _ v .. => v

/-- The second argument permutation. -/
def permV : Schema k ℓ w → BlockPerm k ℓ
  | .binary _ _ _ _ τ => τ
  | .ternary _ _ _ _ _ τ _ => τ

/-- The location at the end of the strip: the second argument of a binary schema, the third
argument of a ternary schema. -/
def locEnd : Schema k ℓ w → Fin w
  | .binary _ v .. => v
  | .ternary _ _ w' .. => w'

/-- The permutation at the end of the strip. -/
def permEnd : Schema k ℓ w → BlockPerm k ℓ
  | .binary _ _ _ _ τ => τ
  | .ternary _ _ _ _ _ _ π => π

/-! ### Steps and check rows -/

/-- The number `N = (k + 1)(k - 1 + ℓ)` of steps of a strip. -/
def numSteps (k ℓ : ℕ) : ℕ := (k + 1) * (k - 1 + ℓ)

/-- The check row processed by step `σ` (as an element of `Fin (k - 1) ⊕ Fin ℓ`). -/
def stepRow (h : 0 < k - 1 + ℓ) (σ : ℕ) : Fin (k - 1) ⊕ Fin ℓ :=
  finSumFinEquiv.symm ⟨σ % (k - 1 + ℓ), Nat.mod_lt _ h⟩

/-- The entry of the row of step `σ` at the coordinate `c`. -/
def ent (σ : ℕ) (c : Coord k ℓ) : ZMod 2 :=
  if h : 0 < k - 1 + ℓ then checkMatrix k ℓ (stepRow h σ) c else 0

/-- The last step before `σ` whose row is nonzero at `c`. -/
def prevStep (c : Coord k ℓ) : ℕ → Option ℕ
  | 0 => none
  | σ + 1 => if ent σ c ≠ 0 then some σ else prevStep c σ

/-! ### Classes and names -/

/-- Vertex classes. -/
inductive Cls (k ℓ w E : ℕ)
  | coord (v : Fin w) (c : Coord k ℓ)
  | sum (e : Fin E) (c : Coord k ℓ)
  | junc (e : Fin E) (c : Coord k ℓ)
  | link (e : Fin E) (c : Coord k ℓ)
  | track (e : Fin E) (σ : ℕ) (c : Coord k ℓ)
  | upd (e : Fin E) (σ : ℕ) (c : Coord k ℓ)
  | coef (e : Fin E) (σ : ℕ)
  deriving DecidableEq

variable (I : ImplicitParitySystem k ℓ)

/-- The classes of `I`. -/
abbrev ICls := Cls k ℓ I.numLocations I.schemas.length

/-- Labels. -/
abbrev Lab := ZMod 2 × ZMod 2

/-- Vertex names: a class and a label. -/
abbrev VName := ICls I × Lab

/-- The schema with index `e`. -/
def sch (e : Fin I.schemas.length) : Schema k ℓ I.numLocations := I.schemas.get e

/-- The coordinate domain of schema `e`. -/
def dom (e : Fin I.schemas.length) : Finset (Coord k ℓ) := (sch I e).domain

/-- The class at which the strip of column `c` starts. -/
def startCls (e : Fin I.schemas.length) (c : Coord k ℓ) : ICls I :=
  if isTern (sch I e) then .sum e c else .coord (locU (sch I e)) ((permU (sch I e)).apply c)

/-- The class at which the strip of column `c` ends. -/
def endCls (e : Fin I.schemas.length) (c : Coord k ℓ) : ICls I :=
  .coord (locEnd (sch I e)) ((permEnd (sch I e)).apply c)

/-- The track class of column `c` at stage `σ`. -/
def trackAt (e : Fin I.schemas.length) (c : Coord k ℓ) (σ : ℕ) : ICls I :=
  match prevStep c σ with
  | none => startCls I e c
  | some σ' => .track e σ' c

/-- The initial seed: `ι(v)` on block `0` and `0` elsewhere (and `0` if `v` is
uninitialized). -/
def initSeed (v : Fin I.numLocations) (c : Coord k ℓ) : ZMod 2 :=
  match I.init v with
  | some b => if (c.1 : ℕ) = 0 then b else 0
  | none => 0

/-- The label offset of a class in `G₁`. -/
def initBit : ICls I → ZMod 2
  | .coord v c => initSeed I v c
  | _ => 0

/-- The effective label of a name in `G_ε`. -/
def eff (ε : ZMod 2) (x : VName I) : Lab := (x.2.1 + ε * initBit I x.1, x.2.2)

/-- The neighbor relation of hubs: `hubB X l Y m` says that a hub of class `X` with effective
label `l` is adjacent to a vertex of class `Y` with effective label `m`. -/
def hubB (X : ICls I) (l : Lab) (Y : ICls I) (m : Lab) : Bool :=
  match X with
  | .upd e σ c =>
      (decide (Y = trackAt I e c σ) && decide (m.1 = l.1)) ||
      (decide (Y = .track e σ c) && decide (m.1 = l.2)) ||
      (decide (Y = .coef e σ) && decide (m.1 = l.1 + l.2))
  | .junc e c =>
      (decide (Y = .coord (locU (sch I e)) ((permU (sch I e)).apply c)) && decide (m.1 = l.1)) ||
      (decide (Y = .coord (locV (sch I e)) ((permV (sch I e)).apply c)) && decide (m.1 = l.2)) ||
      (decide (Y = .sum e c) && decide (m.1 = l.1 + l.2))
  | .link e c =>
      (decide (Y = trackAt I e c (numSteps k ℓ)) && decide (m.1 = l.1)) ||
      (decide (Y = endCls I e c) && decide (m.1 = l.1))
  | _ => false

/-- Adjacency in `G_ε`. -/
def adjN (ε : ZMod 2) (x y : VName I) : Prop :=
  hubB I x.1 (eff I ε x) y.1 (eff I ε y) = true ∨ hubB I y.1 (eff I ε y) x.1 (eff I ε x) = true

instance (ε : ZMod 2) : DecidableRel (adjN I ε) := fun _ _ => by
  unfold adjN; infer_instance

/-- Hubs. -/
def isHub : ICls I → Bool
  | .upd .. => true
  | .junc .. => true
  | .link .. => true
  | _ => false

lemma isHub_startCls (e : Fin I.schemas.length) (c : Coord k ℓ) :
    isHub I (startCls I e c) = false := by
  unfold startCls; split <;> rfl

lemma isHub_trackAt (e : Fin I.schemas.length) (c : Coord k ℓ) (σ : ℕ) :
    isHub I (trackAt I e c σ) = false := by
  unfold trackAt; split
  · exact isHub_startCls I e c
  · rfl

/-- Only hubs have neighbors through `hubB`, and these are not hubs. -/
lemma hubB_hub {X Y : ICls I} {l m : Lab} (h : hubB I X l Y m = true) :
    isHub I X = true ∧ isHub I Y = false := by
  cases X with
  | upd e σ c =>
    refine ⟨rfl, ?_⟩
    simp only [hubB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ((⟨rfl, -⟩ | ⟨rfl, -⟩) | ⟨rfl, -⟩)
    · exact isHub_trackAt I e c σ
    · rfl
    · rfl
  | junc e c =>
    refine ⟨rfl, ?_⟩
    simp only [hubB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ((⟨rfl, -⟩ | ⟨rfl, -⟩) | ⟨rfl, -⟩) <;> rfl
  | link e c =>
    refine ⟨rfl, ?_⟩
    simp only [hubB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with (⟨rfl, -⟩ | ⟨rfl, -⟩)
    · exact isHub_trackAt I e c _
    · rfl
  | coord => simp [hubB] at h
  | sum => simp [hubB] at h
  | track => simp [hubB] at h
  | coef => simp [hubB] at h

lemma adjN_symm (ε : ZMod 2) (x y : VName I) (h : adjN I ε x y) : adjN I ε y x :=
  h.symm

lemma adjN_irrefl (ε : ZMod 2) (x : VName I) : ¬ adjN I ε x x := by
  rintro (h | h) <;>
  · have := hubB_hub I h
    rw [this.1] at this
    exact absurd this.2 (by decide)

/-! ### Valid names -/

/-- The classes present in the graphs. -/
def ClsValid : ICls I → Prop
  | .coord v c => c ∈ I.domain v
  | .sum e c => isTern (sch I e) = true ∧ c ∈ dom I e
  | .junc e c => isTern (sch I e) = true ∧ c ∈ dom I e
  | .link e c => c ∈ dom I e
  | .track e σ c => σ < numSteps k ℓ ∧ c ∈ dom I e ∧ ent σ c ≠ 0
  | .upd e σ c => σ < numSteps k ℓ ∧ c ∈ dom I e ∧ ent σ c ≠ 0
  | .coef e σ => σ < numSteps k ℓ ∧ ∃ c ∈ dom I e, ent σ c ≠ 0

/-- Classes with two label bits. -/
def twoBit : ICls I → Bool
  | .junc .. => true
  | .upd .. => true
  | _ => false

/-- Singleton classes: coordinate classes at initialized locations. -/
def isSingleton : ICls I → Bool
  | .coord v _ => (I.init v).isSome
  | _ => false

/-- The labels present in a class. -/
def LabelOK (X : ICls I) (l : Lab) : Prop :=
  (twoBit I X = false → l.2 = 0) ∧ (isSingleton I X = true → l.1 = 0)

/-- Valid vertex names. -/
def Valid (x : VName I) : Prop := ClsValid I x.1 ∧ LabelOK I x.1 x.2

/-! ### Enumerations -/

/-- All block coordinates. -/
def allBlockCoords : (ℓ : ℕ) → List (BlockCoord ℓ)
  | 0 => [fun i => i.elim0]
  | ℓ + 1 => (allBlockCoords ℓ).flatMap fun b => [Fin.cons 0 b, Fin.cons 1 b]

/-- All coordinates, block by block. -/
def allCoords (k ℓ : ℕ) : List (Coord k ℓ) :=
  (List.finRange k).flatMap fun i => (allBlockCoords ℓ).map fun b => (i, b)

/-- The coordinates of a domain, in the order of `allCoords`. -/
def coordList (D : Finset (Coord k ℓ)) : List (Coord k ℓ) := (allCoords k ℓ).filter (· ∈ D)

/-- One-bit labels. -/
def bits1 : List Lab := [(0, 0), (1, 0)]

/-- Two-bit labels. -/
def bits2 : List Lab := [(0, 0), (0, 1), (1, 0), (1, 1)]

/-- The vertices of the coordinate classes of location `v`. -/
def coordVerts (v : Fin I.numLocations) : List (VName I) :=
  (coordList (I.domain v)).flatMap fun c =>
    (if (I.init v).isSome then [((0 : ZMod 2), (0 : ZMod 2))] else bits1).map fun l =>
      (Cls.coord v c, l)

/-- The `sum`, `junc` and `link` vertices of column `c` of schema `e`. -/
def columnVerts (e : Fin I.schemas.length) (c : Coord k ℓ) : List (VName I) :=
  (if isTern (sch I e) then bits1.map (fun l => (Cls.sum e c, l)) ++
      bits2.map (fun l => (Cls.junc e c, l)) else []) ++
    bits1.map fun l => (Cls.link e c, l)

/-- The vertices of step `σ` of schema `e`. -/
def stepVerts (e : Fin I.schemas.length) (σ : ℕ) : List (VName I) :=
  (if ∃ c ∈ dom I e, ent σ c ≠ 0 then bits1.map fun l => (Cls.coef e σ, l) else []) ++
    ((coordList (dom I e)).filter fun c => ent σ c ≠ 0).flatMap fun c =>
      bits1.map (fun l => (Cls.track e σ c, l)) ++ bits2.map fun l => (Cls.upd e σ c, l)

/-- The vertices of the gadget of schema `e`. -/
def schemaVerts (e : Fin I.schemas.length) : List (VName I) :=
  (coordList (dom I e)).flatMap (columnVerts I e) ++
    (List.range (numSteps k ℓ)).flatMap (stepVerts I e)

/-- The vertex list shared by both graphs. -/
def vertexList : List (VName I) :=
  (List.finRange I.numLocations).flatMap (coordVerts I) ++
    (List.finRange I.schemas.length).flatMap (schemaVerts I)

/-- **The matrix compiler graph** `G_ε`. -/
abbrev matrixGraph (ε : ZMod 2) : ColoredGraph :=
  listGraph (vertexList I) (adjN I ε) (adjN_symm I ε) (adjN_irrefl I ε) Prod.fst

end Lax119563Proofs.Matrix
