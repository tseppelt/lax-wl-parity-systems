import Lax119563.RowSpaceCompiler
import Lax119563Proofs.Matrix.Exposure

/-!
# The row-space construction

The graphs `rsGraph I 0, rsGraph I 1` of the row-space compiler.

## Classes

We reuse the class type `ICls I` of the matrix compiler:
* `coord v c` (`c ∈ 𝔠_v`): coordinate classes;
* `sum e c`, `junc e c` (`e` ternary, `c ∈ 𝔠_e`): sum pairs and junctions;
* `track e h c` (`1 ≤ h ≤ k + 1`, `c ∈ 𝔠_e`): internal track classes;
* `upd e h c` (`1 ≤ h ≤ k + 2`, `c ∈ 𝔠_e`): update classes of stage `h`;
* `coef e h` (`1 ≤ h ≤ k + 2`): the mask class of stage `h`.
The class `link` is unused. The track class at index `h` (`trackCls`) is the start class
(`coord u (σ c)` resp. `sum e c`) for `h = 0`, the end class `coord w (π c)` for `h = k + 2`,
and `track e h c` otherwise.

## Vertices

A vertex is a pair of a class and a label in `RLab k ℓ = 𝔽₂ × 𝔽₂ × 𝔽₂^𝔠`: one-bit classes
use labels `(s, 0, 0)`, two-bit classes (`junc`, `upd`) labels `(s, t, 0)` (standing for the
junction vertex `(s, t, s + t)` resp. the update vertex `(s, t)`), mask classes labels
`(0, 0, x)` for `x` in the row space of `B_e` (extended by zero outside `𝔠_e`). The vertices of
`G_ε` carry their *effective* labels: the names `names I` (the vertices of `G₀`) translated by
`ε • off X`, where `off` is the initial seed on singleton coordinate classes.

## Edges

Every edge joins a hub (update or junction) with a vertex of a neighboring class, subject to
one linear condition on the labels (`hubR`).

## Colors

The color of a vertex is an injective code of its class.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs
open Lax119563Proofs.Matrix

namespace Lax119563Proofs.RowSpace

variable {k ℓ : ℕ}

/-- Labels. -/
abbrev RLab (k ℓ : ℕ) := ZMod 2 × ZMod 2 × Vec k ℓ

instance (k ℓ : ℕ) : DecidableEq (Vec k ℓ) := Fintype.decidablePiFintype

lemma zmod2_self_add (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;> decide

lemma rlab_add_self (l : RLab k ℓ) : l + l = 0 := by
  obtain ⟨a, b, x⟩ := l
  refine Prod.ext (zmod2_self_add a) (Prod.ext (zmod2_self_add b) ?_)
  funext c
  exact zmod2_self_add (x c)

lemma rlab_add_add_cancel (l d : RLab k ℓ) : l + d + d = l := by
  rw [add_assoc, rlab_add_self, add_zero]

variable (I : ImplicitParitySystem k ℓ)

/-! ### Masks -/

/-- The mask `μᵀ B_e`, extended by zero outside `𝔠_e`. -/
def maskOf (e : Fin I.schemas.length) (μ : Row k ℓ → ZMod 2) : Vec k ℓ :=
  fun c => if c ∈ dom I e then ∑ j, μ j * checkMatrix k ℓ j c else 0

/-- The row space of `B_e`, as vectors extended by zero. -/
def maskSet (e : Fin I.schemas.length) : Finset (Vec k ℓ) :=
  Finset.univ.image (maskOf I e)

lemma maskOf_add (e : Fin I.schemas.length) (μ μ' : Row k ℓ → ZMod 2) :
    maskOf I e (μ + μ') = maskOf I e μ + maskOf I e μ' := by
  funext c
  simp only [maskOf, Pi.add_apply]
  split
  · simp [add_mul, Finset.sum_add_distrib]
  · simp

lemma maskOf_zero (e : Fin I.schemas.length) : maskOf I e 0 = 0 := by
  funext c; simp [maskOf]

lemma zero_mem_maskSet (e : Fin I.schemas.length) : (0 : Vec k ℓ) ∈ maskSet I e :=
  Finset.mem_image.mpr ⟨0, Finset.mem_univ _, maskOf_zero I e⟩

lemma add_mem_maskSet {e : Fin I.schemas.length} {x y : Vec k ℓ} (hx : x ∈ maskSet I e)
    (hy : y ∈ maskSet I e) : x + y ∈ maskSet I e := by
  obtain ⟨μ, -, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨μ', -, rfl⟩ := Finset.mem_image.mp hy
  exact Finset.mem_image.mpr ⟨μ + μ', Finset.mem_univ _, maskOf_add I e μ μ'⟩

lemma maskSet_supp {e : Fin I.schemas.length} {x : Vec k ℓ} (hx : x ∈ maskSet I e) {c : Coord k ℓ}
    (hc : c ∉ dom I e) : x c = 0 := by
  obtain ⟨μ, -, rfl⟩ := Finset.mem_image.mp hx
  simp [maskOf, hc]

/-! ### Track classes -/

/-- The track class of column `c` at index `h ∈ [0, k + 2]`. -/
def trackCls (e : Fin I.schemas.length) (c : Coord k ℓ) (h : ℕ) : ICls I :=
  if h = 0 then startCls I e c else if h = k + 2 then endCls I e c else .track e h c

lemma trackCls_zero (e : Fin I.schemas.length) (c : Coord k ℓ) :
    trackCls I e c 0 = startCls I e c := by simp [trackCls]

lemma trackCls_last (e : Fin I.schemas.length) (c : Coord k ℓ) :
    trackCls I e c (k + 2) = endCls I e c := by simp [trackCls]

/-! ### Classes and labels -/

/-- The coordinate classes. -/
def coordClasses : Finset (ICls I) :=
  Finset.univ.biUnion fun v => (I.domain v).image (Cls.coord v)

/-- The classes of the gadget of schema `e`. -/
def schemaClasses (e : Fin I.schemas.length) : Finset (ICls I) :=
  ((if isTern (sch I e) then (dom I e).image (Cls.sum e) ∪ (dom I e).image (Cls.junc e) else ∅) ∪
    (Finset.Icc 1 (k + 1) ×ˢ dom I e).image (fun p => Cls.track e p.1 p.2)) ∪
    ((Finset.Icc 1 (k + 2) ×ˢ dom I e).image (fun p => Cls.upd e p.1 p.2) ∪
    (Finset.Icc 1 (k + 2)).image (Cls.coef e))

/-- All classes. -/
def classes : Finset (ICls I) :=
  coordClasses I ∪ Finset.univ.biUnion (schemaClasses I)

/-- One-bit labels. -/
def lab1 : Finset (RLab k ℓ) := {0, (1, 0, 0)}

/-- Two-bit labels. -/
def lab2 : Finset (RLab k ℓ) := {0, (1, 0, 0), (0, 1, 0), (1, 1, 0)}

/-- The labels of the vertices of a class in `G₀`. -/
def labs : ICls I → Finset (RLab k ℓ)
  | .coord v _ => if (I.init v).isSome then {0} else lab1
  | .sum .. => lab1
  | .track .. => lab1
  | .junc .. => lab2
  | .upd .. => lab2
  | .coef e _ => (maskSet I e).image fun x => (0, 0, x)
  | .link .. => ∅

/-- The vertex names of `G₀`. -/
def names : Finset (ICls I × RLab k ℓ) :=
  (classes I).biUnion fun X => (labs I X).image (Prod.mk X)

/-- The label offset of a class in `G₁`. -/
def off : ICls I → RLab k ℓ
  | .coord v c => (initSeed I v c, 0, 0)
  | _ => 0

/-- The vertices of `G_ε`. -/
def verts (ε : ZMod 2) : Finset (ICls I × RLab k ℓ) :=
  (names I).image fun x => (x.1, x.2 + ε • off I x.1)

lemma mem_names {x : ICls I × RLab k ℓ} : x ∈ names I ↔ x.1 ∈ classes I ∧ x.2 ∈ labs I x.1 := by
  obtain ⟨X, l⟩ := x
  simp only [names, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨Y, hY, l', hl', h⟩
    cases h
    exact ⟨hY, hl'⟩
  · rintro ⟨hX, hl⟩
    exact ⟨X, hX, l, hl, rfl⟩

lemma mem_verts {ε : ZMod 2} {x : ICls I × RLab k ℓ} :
    x ∈ verts I ε ↔ (x.1, x.2 + ε • off I x.1) ∈ names I := by
  obtain ⟨X, l⟩ := x
  simp only [verts, Finset.mem_image]
  constructor
  · rintro ⟨⟨Y, l'⟩, hy, h⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa [rlab_add_add_cancel] using hy
  · intro h
    exact ⟨_, h, by simp [rlab_add_add_cancel]⟩

lemma verts_zero : verts I 0 = names I := by
  simp [verts]

lemma card_verts (ε : ZMod 2) : (verts I ε).card = (names I).card := by
  refine Finset.card_image_of_injective _ fun x y h => ?_
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have := congrArg (· + ε • off I x.1) h2
  simp only [rlab_add_add_cancel] at this
  rw [h1, rlab_add_add_cancel] at this
  exact Prod.ext h1 this

/-! ### Adjacency -/

/-- A hub of class `X` with label `l` is adjacent to the vertex of class `Y` with label `m`. -/
def hubR : ICls I → RLab k ℓ → ICls I → RLab k ℓ → Prop
  | .upd e h c, l, Y, m =>
      (Y = trackCls I e c (h - 1) ∧ m.1 = l.1) ∨ (Y = trackCls I e c h ∧ m.1 = l.2.1) ∨
      (Y = .coef e h ∧ m.2.2 c = l.1 + l.2.1)
  | .junc e c, l, Y, m =>
      (Y = .coord (locU (sch I e)) ((permU (sch I e)).apply c) ∧ m.1 = l.1) ∨
      (Y = .coord (locV (sch I e)) ((permV (sch I e)).apply c) ∧ m.1 = l.2.1) ∨
      (Y = .sum e c ∧ m.1 = l.1 + l.2.1)
  | _, _, _, _ => False

/-- Adjacency of vertices (in both graphs). -/
def radj (x y : ICls I × RLab k ℓ) : Prop :=
  hubR I x.1 x.2 y.1 y.2 ∨ hubR I y.1 y.2 x.1 x.2

/-- Hubs. -/
def isHubR : ICls I → Prop
  | .upd .. => True
  | .junc .. => True
  | _ => False

lemma trackCls_not_hub (e : Fin I.schemas.length) (c : Coord k ℓ) (h : ℕ) :
    ¬ isHubR I (trackCls I e c h) := by
  unfold trackCls startCls endCls
  split_ifs <;> simp [isHubR]

lemma hubR_hub {X Y : ICls I} {l m : RLab k ℓ} (h : hubR I X l Y m) :
    isHubR I X ∧ ¬ isHubR I Y := by
  cases X with
  | upd e σ c =>
    refine ⟨trivial, ?_⟩
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact trackCls_not_hub I e c _
    · exact trackCls_not_hub I e c _
    · simp [isHubR]
  | junc e c =>
    refine ⟨trivial, ?_⟩
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [isHubR]
  | coord => exact h.elim
  | sum => exact h.elim
  | link => exact h.elim
  | track => exact h.elim
  | coef => exact h.elim

lemma radj_symm (x y : ICls I × RLab k ℓ) (h : radj I x y) : radj I y x := h.symm

lemma radj_irrefl (x : ICls I × RLab k ℓ) : ¬ radj I x x := by
  rintro (h | h) <;> exact (hubR_hub I h).2 (hubR_hub I h).1

lemma radj_iff_hub {x y : ICls I × RLab k ℓ} (hx : isHubR I x.1) :
    radj I x y ↔ hubR I x.1 x.2 y.1 y.2 := by
  refine ⟨fun h => h.elim id fun h => absurd hx (hubR_hub I h).2, Or.inl⟩

/-! ### Colors -/

/-- An injective encoding of classes. -/
def clsKey {w E : ℕ} : Cls k ℓ w E → ℕ × ℕ × ℕ × Option (Coord k ℓ)
  | .coord v c => (0, v, 0, some c)
  | .sum e c => (1, e, 0, some c)
  | .junc e c => (2, e, 0, some c)
  | .link e c => (3, e, 0, some c)
  | .track e σ c => (4, e, σ, some c)
  | .upd e σ c => (5, e, σ, some c)
  | .coef e σ => (6, e, σ, none)

lemma clsKey_injective {w E : ℕ} : Function.Injective (clsKey (k := k) (ℓ := ℓ) (w := w) (E := E)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [clsKey, Fin.ext_iff]

instance {w E : ℕ} : Countable (Cls k ℓ w E) := clsKey_injective.countable

/-- The color code of a class. -/
noncomputable def code : ICls I → ℕ := Classical.choose (exists_injective_nat (ICls I))

lemma code_injective : Function.Injective (code I) :=
  Classical.choose_spec (exists_injective_nat (ICls I))

/-! ### The graphs -/

/-- **The row-space graph** `G_ε`. -/
noncomputable abbrev rsGraph (ε : ZMod 2) : ColoredGraph where
  n := (verts I ε).card
  graph :=
    { Adj := fun i j => radj I ((verts I ε).equivFin.symm i).1 ((verts I ε).equivFin.symm j).1
      symm := ⟨fun _ _ h => radj_symm I _ _ h⟩
      loopless := ⟨fun _ h => radj_irrefl I _ h⟩ }
  color := fun i => code I ((verts I ε).equivFin.symm i).1.1

variable {I}

/-- The vertex of `G_ε` with index `i`. -/
noncomputable def vx {ε : ZMod 2} (i : Fin (rsGraph I ε).n) : ICls I × RLab k ℓ :=
  ((verts I ε).equivFin.symm i).1

lemma vx_mem {ε : ZMod 2} (i : Fin (rsGraph I ε).n) : vx i ∈ verts I ε :=
  ((verts I ε).equivFin.symm i).2

/-- The index of a vertex of `G_ε`. -/
noncomputable def ix (ε : ZMod 2) (x : ICls I × RLab k ℓ) (hx : x ∈ verts I ε) :
    Fin (rsGraph I ε).n :=
  (verts I ε).equivFin ⟨x, hx⟩

@[simp] lemma vx_ix {ε : ZMod 2} (x : ICls I × RLab k ℓ) (hx : x ∈ verts I ε) :
    vx (ix ε x hx) = x := by
  simp [vx, ix]

@[simp] lemma ix_vx {ε : ZMod 2} (i : Fin (rsGraph I ε).n) : ix ε (vx i) (vx_mem i) = i := by
  simp [vx, ix]

lemma vx_injective {ε : ZMod 2} : Function.Injective (vx (I := I) (ε := ε)) := by
  intro i j h
  rw [← ix_vx i, ← ix_vx j]
  simp only [ix]
  congr 2

lemma rs_adj {ε : ZMod 2} (i j : Fin (rsGraph I ε).n) :
    (rsGraph I ε).graph.Adj i j ↔ radj I (vx i) (vx j) := Iff.rfl

lemma rs_color {ε : ZMod 2} (i : Fin (rsGraph I ε).n) : (rsGraph I ε).color i = code I (vx i).1 :=
  rfl

lemma rs_color_eq {ε ε' : ZMod 2} (i : Fin (rsGraph I ε).n) (j : Fin (rsGraph I ε').n) :
    (rsGraph I ε).color i = (rsGraph I ε').color j ↔ (vx i).1 = (vx j).1 :=
  (code_injective I).eq_iff

lemma rs_n (ε : ZMod 2) : (rsGraph I ε).n = (names I).card := card_verts I ε

end Lax119563Proofs.RowSpace
