import Lax119563Proofs.Compiler.OrderPos

/-!
# The output of the compiler as a program-shaped list

`gDesc I ε` describes `graphDescription (reGraph I (ordL I) ε)` by data a sequential program
computes from the input (`graphDescription_eq_gDesc`, `encodeGraphPair_eq`):
* `n` (the sum of the class sizes), the colors `colorsOf 0` of the class sizes of `ordCls I`;
* `m`, then for every schema `e`, every hub class of `hubsCls I e` and every label `l` (with
  index `i`), the pairs `(hubStart X + i, v)` for `v ∈ hubNbrs ε X l`: the slot positions
  `slotPos` (closed formulas of `OrderPos`: `schBase`, `hubSize`, `sumSize`, `entBefore`,
  `nEnt`, `coefSteps`, `locStart` and the rank of a coordinate in `coordList (I.domain v)`),
  sorted.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

/-! ## Generic: indexed flatMaps over blocks -/

section Generic

variable {α β γ δ : Type*}

lemma finRange_map_getElem (L : List α) :
    (List.finRange L.length).map (fun u : Fin L.length => (L[(u : ℕ)], (u : ℕ))) = L.zipIdx := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

lemma finRange_flatMap_eq_zipIdx (L : List α) (g : ℕ → α → List δ) :
    (List.finRange L.length).flatMap (fun u : Fin L.length => g u L[(u : ℕ)]) =
      L.zipIdx.flatMap fun p => g p.2 p.1 := by
  rw [← finRange_map_getElem, List.flatMap_map]

lemma zipIdx_map_pair (G : β × γ → ℕ → List δ) (X : β) : ∀ (ls : List γ) (s : ℕ),
    ((ls.map fun m => (X, m)).zipIdx s).flatMap (fun q => G q.1 q.2) =
      (ls.zipIdx s).flatMap fun q => G (X, q.1) q.2
  | [], _ => rfl
  | m :: ls, s => by
    simp only [List.map_cons, List.zipIdx_cons, List.flatMap_cons]
    rw [zipIdx_map_pair G X ls (s + 1)]

variable [DecidableEq β]

/-- Indexed flatMap over a list of blocks: each block is indexed from its start. -/
lemma zipIdx_flatMap_blocks (G : β × γ → ℕ → List δ) :
    ∀ (P : List (β × List γ)) (s : ℕ), (P.map Prod.fst).Nodup →
      ((P.flatMap fun p => p.2.map fun m => (p.1, m)).zipIdx s).flatMap (fun q => G q.1 q.2) =
        P.flatMap fun p => (p.2.zipIdx (s + startIn P p.1)).flatMap fun q => G (p.1, q.1) q.2
  | [], _, _ => rfl
  | (X, ls) :: P, s, hnd => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [List.flatMap_cons, List.zipIdx_append, List.flatMap_append,
      zipIdx_flatMap_blocks G P _ hnd.2, List.flatMap_cons]
    congr 1
    · have : startIn ((X, ls) :: P) X = 0 := startIn_cons_self X ls P
      rw [this, Nat.add_zero]
      exact zipIdx_map_pair G X ls s
    · refine List.flatMap_congr fun p hp => ?_
      have hne : p.1 ≠ X := fun h => hnd.1 (h ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
      have e1 : startIn ((X, ls) :: P) p.1 = ls.length + startIn P p.1 := by
        have := startIn_append_right (P := [(X, ls)]) (P' := P) (X := p.1) (by simpa using hne)
        simpa [sizeOf'] using this
      rw [e1, List.length_map, Nat.add_assoc]

end Generic

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ) (ε : ZMod 2)

/-! ## Edges per hub class -/

lemma nbrPos_of_not_hub {x : VName I} (h : isHub I x.1 = false) : nbrPos I ε x = [] := by
  obtain ⟨X, l⟩ := x
  cases X <;> simp_all [isHub, nbrPos, slotsOf]

/-- **The edges, per hub class.** For every schema and every hub class `X` of `hubsCls I e`
with labels `ls`, the label with index `i` sits at `clsStart X + i`. -/
theorem edgeList_hubsCls :
    edgeList (reGraph I (ordL I) ε) =
      (List.finRange I.schemas.length).flatMap fun e => (hubsCls I e).flatMap fun p =>
        (p.2.zipIdx (clsStart I p.1)).flatMap fun q =>
          (nbrPos I ε (p.1, q.1)).map fun v => (q.2, v) := by
  rw [edgeList_nbrPos]
  have h1 := finRange_flatMap_eq_zipIdx (ordL I)
    (fun u x => (nbrPos I ε x).map fun v => (u, v))
  rw [h1]
  have h2 := zipIdx_flatMap_blocks (fun x u => (nbrPos I ε x).map fun v => (u, v)) (ordCls I) 0
    (nodup_ordCls_fst I)
  have h3 : (ordCls I).flatMap (fun p => p.2.map fun m => (p.1, m)) = ordL I :=
    (ordL_eq_flatMap I).symm
  rw [h3] at h2
  rw [h2]
  simp only [Nat.zero_add]
  have hc : ∀ F : ICls I × List Lab → List (ℕ × ℕ), (ordCls I).flatMap F =
      ((List.finRange I.schemas.length).flatMap fun e => hubsCls I e ++ nonhubsCls I e).flatMap F
        ++ ((List.finRange I.numLocations).flatMap fun v =>
          (coordList (I.domain v)).map fun c => (Cls.coord v c, coordLabs I v)).flatMap F :=
    fun F => by rw [ordCls, List.flatMap_append]
  rw [hc, List.flatMap_assoc]
  have hloc : ((List.finRange I.numLocations).flatMap fun v =>
      (coordList (I.domain v)).map fun c => (Cls.coord v c, coordLabs I v)).flatMap
        (fun p => (p.2.zipIdx (startIn (ordCls I) p.1)).flatMap fun q =>
          (nbrPos I ε (p.1, q.1)).map fun v => (q.2, v)) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro p hp
    simp only [List.mem_flatMap, List.mem_map] at hp
    obtain ⟨v, -, c, -, rfl⟩ := hp
    rw [List.flatMap_eq_nil_iff]
    intro q _
    rw [nbrPos_of_not_hub I ε rfl]; rfl
  rw [hloc, List.append_nil]
  refine List.flatMap_congr fun e _ => ?_
  rw [List.flatMap_append]
  have hnon : (nonhubsCls I e).flatMap
      (fun p => (p.2.zipIdx (startIn (ordCls I) p.1)).flatMap fun q =>
          (nbrPos I ε (p.1, q.1)).map fun v => (q.2, v)) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro p hp
    rw [List.flatMap_eq_nil_iff]
    intro q hq
    have hl : q.1 ∈ p.2 := by
      have := List.mem_iff_getElem.mp hq
      obtain ⟨i, hi, he⟩ := this
      rw [← he, List.getElem_zipIdx]; exact List.getElem_mem _
    have hx : (p.1, q.1) ∈ nonhubsE I e := by
      rw [nonhubsE_eq, List.mem_flatMap]
      exact ⟨p, hp, List.mem_map.mpr ⟨q.1, hl, rfl⟩⟩
    rw [nbrPos_of_not_hub I ε (not_hub_of_mem_nonhubsE I hx).1]; rfl
  rw [hnon, List.append_nil]
  rfl

end Lax119563Proofs.Compiler
