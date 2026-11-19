import Lax119563Proofs.Compiler.PEmitSteps

/-!
# Pass `P4` (list level): the edges of a schema in program form

`schE_eq`: the edges of schema `e` are the junction/link edges per column (`colE1`, with the
column index `r`) followed by the update edges per column and entry (`colE2`): for
`q ≤ k` and the rows `j ∈ rowsL c` (index `p`), the entry `t = q |rowsL c| + p` has the hub
`schBase + |D| colW + 4 (entBefore + t)` and the coefficient index `q |rowsR| + rank j`
(`updEnt`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

/-! ## Generic -/

lemma zipIdx_eq_map_idxOf {α : Type*} [BEq α] [LawfulBEq α] {L : List α} (hL : L.Nodup) :
    L.zipIdx = L.map fun c => (c, L.idxOf c) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_zipIdx, List.getElem_map, Nat.zero_add]
  rw [hL.idxOf_getElem]

lemma flatMap_idxOf {α β : Type*} [BEq α] [LawfulBEq α] {L : List α} (hL : L.Nodup)
    (g : α → ℕ → List β) :
    L.flatMap (fun c => g c (L.idxOf c)) = L.zipIdx.flatMap fun q => g q.1 q.2 := by
  rw [zipIdx_eq_map_idxOf hL, List.flatMap_map]

lemma zipIdx_flatMap_range {α β γ : Type*} (L : List α) (g : ℕ → α → β)
    (F : β × ℕ → List γ) : ∀ (m s : ℕ),
    (((List.range m).flatMap fun q => L.map (g q)).zipIdx s).flatMap F =
      (List.range m).flatMap fun q => L.zipIdx.flatMap fun x =>
        F (g q x.1, s + q * L.length + x.2)
  | 0, _ => rfl
  | m + 1, s => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.zipIdx_append,
      List.flatMap_append, zipIdx_flatMap_range L g F m s, List.flatMap_append,
      List.flatMap_singleton]
    congr 1
    rw [List.zipIdx_map, List.flatMap_map]
    have hl : ((List.range m).flatMap fun q => L.map (g q)).length = m * L.length := by
      rw [List.length_flatMap]; simp [List.map_const', List.sum_replicate]
    rw [hl]
    have : ∀ (t : ℕ), (L.zipIdx t) = (L.zipIdx).map fun x => (x.1, t + x.2) := by
      intro t; rw [List.zipIdx_eq_map_add]
    rw [this, List.flatMap_map]
    rfl

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ) (ε : ZMod 2)

/-! ## The sections of a schema -/

/-- The junction and link edges of column `c` (index `r`) of schema `e`. -/
noncomputable def colE1 (e : Fin I.schemas.length) (c : Coord k ℓ) (r : ℕ) : List (ℕ × ℕ) :=
  (if isTern (sch I e) then hubE I ε (.junc e c) bits2 (schBase I e + r * colW I e) else []) ++
    hubE I ε (.link e c) bits1
      (schBase I e + r * colW I e + (if isTern (sch I e) then 4 else 0))

/-- The edges of schema `e`. -/
noncomputable def schE (e : Fin I.schemas.length) : List (ℕ × ℕ) :=
  (hubsCls I e).flatMap fun p => hubE I ε p.1 p.2 (hubStart I p.1)

lemma gEdges_eq_schE : gEdges I ε = (List.finRange I.schemas.length).flatMap (schE I ε) := rfl

/-- **The edges of a schema, by sections.** -/
theorem schE_eq (e : Fin I.schemas.length) : schE I ε e =
    (coordList (dom I e)).zipIdx.flatMap (fun q => colE1 I ε e q.1 q.2) ++
      (coordList (dom I e)).flatMap fun c => (stepsC c).zipIdx.flatMap fun q =>
        hubE I ε (.upd e q.1 c) bits2 (schBase I e + (coordList (dom I e)).length * colW I e +
          4 * (entBefore I e c + q.2)) := by
  have hnd := nodup_coordList (dom I e)
  rw [schE, hubsCls, List.flatMap_append, List.flatMap_assoc, List.flatMap_assoc]
  congr 1
  · rw [← flatMap_idxOf hnd (fun c r => colE1 I ε e c r)]
    refine List.flatMap_congr fun c _ => ?_
    unfold colE1
    split <;> next h => simp [hubStart, h]
  · refine List.flatMap_congr fun c _ => ?_
    rw [List.flatMap_map, ← flatMap_idxOf (nodup_stepsC c)
      (fun σ t => hubE I ε (.upd e σ c) bits2 (schBase I e + (coordList (dom I e)).length *
        colW I e + 4 * (entBefore I e c + t)))]
    rfl

end Lax119563Proofs.Compiler
