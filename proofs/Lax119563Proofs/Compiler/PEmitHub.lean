import Lax119563Proofs.Compiler.OutDesc
import Lax119563Proofs.Compiler.PJoinFacts

/-!
# Pass `P4` (list level): the edges of one hub class in program form

`P4` emits, for every hub class, its labels in order and for each label the sorted neighbor
positions (`gEdges`, `OutDesc`). Here these lists are written with natural-number bits
`a = i / 2`, `b = i % 2` for the label index `i` (`hubE_bits2`, `hubE_bits1`) and with
explicit numbers:
* coordinate slots by the join answers (`slotPos_coord_ans`: the answer
  `[s, off, labs, seed]` gives the position `locBase + off (+ b)`, present unless `labs = 1`
  and `b ≠ ε · seed`, `cposA`);
* two optional positions sorted (`sort2`);
* junctions (`junE`), links (`lnkE`), updates (`updE`, `updFE` for the first entry of a column
  of a binary schema).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

/-! ## Generic helpers -/

/-- Two optional positions, the present ones sorted. -/
def sort2 : Option ℕ → Option ℕ → List ℕ
  | some x, some y => if x ≤ y then [x, y] else [y, x]
  | some x, none => [x]
  | none, some y => [y]
  | none, none => []

lemma mergeSort_two (o₁ o₂ : Option ℕ) :
    ([o₁, o₂].filterMap id).mergeSort (fun a b => decide (a ≤ b)) = sort2 o₁ o₂ := by
  cases o₁ with
  | none => cases o₂ <;> simp [sort2, List.filterMap_cons]
  | some x =>
    cases o₂ with
    | none => simp [sort2, List.filterMap_cons]
    | some y =>
      simp only [List.filterMap_cons, id, List.filterMap_nil, sort2]
      split_ifs with h
      · exact mergeSort_eq_of (List.Perm.refl _) (by simp [h])
      · exact mergeSort_eq_of (List.Perm.swap x y []) (by simp; omega)

/-- The position of a coordinate slot from a join answer `[s, off, labs, seed]`. -/
def cposA (LB e : ℕ) (a : List ℕ) (b : ℕ) : Option ℕ :=
  if a.getD 2 0 = 1 then (if b = e * a.getD 3 0 then some (LB + a.getD 1 0) else none)
  else some (LB + a.getD 1 0 + b)

/-- The label with index `i` of a two-bit class (`bits2`). -/
def lab2 (i : ℕ) : Lab := (((i / 2 : ℕ) : ZMod 2), ((i % 2 : ℕ) : ZMod 2))

lemma val_natCast_lt {a : ℕ} (h : a < 2) : ((a : ZMod 2)).val = a := by
  rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt h

lemma val_add_natCast (a b : ℕ) : (((a : ℕ) : ZMod 2) + ((b : ℕ) : ZMod 2)).val = (a + b) % 2 := by
  rw [← Nat.cast_add, ZMod.val_natCast]

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ) (ε : ZMod 2)

/-! ## Coordinate slots by the answers -/

lemma val_mul_z2 (x y : ZMod 2) : (x * y).val = x.val * y.val := by
  rcases Lax119563Proofs.Reduction.zmod2_cases x with rfl | rfl <;> rcases Lax119563Proofs.Reduction.zmod2_cases y with rfl | rfl <;> rfl

/-- **Coordinate slots by the join answers.** -/
lemma slotPos_coord_ans {v : Fin I.numLocations} {c' : Coord k ℓ} (hc : c' ∈ I.domain v)
    (b : ZMod 2) (s : ℕ) :
    slotPos I ε (.coord v c') b = cposA (locBase I) ε.val (ansRec I v c' s) b.val := by
  have h1 := clsStart_coord I hc
  have h2 : locBase I ≤ locStart I v := by simp only [locStart]; omega
  simp only [slotPos, cposA, ansRec, List.getD_cons_succ, List.getD_cons_zero, labsN]
  by_cases hi : (I.init v).isSome
  · have hl : (coordLabs I v).length = 1 := by simp [coordLabs, hi]
    rw [if_pos hi, hl, if_pos rfl]
    rw [hl, Nat.mul_one] at h1
    rw [h1]
    have e1 : (b = ε * initSeed I v c') ↔ b.val = ε.val * (initSeed I v c').val := by
      rw [← val_mul_z2]; exact ⟨fun h => h ▸ rfl, fun h => ZMod.val_injective _ h⟩
    by_cases hb : b = ε * initSeed I v c'
    · rw [if_pos hb, if_pos (e1.mp hb)]; congr 1; omega
    · rw [if_neg hb, if_neg (fun h => hb (e1.mpr h))]
  · have hl : (coordLabs I v).length = 2 := by simp [coordLabs, hi, bits1]
    rw [hl] at h1
    rw [h1, hl, if_neg hi, if_neg (by omega)]
    congr 1; omega

/-! ## Hub edges -/

/-- The edges of the hub class `X` with labels `ls` starting at position `h`. -/
noncomputable def hubE (X : ICls I) (ls : List Lab) (h : ℕ) : List (ℕ × ℕ) :=
  (ls.zipIdx h).flatMap fun q => (hubNbrs I ε X q.1).map fun v => (q.2, v)

lemma gEdges_eq_hubE : gEdges I ε = (List.finRange I.schemas.length).flatMap fun e =>
    (hubsCls I e).flatMap fun p => hubE I ε p.1 p.2 (hubStart I p.1) := rfl

lemma hubE_bits2 (X : ICls I) (h : ℕ) : hubE I ε X bits2 h =
    (List.range 4).flatMap fun i => (hubNbrs I ε X (lab2 i)).map fun v => (h + i, v) := by
  simp only [hubE, bits2, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons,
    List.flatMap_nil, List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
    List.flatMap_singleton, lab2]
  norm_num

lemma hubE_bits1 (X : ICls I) (h : ℕ) : hubE I ε X bits1 h =
    (List.range 2).flatMap fun a =>
      (hubNbrs I ε X (((a : ℕ) : ZMod 2), 0)).map fun v => (h + a, v) := by
  simp only [hubE, bits1, List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons,
    List.flatMap_nil, List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
    List.flatMap_singleton]
  norm_num

/-! ## Section bases -/

/-- The start of the sum section of schema `e`. -/
noncomputable def sumBase (e : Fin I.schemas.length) : ℕ := schBase I e + hubSize I e

/-- The start of the track section of schema `e`. -/
noncomputable def trackBase (e : Fin I.schemas.length) : ℕ := sumBase I e + sumSize I e

/-- The start of the coefficient section of schema `e`. -/
noncomputable def coefBase (e : Fin I.schemas.length) : ℕ := trackBase I e + 2 * nEnt I e

/-! ## Junctions -/

/-- The edges of one junction label: the sum, then the two coordinates sorted. -/
def junE1 (h sp : ℕ) (pu pv : Option ℕ) (a b : ℕ) : List (ℕ × ℕ) :=
  (h, sp + (a + b) % 2) :: (sort2 pu pv).map fun v => (h, v)

lemma lab2_fst {i : ℕ} : (lab2 i).1 = (((i / 2 : ℕ)) : ZMod 2) := rfl
lemma lab2_snd {i : ℕ} : (lab2 i).2 = (((i % 2 : ℕ)) : ZMod 2) := rfl

/-- **Junctions.** -/
theorem hubE_junc {e : Fin I.schemas.length} {c : Coord k ℓ} (ht : isTern (sch I e) = true)
    (hc : c ∈ dom I e) (h : ℕ) :
    hubE I ε (.junc e c) bits2 h = (List.range 4).flatMap fun i =>
      junE1 (h + i) (sumBase I e + 2 * (coordList (dom I e)).idxOf c)
        (slotPos I ε (coordU e c) (((i / 2 : ℕ)) : ZMod 2))
        (slotPos I ε (coordV e c) (((i % 2 : ℕ)) : ZMod 2)) (i / 2) (i % 2) := by
  rw [hubE_bits2]
  refine List.flatMap_congr fun i _ => ?_
  rw [hubNbrs_junc I ε ht hc]
  have e1 : ([(coordU e c, (lab2 i).1), (coordV e c, (lab2 i).2)].filterMap
      fun s => slotPos I ε s.1 s.2) =
      [slotPos I ε (coordU e c) (lab2 i).1, slotPos I ε (coordV e c) (lab2 i).2].filterMap id := by
    simp only [List.filterMap_cons, List.filterMap_nil, id]
  rw [e1, mergeSort_two]
  simp only [slotPos, Option.toList_some, List.singleton_append, List.map_cons, junE1,
    lab2_fst, lab2_snd, val_add_natCast, sumBase]

/-! ## Links -/

/-- The edges of one link label: the last track of the column, then the end coordinate. -/
def lnkE1 (h tp : ℕ) (pw : Option ℕ) (a : ℕ) : List (ℕ × ℕ) :=
  (h, tp + a) :: pw.toList.map fun v => (h, v)

/-- **Links** (`k ≥ 2`). -/
theorem hubE_link (hk : 2 ≤ k) {e : Fin I.schemas.length} {c : Coord k ℓ} (hc : c ∈ dom I e)
    (h : ℕ) :
    hubE I ε (.link e c) bits1 h = (List.range 2).flatMap fun a =>
      lnkE1 (h + a) (trackBase I e + 2 * (entBefore I e c + (stepsC c).length - 1))
        (slotPos I ε (endCls I e c) ((a : ℕ) : ZMod 2)) a := by
  rw [hubE_bits1]
  have hne := stepsC_ne_nil hk c
  have hσ : (stepsC c).getLast hne ∈ stepsC c := List.getLast_mem hne
  have hidx : (stepsC c).idxOf ((stepsC c).getLast hne) = (stepsC c).length - 1 := by
    rw [List.getLast_eq_getElem]
    exact (nodup_stepsC c).idxOf_getElem _ _
  have hpos : 0 < (stepsC c).length := List.length_pos_of_ne_nil hne
  refine List.flatMap_congr fun a ha => ?_
  have ha2 : a < 2 := List.mem_range.mp ha
  rw [hubNbrs_link I ε hk hc, trackAt_numSteps, dif_neg hne]
  simp only [slotPos, Option.toList_some, List.singleton_append, List.map_cons, lnkE1,
    val_natCast_lt ha2, hidx, trackBase, sumBase]
  congr 2
  omega

/-! ## Updates -/

/-- The edges of one update label: the previous track (or sum), the track, the coefficient. -/
def updE1 (h pp tp cp : ℕ) (a b : ℕ) : List (ℕ × ℕ) :=
  [(h, pp + a), (h, tp + b), (h, cp + (a + b) % 2)]

/-- The edges of one update label at the first entry of a column of a binary schema: the
track, the coefficient, then the start coordinate. -/
def updF1 (h tp cp : ℕ) (pu : Option ℕ) (a b : ℕ) : List (ℕ × ℕ) :=
  [(h, tp + b), (h, cp + (a + b) % 2)] ++ pu.toList.map fun v => (h, v)

/-- The base of the previous track (or of the sum) of an update. -/
noncomputable def prevBase (e : Fin I.schemas.length) (c : Coord k ℓ) (t : ℕ) : ℕ :=
  if t = 0 then sumBase I e + 2 * (coordList (dom I e)).idxOf c
  else trackBase I e + 2 * (entBefore I e c + t - 1)

/-- **Updates** (not the first entry of a column of a binary schema). -/
theorem hubE_upd {e : Fin I.schemas.length} {c : Coord k ℓ} {σ : ℕ} (hc : c ∈ dom I e)
    (hσ : σ ∈ stepsC c) (h0 : 0 < (stepsC c).idxOf σ ∨ isTern (sch I e) = true) (h : ℕ) :
    hubE I ε (.upd e σ c) bits2 h = (List.range 4).flatMap fun i =>
      updE1 (h + i) (prevBase I e c ((stepsC c).idxOf σ))
        (trackBase I e + 2 * (entBefore I e c + (stepsC c).idxOf σ))
        (coefBase I e + 2 * (coefSteps I e).idxOf σ) (i / 2) (i % 2) := by
  rw [hubE_bits2]
  have hj : (stepsC c).idxOf σ < (stepsC c).length := List.idxOf_lt_length_of_mem hσ
  have hget : (stepsC c)[(stepsC c).idxOf σ] = σ := List.getElem_idxOf hj
  have htr := trackAt_stepsC I e c hj
  rw [hget] at htr
  refine List.flatMap_congr fun i hi => ?_
  have hi2 : i / 2 < 2 := by have := List.mem_range.mp hi; omega
  have hi3 : i % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rw [hubNbrs_upd I ε hc hσ h0]
  have hp : slotPos I ε (trackAt I e c σ) (lab2 i).1 =
      some (prevBase I e c ((stepsC c).idxOf σ) + i / 2) := by
    rw [htr, lab2_fst]
    unfold prevBase
    split
    · next h00 =>
      have ht : isTern (sch I e) = true := by rcases h0 with h0 | h0; omega; exact h0
      simp only [startCls, ht, if_true, slotPos, if_pos h00, sumBase, val_natCast_lt hi2]
    · next h00 =>
      simp only [slotPos, if_neg h00, trackBase, sumBase, val_natCast_lt hi2]
      rw [(nodup_stepsC c).idxOf_getElem _ (by omega)]
      congr 1; omega
  simp only [slotsOf, List.filterMap_cons, List.filterMap_nil, hp]
  simp only [slotPos, List.map_cons, List.map_nil, updE1, lab2_fst, lab2_snd, val_add_natCast,
    val_natCast_lt hi3, trackBase, sumBase, coefBase]

/-- **Updates at the first entry of a column of a binary schema.** -/
theorem hubE_updF {e : Fin I.schemas.length} {c : Coord k ℓ} {σ : ℕ} (hc : c ∈ dom I e)
    (hσ : σ ∈ stepsC c) (h0 : (stepsC c).idxOf σ = 0) (ht : isTern (sch I e) = false)
    (h : ℕ) :
    hubE I ε (.upd e σ c) bits2 h = (List.range 4).flatMap fun i =>
      updF1 (h + i) (trackBase I e + 2 * entBefore I e c)
        (coefBase I e + 2 * (coefSteps I e).idxOf σ)
        (slotPos I ε (startCls I e c) (((i / 2 : ℕ)) : ZMod 2)) (i / 2) (i % 2) := by
  rw [hubE_bits2]
  refine List.flatMap_congr fun i hi => ?_
  have hi3 : i % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rw [hubNbrs_upd_first I ε hc hσ h0 ht]
  simp only [slotPos, Option.toList_some, List.singleton_append, List.map_cons, List.map_append,
    updF1, lab2_fst, lab2_snd, val_add_natCast, val_natCast_lt hi3, h0, trackBase, sumBase,
    coefBase, Nat.add_zero, List.cons_append, List.map_nil, List.nil_append, List.append_assoc]

end Lax119563Proofs.Compiler
