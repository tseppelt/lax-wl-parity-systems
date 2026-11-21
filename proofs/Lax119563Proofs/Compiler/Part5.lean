import Lax119563Proofs.Compiler.Part2
import Lax119563Proofs.Compiler.Part3
import Lax119563Proofs.Compiler.Part4

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchGlue` -/

section Compiler_P4SchGlue

/-!
# Pass `P4`, schema part: list glue for the rank codes

* `codesC_eq`: the rank codes computed by section 1 for the column `D[r]` are
  `(rkL I e D[r]).map rcode`, with the running block-change count `dChg k (blocks of D[0..r]) - 1`;
* `dist1_eq`: the update of that count by `p4Hd`.
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

lemma blkRows_le (cs : List (Coord k ℓ)) : blkRows cs ≤ k - 1 := by
  unfold blkRows
  exact (List.countP_le_length).trans (by simp)

lemma idxOf_rowsR_all (e : Fin I.schemas.length) {c : Coord k ℓ}
    (hc : c ∈ coordList (dom I e)) (hck : ¬ (c.1 : ℕ) + 1 < k) {j : ℕ} (hj : j < k - 1) :
    (rowsR I e).idxOf j = j := by
  have hP : ∀ j', PA I e j' = true := fun j' => by
    simp only [PA, decide_eq_true_eq]; exact ⟨c, hc, Or.inr (by have := c.1.2; omega)⟩
  rw [rank_blk I e hj (hP j), List.countP_eq_length.mpr (fun j' _ => hP j'), List.length_range]

/-- **The rank codes of a column.** -/
lemma codesC_eq (hk : 2 ≤ k) (e : Fin I.schemas.length) {r : ℕ}
    (hr : r < (coordList (dom I e)).length) :
    codesC k (blkRows (coordList (dom I e)))
        (dChg k (((coordList (dom I e)).take (r + 1)).map fun c => (c.1 : ℕ)) - 1)
        ((coordList (dom I e))[r].1 : ℕ) (orsL (coordList (dom I e)))
        (blockDescription (coordList (dom I e))[r].2) =
      (rkL I e (coordList (dom I e))[r]).map rcode := by
  set c := (coordList (dom I e))[r] with hcdef
  have hcD : c ∈ coordList (dom I e) := List.getElem_mem hr
  have hce : c ∈ dom I e := mem_coordList.mp hcD
  rw [rkL, rowsL_eq, List.map_append, List.map_append, codesC, chkRanks_eq I e hce]
  congr 1
  unfold blkCodes
  by_cases hck : (c.1 : ℕ) + 1 < k
  · rw [if_pos hck, if_pos hck]
    simp only [List.map_cons, List.map_nil]
    rw [rank_blk_eq I e hr hck]
    have := blkRows_le (coordList (dom I e))
    by_cases hB : blkRows (coordList (dom I e)) = k - 1
    · rw [if_pos hB, if_neg (by omega)]
    · rw [if_neg hB, if_pos (by omega)]
  · rw [if_neg hck, if_neg hck, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    simp only [Function.comp_apply]
    rw [idxOf_rowsR_all I e hcD hck (List.mem_range.mp hj)]

lemma dChg_pos (p : ℕ) : ∀ (l : List ℕ), l ≠ [] → (∀ x ∈ l, x ≠ p) → 1 ≤ dChg p l
  | [], h, _ => absurd rfl h
  | a :: l, _, h => by
    simp only [dChg, if_neg (h a List.mem_cons_self)]; omega

/-- **The block-change count after a column.** -/
lemma dist1_eq (cs : List (Coord k ℓ)) {r : ℕ} (hr : r < cs.length) (P : ℕ)
    (hP : 0 < r → P = (cs[r - 1].1 : ℕ)) :
    dist1 r (if r = 0 then 0 else dChg k ((cs.take r).map fun c => (c.1 : ℕ)) - 1) P
        (cs[r].1 : ℕ) = dChg k ((cs.take (r + 1)).map fun c => (c.1 : ℕ)) - 1 := by
  have hlt : ∀ c : Coord k ℓ, (c.1 : ℕ) ≠ k := fun c => by have := c.1.2; omega
  rw [List.take_add_one, List.getElem?_eq_getElem hr, Option.toList_some, List.map_append,
    List.map_singleton, dChg_append]
  unfold dist1
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · simp [dChg, hlt]
  · rw [if_neg (by omega), if_neg (by omega)]
    have hne : (cs.take r).map (fun c => (c.1 : ℕ)) ≠ [] := by
      intro h; have := congrArg List.length h
      simp only [List.length_map, List.length_take, List.length_nil] at this; omega
    have h1 := dChg_pos k _ hne (by simp only [List.mem_map]; rintro _ ⟨c, -, rfl⟩; exact hlt c)
    have hlast : ((cs.take r).map fun c => (c.1 : ℕ)).getLastD k = (cs[r - 1].1 : ℕ) := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
      simp [List.getElem?_take, show r - 1 < r by omega, List.getElem?_eq_getElem
        (show r - 1 < cs.length by omega), Nat.min_eq_left hr.le]
    rw [hlast, hP hr0]
    omega

/-! ## Coordinate slots by the answers, in numbers -/

lemma labsN_cases (v : Fin I.numLocations) : labsN I v = 1 ∨ labsN I v = 2 := by
  unfold labsN coordLabs
  split_ifs <;> simp [bits1]

lemma slot_ans (ε : ZMod 2) {v : Fin I.numLocations} {c' : Coord k ℓ} (hc : c' ∈ I.domain v)
    {b : ℕ} (hb : b < 2) (s : ℕ) :
    slotPos I ε (.coord v c') ((b : ℕ) : ZMod 2) =
      cposN (locBase I) (aOff (ansRec I v c' s)) (ansMode ε.val (ansRec I v c' s)) b := by
  rw [slotPos_coord_ans I ε hc _ s, val_natCast_lt hb]
  refine cposA_eq _ _ _ _ (by omega) (by have := ZMod.val_lt ε; omega) ?_ ?_
  · simp only [ansRec, List.getD_cons_succ, List.getD_cons_zero]
    have := ZMod.val_lt (initSeed I v c'); omega
  · simpa [ansRec] using labsN_cases I v

lemma memU {e : Fin I.schemas.length} {c : Coord k ℓ} (hc : c ∈ dom I e) :
    (permU (sch I e)).apply c ∈ I.domain (locU (sch I e)) := by
  have hw := wf_sch I e
  unfold dom at hc
  generalize sch I e = sc at hw hc
  cases sc with
  | binary u v D σ τ => exact hw.2.1 (Finset.mem_image_of_mem _ hc)
  | ternary u v w' D σ τ π => exact hw.2.2.2.1 (Finset.mem_image_of_mem _ hc)

lemma memV {e : Fin I.schemas.length} {c : Coord k ℓ} (hc : c ∈ dom I e) :
    (permV (sch I e)).apply c ∈ I.domain (locV (sch I e)) := by
  have hw := wf_sch I e
  unfold dom at hc
  generalize sch I e = sc at hw hc
  cases sc with
  | binary u v D σ τ => exact hw.2.2 (Finset.mem_image_of_mem _ hc)
  | ternary u v w' D σ τ π => exact hw.2.2.2.2.1 (Finset.mem_image_of_mem _ hc)

lemma memEnd {e : Fin I.schemas.length} {c : Coord k ℓ} (hc : c ∈ dom I e) :
    (permEnd (sch I e)).apply c ∈ I.domain (locEnd (sch I e)) := by
  have hw := wf_sch I e
  unfold dom at hc
  generalize sch I e = sc at hw hc
  cases sc with
  | binary u v D σ τ => exact hw.2.2 (Finset.mem_image_of_mem _ hc)
  | ternary u v w' D σ τ π => exact hw.2.2.2.2.2 (Finset.mem_image_of_mem _ hc)

/-- `tern` as a number. -/
def tnN (b : Bool) : ℕ := if b then 1 else 0

/-- **The junction and link edges of a column, in numbers.** -/
lemma colE1_eq (hk : 2 ≤ k) (ε : ZMod 2) (e : Fin I.schemas.length) {c : Coord k ℓ}
    (hc : c ∈ dom I e) (r : ℕ) (hr : (coordList (dom I e)).idxOf c = r) (sU sV sW : ℕ) :
    colE1 I ε e c r = col1E (tnN (isTern (sch I e))) (schBase I e + r * colW I e)
      (sumBase I e + 2 * r) (trackBase I e + 2 * (entBefore I e c + (stepsC c).length - 1))
      (locBase I) ε.val
      (ansRec I (locU (sch I e)) ((permU (sch I e)).apply c) sU)
      (ansRec I (locV (sch I e)) ((permV (sch I e)).apply c) sV)
      (ansRec I (locEnd (sch I e)) ((permEnd (sch I e)).apply c) sW) := by
  have hL : hubE I ε (.link e c) bits1 (schBase I e + r * colW I e +
      (if isTern (sch I e) then 4 else 0)) = lnkL (schBase I e + r * colW I e +
        4 * tnN (isTern (sch I e))) (trackBase I e + 2 * (entBefore I e c + (stepsC c).length - 1))
        (locBase I) (aOff (ansRec I (locEnd (sch I e)) ((permEnd (sch I e)).apply c) sW))
        (ansMode ε.val (ansRec I (locEnd (sch I e)) ((permEnd (sch I e)).apply c) sW)) := by
    rw [hubE_link I ε hk hc, lnkL]
    have h4 : (if isTern (sch I e) then 4 else 0) = 4 * tnN (isTern (sch I e)) := by
      unfold tnN; split_ifs <;> rfl
    rw [h4]
    refine List.flatMap_congr fun a ha => ?_
    have ha2 : a < 2 := List.mem_range.mp ha
    rw [endCls, slot_ans I ε (memEnd I hc) ha2 sW]
  unfold colE1 col1E
  rw [hL]
  congr 1
  cases ht : isTern (sch I e)
  · simp [tnN]
  · simp only [if_true, tnN]
    rw [hubE_junc I ε ht hc, junL, hr]
    refine List.flatMap_congr fun i hi => ?_
    have hi1 : i / 2 < 2 := by have := List.mem_range.mp hi; omega
    have hi2 : i % 2 < 2 := Nat.mod_lt _ (by norm_num)
    rw [coordU, coordV, slot_ans I ε (memU I hc) hi1 sU, slot_ans I ε (memV I hc) hi2 sV]

end Lax119563Proofs.Compiler

end Compiler_P4SchGlue

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchAns` -/

section Compiler_P4SchAns

/-!
# Pass `P4`, schema part: the answer words of a schema per column

`ansE_flatten`: `(ansE I e).flatten` = the words consumed by section 1 (`a1C`, per column:
ternary `U, V, W`; binary `V` = the end answer) followed by those of section 2 (`a2C`: binary
`U`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The `U` answer of column `q.1` (index `q.2`) with sequence number `s`. -/
noncomputable def aU (e : Fin I.schemas.length) (c : Coord k ℓ) (s : ℕ) : List ℕ :=
  ansRec I (locU (sch I e)) ((permU (sch I e)).apply c) s

noncomputable def aV (e : Fin I.schemas.length) (c : Coord k ℓ) (s : ℕ) : List ℕ :=
  ansRec I (locV (sch I e)) ((permV (sch I e)).apply c) s

noncomputable def aW (e : Fin I.schemas.length) (c : Coord k ℓ) (s : ℕ) : List ℕ :=
  ansRec I (locEnd (sch I e)) ((permEnd (sch I e)).apply c) s

/-- The sequence number of the end answer of column `r`. -/
noncomputable def sW (e : Fin I.schemas.length) (r : ℕ) : ℕ :=
  if isTern (sch I e) then ansBase I e + 3 * r + 2 else ansBase I e + r

/-- The answer words of column `q.2` consumed by section 1. -/
noncomputable def a1C (e : Fin I.schemas.length) (q : Coord k ℓ × ℕ) : List ℕ :=
  ans1 (tnN (isTern (sch I e))) (aU I e q.1 (ansBase I e + 3 * q.2))
    (aV I e q.1 (ansBase I e + 3 * q.2 + 1)) (aW I e q.1 (sW I e q.2))

/-- The answer words of column `q.2` consumed by section 2. -/
noncomputable def a2C (e : Fin I.schemas.length) (q : Coord k ℓ × ℕ) : List ℕ :=
  if isTern (sch I e) then [] else
    aU I e q.1 (ansBase I e + (coordList (dom I e)).length + q.2)

lemma ansE_flatten (e : Fin I.schemas.length) :
    (ansE I e).flatten = (coordList (dom I e)).zipIdx.flatMap (a1C I e) ++
      (coordList (dom I e)).zipIdx.flatMap (a2C I e) := by
  unfold ansE a1C a2C aU aV aW sW dom
  cases h : sch I e with
  | binary u v D σ τ =>
    simp [h, Schema.domain, isTern, tnN, ans1, locU, locV, locEnd, permU, permV, permEnd, List.flatten_append,
      List.flatMap, List.map_map, Function.comp_def]
  | ternary u v w' D σ τ π =>
    simp [h, Schema.domain, isTern, tnN, ans1, locU, locV, locEnd, permU, permV, permEnd, List.flatMap,
      List.map_map, Function.comp_def, List.flatten_flatten]

end Lax119563Proofs.Compiler

end Compiler_P4SchAns

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchL1` -/

section Compiler_P4SchL1

/-!
# Pass `P4`, schema part: the column loop of section 1 (`p4S1_good`)
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-! ## Column facts -/

/-- The columns of schema `e`. -/
noncomputable abbrev cL (e : Fin I.schemas.length) : List (Coord k ℓ) := coordList (dom I e)

/-- The entries of the first `r` columns. -/
noncomputable def entB (e : Fin I.schemas.length) (r : ℕ) : ℕ :=
  (((cL I e).take r).map fun c => (stepsC c).length).sum

/-- The rank codes of a column. -/
noncomputable def codesL (e : Fin I.schemas.length) (c : Coord k ℓ) : List ℕ :=
  (rkL I e c).map rcode

/-- The block-change count before column `r`. -/
noncomputable def distR (e : Fin I.schemas.length) (r : ℕ) : ℕ :=
  if r = 0 then 0 else dChg k (((cL I e).take r).map fun c => (c.1 : ℕ)) - 1

lemma length_stepsC_rowsL (c : Coord k ℓ) : (stepsC c).length = (k + 1) * (rowsL c).length := by
  rw [stepsC_eq, List.length_flatMap]
  simp [List.map_const', List.sum_replicate]

lemma rowsL_pos (hk : 2 ≤ k) (c : Coord k ℓ) : 1 ≤ (rowsL c).length := by
  have h := List.length_pos_of_ne_nil (stepsC_ne_nil hk c)
  rw [length_stepsC_rowsL] at h
  rcases Nat.eq_zero_or_pos (rowsL c).length with h0 | h0
  · rw [h0] at h; omega
  · exact h0

lemma length_codesL (e : Fin I.schemas.length) (c : Coord k ℓ) :
    (codesL I e c).length = (rowsL c).length := by simp [codesL, rkL]

lemma entBefore_get (e : Fin I.schemas.length) {r : ℕ} (hr : r < (cL I e).length) :
    entBefore I e (cL I e)[r] = entB I e r := by
  unfold entBefore entB
  rw [(nodup_coordList (dom I e)).idxOf_getElem]

lemma entB_succ (e : Fin I.schemas.length) {r : ℕ} (hr : r < (cL I e).length) :
    entB I e (r + 1) = entB I e r + (stepsC (cL I e)[r]).length := by
  simp only [entB, List.take_add_one, List.getElem?_eq_getElem hr, Option.toList_some,
    List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]

lemma entB_le (e : Fin I.schemas.length) (r : ℕ) : entB I e r ≤ nEnt I e := by
  unfold entB nEnt cL
  conv_rhs => rw [← List.take_append_drop r (coordList (dom I e))]
  rw [List.map_append, List.sum_append]; omega

lemma codesL_pos (hk : 2 ≤ k) (e : Fin I.schemas.length) (c : Coord k ℓ) (X : ℕ)
    (hX : X ∈ codesL I e c) : 1 ≤ X := by
  simp only [codesL, List.mem_map] at hX
  obtain ⟨ρ, -, rfl⟩ := hX; unfold rcode; omega

end Lax119563Proofs.Compiler

end Compiler_P4SchL1

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchL1b` -/

section Compiler_P4SchL1b

/-!
# Pass `P4`, schema part: the column loop of section 1, invariant and step
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The column loop of section 1. -/
def p4S1 : CStm CR CQ := .loop (.lt (rv r4K) (rv r4D)) p4C1

/-- The state of the column loop of section 1 after `r` columns. -/
def L1Inv (w : ℕ) (ε : ZMod 2) (e : Fin I.schemas.length) (R : List ℕ) (s0 : NSt CR CQ)
    (r : ℕ) (s : NSt CR CQ) : Prop :=
  EM s0 s (((cL I e).zipIdx.take r).flatMap fun q => colE1 I ε e q.1 q.2) ∧
  s.stk qRk = (((cL I e).take r).flatMap fun c => codesL I e c ++ [0]).reverse ++ s0.stk qRk ∧
  s.stk qAns = ((cL I e).zipIdx.drop r).flatMap (a1C I e) ++ R ∧
  s.stk qA2 = (((cL I e).zipIdx.take r).flatMap (a1C I e)).reverse ++ s0.stk qA2 ∧
  (∀ q, q ≠ q4E → q ≠ qRk → q ≠ qAns → q ≠ qA2 → s.stk q = s0.stk q) ∧
  s.env r4K = r ∧ s.env r4Dist = distR I e r ∧
  (∀ h : r - 1 < (cL I e).length, 0 < r → s.env r4Prev = (((cL I e)[r - 1]'h).1 : ℕ)) ∧
  s.env r4H = schBase I e + r * colW I e ∧ s.env r4SP = sumBase I e + 2 * r ∧
  s.env r4TP = trackBase I e + 2 * entB I e r ∧ s.env r4V < 2 ^ w ∧ s.Bdd w ∧
  s.pos = s0.pos + (encodeNats (((cL I e).take r).flatMap cdesc)).length ∧ s.out = s0.out ∧
  ∀ reg, reg ∉ c1W → s.env reg = s0.env reg

lemma zipIdx_drop_cons {α : Type*} (l : List α) {r : ℕ} (hr : r < l.length) :
    l.zipIdx.drop r = (l[r], r) :: l.zipIdx.drop (r + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using hr)]
  simp [List.getElem_zipIdx]

lemma zipIdx_take_succ {α : Type*} (l : List α) {r : ℕ} (hr : r < l.length) :
    l.zipIdx.take (r + 1) = l.zipIdx.take r ++ [(l[r], r)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hr)]
  simp [List.getElem_zipIdx]

lemma cdesc_split (l : List (Coord k ℓ)) {r : ℕ} (hr : r < l.length) :
    l.flatMap cdesc = (l.take r).flatMap cdesc ++
      ((l[r].1 : ℕ) :: blockDescription l[r].2 ++ (l.drop (r + 1)).flatMap cdesc) := by
  have h : l.flatMap cdesc = (l.take r).flatMap cdesc ++ (l.drop r).flatMap cdesc := by
    rw [← List.flatMap_append, List.take_append_drop]
  rw [h, List.drop_eq_getElem_cons hr, List.flatMap_cons]
  simp [cdesc]

/-! ## Answers are well formed -/

lemma aOff_le (hE : I.schemas ≠ []) {v : Fin I.numLocations} {c' : Coord k ℓ}
    (hc : c' ∈ I.domain v) (s : ℕ) : aOff (ansRec I v c' s) ≤ 2 * H I := by
  have hm := le_of_mem_locRecs I hE ((mem_locRecs I).mpr ⟨v, c', hc, rfl⟩)
  have h1 := hm (locOff I v + (coordList (I.domain v)).idxOf c' * labsN I v) (by simp [locRecC])
  rw [off_eq I hc] at h1
  simpa [aOff, ansRec] using h1

lemma ansRec_ok {w : ℕ} {v : Fin I.numLocations} {c' : Coord k ℓ} (s : ℕ) (hs : s < 2 ^ w)
    (ho : aOff (ansRec I v c' s) < 2 ^ w) (hw : 2 ≤ w) : AnsOK w (ansRec I v c' s) := by
  have h4 : (4 : ℕ) ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
  refine ⟨_, _, _, _, rfl, labsN_cases I v, ?_, ?_⟩
  · have := ZMod.val_lt (initSeed I v c'); omega
  · have := ZMod.val_lt (initSeed I v c')
    have := labsN_cases I v
    intro x hx
    simp only [ansRec, List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [aOff, ansRec, List.getD_cons_succ, List.getD_cons_zero] at ho
    rcases hx with rfl | rfl | rfl | rfl <;> omega

/-! ## Section bounds -/

lemma sec_bounds (e : Fin I.schemas.length) :
    schBase I e + (cL I e).length * colW I e + 4 * nEnt I e + sumSize I e + 2 * nEnt I e ≤
      locBase I ∧ sumSize I e = 2 * tnN (Matrix.isTern (sch I e)) * (cL I e).length ∧
      colW I e = 2 + 4 * tnN (Matrix.isTern (sch I e)) ∧
      sumBase I e = schBase I e + (cL I e).length * colW I e + 4 * nEnt I e ∧
      trackBase I e = sumBase I e + sumSize I e ∧ coefBase I e = trackBase I e + 2 * nEnt I e := by
  have h1 := schBase_add_le I e
  rw [schSize_eq] at h1
  refine ⟨by unfold hubSize at h1; simp only [cL]; omega, ?_, ?_,
    by simp [sumBase, hubSize, cL]; omega, rfl, rfl⟩
  · unfold sumSize tnN; split_ifs <;> simp
  · unfold colW tnN; split_ifs <;> omega

end Lax119563Proofs.Compiler

end Compiler_P4SchL1b

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchL1c` -/

section Compiler_P4SchL1c

/-!
# Pass `P4`, schema part: the column loop of section 1, the step (`p4S1_step`)
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The fixed data of the section-1 loop of schema `e`. -/
def L1Fix (w : ℕ) (x : List Bool) (ε : ZMod 2) (e : Fin I.schemas.length) (restx : List Bool)
    (s0 : NSt CR CQ) : Prop :=
  x.drop s0.pos = encodeNats ((cL I e).flatMap cdesc) ++ restx ∧
  s0.env rL = ℓ ∧ s0.env rKk = k ∧ s0.env r4BR = blkRows (cL I e) ∧
  s0.env r4Tn = tnN (Matrix.isTern (sch I e)) ∧ s0.env rLB = locBase I ∧ s0.env r4Eps = ε.val ∧
  s0.env r4D = (cL I e).length ∧ s0.stk qOrsF = orsL (cL I e) ∧ s0.stk qOrsB = [] ∧
  s0.pos ≤ x.length

/-- The numeric bounds of the section-1 loop. -/
def L1Bnd (w : ℕ) (e : Fin I.schemas.length) (s0 : NSt CR CQ) : Prop :=
  16 * (H I + (ordL I).length + 1) ≤ 2 ^ w ∧ k * (ℓ + 1) ≤ H I ∧
  (cL I e).length ≤ H I ∧ ansBase I e + 3 * (cL I e).length ≤ 3 * H I ∧
  s0.env r4M + 3 * (ordL I).length + 16 < 2 ^ w

set_option maxHeartbeats 16000000 in
lemma p4S1_step {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (hk : 2 ≤ k) (hE : I.schemas ≠ [])
    (ε : ZMod 2) (e : Fin I.schemas.length) (R : List ℕ) (restx : List Bool) (s0 : NSt CR CQ)
    (hF : L1Fix I w x ε e restx s0) (hB : L1Bnd I w e s0)
    (hMe : ((cL I e).zipIdx.flatMap fun q => colE1 I ε e q.1 q.2).length ≤ 3 * (ordL I).length)
    (r : ℕ) (hr : r < (cL I e).length) (s : NSt CR CQ) (hI : L1Inv I w ε e R s0 r s) :
    ∃ s', Good x w p4C1 s s' (200 * ((encodeNats (cdesc (cL I e)[r])).length + ℓ +
        (k + 2) * ((rowsL (cL I e)[r]).length + 1) + 10) * Ex.nodeCost w) ∧
      L1Inv I w ε e R s0 (r + 1) s' := by
  obtain ⟨hx, e0L, e0k, e0BR, e0T, e0LB, e0E, e0D, h0F, h0B, h0p⟩ := hF
  obtain ⟨hW, hkl, hcs, hAs, hM⟩ := hB
  obtain ⟨hEM, hRk, hA, hA2, hso, eK, eD, eP, eH, eSP, eTP, hV, hbd, hpos, hout, hfr⟩ := hI
  have hcD : (cL I e)[r] ∈ (cL I e) := List.getElem_mem hr
  have hce : (cL I e)[r] ∈ dom I e := mem_coordList.mp hcD
  set T := tnN (Matrix.isTern (sch I e)) with hT
  have hT1 : T ≤ 1 := by simp only [hT, tnN]; split_ifs <;> omega
  have hLB := locBase_le_length I
  obtain ⟨hsec, hsum, hcolW, hsumB, htrkB, hcofB⟩ := sec_bounds I e
  have hentB := entB_le I e (r + 1)
  have hentS := entB_succ I e hr
  have hst := length_stepsC_rowsL (cL I e)[r]
  have hrow := rowsL_pos hk (cL I e)[r]
  have hrs : r * colW I e ≤ (cL I e).length * colW I e := Nat.mul_le_mul_right _ hr.le
  have hrs1 : (r + 1) * colW I e ≤ (cL I e).length * colW I e := Nat.mul_le_mul_right _ hr
  have hk1 : k ≤ H I := by nlinarith
  have hl1 : ℓ ≤ H I := by nlinarith
  -- fixed registers
  have fL : s.env rL = ℓ := by rw [hfr _ (by decide), e0L]
  have fk : s.env rKk = k := by rw [hfr _ (by decide), e0k]
  have fBR : s.env r4BR = blkRows (cL I e) := by rw [hfr _ (by decide), e0BR]
  have fT : s.env r4Tn = T := by rw [hfr _ (by decide), e0T]
  have fLB : s.env rLB = locBase I := by rw [hfr _ (by decide), e0LB]
  have fE : s.env r4Eps = ε.val := by rw [hfr _ (by decide), e0E]
  have hεv := ZMod.val_lt ε
  -- input
  have hxs : x.drop s.pos = encodeNats (((cL I e)[r].1 : ℕ) :: blockDescription (cL I e)[r].2) ++
      (encodeNats (((cL I e).drop (r + 1)).flatMap cdesc) ++ restx) := by
    rw [hpos, drop_add, hx, cdesc_split (cL I e) hr, encodeNats_append, List.append_assoc,
      List.drop_left, encodeNats_append, List.append_assoc]
  -- answers
  have hAc : s.stk qAns = ans1 T (aU I e (cL I e)[r] (ansBase I e + 3 * r))
      (aV I e (cL I e)[r] (ansBase I e + 3 * r + 1)) (aW I e (cL I e)[r] (sW I e r)) ++
      ((((cL I e).zipIdx.drop (r + 1)).flatMap (a1C I e)) ++ R) := by
    rw [hA, zipIdx_drop_cons (cL I e) hr, List.flatMap_cons, List.append_assoc]; rfl
  have hsq : ∀ j, j ≤ 2 → ansBase I e + 3 * r + j < 2 ^ w := fun j hj => by omega
  have hsW : sW I e r < 2 ^ w := by unfold sW; split_ifs <;> omega
  have hoU : aOff (aU I e (cL I e)[r] (ansBase I e + 3 * r)) ≤ 2 * H I :=
    aOff_le I hE (memU I hce) (ansBase I e + 3 * r)
  have hoV : aOff (aV I e (cL I e)[r] (ansBase I e + 3 * r + 1)) ≤ 2 * H I :=
    aOff_le I hE (memV I hce) (ansBase I e + 3 * r + 1)
  have hoW : aOff (aW I e (cL I e)[r] (sW I e r)) ≤ 2 * H I :=
    aOff_le I hE (memEnd I hce) (sW I e r)
  have hoU' := aOff_le I hE (memU I hce) (ansBase I e + 3 * r)
  have hoV' := aOff_le I hE (memV I hce) (ansBase I e + 3 * r + 1)
  have hoW' := aOff_le I hE (memEnd I hce) (sW I e r)
  have hposx : s.pos ≤ x.length := by
    have h1 := congrArg List.length hx
    rw [List.length_drop, List.length_append] at h1
    have h2 : (encodeNats (((cL I e).take r).flatMap cdesc)).length ≤
        (encodeNats ((cL I e).flatMap cdesc)).length := by
      conv_rhs => rw [← List.take_append_drop r (cL I e)]
      rw [List.flatMap_append, encodeNats_append, List.length_append]; omega
    omega
  -- the column
  have hc1 : ((cL I e)[r].1 : ℕ) < k := (cL I e)[r].1.2
  have hbd' : (Nat.bits ((cL I e)[r].1 : ℕ)).length < w := bits_lt_of_le (H := H I) (by omega) (by omega)
  have hbsl : (blockDescription (cL I e)[r].2).length = ℓ := length_blockDescription' _
  have hBR := blkRows_le (cL I e)
  have hDle : distR I e r ≤ r := by
    unfold distR; split_ifs
    · omega
    · have h1 := dChg_le k (((cL I e).take r).map fun c0 => (c0.1 : ℕ))
      have h2 : (((cL I e).take r).map fun c0 => (c0.1 : ℕ)).length ≤ r := by simp
      omega
  have hpre : (((cL I e).zipIdx.take r).flatMap fun q => colE1 I ε e q.1 q.2).length ≤
      ((cL I e).zipIdx.flatMap fun q => colE1 I ε e q.1 q.2).length :=
    ((List.take_sublist _ _).flatMap _).length_le
  -- previous block
  have hPw : s.env r4Prev < 2 ^ w := hbd.1 _
  -- the codes
  have hdist : dist1 r (distR I e r) (s.env r4Prev) ((cL I e)[r].1 : ℕ) =
      dChg k (((cL I e).take (r + 1)).map fun c0 => (c0.1 : ℕ)) - 1 :=
    dist1_eq (cL I e) hr (s.env r4Prev) (fun h0 => eP (by omega) h0)
  have hcodes : codesC k (blkRows (cL I e)) (dist1 r (distR I e r) (s.env r4Prev)
      ((cL I e)[r].1 : ℕ)) ((cL I e)[r].1 : ℕ) (orsL (cL I e)) (blockDescription (cL I e)[r].2) =
      codesL I e (cL I e)[r] := by
    rw [hdist]; exact codesC_eq I hk e hr
  have hn : (codesC k (blkRows (cL I e)) (dist1 r (distR I e r) (s.env r4Prev) ((cL I e)[r].1 : ℕ)) ((cL I e)[r].1 : ℕ)
      (orsL (cL I e)) (blockDescription (cL I e)[r].2)).length = (rowsL (cL I e)[r]).length := by
    rw [hcodes, length_codesL]
  obtain ⟨s', g, hEM1, hRk1, hA1, hA21, hso1, eD1, eP1, eTP1, eH1, eSP1, eK1, hV1, hbd1, hp1, ho1,
      hfr1⟩ := p4C1_good (x := x) hw s (i := ((cL I e)[r].1 : ℕ)) (k := k) (BR := blkRows (cL I e)) (K := r)
    (D := distR I e r) (P := s.env r4Prev) (H := schBase I e + r * colW I e)
    (SP := sumBase I e + 2 * r) (TP := trackBase I e + 2 * entB I e r) (T := T) (LB := locBase I)
    (blockDescription (cL I e)[r].2) (orsL (cL I e)) _ (aU I e (cL I e)[r] (ansBase I e + 3 * r))
    (aV I e (cL I e)[r] (ansBase I e + 3 * r + 1)) (aW I e (cL I e)[r] (sW I e r)) _ hxs hbd'
    (blockDescription_le _) (orsL_le _) (by rw [length_orsL, hbsl])
    (by rw [fL, hbsl]) (by rw [hso _ (by decide) (by decide) (by decide) (by decide), h0F])
    (by rw [hso _ (by decide) (by decide) (by decide) (by decide), h0B]) hAc
    (fun _ => ansRec_ok I _ (hsq 0 (by omega)) (by omega) hw)
    (fun _ => ansRec_ok I _ (hsq 1 (by omega)) (by omega) hw)
    (ansRec_ok I _ hsW (by omega) hw)
    fk fBR eK eD rfl eH eSP eTP fT hT1 fLB (by rw [fE]; omega) hV hbd hposx hk hc1
    (2 ^ w - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by rw [hsumB]; omega)
    (by rw [hn, htrkB, hsumB, ← hst]; omega) (by rw [hbsl]; omega)
    (fun _ => by omega) (fun _ => by omega) (by omega)
    (by have := hEM.2; omega)
  have hidx : (cL I e).idxOf (cL I e)[r] = r := (nodup_coordList (dom I e)).idxOf_getElem _ _
  have hLT : trackBase I e + 2 * entB I e r + 2 * ((k + 1) *
      (codesC k (blkRows (cL I e)) (dist1 r (distR I e r) (s.env r4Prev) ((cL I e)[r].1 : ℕ)) ((cL I e)[r].1 : ℕ)
        (orsL (cL I e)) (blockDescription (cL I e)[r].2)).length - 1) =
      trackBase I e + 2 * (entBefore I e (cL I e)[r] + (stepsC (cL I e)[r]).length - 1) := by
    rw [hn, entBefore_get I e hr, hst]
    have : 1 ≤ (k + 1) * (rowsL (cL I e)[r]).length := by nlinarith
    omega
  have hpos' : (encodeNats (((cL I e).take (r + 1)).flatMap cdesc)).length =
      (encodeNats (((cL I e).take r).flatMap cdesc)).length +
        (encodeNats (((cL I e)[r].1 : ℕ) :: blockDescription (cL I e)[r].2)).length := by
    rw [List.take_add_one, List.getElem?_eq_getElem hr, Option.toList_some, List.flatMap_append,
      List.flatMap_singleton, encodeNats_append, List.length_append]; rfl
  refine ⟨s', g.mono ?_, ?_, ?_, ?_, ?_, ?_, eK1, ?_, ?_, ?_, ?_, ?_, hV1, hbd1, ?_, ?_, ?_⟩
  · rw [hn, hbsl]; simp only [cdesc]; exact le_rfl
  · rw [zipIdx_take_succ (cL I e) hr, List.flatMap_append, List.flatMap_singleton]
    refine hEM.trans ?_
    rw [colE1_eq I hk ε e hce r hidx (ansBase I e + 3 * r) (ansBase I e + 3 * r + 1) (sW I e r),
      ← hLT, ← fE]
    exact hEM1
  · rw [hRk1, hRk, hcodes, List.take_add_one, List.getElem?_eq_getElem hr]
    simp only [Option.toList_some, List.flatMap_append, List.flatMap_singleton,
      List.reverse_append, List.append_assoc]
  · exact hA1
  · rw [hA21, hA2, zipIdx_take_succ (cL I e) hr, List.flatMap_append, List.flatMap_singleton]
    simp [a1C, hT]
  · intro q h1 h2 h3 h4; rw [hso1 q h1 h2 h3 h4, hso q h1 h2 h3 h4]
  · rw [eD1, hdist]; simp [distR]
  · intro _ _; rw [eP1]; simp
  · rw [eH1, hcolW]; ring
  · rw [eSP1]; ring
  · rw [eTP1, hn, entB_succ I e hr, hst]; ring
  · rw [hp1, hpos, hpos']; ring
  · rw [ho1, hout]
  · intro reg hreg; rw [hfr1 reg hreg, hfr reg hreg]

end Lax119563Proofs.Compiler

end Compiler_P4SchL1c

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchL1d` -/

section Compiler_P4SchL1d

/-!
# Pass `P4`, schema part: the column loop of section 1 (`p4S1_good`)
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

lemma col1_cost (N E S ℓ k n : ℕ) (hl : ℓ + 1 ≤ E) (hS : S = (k + 1) * n) (hn : 1 ≤ n) :
    200 * (E + ℓ + (k + 2) * (n + 1) + 10) * N ≤ 800 * N * (E + 2 * S) + 2000 * N := by
  subst hS
  have h1 : (k + 2) * (n + 1) ≤ 4 * ((k + 1) * n) := by nlinarith
  have h2 : 200 * (E + ℓ + (k + 2) * (n + 1) + 10) ≤ 800 * (E + 2 * ((k + 1) * n)) + 2000 := by
    omega
  calc 200 * (E + ℓ + (k + 2) * (n + 1) + 10) * N
      ≤ (800 * (E + 2 * ((k + 1) * n)) + 2000) * N := Nat.mul_le_mul_right _ h2
    _ = 800 * N * (E + 2 * ((k + 1) * n)) + 2000 * N := by ring

set_option maxHeartbeats 8000000 in
/-- The column loop of section 1, in terms of the invariant. -/
lemma p4S1_loop {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (hk : 2 ≤ k) (hE : I.schemas ≠ [])
    (ε : ZMod 2) (e : Fin I.schemas.length) (R : List ℕ) (restx : List Bool) (s0 : NSt CR CQ)
    (hF : L1Fix I w x ε e restx s0) (hB : L1Bnd I w e s0)
    (hMe : ((cL I e).zipIdx.flatMap fun q => colE1 I ε e q.1 q.2).length ≤ 3 * (ordL I).length)
    (hI0 : L1Inv I w ε e R s0 0 s0) :
    ∃ s', Good x w p4S1 s0 s' (800 * Ex.nodeCost w *
        ((encodeNats ((cL I e).flatMap cdesc)).length + 2 * nEnt I e) +
        (cL I e).length * (2000 * Ex.nodeCost w + condCost w (.lt (rv r4K) (rv r4D))) +
        condCost w (.lt (rv r4K) (rv r4D))) ∧
      L1Inv I w ε e R s0 (cL I e).length s' := by
  have hD : s0.env r4D = (cL I e).length := hF.2.2.2.2.2.2.2.1
  obtain ⟨P1, hP1⟩ : ∃ P1, P1 = s0.pos + (encodeNats ((cL I e).flatMap cdesc)).length := ⟨_, rfl⟩
  obtain ⟨T1, hT1⟩ : ∃ T1, T1 = trackBase I e + 2 * nEnt I e := ⟨_, rfl⟩
  obtain ⟨s', g, ⟨r, hr, hI⟩, hc⟩ := Good.loop_var (x := x) (w := w)
    (e := .lt (rv r4K) (rv r4D)) (body := p4C1)
    (fun s => ∃ r, r ≤ (cL I e).length ∧ L1Inv I w ε e R s0 r s)
    (fun s => (cL I e).length - s.env r4K) (fun s => (P1 - s.pos) + (T1 - s.env r4TP))
    (800 * Ex.nodeCost w) (2000 * Ex.nodeCost w)
    (by
      rintro s ⟨r, hr, hI⟩
      have eK := hI.2.2.2.2.2.1
      have eD : s.env r4D = (cL I e).length := by
        rw [hI.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by decide), hD]
      have hbd := hI.2.2.2.2.2.2.2.2.2.2.2.2.1
      refine ⟨⟨by simp only [Ex.Fits]; exact hbd.1 _, by simp only [Ex.Fits]; exact hbd.1 _⟩,
        fun hc => ?_⟩
      have hr' : r < (cL I e).length := by
        by_contra h; apply hc; simp only [Ex.eval, eK, eD]; rw [if_neg h]
      obtain ⟨s', g, hI'⟩ := p4S1_step I hw hk hE ε e R restx s0 hF hB hMe r hr' s hI
      have eK' := hI'.2.2.2.2.2.1
      have eTP := hI.2.2.2.2.2.2.2.2.2.2.1
      have eTP' := hI'.2.2.2.2.2.2.2.2.2.2.1
      have ep := hI.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have ep' := hI'.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hst := length_stepsC_rowsL (cL I e)[r]
      have hrow := rowsL_pos hk (cL I e)[r]
      have hsucc := entB_succ I e hr'
      have hle := entB_le I e (r + 1)
      have hlen : (encodeNats (((cL I e).take (r + 1)).flatMap cdesc)).length =
          (encodeNats (((cL I e).take r).flatMap cdesc)).length +
            (encodeNats (cdesc (cL I e)[r])).length := by
        rw [List.take_add_one, List.getElem?_eq_getElem hr', Option.toList_some,
          List.flatMap_append, List.flatMap_singleton, encodeNats_append, List.length_append]
      have hall : (encodeNats (((cL I e).take (r + 1)).flatMap cdesc)).length ≤
          (encodeNats ((cL I e).flatMap cdesc)).length := by
        conv_rhs => rw [← List.take_append_drop (r + 1) (cL I e)]
        rw [List.flatMap_append, encodeNats_append, List.length_append]; omega
      have hl := length_le_encodeNats (cdesc (cL I e)[r])
      rw [length_cdesc] at hl
      have hΔ : (P1 - s.pos + (T1 - s.env r4TP)) - (P1 - s'.pos + (T1 - s'.env r4TP)) =
          (encodeNats (cdesc (cL I e)[r])).length + 2 * (stepsC (cL I e)[r]).length := by
        rw [eTP, eTP', ep, ep', hP1, hT1]; omega
      refine ⟨s', g.mono ?_, ⟨r + 1, hr', hI'⟩, by rw [eK, eK']; omega, by
        rw [eTP, eTP', ep, ep', hP1, hT1]; omega⟩
      rw [hΔ]
      exact col1_cost _ _ _ _ _ _ hl hst hrow)
    s0 ⟨0, by omega, hI0⟩
  have eK := hI.2.2.2.2.2.1
  have eD : s'.env r4D = (cL I e).length := by
    rw [hI.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by decide), hD]
  have hr' : r = (cL I e).length := by
    by_contra h; simp only [Ex.eval, eK, eD] at hc; rw [if_pos (by omega)] at hc
    exact one_ne_zero hc
  subst hr'
  refine ⟨s', g.mono (le_of_eq ?_), hI⟩
  have eK0 : s0.env r4K = 0 := hI0.2.2.2.2.2.1
  have eTP0 : s0.env r4TP = trackBase I e + 2 * entB I e 0 := hI0.2.2.2.2.2.2.2.2.2.2.1
  have hφ : P1 - s0.pos + (T1 - s0.env r4TP) =
      (encodeNats ((cL I e).flatMap cdesc)).length + 2 * nEnt I e := by
    rw [eTP0, hP1, hT1]; simp only [entB, List.take_zero, List.map_nil, List.sum_nil]; omega
  rw [hφ, eK0, Nat.sub_zero]

lemma p4S1_cond (w : ℕ) : condCost w (.lt (rv r4K) (rv r4D)) ≤ 4 * Ex.nodeCost w := by
  have h1 := CStm.nodeCost_ge w
  have h2 := CStm.unitCost_ge w
  simp only [condCost, Ex.size]
  omega

lemma p4S1_costN (N E n m c : ℕ) (hc : c ≤ 4 * N) :
    800 * N * (E + 2 * n) + m * (2000 * N + c) + c ≤ 2100 * (E + n + m + 1) * N := by
  have h1 : m * (2000 * N + c) ≤ m * (2004 * N) := Nat.mul_le_mul_left _ (by omega)
  have h2 : 800 * N * (E + 2 * n) + m * (2004 * N) + 4 * N ≤ 2100 * (E + n + m + 1) * N := by
    nlinarith
  omega

lemma entB_all_L1d (e : Fin I.schemas.length) : entB I e (cL I e).length = nEnt I e := by
  simp [entB, nEnt]

lemma L1Inv_zero {w : ℕ} (ε : ZMod 2) (e : Fin I.schemas.length) (R : List ℕ) (s0 : NSt CR CQ)
    (eK : s0.env r4K = 0) (eDi : s0.env r4Dist = 0) (eH : s0.env r4H = schBase I e)
    (eSP : s0.env r4SP = sumBase I e) (eTP : s0.env r4TP = trackBase I e)
    (hV : s0.env r4V < 2 ^ w) (hbd : s0.Bdd w)
    (hA : s0.stk qAns = (cL I e).zipIdx.flatMap (a1C I e) ++ R) :
    L1Inv I w ε e R s0 0 s0 := by
  refine ⟨⟨by simp [pairsRev], by simp⟩, by simp, by simpa using hA, by simp, fun _ _ _ _ _ => rfl,
    eK, by rw [eDi]; simp [distR], fun _ h => absurd h (lt_irrefl 0), by rw [eH]; simp,
    by rw [eSP]; simp, by rw [eTP]; simp [entB], hV, hbd, by simp [encodeNats], rfl,
    fun _ _ => rfl⟩

set_option maxHeartbeats 4000000 in
/-- **The column loop of section 1** (`p4S1`) over the columns `cL I e` of schema `e`: it pushes
the junction and link edges of all columns (`colE1`, the first part of `schE_eq`), the rank codes
of every column (`codesL`, each list terminated by `0`), moves the section-1 answers
(`a1C`, the first part of `ansE_flatten`) from `qAns` to `qA2`, reads the column descriptions,
and advances the hub/sum/track bases. -/
lemma p4S1_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (hk : 2 ≤ k) (hE : I.schemas ≠ [])
    (ε : ZMod 2) (e : Fin I.schemas.length) (R : List ℕ) (restx : List Bool) (s0 : NSt CR CQ)
    (hF : L1Fix I w x ε e restx s0) (hB : L1Bnd I w e s0)
    (hMe : ((cL I e).zipIdx.flatMap fun q => colE1 I ε e q.1 q.2).length ≤ 3 * (ordL I).length)
    (eK : s0.env r4K = 0) (eDi : s0.env r4Dist = 0) (eH : s0.env r4H = schBase I e)
    (eSP : s0.env r4SP = sumBase I e) (eTP : s0.env r4TP = trackBase I e)
    (hV : s0.env r4V < 2 ^ w) (hbd : s0.Bdd w)
    (hA : s0.stk qAns = (cL I e).zipIdx.flatMap (a1C I e) ++ R) :
    ∃ s', Good x w p4S1 s0 s' (2100 * ((encodeNats ((cL I e).flatMap cdesc)).length +
        nEnt I e + (cL I e).length + 1) * Ex.nodeCost w) ∧
      EM s0 s' ((cL I e).zipIdx.flatMap fun q => colE1 I ε e q.1 q.2) ∧
      s'.stk qRk = ((cL I e).flatMap fun c => codesL I e c ++ [0]).reverse ++ s0.stk qRk ∧
      s'.stk qAns = R ∧
      s'.stk qA2 = ((cL I e).zipIdx.flatMap (a1C I e)).reverse ++ s0.stk qA2 ∧
      (∀ q, q ≠ q4E → q ≠ qRk → q ≠ qAns → q ≠ qA2 → s'.stk q = s0.stk q) ∧
      s'.env r4K = (cL I e).length ∧ s'.env r4Dist = distR I e (cL I e).length ∧
      s'.env r4H = schBase I e + (cL I e).length * colW I e ∧
      s'.env r4SP = sumBase I e + 2 * (cL I e).length ∧
      s'.env r4TP = trackBase I e + 2 * nEnt I e ∧ s'.env r4V < 2 ^ w ∧ s'.Bdd w ∧
      s'.pos = s0.pos + (encodeNats ((cL I e).flatMap cdesc)).length ∧ s'.out = s0.out ∧
      ∀ reg, reg ∉ c1W → s'.env reg = s0.env reg := by
  obtain ⟨s', g, hEM, hRk, hA', hA2, hso, eK', eD', -, eH', eSP', eTP', hV', hbd', hp', ho', hfr'⟩ :=
    p4S1_loop I hw hk hE ε e R restx s0 hF hB hMe
      (L1Inv_zero I ε e R s0 eK eDi eH eSP eTP hV hbd hA)
  have hz : (cL I e).zipIdx.take (cL I e).length = (cL I e).zipIdx :=
    List.take_of_length_le (by simp)
  have hz' : (cL I e).zipIdx.drop (cL I e).length = [] :=
    List.drop_eq_nil_of_le (by simp)
  have ht : (cL I e).take (cL I e).length = cL I e := List.take_length
  rw [hz] at hEM hA2
  rw [hz'] at hA'
  rw [ht] at hRk hp'
  rw [entB_all_L1d] at eTP'
  refine ⟨s', g.mono (p4S1_costN _ _ _ _ _ (p4S1_cond w)), hEM, hRk, by simpa using hA', hA2, hso,
    eK', eD', eH', eSP', eTP', hV', hbd', hp', ho', hfr'⟩

end Lax119563Proofs.Compiler

end Compiler_P4SchL1d

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchQ` -/

section Compiler_P4SchQ

/-!
# Pass `P4`, schema part: the `q` loop of section 2 and dropping a column's codes

* `p4QB`: one `q`: the rank loop, then the codes are restored on `qRkF` (`p4QB_good`);
* `p4Qs`: the loop over `q ≤ k` (`p4Qs_good`, edges `col2E`);
* `p4Drop`: drop the codes of a column (`p4Drop_good`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-- One `q`. -/
def p4QB : CStm CR CQ :=
  .seq p4Rks (.seq (.push qRkF (.const 0)) (.seq (moveAllS qOrsB qRkF rc8 r4Dist)
    (.seq (.set rc2 (.add (rv rc2) (rv r4R2))) (.set rc1 (.add (rv rc1) (.const 1))))))

/-- The loop over `q ≤ k`. -/
def p4Qs : CStm CR CQ := .loop (.lt (rv rc1) (.add (rv rKk) (.const 1))) p4QB

/-- The update edges of a column (numbers): for `q ≤ k` the entries `q n + p`. -/
def col2E (T Hc TPc SP QB R2 LB oU mU k : ℕ) (cs : List ℕ) : List (ℕ × ℕ) :=
  (List.range (k + 1)).flatMap fun q =>
    rksE T (q * cs.length) Hc TPc SP (QB + q * R2) LB oU mU cs

/-- The registers written by the `q` loop. -/
def qW : List (Fin CR) := rc1 :: rc2 :: rc5 :: entW

/-- The state of the `q` loop after `q` rounds. -/
def qInv (w : ℕ) (x : List Bool) (T Hc TPc SP QB R2 LB oU mU : ℕ) (cs rest : List ℕ)
    (s0 : NSt CR CQ) (q : ℕ) (s : NSt CR CQ) : Prop :=
  EE s0 s ((List.range q).flatMap fun q' =>
      rksE T (q' * cs.length) Hc TPc SP (QB + q' * R2) LB oU mU cs) ∧
    s.stk qRkF = cs ++ 0 :: rest ∧ s.stk qOrsB = [] ∧
    (∀ q', q' ≠ q4E → q' ≠ qRkF → q' ≠ qOrsB → s.stk q' = s0.stk q') ∧
    s.env rc1 = q ∧ s.env rc2 = QB + q * R2 ∧
    s.env rc6 = (if q * cs.length = 0 then 1 else 0) ∧
    (0 < q * cs.length → s.env rc7 = TPc + 2 * (q * cs.length - 1)) ∧
    s.env r4H = Hc + 4 * (q * cs.length) ∧ s.env r4TP = TPc + 2 * (q * cs.length) ∧
    s.env r4V < 2 ^ w ∧ s.Bdd w ∧ s.pos ≤ x.length ∧
    ∀ r, r ∉ qW → s.env r = s0.env r

lemma length_qE_le (T Hc TPc SP QB R2 LB oU mU : ℕ) (cs : List ℕ) (q : ℕ) :
    ((List.range q).flatMap fun q' =>
      rksE T (q' * cs.length) Hc TPc SP (QB + q' * R2) LB oU mU cs).length ≤
      12 * cs.length * q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, List.flatMap_singleton]
    have := length_rksE_le T (q * cs.length) Hc TPc SP (QB + q * R2) LB oU mU cs
    rw [Nat.mul_succ]; omega

set_option maxHeartbeats 4000000 in
lemma p4QB_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s0 : NSt CR CQ) (k : ℕ)
    {T Hc TPc SP QB R2 LB oU mU : ℕ} (cs rest : List ℕ) (hn : 1 ≤ cs.length)
    (hcs : ∀ X ∈ cs, 1 ≤ X)
    (eT : s0.env r4Tn = T) (hT : T ≤ 1) (eSP : s0.env r4SP = SP) (eR2 : s0.env r4R2 = R2)
    (eLB : s0.env rLB = LB) (eo : s0.env rc3 = oU) (em : s0.env rc4 = mU) (hm2 : mU ≤ 2)
    (hH : Hc + 4 * ((k + 1) * cs.length) + 4 < 2 ^ w)
    (hTP : TPc + 2 * ((k + 1) * cs.length) + 2 < 2 ^ w)
    (hSP : SP + 2 < 2 ^ w) (hQR : ∀ X ∈ cs, QB + (k + 1) * R2 + X + 2 < 2 ^ w)
    (hU : LB + oU + 2 < 2 ^ w)
    (hm : s0.env r4M + 12 * cs.length * (k + 1) + 12 < 2 ^ w)
    (q : ℕ) (hq : q < k + 1) (s : NSt CR CQ)
    (hI : qInv w x T Hc TPc SP QB R2 LB oU mU cs rest s0 q s) :
    ∃ s', Good x w p4QB s s' ((cs.length + 1) * (700 * Ex.nodeCost w)) ∧
      qInv w x T Hc TPc SP QB R2 LB oU mU cs rest s0 (q + 1) s' := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  obtain ⟨hE, hsR, hsB, hso, e1, e2, e6, e7, eH, eTP, hV, hbd, hpos, hfr⟩ := hI
  have hfr' : ∀ r, r ∉ qW → s.env r = s0.env r := hfr
  have hqn : q * cs.length + cs.length ≤ (k + 1) * cs.length := by nlinarith
  have hlq := length_qE_le T Hc TPc SP QB R2 LB oU mU cs q
  have hqk : 12 * cs.length * q + 12 * cs.length ≤ 12 * cs.length * (k + 1) := by nlinarith
  obtain ⟨s1, g1, hR⟩ := p4Rks_good (x := x) hw s (T := T) (t0 := q * cs.length) (Hc := Hc)
    (TPc := TPc) (SP := SP) (QR := QB + q * R2) (LB := LB) (oU := oU) (mU := mU) cs rest hcs
    hsR hsB (by rw [hfr' _ (by decide), eT]) hT e6 e7 (by rw [hfr' _ (by decide), eSP]) eH eTP e2
    (by rw [hfr' _ (by decide), eLB]) (by rw [hfr' _ (by decide), eo])
    (by rw [hfr' _ (by decide), em]) hm2 (by omega) (by omega) hSP
    (fun X hX => by have := hQR X hX; have : q * R2 ≤ (k + 1) * R2 := by nlinarith
                    omega) hU hV (by rw [hE.2.1]; omega)
  obtain ⟨hE1, h1R, h1B, h1o, h15, h16, h17, h1H, h1TP, h1V, h1fr⟩ := hR
  rw [List.take_length] at hE1 h1B
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
    show cs.length + 1 - cs.length = 1 by omega, List.drop_one, List.tail_cons] at h1R
  have hb1 := (g1.bdd hw hbd hpos)
  have gp := CStm.Good.push (x := x) (w := w) (st := s1) (q := qRkF) (e := .const 0)
    (by simp only [Ex.Fits]; positivity)
  set s2 := s1.setS qRkF ((Ex.const 0 : Ex CR).eval s1.env :: s1.stk qRkF)
  have hb2 := gp.bdd hw hb1.1 hb1.2
  obtain ⟨s3, g3, k3, p3, o3, f3⟩ := moveAllS_good (x := x) hw (q := qOrsB) (q' := qRkF)
    (t := rc8) (f := r4Dist) (by decide) (by decide) s2 hb2.1
  have hb3 := g3.bdd hw hb2.1 hb2.2
  have e32 : s3.env rc2 = QB + q * R2 := by
    rw [f3 _ (by decide) (by decide)]; simp only [s2, NSt.setS_env]
    rw [h1fr _ (by decide), e2]
  have e3R2 : s3.env r4R2 = R2 := by
    rw [f3 _ (by decide) (by decide)]; simp only [s2, NSt.setS_env]
    rw [h1fr _ (by decide), hfr' _ (by decide), eR2]
  have g4 := CStm.Good.set (x := x) (w := w) (st := s3) (r := rc2) (e := .add (rv rc2) (rv r4R2))
    (by simp only [Ex.Fits, rv, Ex.eval, e32, e3R2]
        have : QB + (k + 1) * R2 + 1 + 2 < 2 ^ w := by
          have := hQR _ (List.getElem_mem (show 0 < cs.length by omega))
          have := hcs _ (List.getElem_mem (show 0 < cs.length by omega))
          omega
        have h1 : (q + 1) * R2 ≤ (k + 1) * R2 := Nat.mul_le_mul_right _ (by omega)
        have h2 : (q + 1) * R2 = q * R2 + R2 := add_one_mul q R2
        omega)
  set s4 := s3.set rc2 ((Ex.add (rv rc2) (rv r4R2) : Ex CR).eval s3.env)
  have e41 : s4.env rc1 = q := by
    simp only [s4, NSt.set_env, Function.update_of_ne (show rc1 ≠ rc2 by decide)]
    rw [f3 _ (by decide) (by decide)]; simp only [s2, NSt.setS_env]
    rw [h1fr _ (by decide), e1]
  have g5 := CStm.Good.set (x := x) (w := w) (st := s4) (r := rc1) (e := .add (rv rc1) (.const 1))
    (by simp only [Ex.Fits, rv, Ex.eval, e41]
        have : q + 1 < 2 ^ w := by
          have : q + 1 ≤ q * cs.length + cs.length := by nlinarith
          omega
        omega)
  set s5 := s4.set rc1 ((Ex.add (rv rc1) (.const 1) : Ex CR).eval s4.env)
  have hb5 := g5.bdd hw (g4.bdd hw hb3.1 hb3.2).1 (g4.bdd hw hb3.1 hb3.2).2
  -- frames from s1 to s5
  have q51 : ∀ r, r ≠ rc1 → r ≠ rc2 → r ≠ rc8 → r ≠ r4Dist → s5.env r = s1.env r := by
    intro r h1 h2 h3 h4
    simp only [s5, s4, NSt.set_env, Function.update_of_ne h1, Function.update_of_ne h2]
    rw [f3 r h3 h4]; rfl
  have k5 : s5.stk = Function.update (Function.update s1.stk qOrsB []) qRkF
      ((s1.stk qOrsB).reverse ++ (0 :: s1.stk qRkF)) := by
    simp only [s5, s4, NSt.set_stk, k3, s2, NSt.setS_stk,
      Function.update_of_ne (show qOrsB ≠ qRkF by decide), Function.update_self, Ex.eval]
    funext q'
    by_cases h : q' = qRkF
    · subst h; simp +decide
    · by_cases h' : q' = qOrsB
      · subst h'; simp +decide
      · simp [Function.update_of_ne h, Function.update_of_ne h']
  refine ⟨s5, (g1.seq (gp.seq (g3.seq (g4.seq g5)))).mono ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, hb5.1, hb5.2, ?_⟩
  · simp only [Ex.size, rv]
    have hs : (s2.stk qOrsB).length = cs.length := by
      simp +decide [s2, Function.update_of_ne (show qOrsB ≠ qRkF by decide), h1B]
    rw [hs]; nlinarith
  · have ee : EE s1 s5 [] := EE.of_frame (by rw [k5]; simp [Function.update_of_ne
      (show q4E ≠ qRkF by decide), Function.update_of_ne (show q4E ≠ qOrsB by decide)])
      (q51 _ (by decide) (by decide) (by decide) (by decide)) (by
        simp only [s5, s4]; show s3.pos = _; rw [p3]; rfl) (by
        simp only [s5, s4]; show s3.out = _; rw [o3]; rfl)
    have := (hE.trans hE1).trans ee
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    simpa using this
  · rw [k5]; simp +decide [h1R, h1B]
  · rw [k5]; simp +decide
  · intro q' h1 h2 h3
    rw [k5]; simp only [Function.update_of_ne h2, Function.update_of_ne h3]
    rw [h1o q' h1 h2 h3, hso q' h1 h2 h3]
  · simp +decide [s5, Ex.eval, rv, e41]
  · simp only [s5, NSt.set_env, Function.update_of_ne (show rc2 ≠ rc1 by decide), s4,
      Function.update_self, Ex.eval, rv, e32, e3R2]; ring
  · rw [q51 _ (by decide) (by decide) (by decide) (by decide), h16]
    have : q * cs.length + cs.length ≠ 0 := by omega
    simp [this, add_mul]
  · intro _
    rw [q51 _ (by decide) (by decide) (by decide) (by decide), h17 (by omega)]
    rw [add_mul, one_mul]
  · rw [q51 _ (by decide) (by decide) (by decide) (by decide), h1H]; ring
  · rw [q51 _ (by decide) (by decide) (by decide) (by decide), h1TP]; ring
  · rw [q51 _ (by decide) (by decide) (by decide) (by decide)]; exact h1V
  · intro r hr
    simp only [qW, entW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [q51 r hr.1 hr.2.1 hr.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.2.2.2.2,
      h1fr r (by simp [entW]; tauto), hfr' r (by simp [qW, entW]; tauto)]

end Lax119563Proofs.Compiler

end Compiler_P4SchQ

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchC2` -/

section Compiler_P4SchC2

/-!
# Pass `P4`, schema part: a column of section 2

* `p4Qs_good`: the loop over `q ≤ k` (edges `col2E`);
* `p4Drop_good`: drop the rank codes of the column;
* `p4C2_good`: one column (binary schemas: the start answer `U` is popped first).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

lemma qs_cost (k M N : ℕ) (hM : 1 ≤ M) (hN : 64 ≤ N) :
    (k + 1) * (M * (700 * N) + ((1 + (1 + 1 + 1) + 1) * N + 1)) +
      ((1 + (1 + 1 + 1) + 1) * N + 1) ≤ (k + 2) * (M * (800 * N)) := by
  have h1 : N ≤ M * N := Nat.le_mul_of_pos_left N hM
  have h2 : (k + 1) * N ≤ (k + 1) * (M * N) := Nat.mul_le_mul_left _ h1
  nlinarith

set_option maxHeartbeats 4000000 in
lemma p4Qs_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s : NSt CR CQ) (k : ℕ)
    {T Hc TPc SP QB R2 LB oU mU : ℕ} (cs rest : List ℕ) (hn : 1 ≤ cs.length)
    (hcs : ∀ X ∈ cs, 1 ≤ X)
    (hR : s.stk qRkF = cs ++ 0 :: rest) (hB : s.stk qOrsB = [])
    (e1 : s.env rc1 = 0) (e2 : s.env rc2 = QB) (e6 : s.env rc6 = 1) (ek : s.env rKk = k)
    (eH : s.env r4H = Hc) (eTP : s.env r4TP = TPc)
    (eT : s.env r4Tn = T) (hT : T ≤ 1) (eSP : s.env r4SP = SP) (eR2 : s.env r4R2 = R2)
    (eLB : s.env rLB = LB) (eo : s.env rc3 = oU) (em : s.env rc4 = mU) (hm2 : mU ≤ 2)
    (hV : s.env r4V < 2 ^ w) (hbd : s.Bdd w) (hpos : s.pos ≤ x.length)
    (hk : k + 2 < 2 ^ w)
    (hH : Hc + 4 * ((k + 1) * cs.length) + 4 < 2 ^ w)
    (hTP : TPc + 2 * ((k + 1) * cs.length) + 2 < 2 ^ w)
    (hSP : SP + 2 < 2 ^ w) (hQR : ∀ X ∈ cs, QB + (k + 1) * R2 + X + 2 < 2 ^ w)
    (hU : LB + oU + 2 < 2 ^ w)
    (hm : s.env r4M + 12 * cs.length * (k + 1) + 12 < 2 ^ w) :
    ∃ s', Good x w p4Qs s s' ((k + 2) * ((cs.length + 1) * (800 * Ex.nodeCost w))) ∧
      qInv w x T Hc TPc SP QB R2 LB oU mU cs rest s (k + 1) s' := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have hI0 : qInv w x T Hc TPc SP QB R2 LB oU mU cs rest s 0 s := by
    refine ⟨by simpa using EE.refl s, hR, hB, fun _ _ _ _ => rfl, e1, by simp [e2], by simp [e6],
      fun h => by simp at h, by simp [eH], by simp [eTP], hV, hbd, hpos, fun _ _ => rfl⟩
  have hek : ∀ s', qInv w x T Hc TPc SP QB R2 LB oU mU cs rest s 0 s' ∨ True →
      True := fun _ _ => trivial
  obtain ⟨s', g, hI⟩ := CStm.Good.loop_idxC (x := x) (w := w)
    (e := .lt (rv rc1) (.add (rv rKk) (.const 1))) (body := p4QB) (k + 1)
    (qInv w x T Hc TPc SP QB R2 LB oU mU cs rest s) ((cs.length + 1) * (700 * Ex.nodeCost w))
    (by
      intro q hq s1 hs1
      have e1' := hs1.2.2.2.2.1
      have ek' : s1.env rKk = k := by rw [hs1.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by decide), ek]
      refine ⟨by simp only [Ex.Fits, rv, Ex.eval, e1', ek']; omega,
        by simp [Ex.eval, rv, e1', ek']; omega, ?_⟩
      exact p4QB_good hw s k cs rest hn hcs eT hT eSP eR2 eLB eo em hm2 hH hTP hSP hQR hU hm
        q hq s1 hs1)
    (by
      intro s1 hs1
      have e1' := hs1.2.2.2.2.1
      have ek' : s1.env rKk = k := by rw [hs1.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by decide), ek]
      exact ⟨by simp only [Ex.Fits, rv, Ex.eval, e1', ek']; omega, by simp [Ex.eval, rv, e1', ek']⟩)
    s hI0
  refine ⟨s', g.mono ?_, hI⟩
  simp only [condCost, Ex.size, rv]
  exact qs_cost k (cs.length + 1) (Ex.nodeCost w) (by omega) (by omega)

/-! ## Dropping the codes of a column -/

/-- Drop the codes of a column (up to and including the terminator). -/
def p4Drop : CStm CR CQ := .seq (.pop qRkF rc5) (.loop (rv rc5) (.pop qRkF rc5))

set_option maxHeartbeats 2000000 in
lemma p4Drop_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s : NSt CR CQ) (cs rest : List ℕ)
    (hcs : ∀ X ∈ cs, 1 ≤ X) (hcw : ∀ X ∈ cs, X < 2 ^ w) (hR : s.stk qRkF = cs ++ 0 :: rest) :
    ∃ s', Good x w p4Drop s s' ((cs.length + 1) * (10 * Ex.nodeCost w)) ∧
      s'.stk = Function.update s.stk qRkF rest ∧ s'.pos = s.pos ∧ s'.out = s.out ∧
      ∀ r, r ≠ rc5 → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have h1w : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  set L := cs ++ 0 :: rest
  let P : ℕ → NSt CR CQ → Prop := fun p s' =>
    s'.stk = Function.update s.stk qRkF (L.drop (p + 1)) ∧ s'.env rc5 = L.getD p 0 ∧
      s'.pos = s.pos ∧ s'.out = s.out ∧ ∀ r, r ≠ rc5 → s'.env r = s.env r
  have g0 := CStm.Good.pop (x := x) (w := w) (st := s) qRkF rc5
  have hP0 : P 0 ((s.setS qRkF (s.stk qRkF).tail).set rc5 ((s.stk qRkF).headD 0)) := by
    refine ⟨by simp [hR, L], ?_, rfl, rfl, fun r h => by simp [Function.update_of_ne h]⟩
    simp [hR, L]; cases cs <;> simp
  obtain ⟨s', g, hP⟩ := CStm.Good.loop_idxC (x := x) (w := w) (e := rv rc5) (body := .pop qRkF rc5)
    cs.length P (5 * Ex.nodeCost w)
    (by
      intro j hj s1 ⟨k1, v1, p1, o1, f1⟩
      have hv : L.getD j 0 = cs[j] := by
        simp only [L]; rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hj]
      rw [hv] at v1
      have := hcs _ (List.getElem_mem hj)
      have := hcw _ (List.getElem_mem hj)
      refine ⟨by simp only [rv, Ex.Fits, v1]; omega, by simp only [rv, Ex.eval, v1]; omega, ?_⟩
      have hd : L.drop (j + 1) = L.getD (j + 1) 0 :: L.drop (j + 1 + 1) := by
        rw [List.getD_eq_getElem _ _ (by simp [L]; omega)]
        exact List.drop_eq_getElem_cons (by simp [L]; omega)
      refine ⟨_, (CStm.Good.pop (x := x) (w := w) (st := s1) qRkF rc5).mono (by omega), ?_, ?_,
        p1, o1, ?_⟩
      · simp [k1, hd]
      · simp [k1, hd]
      · intro r h; simp [Function.update_of_ne h, f1 r h])
    (by
      rintro s1 ⟨-, v1, -⟩
      have : L.getD cs.length 0 = 0 := by
        simp only [L]; rw [List.getD_eq_getElem _ _ (by simp)]; simp
      rw [this] at v1
      exact ⟨by simp only [rv, Ex.Fits, v1]; omega, by simp [rv, Ex.eval, v1]⟩)
    _ hP0
  obtain ⟨k1, -, p1, o1, f1⟩ := hP
  refine ⟨s', (g0.seq g).mono ?_, ?_, p1, o1, f1⟩
  · simp only [condCost, rv, Ex.size]; nlinarith
  · rw [k1]
    congr 1
    simp only [L]
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
      show cs.length + 1 - cs.length = 1 by omega, List.drop_one, List.tail_cons]

end Lax119563Proofs.Compiler

end Compiler_P4SchC2

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchC2b` -/

section Compiler_P4SchC2b

/-!
# Pass `P4`, schema part: one column of section 2 (`p4C2_good`)
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-- The start answer of a column (binary schemas), else zeros. -/
def c2Ans : CStm CR CQ :=
  .ite (rv r4Tn) (.seq (.set rc3 (.const 0)) (.set rc4 (.const 0))) (pAns rc3 rc4)

/-- The answer hypotheses of a column of section 2: `A` the consumed answer words. -/
def AnsHyp (w : ℕ) (T eps : ℕ) (A : List ℕ) (oU mU : ℕ) : Prop :=
  (T = 1 → A = [] ∧ oU = 0 ∧ mU = 0) ∧
  (T = 0 → (∃ sq labs sd, A = [sq, oU, labs, sd] ∧ (labs = 1 ∨ labs = 2) ∧ sd ≤ 1) ∧
    (∀ v ∈ A, v < 2 ^ w) ∧ mU = ansMode eps A)

lemma AnsHyp.mU_le {w T eps : ℕ} {A : List ℕ} {oU mU : ℕ} (h : AnsHyp w T eps A oU mU)
    (hT : T ≤ 1) (he : eps ≤ 1) : mU ≤ 2 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hT with rfl | rfl
  · obtain ⟨⟨sq, labs, sd, rfl, -, hsd⟩, -, rfl⟩ := h.2 rfl
    unfold ansMode; simp only [List.getD_cons_succ, List.getD_cons_zero]
    split_ifs
    · have : eps * sd ≤ 1 * 1 := Nat.mul_le_mul he hsd
      omega
    · omega
  · obtain ⟨-, -, rfl⟩ := h.1 rfl; omega

set_option maxHeartbeats 2000000 in
lemma c2Ans_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s : NSt CR CQ) {T oU mU : ℕ}
    (A ansRest : List ℕ) (eT : s.env r4Tn = T) (hT : T ≤ 1) (hE : s.env r4Eps ≤ 1)
    (hA : s.stk qAns = A ++ ansRest) (hH : AnsHyp w T (s.env r4Eps) A oU mU) :
    ∃ s', Good x w c2Ans s s' (50 * Ex.nodeCost w) ∧ s'.env rc3 = oU ∧ s'.env rc4 = mU ∧
      s'.stk = Function.update (Function.update s.stk qAns ansRest) qA2
        (A.reverse ++ s.stk qA2) ∧ s'.pos = s.pos ∧ s'.out = s.out ∧
      ∀ r, r ∉ [rc3, rc4, rc6, rc7, rc8] → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
  have hF : (rv r4Tn : Ex CR).Fits w s.env := by simp only [rv, Ex.Fits, eT]; omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hT with rfl | rfl
  · obtain ⟨⟨sq, labs, sd, rfl, hl, hsd⟩, hb, hm⟩ := hH.2 rfl
    obtain ⟨s1, g, k1, v1, m1, -, p1, o1, f1⟩ := pAns_good (x := x) hw (o := rc3) (m := rc4)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) s hA hb hl hsd hE
    refine ⟨s1, (CStm.Good.iteF hF (by simp [rv, Ex.eval, eT]) g).mono ?_, v1, by rw [m1, hm],
      by rw [k1]; simp, p1, o1, ?_⟩
    · simp only [condCost, rv, Ex.size]; nlinarith
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      exact f1 r hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2 hr.1 hr.2.1
  · obtain ⟨rfl, rfl, rfl⟩ := hH.1 rfl
    have g1 := CStm.Good.set (x := x) (w := w) (st := s) (r := rc3) (e := .const 0)
      (by simp only [Ex.Fits]; omega)
    have g2 := CStm.Good.set (x := x) (w := w) (st := s.set rc3 ((Ex.const 0 : Ex CR).eval s.env))
      (r := rc4) (e := .const 0) (by simp only [Ex.Fits]; omega)
    refine ⟨_, (CStm.Good.iteT hF (by simp [rv, Ex.eval, eT]) (g1.seq g2)).mono ?_, ?_, ?_, ?_,
      rfl, rfl, ?_⟩
    · simp only [condCost, rv, Ex.size]; nlinarith
    · simp +decide [Ex.eval]
    · simp +decide [Ex.eval]
    · funext q
      by_cases h1 : q = qA2
      · subst h1; simp +decide
      · by_cases h2 : q = qAns
        · subst h2; simp +decide [hA]
        · simp [Function.update_of_ne h1, Function.update_of_ne h2]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [Function.update_of_ne hr.1, Function.update_of_ne hr.2.1]


/-- One column of section 2. -/
def p4C2 : CStm CR CQ :=
  .seq c2Ans (.seq (.set rc6 (.const 1)) (.seq (.set rc1 (.const 0))
    (.seq (.set rc2 (rv r4Prev)) (.seq p4Qs (.seq p4Drop
      (.seq (.set r4SP (.add (rv r4SP) (.const 2))) (.set r4K (.add (rv r4K) (.const 1)))))))))

/-- Registers written by a column of section 2. -/
def c2W : List (Fin CR) :=
  [rc1, rc2, rc3, rc4, rc5, rc6, rc7, rc8, r4TP, r4H, r4F, r4V, r4M, r4Dist, r4SP, r4K]

set_option maxHeartbeats 8000000 in
/-- **One column of section 2.** -/
lemma p4C2_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (s : NSt CR CQ) (k : ℕ)
    {T Hc TPc SP QB R2 LB K oU mU : ℕ} (cs rest A ansRest : List ℕ) (hn : 1 ≤ cs.length)
    (hcs : ∀ X ∈ cs, 1 ≤ X)
    (hR : s.stk qRkF = cs ++ 0 :: rest) (hB : s.stk qOrsB = [])
    (hA : s.stk qAns = A ++ ansRest) (hAH : AnsHyp w T (s.env r4Eps) A oU mU)
    (ek : s.env rKk = k) (eH : s.env r4H = Hc) (eTP : s.env r4TP = TPc)
    (eT : s.env r4Tn = T) (hT : T ≤ 1) (eSP : s.env r4SP = SP) (eR2 : s.env r4R2 = R2)
    (eLB : s.env rLB = LB) (eQB : s.env r4Prev = QB) (eK : s.env r4K = K)
    (hE : s.env r4Eps ≤ 1)
    (hV : s.env r4V < 2 ^ w) (hbd : s.Bdd w) (hpos : s.pos ≤ x.length)
    (hk : k + 2 < 2 ^ w) (hK : K + 2 < 2 ^ w)
    (hH : Hc + 4 * ((k + 1) * cs.length) + 4 < 2 ^ w)
    (hTP : TPc + 2 * ((k + 1) * cs.length) + 2 < 2 ^ w)
    (hSP : SP + 4 < 2 ^ w) (hQR : ∀ X ∈ cs, QB + (k + 1) * R2 + X + 2 < 2 ^ w)
    (hU : LB + oU + 2 < 2 ^ w)
    (hm : s.env r4M + 12 * cs.length * (k + 1) + 12 < 2 ^ w) :
    ∃ s', Good x w p4C2 s s' ((k + 3) * ((cs.length + 1) * (800 * Ex.nodeCost w))) ∧
      EE s s' (col2E T Hc TPc SP QB R2 LB oU mU k cs) ∧
      s'.stk qRkF = rest ∧ s'.stk qOrsB = [] ∧ s'.stk qAns = ansRest ∧
      s'.stk qA2 = A.reverse ++ s.stk qA2 ∧
      (∀ q, q ≠ q4E → q ≠ qRkF → q ≠ qOrsB → q ≠ qAns → q ≠ qA2 → s'.stk q = s.stk q) ∧
      s'.env r4H = Hc + 4 * ((k + 1) * cs.length) ∧
      s'.env r4TP = TPc + 2 * ((k + 1) * cs.length) ∧ s'.env r4SP = SP + 2 ∧
      s'.env r4K = K + 1 ∧ s'.env r4V < 2 ^ w ∧ s'.Bdd w ∧
      ∀ r, r ∉ c2W → s'.env r = s.env r := by
  have hN := CStm.nodeCost_ge w
  have hN' := CStm.unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
  have hm2 := hAH.mU_le hT hE
  obtain ⟨s1, g1, e13, e14, k1, p1, o1, f1⟩ := c2Ans_good (x := x) hw s A ansRest eT hT hE hA hAH
  have q1 : ∀ r, r ∉ [rc3, rc4, rc6, rc7, rc8] → s1.env r = s.env r := f1
  have b1 := g1.bdd hw hbd hpos
  have ga := CStm.Good.set (x := x) (w := w) (st := s1) (r := rc6) (e := .const 1)
    (by simp only [Ex.Fits]; omega)
  have gb := CStm.Good.set (x := x) (w := w) (st := s1.set rc6 1) (r := rc1) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  have gc := CStm.Good.set (x := x) (w := w) (st := (s1.set rc6 1).set rc1 0) (r := rc2)
    (e := rv r4Prev) (by
      have := hQR _ (List.getElem_mem (show 0 < cs.length by omega))
      simp +decide [Ex.Fits, rv, q1 r4Prev (by decide), eQB]; omega)
  simp only [Ex.eval] at ga gb
  have ev : (rv r4Prev : Ex CR).eval ((s1.set rc6 1).set rc1 0).env = QB := by
    simp +decide [rv, Ex.eval, q1 r4Prev (by decide), eQB]
  rw [ev] at gc
  set s2 := ((s1.set rc6 1).set rc1 0).set rc2 QB
  have b2 := (ga.seq (gb.seq gc)).bdd hw b1.1 b1.2
  have q2 : ∀ r, r ∉ [rc1, rc2, rc3, rc4, rc6, rc7, rc8] → s2.env r = s.env r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [s2, NSt.set_env, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1,
      Function.update_of_ne hr.2.2.2.2.1]
    exact q1 r (by simp; tauto)
  have k2 : s2.stk = s1.stk := rfl
  obtain ⟨s3, g3, hI⟩ := p4Qs_good (x := x) hw s2 k (T := T) (Hc := Hc) (TPc := TPc) (SP := SP)
    (QB := QB) (R2 := R2) (LB := LB) (oU := oU) (mU := mU) cs rest hn hcs
    (by rw [k2, k1]; simp +decide [hR]) (by rw [k2, k1]; simp +decide [hB])
    (by simp +decide [s2]) (by simp +decide [s2]) (by simp +decide [s2])
    (by rw [q2 _ (by decide), ek]) (by rw [q2 _ (by decide), eH]) (by rw [q2 _ (by decide), eTP])
    (by rw [q2 _ (by decide), eT]) hT (by rw [q2 _ (by decide), eSP]) (by rw [q2 _ (by decide), eR2])
    (by rw [q2 _ (by decide), eLB]) (by simp +decide [s2, e13]) (by simp +decide [s2, e14]) hm2
    (by rw [q2 _ (by decide)]; exact hV) b2.1 b2.2 hk hH hTP (by omega) hQR hU
    (by rw [q2 _ (by decide)]; exact hm)
  obtain ⟨hE3, h3R, h3B, h3o, -, -, -, -, h3H, h3TP, h3V, hb3, hp3, h3fr⟩ := hI
  have hcw : ∀ X ∈ cs, X < 2 ^ w := fun X hX => by have := hQR X hX; omega
  obtain ⟨s4, g4, k4, p4, o4, f4⟩ := p4Drop_good (x := x) hw s3 cs rest hcs hcw h3R
  have b4 := g4.bdd hw hb3 hp3
  have e4SP : s4.env r4SP = SP := by
    rw [f4 _ (by decide), h3fr _ (by decide), q2 _ (by decide), eSP]
  have g5 := CStm.Good.set (x := x) (w := w) (st := s4) (r := r4SP) (e := .add (rv r4SP) (.const 2))
    (by simp only [Ex.Fits, rv, Ex.eval, e4SP]; omega)
  have ev5 : (Ex.add (rv r4SP) (.const 2) : Ex CR).eval s4.env = SP + 2 := by
    simp [Ex.eval, rv, e4SP]
  rw [ev5] at g5
  have e5K : (s4.set r4SP (SP + 2)).env r4K = K := by
    simp +decide only [NSt.set_env]
    rw [Function.update_of_ne (by decide), f4 _ (by decide), h3fr _ (by decide), q2 _ (by decide), eK]
  have g6 := CStm.Good.set (x := x) (w := w) (st := s4.set r4SP (SP + 2)) (r := r4K)
    (e := .add (rv r4K) (.const 1)) (by simp only [Ex.Fits, rv, Ex.eval, e5K]; omega)
  have ev6 : (Ex.add (rv r4K) (.const 1) : Ex CR).eval (s4.set r4SP (SP + 2)).env = K + 1 := by
    simp only [Ex.eval, rv, e5K]
  rw [ev6] at g6
  set s6 := (s4.set r4SP (SP + 2)).set r4K (K + 1)
  have b6 := (g5.seq g6).bdd hw b4.1 b4.2
  have q63 : ∀ r, r ≠ r4K → r ≠ r4SP → r ≠ rc5 → s6.env r = s3.env r := by
    intro r h1 h2 h3
    simp only [s6, NSt.set_env, Function.update_of_ne h1, Function.update_of_ne h2]
    exact f4 r h3
  have k6 : s6.stk = Function.update s3.stk qRkF rest := k4
  refine ⟨s6, (g1.seq (ga.seq (gb.seq (gc.seq (g3.seq (g4.seq (g5.seq g6))))))).mono ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, b6.1, ?_⟩
  · have hc : (cs.length + 1) * (800 * Ex.nodeCost w) ≥ 800 * Ex.nodeCost w := by nlinarith
    simp only [Ex.size, rv]
    nlinarith
  · have e01 : EE s s2 [] := EE.of_frame (by rw [k2, k1]; simp +decide)
      (by rw [q2 _ (by decide)]) (by simp [s2, p1]) (by simp [s2, o1])
    have e36 : EE s3 s6 [] := EE.of_frame (by rw [k6]; simp +decide)
      (by rw [q63 _ (by decide) (by decide) (by decide)]) (by simp [s6, p4]) (by simp [s6, o4])
    have := (e01.trans hE3).trans e36
    simpa [col2E] using this
  · rw [k6]; simp
  · rw [k6]; simp +decide [h3B]
  · rw [k6, Function.update_of_ne (by decide), h3o _ (by decide) (by decide) (by decide), k2, k1]
    simp +decide
  · rw [k6, Function.update_of_ne (by decide), h3o _ (by decide) (by decide) (by decide), k2, k1]
    simp +decide
  · intro q h1 h2 h3 h4 h5
    rw [k6, Function.update_of_ne h2, h3o q h1 h2 h3, k2, k1, Function.update_of_ne h5,
      Function.update_of_ne h4]
  · rw [q63 _ (by decide) (by decide) (by decide), h3H]
  · rw [q63 _ (by decide) (by decide) (by decide), h3TP]
  · simp +decide [s6]
  · simp +decide [s6]
  · rw [q63 _ (by decide) (by decide) (by decide)]; exact h3V
  · intro r hr
    simp only [c2W, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [q63 r hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hr.2.2.2.2.1,
      h3fr r (by simp [qW, entW]; tauto)]
    exact q2 r (by simp; tauto)

end Lax119563Proofs.Compiler

end Compiler_P4SchC2b

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchGlue2` -/

section Compiler_P4SchGlue2

/-!
# Pass `P4`, schema part: list glue for section 2 and the answers

* `col2_eq`: the update edges of a column are `col2E` of its rank codes;
* `ansE_flatten`: the answer words of a schema, per column for section 1 (`a1C`) and
  section 2 (`a2C`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

lemma rcode_div (ρ : ℕ) : rcode ρ / 2 = ρ := by unfold rcode; omega

lemma length_rkL (e : Fin I.schemas.length) (c : Coord k ℓ) :
    (rkL I e c).length = (rowsL c).length := by simp [rkL]

/-- **The update edges of a column, in numbers** (`oU, mU`: the start answer of a binary
schema; arbitrary for a ternary one). -/
lemma col2_eq (ε : ZMod 2) (e : Fin I.schemas.length) {c : Coord k ℓ} (hc : c ∈ dom I e)
    (r : ℕ) (hr : (coordList (dom I e)).idxOf c = r) (hb : ℕ) (oU mU : ℕ)
    (hU : isTern (sch I e) = false → ∀ a, a < 2 →
      slotPos I ε (startCls I e c) ((a : ℕ) : ZMod 2) = cposN (locBase I) oU mU a) :
    (stepsC c).zipIdx.flatMap (fun q => hubE I ε (.upd e q.1 c) bits2
        (hb + 4 * (entBefore I e c + q.2))) =
      col2E (tnN (isTern (sch I e))) (hb + 4 * entBefore I e c)
        (trackBase I e + 2 * entBefore I e c) (sumBase I e + 2 * r) (coefBase I e)
        (2 * (rowsR I e).length) (locBase I) oU mU k ((rkL I e c).map rcode) := by
  rw [colE2_eq I ε hc hb, col2E]
  refine List.flatMap_congr fun q _ => ?_
  rw [rksE, List.length_map, length_rkL, List.zipIdx_map, List.flatMap_map]
  refine List.flatMap_congr fun x _ => ?_
  simp only [Prod.map, id, rcode_div]
  unfold updEnt entE
  have hci : coefBase I e + 2 * (q * (rowsR I e).length + x.1) =
      coefBase I e + q * (2 * (rowsR I e).length) + 2 * x.1 := by ring
  rw [hci]
  set t := q * (rowsL c).length + x.2 with ht_def
  have e1 : hb + 4 * (entBefore I e c + t) = hb + 4 * entBefore I e c + 4 * t := by ring
  have e2 : trackBase I e + 2 * (entBefore I e c + t) =
      trackBase I e + 2 * entBefore I e c + 2 * t := by ring
  rw [e1, e2]
  by_cases ht : isTern (sch I e) = true
  · have h1 : ¬ (t = 0 ∧ isTern (sch I e) = false) := by simp [ht]
    have h2 : ¬ (t = 0 ∧ tnN (isTern (sch I e)) = 0) := by simp [ht, tnN]
    rw [if_neg h1, if_neg h2, updL]
    unfold prevBase
    split_ifs with h0
    · rw [hr]
    · have e3 : trackBase I e + 2 * (entBefore I e c + t - 1) =
          trackBase I e + 2 * entBefore I e c + 2 * (t - 1) := by omega
      rw [e3]
  · have ht' : isTern (sch I e) = false := by simpa using ht
    by_cases h0 : t = 0
    · rw [if_pos ⟨h0, ht'⟩, if_pos ⟨h0, by simp [ht', tnN]⟩, updFL]
      refine List.flatMap_congr fun i hi => ?_
      have hi2 : i / 2 < 2 := by have := List.mem_range.mp hi; omega
      rw [hU ht' _ hi2, h0]
      simp
    · rw [if_neg (fun h => h0 h.1), if_neg (fun h => h0 h.1), updL, if_neg h0]
      unfold prevBase
      rw [if_neg h0]
      have e3 : trackBase I e + 2 * (entBefore I e c + t - 1) =
          trackBase I e + 2 * entBefore I e c + 2 * (t - 1) := by omega
      rw [e3]

end Lax119563Proofs.Compiler

end Compiler_P4SchGlue2

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchL2` -/

section Compiler_P4SchL2

/-!
# Pass `P4`, schema part: the column loop of section 2, invariant and facts

* `p4S2`: the loop; `colE2`: the update edges of a column (as in `schE_eq`);
* `L2Fix`/`L2Bnd`: the fixed data and the numeric bounds; `L2Inv`: the state after `r` columns;
* `ans2_hyp`: the start answer of a column satisfies `AnsHyp` and gives the slots of `col2_eq`.
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The column loop of section 2. -/
def p4S2 : CStm CR CQ := .loop (.lt (rv r4K) (rv r4D)) p4C2

/-- The update hub base of schema `e`. -/
noncomputable def updBase (e : Fin I.schemas.length) : ℕ :=
  schBase I e + (cL I e).length * colW I e

/-- The update edges of column `c` (the summand of the second part of `schE_eq`). -/
noncomputable def colE2 (ε : ZMod 2) (e : Fin I.schemas.length) (c : Coord k ℓ) :
    List (ℕ × ℕ) :=
  (stepsC c).zipIdx.flatMap fun q => hubE I ε (.upd e q.1 c) bits2
    (updBase I e + 4 * (entBefore I e c + q.2))

/-- The fixed data of the section-2 loop of schema `e`. -/
def L2Fix (x : List Bool) (ε : ZMod 2) (e : Fin I.schemas.length) (s0 : NSt CR CQ) : Prop :=
  s0.env rKk = k ∧ s0.env r4Tn = tnN (Matrix.isTern (sch I e)) ∧ s0.env rLB = locBase I ∧
  s0.env r4Eps = ε.val ∧ s0.env r4D = (cL I e).length ∧
  s0.env r4R2 = 2 * (rowsR I e).length ∧ s0.env r4Prev = coefBase I e ∧ s0.pos ≤ x.length

/-- The numeric bounds of the section-2 loop. -/
def L2Bnd (w : ℕ) (ε : ZMod 2) (e : Fin I.schemas.length) (s0 : NSt CR CQ) : Prop :=
  16 * (H I + (ordL I).length + 1) ≤ 2 ^ w ∧ k * (ℓ + 1) ≤ H I ∧
  (cL I e).length ≤ H I ∧ ansBase I e + 3 * (cL I e).length ≤ 3 * H I ∧
  s0.env r4M + ((cL I e).flatMap (colE2 I ε e)).length + 12 * nEnt I e + 12 < 2 ^ w

/-- The state of the column loop of section 2 after `r` columns. -/
def L2Inv (w : ℕ) (ε : ZMod 2) (e : Fin I.schemas.length) (R Q : List ℕ)
    (s0 : NSt CR CQ) (r : ℕ) (s : NSt CR CQ) : Prop :=
  EE s0 s (((cL I e).take r).flatMap (colE2 I ε e)) ∧
  s.stk qRkF = ((cL I e).drop r).flatMap (fun c => codesL I e c ++ [0]) ++ Q ∧
  s.stk qOrsB = [] ∧
  s.stk qAns = ((cL I e).zipIdx.drop r).flatMap (a2C I e) ++ R ∧
  s.stk qA2 = (((cL I e).zipIdx.take r).flatMap (a2C I e)).reverse ++ s0.stk qA2 ∧
  (∀ q, q ≠ q4E → q ≠ qRkF → q ≠ qOrsB → q ≠ qAns → q ≠ qA2 → s.stk q = s0.stk q) ∧
  s.env r4K = r ∧ s.env r4H = updBase I e + 4 * entB I e r ∧
  s.env r4TP = trackBase I e + 2 * entB I e r ∧ s.env r4SP = sumBase I e + 2 * r ∧
  s.Bdd w ∧ ∀ reg, reg ∉ c2W → s.env reg = s0.env reg

/-! ## Facts -/

lemma entB_all (e : Fin I.schemas.length) : entB I e (cL I e).length = nEnt I e := by
  simp [entB, nEnt, cL]

lemma length_coefSteps' (e : Fin I.schemas.length) :
    (coefSteps I e).length = (k + 1) * (rowsR I e).length := by
  rw [coefSteps_eq, List.length_flatMap]
  simp [List.map_const', List.sum_replicate]

lemma coef_bound (e : Fin I.schemas.length) :
    coefBase I e + 2 * ((k + 1) * (rowsR I e).length) ≤ locBase I := by
  have h1 := schBase_add_le I e
  rw [schSize_eq, length_coefSteps'] at h1
  unfold coefBase trackBase sumBase
  omega

lemma length_rowsR_le (e : Fin I.schemas.length) : (rowsR I e).length ≤ k - 1 + ℓ := by
  unfold rowsR
  exact (List.length_filter_le _ _).trans (by simp)

lemma codesL_lt (e : Fin I.schemas.length) {c : Coord k ℓ} (hc : c ∈ dom I e) {X : ℕ}
    (hX : X ∈ codesL I e c) : X < 2 * (rowsR I e).length := by
  simp only [codesL, rkL, List.map_map, List.mem_map, Function.comp] at hX
  obtain ⟨j, hj, rfl⟩ := hX
  have := List.idxOf_lt_length_of_mem (rowsL_sub I hc hj)
  unfold rcode; omega

/-- The start answer of a column of section 2. -/
lemma ans2_hyp {w : ℕ} (hw : 2 ≤ w) (ε : ZMod 2) (e : Fin I.schemas.length) {c : Coord k ℓ}
    (hc : c ∈ dom I e) (r : ℕ) (hs : ansBase I e + (cL I e).length + r < 2 ^ w)
    (hH : 2 * H I < 2 ^ w) :
    ∃ oU mU, AnsHyp w (tnN (Matrix.isTern (sch I e))) ε.val (a2C I e (c, r)) oU mU ∧
      (Matrix.isTern (sch I e) = false → ∀ a, a < 2 →
        slotPos I ε (startCls I e c) ((a : ℕ) : ZMod 2) = cposN (locBase I) oU mU a) ∧
      oU ≤ 2 * H I := by
  have hE : I.schemas ≠ [] := by
    intro h; have := e.2; simp [h] at this
  cases ht : Matrix.isTern (sch I e)
  · set A := aU I e c (ansBase I e + (coordList (dom I e)).length + r) with hA
    have hA' : a2C I e (c, r) = A := by simp [a2C, ht, hA]
    have hoff := aOff_le I hE (memU I hc) (ansBase I e + (coordList (dom I e)).length + r)
    have hok := ansRec_ok I (v := Matrix.locU (sch I e))
      (c' := (Matrix.permU (sch I e)).apply c) (ansBase I e + (coordList (dom I e)).length + r)
      hs (by omega) hw
    obtain ⟨sq, off, labs, sd, hAe, hl, hsd, hb⟩ := hok
    have hAe' : A = [sq, off, labs, sd] := hAe
    have hoA : aOff A = off := by rw [hAe']; rfl
    refine ⟨aOff A, ansMode ε.val A, ⟨fun h => by simp [tnN] at h, fun _ => ⟨?_, ?_, ?_⟩⟩,
      fun _ a ha => ?_, hoff⟩
    · rw [hA', hoA]; exact ⟨sq, labs, sd, hAe', hl, hsd⟩
    · rw [hA']; exact hb
    · rw [hA']
    · simp only [startCls, ht, Bool.false_eq_true, if_false]
      exact slot_ans I ε (memU I hc) ha _
  · refine ⟨0, 0, ⟨fun _ => ⟨by simp [a2C, ht], rfl, rfl⟩, fun h => by simp [tnN] at h⟩,
      fun h => by simp at h, by omega⟩

end Lax119563Proofs.Compiler

end Compiler_P4SchL2

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchL2b` -/

section Compiler_P4SchL2b

/-!
# Pass `P4`, schema part: the column loop of section 2, the step (`p4S2_step`)
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

lemma take_succ_getElem {α : Type*} (l : List α) {r : ℕ} (hr : r < l.length) :
    l.take (r + 1) = l.take r ++ [l[r]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hr]; rfl

set_option maxHeartbeats 16000000 in
/-- **One step of the column loop of section 2.** -/
lemma p4S2_step {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (hk : 2 ≤ k) (ε : ZMod 2)
    (e : Fin I.schemas.length) (R Q : List ℕ) (s0 : NSt CR CQ)
    (hF : L2Fix I x ε e s0) (hB : L2Bnd I w ε e s0)
    (r : ℕ) (hr : r < (cL I e).length) (s : NSt CR CQ) (hI : L2Inv I w ε e R Q s0 r s) :
    ∃ s', Good x w p4C2 s s' ((k + 3) * (((rowsL (cL I e)[r]).length + 1) *
        (800 * Ex.nodeCost w))) ∧ L2Inv I w ε e R Q s0 (r + 1) s' := by
  obtain ⟨e0k, e0T, e0LB, e0E, e0D, e0R2, e0P, h0p⟩ := hF
  obtain ⟨hW, hkl, hcs, hAs, hM⟩ := hB
  obtain ⟨hEE, hR, hOB, hA, hA2, hso, eK, eH, eTP, eSP, hbd, hfr⟩ := hI
  have hentS := entB_succ I e hr
  have hEb := entBefore_get I e hr
  have hidx : (coordList (dom I e)).idxOf (cL I e)[r] = r :=
    (nodup_coordList (dom I e)).idxOf_getElem _ _
  have hRc : s.stk qRkF = codesL I e (cL I e)[r] ++ 0 ::
      (((cL I e).drop (r + 1)).flatMap (fun c => codesL I e c ++ [0]) ++ Q) := by
    rw [hR, List.drop_eq_getElem_cons hr, List.flatMap_cons]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hAc : s.stk qAns = a2C I e ((cL I e)[r], r) ++
      ((((cL I e).zipIdx.drop (r + 1)).flatMap (a2C I e)) ++ R) := by
    rw [hA, zipIdx_drop_cons _ hr, List.flatMap_cons, List.append_assoc]
  have hEt := take_succ_getElem (cL I e) hr
  have hAt := zipIdx_take_succ (cL I e) hr
  have hcD : (cL I e)[r] ∈ cL I e := List.getElem_mem hr
  have hce : (cL I e)[r] ∈ dom I e := mem_coordList.mp hcD
  generalize (cL I e)[r] = c at hentS hEb hidx hRc hAc hEt hAt hcD hce ⊢
  have hT1 : tnN (Matrix.isTern (sch I e)) ≤ 1 := by unfold tnN; split_ifs <;> omega
  have hLB := locBase_le_length I
  obtain ⟨hsec, hsum, hcolW, hsumB, htrkB, hcofB⟩ := sec_bounds I e
  have hcoef := coef_bound I e
  have hrowsR := length_rowsR_le I e
  have hentB := entB_le I e (r + 1)
  have hst := length_stepsC_rowsL c
  have hrow := rowsL_pos hk c
  have hlen := length_codesL I e c
  have hk1 : k ≤ H I := by nlinarith
  have hl1 : ℓ ≤ H I := by nlinarith
  have fk : s.env rKk = k := by rw [hfr _ (by decide), e0k]
  have fT : s.env r4Tn = tnN (Matrix.isTern (sch I e)) := by rw [hfr _ (by decide), e0T]
  have fLB : s.env rLB = locBase I := by rw [hfr _ (by decide), e0LB]
  have fE : s.env r4Eps = ε.val := by rw [hfr _ (by decide), e0E]
  have fR2 : s.env r4R2 = 2 * (rowsR I e).length := by rw [hfr _ (by decide), e0R2]
  have fP : s.env r4Prev = coefBase I e := by rw [hfr _ (by decide), e0P]
  have hεv := ZMod.val_lt ε
  obtain ⟨oU, mU, hAH, hU, hoU⟩ := ans2_hyp I hw ε e hce r (by omega) (by omega)
  have hpre : (((cL I e).take r).flatMap (colE2 I ε e)).length ≤
      ((cL I e).flatMap (colE2 I ε e)).length := ((List.take_sublist _ _).flatMap _).length_le
  have hM' : s.env r4M = s0.env r4M + (((cL I e).take r).flatMap (colE2 I ε e)).length :=
    hEE.2.1
  have hS1 : (k + 1) * (codesL I e c).length = (stepsC c).length := by rw [hlen, hst]
  have hQ2 : ∀ X ∈ codesL I e c,
      coefBase I e + (k + 1) * (2 * (rowsR I e).length) + X + 2 < 2 ^ w := by
    intro X hX
    have := codesL_lt I e hce hX
    have h2 : (k + 1) * (2 * (rowsR I e).length) = 2 * ((k + 1) * (rowsR I e).length) := by ring
    omega
  have hm12 : 12 * (codesL I e c).length * (k + 1) = 12 * (stepsC c).length := by
    rw [← hS1]; ring
  obtain ⟨s', g, hE1, hR1, hB1, hA1, hA21, hso1, eH1, eTP1, eSP1, eK1, -, hbd1, hfr1⟩ :=
    p4C2_good (x := x) hw s k (T := tnN (Matrix.isTern (sch I e)))
      (Hc := updBase I e + 4 * entB I e r) (TPc := trackBase I e + 2 * entB I e r)
      (SP := sumBase I e + 2 * r) (QB := coefBase I e) (R2 := 2 * (rowsR I e).length)
      (LB := locBase I) (K := r) (oU := oU) (mU := mU) (codesL I e c) _ _ _ (by omega)
      (codesL_pos I hk e c) hRc hOB hAc (by rw [fE]; exact hAH) fk eH eTP fT hT1 eSP fR2 fLB
      fP eK (by rw [fE]; omega) (hbd.1 _) hbd (by rw [hEE.2.2.1]; exact h0p) (by omega)
      (by omega) (by rw [hS1]; unfold updBase; omega) (by rw [hS1]; omega) (by omega) hQ2
      (by omega) (by rw [hm12, hM']; omega)
  refine ⟨s', g.mono (by rw [hlen]), ?_, ?_, hB1, ?_, ?_, ?_, eK1, ?_, ?_, ?_, hbd1, ?_⟩
  · rw [hEt, List.flatMap_append, List.flatMap_singleton]
    refine hEE.trans ?_
    have h2 := col2_eq I ε e hce r hidx (updBase I e) oU mU hU
    rw [colE2, h2, hEb]
    exact hE1
  · rw [hR1]
  · rw [hA1]
  · rw [hA21, hA2, hAt, List.flatMap_append, List.flatMap_singleton]; simp
  · intro q h1 h2 h3 h4 h5; rw [hso1 q h1 h2 h3 h4 h5, hso q h1 h2 h3 h4 h5]
  · rw [eH1, hS1, hentS]; ring
  · rw [eTP1, hS1, hentS]; ring
  · rw [eSP1]; ring
  · intro reg hreg; rw [hfr1 reg hreg, hfr reg hreg]

end Lax119563Proofs.Compiler

end Compiler_P4SchL2b

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchL2c` -/

section Compiler_P4SchL2c

/-!
# Pass `P4`, schema part: the column loop of section 2 (`p4S2_good`)
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The edges of a schema: section 1 per column, then the update edges `colE2` per column. -/
lemma schE_eq2 (ε : ZMod 2) (e : Fin I.schemas.length) : schE I ε e =
    (cL I e).zipIdx.flatMap (fun q => colE1 I ε e q.1 q.2) ++ (cL I e).flatMap (colE2 I ε e) := by
  rw [schE_eq]; rfl

lemma col2_cost (N k n : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n) :
    (k + 3) * ((n + 1) * (800 * N)) ≤ 1600 * N * (2 * ((k + 1) * n)) + 0 := by
  have h : (k + 3) * (n + 1) ≤ 4 * ((k + 1) * n) := by nlinarith
  calc (k + 3) * ((n + 1) * (800 * N)) = (k + 3) * (n + 1) * (800 * N) := by ring
    _ ≤ 4 * ((k + 1) * n) * (800 * N) := Nat.mul_le_mul_right _ h
    _ = 1600 * N * (2 * ((k + 1) * n)) + 0 := by ring

set_option maxHeartbeats 8000000 in
/-- **The column loop of section 2** of schema `e`: pushes the update edges of all columns,
consumes the rank codes (each column terminated by `0`) from `qRkF` and the start answers
(`a2C`, binary schemas) from `qAns`. -/
theorem p4S2_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (hk : 2 ≤ k) (ε : ZMod 2)
    (e : Fin I.schemas.length) (R Q : List ℕ) (s0 : NSt CR CQ)
    (hF : L2Fix I x ε e s0) (hB : L2Bnd I w ε e s0)
    (h0R : s0.stk qRkF = (cL I e).flatMap (fun c => codesL I e c ++ [0]) ++ Q)
    (h0B : s0.stk qOrsB = [])
    (h0A : s0.stk qAns = (cL I e).zipIdx.flatMap (a2C I e) ++ R)
    (e0K : s0.env r4K = 0) (e0H : s0.env r4H = updBase I e)
    (e0TP : s0.env r4TP = trackBase I e) (e0SP : s0.env r4SP = sumBase I e) (hbd : s0.Bdd w) :
    ∃ s', Good x w p4S2 s0 s' (3200 * Ex.nodeCost w * nEnt I e +
        (cL I e).length * condCost w (.lt (rv r4K) (rv r4D)) +
        condCost w (.lt (rv r4K) (rv r4D))) ∧
      EE s0 s' ((cL I e).flatMap (colE2 I ε e)) ∧
      s'.stk qRkF = Q ∧ s'.stk qOrsB = [] ∧ s'.stk qAns = R ∧
      s'.stk qA2 = ((cL I e).zipIdx.flatMap (a2C I e)).reverse ++ s0.stk qA2 ∧
      (∀ q, q ≠ q4E → q ≠ qRkF → q ≠ qOrsB → q ≠ qAns → q ≠ qA2 → s'.stk q = s0.stk q) ∧
      s'.env r4K = (cL I e).length ∧ s'.env r4H = updBase I e + 4 * nEnt I e ∧
      s'.env r4TP = coefBase I e ∧ s'.env r4SP = sumBase I e + 2 * (cL I e).length ∧
      s'.Bdd w ∧ ∀ reg, reg ∉ c2W → s'.env reg = s0.env reg := by
  have hD := hF.2.2.2.2.1
  have hI0 : L2Inv I w ε e R Q s0 0 s0 := by
    refine ⟨by simpa using EE.refl s0, by simpa using h0R, h0B, by simpa using h0A, by simp,
      fun _ _ _ _ _ _ => rfl, e0K, by simp [entB, e0H], by simp [entB, e0TP], by simp [e0SP],
      hbd, fun _ _ => rfl⟩
  have hcB : coefBase I e = trackBase I e + 2 * nEnt I e := rfl
  obtain ⟨s', g, ⟨r, hr, hI⟩, hc⟩ := Good.loop_var (x := x) (w := w)
    (e := .lt (rv r4K) (rv r4D)) (body := p4C2)
    (fun s => ∃ r, r ≤ (cL I e).length ∧ L2Inv I w ε e R Q s0 r s)
    (fun s => (cL I e).length - s.env r4K) (fun s => coefBase I e - s.env r4TP)
    (1600 * Ex.nodeCost w) 0
    (by
      rintro s ⟨r, hr, hI⟩
      have eK := hI.2.2.2.2.2.2.1
      have eD : s.env r4D = (cL I e).length := by
        rw [hI.2.2.2.2.2.2.2.2.2.2.2 _ (by decide), hD]
      have hbd := hI.2.2.2.2.2.2.2.2.2.2.1
      refine ⟨⟨hbd.1 _, hbd.1 _⟩, fun hc => ?_⟩
      have hr' : r < (cL I e).length := by
        simp only [Ex.eval, eK, eD] at hc; split_ifs at hc with h <;> omega
      obtain ⟨s', g, hI'⟩ := p4S2_step I hw hk ε e R Q s0 hF hB r hr' s hI
      have eK' := hI'.2.2.2.2.2.2.1
      have eTP := hI.2.2.2.2.2.2.2.2.1
      have eTP' := hI'.2.2.2.2.2.2.2.2.1
      have hst := length_stepsC_rowsL (cL I e)[r]
      have hrow := rowsL_pos hk (cL I e)[r]
      have hsucc := entB_succ I e hr'
      have hle := entB_le I e (r + 1)
      refine ⟨s', g.mono ?_, ⟨r + 1, hr', hI'⟩, by rw [eK, eK']; omega, by omega⟩
      have hΔ : (coefBase I e - s.env r4TP) - (coefBase I e - s'.env r4TP) =
          2 * ((k + 1) * (rowsL (cL I e)[r]).length) := by
        rw [eTP, eTP', hcB]; omega
      rw [hΔ]
      exact col2_cost _ _ _ hk hrow)
    s0 ⟨0, by omega, hI0⟩
  have eK := hI.2.2.2.2.2.2.1
  have eD : s'.env r4D = (cL I e).length := by
    rw [hI.2.2.2.2.2.2.2.2.2.2.2 _ (by decide), hD]
  have hr' : r = (cL I e).length := by
    simp only [Ex.eval, eK, eD] at hc; split_ifs at hc with h <;> omega
  subst hr'
  obtain ⟨hEE, hR, hOB, hA, hA2, hso, eK1, eH, eTP, eSP, hbd1, hfr⟩ := hI
  have hall := entB_all I e
  refine ⟨s', g.mono ?_, by simpa using hEE, by simpa using hR, hOB, by
      rw [hA, List.drop_of_length_le (by simp)]; simp,
    by rw [hA2, List.take_of_length_le (by simp)], hso, eK1, by rw [eH, hall], by rw [eTP, hall, hcB], eSP, hbd1, hfr⟩
  rw [e0K, e0TP, hcB]
  have : trackBase I e + 2 * nEnt I e - trackBase I e = 2 * nEnt I e := by omega
  rw [this, Nat.sub_zero]
  have h2 : 1600 * Ex.nodeCost w * (2 * nEnt I e) = 3200 * Ex.nodeCost w * nEnt I e := by ring
  rw [h2, Nat.zero_add]

end Lax119563Proofs.Compiler

end Compiler_P4SchL2c

/-! ### Formerly `Lax119563Proofs.Compiler.P4SzRec` -/

section Compiler_P4SzRec

/-!
# Pass `P4` (program): moving a schema record back onto `qSch`

`p4SRec` moves the record `R ++ [nE, nC]` (`|R| = rL1`) from the top of `qT` back onto
`qSch` (reversing it, so `qSch` is rebuilt), keeping `nE`, `nC` in `rNe`, `rNc`
(**`p4SRec_good`**).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-- Move one schema record from `qT` to `qSch`, keeping its last two words. -/
def p4SRec : CStm CR CQ :=
  .seq (moveN qT qSch rL1 rI rT) (.seq (.pop qT rNe) (.seq (.push qSch (rv rNe))
    (.seq (.pop qT rNc) (.push qSch (rv rNc)))))

lemma p4SRec_good {x : List Bool} {w : ℕ} (s : NSt CR CQ) (R R' : List ℕ) (b c : ℕ)
    (hT : s.stk qT = R ++ b :: c :: R') (hL : s.env rL1 = R.length)
    (hRw : ∀ v ∈ R, v < 2 ^ w) (hb : b < 2 ^ w) (hc : c < 2 ^ w) (hn : R.length + 1 < 2 ^ w) :
    ∃ s', Good x w p4SRec s s' ((R.length + 5) * (12 * Ex.nodeCost w)) ∧
      s'.stk = Function.update (Function.update s.stk qT R') qSch
        (c :: b :: R.reverse ++ s.stk qSch) ∧
      s'.env rNe = b ∧ s'.env rNc = c ∧ s'.pos = s.pos ∧ s'.out = s.out ∧
      ∀ r, r ≠ rI → r ≠ rT → r ≠ rNe → r ≠ rNc → s'.env r = s.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  obtain ⟨s1, r1, h1s, h1f⟩ := moveN_good (x := x) (w := w) (src := qT) (dst := qSch)
    (cnt := rL1) (i := rI) (t := rT) (by decide) (by decide) (by decide) (by decide) s hL
    (by rw [hT]; simp) hn (by rw [hT, List.take_left]; exact hRw)
  have e1T : s1.stk qT = b :: c :: R' := by
    rw [h1s, movedStk, Function.update_of_ne (by decide), Function.update_self, hT,
      List.drop_left]
  have e1S : s1.stk qSch = R.reverse ++ s.stk qSch := by
    rw [h1s, movedStk, Function.update_self, hT, List.take_left]
  have r2 := Good.pop (x := x) (w := w) (st := s1) qT rNe
  set s2 := (s1.setS qT (s1.stk qT).tail).set rNe ((s1.stk qT).headD 0)
  have e2N : s2.env rNe = b := by simp (config := { decide := true }) [s2, e1T]
  have r3 := Good.push (x := x) (w := w) (st := s2) (q := qSch) (e := rv rNe)
    (by simp only [Ex.Fits, rv, e2N]; exact hb)
  set s3 := s2.setS qSch ((rv rNe : Ex CR).eval s2.env :: s2.stk qSch)
  have r4 := Good.pop (x := x) (w := w) (st := s3) qT rNc
  set s4 := (s3.setS qT (s3.stk qT).tail).set rNc ((s3.stk qT).headD 0)
  have e3T : s3.stk qT = c :: R' := by
    simp (config := { decide := true }) [s3, s2, e1T, Function.update_of_ne (show qT ≠ qSch by decide)]
  have e4C : s4.env rNc = c := by simp (config := { decide := true }) [s4, e3T]
  have r5 := Good.push (x := x) (w := w) (st := s4) (q := qSch) (e := rv rNc)
    (by simp only [Ex.Fits, rv, e4C]; exact hc)
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [rv, Ex.size]; nlinarith
  · simp only [NSt.setS_stk, NSt.set_stk]
    funext q
    by_cases hq : q = qSch
    · subst hq
      simp (config := { decide := true }) [s4, s3, s2, e1S, e2N, Function.update_of_ne (show qSch ≠ qT by decide), Ex.eval,
        rv, e4C, e1T]
    · by_cases hq' : q = qT
      · subst hq'
        simp (config := { decide := true }) [s4, e3T, Function.update_of_ne hq]
      · simp only [Function.update_of_ne hq, Function.update_of_ne hq']
        simp (config := { decide := true }) [s4, s3, s2, Function.update_of_ne hq, Function.update_of_ne hq', h1s, movedStk]
  · simp (config := { decide := true }) [s4, s3, Function.update_of_ne (show rNe ≠ rNc by decide), e2N]
  · simp (config := { decide := true }) [e4C]
  · simp (config := { decide := true }) [s4, s3, s2]; exact h1f.1
  · simp (config := { decide := true }) [s4, s3, s2]; exact h1f.2.1
  · intro r h1 h2 h3 h4
    simp (config := { decide := true }) [s4, s3, s2, Function.update_of_ne h3, Function.update_of_ne h4]
    exact h1f.2.2 r (by simp (config := { decide := true }) [h1, h2])

end Lax119563Proofs.Compiler

end Compiler_P4SzRec

/-! ### Formerly `Lax119563Proofs.Compiler.P4SzRead` -/

section Compiler_P4SzRead

/-!
# Pass `P4` (program): reading one schema description for its sizes

`p4SRead` reads the arity (`rA`) and `|D|` (`rD`) of the schema at the cursor and skips the
rest of its description (locations, coordinates, `arity · k (ℓ + 1)` permutation words)
(**`p4SRead_good`**).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- Read arity and `|D|` of the schema at the cursor, skip the rest of its description. -/
def p4SRead : CStm CR CQ :=
  .seq (rdNumS rA rP rT) (.seq (skipNumsS rA rI rT) (.seq (rdNumS rD rP rT)
    (.seq (skipBlocksS rD rL1 rK rI rT) (.seq (mulS rC rA rKk rI) (.seq (mulS rC2 rC rL1 rI)
      (skipNumsS rC2 rI rT))))))

lemma flatMap_eq_map_flatten {α β : Type*} (l : List α) (f : α → List β) :
    l.flatMap f = (l.map f).flatten := List.flatMap_def

lemma p4SRead_arith {N U la llo ld lf lp a d k ℓ np : ℕ} (hU : U ≤ N) (ha : a ≤ llo)
    (hd : d ≤ lf) (hk : k ≤ lp) (hl : ℓ + 1 ≤ lp) (hp : np ≤ lp) :
    (la + 1) * (20 * N) + ((llo + a + 1) * (20 * N) + ((ld + 1) * (20 * N) +
      ((lf + d + 1) * (50 * N) + ((k + 1) * (12 * N) + ((ℓ + 1 + 1) * (12 * N) +
        (lp + np + 1) * (20 * N)))))) ≤
      150 * N * (la + llo + ld + lf + lp) + 200 * N := by
  nlinarith

lemma p4SRead_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hk : 1 ≤ k)
    (s : NSt CR CQ) {j : ℕ} (hj : j < I.schemas.length) (hpos : s.pos = schAt I j)
    (hL1 : s.env rL1 = ℓ + 1) (hK : s.env rKk = k) :
    ∃ s', Good (encodeSystem I) w p4SRead s s'
        (150 * Ex.nodeCost w * (encodeNats (schD I ⟨j, hj⟩)).length + 200 * Ex.nodeCost w) ∧
      s'.pos = s.pos + (encodeNats (schD I ⟨j, hj⟩)).length ∧ s'.stk = s.stk ∧
      s'.out = s.out ∧ s'.env rA = arity (sch I ⟨j, hj⟩) ∧
      s'.env rD = (coordList (dom I ⟨j, hj⟩)).length := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hH2 : 2 * (H I + 1) ≤ 2 ^ w := by omega
  set e : Fin I.schemas.length := ⟨j, hj⟩
  set sc := sch I e
  set a := arity sc
  set locs := schLocs sc
  set D := coordList (dom I e)
  set d := D.length
  set cs := D.map cdesc
  set perms := (schPerms sc).flatMap permDescription
  set rest := encodeNats (schsSuf I (j + 1))
  have hcsM : ∀ b ∈ cs, b.length = ℓ + 1 := by
    intro b hb; obtain ⟨c, -, rfl⟩ := List.mem_map.mp hb; exact length_cdesc c
  have hcsl : cs.length = d := by simp (config := { decide := true }) [cs, d]
  have hfl : cs.flatten.length = d * (ℓ + 1) := by
    rw [List.length_flatten, List.map_congr_left hcsM, sum_map_const, hcsl]
  have hD : schD I e = a :: locs ++ (d :: cs.flatten) ++ perms := by
    rw [schD, schemaDescription_eq', ← flatMap_eq_map_flatten]; rfl
  have hx : (encodeSystem I).drop s.pos = encodeNat a ++ (encodeNats locs ++ (encodeNat d ++
      (encodeNats cs.flatten ++ (encodeNats perms ++ rest)))) := by
    rw [hpos, drop_schAt, schsSuf_cons I hj, encodeNats_append, hD]
    simp only [List.cons_append, encNats_cons, List.append_assoc, encodeNats_append]; rfl
  have hlenD : (encodeNats (schD I e)).length = (encodeNat a).length +
      (encodeNats locs).length + (encodeNat d).length + (encodeNats cs.flatten).length +
      (encodeNats perms).length := by
    rw [hD]; simp only [List.cons_append, encNats_cons, List.append_assoc, encodeNats_append,
      List.length_append]; ring
  have hDH := schD_le_H I e
  have hla : locs.length = a := length_schLocs sc
  have hp : perms.length = a * k * (ℓ + 1) := by
    rw [length_perms]; ring
  have ha23 : 2 ≤ a ∧ a ≤ 3 := by simp only [a, arity]; split_ifs <;> omega
  have hlo := length_le_encodeNats locs
  have hpe := length_le_encodeNats perms
  have hfe := length_le_encodeNats cs.flatten
  have hak : 0 < a * k := Nat.mul_pos (by omega) (by omega)
  have hkp : k ≤ perms.length := by
    rw [hp]
    exact le_trans (Nat.le_mul_of_pos_left k (by omega : 0 < a)) (Nat.le_mul_of_pos_right _ (by omega))
  have hlp : ℓ + 1 ≤ perms.length := by rw [hp]; exact Nat.le_mul_of_pos_left _ hak
  have hdf : d ≤ (encodeNats cs.flatten).length := by
    have : d ≤ cs.flatten.length := by rw [hfl]; exact Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hpH : perms.length ≤ H I := by omega
  have hdH : d ≤ H I := by omega
  -- reading the arity
  have r1 := rdNumS_good (Q := CQ) hw (r := rA) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s a _ hx (bits_lt_of_le (by omega) hH2)
  set s1 := rdNumFinal s rA rP rT a
  have e1A : s1.env rA = a := rdNumFinal_env_r (by decide) (by decide) a
  -- skipping the locations
  obtain ⟨s2, r2, h2s, h2p, h2o, h2f⟩ := skipNumsS_good (Q := CQ) hw (n := rA) (i := rI)
    (t := rT) (by decide) (by decide) (by decide) s1 locs _
    (by simp only [s1, rdNumFinal_pos]; rw [← List.drop_drop, hx, List.drop_left])
    (by rw [e1A, hla]) (by omega)
  -- reading `|D|`
  have r3 := rdNumS_good (Q := CQ) hw (r := rD) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s2 d _ (by
      rw [h2p]; simp only [s1, rdNumFinal_pos]
      rw [← List.drop_drop, ← List.drop_drop, hx, List.drop_left, List.drop_left])
    (bits_lt_of_le hdH hH2)
  set s3 := rdNumFinal s2 rD rP rT d
  have e3 : ∀ r, r ≠ rD → r ≠ rP → r ≠ rT → r ≠ rI → s3.env r = s1.env r := fun r h1 h2 h3 h4 => by
    rw [rdNumFinal_env_ne h1 h2 h3, h2f r h4 h3]
  -- skipping the coordinates
  obtain ⟨s4, r4, h4s, h4p, h4o, h4f⟩ := skipBlocksS_good (Q := CQ) hw (d := rD) (m := rL1)
    (j := rK) (i := rI) (t := rT) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) s3 cs (ℓ + 1) hcsM _
    (by
      simp only [s3, rdNumFinal_pos]; rw [h2p]; simp only [s1, rdNumFinal_pos]
      rw [← List.drop_drop, ← List.drop_drop, ← List.drop_drop, hx, List.drop_left,
        List.drop_left, List.drop_left])
    (by rw [hcsl]; exact rdNumFinal_env_r (by decide) (by decide) d)
    (by rw [e3 _ (by decide) (by decide) (by decide) (by decide),
      rdNumFinal_env_ne (by decide) (by decide) (by decide), hL1])
    (by rw [hcsl]; omega) (by omega)
  have e4 : ∀ r, r ≠ rK → r ≠ rI → r ≠ rT → r ≠ rD → r ≠ rP → s4.env r = s1.env r :=
    fun r h1 h2 h3 h4 h5 => by rw [h4f r h1 h2 h3, e3 r h4 h5 h3 h2]
  have e4A : s4.env rA = a := by rw [e4 _ (by decide) (by decide) (by decide) (by decide) (by decide), e1A]
  have e4K : s4.env rKk = k := by
    rw [e4 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      rdNumFinal_env_ne (by decide) (by decide) (by decide), hK]
  have e4L : s4.env rL1 = ℓ + 1 := by
    rw [e4 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      rdNumFinal_env_ne (by decide) (by decide) (by decide), hL1]
  -- the number of permutation words
  have r5 := mulS_good (x := encodeSystem I) (w := w) hw (dst := rC) (a := rA) (b := rKk)
    (j := rI) (by decide) (by decide) (by decide) (by decide) (by decide) s4 e4A e4K
    (by nlinarith) (by omega)
  set s5 := (s4.set rC (a * k)).set rI k
  have r6 := mulS_good (x := encodeSystem I) (w := w) hw (dst := rC2) (a := rC) (b := rL1)
    (j := rI) (by decide) (by decide) (by decide) (by decide) (by decide) s5 (A := a * k) (B := ℓ + 1)
    (by simp (config := { decide := true }) [s5, Function.update_of_ne (show rC ≠ rI by decide)])
    (by simp (config := { decide := true }) [s5, Function.update_of_ne (show rL1 ≠ rI by decide),
      Function.update_of_ne (show rL1 ≠ rC by decide), e4L])
    (by rw [← hp]; omega) (by omega)
  set s6 := (s5.set rC2 (a * k * (ℓ + 1))).set rI (ℓ + 1)
  -- skipping the permutations
  obtain ⟨s7, r7, h7s, h7p, h7o, h7f⟩ := skipNumsS_good (Q := CQ) hw (n := rC2) (i := rI)
    (t := rT) (by decide) (by decide) (by decide) s6 perms rest
    (by
      simp only [s6, s5, NSt.set_pos]; rw [h4p]; simp only [s3, rdNumFinal_pos]; rw [h2p]
      simp only [s1, rdNumFinal_pos]
      rw [← List.drop_drop, ← List.drop_drop, ← List.drop_drop, ← List.drop_drop, hx,
        List.drop_left, List.drop_left, List.drop_left, List.drop_left])
    (by simp (config := { decide := true }) [s6, Function.update_of_ne (show rC2 ≠ rI by decide), hp]) (by omega)
  refine ⟨s7, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))).mono ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [hlenD]
    have := p4SRead_arith (N := Ex.nodeCost w) (U := unitCost w)
      (la := (encodeNat a).length) (llo := (encodeNats locs).length)
      (ld := (encodeNat d).length) (lf := (encodeNats cs.flatten).length)
      (lp := (encodeNats perms).length) (a := locs.length) (d := cs.length) (k := k) (ℓ := ℓ)
      (np := perms.length) hU hlo (by rw [hcsl]; exact hdf) (by omega) (by omega) hpe
    exact this
  · rw [h7p]; simp only [s6, s5, NSt.set_pos]; rw [h4p]; simp only [s3, rdNumFinal_pos]
    rw [h2p]; simp only [s1, rdNumFinal_pos]; rw [hlenD]; ring
  · rw [h7s]; simp only [s6, s5, NSt.set_stk]; rw [h4s]; simp only [s3, rdNumFinal_stk]
    rw [h2s]; rfl
  · rw [h7o]; simp only [s6, s5, NSt.set_out]; rw [h4o]; simp only [s3, rdNumFinal_out]
    rw [h2o]; rfl
  · rw [h7f _ (by decide) (by decide)]
    simp (config := { decide := true }) [s6, s5, Function.update_of_ne (show rA ≠ rI by decide),
      Function.update_of_ne (show rA ≠ rC2 by decide), Function.update_of_ne (show rA ≠ rC by decide)]
    exact e4A
  · rw [h7f _ (by decide) (by decide)]
    simp (config := { decide := true }) [s6, s5, Function.update_of_ne (show rD ≠ rI by decide),
      Function.update_of_ne (show rD ≠ rC2 by decide), Function.update_of_ne (show rD ≠ rC by decide)]
    rw [h4f _ (by decide) (by decide) (by decide)]
    exact rdNumFinal_env_r (by decide) (by decide) d

end Lax119563Proofs.Compiler

end Compiler_P4SzRead

/-! ### Formerly `Lax119563Proofs.Compiler.PSchLoop` -/

section Compiler_PSchLoop

/-!
# Pass `P2`: the schema loop and the pass (`p2Sch_good`, `p2_good`)
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-! ## One schema -/

/-- The sum of the sizes of the first `j` schemas. -/
noncomputable def lbUpTo (j : ℕ) : ℕ := (((List.finRange I.schemas.length).take j).map (schSize I)).sum

lemma lbUpTo_succ {j : ℕ} (hj : j < I.schemas.length) :
    lbUpTo I (j + 1) = lbUpTo I j + schSize I ⟨j, hj⟩ := by
  rw [lbUpTo, List.take_add_one, List.getElem?_eq_getElem (by simpa using hj)]
  simp [lbUpTo]

lemma lbUpTo_le (j : ℕ) : lbUpTo I j ≤ locBase I := by
  rw [lbUpTo, locBase]
  conv_rhs => rw [← List.take_append_drop j (List.finRange I.schemas.length)]
  rw [List.map_append, List.sum_append]; omega

lemma lbUpTo_all : lbUpTo I I.schemas.length = locBase I := by
  rw [lbUpTo, locBase, List.take_of_length_le (by simp)]

lemma schRecsUpTo_succ {j : ℕ} (hj : j < I.schemas.length) :
    schRecsUpTo I (j + 1) = schRecsUpTo I j ++ schRec I ⟨j, hj⟩ := by
  rw [schRecsUpTo, List.take_add_one, List.getElem?_eq_getElem (by simpa using hj)]
  simp [schRecsUpTo]

/-- The invariant of the schema loop. -/
def p2Inv (st s : NSt CR CQ) : Prop :=
  s.env rJ ≤ I.schemas.length ∧ s.env rE = I.schemas.length ∧ s.env rL = ℓ ∧ s.env rKk = k ∧
    s.env rKm1 = k - 1 ∧ s.env rK1 = k + 1 ∧ s.env rPL = k * (ℓ + 1) ∧
    s.env rLB = lbUpTo I (s.env rJ) ∧ s.pos = schAt I (s.env rJ) ∧
    s.stk = Function.update st.stk qSch ((schRecsUpTo I (s.env rJ)).reverse ++ st.stk qSch) ∧
    s.out = st.out

lemma arity_le (s : Schema k ℓ I.numLocations) : arity s ≤ 3 := by
  unfold arity; split_ifs <;> omega

lemma lt_arity_iff (s : Schema k ℓ I.numLocations) :
    (if 2 < arity s then 1 else 0) = (if Matrix.isTern s then 1 else 0) := by
  unfold arity; split_ifs <;> simp_all

lemma p2Sch_cost_arith (N U la ll lo ld ℓ lc d k a lp pl : ℕ) (hU : U ≤ N) (hU' : 64 ≤ U)
    (hd : d ≤ lc) (hℓ : ℓ ≤ lp) (hk : k ≤ lp) (hp : pl ≤ lp) (ha : a ≤ 3) (hlo : lo ≤ ll) :
    (la + 1) * (20 * N) +
      ((1 + 1 + 1) * N + U +
        ((ll + lo + 1) * (20 * N) +
          ((ld + 1) * (20 * N) +
            (12 * N +
              ((ℓ + 1) * (12 * N) +
                (150 * N * lc + d * (150 * N + ((1 + 1 + 1) * N + 1)) + ((1 + 1 + 1) * N + 1) +
                  ((ℓ + k + 10) * (60 * N) +
                    ((a + 1) * (12 * N) +
                      ((lp + pl + 1) * (20 * N) + ((1 + 1 + 1) * N + U)))))))))) ≤
    400 * N * (la + ll + ld + lc + lp) + 1000 * N := by
  have m1 := Nat.mul_le_mul_left N hd
  have m2 := Nat.mul_le_mul_left N hℓ
  have m3 := Nat.mul_le_mul_left N hk
  have m4 := Nat.mul_le_mul_left N hp
  have m6 := Nat.mul_le_mul_left N ha
  have m9 := Nat.mul_le_mul_left N hlo
  have m7 : d ≤ N * lc := le_trans hd (Nat.le_mul_of_pos_left _ (by omega))
  nlinarith

set_option maxHeartbeats 6000000 in
/-- One schema. -/
lemma p2Sch_good {w : ℕ} (hw : 2 ≤ w) (hk : 1 ≤ k) (hkH : k ≤ H I) (hℓ : ℓ ≤ H I)
    (hS : 16 * (H I + locBase I + 1) ≤ 2 ^ w) (st : NSt CR CQ) (hq1 : st.stk qOr = [])
    (hq2 : st.stk qOr2 = []) (s : NSt CR CQ) (hI : p2Inv I st s)
    (hc : (Ex.lt (rv rJ) (rv rE)).eval s.env ≠ 0) :
    ∃ s', Good (encodeSystem I) w p2Sch s s'
        (400 * Ex.nodeCost w * ((H I - s.pos) - (H I - s'.pos)) + 1000 * Ex.nodeCost w) ∧
      p2Inv I st s' ∧ I.schemas.length - s'.env rJ < I.schemas.length - s.env rJ ∧
      H I - s'.pos ≤ H I - s.pos := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hH2 : 2 * (H I + 1) ≤ 2 ^ w := by omega
  have h3H := three_le_H I
  obtain ⟨hJ, hE, hL, hKk, hKm, hK1, hPL, hLB, hpos, hstk, hout⟩ := hI
  have hlt : s.env rJ < I.schemas.length := by
    by_contra h; apply hc; simp only [Ex.eval, rv, hE]; rw [if_neg h]
  obtain ⟨j, hjdef⟩ : ∃ j, s.env rJ = j := ⟨_, rfl⟩
  rw [hjdef] at hlt hLB hpos hstk
  set e : Fin I.schemas.length := ⟨j, hlt⟩
  set sc := sch I e
  set D := coordList (dom I e)
  set d := D.length
  set a := arity sc
  set tern := Matrix.isTern sc
  set locs := schLocs sc
  set perms := (schPerms sc).flatMap permDescription
  have hschD : schD I e = a :: locs ++ (d :: D.flatMap cdesc) ++ perms := by
    rw [schD, schemaDescription_eq']; rfl
  set rest := encodeNats (schsSuf I (j + 1))
  have hx : (encodeSystem I).drop s.pos = encodeNat a ++ (encodeNats locs ++
      (encodeNat d ++ (encodeNats (D.flatMap cdesc) ++ (encodeNats perms ++ rest)))) := by
    rw [hpos, drop_schAt, schsSuf_cons I hlt, encodeNats_append, hschD]
    simp only [List.cons_append, List.append_assoc, encNats_cons, encodeNats_append]
    rfl
  have hΔ : (encodeNats (schD I e)).length = (encodeNat a).length + (encodeNats locs).length +
      (encodeNat d).length + (encodeNats (D.flatMap cdesc)).length + (encodeNats perms).length := by
    rw [hschD]
    simp only [List.cons_append, List.append_assoc, encNats_cons, encodeNats_append,
      List.length_append]; ring
  have hsch : schAt I (j + 1) = schAt I j + (encodeNats (schD I e)).length := schAt_succ I hlt
  have hschle := schAt_le I (j + 1)
  have ha3 : a ≤ 3 := arity_le I sc
  have hlocs : locs.length = a := length_schLocs sc
  have hperms : perms.length = a * (k + k * ℓ) := length_perms sc
  have hcl : (D.flatMap cdesc).length = d * (ℓ + 1) := by
    rw [List.length_flatMap]
    simp [length_cdesc, d]
  have hpe : perms.length ≤ (encodeNats perms).length := length_le_encodeNats _
  have hce : (D.flatMap cdesc).length ≤ (encodeNats (D.flatMap cdesc)).length :=
    length_le_encodeNats _
  have hle_e : (encodeNats (schD I e)).length ≤ H I := schD_le_H I e
  have ha2 : 2 ≤ a := by unfold a arity; split_ifs <;> omega
  have hdH : d ≤ H I := by nlinarith
  have hkp : k ≤ perms.length := by rw [hperms]; nlinarith
  have hℓp : ℓ ≤ perms.length := by rw [hperms]; nlinarith
  have hPLH : k * (ℓ + 1) * a ≤ H I := by
    have : k * (ℓ + 1) * a = perms.length := by rw [hperms]; ring
    omega
  -- sizes
  have hsz := schSize_eq' I e
  have hne := nEnt_eq I e
  have hlb : lbUpTo I j + schSize I e ≤ locBase I := by
    have := lbUpTo_le I (j + 1); rwa [lbUpTo_succ I hlt] at this
  have hrs : rowsSum D ≤ locBase I := by
    have : rowsSum D ≤ nEnt I e := by rw [hne]; nlinarith
    omega
  -- arity
  have r1 := rdNumS_good (Q := CQ) hw (r := rA) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s a _ hx (bits_lt_of_le (by omega) hH2)
  set s1 := rdNumFinal s rA rP rT a
  have e1A : s1.env rA = a := rdNumFinal_env_r (by decide) (by decide) _
  have r2 := Good.set (x := encodeSystem I) (w := w) (st := s1) (r := rTern)
    (e := .lt (.const 2) (rv rA)) (by simp only [Ex.Fits, rv, e1A]; omega)
  set s2 := s1.set rTern ((Ex.lt (.const 2) (rv rA)).eval s1.env)
  have e2T : s2.env rTern = if tern then 1 else 0 := by
    simp only [s2, NSt.set_env, Function.update_self, Ex.eval, rv, e1A]
    exact lt_arity_iff I sc
  have e2A : s2.env rA = a := by
    simp only [s2, NSt.set_env, Function.update_of_ne (show rA ≠ rTern by decide)]; exact e1A
  have hx2 : (encodeSystem I).drop s2.pos = encodeNats locs ++
      (encodeNat d ++ (encodeNats (D.flatMap cdesc) ++ (encodeNats perms ++ rest))) := by
    show (encodeSystem I).drop (s.pos + (encodeNat a).length) = _
    rw [drop_add, hx, List.drop_left]
  obtain ⟨s3, r3, hs3, hp3, ho3, he3⟩ := skipNumsS_good (x := encodeSystem I) (w := w)
    (Q := CQ) hw (n := rA) (i := rI) (t := rT) (by decide) (by decide) (by decide) s2 locs _ hx2
    (by rw [e2A, hlocs]) (by omega)
  have hx3 : (encodeSystem I).drop s3.pos = encodeNat d ++
      (encodeNats (D.flatMap cdesc) ++ (encodeNats perms ++ rest)) := by
    rw [hp3, drop_add, hx2, List.drop_left]
  have r4 := rdNumS_good (Q := CQ) hw (r := rD) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s3 d _ hx3 (bits_lt_of_le hdH hH2)
  set s4 := rdNumFinal s3 rD rP rT d
  have e4 : ∀ q, q ≠ rD → q ≠ rP → q ≠ rT → s4.env q = s3.env q :=
    fun q h1 h2 h3 => rdNumFinal_env_ne h1 h2 h3 _
  -- registers from `s` to `s4`
  have k04 : ∀ q, CStm.wReg q (.seq (rdNumS rA rP rT) (.seq (.set rTern (.lt (.const 2) (rv rA)))
      (.seq (skipNumsS rA rI rT) (rdNumS rD rP rT))) : CStm CR CQ) = false →
      s4.env q = s.env q := fun q hq => (r1.seq (r2.seq (r3.seq r4))).env_of hq
  have e4Kk : s4.env rKk = k := by rw [k04 _ (by decide), hKk]
  -- initialisation
  have hI5 : ∃ s5, Good (encodeSystem I) w p2Init s4 s5 (12 * Ex.nodeCost w) ∧
      s5.env rRows = 0 ∧ s5.env rCol = 0 ∧ s5.env rDist = 0 ∧ s5.env rLast = 0 ∧
      s5.env rPrev = k ∧ s5.env rK = 0 ∧ s5.pos = s4.pos ∧ s5.stk = s4.stk ∧ s5.out = s4.out ∧
      ∀ q, CStm.wReg q p2Init = false → s5.env q = s4.env q := by
    set t1 := s4.set rRows 0
    set t2 := t1.set rCol 0
    set t3 := t2.set rDist 0
    set t4 := t3.set rLast 0
    set t5 := t4.set rPrev k
    have g1 : Good (encodeSystem I) w (.set rRows (.const 0) : CStm CR CQ) s4 t1
        (Ex.nodeCost w + unitCost w) := (CStm.Good.set (by simp only [Ex.Fits]; omega)).mono (by simp [Ex.size])
    have g2 : Good (encodeSystem I) w (.set rCol (.const 0) : CStm CR CQ) t1 t2
        (Ex.nodeCost w + unitCost w) := (CStm.Good.set (by simp only [Ex.Fits]; omega)).mono (by simp [Ex.size])
    have g3 : Good (encodeSystem I) w (.set rDist (.const 0) : CStm CR CQ) t2 t3
        (Ex.nodeCost w + unitCost w) := (CStm.Good.set (by simp only [Ex.Fits]; omega)).mono (by simp [Ex.size])
    have g4 : Good (encodeSystem I) w (.set rLast (.const 0) : CStm CR CQ) t3 t4
        (Ex.nodeCost w + unitCost w) := (CStm.Good.set (by simp only [Ex.Fits]; omega)).mono (by simp [Ex.size])
    have ht4 : t4.env rKk = k := by
      simp [t4, t3, t2, t1, Function.update_of_ne (show rKk ≠ rLast by decide),
        Function.update_of_ne (show rKk ≠ rDist by decide),
        Function.update_of_ne (show rKk ≠ rCol by decide),
        Function.update_of_ne (show rKk ≠ rRows by decide), e4Kk]
    have g5 : Good (encodeSystem I) w (.set rPrev (rv rKk) : CStm CR CQ) t4 t5
        (Ex.nodeCost w + unitCost w) :=
      (CStm.Good.set (by simp only [Ex.Fits, rv, ht4]; omega)).of_eq
        (by simp only [Ex.eval, rv, ht4, t5]) (by simp [Ex.size])
    have g6 : Good (encodeSystem I) w (.set rK (.const 0) : CStm CR CQ) t5 (t5.set rK 0)
        (Ex.nodeCost w + unitCost w) := (CStm.Good.set (by simp only [Ex.Fits]; omega)).mono (by simp [Ex.size])
    have g := g1.seq (g2.seq (g3.seq (g4.seq (g5.seq g6))))
    refine ⟨_, g.mono ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, fun q hq => g.env_of hq⟩
    · omega
    all_goals simp [t5, t4, t3, t2, t1, NSt.set, Function.update_apply, rRows, rK, rPrev, rCol, rDist, rLast]
  obtain ⟨s5, r5, e5R, e5C, e5D, e5L, e5P, e5K, hp5, hs5, ho5, k45⟩ := hI5
  -- the OR stack
  have e5L' : s5.env rL = ℓ := by rw [k45 _ (by decide), k04 _ (by decide), hL]
  have r6 := pushZS_good (x := encodeSystem I) (w := w) (q := qOr) hw (n := rL) (j := rI)
    (by decide) s5 e5L' (by omega)
  set s6 := (s5.setS qOr (List.replicate ℓ 0 ++ s5.stk qOr)).set rI ℓ
  have hst4 : s4.stk = s.stk := by
    rw [show s4.stk = s3.stk from rfl, hs3]; rfl
  have hs6 : s6.stk = Function.update s.stk qOr (orsL ([] : List (Coord k ℓ))) := by
    simp only [s6, NSt.set_stk, NSt.setS_stk, hs5, hst4, hstk, orsL_nil]
    rw [Function.update_of_ne (show qOr ≠ qSch by decide), hq1, List.append_nil]
  have hs6' : s6.stk = Function.update (Function.update s6.stk qOr (orsL ([] : List (Coord k ℓ))))
      qOr2 [] := by
    rw [hs6]
    funext q
    by_cases h1 : q = qOr2
    · subst h1
      simp [Function.update_of_ne (show qOr2 ≠ qOr by decide), hstk,
        Function.update_of_ne (show qOr2 ≠ qSch by decide), hq2]
    · by_cases h2 : q = qOr
      · subst h2; simp [Function.update_of_ne h1]
      · simp [Function.update_of_ne h1, Function.update_of_ne h2]
  have e6 : ∀ q, q ≠ rI → s6.env q = s5.env q := fun q h => by
    simp [s6, Function.update_of_ne h]
  -- the coordinates
  have hx6 : (encodeSystem I).drop s6.pos = encodeNats (D.flatMap cdesc) ++
      (encodeNats perms ++ rest) := by
    show (encodeSystem I).drop s5.pos = _
    rw [hp5]
    show (encodeSystem I).drop (s3.pos + (encodeNat d).length) = _
    rw [drop_add, hx3, List.drop_left]
  have k46 : ∀ q, q ≠ rI → CStm.wReg q p2Init = false → s6.env q = s4.env q :=
    fun q h1 h2 => by rw [e6 q h1, k45 q h2]
  have e4D : s4.env rD = d := rdNumFinal_env_r (by decide) (by decide) _
  have e4T : s4.env rTern = if tern then 1 else 0 := by
    rw [e4 _ (by decide) (by decide) (by decide), r3.env_of (r := rTern) (by decide), e2T]
  have hI6 : p2CoordInv D tern s6.pos s6.stk s6.out s6 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · rw [e6 _ (by decide), e5K]; omega
    · rw [k46 _ (by decide) (by decide), e4D]
    · rw [k46 _ (by decide) (by decide), k04 _ (by decide), hL]
    · rw [k46 _ (by decide) (by decide), e4Kk]
    · rw [k46 _ (by decide) (by decide), k04 _ (by decide), hKm]
    · rw [k46 _ (by decide) (by decide), e4T]
    · rw [e6 _ (by decide), e5R, e6 _ (by decide), e5K]; rfl
    · rw [e6 _ (by decide), e5C, e6 _ (by decide), e5K]; simp
    · rw [e6 _ (by decide), e5D, e6 _ (by decide), e5K]; rfl
    · rw [e6 _ (by decide), e5P, e6 _ (by decide), e5K]; rfl
    · rw [e6 _ (by decide), e5L, e6 _ (by decide), e5K]; simp
    · rw [e6 _ (by decide), e5K]; simp [encodeNats]
    · rw [e6 _ (by decide), e5K, List.take_zero]; exact hs6'
  obtain ⟨s7, r7, hI7, hc7⟩ := Good.loop_var (x := encodeSystem I) (w := w)
    (e := .lt (rv rK) (rv rD)) (body := p2Coord) (p2CoordInv D tern s6.pos s6.stk s6.out)
    (fun s => d - s.env rK) (fun s' => s6.pos + (encodeNats (D.flatMap cdesc)).length - s'.pos)
    (150 * Ex.nodeCost w) (150 * Ex.nodeCost w) (fun s' hI' => ⟨by
      obtain ⟨hK', hD', -⟩ := hI'
      simp only [Ex.Fits, rv, hD']; omega,
      fun hc' => p2Coord_good I hw D hkH hℓ hdH (by omega) tern s6.pos s6.stk s6.out _ hx6
        s' hI' hc'⟩) s6 hI6
  obtain ⟨hK7, hD7, hL7, hKk7, hKm7, hT7, hR7, hC7, hDi7, hP7, hLa7, hp7, hs7, ho7⟩ := hI7
  have hK7' : s7.env rK = d := by
    simp only [Ex.eval, rv, hD7] at hc7; split_ifs at hc7 with h <;> omega
  rw [hK7', List.take_of_length_le le_rfl] at hR7 hDi7 hLa7 hp7 hs7
  rw [hK7'] at hC7
  -- the numbers
  set Lt := if ∃ c ∈ D, ¬ (c.1 : ℕ) + 1 < k then 1 else 0
  set Dt := dChg k (D.map fun c => (c.1 : ℕ))
  have hBR : (if Lt ≠ 0 then k - 1 else Dt) = blkRows D := by
    rw [blkRows_eq]
    by_cases h : ∃ c ∈ D, ¬ (c.1 : ℕ) + 1 < k
    · rw [if_pos h, if_pos (by simp only [Lt, if_pos h]; omega)]
    · rw [if_neg h, if_neg (by simp only [Lt, if_neg h]; omega)]
  have hors7 : s7.stk qOr = orsL D := by
    rw [hs7, Function.update_of_ne (show qOr ≠ qOr2 by decide), Function.update_self]
  have k47 : ∀ q, CStm.wReg q (.seq p2Init (.seq (pushZS qOr rL rI)
      (.loop (.lt (rv rK) (rv rD)) p2Coord)) : CStm CR CQ) = false → s7.env q = s4.env q :=
    fun q hq => (r5.seq (r6.seq r7)).env_of hq
  have e7K1 : s7.env rK1 = k + 1 := by rw [k47 _ (by decide), k04 _ (by decide), hK1]
  have e7LB : s7.env rLB = lbUpTo I j := by rw [k47 _ (by decide), k04 _ (by decide), hLB]
  have hDt : Dt ≤ H I := (dChg_le _ _).trans (by simp [Dt]; omega)
  have hsum : (orsL D).sum = orPop D := sum_orsL D
  have hcoef := length_coefSteps I e
  have hszv : d * colV tern + 6 * (rowsSum D * (k + 1)) +
      2 * (((if Lt ≠ 0 then k - 1 else Dt) + (orsL D).sum) * (k + 1)) = schSize I e := by
    rw [hsz, hne, hcoef, hBR, hsum]
    simp only [colV, tern]; ring
  obtain ⟨s8, r8, e8LB, hs8, hp8, ho8⟩ := p2Fin_good I hw s7 (orsL D) hors7 (length_orsL D)
    (orsL_le D) hL7 hKm7 e7K1 hLa7 (by simp only [Lt]; split_ifs <;> omega) hDi7 hR7 hC7 e7LB
    (by omega)
  -- the permutations
  have k48 : ∀ q, CStm.wReg q (.seq p2Init (.seq (pushZS qOr rL rI)
      (.seq (.loop (.lt (rv rK) (rv rD)) p2Coord) p2Fin)) : CStm CR CQ) = false →
      s8.env q = s4.env q :=
    fun q hq => (r5.seq (r6.seq (r7.seq r8))).env_of hq
  have e8PL : s8.env rPL = k * (ℓ + 1) := by rw [k48 _ (by decide), k04 _ (by decide), hPL]
  have e8A : s8.env rA = a := by
    rw [k48 _ (by decide), e4 _ (by decide) (by decide) (by decide),
      r3.env_of (r := rA) (by decide), e2A]
  have r9 := mulS_good (x := encodeSystem I) (w := w) (Q := CQ) (dst := rPN) (a := rPL)
    (b := rA) (j := rJ2) hw (by decide) (by decide) (by decide) (by decide) (by decide) s8 e8PL
    e8A (by omega) (by omega)
  set s9 := (s8.set rPN (k * (ℓ + 1) * a)).set rJ2 a
  have hx9 : (encodeSystem I).drop s9.pos = encodeNats perms ++ rest := by
    show (encodeSystem I).drop s8.pos = _
    rw [hp8, hp7]
    rw [drop_add, hx6, List.drop_left]
  obtain ⟨s10, r10, hs10, hp10, ho10, he10⟩ := skipNumsS_good (x := encodeSystem I) (w := w)
    (Q := CQ) hw (n := rPN) (i := rI) (t := rT) (by decide) (by decide) (by decide) s9 perms _
    hx9 (by simp [s9, Function.update_of_ne (show rPN ≠ rJ2 by decide), hperms]; ring)
    (by omega)
  have r11 := Good.set (x := encodeSystem I) (w := w) (st := s10) (r := rJ)
    (e := .add (rv rJ) (.const 1)) (by
      have : s10.env rJ = j := by
        rw [he10 _ (by decide) (by decide)]
        simp only [s9, NSt.set_env, Function.update_of_ne (show rJ ≠ rJ2 by decide),
          Function.update_of_ne (show rJ ≠ rPN by decide)]
        rw [k48 _ (by decide), k04 _ (by decide), hjdef]
      have := E_le I
      simp only [Ex.Fits, Ex.eval, rv, this]; omega)
  set s11 := s10.set rJ ((Ex.add (rv rJ) (.const 1)).eval s10.env)
  have hall := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq
    (r10.seq r11)))))))))
  have htail := r9.seq (r10.seq r11)
  have e11J : s11.env rJ = j + 1 := by
    simp only [s11, NSt.set_env, Function.update_self, Ex.eval, rv]
    rw [he10 _ (by decide) (by decide)]
    simp only [s9, NSt.set_env, Function.update_of_ne (show rJ ≠ rJ2 by decide),
      Function.update_of_ne (show rJ ≠ rPN by decide)]
    rw [k48 _ (by decide), k04 _ (by decide), hjdef]
  have hp11 : s11.pos = s.pos + (encodeNats (schD I e)).length := by
    have q10 : s11.pos = s9.pos + (encodeNats perms).length := hp10
    have q9 : s9.pos = s8.pos := rfl
    have q6 : s6.pos = s4.pos := by show s5.pos = _; exact hp5
    have q4 : s4.pos = s3.pos + (encodeNat d).length := rfl
    have q2 : s2.pos = s.pos + (encodeNat a).length := rfl
    rw [q10, q9, hp8, hp7, q6, q4, hp3, q2, hΔ]; ring
  refine ⟨s11, hall.mono ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hp11]
    have hΔ' : H I - s.pos - (H I - (s.pos + (encodeNats (schD I e)).length)) =
        (encodeNats (schD I e)).length := by rw [hpos]; omega
    rw [hΔ', hΔ]
    have hφ6 : s6.pos + (encodeNats (D.flatMap cdesc)).length - s6.pos =
        (encodeNats (D.flatMap cdesc)).length := by omega
    have hμ6 : d - s6.env rK = d := by rw [e6 _ (by decide), e5K]; rfl
    rw [hφ6, hμ6]
    have hel : a ≤ (encodeNats locs).length := hlocs ▸ length_le_encodeNats locs
    have hdc : d ≤ (encodeNats (D.flatMap cdesc)).length :=
      le_trans (Nat.le_mul_of_pos_right d (by omega)) (hcl ▸ hce)
    simp only [condCost, Ex.size, rv]
    exact p2Sch_cost_arith _ _ _ _ _ _ _ _ _ _ _ _ _ hU hU' hdc (by omega) (by omega) hpe ha3
      (length_le_encodeNats locs)
  · rw [e11J]; omega
  · rw [hall.env_of (by decide), hE]
  · rw [hall.env_of (by decide), hL]
  · rw [hall.env_of (by decide), hKk]
  · rw [hall.env_of (by decide), hKm]
  · rw [hall.env_of (by decide), hK1]
  · rw [hall.env_of (by decide), hPL]
  · rw [e11J, show lbUpTo I (j + 1) = lbUpTo I j + schSize I e from lbUpTo_succ I hlt,
      htail.env_of (by decide), e8LB, ← hszv]; ring
  · rw [e11J, hp11, hpos, hsch]
  · rw [e11J]
    show s10.stk = _
    rw [hs10]
    show s8.stk = _
    rw [hs8]
    funext q
    by_cases h1 : q = qSch
    · subst h1
      simp only [Function.update_self, hs7, hs6, hstk,
        Function.update_of_ne (show qSch ≠ qOr2 by decide),
        Function.update_of_ne (show qSch ≠ qOr by decide)]
      rw [show schRecsUpTo I (j + 1) = schRecsUpTo I j ++ schRec I e from
        schRecsUpTo_succ I hlt]
      simp only [schRec, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append, List.singleton_append, List.append_assoc, hne, hcoef,
        hBR, hsum, List.cons.injEq]
      refine ⟨by ring, by ring, rfl, rfl⟩
    · rw [Function.update_of_ne h1, Function.update_of_ne h1]
      by_cases h2 : q = qOr
      · subst h2; rw [Function.update_self, hq1]
      · rw [Function.update_of_ne h2, hs7]
        by_cases h3 : q = qOr2
        · subst h3; rw [Function.update_self, hq2]
        · rw [Function.update_of_ne h3, Function.update_of_ne h2, hs6, Function.update_of_ne h2,
            hstk, Function.update_of_ne h1]
  · rw [hall.out_of (by decide), hout]
  · rw [e11J]; omega
  · rw [hp11]; omega

/-! ## The pass -/

lemma schsPre_all : schsPre I I.schemas.length = schsDesc I := by
  rw [schsPre, schsDesc_eq, List.take_of_length_le (by simp)]

lemma schAt_all : schAt I I.schemas.length = H I := by
  rw [schAt, schsPre_all, schPos_add]

lemma kl_le_H (hE : I.schemas ≠ []) : k * (ℓ + 1) ≤ H I := by
  have hj : 0 < I.schemas.length := List.length_pos_of_ne_nil hE
  have h1 := schD_length_le I ⟨0, hj⟩
  rw [schD, schemaDescription_eq'] at h1
  have h2 := length_perms (sch I ⟨0, hj⟩)
  have h3 : 2 ≤ arity (sch I ⟨0, hj⟩) := by unfold arity; split_ifs <;> omega
  simp only [List.length_append, List.length_cons] at h1
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **Pass `P2`.** Run at the position of `E` (after `p1r`) with `rKk = k`, `rL = ℓ`,
`rL1 = ℓ + 1` and empty stacks `qOr`, `qOr2`, `p2` computes `rLB = locBase I` and pushes the
schema records onto `qSch`, ending at the end of the input. -/
theorem p2_good {w : ℕ} (hw : 2 ≤ w) (hk : 1 ≤ k) (hE : I.schemas ≠ [])
    (hS : 16 * (H I + locBase I + 1) ≤ 2 ^ w) (st : NSt CR CQ)
    (hp : st.pos = posAt I I.numLocations) (hKk : st.env rKk = k) (hL : st.env rL = ℓ)
    (hL1 : st.env rL1 = ℓ + 1) (hq1 : st.stk qOr = []) (hq2 : st.stk qOr2 = []) :
    ∃ st', Good (encodeSystem I) w p2 st st' (2000 * (H I + 1) * Ex.nodeCost w) ∧
      st'.env rLB = locBase I ∧
      st'.stk = Function.update st.stk qSch
        ((schRecsUpTo I I.schemas.length).reverse ++ st.stk qSch) ∧
      st'.out = st.out ∧ st'.pos = H I ∧
      ∀ r, CStm.wReg r p2 = false → st'.env r = st.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hH2 : 2 * (H I + 1) ≤ 2 ^ w := by omega
  have hkH := k_le_H I hE
  have hℓ := ell_le_H I hk (fun h => hE h.2)
  have hEH := E_le I
  have hPLH := kl_le_H I hE
  have hx : (encodeSystem I).drop st.pos = encodeNat I.schemas.length ++
      encodeNats (schsDesc I) := by rw [hp, drop_posAt_W]
  have r1 := rdNumS_good (Q := CQ) hw (r := rE) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) st I.schemas.length _ hx (bits_lt_of_le hEH hH2)
  set s1 := rdNumFinal st rE rP rT I.schemas.length
  have e1 : ∀ q, q ≠ rE → q ≠ rP → q ≠ rT → s1.env q = st.env q :=
    fun q h1 h2 h3 => rdNumFinal_env_ne h1 h2 h3 _
  have r2 := predS_good (x := encodeSystem I) (w := w) (Q := CQ) hw (dst := rKm1) (n := rKk)
    (by decide) s1 (by rw [e1 _ (by decide) (by decide) (by decide), hKk]) (by omega)
  set s2 := s1.set rKm1 (k - 1)
  have e2K : s2.env rKk = k := by
    simp [s2, Function.update_of_ne (show rKk ≠ rKm1 by decide),
      e1 _ (show rKk ≠ rE by decide) (by decide) (by decide), hKk]
  have r3 := Good.set (x := encodeSystem I) (w := w) (st := s2) (r := rK1)
    (e := .add (rv rKk) (.const 1)) (by simp only [Ex.Fits, Ex.eval, rv, e2K]; omega)
  set s3 := s2.set rK1 ((Ex.add (rv rKk) (.const 1)).eval s2.env)
  have e3K : s3.env rKk = k := by
    simp only [s3, NSt.set_env, Function.update_of_ne (show rKk ≠ rK1 by decide)]; exact e2K
  have e3L1 : s3.env rL1 = ℓ + 1 := by
    simp only [s3, s2, NSt.set_env, Function.update_of_ne (show rL1 ≠ rK1 by decide),
      Function.update_of_ne (show rL1 ≠ rKm1 by decide)]
    rw [e1 _ (by decide) (by decide) (by decide), hL1]
  have r4 := mulS_good (x := encodeSystem I) (w := w) (Q := CQ) (dst := rPL) (a := rKk)
    (b := rL1) (j := rJ2) hw (by decide) (by decide) (by decide) (by decide) (by decide) s3 e3K
    e3L1 (by omega) (by omega)
  set s4 := (s3.set rPL (k * (ℓ + 1))).set rJ2 (ℓ + 1)
  have r5 := Good.set (x := encodeSystem I) (w := w) (st := s4) (r := rLB) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  set s5 := s4.set rLB ((Ex.const 0 : Ex CR).eval s4.env)
  have r6 := Good.set (x := encodeSystem I) (w := w) (st := s5) (r := rJ) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  set s6 := s5.set rJ ((Ex.const 0 : Ex CR).eval s5.env)
  have hpre := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))
  have e6J : s6.env rJ = 0 := by simp [s6, Ex.eval]
  have hI6 : p2Inv I st s6 := by
    refine ⟨by rw [e6J]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [(r2.seq (r3.seq (r4.seq (r5.seq r6)))).env_of (by decide)]
      exact rdNumFinal_env_r (by decide) (by decide) _
    · rw [hpre.env_of (by decide), hL]
    · rw [hpre.env_of (by decide), hKk]
    · rw [(r3.seq (r4.seq (r5.seq r6))).env_of (by decide)]; simp [s2]
    · rw [(r4.seq (r5.seq r6)).env_of (by decide)]; simp [s3, Ex.eval, rv, e2K]
    · rw [(r5.seq r6).env_of (by decide)]
      simp [s4, Function.update_of_ne (show rPL ≠ rJ2 by decide)]
    · rw [e6J, r6.env_of (by decide)]; simp [s5, Ex.eval, lbUpTo]
    · rw [e6J, schAt_zero, (r2.seq (r3.seq (r4.seq (r5.seq r6)))).pos_of (by decide)]
      show st.pos + (encodeNat I.schemas.length).length = _
      rw [hp]; rfl
    · rw [e6J]
      simp only [schRecsUpTo, List.take_zero, List.flatMap_nil, List.reverse_nil,
        List.nil_append, Function.update_eq_self]
      funext q
      exact hpre.stk_of rfl
    · exact hpre.out_of (by decide)
  obtain ⟨s7, r7, hI7, hc7⟩ := Good.loop_var (x := encodeSystem I) (w := w)
    (e := .lt (rv rJ) (rv rE)) (body := p2Sch) (p2Inv I st)
    (fun s => I.schemas.length - s.env rJ) (fun s => H I - s.pos) (400 * Ex.nodeCost w)
    (1000 * Ex.nodeCost w) (fun s hI => ⟨by
      obtain ⟨hj, hE', -⟩ := hI
      simp only [Ex.Fits, rv, hE']; omega,
      fun hc => p2Sch_good I hw hk hkH hℓ hS st hq1 hq2 s hI hc⟩) s6 hI6
  obtain ⟨hJ7, hE7, -, -, -, -, -, hLB7, hp7, hs7, ho7⟩ := hI7
  have hj : s7.env rJ = I.schemas.length := by
    simp only [Ex.eval, rv, hE7] at hc7; split_ifs at hc7 with h <;> omega
  have hall := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))
  refine ⟨s7, hall.mono ?_, by rw [hLB7, hj, lbUpTo_all], by rw [hs7, hj], ho7,
    by rw [hp7, hj, schAt_all], fun r hr => hall.env_of hr⟩
  have hφ : H I - s6.pos ≤ H I := by omega
  have hμ : I.schemas.length - s6.env rJ ≤ H I := by omega
  have hlE : (encodeNat I.schemas.length).length ≤ H I := by
    have := congrArg List.length hx
    simp only [List.length_drop, List.length_append] at this
    show _ ≤ (encodeSystem I).length; omega
  simp only [condCost, Ex.size, rv] at *
  generalize Ex.nodeCost w = N at *
  generalize unitCost w = U at *
  generalize H I - s6.pos = φ at *
  generalize I.schemas.length - s6.env rJ = μ at *
  generalize (encodeNat I.schemas.length).length = le at *
  generalize H I = h at *
  nlinarith

end Lax119563Proofs.Compiler

end Compiler_PSchLoop

/-! ### Formerly `Lax119563Proofs.Compiler.P4SzLoop` -/

section Compiler_P4SzLoop

/-!
# Pass `P4` (program): the schema-size scan

`p4SzS` (run at `schPos I` with the records `(schRecsUpTo I E).reverse` on `qSch`): moves the
records forward onto `qT`, and per schema reads its description (`p4SRead`), moves its
record back onto `qSch` (`p4SRec`) and pushes its class sizes (`p4SPush`); finally the
sizes are moved onto `qSzB` (**`p4SzS_good`**: `qSzB := schAll ++ qSzB`, `qSch` restored,
`rNt += Σ schAll`, cursor at `H`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The class sizes of the first `j` schemas. -/
noncomputable def schSzUpTo (j : ℕ) : List ℕ :=
  ((List.finRange I.schemas.length).take j).flatMap (schSizes I)

/-- The records of the schemas from `j` on. -/
noncomputable def schRecsFrom (j : ℕ) : List ℕ :=
  ((List.finRange I.schemas.length).drop j).flatMap (schRec I)

/-- The class sizes of all schemas. -/
noncomputable def schAll : List ℕ := (List.finRange I.schemas.length).flatMap (schSizes I)

lemma schSzUpTo_succ {j : ℕ} (hj : j < I.schemas.length) :
    schSzUpTo I (j + 1) = schSzUpTo I j ++ schSizes I ⟨j, hj⟩ := by
  rw [schSzUpTo, List.take_add_one, List.getElem?_eq_getElem (by simpa using hj)]
  simp (config := { decide := true }) [schSzUpTo]

lemma schSzUpTo_all : schSzUpTo I I.schemas.length = schAll I := by
  rw [schSzUpTo, List.take_of_length_le (by simp), schAll]

lemma schSzUpTo_sum_le (j : ℕ) : (schSzUpTo I j).sum ≤ (schAll I).sum := by
  have : schAll I = schSzUpTo I j ++
      ((List.finRange I.schemas.length).drop j).flatMap (schSizes I) := by
    rw [schAll, schSzUpTo, ← List.flatMap_append, List.take_append_drop]
  rw [this, List.sum_append]; omega

lemma schRecsFrom_cons {j : ℕ} (hj : j < I.schemas.length) :
    schRecsFrom I j = schRec I ⟨j, hj⟩ ++ schRecsFrom I (j + 1) := by
  rw [schRecsFrom, List.drop_eq_getElem_cons (by simpa using hj), List.flatMap_cons, schRecsFrom]
  simp

lemma schRecsFrom_sub (j : ℕ) : ∀ v ∈ schRecsFrom I j, v ∈ schRecsUpTo I I.schemas.length := by
  intro v hv
  simp only [schRecsFrom, List.mem_flatMap] at hv
  obtain ⟨e, he, hv⟩ := hv
  simp only [schRecsUpTo, List.mem_flatMap]
  exact ⟨e, by rw [List.take_of_length_le (by simp)]; exact List.mem_finRange e, hv⟩

lemma schRecsFrom_zero : schRecsFrom I 0 = schRecsUpTo I I.schemas.length := by
  rw [schRecsFrom, schRecsUpTo, List.drop_zero, List.take_of_length_le (by simp)]

lemma schRecsFrom_all : schRecsFrom I I.schemas.length = [] := by
  rw [schRecsFrom, List.drop_of_length_le (by simp)]; rfl

lemma schRec_split (e : Fin I.schemas.length) :
    schRec I e = (orsL (coordList (dom I e)) ++ [blkRows (coordList (dom I e))]) ++
      nEnt I e :: (coefSteps I e).length :: [] := by
  simp (config := { decide := true }) [schRec]

/-! ## The loop -/

/-- The body of the schema-size loop. -/
def p4SBody : CStm CR CQ :=
  .seq p4SRead (.seq p4SRec (.seq p4SPush (.set rJ (.add (rv rJ) (.const 1)))))

/-- The schema-size loop. -/
def p4SLoop : CStm CR CQ := .loop (.lt (rv rJ) (rv rE)) p4SBody

/-- The loop invariant (`st`: the state before the loop). -/
def p4SInv (st s : NSt CR CQ) : Prop :=
  s.env rE = I.schemas.length ∧ s.env rL1 = ℓ + 1 ∧ s.env rKk = k ∧
    s.env rJ ≤ I.schemas.length ∧ s.pos = schAt I (s.env rJ) ∧
    s.env rNt = st.env rNt + (schSzUpTo I (s.env rJ)).sum ∧
    s.stk = Function.update (Function.update (Function.update st.stk qT
      (schRecsFrom I (s.env rJ))) qSch (schRecsUpTo I (s.env rJ)).reverse) qSzA
      ((schSzUpTo I (s.env rJ)).reverse ++ st.stk qSzA) ∧
    s.out = st.out

/-- The potential of the loop. -/
noncomputable def p4SPot (st s : NSt CR CQ) : ℕ :=
  (H I - s.pos) + (st.env rNt + (schAll I).sum - s.env rNt)

lemma p4SBody_arith {N U P l d nE nC Z : ℕ} (hU : U ≤ N) (hl : l ≤ P) (hd : d ≤ Z)
    (hE : nE ≤ Z) (hC : nC ≤ Z) :
    150 * N * P + 200 * N + ((l + 1 + 5) * (12 * N) + ((2 * d + 2 * nE + nC + 10) * (30 * N) +
      (3 * N + U))) ≤ 200 * N * (P + Z) + 700 * N := by
  nlinarith

lemma p4SBody_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hk : 1 ≤ k)
    (st s : NSt CR CQ) (hrec : ∀ v ∈ schRecsUpTo I I.schemas.length, v < 2 ^ w)
    (hT : st.env rNt + (schAll I).sum + 8 < 2 ^ w)
    (hI : p4SInv I st s) (hc : (Ex.lt (rv rJ) (rv rE)).eval s.env ≠ 0) :
    ∃ s', Good (encodeSystem I) w p4SBody s s'
        (200 * Ex.nodeCost w * (p4SPot I st s - p4SPot I st s') + 700 * Ex.nodeCost w) ∧
      p4SInv I st s' ∧ I.schemas.length - s'.env rJ < I.schemas.length - s.env rJ ∧
      p4SPot I st s' ≤ p4SPot I st s := by
  have hU := CStm.nodeCost_ge w
  obtain ⟨hE, hL1, hK, hjE, hpos, hnt, hstk, hout⟩ := hI
  have hlt : s.env rJ < I.schemas.length := by
    by_contra h; apply hc; simp only [Ex.eval, rv, hE]; rw [if_neg h]
  set j := s.env rJ with hjdef
  set e : Fin I.schemas.length := ⟨j, hlt⟩
  set D := coordList (dom I e)
  -- reading
  obtain ⟨sA, rA', hAp, hAs, hAo, hAA, hAD⟩ := p4SRead_good I hw hH hk s hlt hpos hL1 hK
  have eA : ∀ r, wReg r p4SRead = false → sA.env r = s.env r := fun r h => rA'.env_of h
  -- the record
  have hTs : sA.stk qT = (orsL D ++ [blkRows D]) ++ nEnt I e :: (coefSteps I e).length ::
      schRecsFrom I (j + 1) := by
    rw [hAs, hstk, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self, schRecsFrom_cons I hlt, schRec_split]
    simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl
  have hmem : ∀ v ∈ schRecsFrom I j, v < 2 ^ w := fun v hv => hrec v (schRecsFrom_sub I j v hv)
  rw [schRecsFrom_cons I hlt, schRec_split] at hmem
  obtain ⟨sB, rB, hBs, hBe, hBc, hBp, hBo, hBf⟩ := p4SRec_good (x := encodeSystem I) (w := w)
    sA (orsL D ++ [blkRows D]) (schRecsFrom I (j + 1)) (nEnt I e) (coefSteps I e).length hTs
    (by rw [eA _ (by decide), hL1]; simp (config := { decide := true }) [length_orsL])
    (fun v hv => hmem v (List.mem_append_left _ (List.mem_append_left _ hv)))
    (hmem _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self ..))))
    (hmem _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
    (by
      have h1 := length_schemaDescription_ge I hk (sch I e)
      have h2 := schD_length_le I e
      simp only [schD] at h2
      simp only [List.length_append, length_orsL, List.length_singleton]; omega)
  -- the sizes
  have hszE : schSizes I e = szL (Matrix.isTern (sch I e)) D.length (nEnt I e) (coefSteps I e).length :=
    schSizes_eq_szL I e
  have hsumle := schSzUpTo_sum_le I (j + 1)
  rw [schSzUpTo_succ I hlt, List.sum_append] at hsumle
  replace hsumle : (schSzUpTo I j).sum + (schSizes I e).sum ≤ (schAll I).sum := hsumle
  obtain ⟨sC, rC', hCs, hCn, hCp, hCo⟩ := p4SPush_good (x := encodeSystem I) hw sB
    (Matrix.isTern (sch I e)) (d := D.length) (nE := nEnt I e) (nC := (coefSteps I e).length)
    (A := st.env rNt + (schSzUpTo I j).sum)
    (by rw [hBf _ (by decide) (by decide) (by decide) (by decide), hAA]; rfl)
    (by rw [hBf _ (by decide) (by decide) (by decide) (by decide), hAD])
    hBe hBc
    (by rw [hBf _ (by decide) (by decide) (by decide) (by decide), eA _ (by decide), hnt])
    (by rw [← hszE]; omega)
  have hCJ : sC.env rJ = j := by
    rw [rC'.env_of (by decide), hBf _ (by decide) (by decide) (by decide) (by decide),
      eA _ (by decide)]
  have rD' := Good.set (x := encodeSystem I) (w := w) (st := sC) (r := rJ)
    (e := .add (rv rJ) (.const 1)) (by
      have := E_le I
      simp only [Ex.Fits, Ex.eval, rv, hCJ]; omega)
  set s' := sC.set rJ ((Ex.add (rv rJ) (.const 1) : Ex CR).eval sC.env)
  have e'J : s'.env rJ = j + 1 := by simp (config := { decide := true }) [s', Ex.eval, rv, hCJ]
  have e' : ∀ r, r ≠ rJ → wReg r p4SPush = false → r ≠ rI → r ≠ rT → r ≠ rNe → r ≠ rNc →
      wReg r p4SRead = false → s'.env r = s.env r := fun r h0 h1 h2 h3 h4 h5 h6 => by
    simp only [s', NSt.set_env, Function.update_of_ne h0]
    rw [rC'.env_of h1, hBf r h2 h3 h4 h5, eA r h6]
  have hp' : s'.pos = s.pos + (encodeNats (schD I e)).length := by
    simp only [s', NSt.set_pos]; rw [hCp, hBp, hAp]
  have hn' : s'.env rNt = st.env rNt + (schSzUpTo I (j + 1)).sum := by
    simp only [s', NSt.set_env, Function.update_of_ne (show rNt ≠ rJ by decide)]
    rw [hCn, schSzUpTo_succ I hlt, List.sum_append, hszE]; ring
  have hposH : s.pos + (encodeNats (schD I e)).length ≤ H I := by
    have := schAt_le I (j + 1); rw [schAt_succ I hlt] at this; rw [hpos]; exact this
  have hZ : (schSizes I e).sum = (szL (Matrix.isTern (sch I e)) D.length (nEnt I e)
      (coefSteps I e).length).sum := by rw [hszE]
  have hpot : p4SPot I st s - p4SPot I st s' =
      (encodeNats (schD I e)).length + (szL (Matrix.isTern (sch I e)) D.length (nEnt I e)
        (coefSteps I e).length).sum := by
    unfold p4SPot; rw [hp', hn', hnt, schSzUpTo_succ I hlt, List.sum_append, hszE]; omega
  have hℓ : ℓ ≤ (encodeNats (schD I e)).length :=
    (length_schemaDescription_ge I hk (sch I e)).trans (length_le_encodeNats _)
  have hsz := szL_sum (Matrix.isTern (sch I e)) D.length (nEnt I e) (coefSteps I e).length
  refine ⟨s', (rA'.seq (rB.seq (rC'.seq rD'))).mono ?_, ⟨?_, ?_, ?_, ?_, ?_, by rw [e'J]; exact hn', ?_, ?_⟩, ?_, ?_⟩
  · rw [hpot]
    have hR : (orsL D ++ [blkRows D]).length = ℓ + 1 := by simp [length_orsL]
    rw [hR]
    have hdZ : D.length ≤ (szL (Matrix.isTern (sch I e)) D.length (nEnt I e)
        (coefSteps I e).length).sum := by rw [hsz]; split_ifs <;> omega
    have hEZ : nEnt I e ≤ (szL (Matrix.isTern (sch I e)) D.length (nEnt I e)
        (coefSteps I e).length).sum := by rw [hsz]; omega
    have hCZ : (coefSteps I e).length ≤ (szL (Matrix.isTern (sch I e)) D.length (nEnt I e)
        (coefSteps I e).length).sum := by rw [hsz]; omega
    have := p4SBody_arith (N := Ex.nodeCost w) (U := unitCost w)
      (P := (encodeNats (schD I e)).length) (l := ℓ) hU (by omega) hdZ hEZ hCZ
    simp only [Ex.size, rv]
    linarith
  · rw [e' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hE]
  · rw [e' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hL1]
  · rw [e' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hK]
  · rw [e'J]; omega
  · rw [e'J, hp', hpos, schAt_succ I hlt]
  · rw [e'J]
    simp only [s', NSt.set_stk]
    rw [hCs, hBs, hAs, hstk, schSzUpTo_succ I hlt, schRecsUpTo_succ I hlt, ← hszE]
    funext q
    by_cases h1 : q = qSzA
    · subst h1; simp (config := { decide := true }); rfl
    by_cases h2 : q = qSch
    · subst h2; simp (config := { decide := true }) [Function.update_of_ne (show qSch ≠ qSzA by decide),
        Function.update_of_ne (show qSch ≠ qT by decide), schRec_split]
      exact ⟨rfl, rfl, rfl, rfl⟩
    by_cases h3 : q = qT
    · subst h3; simp (config := { decide := true }) [Function.update_of_ne (show qT ≠ qSzA by decide),
        Function.update_of_ne (show qT ≠ qSch by decide)]
    simp (config := { decide := true }) [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
  · simp only [s', NSt.set_out]; rw [hCo, hBo, hAo, hout]
  · rw [e'J]; omega
  · have hZ' := hZ
    unfold p4SPot; rw [hp', hn', hnt, schSzUpTo_succ I hlt, List.sum_append]
    change _ + (_ - (_ + ((schSzUpTo I j).sum + (schSizes I e).sum))) ≤ _
    omega

end Lax119563Proofs.Compiler

end Compiler_P4SzLoop

/-! ### Formerly `Lax119563Proofs.Compiler.P4SzS` -/

section Compiler_P4SzS

/-!
# Pass `P4` (program): the schema-size scan, assembled

**`p4SzS_good`**: at `schPos I`, with the records `(schRecsUpTo I E).reverse` on `qSch` and
`qT = qSzA = []`, `p4SzS` puts `schAll I ++ qSzB` on `qSzB`, adds `Σ schAll` to `rNt`, keeps
every other stack and ends at `H`.
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- **The schema-size scan.** -/
def p4SzS : CStm CR CQ :=
  .seq (moveAllS qSch qT rT rP) (.seq (.set rJ (.const 0)) (.seq p4SLoop (moveAllS qSzA qSzB rT rP)))

lemma p4SLoop_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hk : 1 ≤ k)
    (st : NSt CR CQ) (hrec : ∀ v ∈ schRecsUpTo I I.schemas.length, v < 2 ^ w)
    (hT : st.env rNt + (schAll I).sum + 8 < 2 ^ w) (hI : p4SInv I st st) (hj : st.env rJ = 0) :
    ∃ s', Good (encodeSystem I) w p4SLoop st s'
        (1000 * (H I + (schAll I).sum + 1) * Ex.nodeCost w) ∧ p4SInv I st s' ∧
      s'.env rJ = I.schemas.length := by
  have hU := CStm.nodeCost_ge w
  obtain ⟨s', r, hI', hc'⟩ := Good.loop_var (x := encodeSystem I) (w := w)
    (e := .lt (rv rJ) (rv rE)) (body := p4SBody) (p4SInv I st)
    (fun s => I.schemas.length - s.env rJ) (p4SPot I st) (200 * Ex.nodeCost w)
    (700 * Ex.nodeCost w) (fun s hI => ⟨by
      obtain ⟨hE, -, -, hj, -⟩ := hI
      have := E_le I
      simp only [Ex.Fits, rv, hE]; omega,
      fun hc => p4SBody_good I hw hH hk st s hrec hT hI hc⟩) st hI
  have hJ : s'.env rJ = I.schemas.length := by
    obtain ⟨hE, -, -, hj', -⟩ := hI'
    simp only [Ex.eval, rv, hE] at hc'; split_ifs at hc' with h <;> omega
  refine ⟨s', r.mono ?_, hI', hJ⟩
  have hE := E_le I
  have hpot : p4SPot I st st ≤ H I + (schAll I).sum := by unfold p4SPot; omega
  have hU' := CStm.unitCost_ge w
  have hc : condCost w (Ex.lt (rv rJ) (rv rE) : Ex CR) ≤ 4 * Ex.nodeCost w := by
    simp only [condCost, Ex.size, rv]; omega
  rw [hj, Nat.sub_zero]
  generalize condCost w (Ex.lt (rv rJ) (rv rE) : Ex CR) = c at *
  generalize Ex.nodeCost w = N at *
  generalize p4SPot I st st = φ at *
  generalize H I = h at *
  generalize (schAll I).sum = z at *
  generalize I.schemas.length = E at *
  have h1 : 200 * N * φ ≤ 200 * N * (h + z) := Nat.mul_le_mul_left _ hpot
  have h2 : E * (700 * N + c) ≤ h * (704 * N) := Nat.mul_le_mul hE (by omega)
  nlinarith

lemma p4SzS_arith {N U a b c h z : ℕ} (hU : U ≤ N) (ha : a ≤ c) (hb : b ≤ z) :
    (a + 1) * (10 * N) + (N + U + (1000 * (h + z + 1) * N + (b + 1) * (10 * N))) ≤
      2000 * (h + c + z + 1) * N := by
  nlinarith

/-- **The schema-size scan.** -/
theorem p4SzS_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hk : 1 ≤ k)
    (st : NSt CR CQ) (hb : st.Bdd w) (hpos : st.pos = schPos I)
    (hE : st.env rE = I.schemas.length) (hL1 : st.env rL1 = ℓ + 1) (hK : st.env rKk = k)
    (hSch : st.stk qSch = (schRecsUpTo I I.schemas.length).reverse) (hT0 : st.stk qT = [])
    (hA0 : st.stk qSzA = []) (hT : st.env rNt + (schAll I).sum + 8 < 2 ^ w) :
    ∃ st', Good (encodeSystem I) w p4SzS st st'
        (2000 * (H I + (schRecsUpTo I I.schemas.length).length + (schAll I).sum + 1) *
          Ex.nodeCost w) ∧
      st'.stk = Function.update st.stk qSzB (schAll I ++ st.stk qSzB) ∧
      st'.env rNt = st.env rNt + (schAll I).sum ∧ st'.pos = H I ∧ st'.out = st.out := by
  have hU := CStm.nodeCost_ge w
  have hrec : ∀ v ∈ schRecsUpTo I I.schemas.length, v < 2 ^ w := fun v hv =>
    hb.2 qSch v (by rw [hSch]; exact List.mem_reverse.mpr hv)
  have hp0 : st.pos ≤ (encodeSystem I).length := by
    rw [hpos]; have := schAt_le I 0; rw [schAt_zero] at this; exact this
  obtain ⟨s1, r1, h1s, h1p, h1o, h1e⟩ := moveAllS_good (x := encodeSystem I) hw (q := qSch)
    (q' := qT) (t := rT) (f := rP) (by decide) (by decide) st hb
  have r2 := Good.set (x := encodeSystem I) (w := w) (st := s1) (r := rJ) (e := .const 0)
    (by simp only [Ex.Fits]; positivity)
  set s2 := s1.set rJ ((Ex.const 0 : Ex CR).eval s1.env)
  have e2 : ∀ r, r ≠ rJ → r ≠ rT → r ≠ rP → s2.env r = st.env r := fun r h1 h2 h3 => by
    simp only [s2, NSt.set_env, Function.update_of_ne h1]; exact h1e r h2 h3
  have e2J : s2.env rJ = 0 := by simp (config := { decide := true }) [s2, Ex.eval]
  have e2s : s2.stk = Function.update (Function.update st.stk qSch []) qT
      (schRecsUpTo I I.schemas.length) := by
    show s1.stk = _; rw [h1s, hSch, hT0, List.reverse_reverse, List.append_nil]
  have hI2 : p4SInv I s2 s2 := by
    refine ⟨by rw [e2 _ (by decide) (by decide) (by decide), hE],
      by rw [e2 _ (by decide) (by decide) (by decide), hL1],
      by rw [e2 _ (by decide) (by decide) (by decide), hK], by rw [e2J]; omega,
      by rw [e2J, schAt_zero]; show s1.pos = _; rw [h1p, hpos],
      by rw [e2J]; simp (config := { decide := true }) [schSzUpTo], ?_, rfl⟩
    rw [e2J, schRecsFrom_zero]
    simp only [schSzUpTo, List.take_zero, List.flatMap_nil, List.reverse_nil, List.nil_append,
      schRecsUpTo, List.take_zero]
    funext q
    by_cases h1 : q = qSzA
    · subst h1; simp
    by_cases h2 : q = qSch
    · subst h2; simp (config := { decide := true }) [e2s, Function.update_of_ne (show qSch ≠ qSzA by decide),
        Function.update_of_ne (show qSch ≠ qT by decide)]
    by_cases h3 : q = qT
    · subst h3; simp (config := { decide := true }) [e2s, Function.update_of_ne (show qT ≠ qSzA by decide),
        Function.update_of_ne (show qT ≠ qSch by decide), schRecsUpTo]
    simp (config := { decide := true }) [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
  have hT2 : s2.env rNt + (schAll I).sum + 8 < 2 ^ w := by
    rw [e2 _ (by decide) (by decide) (by decide)]; exact hT
  obtain ⟨s3, r3, hI3, hJ3⟩ := p4SLoop_good I hw hH hk s2 hrec hT2 hI2 e2J
  obtain ⟨-, -, -, -, h3p, h3n, h3s, h3o⟩ := hI3
  rw [hJ3, schAt_all, schSzUpTo_all, schRecsFrom_all] at *
  have r13 := r1.seq (r2.seq r3)
  have hb3 := r13.bdd hw hb hp0
  obtain ⟨s4, r4, h4s, h4p, h4o, h4e⟩ := moveAllS_good (x := encodeSystem I) hw (q := qSzA)
    (q' := qSzB) (t := rT) (f := rP) (by decide) (by decide) s3 hb3.1
  have e3A : s3.stk qSzA = (schAll I).reverse := by
    rw [h3s]; simp (config := { decide := true }) [e2s, hA0, Function.update_of_ne (show qSzA ≠ qT by decide),
      Function.update_of_ne (show qSzA ≠ qSch by decide)]
  refine ⟨s4, (r1.seq (r2.seq (r3.seq r4))).mono ?_, ?_, ?_, by rw [h4p, h3p], by rw [h4o, h3o]; show s1.out = _; exact h1o⟩
  · rw [e3A, List.length_reverse]
    simp only [Ex.size]
    have := p4SzS_arith (N := Ex.nodeCost w) (U := unitCost w) (a := (st.stk qSch).length)
      (b := (schAll I).length) (c := (schRecsUpTo I I.schemas.length).length) (h := H I)
      (z := (schAll I).sum) hU (by rw [hSch, List.length_reverse])
      (by
        have : ∀ v ∈ schAll I, 1 ≤ v := by
          intro v hv
          simp only [schAll, List.mem_flatMap] at hv
          obtain ⟨e, -, hv⟩ := hv
          rw [schSizes_eq_szL] at hv
          simp only [szL, jlSizes, List.mem_append, List.mem_flatten, List.mem_replicate] at hv
          rcases hv with (((⟨l, ⟨-, rfl⟩, hl⟩ | ⟨-, rfl⟩) | ⟨l, ⟨-, rfl⟩, hl⟩) | ⟨-, rfl⟩) | ⟨-, rfl⟩
          all_goals first | omega | (split_ifs at hl <;> simp at hl <;> omega)
        calc (schAll I).length = ((schAll I).map fun _ => 1).sum := by simp
          _ ≤ (schAll I).sum := by
            have := List.sum_le_sum (l := schAll I) (f := fun _ => 1) (g := id)
              (fun v hv => this v hv)
            simpa using this)
    omega
  · rw [h4s, e3A, List.reverse_reverse, h3s]
    funext q
    by_cases h0 : q = qSzB
    · subst h0; simp (config := { decide := true }) [e2s, Function.update_of_ne (show qSzB ≠ qSzA by decide),
        Function.update_of_ne (show qSzB ≠ qT by decide),
        Function.update_of_ne (show qSzB ≠ qSch by decide)]
    by_cases h1 : q = qSzA
    · subst h1; simp (config := { decide := true }) [hA0]
    by_cases h2 : q = qSch
    · subst h2; simp (config := { decide := true }) [hSch]
    by_cases h3 : q = qT
    · subst h3; simp (config := { decide := true }) [hT0, Function.update_of_ne (show qT ≠ qSzB by decide)]
    simp (config := { decide := true }) [Function.update_of_ne h0, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3, e2s]
  · rw [h4e _ (by decide) (by decide), h3n, e2 _ (by decide) (by decide) (by decide)]

end Lax119563Proofs.Compiler

end Compiler_P4SzS

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchB1` -/

section Compiler_P4SchB1

/-!
# Pass `P4`, schema part: the schema body, reading the header

* registers of the schema body: `r4NE` (`nEnt`), `r4NC` (`|coefSteps|`), `r4SuB` (sum base),
  `r4TrB` (track base); the schema base is kept in `r4SB`, the schema index in `rJ`;
* `p4Rd`: read the arity (→ `r4Tn`), skip the locations, read `|D|` (→ `r4D`)
  (**`p4Rd_good`**); `schD_len`: the length of a schema description by parts.
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-- `nEnt` of the current schema. -/
def r4NE : Fin CR := 14
/-- `|coefSteps|` of the current schema. -/
def r4NC : Fin CR := 15
/-- The sum base of the current schema. -/
def r4SuB : Fin CR := 38
/-- The track base of the current schema. -/
def r4TrB : Fin CR := 39

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The header of a schema description: arity, locations, `|D|`. -/
noncomputable def hdrL (e : Fin I.schemas.length) : ℕ :=
  (encodeNat (arity (sch I e))).length + (encodeNats (schLocs (sch I e))).length +
    (encodeNat (cL I e).length).length

/-- The permutation words of a schema. -/
noncomputable def permsL (e : Fin I.schemas.length) : List ℕ :=
  (schPerms (sch I e)).flatMap permDescription

lemma schD_split (e : Fin I.schemas.length) :
    schD I e = arity (sch I e) :: schLocs (sch I e) ++
      ((cL I e).length :: (cL I e).flatMap cdesc) ++ permsL I e := by
  rw [schD, schemaDescription_eq']; rfl

lemma schD_len (e : Fin I.schemas.length) :
    (encodeNats (schD I e)).length = hdrL I e + (encodeNats ((cL I e).flatMap cdesc)).length +
      (encodeNats (permsL I e)).length := by
  rw [schD_split]
  simp only [hdrL, List.cons_append, encNats_cons, List.append_assoc, encodeNats_append,
    List.length_append]
  ring

lemma length_permsL (e : Fin I.schemas.length) :
    (permsL I e).length = arity (sch I e) * (k * (ℓ + 1)) := by
  rw [permsL, length_perms]; ring

/-- Read the header of the schema at the cursor. -/
def p4Rd : CStm CR CQ :=
  .seq (rdNumS rc1 rP rT) (.seq (.set r4Tn (.lt (.const 2) (rv rc1)))
    (.seq (skipNumsS rc1 rc2 rT) (rdNumS r4D rP rT)))

lemma arity_eq (s : Schema k ℓ I.numLocations) :
    arity s = 2 + tnN (Matrix.isTern s) := by
  unfold arity tnN; split_ifs <;> rfl

set_option maxHeartbeats 4000000 in
lemma p4Rd_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (s : NSt CR CQ) {j : ℕ}
    (hj : j < I.schemas.length) (hpos : s.pos = schAt I j) :
    ∃ s', Good (encodeSystem I) w p4Rd s s' (100 * Ex.nodeCost w * (hdrL I ⟨j, hj⟩ + 1)) ∧
      s'.pos = s.pos + hdrL I ⟨j, hj⟩ ∧
      (encodeSystem I).drop s'.pos = encodeNats ((cL I ⟨j, hj⟩).flatMap cdesc) ++
        (encodeNats (permsL I ⟨j, hj⟩) ++ encodeNats (schsSuf I (j + 1))) ∧
      s'.stk = s.stk ∧ s'.out = s.out ∧ s'.env r4Tn = tnN (Matrix.isTern (sch I ⟨j, hj⟩)) ∧
      s'.env r4D = (cL I ⟨j, hj⟩).length ∧
      ∀ r, r ∉ [rc1, rc2, rP, rT, r4Tn, r4D] → s'.env r = s.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hH2 : 2 * (H I + 1) ≤ 2 ^ w := by omega
  have hDH := schD_le_H I ⟨j, hj⟩
  rw [schD_len] at hDH
  have hpH : s.pos + (encodeNats (schD I ⟨j, hj⟩)).length ≤ H I := by
    have := schAt_le I (j + 1); rw [schAt_succ I hj] at this; rw [hpos]; exact this
  rw [schD_len] at hpH
  unfold hdrL at hDH hpH
  set e : Fin I.schemas.length := ⟨j, hj⟩
  set sc := sch I e
  set a := arity sc
  set locs := schLocs sc
  set d := (cL I e).length
  set cs := (cL I e).flatMap cdesc
  set perms := permsL I e
  set rest := encodeNats (schsSuf I (j + 1))
  have hx : (encodeSystem I).drop s.pos = encodeNat a ++ (encodeNats locs ++ (encodeNat d ++
      (encodeNats cs ++ (encodeNats perms ++ rest)))) := by
    rw [hpos, drop_schAt, schsSuf_cons I hj, encodeNats_append, schD_split]
    simp only [List.cons_append, encNats_cons, List.append_assoc, encodeNats_append]; rfl
  have hla : locs.length = a := length_schLocs sc
  have ha23 : 2 ≤ a ∧ a ≤ 3 := by simp only [a, arity]; split_ifs <;> omega
  have hlo := length_le_encodeNats locs
  have hd1 := length_le_encodeNats cs
  have hdcs : d ≤ cs.length := by
    simp only [cs, d, List.length_flatMap, length_cdesc]
    simp only [List.map_const', List.sum_replicate, smul_eq_mul]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hdH : d ≤ H I := by omega
  -- reading the arity
  have r1 := rdNumS_good (Q := CQ) hw (r := rc1) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s a _ hx (bits_lt_of_le (by have := three_le_H I; omega) hH2)
  set s1 := rdNumFinal s rc1 rP rT a
  have e1A : s1.env rc1 = a := rdNumFinal_env_r (by decide) (by decide) a
  have r2 := Good.set (x := encodeSystem I) (w := w) (st := s1) (r := r4Tn)
    (e := .lt (.const 2) (rv rc1)) (by
      simp only [Ex.Fits, rv, e1A]; constructor <;> omega)
  set s2 := s1.set r4Tn ((Ex.lt (.const 2) (rv rc1) : Ex CR).eval s1.env)
  have e2T : s2.env r4Tn = tnN (Matrix.isTern sc) := by
    simp only [s2, NSt.set_env, Function.update_self, Ex.eval, rv, e1A, a, arity, tnN]
    split_ifs <;> omega
  have e2A : s2.env rc1 = a := by
    simp only [s2, NSt.set_env, Function.update_of_ne (show rc1 ≠ r4Tn by decide)]; exact e1A
  -- skipping the locations
  obtain ⟨s3, r3, h3s, h3p, h3o, h3f⟩ := skipNumsS_good (Q := CQ) hw (n := rc1) (i := rc2)
    (t := rT) (by decide) (by decide) (by decide) s2 locs _
    (by show (encodeSystem I).drop s1.pos = _
        simp only [s1, rdNumFinal_pos]; rw [← List.drop_drop, hx, List.drop_left])
    (by rw [e2A, hla]) (by have := e2A; have := hla; omega)
  -- reading `|D|`
  have r4 := rdNumS_good (Q := CQ) hw (r := r4D) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s3 d _ (by
      rw [h3p]; show (encodeSystem I).drop (s1.pos + _) = _
      simp only [s1, rdNumFinal_pos]
      rw [← List.drop_drop, ← List.drop_drop, hx, List.drop_left, List.drop_left])
    (bits_lt_of_le hdH hH2)
  set s4 := rdNumFinal s3 r4D rP rT d
  have hp4 : s4.pos = s.pos + hdrL I e := by
    simp only [s4, rdNumFinal_pos]; rw [h3p]; show s1.pos + _ + _ = _
    simp only [s1, rdNumFinal_pos, hdrL]; ring
  refine ⟨s4, (r1.seq (r2.seq (r3.seq r4))).mono ?_, hp4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Ex.size, rv]
    have hl2 : (encodeNats locs).length + locs.length ≤ 2 * (encodeNats locs).length := by omega
    unfold hdrL
    generalize Ex.nodeCost w = N at *
    generalize unitCost w = U at *
    generalize (encodeNat (arity (sch I e))).length = la at *
    generalize (encodeNats (schLocs (sch I e))).length = llo at *
    generalize (encodeNat (cL I e).length).length = ld at *
    nlinarith
  · have hh : hdrL I e = (encodeNat a ++ (encodeNats locs ++ encodeNat d)).length := by
      simp only [hdrL, List.length_append]; ring
    rw [hp4, hh, ← List.drop_drop, hx,
      show encodeNat a ++ (encodeNats locs ++ (encodeNat d ++ (encodeNats cs ++
        (encodeNats perms ++ rest)))) = (encodeNat a ++ (encodeNats locs ++ encodeNat d)) ++
        (encodeNats cs ++ (encodeNats perms ++ rest)) by simp, List.drop_left]
  · simp only [s4, rdNumFinal_stk]; rw [h3s]; rfl
  · simp only [s4, rdNumFinal_out]; rw [h3o]; rfl
  · rw [rdNumFinal_env_ne (by decide) (by decide) (by decide), h3f _ (by decide) (by decide)]
    exact e2T
  · exact rdNumFinal_env_r (by decide) (by decide) d
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
    rw [rdNumFinal_env_ne h6 h3 h4, h3f r h2 h4]
    simp only [s2, NSt.set_env, Function.update_of_ne h5, s1]
    rw [rdNumFinal_env_ne h1 h3 h4]

end Lax119563Proofs.Compiler

end Compiler_P4SchB1

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchB2` -/

section Compiler_P4SchB2

/-!
# Pass `P4`, schema part: the schema body, the record and the section bases

* `p4OrS`: move the `ℓ` OR bits of the record from `qS2` to `qOrsB`, summing them in `r4R2`
  (**`p4OrS_good`**);
* `p4Rec`: the record transfer (`qOrsF := orsL`, `r4BR, r4NE, r4NC`, `r4R2 := 2 (b + Σ ors)`)
  (**`p4Rec_good`**);
* `p4Bas`: the section bases (`r4H := r4SB`, `r4SuB, r4TrB, r4SP, r4TP`, `r4K, r4Dist := 0`)
  (**`p4Bas_good`**).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-! ## The OR bits -/

/-- One OR bit. -/
def p4OrB : CStm CR CQ :=
  .seq (.pop qS2 rT) (.seq (.push qOrsB (rv rT)) (.seq (.set r4R2 (.add (rv r4R2) (rv rT)))
    (.set rc1 (.add (rv rc1) (.const 1)))))

/-- The OR bits of the record. -/
def p4OrS : CStm CR CQ :=
  .seq (.set rc1 (.const 0)) (.seq (.set r4R2 (.const 0)) (.loop (.lt (rv rc1) (rv rL)) p4OrB))

lemma sum_take_le_length (L : List ℕ) (hL : ∀ v ∈ L, v ≤ 1) (i : ℕ) :
    (L.take i).sum ≤ i := by
  induction L generalizing i with
  | nil => simp
  | cons a t ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.take_succ_cons, List.sum_cons]
      have h1 := hL a (by simp)
      have h2 := ih (fun v hv => hL v (by simp [hv])) i
      omega

set_option maxHeartbeats 4000000 in
lemma p4OrS_good {x : List Bool} {w : ℕ} (s : NSt CR CQ) (L R' : List ℕ)
    (hS : s.stk qS2 = L ++ R') (hL : s.env rL = L.length) (hL1 : ∀ v ∈ L, v ≤ 1)
    (hw : L.length + 2 < 2 ^ w) :
    ∃ s', Good x w p4OrS s s' ((L.length + 1) * (30 * Ex.nodeCost w)) ∧
      s'.stk = Function.update (Function.update s.stk qS2 R') qOrsB (L.reverse ++ s.stk qOrsB) ∧
      s'.env r4R2 = L.sum ∧ s'.pos = s.pos ∧ s'.out = s.out ∧
      ∀ r, r ≠ rT → r ≠ rc1 → r ≠ r4R2 → s'.env r = s.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  set n := L.length with hn
  have r1 := Good.set (x := x) (w := w) (st := s) (r := rc1) (e := .const 0)
    (by simp only [Ex.Fits]; positivity)
  set s1 := s.set rc1 ((Ex.const 0 : Ex CR).eval s.env)
  have r2 := Good.set (x := x) (w := w) (st := s1) (r := r4R2) (e := .const 0)
    (by simp only [Ex.Fits]; positivity)
  set s2 := s1.set r4R2 ((Ex.const 0 : Ex CR).eval s1.env)
  set P : ℕ → NSt CR CQ → Prop := fun i t => t.env rc1 = i ∧ t.env r4R2 = (L.take i).sum ∧
    t.stk = Function.update (Function.update s.stk qS2 (L.drop i ++ R')) qOrsB
      ((L.take i).reverse ++ s.stk qOrsB) ∧ t.pos = s.pos ∧ t.out = s.out ∧
    ∀ r, r ≠ rT → r ≠ rc1 → r ≠ r4R2 → t.env r = s.env r with hP
  have hP0 : P 0 s2 := by
    refine ⟨by simp +decide [s2, s1, Ex.eval], by simp [s2, Ex.eval], ?_, rfl, rfl, ?_⟩
    · simp only [List.drop_zero, List.take_zero, List.reverse_nil, List.nil_append, ← hS]
      simp [s2, s1]
    · intro r h1 h2 h3; simp [s2, s1, Function.update_of_ne h2, Function.update_of_ne h3]
  have hstep : ∀ i < n, ∀ t, P i t → (Ex.lt (rv rc1) (rv rL) : Ex CR).Fits w t.env ∧
      (Ex.lt (rv rc1) (rv rL) : Ex CR).eval t.env ≠ 0 ∧
      ∃ t', Good x w p4OrB t t' (20 * Ex.nodeCost w) ∧ P (i + 1) t' := by
    rintro i hi t ⟨e1, e2, e3, e4, e5, e6⟩
    have eL : t.env rL = n := by rw [e6 _ (by decide) (by decide) (by decide), hL]
    have hsum := sum_take_le_length L hL1 i
    refine ⟨by simp only [Ex.Fits, rv, e1, eL]; omega, by
      simp only [Ex.eval, rv, e1, eL]; rw [if_pos hi]; omega, ?_⟩
    have hti : t.stk qS2 = L[i] :: (L.drop (i + 1) ++ R') := by
      rw [e3, Function.update_of_ne (by decide), Function.update_self,
        List.drop_eq_getElem_cons hi]; rfl
    have hLi : L[i] ≤ 1 := hL1 _ (List.getElem_mem hi)
    have g1 := Good.pop (x := x) (w := w) (st := t) qS2 rT
    set t1 := (t.setS qS2 (t.stk qS2).tail).set rT ((t.stk qS2).headD 0)
    have f1T : t1.env rT = L[i] := by simp [t1, hti]
    have g2 := Good.push (x := x) (w := w) (st := t1) (q := qOrsB) (e := rv rT)
      (by simp only [Ex.Fits, rv, f1T]; omega)
    set t2 := t1.setS qOrsB ((rv rT : Ex CR).eval t1.env :: t1.stk qOrsB)
    have f2R : t2.env r4R2 = (L.take i).sum := by
      simp +decide [t2, t1, Function.update_of_ne (show r4R2 ≠ rT by decide), e2]
    have f2T : t2.env rT = L[i] := f1T
    have g3 := Good.set (x := x) (w := w) (st := t2) (r := r4R2) (e := .add (rv r4R2) (rv rT))
      (by simp only [Ex.Fits, Ex.eval, rv, f2R, f2T]; omega)
    set t3 := t2.set r4R2 ((Ex.add (rv r4R2) (rv rT) : Ex CR).eval t2.env)
    have f3c : t3.env rc1 = i := by
      simp +decide [t3, t2, t1, Function.update_of_ne (show rc1 ≠ rT by decide), e1]
    have g4 := Good.set (x := x) (w := w) (st := t3) (r := rc1) (e := .add (rv rc1) (.const 1))
      (by simp only [Ex.Fits, Ex.eval, rv, f3c]; omega)
    refine ⟨_, (g1.seq (g2.seq (g3.seq g4))).mono ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Ex.size, rv]; omega
    · simp [Ex.eval, rv, f3c]
    · simp +decide [Function.update_of_ne (show r4R2 ≠ rc1 by decide), Ex.eval, rv, f2R, f2T,
        t3]
      rw [List.sum_take_succ _ _ hi]
    · simp only [t3, t2, t1, NSt.setS_stk, NSt.set_stk]
      rw [hti, e3]
      funext q
      by_cases hq : q = qOrsB
      · subst hq
        simp only [Function.update_self, Function.update_of_ne (show qOrsB ≠ qS2 by decide),
          Ex.eval, rv, NSt.set_env, NSt.setS_env, List.headD_cons, List.take_add_one,
          List.getElem?_eq_getElem hi, Option.toList_some, List.reverse_append,
          List.reverse_singleton, List.singleton_append, List.cons_append, List.nil_append]
      by_cases hq2 : q = qS2
      · subst hq2
        simp only [Function.update_self, Function.update_of_ne (show qS2 ≠ qOrsB by decide),
          List.tail_cons]
      simp only [Function.update_of_ne hq, Function.update_of_ne hq2]
    · simp [t3, t2, t1, e4]
    · simp [t3, t2, t1, e5]
    · intro r h1 h2 h3
      simp [t3, t2, t1, Function.update_of_ne h1, Function.update_of_ne h2,
        Function.update_of_ne h3, e6 r h1 h2 h3]
  have hend : ∀ t, P n t → (Ex.lt (rv rc1) (rv rL) : Ex CR).Fits w t.env ∧
      (Ex.lt (rv rc1) (rv rL) : Ex CR).eval t.env = 0 := by
    rintro t ⟨e1, -, -, -, -, e6⟩
    have eL : t.env rL = n := by rw [e6 _ (by decide) (by decide) (by decide), hL]
    exact ⟨by simp only [Ex.Fits, rv, e1, eL]; omega, by simp [Ex.eval, rv, e1, eL]⟩
  obtain ⟨s', g, e1, e2, e3, e4, e5, e6⟩ :=
    Good.loop_idxC (x := x) (w := w) n P (20 * Ex.nodeCost w) hstep hend s2 hP0
  refine ⟨s', (r1.seq (r2.seq g)).mono ?_, ?_, ?_, e4, e5, e6⟩
  · simp only [condCost, Ex.size, rv]
    nlinarith
  · rw [e3, List.drop_of_length_le (by omega), List.take_of_length_le (by omega)]; rfl
  · rw [e2, List.take_of_length_le (by omega)]

/-! ## The record -/

/-- The record transfer. -/
def p4Rec : CStm CR CQ :=
  .seq p4OrS (.seq (moveAllS qOrsB qOrsF rT rP) (.seq (.pop qS2 r4BR) (.seq (.pop qS2 r4NE)
    (.seq (.pop qS2 r4NC) (.seq (.set r4R2 (.add (rv r4R2) (rv r4BR)))
      (.set r4R2 (.add (rv r4R2) (rv r4R2))))))))

set_option maxHeartbeats 4000000 in
lemma p4Rec_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (s : NSt CR CQ) (L R' : List ℕ)
    (b nE nC : ℕ) (hS : s.stk qS2 = L ++ b :: nE :: nC :: R') (hL : s.env rL = L.length)
    (hL1 : ∀ v ∈ L, v ≤ 1) (hF : s.stk qOrsF = []) (hB : s.stk qOrsB = [])
    (hbd : s.Bdd w) (hp : s.pos ≤ x.length) (hbw : 2 * (L.length + b) + 2 < 2 ^ w) :
    ∃ s', Good x w p4Rec s s' ((L.length + 1) * (40 * Ex.nodeCost w) + 30 * Ex.nodeCost w) ∧
      s'.stk = Function.update (Function.update s.stk qS2 R') qOrsF L ∧
      s'.env r4BR = b ∧ s'.env r4NE = nE ∧ s'.env r4NC = nC ∧
      s'.env r4R2 = 2 * (b + L.sum) ∧ s'.pos = s.pos ∧ s'.out = s.out ∧
      ∀ r, r ∉ [rT, rP, rc1, r4R2, r4BR, r4NE, r4NC] → s'.env r = s.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hsum := sum_take_le_length L hL1 L.length
  rw [List.take_length] at hsum
  obtain ⟨s1, g1, h1s, h1R, h1p, h1o, h1f⟩ := p4OrS_good (x := x) (w := w) s L
    (b :: nE :: nC :: R') hS hL hL1 (by omega)
  have hb1 := (g1.bdd hw hbd hp).1
  obtain ⟨s2, g2, h2s, h2p, h2o, h2f⟩ := moveAllS_good (x := x) hw (q := qOrsB) (q' := qOrsF)
    (t := rT) (f := rP) (by decide) (by decide) s1 hb1
  have e2S : s2.stk qS2 = b :: nE :: nC :: R' := by
    rw [h2s, Function.update_of_ne (by decide), Function.update_of_ne (by decide), h1s,
      Function.update_of_ne (by decide), Function.update_self]
  have g3 := Good.pop (x := x) (w := w) (st := s2) qS2 r4BR
  set s3 := (s2.setS qS2 (s2.stk qS2).tail).set r4BR ((s2.stk qS2).headD 0)
  have g4 := Good.pop (x := x) (w := w) (st := s3) qS2 r4NE
  set s4 := (s3.setS qS2 (s3.stk qS2).tail).set r4NE ((s3.stk qS2).headD 0)
  have g5 := Good.pop (x := x) (w := w) (st := s4) qS2 r4NC
  set s5 := (s4.setS qS2 (s4.stk qS2).tail).set r4NC ((s4.stk qS2).headD 0)
  have e5R : s5.env r4R2 = L.sum := by
    simp +decide [s5, s4, s3]; rw [h2f _ (by decide) (by decide), h1R]
  have e5B : s5.env r4BR = b := by simp +decide [s5, s4, s3, e2S]
  have g6 := Good.set (x := x) (w := w) (st := s5) (r := r4R2) (e := .add (rv r4R2) (rv r4BR))
    (by simp only [Ex.Fits, Ex.eval, rv, e5R, e5B]; omega)
  set s6 := s5.set r4R2 ((Ex.add (rv r4R2) (rv r4BR) : Ex CR).eval s5.env)
  have e6R : s6.env r4R2 = L.sum + b := by simp [s6, Ex.eval, rv, e5R, e5B]
  have g7 := Good.set (x := x) (w := w) (st := s6) (r := r4R2) (e := .add (rv r4R2) (rv r4R2))
    (by simp only [Ex.Fits, Ex.eval, rv, e6R]; omega)
  refine ⟨_, (g1.seq (g2.seq (g3.seq (g4.seq (g5.seq (g6.seq g7)))))).mono ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · have hBl : (s1.stk qOrsB).length = L.length := by
      rw [h1s, Function.update_self, hB]; simp
    rw [hBl]; simp only [Ex.size, rv]; nlinarith
  · simp only [NSt.set_stk, s6, s5, s4, s3, NSt.setS_stk]
    rw [h2s, h1s]
    funext q
    by_cases h1 : q = qS2
    · subst h1; simp +decide [e2S]
    by_cases h2 : q = qOrsF
    · subst h2; simp +decide [hF, hB]
    by_cases h3 : q = qOrsB
    · subst h3; simp +decide [hB]
    simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
  · simp +decide [s6, s5, s4, s3, e2S]
  · simp +decide [s6, s5, s4, s3, e2S]
  · simp +decide [s6, s5, s4, s3, e2S]
  · simp [Ex.eval, rv, e6R]; ring
  · simp [s6, s5, s4, s3, h2p, h1p]
  · simp [s6, s5, s4, s3, h2o, h1o]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
    simp [s6, s5, s4, s3, Function.update_of_ne h4, Function.update_of_ne h5,
      Function.update_of_ne h6, Function.update_of_ne h7]
    rw [h2f r h1 h2, h1f r h1 h3 h4]

/-! ## The section bases -/

/-- `r4SB + 2 r4D + 4 r4NE`. -/
def sumEx2 : Ex CR :=
  .add (rv r4SB) (.add (.add (rv r4D) (rv r4D)) (.add (.add (rv r4NE) (rv r4NE))
    (.add (rv r4NE) (rv r4NE))))

/-- `r4SB + 6 r4D + 4 r4NE`. -/
def sumEx6 : Ex CR :=
  .add sumEx2 (.add (.add (rv r4D) (rv r4D)) (.add (rv r4D) (rv r4D)))

/-- The section bases. -/
def p4Bas : CStm CR CQ :=
  .seq (.set r4H (rv r4SB)) (.seq (.set r4K (.const 0)) (.seq (.set r4Dist (.const 0))
    (.seq (.ite (rv r4Tn)
        (.seq (.set r4SuB sumEx6) (.set r4TrB (.add (rv r4SuB) (.add (rv r4D) (rv r4D)))))
        (.seq (.set r4SuB sumEx2) (.set r4TrB (rv r4SuB))))
      (.seq (.set r4SP (rv r4SuB)) (.set r4TP (rv r4TrB))))))

/-- Registers written by `p4Bas`. -/
def basW : List (Fin CR) := [r4H, r4K, r4Dist, r4SuB, r4TrB, r4SP, r4TP]

set_option maxHeartbeats 4000000 in
lemma p4Bas_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (s : NSt CR CQ) {SB D NE T : ℕ}
    (eSB : s.env r4SB = SB) (eD : s.env r4D = D) (eNE : s.env r4NE = NE) (eT : s.env r4Tn = T)
    (hT : T ≤ 1) (hb : SB + 8 * D + 4 * NE < 2 ^ w) :
    ∃ s', Good x w p4Bas s s' (80 * Ex.nodeCost w) ∧
      s'.env r4H = SB ∧ s'.env r4K = 0 ∧ s'.env r4Dist = 0 ∧
      s'.env r4SuB = SB + D * (2 + 4 * T) + 4 * NE ∧
      s'.env r4TrB = SB + D * (2 + 4 * T) + 4 * NE + 2 * T * D ∧
      s'.env r4SP = SB + D * (2 + 4 * T) + 4 * NE ∧
      s'.env r4TP = SB + D * (2 + 4 * T) + 4 * NE + 2 * T * D ∧
      s'.stk = s.stk ∧ s'.pos = s.pos ∧ s'.out = s.out ∧
      ∀ r, r ∉ basW → s'.env r = s.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hlf : lf p4Bas = true := rfl
  have hsc : scost p4Bas ≤ 80 := by decide
  have h2 : (0 : ℕ) < 2 ^ w := by positivity
  have hT01 : T = 0 ∨ T = 1 := by omega
  have hfits : Fits x w p4Bas s := by
    rcases hT01 with rfl | rfl
    · simp +decide [p4Bas, CStm.Fits, CStm.exec, Ex.Fits, Ex.eval, rv, sumEx2, eSB, eD, eNE,
        eT, Function.update_of_ne]
      (repeat' apply And.intro) <;> omega
    · simp +decide [p4Bas, CStm.Fits, CStm.exec, Ex.Fits, Ex.eval, rv, sumEx2, sumEx6, eSB, eD,
        eNE, eT, Function.update_of_ne]
      (repeat' apply And.intro) <;> omega
  refine ⟨_, (good_lf hlf hfits).mono (Nat.mul_le_mul_right _ hsc), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  all_goals rcases hT01 with rfl | rfl
  all_goals simp +decide [p4Bas, CStm.exec, Ex.eval, rv, sumEx2, sumEx6, eSB, eD, eNE, eT,
      Function.update_of_ne, basW]
  all_goals try omega
  all_goals intro r h1 h2 h3 h4 h5 h6 h7
  all_goals simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h4, Function.update_of_ne h5, Function.update_of_ne h6,
      Function.update_of_ne h7]

end Lax119563Proofs.Compiler

end Compiler_P4SchB2

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchB3` -/

section Compiler_P4SchB3

/-!
# Pass `P4`, schema part: the schema body, between the sections and the end

* `p4Mid` (after section 1): rank codes `qRk → qRkF`, the record back onto `qSch` (OR bits from
  `qOrsF`, then `blkRows, nEnt, |coef|`), skip the permutations, `r4Prev := r4TP` (the
  coefficient base), `r4SP := r4SuB`, `r4TP := r4TrB`, `r4K := 0` (**`p4Mid_good`**);
* `p4End`: the next schema base `r4SB := r4Prev + 2 r4NC`, `rJ += 1` (**`p4End_good`**).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-- Between the sections. -/
def p4Mid : CStm CR CQ :=
  .seq (moveAllS qRk qRkF rT rP) (.seq (moveN qOrsF qSch rL rc1 rT)
    (.seq (.push qSch (rv r4BR)) (.seq (.push qSch (rv r4NE)) (.seq (.push qSch (rv r4NC))
      (.seq (.set rc1 (.add (.const 2) (rv r4Tn))) (.seq (mulS rc2 r4PL rc1 rc3)
        (.seq (skipNumsS rc2 rc3 rT) (.seq (.set r4Prev (rv r4TP)) (.seq (.set r4SP (rv r4SuB))
          (.seq (.set r4TP (rv r4TrB)) (.set r4K (.const 0))))))))))))

/-- Registers written by `p4Mid`. -/
def midW : List (Fin CR) := [rT, rP, rc1, rc2, rc3, r4Prev, r4SP, r4TP, r4K]

/-- Scratch registers of `p4Mid`. -/
def midW0 : List (Fin CR) := [rT, rP, rc1, rc2, rc3]

set_option maxHeartbeats 8000000 in
lemma p4Mid_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (s : NSt CR CQ) (Rk O perms : List ℕ)
    (rest : List Bool) {b nE nC T PL TP SuB TrB : ℕ}
    (hRk : s.stk qRk = Rk) (hO : s.stk qOrsF = O) (hL : s.env rL = O.length)
    (eB : s.env r4BR = b) (eNE : s.env r4NE = nE) (eNC : s.env r4NC = nC)
    (eT : s.env r4Tn = T) (hT : T ≤ 1) (ePL : s.env r4PL = PL) (eTP : s.env r4TP = TP)
    (eSu : s.env r4SuB = SuB) (eTr : s.env r4TrB = TrB)
    (hx : x.drop s.pos = encodeNats perms ++ rest) (hpl : perms.length = (2 + T) * PL)
    (hbd : s.Bdd w) (hp : s.pos ≤ x.length) (hPLw : 3 * PL + O.length + 2 < 2 ^ w) :
    ∃ s', Good x w p4Mid s s' (10 * Ex.nodeCost w * Rk.length + 12 * Ex.nodeCost w * O.length +
        40 * Ex.nodeCost w * (encodeNats perms).length + 300 * Ex.nodeCost w) ∧
      s'.stk = Function.update (Function.update (Function.update (Function.update s.stk qRk [])
        qRkF (Rk.reverse ++ s.stk qRkF)) qOrsF []) qSch (nC :: nE :: b :: O.reverse ++ s.stk qSch) ∧
      s'.pos = s.pos + (encodeNats perms).length ∧ s'.out = s.out ∧
      s'.env r4Prev = TP ∧ s'.env r4SP = SuB ∧ s'.env r4TP = TrB ∧ s'.env r4K = 0 ∧
      ∀ r, r ∉ midW → s'.env r = s.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
  -- the rank codes
  obtain ⟨s1, g1, h1s, h1p, h1o, h1f⟩ := moveAllS_good (x := x) hw (q := qRk) (q' := qRkF)
    (t := rT) (f := rP) (by decide) (by decide) s hbd
  have hb1 := (g1.bdd hw hbd hp).1
  have e1 : ∀ r, r ∉ midW0 → s1.env r = s.env r := fun r hr =>
    h1f r (fun h => hr (by simp [h, midW0])) (fun h => hr (by simp [h, midW0]))
  -- the OR bits back onto `qSch`
  have h1O : s1.stk qOrsF = O := by
    rw [h1s, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hO]
  obtain ⟨s2, g2, h2s, h2f⟩ := moveN_good (x := x) (w := w) (src := qOrsF) (dst := qSch)
    (cnt := rL) (i := rc1) (t := rT) (by decide) (by decide) (by decide) (by decide) s1
    (n := O.length) (by rw [e1 _ (by decide), hL]) (by rw [h1O]) (by omega)
    (fun v hv => hb1.2 qOrsF v (List.mem_of_mem_take hv))
  have hb2 := ((g1.seq g2).bdd hw hbd hp).1
  have e2 : ∀ r, r ∉ midW0 → s2.env r = s.env r := fun r hr => by
    rw [h2f.2.2 r (fun h => hr (by simp at h; rcases h with rfl | rfl <;> simp [midW0])), e1 r hr]
  have g3 := Good.push (x := x) (w := w) (st := s2) (q := qSch) (e := rv r4BR)
    (by simp only [Ex.Fits, rv]; exact hb2.1 _)
  set s3 := s2.setS qSch ((rv r4BR : Ex CR).eval s2.env :: s2.stk qSch)
  have g4 := Good.push (x := x) (w := w) (st := s3) (q := qSch) (e := rv r4NE)
    (by simp only [Ex.Fits, rv]; exact hb2.1 _)
  set s4 := s3.setS qSch ((rv r4NE : Ex CR).eval s3.env :: s3.stk qSch)
  have g5 := Good.push (x := x) (w := w) (st := s4) (q := qSch) (e := rv r4NC)
    (by simp only [Ex.Fits, rv]; exact hb2.1 _)
  set s5 := s4.setS qSch ((rv r4NC : Ex CR).eval s4.env :: s4.stk qSch)
  have e5 : ∀ r, s5.env r = s2.env r := fun r => rfl
  have e5T : s5.env r4Tn = T := by rw [e5, e2 _ (by decide), eT]
  have g6 := Good.set (x := x) (w := w) (st := s5) (r := rc1) (e := .add (.const 2) (rv r4Tn))
    (by simp only [Ex.Fits, Ex.eval, rv]; have := e5T; omega)
  set s6 := s5.set rc1 ((Ex.add (.const 2) (rv r4Tn) : Ex CR).eval s5.env)
  have e6c : s6.env rc1 = 2 + T := by simp [s6, Ex.eval, rv, e5T]
  have e6P : s6.env r4PL = PL := by
    simp only [s6, NSt.set_env, Function.update_of_ne (show r4PL ≠ rc1 by decide)]
    rw [e5, e2 _ (by decide), ePL]
  have g7 := mulS_good (x := x) (w := w) hw (dst := rc2) (a := r4PL) (b := rc1) (j := rc3)
    (by decide) (by decide) (by decide) (by decide) (by decide) s6 e6P e6c
    (by have : PL * (2 + T) ≤ 3 * PL := by nlinarith
        omega) (by omega)
  set s7 := (s6.set rc2 (PL * (2 + T))).set rc3 (2 + T)
  have hpos7 : s7.pos = s.pos := by
    simp only [s7, s6, s5, s4, s3, NSt.set_pos, NSt.setS_pos]; rw [h2f.1, h1p]
  obtain ⟨s8, g8, h8s, h8p, h8o, h8f⟩ := skipNumsS_good (Q := CQ) (x := x) hw (n := rc2) (i := rc3)
    (t := rT) (by decide) (by decide) (by decide) s7 perms rest (by rw [hpos7, hx])
    (by simp [s7, Function.update_of_ne (show rc2 ≠ rc3 by decide), hpl]; ring)
    (by rw [hpl]; nlinarith)
  have e8 : ∀ r, r ∉ midW0 → s8.env r = s.env r := fun r hr => by
    rw [h8f r (fun h => hr (by simp [h, midW0])) (fun h => hr (by simp [h, midW0]))]
    simp only [s7, s6, NSt.set_env]
    rw [Function.update_of_ne (fun h => hr (by simp [h, midW0])),
      Function.update_of_ne (fun h => hr (by simp [h, midW0])),
      Function.update_of_ne (fun h => hr (by simp [h, midW0])), e5, e2 r hr]
  have g9 := Good.set (x := x) (w := w) (st := s8) (r := r4Prev) (e := rv r4TP)
    (by simp only [Ex.Fits, rv]; exact ((g1.seq (g2.seq (g3.seq (g4.seq (g5.seq (g6.seq
      (g7.seq g8))))))).bdd hw hbd hp).1.1 _)
  set s9 := s8.set r4Prev ((rv r4TP : Ex CR).eval s8.env)
  have hb9 := ((g1.seq (g2.seq (g3.seq (g4.seq (g5.seq (g6.seq (g7.seq (g8.seq g9)))))))).bdd
    hw hbd hp).1
  have g10 := Good.set (x := x) (w := w) (st := s9) (r := r4SP) (e := rv r4SuB)
    (by simp only [Ex.Fits, rv]; exact hb9.1 _)
  set s10 := s9.set r4SP ((rv r4SuB : Ex CR).eval s9.env)
  have g11 := Good.set (x := x) (w := w) (st := s10) (r := r4TP) (e := rv r4TrB)
    (by simp only [Ex.Fits, rv, s10, NSt.set_env, Function.update_of_ne
          (show r4TrB ≠ r4SP by decide)]; exact hb9.1 _)
  set s11 := s10.set r4TP ((rv r4TrB : Ex CR).eval s10.env)
  have g12 := Good.set (x := x) (w := w) (st := s11) (r := r4K) (e := .const 0)
    (by simp only [Ex.Fits]; positivity)
  refine ⟨_, (g1.seq (g2.seq (g3.seq (g4.seq (g5.seq (g6.seq (g7.seq (g8.seq (g9.seq (g10.seq
    (g11.seq g12))))))))))).mono ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hRl : (s.stk qRk).length = Rk.length := by rw [hRk]
    rw [hRl]
    simp only [Ex.size, rv]
    have hT3 : 2 + T + 1 ≤ 4 := by omega
    have h7 : (2 + T + 1) * (12 * Ex.nodeCost w) ≤ 48 * Ex.nodeCost w := by nlinarith
    have hpe := length_le_encodeNats perms
    have h8 : ((encodeNats perms).length + perms.length + 1) * (20 * Ex.nodeCost w) ≤
        40 * Ex.nodeCost w * (encodeNats perms).length + 20 * Ex.nodeCost w := by nlinarith
    nlinarith
  · simp only [s11, s10, s9, NSt.set_stk]
    rw [h8s]
    simp only [s7, s6, s5, s4, s3, NSt.set_stk, NSt.setS_stk]
    rw [h2s, h1s]
    funext q
    by_cases hq : q = qSch
    · subst hq
      simp only [Function.update_self, movedStk_dst, Ex.eval, rv, NSt.setS_env]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
      rw [e2 _ (by decide), e2 _ (by decide), e2 _ (by decide), eB, eNE, eNC]
      simp only [Function.update_of_ne (show qOrsF ≠ qRkF by decide),
        Function.update_of_ne (show qOrsF ≠ qRk by decide), hO, List.take_length,
        List.cons_append]
    · simp only [Function.update_of_ne hq]
      by_cases hq2 : q = qOrsF
      · subst hq2
        simp only [Function.update_self, movedStk_src _ (show qOrsF ≠ qSch by decide),
          Function.update_of_ne (show qOrsF ≠ qRkF by decide),
          Function.update_of_ne (show qOrsF ≠ qRk by decide), hO, List.drop_length]
      · simp only [Function.update_of_ne hq2, movedStk_other _ hq2 hq, hRk]
  · simp only [s11, s10, s9, NSt.set_pos]; rw [h8p, hpos7]
  · simp only [s11, s10, s9, NSt.set_out]; rw [h8o]
    simp only [s7, s6, s5, s4, s3, NSt.set_out, NSt.setS_out]; rw [h2f.2.1, h1o]
  · simp only [s11, s10, s9, NSt.set_env, Ex.eval, rv]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_self, e8 _ (by decide), eTP]
  · simp only [s11, s10, s9, NSt.set_env, Ex.eval, rv]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self, Function.update_of_ne (by decide), e8 _ (by decide), eSu]
  · simp only [s11, s10, s9, NSt.set_env, Ex.eval, rv]
    rw [Function.update_of_ne (by decide), Function.update_self, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), e8 _ (by decide), eTr]
  · simp [Ex.eval]
  · intro r hr
    simp only [midW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hr
    simp only [s11, s10, s9, NSt.set_env]
    rw [Function.update_of_ne h9, Function.update_of_ne h8, Function.update_of_ne h7,
      Function.update_of_ne h6]
    exact e8 r (by simp [midW0, h1, h2, h3, h4, h5])

/-- The end of the schema body. -/
def p4End : CStm CR CQ :=
  .seq (.set r4SB (.add (rv r4Prev) (.add (rv r4NC) (rv r4NC))))
    (.set rJ (.add (rv rJ) (.const 1)))

lemma p4End_good {x : List Bool} {w : ℕ} (s : NSt CR CQ) {P nC j : ℕ}
    (eP : s.env r4Prev = P) (eC : s.env r4NC = nC) (eJ : s.env rJ = j)
    (hb : P + 2 * nC < 2 ^ w) (hj : j + 1 < 2 ^ w) :
    ∃ s', Good x w p4End s s' (20 * Ex.nodeCost w) ∧ s'.env r4SB = P + 2 * nC ∧
      s'.env rJ = j + 1 ∧ s'.stk = s.stk ∧ s'.pos = s.pos ∧ s'.out = s.out ∧
      ∀ r, r ≠ r4SB → r ≠ rJ → s'.env r = s.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have g1 := Good.set (x := x) (w := w) (st := s) (r := r4SB)
    (e := .add (rv r4Prev) (.add (rv r4NC) (rv r4NC)))
    (by simp only [Ex.Fits, Ex.eval, rv, eP, eC]; omega)
  set s1 := s.set r4SB ((Ex.add (rv r4Prev) (.add (rv r4NC) (rv r4NC)) : Ex CR).eval s.env)
  have e1J : s1.env rJ = j := by
    simp only [s1, NSt.set_env, Function.update_of_ne (show rJ ≠ r4SB by decide)]; exact eJ
  have g2 := Good.set (x := x) (w := w) (st := s1) (r := rJ) (e := .add (rv rJ) (.const 1))
    (by simp only [Ex.Fits, Ex.eval, rv, e1J]; omega)
  refine ⟨_, (g1.seq g2).mono ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · simp only [Ex.size, rv]; omega
  · simp [s1, Ex.eval, rv, eP, eC, Function.update_of_ne (show r4SB ≠ rJ by decide)]; ring
  · simp [Ex.eval, rv, e1J]
  · intro r h1 h2
    simp [s1, Function.update_of_ne h1, Function.update_of_ne h2]

end Lax119563Proofs.Compiler

end Compiler_P4SchB3

/-! ### Formerly `Lax119563Proofs.Compiler.PReqCols` -/

section Compiler_PReqCols

/-!
# Pass `P3`, request generation: the column loop of one argument

`p3Cols` runs `p3Col` over the columns of a domain (listed on `qDom2` as
`(cs.flatMap cdesc)`, blocks nondecreasing), pushing the requests
`colReqs u π cs s₀ t = [reqRec u π c (s₀ + r t) | (c, r) ∈ cs.zipIdx]` (**`p3Cols_good`**).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ}

/-- The requests of the columns `cs` for the argument `(u, π)`. -/
def colReqs (u : ℕ) (π : BlockPerm k ℓ) (cs : List (Coord k ℓ)) (s0 t : ℕ) : List (List ℕ) :=
  cs.zipIdx.map fun q => reqRec u π q.1 (s0 + q.2 * t)

lemma colReqs_take_succ (u : ℕ) (π : BlockPerm k ℓ) (cs : List (Coord k ℓ)) (s0 t : ℕ) {r : ℕ}
    (hr : r < cs.length) :
    colReqs u π (cs.take (r + 1)) s0 t = colReqs u π (cs.take r) s0 t ++
      [reqRec u π cs[r] (s0 + r * t)] := by
  rw [colReqs, colReqs, List.take_add_one, List.getElem?_eq_getElem hr, Option.toList_some,
    List.zipIdx_append, List.map_append]
  simp only [List.length_take, Nat.min_eq_left hr.le, List.zipIdx_cons, List.zipIdx_nil,
    List.map_cons, List.map_nil, zero_add]

/-- The block reached after `r` columns. -/
def curB (cs : List (Coord k ℓ)) (r : ℕ) : ℕ := ((cs.take r).getLast?.map fun c => (c.1 : ℕ)).getD 0

lemma curB_succ (cs : List (Coord k ℓ)) {r : ℕ} (hr : r < cs.length) :
    curB cs (r + 1) = cs[r].1 := by
  rw [curB, List.take_add_one, List.getElem?_eq_getElem hr, Option.toList_some,
    List.getLast?_append]
  simp only [List.getLast?_singleton, Option.some_or, Option.map_some, Option.getD_some]

lemma curB_le (cs : List (Coord k ℓ)) (hs : (cs.map fun c => (c.1 : ℕ)).Pairwise (· ≤ ·))
    {r : ℕ} (hr : r < cs.length) : curB cs r ≤ cs[r].1 := by
  rcases r with _ | r
  · simp [curB]
  · rw [curB_succ cs (by omega)]
    have := List.pairwise_iff_getElem.mp hs r (r + 1) (by simp; omega) (by simp; omega)
      (by omega)
    simpa using this

/-- The column loop. -/
def p3Cols : CStm CR CQ := .seq (.set rK (.const 0)) (.loop (.lt (rv rK) (rv rD)) p3Col)

lemma fL_lt (π : BlockPerm k ℓ) : ∀ v ∈ fL π, v < k := by
  intro v hv; simp only [fL, List.mem_map] at hv; obtain ⟨i, -, rfl⟩ := hv; exact (π.perm i).2

lemma dL_mem (π : BlockPerm k ℓ) : ∀ d ∈ dL π, d.length = ℓ ∧ ∀ v ∈ d, v ≤ 1 := by
  intro d hd; simp only [dL, List.mem_map] at hd; obtain ⟨i, -, rfl⟩ := hd
  exact ⟨length_blockDescription _, blockDescription_le _⟩

lemma cols_arith (N U k n ℓ : ℕ) (hU : U ≤ N) (hU' : 64 ≤ U) :
    1 * N + U + ((ℓ + 3) * (12 * N) * k + n * ((ℓ + 3) * (12 * N) + (ℓ + 2) * (40 * N) +
      ((1 + 1 + 1) * N + 1)) + ((1 + 1 + 1) * N + 1)) ≤ (k + n + 1) * ((ℓ + 3) * (60 * N)) := by
  have h1 : n * ((ℓ + 3) * (12 * N) + (ℓ + 2) * (40 * N) + ((1 + 1 + 1) * N + 1)) ≤
      n * ((ℓ + 3) * (60 * N)) := Nat.mul_le_mul_left _ (by nlinarith)
  have h2 : (ℓ + 3) * (12 * N) * k ≤ k * ((ℓ + 3) * (60 * N)) := by
    rw [mul_comm]; exact Nat.mul_le_mul_left _ (by nlinarith)
  have h3 : 1 * N + U + ((1 + 1 + 1) * N + 1) ≤ (ℓ + 3) * (60 * N) := by nlinarith
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **The column loop of one argument.** -/
lemma p3Cols_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (st : NSt CR CQ) (u : ℕ)
    (π : BlockPerm k ℓ) (cs : List (Coord k ℓ)) (s0 t : ℕ) (R D0 Q0 : List ℕ)
    (hs : (cs.map fun c => (c.1 : ℕ)).Pairwise (· ≤ ·)) (hk : 1 ≤ k)
    (hKw : k + 1 < 2 ^ w) (hℓw : ℓ + 1 < 2 ^ w) (huw : u < 2 ^ w) (hnw : cs.length + 1 < 2 ^ w)
    (hsw : s0 + cs.length * t < 2 ^ w)
    (hD : st.env rD = cs.length) (hX2 : st.stk qDom2 = cs.flatMap cdesc ++ R)
    (hDom : st.stk qDom = D0) (hAux : st.stk qAux = []) (hC : st.env rCur = 0)
    (hL : st.env rL = ℓ) (hU : st.env rU = u) (hS : st.env rSq = s0) (hT : st.env rStr = t)
    (hD2 : st.stk qDl2 = (dL π).flatten) (hF2 : st.stk qF2 = (fL π).drop 1)
    (hFi : st.env rFi = (fL π).getD 0 0) (hRec : st.stk qRec = Q0) :
    ∃ st', Good x w p3Cols st st' ((k + cs.length + 1) * ((ℓ + 3) * (60 * Ex.nodeCost w))) ∧
      st'.stk qDom2 = R ∧ st'.stk qDom = (cs.flatMap cdesc).reverse ++ D0 ∧
      st'.stk qDl2 = ((dL π).drop (curB cs cs.length)).flatten ∧
      st'.stk qF2 = (fL π).drop (curB cs cs.length + 1) ∧ st'.stk qAux = [] ∧
      st'.stk qRec = (colReqs u π cs s0 t).flatten.reverse ++ Q0 ∧
      (∀ q, q ≠ qDom2 → q ≠ qDom → q ≠ qDl2 → q ≠ qF2 → q ≠ qAux → q ≠ qRec → q ≠ qJunk →
        st'.stk q = st.stk q) ∧
      st'.pos = st.pos ∧ st'.out = st.out ∧
      ∀ r, wReg r p3Cols = false → st'.env r = st.env r := by
  have hU0 := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  set n := cs.length
  have r0 := Good.set (x := x) (w := w) (r := rK) (e := .const 0) (st := st)
    (by simp only [Ex.Fits]; omega)
  set s0' := st.set rK ((Ex.const 0 : Ex CR).eval st.env)
  set Inv : NSt CR CQ → Prop := fun s => s.env rK ≤ n ∧ s.env rD = n ∧ s.env rL = ℓ ∧
    s.env rU = u ∧ s.env rStr = t ∧ s.env rSq = s0 + s.env rK * t ∧
    s.env rCur = curB cs (s.env rK) ∧ s.env rFi = (fL π).getD (curB cs (s.env rK)) 0 ∧
    s.stk qDom2 = (cs.drop (s.env rK)).flatMap cdesc ++ R ∧
    s.stk qDom = ((cs.take (s.env rK)).flatMap cdesc).reverse ++ D0 ∧
    s.stk qDl2 = ((dL π).drop (curB cs (s.env rK))).flatten ∧
    s.stk qF2 = (fL π).drop (curB cs (s.env rK) + 1) ∧ s.stk qAux = [] ∧
    s.stk qRec = (colReqs u π (cs.take (s.env rK)) s0 t).flatten.reverse ++ Q0 ∧
    (∀ q, q ≠ qDom2 → q ≠ qDom → q ≠ qDl2 → q ≠ qF2 → q ≠ qAux → q ≠ qRec → q ≠ qJunk →
      s.stk q = st.stk q) ∧
    s.pos = st.pos ∧ s.out = st.out ∧ ∀ r, wReg r p3Cols = false → s.env r = st.env r
    with hInv
  have hloop := Good.loop_var (x := x) (w := w) (e := .lt (rv rK) (rv rD)) (body := p3Col)
    Inv (fun s => n - s.env rK) (fun s => k - s.env rCur) ((ℓ + 3) * (12 * Ex.nodeCost w))
    ((ℓ + 3) * (12 * Ex.nodeCost w) + (ℓ + 2) * (40 * Ex.nodeCost w)) (by
      intro s ⟨hk1, hd, hl, hu, ht, hsq, hcur, hfi, hx2, hdom, hdl, hf2, haux, hrec, hS, hp, ho,
        he⟩
      refine ⟨⟨by simp only [rv, Ex.Fits]; omega, by simp only [rv, Ex.Fits]; omega⟩, ?_⟩
      intro hcond
      have hlt : s.env rK < n := by simpa [rv, Ex.eval, hd] using hcond
      set r := s.env rK with hr
      have hrn : r < cs.length := hlt
      set c := cs[r]
      have hci : curB cs r ≤ (c.1 : ℕ) := curB_le cs hs hrn
      have hik : (c.1 : ℕ) < (fL π).length := by rw [length_fL]; exact c.1.2
      have hx2' : s.stk qDom2 = (c.1 : ℕ) :: blockDescription c.2 ++
          ((cs.drop (r + 1)).flatMap cdesc ++ R) := by
        rw [hx2, List.drop_eq_getElem_cons hrn, List.flatMap_cons]; simp [cdesc, c]
      have hrt : r * t + t ≤ n * t := by
        have : (r + 1) * t ≤ n * t := Nat.mul_le_mul_right _ (by omega)
        rw [add_one_mul] at this; exact this
      obtain ⟨s', r', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
        p3Col_good (x := x) hw s (blockDescription c.2) ((cs.drop (r + 1)).flatMap cdesc ++ R)
          (length_blockDescription _) (blockDescription_le _) (fL π) (dL π)
          (by rw [length_fL, length_dL]) hik hci (dL_mem π)
          (fun v hv => lt_trans (fL_lt π v hv) (by omega)) hℓw (by have := c.1.2; omega) huw
          (by omega) (by omega) hx2' haux hcur hl hu hsq ht hdl hf2 hfi
      have hc1 : curB cs (r + 1) = c.1 := curB_succ cs hrn
      have hK' : s'.env rK = r + 1 := h11
      refine ⟨s', r'.mono ?_, ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_⟩, by rw [hK']; omega, by rw [h8, hcur]; have := hci; omega⟩
      · rw [hcur, h8]
        have : k - curB cs r - (k - c.1) = c.1 - curB cs r := by
          have := c.1.2; omega
        rw [this]; nlinarith
      · rw [h14 _ (by decide), hd]
      · rw [h14 _ (by decide), hl]
      · rw [h14 _ (by decide), hu]
      · rw [h14 _ (by decide), ht]
      · rw [h10, hK']; ring
      · rw [h8, hK', hc1]
      · rw [h9, hK', hc1]
      · rw [h1, hK']
      · rw [h2, hK', hdom, List.take_add_one, List.getElem?_eq_getElem hrn, Option.toList_some,
          List.flatMap_append]
        simp [cdesc, c]
      · rw [h3, hK', hc1]
      · rw [h4, hK', hc1]
      · exact h5
      · rw [h6, hK', colReqs_take_succ _ _ _ _ _ hrn, hrec, reqRec_eq]
        simp [c]
      · intro q n1 n2 n3 n4 n5 n6 n7; rw [h7 q n1 n2 n3 n4 n5 n6 n7, hS q n1 n2 n3 n4 n5 n6 n7]
      · rw [h12, hp]
      · rw [h13, ho]
      · intro q hq
        rw [h14 q (by simp only [p3Cols, wReg, Bool.or_eq_false_iff] at hq; exact hq.2), he q hq])
    s0' ⟨by simp [s0', Ex.eval], by simp [s0', Function.update_of_ne (show rD ≠ rK by decide), hD],
      by simp [s0', Function.update_of_ne (show rL ≠ rK by decide), hL],
      by simp [s0', Function.update_of_ne (show rU ≠ rK by decide), hU],
      by simp [s0', Function.update_of_ne (show rStr ≠ rK by decide), hT],
      by simp [s0', Function.update_of_ne (show rSq ≠ rK by decide), hS, Ex.eval],
      by simp [s0', Function.update_of_ne (show rCur ≠ rK by decide), hC, Ex.eval, curB],
      by simp [s0', Function.update_of_ne (show rFi ≠ rK by decide), hFi, Ex.eval, curB],
      by simp [s0', Ex.eval, hX2], by simp [s0', Ex.eval, hDom], by simp [s0', Ex.eval, hD2, curB],
      by simp [s0', Ex.eval, hF2, curB], by simp [s0', hAux],
      by simp [s0', Ex.eval, hRec, colReqs], fun _ _ _ _ _ _ _ _ => rfl, rfl, rfl,
      fun r hr => by
        simp only [p3Cols, wReg, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
        simp [s0', Function.update_of_ne (Ne.symm hr.1)]⟩
  obtain ⟨s', r', ⟨hk1, hd, -, -, -, -, -, -, hx2, hdom, hdl, hf2, haux, hrec, hS, hp, ho, he⟩,
    hc⟩ := hloop
  have hkn : s'.env rK = n := by
    simp only [Ex.eval, rv, hd] at hc; split_ifs at hc with h <;> omega
  refine ⟨s', (r0.seq r').mono ?_, ?_, ?_, ?_, ?_, haux, ?_, hS, hp, ho, he⟩
  · have h0 : n - s0'.env rK = n := by simp [s0', Ex.eval]
    have h1 : k - s0'.env rCur = k := by
      simp [s0', Function.update_of_ne (show rCur ≠ rK by decide), hC]
    rw [h0, h1]; simp only [condCost, rv, Ex.size]
    exact cols_arith _ _ _ _ _ hU0 hU'
  · rw [hx2, hkn]; simp [n]
  · rw [hdom, hkn, List.take_of_length_le (le_of_eq rfl)]
  · rw [hdl, hkn]
  · rw [hf2, hkn]
  · rw [hrec, hkn, List.take_of_length_le (le_of_eq rfl)]

end Lax119563Proofs.Compiler

end Compiler_PReqCols

/-! ### Formerly `Lax119563Proofs.Compiler.PReqArg` -/

section Compiler_PReqArg

/-!
# Pass `P3`, request generation: one argument of a schema

`p3Arg` (at the description of the permutation `π` of the argument, with its location on top
of `qLs2` and the coordinates of the domain on `qDom2`) reads `f` and the shifts onto stacks,
pushes the requests of all columns (`p3Cols`) with the sequence numbers
`base + sqOff tern a |D| + r · (tern ? 3 : 1)`, restores the domain and discards the rest of
the permutation (**`p3Arg_good`**).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ}

/-- The sequence base (number of requests of the previous schemas). -/
def rSB : Fin CR := 37

/-- The first sequence number of argument `a`. -/
def sqOff (tern : Bool) (a d : ℕ) : ℕ := if tern then a else if a = 0 then d else 0

/-- The stride of the sequence numbers. -/
def sqStr (tern : Bool) : ℕ := if tern then 3 else 1

lemma seqOff_eq (tern : Bool) (d a r : ℕ) (ha : a < (if tern then 3 else 2)) :
    seqOff tern d a r = sqOff tern a d + r * sqStr tern := by
  unfold seqOff sqOff sqStr; split_ifs <;> omega

/-- Set the first sequence number. -/
def p3Seq : CStm CR CQ :=
  .ite (rv rTn) (.set rSq (.add (rv rSB) (rv rAi)))
    (.ite (.lt (rv rAi) (.const 1)) (.set rSq (.add (rv rSB) (rv rD))) (.set rSq (rv rSB)))

lemma p3Seq_good {x : List Bool} {w : ℕ} (st : NSt CR CQ) (tern : Bool) {a d b : ℕ}
    (hTn : st.env rTn = if tern then 1 else 0) (hAi : st.env rAi = a) (hD : st.env rD = d)
    (hB : st.env rSB = b) (hw : b + sqOff tern a d < 2 ^ w) (haw : a + 1 < 2 ^ w)
    (hdw : d < 2 ^ w) :
    Good x w p3Seq st (st.set rSq (b + sqOff tern a d)) (12 * Ex.nodeCost w) := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h1 : (1 : ℕ) < 2 ^ w := by omega
  unfold p3Seq
  cases tern with
  | true =>
    refine (CStm.Good.iteT (by simp only [Ex.Fits, rv, hTn]; split_ifs <;> omega) (by simp [rv, Ex.eval, hTn])
      (CStm.Good.set (by simp only [Ex.Fits, rv, Ex.eval, hB, hAi]; simp [sqOff] at hw; omega))).of_eq
      (by simp [Ex.eval, rv, hB, hAi, sqOff]) (by simp [condCost, Ex.size, rv]; omega)
  | false =>
    suffices h : Good x w (.ite (.lt (rv rAi) (.const 1)) (.set rSq (.add (rv rSB) (rv rD)))
        (.set rSq (rv rSB))) st (st.set rSq (b + sqOff false a d)) (8 * Ex.nodeCost w) from
      (CStm.Good.iteF (by simp only [Ex.Fits, rv, hTn]; split_ifs <;> omega) (by simp [rv, Ex.eval, hTn])
        h).mono (by simp [condCost, Ex.size, rv]; omega)
    by_cases ha : a = 0
    · refine (CStm.Good.iteT (by simp only [Ex.Fits, rv, hAi]; try omega) (by simp [rv, Ex.eval, hAi, ha])
        (CStm.Good.set (by simp only [Ex.Fits, rv, Ex.eval, hB, hD]; simp [sqOff, ha] at hw; omega))).of_eq
        (by simp [Ex.eval, rv, hB, hD, sqOff, ha]) (by simp [condCost, Ex.size, rv]; omega)
    · refine (CStm.Good.iteF (by simp only [Ex.Fits, rv, hAi]; try omega) (by simp [rv, Ex.eval, hAi]; omega)
        (CStm.Good.set (by simp only [Ex.Fits, rv, hB]; simp [sqOff, ha] at hw; omega))).of_eq
        (by simp [Ex.eval, rv, hB, sqOff, ha]) (by simp [condCost, Ex.size, rv]; omega)

/-- **One argument.** -/
def p3Arg : CStm CR CQ :=
  .seq (.pop qLs2 rU) (.seq (rdNumsS qF rKk rI rV rP rT) (.seq (moveAllS qF qF2 rT rT2)
    (.seq (rdNumsS qDl rKL rI rV rP rT) (.seq (moveAllS qDl qDl2 rT rT2)
      (.seq (.pop qF2 rFi) (.seq (.set rCur (.const 0)) (.seq p3Seq (.seq p3Cols
        (.seq (moveAllS qDom qDom2 rT rT2) (.seq (moveAllS qF2 qJunk rT rT2)
          (.seq (moveAllS qDl2 qJunk rT rT2) (.set rAi (.add (rv rAi) (.const 1))))))))))))))

lemma length_flatten_dL (π : BlockPerm k ℓ) : (dL π).flatten.length = k * ℓ := by
  rw [List.length_flatten]
  have : (dL π).map List.length = (dL π).map fun _ => ℓ :=
    List.map_congr_left fun d hd => (dL_mem π d hd).1
  rw [this, sum_map_const, length_dL]

lemma length_flatten_drop_le (L : List (List ℕ)) (c : ℕ) :
    (L.drop c).flatten.length ≤ L.flatten.length := by
  conv_rhs => rw [← List.take_append_drop c L]
  rw [List.flatten_append, List.length_append]; omega

lemma arg_arith (N U k n ℓ lf ld a b : ℕ) (hU : U ≤ N) (hU' : 64 ≤ U) (hk : 1 ≤ k)
    (hlf : k ≤ lf) (hld : k * ℓ ≤ ld) (ha : a ≤ k) (hb : b ≤ k * ℓ) :
    U + 1 + (lf + 2 * k + 1) * (20 * N) + (k + 1) * (10 * N) + (ld + 2 * (k * ℓ) + 1) * (20 * N)
      + (k * ℓ + 1) * (10 * N) + (U + 1) + (1 * N + U) + 12 * N
      + (k + n + 1) * ((ℓ + 3) * (60 * N)) + (n * (ℓ + 1) + 1) * (10 * N) + (a + 1) * (10 * N)
      + (b + 1) * (10 * N) + (3 * N + U) ≤ 600 * (lf + ld + n * (ℓ + 1) + 1) * N := by
  have hkl : 1 * ℓ ≤ k * ℓ := Nat.mul_le_mul_right ℓ hk
  have h1 : (k + n + 1) * (ℓ + 3) ≤ 6 * (k * ℓ + k) + 3 * (n * (ℓ + 1)) := by nlinarith
  have key : (k + n + 1) * ((ℓ + 3) * (60 * N)) ≤
      360 * (k * ℓ * N) + 360 * (k * N) + 180 * (n * (ℓ + 1) * N) := by
    have := Nat.mul_le_mul_right (60 * N) h1
    calc (k + n + 1) * ((ℓ + 3) * (60 * N)) = (k + n + 1) * (ℓ + 3) * (60 * N) := by ring
      _ ≤ (6 * (k * ℓ + k) + 3 * (n * (ℓ + 1))) * (60 * N) := this
      _ = _ := by ring
  have e2 : a * N ≤ k * N := Nat.mul_le_mul_right _ ha
  have e3 : b * N ≤ k * ℓ * N := Nat.mul_le_mul_right _ hb
  have e4 : k * N ≤ lf * N := Nat.mul_le_mul_right _ hlf
  have e5 : k * ℓ * N ≤ ld * N := Nat.mul_le_mul_right _ hld
  have hN : 64 ≤ N := le_trans hU' hU
  have eq1 : U + 1 + (lf + 2 * k + 1) * (20 * N) + (k + 1) * (10 * N) +
      (ld + 2 * (k * ℓ) + 1) * (20 * N) + (k * ℓ + 1) * (10 * N) + (U + 1) + (1 * N + U) + 12 * N
      + (k + n + 1) * ((ℓ + 3) * (60 * N)) + (n * (ℓ + 1) + 1) * (10 * N) + (a + 1) * (10 * N)
      + (b + 1) * (10 * N) + (3 * N + U) =
      4 * U + 2 + 20 * (lf * N) + 50 * (k * N) + 20 * (ld * N) + 50 * (k * ℓ * N) + 106 * N
      + (k + n + 1) * ((ℓ + 3) * (60 * N)) + 10 * (n * (ℓ + 1) * N) + 10 * (a * N)
      + 10 * (b * N) := by ring
  have eq2 : 600 * (lf + ld + n * (ℓ + 1) + 1) * N =
      600 * (lf * N) + 600 * (ld * N) + 600 * (n * (ℓ + 1) * N) + 600 * N := by ring
  rw [eq1, eq2]
  generalize (k + n + 1) * ((ℓ + 3) * (60 * N)) = K at *
  generalize lf * N = A1 at *
  generalize ld * N = A2 at *
  generalize k * N = A3 at *
  generalize k * ℓ * N = A4 at *
  generalize n * (ℓ + 1) * N = A5 at *
  generalize a * N = A6 at *
  generalize b * N = A7 at *
  omega

set_option maxHeartbeats 8000000 in
/-- **One argument of a schema.** -/
lemma p3Arg_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (st : NSt CR CQ) (hb : st.Bdd w)
    (hpx : st.pos ≤ x.length) (u : ℕ) (Ls : List ℕ) (π : BlockPerm k ℓ) (cs : List (Coord k ℓ))
    (tern : Bool) (a base : ℕ) (rest : List Bool)
    (hs : (cs.map fun c => (c.1 : ℕ)).Pairwise (· ≤ ·)) (hk : 1 ≤ k)
    (hx : x.drop st.pos = encodeNats (permDescription π) ++ rest)
    (hKw : k * ℓ + k + 1 < 2 ^ w) (hℓw : ℓ + 1 < 2 ^ w) (huw : u < 2 ^ w)
    (hnw : cs.length + 1 < 2 ^ w) (haw : a + 1 < 2 ^ w)
    (hsw : base + sqOff tern a cs.length + cs.length * sqStr tern < 2 ^ w)
    (hbits : ∀ v ∈ permDescription π, (Nat.bits v).length < w)
    (hKk : st.env rKk = k) (hKL : st.env rKL = k * ℓ) (hL : st.env rL = ℓ)
    (hD : st.env rD = cs.length) (hTn : st.env rTn = if tern then 1 else 0)
    (hAi : st.env rAi = a) (hSB : st.env rSB = base) (hStr : st.env rStr = sqStr tern)
    (hLs : st.stk qLs2 = u :: Ls) (hF : st.stk qF = []) (hF2 : st.stk qF2 = [])
    (hDl : st.stk qDl = []) (hDl2 : st.stk qDl2 = []) (hDom : st.stk qDom = [])
    (hDom2 : st.stk qDom2 = cs.flatMap cdesc) (hAux : st.stk qAux = []) :
    ∃ st', Good x w p3Arg st st'
        (600 * ((encodeNats (permDescription π)).length + cs.length * (ℓ + 1) + 1) *
          Ex.nodeCost w) ∧
      st'.stk qLs2 = Ls ∧ st'.stk qF = [] ∧ st'.stk qF2 = [] ∧ st'.stk qDl = [] ∧
      st'.stk qDl2 = [] ∧ st'.stk qDom = [] ∧ st'.stk qDom2 = cs.flatMap cdesc ∧
      st'.stk qAux = [] ∧
      st'.stk qRec = (colReqs u π cs (base + sqOff tern a cs.length) (sqStr tern)).flatten.reverse ++
        st.stk qRec ∧
      (∀ q, q ≠ qLs2 → q ≠ qF → q ≠ qF2 → q ≠ qDl → q ≠ qDl2 → q ≠ qDom → q ≠ qDom2 →
        q ≠ qAux → q ≠ qRec → q ≠ qJunk → st'.stk q = st.stk q) ∧
      st'.env rAi = a + 1 ∧
      st'.pos = st.pos + (encodeNats (permDescription π)).length ∧ st'.out = st.out ∧
      ∀ r, wReg r p3Arg = false → st'.env r = st.env r := by
  have hU0 := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  set n := cs.length
  have hfk : (fL π).length = k := length_fL π
  have hdk : (dL π).flatten.length = k * ℓ := length_flatten_dL π
  have hxF : x.drop (st.pos) = encodeNats (fL π) ++ (encodeNats (dL π).flatten ++ rest) := by
    rw [hx, permDescription_eq, encodeNats_append, List.append_assoc]
  -- the location
  have r1 := Good.pop_cons (x := x) (w := w) (r := rU) hLs
  set s1 := (st.setS qLs2 Ls).set rU u
  -- `f`
  obtain ⟨r2, h2S, h2p, h2o, h2e⟩ := rdNumsS_good (Q := CQ) (x := x) hw (q := qF) (n := rKk)
    (i := rI) (r := rV) (p := rP) (t := rT) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s1 (fL π)
    (encodeNats (dL π).flatten ++ rest) hxF (by rw [hfk]; simp [s1, Function.update_of_ne
      (show rKk ≠ rU by decide), hKk]) (by rw [hfk]; omega)
    (fun v hv => hbits v (by rw [permDescription_eq]; exact List.mem_append_left _ hv))
  set s2 := rnsSt s1 qF rI rV rP rT (fL π) (fL π).length
  have hb2 := (r1.seq r2).bdd hw hb hpx
  obtain ⟨s3, r3, h3S, h3p, h3o, h3e⟩ := moveAllS_good (x := x) hw (q := qF) (q' := qF2)
    (t := rT) (f := rT2) (by decide) (by decide) s2 hb2.1
  have h2F : s2.stk qF = (fL π).reverse := by rw [h2S]; simp [s1, Function.update_of_ne (show qF ≠ qLs2 by decide), hF]
  have h3F2 : s3.stk qF2 = fL π := by
    rw [h3S, Function.update_self, h2F, List.reverse_reverse, h2S,
      Function.update_of_ne (by decide)]; simp [s1, Function.update_of_ne (show qF2 ≠ qLs2 by decide), hF2]
  -- the shifts
  have hx3 : x.drop s3.pos = encodeNats (dL π).flatten ++ rest := by
    rw [h3p, h2p, ← List.drop_drop, show s1.pos = st.pos from rfl, hxF, List.drop_left]
  have e3 : ∀ r, r ≠ rT → r ≠ rT2 → r ≠ rI → r ≠ rV → r ≠ rP → r ≠ rU → s3.env r = st.env r := by
    intro r n1 n2 n3 n4 n5 n6
    rw [h3e r n1 n2, h2e r n3 n4 n5 n1]; simp [s1, Function.update_of_ne n6]
  obtain ⟨r4, h4S, h4p, h4o, h4e⟩ := rdNumsS_good (Q := CQ) (x := x) hw (q := qDl) (n := rKL)
    (i := rI) (r := rV) (p := rP) (t := rT) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s3 (dL π).flatten
    rest hx3 (by rw [hdk, e3 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hKL]) (by rw [hdk]; omega)
    (fun v hv => hbits v (by rw [permDescription_eq]; exact List.mem_append_right _ hv))
  set s4 := rnsSt s3 qDl rI rV rP rT (dL π).flatten (dL π).flatten.length
  have hb4 := (r1.seq (r2.seq (r3.seq r4))).bdd hw hb hpx
  obtain ⟨s5, r5, h5S, h5p, h5o, h5e⟩ := moveAllS_good (x := x) hw (q := qDl) (q' := qDl2)
    (t := rT) (f := rT2) (by decide) (by decide) s4 hb4.1
  have h4Dl : s4.stk qDl = (dL π).flatten.reverse := by
    rw [h4S, Function.update_self, h3S, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), h2S, Function.update_of_ne (by decide)]
    simp [s1, Function.update_of_ne (show qDl ≠ qLs2 by decide), hDl]
  have h5Dl2 : s5.stk qDl2 = (dL π).flatten := by
    rw [h5S, Function.update_self, h4Dl, List.reverse_reverse, h4S,
      Function.update_of_ne (by decide), h3S, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), h2S, Function.update_of_ne (by decide)]
    simp [s1, Function.update_of_ne (show qDl2 ≠ qLs2 by decide), hDl2]
  have h5F2 : s5.stk qF2 = (fL π).getD 0 0 :: (fL π).drop 1 := by
    rw [h5S, Function.update_of_ne (by decide), Function.update_of_ne (by decide), h4S,
      Function.update_of_ne (by decide), h3F2]
    obtain ⟨f0, fs, hfs⟩ : ∃ f0 fs, fL π = f0 :: fs := by
      cases h : fL π with
      | nil => rw [h] at hfk; simp at hfk; omega
      | cons f0 fs => exact ⟨f0, fs, rfl⟩
    rw [hfs]; rfl
  -- the first image
  have r6 := Good.pop_cons (x := x) (w := w) (r := rFi) h5F2
  set s6 := (s5.setS qF2 ((fL π).drop 1)).set rFi ((fL π).getD 0 0)
  have r7 := Good.set (x := x) (w := w) (r := rCur) (e := .const 0) (st := s6)
    (by simp only [Ex.Fits]; omega)
  set s7 := s6.set rCur ((Ex.const 0 : Ex CR).eval s6.env)
  have hpre7 := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))
  have r8 := p3Seq_good (x := x) (w := w) s7 tern (a := a) (d := n) (b := base)
    (by rw [hpre7.env_of (by decide), hTn]) (by rw [hpre7.env_of (by decide), hAi])
    (by rw [hpre7.env_of (by decide), hD]) (by rw [hpre7.env_of (by decide), hSB])
    (by omega) haw (by omega)
  set s8 := s7.set rSq (base + sqOff tern a n)
  have hpre8 := hpre7.seq r8
  have hsuf2 : ∀ r, r ≠ rI → r ≠ rV → r ≠ rP → r ≠ rT → r ≠ rT2 → r ≠ rFi → r ≠ rCur →
      r ≠ rSq → s8.env r = s1.env r := by
    intro r n1 n2 n3 n4 n5 n6 n7 n8
    simp only [s8, s7, s6, NSt.set_env, NSt.setS_env, Function.update_of_ne n8,
      Function.update_of_ne n7, Function.update_of_ne n6]
    rw [h5e r n4 n5, h4e r n1 n2 n3 n4, h3e r n4 n5, h2e r n1 n2 n3 n4]
  -- the columns
  obtain ⟨s9, r9, h9D2, h9D, h9Dl2, h9F2, h9Aux, h9Rec, h9S, h9p, h9o, h9e⟩ :=
    p3Cols_good (x := x) hw s8 u π cs (base + sqOff tern a n) (sqStr tern) [] []
      (st.stk qRec) hs hk (by nlinarith) hℓw huw hnw hsw
      (by rw [hpre8.env_of (by decide), hD])
      (by rw [hpre8.stk_of (by decide), hDom2, List.append_nil])
      (by rw [hpre8.stk_of (by decide), hDom]) (by rw [hpre8.stk_of (by decide), hAux])
      (by simp [s8, s7, Function.update_of_ne (show rCur ≠ rSq by decide), Ex.eval])
      (by rw [hpre8.env_of (by decide), hL])
      (by rw [hsuf2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]; simp [s1])
      (by simp [s8]) (by rw [hpre8.env_of (by decide), hStr])
      (by simp only [s8, s7, s6, NSt.set_stk, NSt.setS_stk, Function.update_of_ne
        (show qDl2 ≠ qF2 by decide)]; exact h5Dl2)
      (by simp [s8, s7, s6])
      (by simp [s8, s7, s6, Function.update_of_ne (show rFi ≠ rSq by decide),
        Function.update_of_ne (show rFi ≠ rCur by decide)])
      (by rw [hpre8.stk_of (by decide)])
  have hb9 := (hpre8.seq r9).bdd hw hb hpx
  obtain ⟨s10, r10, h10S, h10p, h10o, h10e⟩ := moveAllS_good (x := x) hw (q := qDom)
    (q' := qDom2) (t := rT) (f := rT2) (by decide) (by decide) s9 hb9.1
  have hb10 := ((hpre8.seq r9).seq r10).bdd hw hb hpx
  obtain ⟨s11, r11, h11S, h11p, h11o, h11e⟩ := moveAllS_good (x := x) hw (q := qF2)
    (q' := qJunk) (t := rT) (f := rT2) (by decide) (by decide) s10 hb10.1
  have hb11 := (((hpre8.seq r9).seq r10).seq r11).bdd hw hb hpx
  obtain ⟨s12, r12, h12S, h12p, h12o, h12e⟩ := moveAllS_good (x := x) hw (q := qDl2)
    (q' := qJunk) (t := rT) (f := rT2) (by decide) (by decide) s11 hb11.1
  have r13 := Good.set (x := x) (w := w) (r := rAi) (e := .add (rv rAi) (.const 1)) (st := s12)
    (by
      have : s12.env rAi = a := by
        rw [h12e _ (by decide) (by decide), h11e _ (by decide) (by decide),
          h10e _ (by decide) (by decide), h9e _ (by decide), hpre8.env_of (by decide), hAi]
      simp only [Ex.Fits, Ex.eval, rv, this]; omega)
  set s13 := s12.set rAi (Ex.eval s12.env (.add (rv rAi) (.const 1)))
  have hall := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq
    (r11.seq (r12.seq r13)))))))))))
  have hsuf2 := r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq
    (r11.seq (r12.seq r13))))))))))
  have hsuf4 := r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq (r11.seq (r12.seq r13))))))))
  have hsuf5 := r5.seq (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq (r11.seq (r12.seq r13)))))))
  have hsuf6 := r6.seq (r7.seq (r8.seq (r9.seq (r10.seq (r11.seq (r12.seq r13))))))
  have hsuf10 := r10.seq (r11.seq (r12.seq r13))
  have hsuf11 := r11.seq (r12.seq r13)
  have hsuf12 := r12.seq r13
  have hlen9 : (s9.stk qDom).length = n * (ℓ + 1) := by
    rw [h9D, List.append_nil, List.length_reverse, List.length_flatMap]
    have : cs.map (fun c => (cdesc c).length) = cs.map fun _ => ℓ + 1 :=
      List.map_congr_left fun c _ => length_cdesc c
    rw [this, sum_map_const]
  have hlen10 : (s10.stk qF2).length ≤ k := by
    rw [h10S, Function.update_of_ne (by decide), Function.update_of_ne (by decide), h9F2]
    simp [hfk]
  have hlen11 : (s11.stk qDl2).length ≤ k * ℓ := by
    rw [h11S, Function.update_of_ne (by decide), Function.update_of_ne (by decide), h10S,
      Function.update_of_ne (by decide), Function.update_of_ne (by decide), h9Dl2, ← hdk]
    exact length_flatten_drop_le _ _
  have hlenF : (s2.stk qF).length = k := by rw [h2F, List.length_reverse, hfk]
  have hlenD : (s4.stk qDl).length = k * ℓ := by rw [h4Dl, List.length_reverse, hdk]
  have hP : (encodeNats (permDescription π)).length =
      (encodeNats (fL π)).length + (encodeNats (dL π).flatten).length := by
    rw [permDescription_eq, encodeNats_append, List.length_append]
  refine ⟨s13, hall.mono ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hall.out_of (by decide),
    fun r hr => hall.env_of hr⟩
  · rw [hlenF, hlenD, hlen9, hP, hfk, hdk]
    simp only [condCost, Ex.size, rv]
    have hlf : k ≤ (encodeNats (fL π)).length := by
      have := length_le_encodeNats (fL π); rwa [hfk] at this
    have hld : k * ℓ ≤ (encodeNats (dL π).flatten).length := by
      have := length_le_encodeNats (dL π).flatten; rwa [hdk] at this
    have := arg_arith (Ex.nodeCost w) (unitCost w) k n ℓ (encodeNats (fL π)).length
      (encodeNats (dL π).flatten).length _ _ hU0 hU' hk hlf hld hlen10 hlen11
    linarith
  · rw [hsuf2.stk_of (by decide)]; simp [s1]
  · rw [hsuf4.stk_of (by decide), h3S, Function.update_of_ne (by decide), Function.update_self]
  · rw [hsuf12.stk_of (by decide)]
    show s11.stk qF2 = []
    rw [h11S, Function.update_of_ne (by decide), Function.update_self]
  · rw [hsuf6.stk_of (by decide), h5S, Function.update_of_ne (by decide), Function.update_self]
  · show s12.stk qDl2 = []
    rw [h12S, Function.update_of_ne (by decide), Function.update_self]
  · rw [hsuf11.stk_of (by decide), h10S, Function.update_of_ne (by decide), Function.update_self]
  · rw [hsuf11.stk_of (by decide), h10S, Function.update_self, h9D, h9D2]; simp
  · rw [hsuf10.stk_of (by decide), h9Aux]
  · rw [hsuf10.stk_of (by decide), h9Rec]
  · intro q n1 n2 n3 n4 n5 n6 n7 n8 n9 n10
    exact hall.stk_of (by
      simp [p3Arg, p3Seq, p3Cols, p3Col, p3Advs, p3Adv, p3Bits, p3Bit, moveN, moveAllS, rdNumsS,
        rdNumS, wStk, Ne.symm n1, Ne.symm n2, Ne.symm n3, Ne.symm n4, Ne.symm n5, Ne.symm n6,
        Ne.symm n7, Ne.symm n8, Ne.symm n9, Ne.symm n10])
  · simp only [s13, NSt.set_env, Function.update_self, Ex.eval, rv]
    rw [h12e _ (by decide) (by decide), h11e _ (by decide) (by decide),
      h10e _ (by decide) (by decide), h9e _ (by decide), hpre8.env_of (by decide), hAi]
  · rw [hsuf5.pos_of (by decide), h4p, h3p, h2p, hP]; simp [s1]; ring

end Lax119563Proofs.Compiler

end Compiler_PReqArg

/-! ### Formerly `Lax119563Proofs.Compiler.PReqArgs` -/

section Compiler_PReqArgs

/-!
# Pass `P3`, request generation: the argument loop of a schema

`p3Args` runs `p3Arg` for the `A` arguments (locations `locs` on `qLs2`, permutation
descriptions in the input), pushing `argsReqs` (**`p3Args_good`**).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ}

/-- The requests of argument `p = ((u, π), a)`. -/
def argReqs (cs : List (Coord k ℓ)) (base : ℕ) (tern : Bool) (p : (ℕ × BlockPerm k ℓ) × ℕ) :
    List (List ℕ) :=
  colReqs p.1.1 p.1.2 cs (base + sqOff tern p.2 cs.length) (sqStr tern)

/-- The requests of the arguments. -/
def argsReqs (locs : List ℕ) (perms : List (BlockPerm k ℓ)) (cs : List (Coord k ℓ))
    (base : ℕ) (tern : Bool) (a : ℕ) : List (List ℕ) :=
  (((locs.zip perms).zipIdx).take a).flatMap (argReqs cs base tern)

/-- The argument loop. -/
def p3Args : CStm CR CQ := .seq (.set rAi (.const 0)) (.loop (.lt (rv rAi) (rv rA)) p3Arg)

lemma argsReqs_succ (locs : List ℕ) (perms : List (BlockPerm k ℓ)) (cs : List (Coord k ℓ))
    (base : ℕ) (tern : Bool) {a : ℕ} (hl : a < locs.length) (hp : a < perms.length) :
    argsReqs locs perms cs base tern (a + 1) = argsReqs locs perms cs base tern a ++
      colReqs locs[a] perms[a] cs (base + sqOff tern a cs.length) (sqStr tern) := by
  have ha : a < ((locs.zip perms).zipIdx).length := by simp; omega
  rw [argsReqs, argsReqs, List.take_add_one, List.getElem?_eq_getElem ha, Option.toList_some,
    List.flatMap_append]
  simp [argReqs, List.getElem_zipIdx]

lemma flatMap_perms_split (perms : List (BlockPerm k ℓ)) {a : ℕ} (ha : a < perms.length) :
    (perms.drop a).flatMap permDescription =
      permDescription perms[a] ++ (perms.drop (a + 1)).flatMap permDescription := by
  rw [List.drop_eq_getElem_cons ha, List.flatMap_cons]

lemma flatMap_take_succ (perms : List (BlockPerm k ℓ)) {a : ℕ} (ha : a < perms.length) :
    (perms.take (a + 1)).flatMap permDescription =
      (perms.take a).flatMap permDescription ++ permDescription perms[a] := by
  rw [List.take_add_one, List.getElem?_eq_getElem ha, Option.toList_some, List.flatMap_append]
  simp

lemma args_arith (N P A m : ℕ) (hN : 64 ≤ N) :
    1 * N + N + (600 * N * P + A * (600 * (m + 1) * N + ((1 + 1 + 1) * N + 1)) +
      ((1 + 1 + 1) * N + 1)) ≤ 600 * (P + A * (m + 2) + 1) * N := by
  have : A * (600 * (m + 1) * N + ((1 + 1 + 1) * N + 1)) ≤ A * (600 * (m + 2) * N) :=
    Nat.mul_le_mul_left _ (by nlinarith)
  nlinarith

set_option maxHeartbeats 8000000 in
/-- **The arguments of a schema.** -/
lemma p3Args_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (st : NSt CR CQ) (hb : st.Bdd w)
    (hpx : st.pos ≤ x.length) (locs : List ℕ) (perms : List (BlockPerm k ℓ))
    (cs : List (Coord k ℓ)) (tern : Bool) (base : ℕ) (rest : List Bool) {A : ℕ}
    (hl : locs.length = A) (hp : perms.length = A)
    (hs : (cs.map fun c => (c.1 : ℕ)).Pairwise (· ≤ ·)) (hk : 1 ≤ k)
    (hx : x.drop st.pos = encodeNats (perms.flatMap permDescription) ++ rest)
    (hKw : k * ℓ + k + 1 < 2 ^ w) (hℓw : ℓ + 1 < 2 ^ w) (huw : ∀ u ∈ locs, u < 2 ^ w)
    (hnw : cs.length + 1 < 2 ^ w) (hAw : A + 1 < 2 ^ w)
    (hsw : ∀ a < A, base + sqOff tern a cs.length + cs.length * sqStr tern < 2 ^ w)
    (hbits : ∀ π ∈ perms, ∀ v ∈ permDescription π, (Nat.bits v).length < w)
    (hKk : st.env rKk = k) (hKL : st.env rKL = k * ℓ) (hL : st.env rL = ℓ)
    (hD : st.env rD = cs.length) (hTn : st.env rTn = if tern then 1 else 0)
    (hSB : st.env rSB = base) (hStr : st.env rStr = sqStr tern) (hrA : st.env rA = A)
    (hLs : st.stk qLs2 = locs) (hF : st.stk qF = []) (hF2 : st.stk qF2 = [])
    (hDl : st.stk qDl = []) (hDl2 : st.stk qDl2 = []) (hDom : st.stk qDom = [])
    (hDom2 : st.stk qDom2 = cs.flatMap cdesc) (hAux : st.stk qAux = []) :
    ∃ st', Good x w p3Args st st'
        (600 * ((encodeNats (perms.flatMap permDescription)).length +
          A * (cs.length * (ℓ + 1) + 2) + 1) * Ex.nodeCost w) ∧
      st'.stk qLs2 = [] ∧ st'.stk qF = [] ∧ st'.stk qF2 = [] ∧ st'.stk qDl = [] ∧
      st'.stk qDl2 = [] ∧ st'.stk qDom = [] ∧ st'.stk qDom2 = cs.flatMap cdesc ∧
      st'.stk qAux = [] ∧
      st'.stk qRec = (argsReqs locs perms cs base tern A).flatten.reverse ++ st.stk qRec ∧
      (∀ q, q ≠ qLs2 → q ≠ qF → q ≠ qF2 → q ≠ qDl → q ≠ qDl2 → q ≠ qDom → q ≠ qDom2 →
        q ≠ qAux → q ≠ qRec → q ≠ qJunk → st'.stk q = st.stk q) ∧
      st'.pos = st.pos + (encodeNats (perms.flatMap permDescription)).length ∧
      st'.out = st.out ∧ ∀ r, wReg r p3Args = false → st'.env r = st.env r := by
  have hU0 := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  set n := cs.length
  set P := (encodeNats (perms.flatMap permDescription)).length
  have hxl : st.pos + P ≤ x.length := by
    have := congrArg List.length hx
    simp only [List.length_drop, List.length_append] at this; omega
  have r0 := Good.set (x := x) (w := w) (r := rAi) (e := .const 0) (st := st)
    (by simp only [Ex.Fits]; omega)
  set s0 := st.set rAi ((Ex.const 0 : Ex CR).eval st.env)
  set Inv : NSt CR CQ → Prop := fun s => s.env rAi ≤ A ∧ s.env rA = A ∧ s.env rKk = k ∧
    s.env rKL = k * ℓ ∧ s.env rL = ℓ ∧ s.env rD = n ∧ s.env rTn = (if tern then 1 else 0) ∧
    s.env rSB = base ∧ s.env rStr = sqStr tern ∧
    s.stk qLs2 = locs.drop (s.env rAi) ∧ s.stk qF = [] ∧ s.stk qF2 = [] ∧ s.stk qDl = [] ∧
    s.stk qDl2 = [] ∧ s.stk qDom = [] ∧ s.stk qDom2 = cs.flatMap cdesc ∧ s.stk qAux = [] ∧
    s.stk qRec = (argsReqs locs perms cs base tern (s.env rAi)).flatten.reverse ++ st.stk qRec ∧
    (∀ q, q ≠ qLs2 → q ≠ qF → q ≠ qF2 → q ≠ qDl → q ≠ qDl2 → q ≠ qDom → q ≠ qDom2 →
      q ≠ qAux → q ≠ qRec → q ≠ qJunk → s.stk q = st.stk q) ∧
    s.pos = st.pos + (encodeNats ((perms.take (s.env rAi)).flatMap permDescription)).length ∧
    s.out = st.out ∧ s.Bdd w ∧ (∀ r, wReg r p3Args = false → s.env r = st.env r) with hInv
  have hloop := Good.loop_var (x := x) (w := w) (e := .lt (rv rAi) (rv rA)) (body := p3Arg)
    Inv (fun s => A - s.env rAi) (fun s => st.pos + P - s.pos) (600 * Ex.nodeCost w)
    (600 * (n * (ℓ + 1) + 1) * Ex.nodeCost w) (by
      intro s ⟨ha, hA', hk', hkl, hl', hd, htn, hsb, hstr, hls, hf, hf2, hdl, hdl2, hdom, hdom2,
        haux, hrec, hS, hps, ho, hbs, he⟩
      refine ⟨⟨by simp only [rv, Ex.Fits]; omega, by simp only [rv, Ex.Fits]; omega⟩, ?_⟩
      intro hcond
      have hlt : s.env rAi < A := by simpa [rv, Ex.eval, hA'] using hcond
      set a := s.env rAi with hadef
      have hal : a < locs.length := by omega
      have hap : a < perms.length := by omega
      have hPa : (encodeNats ((perms.take a).flatMap permDescription)).length +
          (encodeNats (permDescription perms[a])).length +
          (encodeNats ((perms.drop (a + 1)).flatMap permDescription)).length = P := by
        simp only [P]
        conv_rhs => rw [← List.take_append_drop a perms, List.flatMap_append,
          flatMap_perms_split perms hap]
        simp only [encodeNats_append, List.length_append]; ring
      have hxa : x.drop s.pos = encodeNats (permDescription perms[a]) ++
          (encodeNats ((perms.drop (a + 1)).flatMap permDescription) ++ rest) := by
        have e : perms.flatMap permDescription = (perms.take a).flatMap permDescription ++
            (permDescription perms[a] ++ (perms.drop (a + 1)).flatMap permDescription) := by
          rw [← flatMap_perms_split perms hap, ← List.flatMap_append, List.take_append_drop]
        rw [hps, ← List.drop_drop, hx, e, encodeNats_append, encodeNats_append, List.append_assoc,
          List.append_assoc, List.drop_left]
      have hpsx : s.pos ≤ x.length := by omega
      have hls' : s.stk qLs2 = locs[a] :: locs.drop (a + 1) := by
        rw [hls, List.drop_eq_getElem_cons hal]
      obtain ⟨s', r', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
        p3Arg_good (x := x) hw s hbs hpsx locs[a] (locs.drop (a + 1)) perms[a] cs tern a base
          _ hs hk hxa hKw hℓw (huw _ (List.getElem_mem hal)) hnw (by omega)
          (hsw a hlt) (hbits _ (List.getElem_mem hap)) hk' hkl hl' hd htn
          hadef.symm hsb hstr hls' hf hf2 hdl hdl2 hdom hdom2 haux
      have hbs' := (r'.bdd hw hbs hpsx).1
      refine ⟨s', r'.mono ?_, ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, hbs', ?_⟩, by omega, by omega⟩
      · rw [h12, hps]
        have : st.pos + P - (st.pos + (encodeNats ((perms.take a).flatMap permDescription)).length)
            - (st.pos + P - (st.pos + (encodeNats ((perms.take a).flatMap permDescription)).length
              + (encodeNats (permDescription perms[a])).length)) =
            (encodeNats (permDescription perms[a])).length := by omega
        rw [this]; nlinarith
      · rw [h14 _ (by decide), hA']
      · rw [h14 _ (by decide), hk']
      · rw [h14 _ (by decide), hkl]
      · rw [h14 _ (by decide), hl']
      · rw [h14 _ (by decide), hd]
      · rw [h14 _ (by decide), htn]
      · rw [h14 _ (by decide), hsb]
      · rw [h14 _ (by decide), hstr]
      · rw [h11, h1]
      · exact h2
      · exact h3
      · exact h4
      · exact h5
      · exact h6
      · exact h7
      · exact h8
      · rw [h9, h11, argsReqs_succ _ _ _ _ _ hal hap, hrec]; simp
      · intro q n1 n2 n3 n4 n5 n6 n7 n8 n9 n10
        rw [h10 q n1 n2 n3 n4 n5 n6 n7 n8 n9 n10, hS q n1 n2 n3 n4 n5 n6 n7 n8 n9 n10]
      · rw [h12, hps, h11, flatMap_take_succ perms hap, encodeNats_append, List.length_append]
        ring
      · rw [h13, ho]
      · intro r hr
        rw [h14 r (by simp only [p3Args, wReg, Bool.or_eq_false_iff] at hr; exact hr.2), he r hr])
    s0 ⟨by simp [s0, Ex.eval], by simp [s0, Function.update_of_ne (show rA ≠ rAi by decide), hrA],
      by simp [s0, Function.update_of_ne (show rKk ≠ rAi by decide), hKk],
      by simp [s0, Function.update_of_ne (show rKL ≠ rAi by decide), hKL],
      by simp [s0, Function.update_of_ne (show rL ≠ rAi by decide), hL],
      by simp [s0, Function.update_of_ne (show rD ≠ rAi by decide), hD],
      by simp [s0, Function.update_of_ne (show rTn ≠ rAi by decide), hTn],
      by simp [s0, Function.update_of_ne (show rSB ≠ rAi by decide), hSB],
      by simp [s0, Function.update_of_ne (show rStr ≠ rAi by decide), hStr],
      by simp [s0, Ex.eval, hLs], hF, hF2, hDl, hDl2, hDom, hDom2, hAux,
      by simp [s0, Ex.eval, argsReqs], fun _ _ _ _ _ _ _ _ _ _ _ => rfl,
      by simp [s0, Ex.eval, encodeNats], rfl, (r0.bdd hw hb hpx).1,
      fun r hr => by
        simp only [p3Args, wReg, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
        simp [s0, Function.update_of_ne (Ne.symm hr.1)]⟩
  obtain ⟨s', r', ⟨ha, hA', -, -, -, -, -, -, -, hls, hf, hf2, hdl, hdl2, hdom, hdom2, haux, hrec,
    hS, hps, ho, -, he⟩, hc⟩ := hloop
  have haA : s'.env rAi = A := by
    simp only [Ex.eval, rv, hA'] at hc; split_ifs at hc with h <;> omega
  refine ⟨s', (r0.seq r').mono ?_, by rw [hls, haA, ← hl]; simp, hf, hf2, hdl, hdl2, hdom,
    hdom2, haux, by rw [hrec, haA], hS, by rw [hps, haA, ← hp, List.take_length], ho, he⟩
  have h0 : A - s0.env rAi = A := by simp [s0, Ex.eval]
  have h1 : st.pos + P - s0.pos = P := by simp [s0]
  rw [h0, h1]; simp only [condCost, rv, Ex.size]
  exact le_trans (by nlinarith) (args_arith (Ex.nodeCost w) P A (n * (ℓ + 1)) (by omega))

end Lax119563Proofs.Compiler

end Compiler_PReqArgs

/-! ### Formerly `Lax119563Proofs.Compiler.PReqSch` -/

section Compiler_PReqSch

/-!
# Pass `P3`, request generation: one schema

`p3Sch` reads the arity, the locations (onto `qLs2`), `|D|` and the coordinates (onto `qDom2`),
runs `p3Args`, discards the domain and adds `arity · |D|` to the sequence base `rSB`
(**`p3Sch_good`**).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ W : ℕ}

/-- **One schema.** -/
def p3Sch : CStm CR CQ :=
  .seq (rdNumS rA rP rT) (.seq (.set rTn (.lt (.const 2) (rv rA)))
    (.seq (.set rStr (.add (.const 1) (.add (rv rTn) (rv rTn))))
      (.seq (rdNumsS qLs rA rI rV rP rT) (.seq (moveAllS qLs qLs2 rT rT2)
        (.seq (rdNumS rD rP rT) (.seq (mulS rNw rD rL1 rGj)
          (.seq (rdNumsS qDom rNw rI rV rP rT) (.seq (moveAllS qDom qDom2 rT rT2)
            (.seq p3Args (.seq (moveAllS qDom2 qJunk rT rT2) (.seq (mulS rNw rA rD rGj)
              (.seq (.set rSB (.add (rv rSB) (rv rNw)))
                (.set rJ (.add (rv rJ) (.const 1)))))))))))))))

lemma tern_val (s : Schema k ℓ W) :
    (if 2 < arity s then 1 else 0) = (if Matrix.isTern s then 1 else 0) := by
  unfold arity; split_ifs <;> simp_all

lemma arity_le' (s : Schema k ℓ W) : arity s ≤ 3 := by unfold arity; split_ifs <;> omega

lemma sqStr_val (s : Schema k ℓ W) :
    1 + ((if Matrix.isTern s then 1 else 0) + (if Matrix.isTern s then 1 else 0)) =
      sqStr (Matrix.isTern s) := by
  unfold sqStr; split_ifs <;> rfl

lemma length_schPerms (s : Schema k ℓ W) : (schPerms s).length = arity s := by
  cases s <;> simp [schPerms, arity, Matrix.isTern]

lemma sqOff_le (s : Schema k ℓ W) (n : ℕ) {a : ℕ} (ha : a < arity s) :
    sqOff (Matrix.isTern s) a n + n * sqStr (Matrix.isTern s) ≤ 3 * n + 3 := by
  unfold sqOff sqStr; unfold arity at ha; split_ifs at * <;> omega

lemma length_flatMap_cdesc (cs : List (Coord k ℓ)) :
    (cs.flatMap cdesc).length = cs.length * (ℓ + 1) := by
  rw [List.length_flatMap]
  have : cs.map (fun c => (cdesc c).length) = cs.map fun _ => ℓ + 1 :=
    List.map_congr_left fun c _ => length_cdesc c
  rw [this, sum_map_const]

lemma sch_arith (N U la ll lo ln lc cl P A n ℓ : ℕ) (hU : U ≤ N) (hU' : 64 ≤ U) (hA : A ≤ 3)
    (hlo : lo = A) (hcl : cl = n * (ℓ + 1)) (hclc : cl ≤ lc) (hP : ℓ + 1 ≤ P) :
    (la + 1) * (20 * N) + ((1 + 1 + 1) * N + U + ((1 + (1 + 1 + 1) + 1) * N + U +
      ((ll + 2 * lo + 1) * (20 * N) + ((A + 1) * (10 * N) + ((ln + 1) * (20 * N) +
      ((ℓ + 1 + 1) * (12 * N) + ((lc + 2 * cl + 1) * (20 * N) + ((n * (ℓ + 1) + 1) * (10 * N) +
      (600 * (P + A * (n * (ℓ + 1) + 2) + 1) * N + ((n * (ℓ + 1) + 1) * (10 * N) +
      ((n + 1) * (12 * N) + ((1 + 1 + 1) * N + U + ((1 + 1 + 1) * N + U))))))))))))) ≤
      10000 * (la + ll + ln + lc + P + 1) * N := by
  rw [hlo]
  rw [← hcl]
  have hnX : n ≤ cl := by rw [hcl]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hY : A * (cl + 2) ≤ 3 * cl + 6 := by nlinarith
  have key : (la + 1) * (20 * N) + ((1 + 1 + 1) * N + U + ((1 + (1 + 1 + 1) + 1) * N + U +
      ((ll + 2 * A + 1) * (20 * N) + ((A + 1) * (10 * N) + ((ln + 1) * (20 * N) +
      ((ℓ + 1 + 1) * (12 * N) + ((lc + 2 * cl + 1) * (20 * N) + ((cl + 1) * (10 * N) +
      (600 * (P + A * (cl + 2) + 1) * N + ((cl + 1) * (10 * N) +
      ((n + 1) * (12 * N) + ((1 + 1 + 1) * N + U + ((1 + 1 + 1) * N + U))))))))))))) =
      (20 * (la + 1) + 3 + 5 + 20 * (ll + 2 * A + 1) + 10 * (A + 1) + 20 * (ln + 1) +
        12 * (ℓ + 2) + 20 * (lc + 2 * cl + 1) + 10 * (cl + 1) + 600 * (P + A * (cl + 2) + 1) +
        10 * (cl + 1) + 12 * (n + 1) + 3 + 3) * N + 4 * U := by ring
  rw [key]
  generalize A * (cl + 2) = Y at *
  have hE : 20 * (la + 1) + 3 + 5 + 20 * (ll + 2 * A + 1) + 10 * (A + 1) + 20 * (ln + 1) +
      12 * (ℓ + 2) + 20 * (lc + 2 * cl + 1) + 10 * (cl + 1) + 600 * (P + Y + 1) +
      10 * (cl + 1) + 12 * (n + 1) + 3 + 3 + 4 ≤ 10000 * (la + ll + ln + lc + P + 1) := by omega
  have h4 : 4 * U ≤ 4 * N := by omega
  calc _ ≤ (20 * (la + 1) + 3 + 5 + 20 * (ll + 2 * A + 1) + 10 * (A + 1) + 20 * (ln + 1) +
        12 * (ℓ + 2) + 20 * (lc + 2 * cl + 1) + 10 * (cl + 1) + 600 * (P + Y + 1) +
        10 * (cl + 1) + 12 * (n + 1) + 3 + 3) * N + 4 * N := by omega
    _ = (20 * (la + 1) + 3 + 5 + 20 * (ll + 2 * A + 1) + 10 * (A + 1) + 20 * (ln + 1) +
        12 * (ℓ + 2) + 20 * (lc + 2 * cl + 1) + 10 * (cl + 1) + 600 * (P + Y + 1) +
        10 * (cl + 1) + 12 * (n + 1) + 3 + 3 + 4) * N := by ring
    _ ≤ 10000 * (la + ll + ln + lc + P + 1) * N := Nat.mul_le_mul_right _ hE

set_option maxHeartbeats 8000000 in
/-- **One schema.** -/
lemma p3Sch_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (st : NSt CR CQ) (hb : st.Bdd w)
    (hpx : st.pos ≤ x.length) (sc : Schema k ℓ W) (base j Hb : ℕ) (rest : List Bool)
    (hk : 1 ≤ k) (hx : x.drop st.pos = encodeNats (schemaDescription sc) ++ rest)
    (hHb : 2 * (Hb + 1) ≤ 2 ^ w) (hvals : ∀ v ∈ schemaDescription sc, v ≤ Hb)
    (hnl : (coordList sc.domain).length * (ℓ + 1) ≤ Hb) (hkl : k * ℓ + k + 1 ≤ Hb)
    (hbase : base + 3 * (coordList sc.domain).length + 3 ≤ Hb) (hj : j + 1 ≤ Hb)
    (hℓ : ℓ + 2 ≤ Hb)
    (hKk : st.env rKk = k) (hKL : st.env rKL = k * ℓ) (hL : st.env rL = ℓ)
    (hL1 : st.env rL1 = ℓ + 1) (hSB : st.env rSB = base) (hJ : st.env rJ = j)
    (hLs : st.stk qLs = []) (hLs2 : st.stk qLs2 = []) (hF : st.stk qF = [])
    (hF2 : st.stk qF2 = []) (hDl : st.stk qDl = []) (hDl2 : st.stk qDl2 = [])
    (hDom : st.stk qDom = []) (hDom2 : st.stk qDom2 = []) (hAux : st.stk qAux = []) :
    ∃ st', Good x w p3Sch st st'
        (10000 * ((encodeNats (schemaDescription sc)).length + 1) * Ex.nodeCost w) ∧
      st'.stk qLs = [] ∧ st'.stk qLs2 = [] ∧ st'.stk qF = [] ∧ st'.stk qF2 = [] ∧
      st'.stk qDl = [] ∧ st'.stk qDl2 = [] ∧ st'.stk qDom = [] ∧ st'.stk qDom2 = [] ∧
      st'.stk qAux = [] ∧
      st'.stk qRec = (argsReqs (schLocs sc) (schPerms sc) (coordList sc.domain) base
        (Matrix.isTern sc) (arity sc)).flatten.reverse ++ st.stk qRec ∧
      (∀ q, q ≠ qLs → q ≠ qLs2 → q ≠ qF → q ≠ qF2 → q ≠ qDl → q ≠ qDl2 → q ≠ qDom →
        q ≠ qDom2 → q ≠ qAux → q ≠ qRec → q ≠ qJunk → st'.stk q = st.stk q) ∧
      st'.env rSB = base + arity sc * (coordList sc.domain).length ∧ st'.env rJ = j + 1 ∧
      st'.pos = st.pos + (encodeNats (schemaDescription sc)).length ∧ st'.out = st.out ∧
      ∀ r, wReg r p3Sch = false → st'.env r = st.env r := by
  have hU0 := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have hHw : Hb < 2 ^ w := by omega
  set A := arity sc
  set locs := schLocs sc
  set perms := schPerms sc
  set cs := coordList sc.domain
  set n := cs.length
  set coords := cs.flatMap cdesc
  set tern := Matrix.isTern sc
  have hA3 : A ≤ 3 := arity_le' sc
  have hlocsA : locs.length = A := length_schLocs sc
  have hpermsA : perms.length = A := length_schPerms sc
  have hcl : coords.length = n * (ℓ + 1) := length_flatMap_cdesc cs
  have hdesc := schemaDescription_eq' sc
  have hbits : ∀ v ∈ schemaDescription sc, (Nat.bits v).length < w :=
    fun v hv => bits_lt_of_le (hvals v hv) hHb
  have hmem : ∀ v, (v ∈ [A] ∨ v ∈ locs ∨ v ∈ [n] ∨ v ∈ coords ∨
      v ∈ perms.flatMap permDescription) → v ∈ schemaDescription sc := by
    intro v hv; rw [hdesc]; simp only [List.mem_cons, List.mem_append, List.mem_singleton] at hv ⊢
    tauto
  have hx1 : x.drop st.pos = encodeNat A ++ (encodeNats locs ++ (encodeNat n ++
      (encodeNats coords ++ (encodeNats (perms.flatMap permDescription) ++ rest)))) := by
    rw [hx, hdesc]
    simp only [List.cons_append, encNats_cons, encodeNats_append, List.append_assoc]
    rfl
  -- arity
  have r1 := rdNumS_good (Q := CQ) (x := x) hw (r := rA) (p := rP) (t := rT) (by decide)
    (by decide) (by decide) st A _ hx1 (hbits A (hmem A (by simp)))
  set s1 := rdNumFinal st rA rP rT A
  have e1A : s1.env rA = A := rdNumFinal_env_r (by decide) (by decide) A
  have r2 := Good.set (x := x) (w := w) (r := rTn) (e := .lt (.const 2) (rv rA)) (st := s1)
    (by simp only [Ex.Fits, rv, e1A]; omega)
  set s2 := s1.set rTn (Ex.eval s1.env (.lt (.const 2) (rv rA)))
  have e2T : s2.env rTn = if tern then 1 else 0 := by
    simp only [s2, NSt.set_env, Function.update_self, Ex.eval, rv, e1A]; exact tern_val sc
  have r3 := Good.set (x := x) (w := w) (r := rStr)
    (e := .add (.const 1) (.add (rv rTn) (rv rTn))) (st := s2)
    (by simp only [Ex.Fits, Ex.eval, rv, e2T]; split_ifs <;> omega)
  set s3 := s2.set rStr (Ex.eval s2.env (.add (.const 1) (.add (rv rTn) (rv rTn))))
  have e3S : s3.env rStr = sqStr tern := by
    simp only [s3, NSt.set_env, Function.update_self, Ex.eval, rv, e2T]; exact sqStr_val sc
  -- locations
  have hx3 : x.drop s3.pos = encodeNats locs ++ (encodeNat n ++
      (encodeNats coords ++ (encodeNats (perms.flatMap permDescription) ++ rest))) := by
    show x.drop s1.pos = _
    rw [rdNumFinal_pos, ← List.drop_drop, hx1, List.drop_left]
  obtain ⟨r4, h4S, h4p, h4o, h4e⟩ := rdNumsS_good (Q := CQ) (x := x) hw (q := qLs) (n := rA)
    (i := rI) (r := rV) (p := rP) (t := rT) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s3 locs _ hx3
    (by rw [hlocsA]; simp [s3, s2, Function.update_of_ne (show rA ≠ rStr by decide),
      Function.update_of_ne (show rA ≠ rTn by decide), e1A]) (by omega)
    (fun v hv => hbits v (hmem v (by tauto)))
  set s4 := rnsSt s3 qLs rI rV rP rT locs locs.length
  have hb4 := (r1.seq (r2.seq (r3.seq r4))).bdd hw hb hpx
  obtain ⟨s5, r5, h5S, h5p, h5o, h5e⟩ := moveAllS_good (x := x) hw (q := qLs) (q' := qLs2)
    (t := rT) (f := rT2) (by decide) (by decide) s4 hb4.1
  have h5Ls2 : s5.stk qLs2 = locs := by
    rw [h5S, Function.update_self, h4S, Function.update_self, Function.update_of_ne (by decide)]
    simp [s3, s2, s1, hLs, hLs2]
  have h5Ls : s5.stk qLs = [] := by
    rw [h5S, Function.update_of_ne (by decide), Function.update_self]
  -- the domain
  have hx5 : x.drop s5.pos = encodeNat n ++ (encodeNats coords ++
      (encodeNats (perms.flatMap permDescription) ++ rest)) := by
    rw [h5p, h4p, ← List.drop_drop, hx3, List.drop_left]
  have r6 := rdNumS_good (Q := CQ) (x := x) hw (r := rD) (p := rP) (t := rT) (by decide)
    (by decide) (by decide) s5 n _ hx5 (hbits n (hmem n (by simp)))
  set s6 := rdNumFinal s5 rD rP rT n
  have e6D : s6.env rD = n := rdNumFinal_env_r (by decide) (by decide) n
  have hpre6 := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))
  have r7 := mulS_good (x := x) (w := w) (Q := CQ) hw (dst := rNw) (a := rD) (b := rL1)
    (j := rGj) (by decide) (by decide) (by decide) (by decide) (by decide) s6 e6D
    (by rw [hpre6.env_of (by decide), hL1]) (by omega) (by omega)
  set s7 := (s6.set rNw (n * (ℓ + 1))).set rGj (ℓ + 1)
  have hx7 : x.drop s7.pos = encodeNats coords ++
      (encodeNats (perms.flatMap permDescription) ++ rest) := by
    show x.drop s6.pos = _
    rw [rdNumFinal_pos, ← List.drop_drop, hx5, List.drop_left]
  obtain ⟨r8, h8S, h8p, h8o, h8e⟩ := rdNumsS_good (Q := CQ) (x := x) hw (q := qDom) (n := rNw)
    (i := rI) (r := rV) (p := rP) (t := rT) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s7 coords _ hx7
    (by rw [hcl]; simp [s7, Function.update_of_ne (show rNw ≠ rGj by decide)]) (by omega)
    (fun v hv => hbits v (hmem v (by tauto)))
  set s8 := rnsSt s7 qDom rI rV rP rT coords coords.length
  have hpre8 := hpre6.seq (r7.seq r8)
  have hb8 := hpre8.bdd hw hb hpx
  obtain ⟨s9, r9, h9S, h9p, h9o, h9e⟩ := moveAllS_good (x := x) hw (q := qDom) (q' := qDom2)
    (t := rT) (f := rT2) (by decide) (by decide) s8 hb8.1
  have h9D2 : s9.stk qDom2 = coords := by
    rw [h9S, Function.update_self, h8S, Function.update_self, Function.update_of_ne (by decide)]
    have e7a : s7.stk qDom = [] := by rw [(hpre6.seq r7).stk_of (by decide), hDom]
    have e7b : s7.stk qDom2 = [] := by rw [(hpre6.seq r7).stk_of (by decide), hDom2]
    rw [e7a, e7b]; simp
  have h9D : s9.stk qDom = [] := by
    rw [h9S, Function.update_of_ne (by decide), Function.update_self]
  have hpre9 := hpre8.seq r9
  have hsuf2 := r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq r9))))))
  have hsuf4 := r4.seq (r5.seq (r6.seq (r7.seq (r8.seq r9))))
  have hsuf6 := r6.seq (r7.seq (r8.seq r9))
  have hsuf7 := r7.seq (r8.seq r9)
  have hx9 : x.drop s9.pos = encodeNats (perms.flatMap permDescription) ++ rest := by
    rw [h9p, h8p, ← List.drop_drop, hx7, List.drop_left]
  -- the arguments
  obtain ⟨s10, r10, h10Ls2, h10F, h10F2, h10Dl, h10Dl2, h10D, h10D2, h10Aux, h10Rec, h10S, h10p,
      h10o, h10e⟩ := p3Args_good (x := x) hw s9 (hpre9.bdd hw hb hpx).1 (hpre9.bdd hw hb hpx).2
    locs perms cs tern base rest hlocsA
    hpermsA (pairwise_blocks _) hk hx9 (by linarith) (by omega)
    (fun u hu => lt_of_le_of_lt (hvals u (hmem u (by tauto))) hHw) (by nlinarith) (by omega)
    (fun a ha => by
      have h' : sqOff tern a n + n * sqStr tern ≤ 3 * n + 3 := sqOff_le sc n ha
      show base + sqOff tern a n + n * sqStr tern < 2 ^ w
      omega)
    (fun π hπ v hv => hbits v (hmem v (Or.inr (Or.inr (Or.inr (Or.inr
      (List.mem_flatMap.mpr ⟨π, hπ, hv⟩)))))))
    (by rw [hpre9.env_of (by decide), hKk]) (by rw [hpre9.env_of (by decide), hKL])
    (by rw [hpre9.env_of (by decide), hL]) (by rw [hsuf7.env_of (by decide), e6D])
    (by rw [(r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq r9)))))).env_of (by decide), e2T])
    (by rw [hpre9.env_of (by decide), hSB])
    (by rw [(r4.seq (r5.seq (r6.seq (r7.seq (r8.seq r9))))).env_of (by decide), e3S])
    (by rw [hsuf2.env_of (by decide), e1A])
    (by rw [hsuf6.stk_of (by decide), h5Ls2]) (by rw [hpre9.stk_of (by decide), hF])
    (by rw [hpre9.stk_of (by decide), hF2]) (by rw [hpre9.stk_of (by decide), hDl])
    (by rw [hpre9.stk_of (by decide), hDl2]) h9D h9D2 (by rw [hpre9.stk_of (by decide), hAux])
  have hpre10 := hpre9.seq r10
  have hb10 := hpre10.bdd hw hb hpx
  obtain ⟨s11, r11, h11S, h11p, h11o, h11e⟩ := moveAllS_good (x := x) hw (q := qDom2)
    (q' := qJunk) (t := rT) (f := rT2) (by decide) (by decide) s10 hb10.1
  have e10A : s10.env rA = A := by rw [h10e _ (by decide), hsuf2.env_of (by decide), e1A]
  have e10D : s10.env rD = n := by rw [h10e _ (by decide), hsuf7.env_of (by decide), e6D]
  have hAn : A * n ≤ 3 * n := Nat.mul_le_mul_right _ hA3
  have hnX : n ≤ n * (ℓ + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have r12 := mulS_good (x := x) (w := w) (Q := CQ) hw (dst := rNw) (a := rA) (b := rD)
    (j := rGj) (by decide) (by decide) (by decide) (by decide) (by decide) s11
    (by rw [h11e _ (by decide) (by decide), e10A]) (by rw [h11e _ (by decide) (by decide), e10D])
    (by omega) (by omega)
  set s12 := (s11.set rNw (A * n)).set rGj n
  have e12B : s12.env rSB = base := by
    simp only [s12, NSt.set_env, Function.update_of_ne (show rSB ≠ rGj by decide),
      Function.update_of_ne (show rSB ≠ rNw by decide)]
    rw [h11e _ (by decide) (by decide), h10e _ (by decide), hpre9.env_of (by decide), hSB]
  have e12N : s12.env rNw = A * n := by
    simp [s12, Function.update_of_ne (show rNw ≠ rGj by decide)]
  have r13 := Good.set (x := x) (w := w) (r := rSB) (e := .add (rv rSB) (rv rNw)) (st := s12)
    (by simp only [Ex.Fits, Ex.eval, rv, e12B, e12N]; omega)
  set s13 := s12.set rSB (Ex.eval s12.env (.add (rv rSB) (rv rNw)))
  have hpre13 := hpre10.seq (r11.seq (r12.seq r13))
  have e13J : s13.env rJ = j := by rw [hpre13.env_of (by decide), hJ]
  have r14 := Good.set (x := x) (w := w) (r := rJ) (e := .add (rv rJ) (.const 1)) (st := s13)
    (by simp only [Ex.Fits, Ex.eval, rv, e13J]; omega)
  set s14 := s13.set rJ (Ex.eval s13.env (.add (rv rJ) (.const 1)))
  have hall := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq
    (r10.seq (r11.seq (r12.seq (r13.seq r14))))))))))))
  have hsuf11 := r11.seq (r12.seq (r13.seq r14))
  have hsuf12 := r12.seq (r13.seq r14)
  have hsuf6' := r6.seq (r7.seq (r8.seq (r9.seq (r10.seq (r11.seq (r12.seq (r13.seq r14)))))))
  have hlen4 : (s4.stk qLs).length = A := by
    rw [h4S, Function.update_self]; simp [s3, s2, s1, hLs, hlocsA]
  have hlen8 : (s8.stk qDom).length = n * (ℓ + 1) := by
    rw [h8S, Function.update_self, (hpre6.seq r7).stk_of (by decide), hDom]; simp [hcl]
  have hlen10 : (s10.stk qDom2).length = n * (ℓ + 1) := by rw [h10D2, hcl]
  have hL : (encodeNats (schemaDescription sc)).length = (encodeNat A).length +
      (encodeNats locs).length + (encodeNat n).length + (encodeNats coords).length +
      (encodeNats (perms.flatMap permDescription)).length := by
    rw [hdesc]; simp only [List.cons_append, encNats_cons, encodeNats_append, List.length_append]
    ring
  refine ⟨s14, hall.mono ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hall.out_of (by decide), fun r hr => hall.env_of hr⟩
  · rw [hlen4, hlen8, hlen10]
    simp only [condCost, Ex.size, rv]
    rw [hL]
    have hPk : ℓ + 1 ≤ (encodeNats (perms.flatMap permDescription)).length := by
      refine le_trans ?_ (length_le_encodeNats _)
      obtain ⟨π, hπ⟩ : ∃ π, π ∈ perms := List.exists_mem_of_length_pos (by
        rw [hpermsA]; unfold A arity; split_ifs <;> omega)
      have h1 : (permDescription π).length ≤ (perms.flatMap permDescription).length := by
        rw [List.length_flatMap]; exact List.le_sum_of_mem (List.mem_map_of_mem hπ)
      have h2 := length_permDescription π
      have : ℓ + 1 ≤ k + k * ℓ := by nlinarith
      omega
    exact sch_arith _ _ _ _ _ _ _ _ _ _ _ ℓ hU0 hU' hA3 hlocsA hcl
      (hcl ▸ length_le_encodeNats coords) hPk
  · rw [hsuf6'.stk_of (by decide), h5Ls]
  · rw [hsuf11.stk_of (by decide), h10Ls2]
  · rw [hsuf11.stk_of (by decide), h10F]
  · rw [hsuf11.stk_of (by decide), h10F2]
  · rw [hsuf11.stk_of (by decide), h10Dl]
  · rw [hsuf11.stk_of (by decide), h10Dl2]
  · rw [hsuf11.stk_of (by decide), h10D]
  · rw [hsuf12.stk_of (by decide), h11S, Function.update_of_ne (by decide), Function.update_self]
  · rw [hsuf11.stk_of (by decide), h10Aux]
  · rw [hsuf11.stk_of (by decide), h10Rec, hpre9.stk_of (by decide)]
  · intro q n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11
    exact hall.stk_of (by
      simp [p3Sch, p3Args, p3Arg, p3Seq, p3Cols, p3Col, p3Advs, p3Adv, p3Bits, p3Bit, moveN,
        moveAllS, rdNumsS, rdNumS, mulS, wStk, Ne.symm n1, Ne.symm n2, Ne.symm n3, Ne.symm n4,
        Ne.symm n5, Ne.symm n6, Ne.symm n7, Ne.symm n8, Ne.symm n9, Ne.symm n10, Ne.symm n11])
  · simp only [s14, NSt.set_env, Function.update_of_ne (show rSB ≠ rJ by decide), s13,
      Function.update_self, Ex.eval, rv, e12B, e12N]
  · simp only [s14, NSt.set_env, Function.update_self, Ex.eval, rv, e13J]
  · show s11.pos = _
    rw [h11p, h10p, h9p, h8p, hL]
    show (rdNumFinal s5 rD rP rT n).pos + _ + _ = _
    rw [rdNumFinal_pos, h5p, h4p]
    show (rdNumFinal st rA rP rT A).pos + _ + _ + _ + _ = _
    rw [rdNumFinal_pos]; ring

end Lax119563Proofs.Compiler

end Compiler_PReqSch
