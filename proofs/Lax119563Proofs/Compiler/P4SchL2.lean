import Lax119563Proofs.Compiler.P4SchL1b
import Lax119563Proofs.Compiler.P4SchGlue2
import Lax119563Proofs.Compiler.PChainSize

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
