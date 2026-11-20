import Lax119563Proofs.Compiler.P4SchB3
import Lax119563Proofs.Compiler.PReqLoopList

/-!
# Pass `P4`, schema part: the schema body (`p4Body_good`)

`p4Body = p4Rd; p4Rec; p4Bas; p4S1; p4Mid; p4S2; p4End` processes schema `j`: it pushes the
edges `schE I ε j`, consumes the answers `(ansE I j).flatten` from `qAns` and saves them on
`qA2`, moves the record of `j` from `qS2` back onto `qSch`, advances the cursor over the
description of `j` and the schema base by `schSize I j`. The state before schema `j` is
`BInv`; **`p4Body_good`** is the step `BInv j → BInv (j + 1)`.
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- **The schema body.** -/
def p4Body : CStm CR CQ :=
  .seq p4Rd (.seq p4Rec (.seq p4Bas (.seq p4S1 (.seq p4Mid (.seq p4S2 p4End)))))

/-! ## Prefix data -/

/-- The edges of the first `j` schemas. -/
noncomputable def edUp (ε : ZMod 2) (j : ℕ) : List (ℕ × ℕ) :=
  ((List.finRange I.schemas.length).take j).flatMap (schE I ε)

/-- The answer words of the first `j` schemas. -/
noncomputable def ansUp (j : ℕ) : List ℕ :=
  ((List.finRange I.schemas.length).take j).flatMap fun e => (ansE I e).flatten

/-- The answer words of the schemas from `j` on. -/
noncomputable def ansFr (j : ℕ) : List ℕ :=
  ((List.finRange I.schemas.length).drop j).flatMap fun e => (ansE I e).flatten

/-- The base of schema `j`. -/
noncomputable def sBase (j : ℕ) : ℕ :=
  (((List.finRange I.schemas.length).take j).map (schSize I)).sum

lemma edUp_succ (ε : ZMod 2) {j : ℕ} (hj : j < I.schemas.length) :
    edUp I ε (j + 1) = edUp I ε j ++ schE I ε ⟨j, hj⟩ := by
  rw [edUp, List.take_add_one, List.getElem?_eq_getElem (by simpa using hj)]
  simp [edUp]

lemma ansUp_succ {j : ℕ} (hj : j < I.schemas.length) :
    ansUp I (j + 1) = ansUp I j ++ (ansE I ⟨j, hj⟩).flatten := by
  rw [ansUp, List.take_add_one, List.getElem?_eq_getElem (by simpa using hj)]
  simp [ansUp]

lemma ansFr_cons {j : ℕ} (hj : j < I.schemas.length) :
    ansFr I j = (ansE I ⟨j, hj⟩).flatten ++ ansFr I (j + 1) := by
  rw [ansFr, List.drop_eq_getElem_cons (by simpa using hj), List.flatMap_cons, ansFr]
  simp

lemma sBase_succ {j : ℕ} (hj : j < I.schemas.length) :
    sBase I (j + 1) = sBase I j + schSize I ⟨j, hj⟩ := by
  rw [sBase, List.take_add_one, List.getElem?_eq_getElem (by simpa using hj)]
  simp [sBase]

lemma flatten_flatMap' {α β : Type*} (l : List α) (f : α → List (List β)) :
    (l.flatMap f).flatten = l.flatMap fun a => (f a).flatten := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.flatMap_cons, List.flatten_append, ih]

lemma ansFr_zero : ansFr I 0 = (ansAll I).flatten := by
  rw [ansFr, List.drop_zero, ansAll, flatten_flatMap']

lemma ansUp_all : ansUp I I.schemas.length = (ansAll I).flatten := by
  rw [ansUp, List.take_of_length_le (by simp), ansAll, flatten_flatMap']

lemma ansFr_all : ansFr I I.schemas.length = [] := by
  rw [ansFr, List.drop_of_length_le (by simp)]; rfl

lemma edUp_all (ε : ZMod 2) : edUp I ε I.schemas.length = gEdges I ε := by
  rw [edUp, List.take_of_length_le (by simp), gEdges_eq_schE]

lemma edUp_le (ε : ZMod 2) (j : ℕ) : (edUp I ε j).length ≤ (gEdges I ε).length := by
  rw [edUp, gEdges_eq_schE]
  exact ((List.take_sublist _ _).flatMap _).length_le

lemma sBase_le (j : ℕ) : sBase I j ≤ locBase I := by
  unfold sBase locBase
  conv_rhs => rw [← List.take_append_drop j (List.finRange I.schemas.length)]
  rw [List.map_append, List.sum_append]; omega

/-! ## Numeric facts -/

lemma cL_le_H (e : Fin I.schemas.length) : (cL I e).length ≤ H I := by
  have h := schD_le_H I e
  rw [schD_len] at h
  have h1 := length_le_encodeNats ((cL I e).flatMap cdesc)
  have h2 : (cL I e).length ≤ ((cL I e).flatMap cdesc).length := by
    simp only [List.length_flatMap, length_cdesc, List.map_const', List.sum_replicate,
      smul_eq_mul]
    exact Nat.le_mul_of_pos_right _ (by omega)
  omega

lemma ansB_le (hℓ : 1 ≤ ℓ) (e : Fin I.schemas.length) :
    ansBase I e + 3 * (cL I e).length ≤ 3 * H I := by
  have h1 := ansBase_le I (e + 1)
  rw [ansBase_succ I e.2] at h1
  simp only [Fin.eta] at h1
  have ha : 2 ≤ arity (sch I e) := by unfold arity; split_ifs <;> omega
  have h2 : 2 * (cL I e).length ≤ arity (sch I e) * (coordList (dom I e)).length :=
    Nat.mul_le_mul_right _ ha
  have h3 : (ansBase I e + arity (sch I e) * (coordList (dom I e)).length) * 2 ≤
      (ansBase I e + arity (sch I e) * (coordList (dom I e)).length) * (ℓ + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  simp only [cL] at h2 ⊢
  omega

lemma rowsR_len (e : Fin I.schemas.length) :
    (rowsR I e).length = blkRows (cL I e) + (orsL (cL I e)).sum := by
  have h1 := length_coefSteps I e
  rw [length_coefSteps' I e, ← sum_orsL] at h1
  exact Nat.eq_of_mul_eq_mul_left (by omega) h1

lemma schE_le_gEdges (ε : ZMod 2) (e : Fin I.schemas.length) :
    (schE I ε e).length ≤ (gEdges I ε).length := by
  rw [gEdges_eq_schE, List.length_flatMap]
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨e, List.mem_finRange e, rfl⟩)

/-! ## The invariant -/

/-- Registers written by the schema body. -/
def bodyW : List (Fin CR) :=
  [rT, rP, rJ, r4SB, r4Tn, r4D, r4BR, r4R2, r4NE, r4NC, r4SuB, r4TrB, rc1, rc2, rc3, rc4, rc5,
    rc6, rc7, rc8, r4Dist, r4Prev, r4TP, r4H, r4SP, r4K, r4F, r4V, r4M]

/-- Stacks changed by the schema body. -/
def bodyQ : List (Fin CQ) := [qS2, qSch, qAns, qA2, q4E, qRk, qRkF, qOrsF, qOrsB]

/-- The fixed data of the schema loop (`s0`: the state before the loop). -/
def BFix (w : ℕ) (ε : ZMod 2) (s0 : NSt CR CQ) : Prop :=
  I.schemas ≠ [] ∧ 2 ≤ k ∧ 1 ≤ ℓ ∧ 16 * (H I + (ordL I).length + 1) ≤ 2 ^ w ∧
  s0.env rL = ℓ ∧ s0.env rKk = k ∧ s0.env rLB = locBase I ∧ s0.env r4Eps = ε.val ∧
  s0.env r4PL = k * (ℓ + 1) ∧ s0.env r4M = 0

/-- **The state before schema `j`.** -/
def BInv (w : ℕ) (ε : ZMod 2) (s0 : NSt CR CQ) (j : ℕ) (s : NSt CR CQ) : Prop :=
  j ≤ I.schemas.length ∧ s.env rJ = j ∧ s.pos = schAt I j ∧ s.env r4SB = sBase I j ∧
  s.stk qS2 = schRecsFrom I j ∧ s.stk qSch = (schRecsUpTo I j).reverse ∧
  s.stk qAns = ansFr I j ∧ s.stk qA2 = (ansUp I j).reverse ∧
  s.stk q4E = pairsRev (edUp I ε j) ++ s0.stk q4E ∧ s.stk qRk = [] ∧ s.stk qRkF = [] ∧
  s.stk qOrsF = [] ∧ s.stk qOrsB = [] ∧ (∀ q, q ∉ bodyQ → s.stk q = s0.stk q) ∧
  s.env r4M = (edUp I ε j).length ∧ s.out = s0.out ∧ s.Bdd w ∧
  ∀ r, r ∉ bodyW → s.env r = s0.env r

lemma codes_len_le (hk : 2 ≤ k) (e : Fin I.schemas.length) :
    ((cL I e).flatMap fun c => codesL I e c ++ [0]).length ≤ nEnt I e := by
  rw [List.length_flatMap, nEnt]
  apply List.sum_le_sum
  intro c _
  simp only [List.length_append, length_codesL, List.length_singleton]
  rw [length_stepsC_rowsL]
  have := rowsL_pos hk c
  nlinarith

lemma body_arith {N U hdr co pe nE cl ℓ sz rk : ℕ} (hU : U ≤ N) (hN : 64 ≤ U)
    (hl : ℓ + 1 ≤ pe) (hrk : rk ≤ nE) (hsz : 6 * nE + 2 * cl ≤ sz) :
    100 * N * (hdr + 1) + ((ℓ + 1) * (40 * N) + 30 * N + (80 * N +
      (2100 * (co + nE + cl + 1) * N + (10 * N * rk + 12 * N * ℓ + 40 * N * pe + 300 * N +
        ((3200 * N * nE + cl * (3 * N + 1) + (3 * N + 1)) + 20 * N))))) ≤
      5000 * N * (hdr + co + pe + sz + 1) := by
  have h1 : 10 * N * rk ≤ 10 * N * nE := Nat.mul_le_mul_left _ hrk
  have h2 : (ℓ + 1) * (40 * N) ≤ pe * (40 * N) := Nat.mul_le_mul_right _ hl
  have h3 : 12 * N * ℓ ≤ 12 * N * pe := Nat.mul_le_mul_left _ (by omega)
  have h4 : (6 * nE + 2 * cl) * (1052 * N) ≤ sz * (1052 * N) := Nat.mul_le_mul_right _ hsz
  nlinarith

end Lax119563Proofs.Compiler
