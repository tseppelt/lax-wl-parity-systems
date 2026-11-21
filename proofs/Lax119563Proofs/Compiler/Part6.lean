import Lax119563Proofs.Compiler.Part1
import Lax119563Proofs.Compiler.Part2
import Lax119563Proofs.Compiler.Part3
import Lax119563Proofs.Compiler.Part4
import Lax119563Proofs.Compiler.Part5
import Lax119563Proofs.Machines.Part1

/-! ### Formerly `Lax119563Proofs.Compiler.PReqLoopList` -/

section Compiler_PReqLoopList

/-!
# Pass `P3`, request generation: list facts for the schema loop

* `argsReqs_eq_reqsE`: the requests pushed by `p3Sch` for schema `e` at the sequence base
  `ansBase I e` are `reqsE I e` (via `seqOff_eq`);
* `reqsUpTo_succ`, `reqsUpTo_all`;
* sizes: `ansBase_mul_le` (`ansBase I j · (ℓ + 1) ≤ 3 |encodeNats (schsPre I j)|`),
  `length_reqsUpTo`, `schD_vals_le` (every number of a schema description is `≤ H`),
  `length_locRecs_mul_le` (`|locRecs I| (ℓ + 1) ≤ H`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

lemma argsReqs_eq_reqsE (e : Fin I.schemas.length) :
    argsReqs (schLocs (sch I e)) (schPerms (sch I e)) (coordList (sch I e).domain) (ansBase I e)
      (Matrix.isTern (sch I e)) (arity (sch I e)) = reqsE I e := by
  have hl : ((schLocs (sch I e)).zip (schPerms (sch I e))).zipIdx.length = arity (sch I e) := by
    simp [length_schLocs, length_schPerms]
  rw [argsReqs, List.take_of_length_le (le_of_eq hl), reqsE]
  refine List.flatMap_congr fun p hp => ?_
  have hp2 : p.2 < arity (sch I e) := by
    have := (List.mem_zipIdx' (x := p.1) (i := p.2) hp).1
    simpa [length_schLocs, length_schPerms] using this
  rw [argReqs, colReqs]
  refine List.map_congr_left fun q _ => ?_
  rw [seqOff_eq _ _ _ _ (by unfold arity at hp2; split_ifs at hp2 <;> simp_all), add_assoc]
  rfl

lemma reqsUpTo_succ {j : ℕ} (hj : j < I.schemas.length) :
    reqsUpTo I (j + 1) = reqsUpTo I j ++ reqsE I ⟨j, hj⟩ := by
  rw [reqsUpTo, List.take_add_one, List.getElem?_eq_getElem (by simpa using hj)]
  simp [reqsUpTo]

lemma reqsUpTo_all : reqsUpTo I I.schemas.length = reqs I := by
  rw [reqsUpTo, reqs, List.take_of_length_le (by simp)]

lemma length_reqsE (e : Fin I.schemas.length) :
    (reqsE I e).length = arity (sch I e) * (coordList (dom I e)).length := by
  rw [reqsE, List.length_flatMap]
  have : (((schLocs (sch I e)).zip (schPerms (sch I e))).zipIdx.map fun
      (p : (ℕ × BlockPerm k ℓ) × ℕ) => ((coordList (dom I e)).zipIdx.map fun
        (q : Coord k ℓ × ℕ) => reqRec p.1.1 p.1.2 q.1
          (ansBase I e + seqOff (Matrix.isTern (sch I e)) (coordList (dom I e)).length p.2
            q.2)).length) =
      ((schLocs (sch I e)).zip (schPerms (sch I e))).zipIdx.map fun _ =>
        (coordList (dom I e)).length :=
    List.map_congr_left fun p _ => by simp
  rw [this, sum_map_const]
  simp [length_schLocs, length_schPerms]

lemma length_reqsUpTo : ∀ j, (reqsUpTo I j).length = ansBase I j
  | 0 => by simp [reqsUpTo, ansBase]
  | j + 1 => by
    by_cases hj : j < I.schemas.length
    · rw [reqsUpTo_succ I hj, ansBase_succ I hj, List.length_append, length_reqsUpTo j,
        length_reqsE]
    · have h1 : (List.finRange I.schemas.length).take (j + 1) =
          (List.finRange I.schemas.length).take j := by
        rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega)]
      rw [reqsUpTo, ansBase, h1, ← reqsUpTo, ← ansBase, length_reqsUpTo j]

lemma dom_mul_le (e : Fin I.schemas.length) :
    (coordList (dom I e)).length * (ℓ + 1) ≤ (encodeNats (schD I e)).length := by
  refine le_trans ?_ (length_le_encodeNats _)
  rw [schD, schemaDescription_eq', ← length_flatMap_cdesc]
  simp only [List.length_append, List.length_cons]
  change ((coordList (sch I e).domain).flatMap cdesc).length ≤ _
  omega

lemma ansBase_mul_le : ∀ j, ansBase I j * (ℓ + 1) ≤ 3 * (encodeNats (schsPre I j)).length
  | 0 => by simp [ansBase]
  | j + 1 => by
    by_cases hj : j < I.schemas.length
    · rw [ansBase_succ I hj, schsPre_succ I hj, encodeNats_append, List.length_append]
      have ih := ansBase_mul_le j
      have h1 := dom_mul_le I ⟨j, hj⟩
      have h2 : arity (sch I ⟨j, hj⟩) ≤ 3 := arity_le' _
      have h3 : arity (sch I ⟨j, hj⟩) * (coordList (dom I ⟨j, hj⟩)).length * (ℓ + 1) ≤
          3 * ((coordList (dom I ⟨j, hj⟩)).length * (ℓ + 1)) := by
        rw [mul_assoc]; exact Nat.mul_le_mul_right _ h2
      nlinarith
    · have h1 : (List.finRange I.schemas.length).take (j + 1) =
          (List.finRange I.schemas.length).take j := by
        rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega)]
      have ih := ansBase_mul_le j
      rw [ansBase, schsPre, h1] at *
      exact ih

lemma schsPre_enc_le (j : ℕ) : (encodeNats (schsPre I j)).length ≤ H I := by
  have := schAt_le I j; unfold schAt at this; omega

lemma ansBase_le (j : ℕ) : ansBase I j * (ℓ + 1) ≤ 3 * H I :=
  (ansBase_mul_le I j).trans (Nat.mul_le_mul_left _ (schsPre_enc_le I j))

lemma length_reqs_mul_le : (reqs I).length * (ℓ + 1) ≤ 3 * H I := by
  rw [← reqsUpTo_all, length_reqsUpTo]; exact ansBase_le I _

lemma length_recsUpTo_mul_le : ∀ j, j ≤ I.numLocations →
    (recsUpTo I j).length * (ℓ + 1) ≤ (locsPre I j).length
  | 0, _ => by simp [recsUpTo]
  | j + 1, hj => by
    have ih := length_recsUpTo_mul_le j (by omega)
    rw [recsUpTo_succ I (by omega), locsPre_succ I (by omega), List.length_append,
      List.length_append, locD_eq']
    have := length_flatten_cnd I ⟨j, by omega⟩
    simp only [recsV, List.length_map, List.length_range, List.length_cons]
    nlinarith

lemma length_locRecs_mul_le : (locRecs I).length * (ℓ + 1) ≤ H I := by
  rw [← recsUpTo_all]
  exact (length_recsUpTo_mul_le I _ le_rfl).trans (locsPre_le I _)

/-- Every number of a schema description is at most `H` (given `k ≤ H`). -/
lemma schD_vals_le (hkH : k ≤ H I) (e : Fin I.schemas.length) :
    ∀ v ∈ schemaDescription (sch I e), v ≤ H I := by
  have h3 := three_le_H I
  have hW := W_le I
  have hd : (coordList (sch I e).domain).length ≤ H I := by
    have h1 := dom_mul_le I e
    have h2 := schD_le_H I e
    have : (coordList (dom I e)).length ≤ (coordList (dom I e)).length * (ℓ + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    exact le_trans this (h1.trans h2)
  have hbd : ∀ (b : BlockCoord ℓ), ∀ v ∈ blockDescription b, v ≤ H I := by
    intro b v hv
    simp only [blockDescription, List.mem_map, List.mem_finRange, true_and] at hv
    obtain ⟨t, rfl⟩ := hv
    have : (b t).val < 2 := ZMod.val_lt (b t)
    omega
  intro v hv
  rw [schemaDescription_eq'] at hv
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_flatMap] at hv
  rcases hv with rfl | (hv | rfl | ⟨c, -, hc⟩) | ⟨π, -, hπ⟩
  · exact (arity_le' _).trans h3
  · exact (schLocs_le _ v hv).le.trans hW
  · exact hd
  · simp only [cdesc, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact c.1.isLt.le.trans hkH
    · exact hbd _ v hc
  · simp only [permDescription, List.mem_append, List.mem_map, List.mem_finRange, true_and,
      List.mem_flatMap] at hπ
    rcases hπ with ⟨i, hi⟩ | ⟨i, hi⟩
    · rw [← hi]; exact (Fin.isLt _).le.trans hkH
    · exact hbd _ v hi

end Lax119563Proofs.Compiler

end Compiler_PReqLoopList

/-! ### Formerly `Lax119563Proofs.Compiler.P3Aux` -/

section Compiler_P3Aux

/-!
# Pass `P3`: list facts used by the assembly

On top of `PJoinFacts` (`union I = locRecs I ++ reqs I`, `p3_answers`, word bounds):
* `p3Union I`: the union sorted by `CSort.rle`; `p3Scan I`: the answers of the scan over it;
* `p3Ans_eq`: the answers sorted by `CSort.rle` are `ansAll I` (the order of `P4`);
* sizes: `length_flatten_union`, `union_mul_le` (`|union I| (ℓ + 1) ≤ 4 H`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

lemma length_flatten_union :
    (union I).flatten.length = ((locRecs I).length + (reqs I).length) * (ℓ + 6) := by
  rw [List.length_flatten]
  have : (union I).map List.length = (union I).map fun _ => ℓ + 6 :=
    List.map_congr_left fun m hm => length_of_mem_union I hm
  rw [this, sum_map_const, union, List.length_append]

lemma union_mul_le : ((locRecs I).length + (reqs I).length) * (ℓ + 1) ≤ 4 * H I := by
  have h1 := length_locRecs_mul_le I
  have h2 := length_reqs_mul_le I
  nlinarith

/-- The sorted union of the location records and the requests. -/
noncomputable def p3Union : List (List ℕ) := (union I).mergeSort CSort.rle

/-- The answers of the scan (in the order of the sorted union). -/
noncomputable def p3Scan : List (List ℕ) := jScan ℓ (0, 0, 0) (p3Union I)

lemma mem_p3Union {m : List ℕ} : m ∈ p3Union I ↔ m ∈ union I :=
  (List.mergeSort_perm _ _).mem_iff

lemma length_p3Union : (p3Union I).length = (locRecs I).length + (reqs I).length := by
  rw [p3Union, List.length_mergeSort, union, List.length_append]

lemma length_p3Scan : (p3Scan I).length = (reqs I).length := by
  rw [p3Scan, p3Union, length_jScan I _ (List.Perm.refl _), length_reqs]

/-- **The answers of `P3`** in the order of `P4`. -/
lemma p3Ans_eq : (p3Scan I).reverse.mergeSort CSort.rle = ansAll I :=
  p3_answers I _ (List.Perm.refl _) _

lemma p3Scan_words (hE : I.schemas ≠ []) {w : ℕ} (hw : 4 * (H I + 1) ≤ 2 ^ w) :
    ∀ y ∈ p3Scan I, y.length = 4 ∧ ∀ z ∈ y, z < 2 ^ w := fun _ hy =>
  ⟨length_of_mem_jScan I _ (List.Perm.refl _) _ hy,
    lt_of_mem_jScan I hE hw _ (List.Perm.refl _) _ hy⟩

end Lax119563Proofs.Compiler

end Compiler_P3Aux

/-! ### Formerly `Lax119563Proofs.Compiler.P3Join` -/

section Compiler_P3Join

/-!
# Pass `P3`, second part: union sort, scan, sort of the answers

`p3Join` sorts the `rCnt + rSB` records of `ℓ + 6` words on `qX` (`sortS`), answers the
requests by the scan `pJScan` (answers on `qAns`) and sorts the `rSB` answers of `4` words
(**`p3Join_good`**: `qAns` ends holding `(ansAll I).flatten`, the order of `P4`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

/-! ## Registers of the sorts -/

/-- The record width of the sorts. -/
def rsA : Fin CR := 38
def rsDir : Fin CR := 20
def rsC : Fin CR := 21
def rsF1 : Fin CR := 22
def rsF2 : Fin CR := 23
def rsKc : Fin CR := 24
def rsT1 : Fin CR := 25
def rsT2 : Fin CR := 26
def rsI : Fin CR := 27
def rsT : Fin CR := 29
def rsR : Fin CR := 30
def rsDone : Fin CR := 39
def rsK : Fin CR := 32
def rsLim : Fin CR := 33

/-- Sort the `rN` records of `rsA` words on stack `X`. -/
def p3Sort (X : Fin CQ) : CStm CR CQ :=
  sortS X qT1 qT2 qY qTmp qC1 qC2 rsA rsDir rsC rsF1 rsF2 rsKc rsT1 rsT2 rsI rsT rsR rN rsDone
    rsK rsLim

/-- **The join part of `P3`.** -/
def p3Join : CStm CR CQ :=
  .seq (.set rN (.add (rv rCnt) (rv rSB))) (.seq (.set rsA (.add (rv rL) (.const 6)))
    (.seq (p3Sort qX) (.seq (.set rCo (.const 0)) (.seq (.set rCl (.const 0))
      (.seq (.set rCs (.const 0)) (.seq pJScan (.seq (.set rN (rv rSB))
        (.seq (.set rsA (.const 4)) (p3Sort qAns)))))))))

lemma log_le_of_le_four {n h : ℕ} (hn : n ≤ 4 * (h + 1)) :
    Nat.log 2 n ≤ Nat.log 2 (h + 1) + 2 := by
  calc Nat.log 2 n ≤ Nat.log 2 (2 * (2 * (h + 1))) := Nat.log_mono_right (by omega)
    _ ≤ Nat.log 2 (2 * (h + 1)) + 1 := log_two_mul_le _
    _ ≤ Nat.log 2 (h + 1) + 1 + 1 := by have := log_two_mul_le (h + 1); omega

lemma p3Join_arith (N U n m ℓ h lg ln lm : ℕ) (hU : U ≤ N) (hn : n * (ℓ + 1) ≤ 4 * h)
    (hℓ : ℓ ≤ h) (hm : m ≤ 3 * h) (hln : ln ≤ lg + 2) (hlm : lm ≤ lg + 2) (h3 : 3 ≤ h) :
    (1 + 1 + 1) * N + U + ((1 + 1 + 1) * N + U +
      ((n + 1) * (ln + 2) * (700 * (ℓ + 6 + 1) * N) + (1 * N + U + (1 * N + U + (1 * N + U +
        ((n + 1) * ((ℓ + 21) * (12 * N)) + (1 * N + U + (1 * N + U +
          (m + 1) * (lm + 2) * (700 * (4 + 1) * N))))))))) ≤
      150000 * (h + 1) * (lg + 1) * N := by
  have hn1 : n ≤ n * (ℓ + 1) := Nat.le_mul_of_pos_right _ (by omega)
  -- the first sort
  have p1 : (n + 1) * (ℓ + 7) ≤ 29 * (h + 1) := by
    have : (n + 1) * (ℓ + 7) = n * (ℓ + 1) + 6 * n + ℓ + 7 := by ring
    omega
  have q1 : ln + 2 ≤ 4 * (lg + 1) := by omega
  have t1 : (n + 1) * (ln + 2) * (700 * (ℓ + 6 + 1) * N) ≤
      700 * (29 * (h + 1)) * (4 * (lg + 1)) * N := by
    have : (n + 1) * (ln + 2) * (700 * (ℓ + 6 + 1) * N) =
        700 * ((n + 1) * (ℓ + 7)) * (ln + 2) * N := by ring
    rw [this]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ p1) q1)
  -- the scan
  have p2 : (n + 1) * (ℓ + 21) ≤ 105 * (h + 1) := by
    have : (n + 1) * (ℓ + 21) = n * (ℓ + 1) + 20 * n + ℓ + 21 := by ring
    omega
  have t2 : (n + 1) * ((ℓ + 21) * (12 * N)) ≤ 12 * (105 * (h + 1)) * (lg + 1) * N := by
    have : (n + 1) * ((ℓ + 21) * (12 * N)) = 12 * ((n + 1) * (ℓ + 21)) * 1 * N := by ring
    rw [this]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ p2) (by omega))
  -- the second sort
  have q3 : lm + 2 ≤ 4 * (lg + 1) := by omega
  have t3 : (m + 1) * (lm + 2) * (700 * (4 + 1) * N) ≤ 3500 * (3 * (h + 1)) * (4 * (lg + 1)) * N := by
    have : (m + 1) * (lm + 2) * (700 * (4 + 1) * N) = 3500 * (m + 1) * (lm + 2) * N := by ring
    rw [this]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) q3)
  have t0 : 20 * N ≤ 20 * (h + 1) * (lg + 1) * N := by
    have : 1 ≤ (h + 1) * (lg + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith
  have e : 700 * (29 * (h + 1)) * (4 * (lg + 1)) * N + 12 * (105 * (h + 1)) * (lg + 1) * N +
      3500 * (3 * (h + 1)) * (4 * (lg + 1)) * N + 20 * (h + 1) * (lg + 1) * N =
      124480 * ((h + 1) * (lg + 1) * N) := by ring
  have e' : 150000 * (h + 1) * (lg + 1) * N = 150000 * ((h + 1) * (lg + 1) * N) := by ring
  rw [e']
  omega

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

set_option maxHeartbeats 4000000 in
/-- **The join part of `P3`.** With `(union I).flatten` on `qX`, `rCnt = |locRecs I|`,
`rSB = |reqs I|`, `rL = ℓ` and `qT1, qT2, qY, qAns` empty, `p3Join` leaves the sorted answers
`(ansAll I).flatten` on `qAns` and empties `qX`. -/
theorem p3Join_good {w : ℕ} (hw : 2 ≤ w) (hk : 1 ≤ k) (hE : I.schemas ≠ [])
    (hS : 16 * (H I + 1) ≤ 2 ^ w)
    (s : NSt CR CQ) (hX : s.stk qX = (union I).flatten) (hT1 : s.stk qT1 = [])
    (hT2 : s.stk qT2 = []) (hY : s.stk qY = []) (hAns : s.stk qAns = []) (hL : s.env rL = ℓ)
    (hC : s.env rCnt = (locRecs I).length) (hSB : s.env rSB = (reqs I).length) :
    ∃ s', Good (encodeSystem I) w p3Join s s'
        (150000 * (H I + 1) * (Nat.log 2 (H I + 1) + 1) * Ex.nodeCost w) ∧
      s'.stk qAns = (ansAll I).flatten ∧ s'.stk qX = [] ∧
      (∀ q, q ≠ qX → q ≠ qAns → q ≠ qJunk → s'.stk q = s.stk q) ∧
      s'.pos = s.pos ∧ s'.out = s.out ∧ ∀ r, wReg r p3Join = false → s'.env r = s.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hU0 := Ex.unitCost_le_nodeCost w
  have hℓ := ell_le_H I hk (fun h => hE h.2)
  have h3H := three_le_H I
  have hcnt := union_mul_le I
  have hreq := length_reqs_mul_le I
  set n := (locRecs I).length + (reqs I).length with hn
  set m := (reqs I).length with hm
  have hn1 : n ≤ n * (ℓ + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hm1 : m ≤ m * (ℓ + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hw0 : 0 < 2 ^ w := by positivity
  have hrw : ∀ y ∈ union I, y.length = ℓ + 6 ∧ ∀ z ∈ y, z < 2 ^ w :=
    fun y hy => ⟨length_of_mem_union I hy, lt_of_mem_union I hE (by omega) hy⟩
  -- `rN := rCnt + rSB`
  have r1 := Good.set (x := encodeSystem I) (w := w) (st := s) (r := rN)
    (e := .add (rv rCnt) (rv rSB)) (by simp only [Ex.Fits, Ex.eval, rv, hC, hSB]; omega)
  set s1 := s.set rN ((Ex.add (rv rCnt) (rv rSB)).eval s.env)
  have e1N : s1.env rN = n := by simp [s1, Ex.eval, rv, hC, hSB, n, m]
  have r2 := Good.set (x := encodeSystem I) (w := w) (st := s1) (r := rsA)
    (e := .add (rv rL) (.const 6)) (by
      have : s1.env rL = ℓ := by simp [s1, Function.update_of_ne (show rL ≠ rN by decide), hL]
      simp only [Ex.Fits, Ex.eval, rv, this]; omega)
  set s2 := s1.set rsA ((Ex.add (rv rL) (.const 6)).eval s1.env)
  have e2A : s2.env rsA = ℓ + 6 := by
    simp [s2, s1, Ex.eval, rv, Function.update_of_ne (show rL ≠ rN by decide), hL]
  have e2N : s2.env rN = n := by
    simp only [s2, NSt.set_env, Function.update_of_ne (show rN ≠ rsA by decide)]; exact e1N
  -- the union sort
  obtain ⟨s3, r3, h3S, f3⟩ := sortS_good (x := encodeSystem I) (X := qX) (T1 := qT1) (T2 := qT2)
    (Y := qY) (tmp := qTmp) (C1 := qC1) (C2 := qC2) (A := rsA) (dir := rsDir) (c := rsC)
    (f1 := rsF1) (f2 := rsF2) (kc := rsKc) (t1 := rsT1) (t2 := rsT2) (i := rsI) (t := rsT)
    (r := rsR) (N := rN) (done := rsDone) (k := rsK) (lim2 := rsLim) (a := ℓ + 6) (n := n) hw (by decide) (by decide)
    s2 (union I) hX hT1 hT2 hY e2A (by omega) e2N (by simp [n, union]) hrw (by omega)
    (by omega)
  have r4 := Good.set (x := encodeSystem I) (w := w) (st := s3) (r := rCo) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  set s4 := s3.set rCo ((Ex.const 0 : Ex CR).eval s3.env)
  have r5 := Good.set (x := encodeSystem I) (w := w) (st := s4) (r := rCl) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  set s5 := s4.set rCl ((Ex.const 0 : Ex CR).eval s4.env)
  have r6 := Good.set (x := encodeSystem I) (w := w) (st := s5) (r := rCs) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  set s6 := s5.set rCs ((Ex.const 0 : Ex CR).eval s5.env)
  have h6S : s6.stk = s3.stk := rfl
  have f36 : ∀ r, r ≠ rCo → r ≠ rCl → r ≠ rCs → s6.env r = s3.env r := fun r h1 h2 h3 => by
    simp [s6, s5, s4, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3]
  have e6N : s6.env rN = n := by
    rw [f36 _ (by decide) (by decide) (by decide), f3.2.2 rN (by decide), e2N]
  have e6L : s6.env rL = ℓ := by
    rw [f36 _ (by decide) (by decide) (by decide), f3.2.2 rL (by decide)]
    simp [s2, s1, Function.update_of_ne (show rL ≠ rN by decide),
      Function.update_of_ne (show rL ≠ rsA by decide), hL]
  have e6SB : s6.env rSB = m := by
    rw [f36 _ (by decide) (by decide) (by decide), f3.2.2 rSB (by decide)]
    simp [s2, s1, Function.update_of_ne (show rSB ≠ rN by decide),
      Function.update_of_ne (show rSB ≠ rsA by decide), hSB, m]
  have e6a : s6.env rCo = 0 := by
    simp [s6, s5, s4, Ex.eval, Function.update_of_ne (show rCo ≠ rCs by decide),
      Function.update_of_ne (show rCo ≠ rCl by decide)]
  have e6b : s6.env rCl = 0 := by
    simp [s6, s5, Ex.eval, Function.update_of_ne (show rCl ≠ rCs by decide)]
  have e6d : s6.env rCs = 0 := by simp [s6, Ex.eval]
  -- the scan
  have hU3 : ∀ y ∈ p3Union I, y.length = ℓ + 6 ∧ ∀ z ∈ y, z < 2 ^ w :=
    fun y hy => hrw y ((mem_p3Union I).mp hy)
  obtain ⟨s7, r7, h7X, h7A, h7S, h7p, h7o, h7e⟩ := pJScan_good (x := encodeSystem I) hw s6
    (p3Union I) (by rw [h6S, h3S, Function.update_self]; rfl) e6L
    (by rw [e6N, length_p3Union]) (fun r hr => (hU3 r hr).1) (fun r hr => (hU3 r hr).2)
    (by omega) (by rw [length_p3Union]; omega) (by rw [e6a, e6b, e6d]; simp [hw0])
  have h6A : s6.stk qAns = [] := by
    rw [h6S, h3S, Function.update_of_ne (by decide)]; exact hAns
  -- `rN := rSB`, `rsA := 4`
  have e7SB : s7.env rSB = m := by rw [h7e _ (by decide), e6SB]
  have r8 := Good.set (x := encodeSystem I) (w := w) (st := s7) (r := rN) (e := rv rSB)
    (by simp only [Ex.Fits, rv, e7SB]; omega)
  set s8 := s7.set rN ((rv rSB : Ex CR).eval s7.env)
  have r9 := Good.set (x := encodeSystem I) (w := w) (st := s8) (r := rsA) (e := .const 4)
    (by simp only [Ex.Fits]; omega)
  set s9 := s8.set rsA ((Ex.const 4 : Ex CR).eval s8.env)
  have h9S : s9.stk = s7.stk := rfl
  have hscan : (p3Scan I).length = m := length_p3Scan I
  have hwB := p3Scan_words I hE (w := w) (by omega)
  -- the sort of the answers
  obtain ⟨s10, r10, h10S, f10⟩ := sortS_good (x := encodeSystem I) (X := qAns) (T1 := qT1)
    (T2 := qT2) (Y := qY) (tmp := qTmp) (C1 := qC1) (C2 := qC2) (A := rsA) (dir := rsDir)
    (c := rsC) (f1 := rsF1) (f2 := rsF2) (kc := rsKc) (t1 := rsT1) (t2 := rsT2) (i := rsI)
    (t := rsT) (r := rsR) (N := rN) (done := rsDone) (k := rsK) (lim2 := rsLim) (a := 4) (n := m) hw (by decide)
    (by decide) s9 (p3Scan I).reverse
    (by rw [h9S, h7A, h6A, List.append_nil, e6a, e6b, e6d]; rfl)
    (by rw [h9S, h7S _ (by decide) (by decide) (by decide), h6S, h3S,
      Function.update_of_ne (by decide)]; exact hT1)
    (by rw [h9S, h7S _ (by decide) (by decide) (by decide), h6S, h3S,
      Function.update_of_ne (by decide)]; exact hT2)
    (by rw [h9S, h7S _ (by decide) (by decide) (by decide), h6S, h3S,
      Function.update_of_ne (by decide)]; exact hY)
    (by simp [s9, Ex.eval]) (by omega)
    (by simp [s9, s8, Ex.eval, rv, Function.update_of_ne (show rN ≠ rsA by decide), e7SB])
    (by rw [List.length_reverse, hscan])
    (fun y hy => by
      have := hwB y (List.mem_reverse.mp hy)
      exact this)
    (by omega) (by omega)
  have hall := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq r10))))))))
  refine ⟨s10, hall.mono ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => hall.env_of hr⟩
  · rw [length_p3Union]
    simp only [condCost, Ex.size, rv]
    have hlg1 : Nat.log 2 n ≤ Nat.log 2 (H I + 1) + 2 := log_le_of_le_four (by omega)
    have hlg2 : Nat.log 2 m ≤ Nat.log 2 (H I + 1) + 2 := log_le_of_le_four (by omega)
    exact p3Join_arith _ _ n m ℓ (H I) _ _ _ hU0 hcnt hℓ (by omega) hlg1 hlg2 h3H
  · rw [h10S, Function.update_self, p3Ans_eq]
  · rw [h10S, Function.update_of_ne (by decide), h9S, h7X]
  · intro q h1 h2 h3
    rw [h10S, Function.update_of_ne h2, h9S, h7S q h1 h2 h3, h6S, h3S, Function.update_of_ne h1]
    rfl
  · rw [f10.1, show s9.pos = s7.pos from rfl, h7p, show s6.pos = s3.pos from rfl, f3.1]; rfl
  · rw [f10.2.1, show s9.out = s7.out from rfl, h7o, show s6.out = s3.out from rfl, f3.2.1]; rfl

end Lax119563Proofs.Compiler

end Compiler_P3Join

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchB4` -/

section Compiler_P4SchB4

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

end Compiler_P4SchB4

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchB5` -/

section Compiler_P4SchB5

/-!
# Pass `P4`, schema part: one schema (`p4Body_good`)
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

lemma notMem_of_bodyW_rd : ∀ r : Fin CR, r ∉ bodyW → r ∉ [rc1, rc2, rP, rT, r4Tn, r4D] := by
  decide
lemma notMem_of_bodyW_rec :
    ∀ r : Fin CR, r ∉ bodyW → r ∉ [rT, rP, rc1, r4R2, r4BR, r4NE, r4NC] := by decide
lemma notMem_of_bodyW_bas : ∀ r : Fin CR, r ∉ bodyW → r ∉ basW := by decide
lemma notMem_of_bodyW_c1 : ∀ r : Fin CR, r ∉ bodyW → r ∉ c1W := by decide
lemma notMem_of_bodyW_mid : ∀ r : Fin CR, r ∉ bodyW → r ∉ midW := by decide
lemma notMem_of_bodyW_c2 : ∀ r : Fin CR, r ∉ bodyW → r ∉ c2W := by decide
lemma notMem_of_bodyW_end : ∀ r : Fin CR, r ∉ bodyW → r ≠ r4SB ∧ r ≠ rJ := by decide

lemma schSize_ge (e : Fin I.schemas.length) :
    6 * nEnt I e + 2 * (cL I e).length ≤ schSize I e := by
  rw [schSize_eq' I e]; simp only [cL]; split_ifs <;> omega

lemma permsL_ge (hk : 2 ≤ k) (e : Fin I.schemas.length) :
    ℓ + 1 ≤ (encodeNats (permsL I e)).length := by
  have h1 := length_le_encodeNats (permsL I e)
  rw [length_permsL] at h1
  have ha : 2 ≤ arity (sch I e) := by unfold arity; split_ifs <;> omega
  have h2 : 1 * (ℓ + 1) ≤ arity (sch I e) * k * (ℓ + 1) :=
    Nat.mul_le_mul_right _ (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))
  rw [Nat.mul_assoc] at h2
  omega

set_option maxHeartbeats 40000000 in
/-- **One schema.** -/
theorem p4Body_good {w : ℕ} (hw : 2 ≤ w) (ε : ZMod 2) (s0 : NSt CR CQ) (hF : BFix I w ε s0)
    {j : ℕ} (hj : j < I.schemas.length) (s : NSt CR CQ) (hI : BInv I w ε s0 j s) :
    ∃ s', Good (encodeSystem I) w p4Body s s'
        (5000 * Ex.nodeCost w * ((encodeNats (schD I ⟨j, hj⟩)).length +
          schSize I ⟨j, hj⟩ + 1)) ∧
      BInv I w ε s0 (j + 1) s' := by
  obtain ⟨hE, hk, hℓ, hW16, f0L, f0k, f0LB, f0Eps, f0PL, f0M⟩ := hF
  obtain ⟨hjE, eJ, hpos, eSB, hS2, hSch, hAns, hA2, h4E, hRk, hRkF, hOF, hOB, hoth, eM, hout,
    hbd, hfr⟩ := hI
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  set e : Fin I.schemas.length := ⟨j, hj⟩ with he
  have hH : 4 * (H I + 1) ≤ 2 ^ w := by omega
  have hkl := kl_le_H I hE
  have hcl := cL_le_H I e
  have hab := ansB_le I hℓ e
  have hLB := locBase_le_length I
  have hgE := length_gEdges I ε
  have hsE := schE_le_gEdges I ε e
  have hed : (edUp I ε j).length + (schE I ε e).length ≤ (gEdges I ε).length := by
    have h := edUp_le I ε (j + 1)
    rwa [edUp_succ I ε hj, List.length_append] at h
  obtain ⟨hsec, hsum, hcolW, hsumB, htrkB, hcofB⟩ := sec_bounds I e
  have hsz := schSize_eq I e
  have hsB : sBase I j + schSize I e ≤ locBase I := by
    have h := sBase_le I (j + 1)
    rwa [sBase_succ I hj] at h
  have hsBe : schBase I e = sBase I j := rfl
  have hhub : sumBase I e = schBase I e + hubSize I e := rfl
  have hE2 := schE_eq2 I ε e
  have hE2l := congrArg List.length hE2
  rw [List.length_append] at hE2l
  have hTn : tnN (Matrix.isTern (sch I e)) ≤ 1 := by unfold tnN; split_ifs <;> omega
  have hk1 : k ≤ H I := by nlinarith
  have hl1 : ℓ + 1 ≤ H I := by nlinarith
  have hBR := blkRows_le (cL I e)
  have hp : s.pos ≤ (encodeSystem I).length := by rw [hpos]; exact schAt_le I j
  -- fixed registers of `s`
  have fL : s.env rL = ℓ := by rw [hfr _ (by decide), f0L]
  have fk : s.env rKk = k := by rw [hfr _ (by decide), f0k]
  have fLB : s.env rLB = locBase I := by rw [hfr _ (by decide), f0LB]
  have fEps : s.env r4Eps = ε.val := by rw [hfr _ (by decide), f0Eps]
  have fPL : s.env r4PL = k * (ℓ + 1) := by rw [hfr _ (by decide), f0PL]
  /- 1. the header -/
  obtain ⟨s1, g1, h1p, h1x, h1s, h1o, h1T, h1D, h1f⟩ := p4Rd_good I hw hH s hj hpos
  have hb1 := g1.bdd hw hbd hp
  /- 2. the record -/
  have h1S2 : s1.stk qS2 = orsL (cL I e) ++ blkRows (cL I e) :: nEnt I e ::
      (coefSteps I e).length :: schRecsFrom I (j + 1) := by
    rw [h1s, hS2, schRecsFrom_cons I hj, schRec]; simp <;> rfl
  obtain ⟨s2, g2, h2s, h2BR, h2NE, h2NC, h2R2, h2p, h2o, h2f⟩ := p4Rec_good
    (x := encodeSystem I) hw s1 (orsL (cL I e)) (schRecsFrom I (j + 1)) _ _ _ h1S2
    (by rw [h1f _ (by decide), fL, length_orsL]) (orsL_le _) (by rw [h1s, hOF])
    (by rw [h1s, hOB]) hb1.1 hb1.2 (by rw [length_orsL]; omega)
  have hb2 := (g1.seq g2).bdd hw hbd hp
  have e2 : ∀ r, r ∉ [rc1, rc2, rP, rT, r4Tn, r4D] → r ∉ [rT, rP, rc1, r4R2, r4BR, r4NE, r4NC] →
      s2.env r = s.env r := fun r h1 h2 => by rw [h2f r h2, h1f r h1]
  have e2s : ∀ q, q ≠ qS2 → q ≠ qOrsF → s2.stk q = s.stk q := fun q h1 h2 => by
    rw [h2s, Function.update_of_ne h2, Function.update_of_ne h1, h1s]
  /- 3. the section bases -/
  have e2SB : s2.env r4SB = sBase I j := by rw [e2 _ (by decide) (by decide), eSB]
  have e2D : s2.env r4D = (cL I e).length := by rw [h2f _ (by decide), h1D]
  have e2T : s2.env r4Tn = tnN (Matrix.isTern (sch I e)) := by rw [h2f _ (by decide), h1T]
  obtain ⟨s3, g3, h3H, h3K, h3Di, h3Su, h3Tr, h3SP, h3TP, h3s, h3p, h3o, h3f⟩ :=
    p4Bas_good (x := encodeSystem I) hw s2 e2SB e2D h2NE e2T hTn (by
      rw [← hsBe]; rw [hcolW] at hsec; nlinarith)
  have hb3 := (g1.seq (g2.seq g3)).bdd hw hbd hp
  set T := tnN (Matrix.isTern (sch I e)) with hT
  have hSu : sBase I j + (cL I e).length * (2 + 4 * T) + 4 * nEnt I e = sumBase I e := by
    rw [hsumB, hcolW, hsBe]
  have hTr : sBase I j + (cL I e).length * (2 + 4 * T) + 4 * nEnt I e + 2 * T * (cL I e).length =
      trackBase I e := by rw [hSu, htrkB, hsum]
  rw [hSu] at h3Su h3SP
  rw [hTr] at h3Tr h3TP
  have e3 : ∀ r, r ∉ bodyW → s3.env r = s.env r := fun r hr => by
    rw [h3f r (notMem_of_bodyW_bas r hr), e2 r (notMem_of_bodyW_rd r hr) (notMem_of_bodyW_rec r hr)]
  /- 4. section 1 -/
  set A1 := (cL I e).zipIdx.flatMap (a1C I e)
  set A2 := (cL I e).zipIdx.flatMap (a2C I e)
  set E1 := (cL I e).zipIdx.flatMap fun q => colE1 I ε e q.1 q.2
  set E2 := (cL I e).flatMap (colE2 I ε e)
  set codes := (cL I e).flatMap fun c => codesL I e c ++ [0]
  have hAe : (ansE I e).flatten = A1 ++ A2 := ansE_flatten I e
  have h3A : s3.stk qAns = A1 ++ (A2 ++ ansFr I (j + 1)) := by
    rw [h3s, e2s _ (by decide) (by decide), hAns, ansFr_cons I hj]
    show (ansE I e).flatten ++ _ = _
    rw [hAe, List.append_assoc]
  have hF1 : L1Fix I w (encodeSystem I) ε e
      (encodeNats (permsL I e) ++ encodeNats (schsSuf I (j + 1))) s3 := by
    refine ⟨by rw [h3p, h2p]; exact h1x, by rw [e3 _ (by decide), fL],
      by rw [e3 _ (by decide), fk], by rw [h3f _ (by decide), h2BR],
      by rw [h3f _ (by decide), e2T], by rw [e3 _ (by decide), fLB],
      by rw [e3 _ (by decide), fEps], by rw [h3f _ (by decide), e2D], ?_, ?_, hb3.2⟩
    · rw [h3s, h2s, Function.update_self]
    · rw [h3s, e2s _ (by decide) (by decide), hOB]
  have e3M : s3.env r4M = (edUp I ε j).length := by
    rw [h3f _ (by decide), e2 _ (by decide) (by decide), eM]
  have hB1 : L1Bnd I w e s3 := ⟨hW16, hkl, hcl, hab, by rw [e3M]; omega⟩
  obtain ⟨s4, g4, h4EM, h4Rk, h4A, h4A2, h4so, h4K, h4Di, h4H, h4SP, h4TP, h4V, hb4', h4p, h4o,
      h4f⟩ := p4S1_good I hw hk hE ε e (A2 ++ ansFr I (j + 1)) _ s3 hF1 hB1 (by
      rw [show ((cL I e).zipIdx.flatMap fun q => colE1 I ε e q.1 q.2) = E1 from rfl]; omega) h3K h3Di
    (by rw [h3H, hsBe]) h3SP h3TP (hb3.1.1 _) hb3.1 h3A
  have hb4 := (g1.seq (g2.seq (g3.seq g4))).bdd hw hbd hp
  have e4 : ∀ r, r ∉ bodyW → s4.env r = s.env r := fun r hr => by
    rw [h4f r (notMem_of_bodyW_c1 r hr), e3 r hr]
  have h3Rk : s3.stk qRk = [] := by rw [h3s, e2s _ (by decide) (by decide), hRk]
  have h4Rk' : s4.stk qRk = codes.reverse := by rw [h4Rk, h3Rk, List.append_nil]
  /- 5. between the sections -/
  have hx4 : (encodeSystem I).drop s4.pos =
      encodeNats (permsL I e) ++ encodeNats (schsSuf I (j + 1)) := by
    rw [h4p, drop_add, hF1.1, List.drop_left]
  obtain ⟨s5, g5, h5s, h5p, h5o, h5P, h5SP, h5TP, h5K, h5f⟩ := p4Mid_good (x := encodeSystem I)
    hw s4 (s4.stk qRk) (orsL (cL I e)) (permsL I e) (encodeNats (schsSuf I (j + 1))) rfl
    (by rw [h4so _ (by decide) (by decide) (by decide) (by decide), h3s, h2s,
      Function.update_self])
    (by rw [e4 _ (by decide), fL, length_orsL])
    (by rw [h4f _ (by decide), h3f _ (by decide), h2BR])
    (by rw [h4f _ (by decide), h3f _ (by decide), h2NE])
    (by rw [h4f _ (by decide), h3f _ (by decide), h2NC])
    (by rw [h4f _ (by decide), h3f _ (by decide), e2T]) hTn
    (by rw [e4 _ (by decide), fPL]) h4TP
    (by rw [h4f _ (by decide), h3Su]) (by rw [h4f _ (by decide), h3Tr]) hx4
    (by rw [length_permsL, arity_eq]) hb4.1 hb4.2 (by rw [length_orsL]; omega)
  have hb5 := (g1.seq (g2.seq (g3.seq (g4.seq g5)))).bdd hw hbd hp
  have e5 : ∀ r, r ∉ bodyW → s5.env r = s.env r := fun r hr => by
    rw [h5f r (notMem_of_bodyW_mid r hr), e4 r hr]
  have e5s : ∀ q, q ≠ qRk → q ≠ qRkF → q ≠ qOrsF → q ≠ qSch → s5.stk q = s4.stk q :=
    fun q h1 h2 h3 h4 => by
      rw [h5s, Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne h2,
        Function.update_of_ne h1]
  /- 6. section 2 -/
  have hF2 : L2Fix I (encodeSystem I) ε e s5 := by
    refine ⟨by rw [e5 _ (by decide), fk],
      by rw [h5f _ (by decide), h4f _ (by decide), h3f _ (by decide), e2T],
      by rw [e5 _ (by decide), fLB], by rw [e5 _ (by decide), fEps],
      by rw [h5f _ (by decide), h4f _ (by decide), h3f _ (by decide), e2D],
      by rw [h5f _ (by decide), h4f _ (by decide), h3f _ (by decide), h2R2, rowsR_len],
      by rw [h5P, hcofB], hb5.2⟩
  have e5M : s5.env r4M = (edUp I ε j).length + E1.length := by
    rw [h5f _ (by decide), h4EM.2, e3M]
  have hnE6 : 6 * nEnt I e ≤ locBase I := by omega
  have hE12 : E1.length + E2.length = (schE I ε e).length := by rw [hE2l]
  have hB2 : L2Bnd I w ε e s5 := ⟨hW16, hkl, hcl, hab, by
    rw [e5M]
    have : (edUp I ε j).length + E1.length + E2.length ≤ 3 * (ordL I).length := by omega
    have h2e : ((cL I e).flatMap (colE2 I ε e)).length = E2.length := rfl
    omega⟩
  have h5R : s5.stk qRkF = codes ++ [] := by
    rw [h5s, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self, h4Rk', h4so _ (by decide) (by decide) (by decide) (by decide), h3s,
      e2s _ (by decide) (by decide), hRkF, List.reverse_reverse]
  have h5B : s5.stk qOrsB = [] := by
    rw [e5s _ (by decide) (by decide) (by decide) (by decide),
      h4so _ (by decide) (by decide) (by decide) (by decide), h3s,
      e2s _ (by decide) (by decide), hOB]
  have h5A : s5.stk qAns = A2 ++ ansFr I (j + 1) := by
    rw [e5s _ (by decide) (by decide) (by decide) (by decide), h4A]
  obtain ⟨s6, g6, h6EE, h6R, h6B, h6A, h6A2, h6so, h6K, h6H, h6TP, h6SP, hb6', h6f⟩ :=
    p4S2_good I hw hk ε e (ansFr I (j + 1)) [] s5 hF2 hB2 h5R h5B h5A h5K
    (by rw [h5f _ (by decide), h4H]; rfl) h5TP h5SP hb5.1
  have hb6 := (g1.seq (g2.seq (g3.seq (g4.seq (g5.seq g6))))).bdd hw hbd hp
  /- 7. the end -/
  have h6J : s6.env rJ = j := by
    rw [h6f _ (by decide), h5f _ (by decide), h4f _ (by decide), h3f _ (by decide),
      e2 _ (by decide) (by decide), eJ]
  have hcoef : coefBase I e + 2 * (coefSteps I e).length = sBase I j + schSize I e := by
    rw [hcofB, htrkB, hhub, hsz, hsBe]; ring
  obtain ⟨s7, g7, h7SB, h7J, h7s, h7p, h7o, h7f⟩ := p4End_good (x := encodeSystem I) (w := w) s6
    (P := coefBase I e) (nC := (coefSteps I e).length) (j := j)
    (by rw [h6f _ (by decide), h5P, hcofB])
    (by rw [h6f _ (by decide), h5f _ (by decide), h4f _ (by decide), h3f _ (by decide), h2NC])
    h6J (by rw [hcoef]; omega) (by have := E_le I; omega)
  have hb7 := (g1.seq (g2.seq (g3.seq (g4.seq (g5.seq (g6.seq g7)))))).bdd hw hbd hp
  have e6s : ∀ q, q ≠ q4E → q ≠ qRkF → q ≠ qOrsB → q ≠ qAns → q ≠ qA2 → s7.stk q = s5.stk q :=
    fun q h1 h2 h3 h4 h5 => by rw [h7s, h6so q h1 h2 h3 h4 h5]
  have hsch : s.stk qSch = s4.stk qSch := by
    rw [h4so _ (by decide) (by decide) (by decide) (by decide), h3s,
      e2s _ (by decide) (by decide)]
  refine ⟨s7, (g1.seq (g2.seq (g3.seq (g4.seq (g5.seq (g6.seq g7)))))).mono ?_,
    by omega, h7J, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hb7.1, ?_⟩
  · -- the cost
    have hcc : condCost w (Ex.lt (rv r4K) (rv r4D) : Ex CR) = 3 * Ex.nodeCost w + 1 := by
      simp only [condCost, Ex.size]
    rw [hcc, h4Rk', List.length_reverse, length_orsL, schD_len]
    have hrk : codes.length ≤ nEnt I e := codes_len_le I hk e
    have hsz2 := schSize_ge I e
    have hpe := permsL_ge I hk e
    have key := body_arith (N := Ex.nodeCost w) (U := unitCost w) (hdr := hdrL I e)
      (co := (encodeNats ((cL I e).flatMap cdesc)).length)
      (pe := (encodeNats (permsL I e)).length) (nE := nEnt I e) (cl := (cL I e).length)
      (ℓ := ℓ) (sz := schSize I e) (rk := codes.length) hU hU' hpe hrk hsz2
    simp only [← he]
    linarith only [key]
  · rw [h7p, h6EE.2.2.1, h5p, h4p, h3p, h2p, h1p, hpos, schAt_succ I hj, schD_len]; ring
  · rw [h7SB, hcoef, sBase_succ I hj]
  · rw [e6s _ (by decide) (by decide) (by decide) (by decide) (by decide),
      e5s _ (by decide) (by decide) (by decide) (by decide),
      h4so _ (by decide) (by decide) (by decide) (by decide), h3s, h2s,
      Function.update_of_ne (by decide), Function.update_self]
  · rw [e6s _ (by decide) (by decide) (by decide) (by decide) (by decide), h5s,
      Function.update_self, ← hsch, hSch, schRecsUpTo_succ I hj, List.reverse_append, schRec]
    simp; exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [h7s, h6A]
  · rw [h7s, h6A2, e5s _ (by decide) (by decide) (by decide) (by decide), h4A2, h3s,
      e2s _ (by decide) (by decide), hA2, ansUp_succ I hj]
    show _ = (ansUp I j ++ (ansE I e).flatten).reverse
    rw [hAe]; simp <;> rfl
  · rw [h7s, h6EE.1, e5s _ (by decide) (by decide) (by decide) (by decide), h4EM.1, h3s,
      e2s _ (by decide) (by decide), h4E, edUp_succ I ε hj]
    show _ = pairsRev (edUp I ε j ++ schE I ε e) ++ _
    rw [hE2, pairsRev_append, pairsRev_append]; simp <;> rfl
  · rw [e6s _ (by decide) (by decide) (by decide) (by decide) (by decide), h5s,
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_self]
  · rw [h7s, h6R]
  · rw [e6s _ (by decide) (by decide) (by decide) (by decide) (by decide), h5s,
      Function.update_of_ne (by decide), Function.update_self]
  · rw [h7s, h6B]
  · intro q hq
    simp only [bodyQ, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ := hq
    rw [e6s q q5 q7 q9 q3 q4, e5s q q6 q7 q8 q2, h4so q q5 q6 q3 q4, h3s, e2s q q1 q8, hoth q
      (by simp [bodyQ, q1, q2, q3, q4, q5, q6, q7, q8, q9])]
  · rw [h7f _ (by decide) (by decide), h6EE.2.1, e5M, edUp_succ I ε hj, List.length_append,
      hE2l]
    ring
  · rw [h7o, h6EE.2.2.2, h5o, h4o, h3o, h2o, h1o, hout]
  · intro r hr
    obtain ⟨n1, n2⟩ := notMem_of_bodyW_end r hr
    rw [h7f r n1 n2, h6f r (notMem_of_bodyW_c2 r hr), e5 r hr, hfr r hr]

end Lax119563Proofs.Compiler

end Compiler_P4SchB5

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchSpec` -/

section Compiler_P4SchSpec

/-!
# Pass `P4`, schema part: the program `p4Sch` and its specification

`p4Sch = p4SchPre; p4SLp; moveAllS qA2 qAns`: the prefix rewinds the input, skips `k, ℓ, W`,
the location section and `E`, computes `r4PL = k (ℓ + 1)`, sets `rJ, r4SB := 0` and moves the
records forward onto `qS2`; the loop runs the schema body for `rJ < rE`; the suffix restores
`qAns` (**`p4Sch_spec`**: `SchSpec I (wordOf H S) p4Sch (400000 (H + S + 1) · nodeCost w)`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The prefix of the schema part. -/
def p4SchPre : CStm CR CQ :=
  .seq .rst (.seq (skipNumS rT) (.seq (skipNumS rT) (.seq (skipNumS rT)
    (.seq (.set rJ (.const 0)) (.seq p4KLoop (.seq (skipNumS rT)
      (.seq (mulS r4PL rKk rL1 rc1) (.seq (.set rJ (.const 0)) (.seq (.set r4SB (.const 0))
        (moveAllS qSch qS2 rT rP))))))))))

/-- The schema loop. -/
def p4SLp : CStm CR CQ := .loop (.lt (rv rJ) (rv rE)) p4Body

/-- **The schema edge part of `P4`.** -/
def p4Sch : CStm CR CQ := .seq p4SchPre (.seq p4SLp (moveAllS qA2 qAns rT rP))

/-- Registers written by the prefix. -/
def preW : List (Fin CR) := [rT, rP, r4D, rc2, rc3, rJ, rc1, r4PL, r4SB]

/-! ## The prefix -/

lemma schPre_arith {N U p h a b c d m z : ℕ} (hU : U ≤ N) (hp : p ≤ h) (habcd : a + b + c + d ≤ h)
    (hm : m ≤ h) (hz : z ≤ 4 * h) :
    U * (p + 1) + ((a + 1) * (4 * N) + ((b + 1) * (4 * N) + ((c + 1) * (4 * N) + (N + U +
      (400 * (h + 1) * N + ((d + 1) * (4 * N) + ((m + 1) * (12 * N) + (N + U + (N + U +
        (z + 1) * (10 * N)))))))))) ≤ 1000 * (h + 1) * N := by
  have h1 : (a + b + c + d) * N ≤ h * N := Nat.mul_le_mul_right _ habcd
  have h2 : m * N ≤ h * N := Nat.mul_le_mul_right _ hm
  have h3 : z * N ≤ 4 * h * N := Nat.mul_le_mul_right _ hz
  have h4 : U * (p + 1) ≤ N * (h + 1) := Nat.mul_le_mul hU (by omega)
  nlinarith

set_option maxHeartbeats 4000000 in
lemma p4SchPre_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hk : 1 ≤ k)
    (hE : I.schemas ≠ [])
    (st : NSt CR CQ) (hb : st.Bdd w) (hp : st.pos ≤ H I) (hW : st.env rW = I.numLocations)
    (hL1 : st.env rL1 = ℓ + 1) (hK : st.env rKk = k) (hz : (st.stk qSch).length ≤ 4 * H I) :
    ∃ s0, Good (encodeSystem I) w p4SchPre st s0 (1000 * (H I + 1) * Ex.nodeCost w) ∧
      s0.pos = schPos I ∧ s0.out = st.out ∧
      s0.stk = Function.update (Function.update st.stk qSch []) qS2
        ((st.stk qSch).reverse ++ st.stk qS2) ∧
      s0.env rJ = 0 ∧ s0.env r4SB = 0 ∧ s0.env r4PL = k * (ℓ + 1) ∧
      ∀ r, r ∉ preW → s0.env r = st.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hkl := kl_le_H I hE
  have hl1 : 1 * (ℓ + 1) ≤ k * (ℓ + 1) := Nat.mul_le_mul_right _ hk
  have hℓ : ℓ ≤ H I := by omega
  have r0 := Good.rst (x := encodeSystem I) (w := w) (st := st)
  set s0 : NSt CR CQ := { st with pos := 0 }
  have r1 := skipNumS_good (Q := CQ) hw (t := rT) s0 k _ (drop_zero_k I)
  set s1 := skipNumFinal s0 rT k
  have r2 := skipNumS_good (Q := CQ) hw (t := rT) s1 ℓ _
    (by show (encodeSystem I).drop (0 + _) = _; rw [zero_add]; exact drop_ell I)
  set s2 := skipNumFinal s1 rT ℓ
  have r3 := skipNumS_good (Q := CQ) hw (t := rT) s2 I.numLocations _
    (by show (encodeSystem I).drop (0 + (encodeNat k).length + (encodeNat ℓ).length) = _
        rw [zero_add]; exact drop_W I)
  set s3 := skipNumFinal s2 rT I.numLocations
  have e3 : ∀ r, r ≠ rT → s3.env r = st.env r := fun r h => by
    rw [skipNumFinal_env_ne h, skipNumFinal_env_ne h, skipNumFinal_env_ne h]
  have r4 := Good.set (x := encodeSystem I) (w := w) (st := s3) (r := rJ) (e := .const 0)
    (by simp only [Ex.Fits]; positivity)
  set s4 := s3.set rJ ((Ex.const 0 : Ex CR).eval s3.env)
  have e4 : ∀ r, r ≠ rT → r ≠ rJ → s4.env r = st.env r := fun r h1 h2 => by
    simp only [s4, NSt.set_env, Function.update_of_ne h2]; exact e3 r h1
  have h4p : s4.pos = posAt I 0 := by
    show 0 + (encodeNat k).length + (encodeNat ℓ).length + (encodeNat I.numLocations).length = _
    rw [posAt_zero]; ring
  have hI4 : p4KInv I s4 s4 := by
    refine ⟨by rw [e4 _ (by decide) (by decide), hW], by rw [e4 _ (by decide) (by decide), hL1],
      by simp [s4, Ex.eval], by rw [show s4.env rJ = 0 by simp [s4, Ex.eval]]; exact h4p,
      rfl, rfl, fun _ _ => rfl⟩
  obtain ⟨s5, r5, h5p, h5s, h5o, h5f⟩ := p4KLoop_good I hw hH hℓ s4 hI4
    (by simp [s4, Ex.eval])
  have r6 := skipNumS_good (Q := CQ) hw (t := rT) s5 I.schemas.length _
    (by rw [h5p]; exact drop_posAt_W I)
  set s6 := skipNumFinal s5 rT I.schemas.length
  have e6 : ∀ r, r ∉ preW → s6.env r = st.env r := fun r hr => by
    simp only [preW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [skipNumFinal_env_ne hr.1, h5f r (by simp [kW, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2.1]), e4 r hr.1 hr.2.2.2.2.2.1]
  have r7 := mulS_good (x := encodeSystem I) (w := w) hw (dst := r4PL) (a := rKk) (b := rL1)
    (j := rc1) (by decide) (by decide) (by decide) (by decide) (by decide) s6
    (by rw [e6 _ (by decide), hK]) (by rw [e6 _ (by decide), hL1]) (by omega) (by omega)
  set s7 := (s6.set r4PL (k * (ℓ + 1))).set rc1 (ℓ + 1)
  have r8 := Good.set (x := encodeSystem I) (w := w) (st := s7) (r := rJ) (e := .const 0)
    (by simp only [Ex.Fits]; positivity)
  set s8 := s7.set rJ ((Ex.const 0 : Ex CR).eval s7.env)
  have r9 := Good.set (x := encodeSystem I) (w := w) (st := s8) (r := r4SB) (e := .const 0)
    (by simp only [Ex.Fits]; positivity)
  set s9 := s8.set r4SB ((Ex.const 0 : Ex CR).eval s8.env)
  have r19 := r0.seq (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq r9))))))))
  have hb9 := r19.bdd hw hb (hp.trans le_rfl)
  obtain ⟨s10, r10, h10s, h10p, h10o, h10f⟩ := moveAllS_good (x := encodeSystem I) hw
    (q := qSch) (q' := qS2) (t := rT) (f := rP) (by decide) (by decide) s9 hb9.1
  have h9s : s9.stk = st.stk := by
    show s5.stk = _; rw [h5s]; rfl
  have hlen3 : (encodeNat k).length + (encodeNat ℓ).length + (encodeNat I.numLocations).length +
      (encodeNat I.schemas.length).length ≤ H I := by
    have h1 := schAt_le I 0
    rw [schAt_zero, schPos] at h1
    have h3 : posAt I 0 ≤ posAt I I.numLocations := by
      have : ∀ j ≤ I.numLocations, posAt I 0 ≤ posAt I j := by
        intro j
        induction j with
        | zero => intro _; exact le_rfl
        | succ j ih => intro hj; rw [posAt_succ I (by omega)]; have := ih (by omega); omega
      exact this _ le_rfl
    rw [posAt_zero] at h3
    omega
  refine ⟨s10, (r0.seq (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq
    (r9.seq r10)))))))))).mono ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h9s]
    simp only [Ex.size, one_mul]
    have := schPre_arith (N := Ex.nodeCost w) (U := unitCost w) (p := st.pos) (h := H I)
      (a := (encodeNat k).length) (b := (encodeNat ℓ).length)
      (c := (encodeNat I.numLocations).length) (d := (encodeNat I.schemas.length).length)
      (m := ℓ + 1) (z := (st.stk qSch).length) hU hp hlen3 (by omega) hz
    linarith only [this]
  · rw [h10p]; show s5.pos + _ = _; rw [h5p]; rfl
  · rw [h10o]; show s5.out = _; rw [h5o]; rfl
  · rw [h10s, h9s]
  · rw [h10f _ (by decide) (by decide)]
    simp [s9, s8, Ex.eval, Function.update_of_ne (show rJ ≠ r4SB by decide)]
  · rw [h10f _ (by decide) (by decide)]; simp [s9, Ex.eval]
  · rw [h10f _ (by decide) (by decide)]
    simp [s9, s8, s7, Function.update_of_ne (show r4PL ≠ r4SB by decide),
      Function.update_of_ne (show r4PL ≠ rJ by decide),
      Function.update_of_ne (show r4PL ≠ rc1 by decide)]
  · intro r hr
    have h1 : r ≠ rT := fun h => hr (by simp [h, preW])
    have h2 : r ≠ rP := fun h => hr (by simp [h, preW])
    rw [h10f r h1 h2]
    simp only [s9, s8, s7, NSt.set_env]
    rw [Function.update_of_ne (fun h => hr (by simp [h, preW])),
      Function.update_of_ne (fun h => hr (by simp [h, preW])),
      Function.update_of_ne (fun h => hr (by simp [h, preW])),
      Function.update_of_ne (fun h => hr (by simp [h, preW])), e6 r hr]

end Lax119563Proofs.Compiler

end Compiler_P4SchSpec

/-! ### Formerly `Lax119563Proofs.Compiler.PReqLoop` -/

section Compiler_PReqLoop

/-!
# Pass `P3`, request generation: the loop over the schemas

`p3Loop` runs `p3Sch` for `rJ = j, …, E - 1`; started at `schAt I 0` with `rJ = 0`,
`rSB = 0` and empty generation stacks, it pushes `(reqs I).flatten.reverse` onto `qRec`
and ends at the end of the input with `rSB = ansBase I E = |reqs I|` (**`p3Loop_good`**).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- **The schema loop of the request generation.** -/
def p3Loop : CStm CR CQ := .loop (.lt (rv rJ) (rv rE)) p3Sch

/-- The generation stacks. -/
def GenEmpty (s : NSt CR CQ) : Prop :=
  s.stk qLs = [] ∧ s.stk qLs2 = [] ∧ s.stk qF = [] ∧ s.stk qF2 = [] ∧ s.stk qDl = [] ∧
    s.stk qDl2 = [] ∧ s.stk qDom = [] ∧ s.stk qDom2 = [] ∧ s.stk qAux = []

/-- The stacks other than the generation stacks, `qRec` and `qJunk`. -/
def OtherStk (st s : NSt CR CQ) : Prop :=
  ∀ q, q ≠ qLs → q ≠ qLs2 → q ≠ qF → q ≠ qF2 → q ≠ qDl → q ≠ qDl2 → q ≠ qDom →
    q ≠ qDom2 → q ≠ qAux → q ≠ qRec → q ≠ qJunk → s.stk q = st.stk q

/-- The invariant of the schema loop. -/
def p3Inv (w : ℕ) (st s : NSt CR CQ) : Prop :=
  s.env rJ ≤ I.schemas.length ∧ s.env rE = I.schemas.length ∧ s.env rKk = k ∧
    s.env rKL = k * ℓ ∧ s.env rL = ℓ ∧ s.env rL1 = ℓ + 1 ∧ s.env rSB = ansBase I (s.env rJ) ∧
    s.pos = schAt I (s.env rJ) ∧ GenEmpty s ∧
    s.stk qRec = (reqsUpTo I (s.env rJ)).flatten.reverse ++ st.stk qRec ∧ OtherStk st s ∧
    s.out = st.out ∧ s.Bdd w

set_option maxHeartbeats 4000000 in
/-- One schema of the loop. -/
lemma p3Loop_step {w : ℕ} (hw : 2 ≤ w) (hk : 1 ≤ k) (hE : I.schemas ≠ [])
    (hS : 16 * (H I + 1) ≤ 2 ^ w) (st s : NSt CR CQ) (hI : p3Inv I w st s)
    (hc : (Ex.lt (rv rJ) (rv rE)).eval s.env ≠ 0) :
    ∃ s', Good (encodeSystem I) w p3Sch s s'
        (10000 * Ex.nodeCost w * ((H I - s.pos) - (H I - s'.pos)) + 10000 * Ex.nodeCost w) ∧
      p3Inv I w st s' ∧ I.schemas.length - s'.env rJ < I.schemas.length - s.env rJ ∧
      H I - s'.pos ≤ H I - s.pos := by
  obtain ⟨hJ, hEr, hKk, hKL, hL, hL1, hSB, hpos, ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩, hRec,
    hOth, hout, hb⟩ := hI
  have hlt : s.env rJ < I.schemas.length := by
    by_contra h; apply hc; simp only [Ex.eval, rv, hEr]; rw [if_neg h]
  obtain ⟨j, hjdef⟩ : ∃ j, s.env rJ = j := ⟨_, rfl⟩
  rw [hjdef] at hlt hSB hpos hRec
  set e : Fin I.schemas.length := ⟨j, hlt⟩
  have hkH := k_le_H I hE
  have hℓ := ell_le_H I hk (fun h => hE h.2)
  have hEH := E_le I
  have hPLH := kl_le_H I hE
  have h3H := three_le_H I
  have hx : (encodeSystem I).drop s.pos =
      encodeNats (schemaDescription (sch I e)) ++ encodeNats (schsSuf I (j + 1)) := by
    rw [hpos, drop_schAt, schsSuf_cons I hlt, encodeNats_append]; rfl
  have hsch : schAt I (j + 1) = schAt I j + (encodeNats (schD I e)).length := schAt_succ I hlt
  have hschle := schAt_le I (j + 1)
  have hd1 := dom_mul_le I e
  have hdl : (coordList (dom I e)).length ≤ (coordList (dom I e)).length * (ℓ + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hab := ansBase_mul_le I j
  have hab' : ansBase I j ≤ ansBase I j * (ℓ + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hpre : (encodeNats (schsPre I j)).length + (encodeNats (schD I e)).length ≤ H I := by
    have := schsPre_enc_le I (j + 1)
    rw [schsPre_succ I hlt, encodeNats_append, List.length_append] at this
    exact this
  have hpx : s.pos ≤ (encodeSystem I).length := by rw [hpos]; exact schAt_le I j
  obtain ⟨s', r, h1, h2, h3, h4, h5, h6, h7, h8, h9, hRec', hOth', hSB', hJ', hp', ho', he'⟩ :=
    p3Sch_good (x := encodeSystem I) hw s hb hpx (sch I e) (ansBase I j) j (3 * (H I + 1))
      _ hk hx (by omega) (fun v hv => (schD_vals_le I hkH e v hv).trans (by omega))
      (by have := schD_le_H I e; exact hd1.trans (this.trans (by omega)))
      (by nlinarith)
      (by
        show ansBase I j + 3 * (coordList (dom I e)).length + 3 ≤ _
        have : (encodeNats (schD I e)).length ≤ H I := schD_le_H I e
        omega)
      (by omega) (by omega) hKk hKL hL hL1 hSB hjdef g1 g2 g3 g4 g5 g6 g7 g8 g9
  have hlen : s'.pos = schAt I (j + 1) := by rw [hp', hsch, hpos]; rfl
  refine ⟨s', r.mono ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩,
    ?_, ?_, ?_, (r.bdd hw hb hpx).1⟩, ?_, ?_⟩
  · rw [hlen, hsch, hpos]
    have : H I - schAt I j - (H I - (schAt I j + (encodeNats (schD I e)).length)) =
        (encodeNats (schD I e)).length := by omega
    rw [this]; show _ ≤ _ + _
    rw [schD]; nlinarith
  · rw [hJ']; omega
  · rw [he' _ (by decide), hEr]
  · rw [he' _ (by decide), hKk]
  · rw [he' _ (by decide), hKL]
  · rw [he' _ (by decide), hL]
  · rw [he' _ (by decide), hL1]
  · rw [hSB', hJ', ansBase_succ I hlt]; rfl
  · rw [hJ', hlen]
  · rw [hRec', hRec, hJ', reqsUpTo_succ I hlt, argsReqs_eq_reqsE]
    simp; rfl
  · intro q n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11
    rw [hOth' q n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11, hOth q n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11]
  · rw [ho', hout]
  · rw [hJ']; omega
  · rw [hlen, hpos]; omega

lemma p3Loop_arith (N U h E φ : ℕ) (hU : 1 ≤ N) (hφ : φ ≤ h) (hE : E ≤ h) :
    10000 * N * φ + E * (10000 * N + ((1 + 1 + 1) * N + 1)) + ((1 + 1 + 1) * N + 1) ≤
      30000 * (h + 1) * N + U := by
  have e1 : 10000 * N * φ ≤ 10000 * N * h := Nat.mul_le_mul_left _ hφ
  have e2 : E * (10000 * N + ((1 + 1 + 1) * N + 1)) ≤ h * (10000 * N + ((1 + 1 + 1) * N + 1)) :=
    Nat.mul_le_mul_right _ hE
  have e3 : h ≤ h * N := Nat.le_mul_of_pos_right _ hU
  have e4 : 10000 * N * h + h * (10000 * N + ((1 + 1 + 1) * N + 1)) = 20003 * (h * N) + h := by
    ring
  have e5 : 30000 * (h + 1) * N = 30000 * (h * N) + 30000 * N := by ring
  omega

set_option maxHeartbeats 2000000 in
/-- **The schema loop.** -/
theorem p3Loop_good {w : ℕ} (hw : 2 ≤ w) (hk : 1 ≤ k) (hE : I.schemas ≠ [])
    (hS : 16 * (H I + 1) ≤ 2 ^ w) (st : NSt CR CQ) (hb : st.Bdd w) (hJ : st.env rJ = 0)
    (hEr : st.env rE = I.schemas.length) (hKk : st.env rKk = k) (hKL : st.env rKL = k * ℓ)
    (hL : st.env rL = ℓ) (hL1 : st.env rL1 = ℓ + 1) (hSB : st.env rSB = 0)
    (hpos : st.pos = schPos I) (hG : GenEmpty st) :
    ∃ st', Good (encodeSystem I) w p3Loop st st' (30000 * (H I + 1) * Ex.nodeCost w) ∧
      GenEmpty st' ∧ st'.stk qRec = (reqs I).flatten.reverse ++ st.stk qRec ∧ OtherStk st st' ∧
      st'.env rSB = (reqs I).length ∧ st'.pos = H I ∧ st'.out = st.out ∧ st'.Bdd w ∧
      ∀ r, wReg r p3Sch = false → st'.env r = st.env r := by
  have hU := CStm.nodeCost_ge w
  have hI0 : p3Inv I w st st := by
    refine ⟨by rw [hJ]; omega, hEr, hKk, hKL, hL, hL1, by rw [hSB, hJ]; simp [ansBase],
      by rw [hpos, hJ, schAt_zero], hG, by rw [hJ]; simp [reqsUpTo], fun _ _ _ _ _ _ _ _ _ _ _ _ =>
      rfl, rfl, hb⟩
  obtain ⟨s', r, hI', hc'⟩ := Good.loop_var (x := encodeSystem I) (w := w)
    (e := .lt (rv rJ) (rv rE)) (body := p3Sch) (p3Inv I w st)
    (fun s => I.schemas.length - s.env rJ) (fun s => H I - s.pos) (10000 * Ex.nodeCost w)
    (10000 * Ex.nodeCost w) (fun s hI => ⟨by
      obtain ⟨hj, hE', -⟩ := hI
      simp only [Ex.Fits, rv, hE']
      have := E_le I
      have h2 : 2 * (H I + 1) ≤ 2 ^ w := by omega
      omega,
      fun hc => p3Loop_step I hw hk hE hS st s hI hc⟩) st hI0
  obtain ⟨hJ7, hE7, -, -, -, -, hSB7, hp7, hG7, hRec7, hOth7, ho7, hb7⟩ := hI'
  have hj : s'.env rJ = I.schemas.length := by
    simp only [Ex.eval, rv, hE7] at hc'; split_ifs at hc' with h <;> omega
  refine ⟨s', r.mono ?_, hG7, by rw [hRec7, hj, reqsUpTo_all], hOth7,
    by rw [hSB7, hj, ← length_reqsUpTo, reqsUpTo_all], by rw [hp7, hj, schAt_all], ho7, hb7,
    fun q hq => r.env_of (by simpa [wReg] using hq)⟩
  have hU0 := Ex.unitCost_le_nodeCost w
  have hU' := CStm.unitCost_ge w
  simp only [condCost, Ex.size, rv]
  have := p3Loop_arith (Ex.nodeCost w) 0 (H I) (I.schemas.length - st.env rJ) (H I - st.pos)
    (by omega) (by omega) (by have := E_le I; omega)
  omega

end Lax119563Proofs.Compiler

end Compiler_PReqLoop

/-! ### Formerly `Lax119563Proofs.Compiler.P3Gen` -/

section Compiler_P3Gen

/-!
# Pass `P3`, first part: the union of location records and requests

`p3Gen` drops the old records (`moveAllS qRec qJunk`), pushes the location records again
(`p1r`, which leaves the cursor at the position of `E`), reads `E`, sets `rKL = k ℓ`,
`rSB = 0`, `rJ = 0`, runs the schema loop `p3Loop` and moves everything onto `qX`, which then
holds `(union I).flatten` (**`p3Gen_good`**).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- **The generation part of `P3`.** -/
def p3Gen : CStm CR CQ :=
  .seq (moveAllS qRec qJunk rT rT2) (.seq p1r (.seq (rdNumS rE rP rT)
    (.seq (mulS rKL rKk rL rGj) (.seq (.set rSB (.const 0)) (.seq (.set rJ (.const 0))
      (.seq p3Loop (moveAllS qRec qX rT rT2)))))))

lemma p3Gen_arith (N U h q ℓ lE X : ℕ) (hU : U ≤ N) (hq : q ≤ 6 * (h + 1))
    (hlE : lE ≤ h) (hℓ : ℓ ≤ h) (hX : X * (ℓ + 1) ≤ 4 * h) :
    (q + 1) * (10 * N) + (600 * (h + 1) * N + ((lE + 1) * (20 * N) + ((ℓ + 1) * (12 * N) +
      (1 * N + U + (1 * N + U + (30000 * (h + 1) * N +
        (X * (ℓ + 6) + 1) * (10 * N))))))) ≤ 32000 * (h + 1) * N := by
  have hX6 : X * (ℓ + 6) ≤ 6 * (X * (ℓ + 1)) := by nlinarith
  have e1 : (q + 1) * (10 * N) ≤ (6 * (h + 1) + 1) * (10 * N) := Nat.mul_le_mul_right _ (by omega)
  have e2 : (lE + 1) * (20 * N) ≤ (h + 1) * (20 * N) := Nat.mul_le_mul_right _ (by omega)
  have e3 : (ℓ + 1) * (12 * N) ≤ (h + 1) * (12 * N) := Nat.mul_le_mul_right _ (by omega)
  have e4 : (X * (ℓ + 6) + 1) * (10 * N) ≤ (24 * h + 1) * (10 * N) :=
    Nat.mul_le_mul_right _ (by omega)
  have e5 : (6 * (h + 1) + 1) * (10 * N) + 600 * (h + 1) * N + (h + 1) * (20 * N) +
      (h + 1) * (12 * N) + 1 * N + N + (1 * N + N + (30000 * (h + 1) * N)) +
      (24 * h + 1) * (10 * N) ≤ 32000 * (h + 1) * N := by
    have : (6 * (h + 1) + 1) * (10 * N) + 600 * (h + 1) * N + (h + 1) * (20 * N) +
      (h + 1) * (12 * N) + 1 * N + N + (1 * N + N + (30000 * (h + 1) * N)) +
      (24 * h + 1) * (10 * N) = 30932 * (h * N) + 30716 * N := by ring
    rw [this]
    have : 32000 * (h + 1) * N = 32000 * (h * N) + 32000 * N := by ring
    rw [this]; omega
  omega

set_option maxHeartbeats 4000000 in
/-- **The generation part of `P3`.** From any state with `rW = W`, `rL = ℓ`, `rL1 = ℓ + 1`
and empty generation stacks, `p3Gen` leaves `(union I).flatten` on `qX`, empties
`qRec` and ends at the end of the input with `rCnt = |locRecs I|`, `rSB = |reqs I|`. -/
theorem p3Gen_good {w : ℕ} (hw : 2 ≤ w) (hk : 1 ≤ k) (hE : I.schemas ≠ [])
    (hS : 16 * (H I + 1) ≤ 2 ^ w) (st : NSt CR CQ) (hb : st.Bdd w) (hp : st.pos ≤ H I)
    (hW : st.env rW = I.numLocations) (hL : st.env rL = ℓ) (hL1 : st.env rL1 = ℓ + 1)
    (hG : GenEmpty st) (hRecL : (st.stk qRec).length ≤ 6 * (H I + 1)) :
    ∃ st', Good (encodeSystem I) w p3Gen st st' (32000 * (H I + 1) * Ex.nodeCost w) ∧
      st'.stk qX = (union I).flatten ∧ st'.stk qRec = [] ∧
      st'.stk qLs = [] ∧ st'.stk qLs2 = [] ∧ st'.stk qF2 = [] ∧ st'.stk qDl = [] ∧
      st'.stk qDl2 = [] ∧ st'.stk qDom = [] ∧ st'.stk qDom2 = [] ∧ st'.stk qAux = [] ∧
      OtherStk st st' ∧
      st'.env rW = I.numLocations ∧ st'.env rL = ℓ ∧ st'.env rL1 = ℓ + 1 ∧ st'.env rKk = k ∧
      st'.env rE = I.schemas.length ∧ st'.env rKL = k * ℓ ∧
      st'.env rCnt = (locRecs I).length ∧ st'.env rSB = (reqs I).length ∧
      st'.pos = H I ∧ st'.out = st.out ∧ st'.Bdd w ∧
      ∀ r, wReg r p3Gen = false → st'.env r = st.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hU0 := Ex.unitCost_le_nodeCost w
  have hkH := k_le_H I hE
  have hℓ := ell_le_H I hk (fun h => hE h.2)
  have hEH := E_le I
  have hH2 : 2 * (H I + 1) ≤ 2 ^ w := by omega
  have hpx : st.pos ≤ (encodeSystem I).length := hp
  -- drop the old records
  obtain ⟨s1, r1, h1S, h1p, h1o, h1e⟩ := moveAllS_good (x := encodeSystem I) hw (q := qRec)
    (q' := qJunk) (t := rT) (f := rT2) (by decide) (by decide) st hb
  -- the location records
  obtain ⟨s2, r2, h2S, h2o, h2p, h2W, h2L1, h2K, h2C, h2e⟩ := p1r_good I hw (by omega) hkH hℓ s1
    (by rw [h1p]; exact hp) (by rw [h1e _ (by decide) (by decide), hW])
    (by rw [h1e _ (by decide) (by decide), hL1])
  -- `E`
  have r3 := rdNumS_good (Q := CQ) hw (r := rE) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s2 I.schemas.length _ (by rw [h2p, drop_posAt_W]) (bits_lt_of_le hEH hH2)
  set s3 := rdNumFinal s2 rE rP rT I.schemas.length
  have e3 : ∀ q, q ≠ rE → q ≠ rP → q ≠ rT → s3.env q = s2.env q :=
    fun q h1 h2 h3 => rdNumFinal_env_ne h1 h2 h3 _
  have e2L : s2.env rL = ℓ := by
    rw [h2e _ (by decide), h1e _ (by decide) (by decide), hL]
  have r4 := mulS_good (x := encodeSystem I) (w := w) (Q := CQ) hw (dst := rKL) (a := rKk)
    (b := rL) (j := rGj) (by decide) (by decide) (by decide) (by decide) (by decide) s3
    (by rw [e3 _ (by decide) (by decide) (by decide), h2K])
    (by rw [e3 _ (by decide) (by decide) (by decide), e2L])
    (by have := kl_le_H I hE; have : k * ℓ ≤ k * (ℓ + 1) := Nat.mul_le_mul_left _ (by omega)
        omega) (by omega)
  set s4 := (s3.set rKL (k * ℓ)).set rGj ℓ
  have r5 := Good.set (x := encodeSystem I) (w := w) (st := s4) (r := rSB) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  set s5 := s4.set rSB ((Ex.const 0 : Ex CR).eval s4.env)
  have r6 := Good.set (x := encodeSystem I) (w := w) (st := s5) (r := rJ) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  set s6 := s5.set rJ ((Ex.const 0 : Ex CR).eval s5.env)
  have h36 := r3.seq (r4.seq (r5.seq r6))
  have h46 := r4.seq (r5.seq r6)
  have hpre := r1.seq (r2.seq h36)
  have hb6 := hpre.bdd hw hb hpx
  -- stacks of `s6`
  have h6S : ∀ q, s6.stk q = s2.stk q := fun q => by
    show s3.stk q = _; rfl
  have h2S' : ∀ q, q ≠ qRec → s2.stk q = s1.stk q := fun q hq => by
    rw [h2S, Function.update_of_ne hq]
  have h1S' : ∀ q, q ≠ qRec → q ≠ qJunk → s1.stk q = st.stk q := fun q hq hq' => by
    rw [h1S, Function.update_of_ne hq', Function.update_of_ne hq]
  have hg : ∀ q, q ≠ qRec → q ≠ qJunk → s6.stk q = st.stk q := fun q hq hq' => by
    rw [h6S, h2S' q hq, h1S' q hq hq']
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := hG
  have hG6 : GenEmpty s6 := ⟨by rw [hg _ (by decide) (by decide), g1],
    by rw [hg _ (by decide) (by decide), g2], by rw [hg _ (by decide) (by decide), g3],
    by rw [hg _ (by decide) (by decide), g4], by rw [hg _ (by decide) (by decide), g5],
    by rw [hg _ (by decide) (by decide), g6], by rw [hg _ (by decide) (by decide), g7],
    by rw [hg _ (by decide) (by decide), g8], by rw [hg _ (by decide) (by decide), g9]⟩
  have h6Rec : s6.stk qRec = (locRecs I).flatten.reverse := by
    rw [h6S, h2S, Function.update_self, h1S, Function.update_of_ne (by decide),
      Function.update_self, List.append_nil]
  -- the schema loop
  obtain ⟨s7, r7, hG7, h7Rec, hO7, h7SB, h7p, h7o, hb7, h7e⟩ := p3Loop_good I hw hk hE hS s6
    hb6.1 (by simp [s6, Ex.eval])
    (by rw [h46.env_of (by decide)]; exact rdNumFinal_env_r (by decide) (by decide) _)
    (by rw [h36.env_of (by decide), h2K])
    (by simp [s6, s5, s4, Function.update_of_ne (show rKL ≠ rGj by decide),
      Function.update_of_ne (show rKL ≠ rJ by decide), Function.update_of_ne (show rKL ≠ rSB by decide)])
    (by rw [h36.env_of (by decide), e2L]) (by rw [h36.env_of (by decide), h2L1])
    (by simp [s6, s5, Ex.eval, Function.update_of_ne (show rSB ≠ rJ by decide)])
    (by show s2.pos + _ = _; rw [h2p]; rfl) hG6
  -- onto `qX`
  obtain ⟨s8, r8, h8S, h8p, h8o, h8e⟩ := moveAllS_good (x := encodeSystem I) hw (q := qRec)
    (q' := qX) (t := rT) (f := rT2) (by decide) (by decide) s7 hb7
  have hall := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq r8))))))
  have h8S' : ∀ q, q ≠ qRec → q ≠ qX → s8.stk q = s7.stk q := fun q hq hq' => by
    rw [h8S, Function.update_of_ne hq', Function.update_of_ne hq]
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := hG7
  have h7R : s7.stk qRec = ((union I).flatten).reverse := by
    rw [h7Rec, h6Rec, union, List.flatten_append, List.reverse_append]
  refine ⟨s8, hall.mono ?_, ?_, ?_, by rw [h8S' _ (by decide) (by decide), k1],
    by rw [h8S' _ (by decide) (by decide), k2], by rw [h8S' _ (by decide) (by decide), k4],
    by rw [h8S' _ (by decide) (by decide), k5], by rw [h8S' _ (by decide) (by decide), k6],
    by rw [h8S' _ (by decide) (by decide), k7], by rw [h8S' _ (by decide) (by decide), k8],
    by rw [h8S' _ (by decide) (by decide), k9], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [h8p, h7p], by rw [h8o, h7o]; exact hpre.out_of (by decide),
    (r8.bdd hw hb7 (by rw [h7p])).1, fun r hr => hall.env_of hr⟩
  · -- cost
    rw [h7R, List.length_reverse, length_flatten_union]
    have hlE : (encodeNat I.schemas.length).length ≤ H I := by
      have h := congrArg List.length (drop_posAt_W I)
      simp only [List.length_drop, List.length_append] at h
      show _ ≤ (encodeSystem I).length
      omega
    simp only [condCost, Ex.size, rv]
    exact p3Gen_arith _ _ _ _ _ _ _ hU0 hRecL hlE hℓ (union_mul_le I)
  · rw [h8S, Function.update_self, h7R, List.reverse_reverse, show s7.stk qX = [] from k3, List.append_nil]
  · rw [h8S, Function.update_of_ne (by decide), Function.update_self]
  · intro q n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11
    have hqX : q ≠ qX := n3
    rw [h8S' q n10 hqX, hO7 q n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11, hg q n10 n11]
  · rw [h8e _ (by decide) (by decide), h7e _ (by decide), h46.env_of (by decide),
      e3 _ (by decide) (by decide) (by decide), h2W]
  · rw [h8e _ (by decide) (by decide), h7e _ (by decide), h46.env_of (by decide),
      e3 _ (by decide) (by decide) (by decide), e2L]
  · rw [h8e _ (by decide) (by decide), h7e _ (by decide), h46.env_of (by decide),
      e3 _ (by decide) (by decide) (by decide), h2L1]
  · rw [h8e _ (by decide) (by decide), h7e _ (by decide), h46.env_of (by decide),
      e3 _ (by decide) (by decide) (by decide), h2K]
  · rw [h8e _ (by decide) (by decide), h7e _ (by decide), h46.env_of (by decide)]
    exact rdNumFinal_env_r (by decide) (by decide) _
  · rw [h8e _ (by decide) (by decide), h7e _ (by decide)]
    simp [s6, s5, s4, Function.update_of_ne (show rKL ≠ rGj by decide),
      Function.update_of_ne (show rKL ≠ rJ by decide), Function.update_of_ne (show rKL ≠ rSB by decide)]
  · rw [h8e _ (by decide) (by decide), h7e _ (by decide), h46.env_of (by decide),
      e3 _ (by decide) (by decide) (by decide), h2C]
  · rw [h8e _ (by decide) (by decide), h7SB]

end Lax119563Proofs.Compiler

end Compiler_P3Gen

/-! ### Formerly `Lax119563Proofs.Compiler.P3` -/

section Compiler_P3

/-!
# Pass `P3` (requests and the join): the assembly

`p3 = p3Gen; p3Join` (**`p3_good`**): from a state with `rW = W`, `rL = ℓ`, `rL1 = ℓ + 1`,
empty generation stacks and `qAns = []`, `p3` leaves the sorted answers on
`qAns` (`ansAll I`, the order of `P4`) within `200000 (H + 1) (log₂ (H + 1) + 1) · nodeCost w`.

The answers are `ansAll I` (`PJoinFacts.p3_answers`): the order in which `P4` consumes them.
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- **Pass `P3`.** -/
def p3 : CStm CR CQ := .seq p3Gen p3Join

lemma p3_arith (N h lg : ℕ) :
    32000 * (h + 1) * N + 150000 * (h + 1) * (lg + 1) * N ≤
      200000 * (h + 1) * (lg + 1) * N := by
  have : 32000 * (h + 1) * N ≤ 32000 * (h + 1) * (lg + 1) * N := by
    have := Nat.le_mul_of_pos_right (32000 * (h + 1)) (Nat.succ_pos lg)
    exact Nat.mul_le_mul_right _ this
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **Pass `P3`.** -/
theorem p3_good {w : ℕ} (hw : 2 ≤ w) (hk : 1 ≤ k) (hE : I.schemas ≠ [])
    (hS : 16 * (H I + 1) ≤ 2 ^ w)
    (st : NSt CR CQ) (hb : st.Bdd w) (hp : st.pos ≤ H I)
    (hW : st.env rW = I.numLocations) (hL : st.env rL = ℓ) (hL1 : st.env rL1 = ℓ + 1)
    (hG : GenEmpty st) (hAns : st.stk qAns = []) (hRecL : (st.stk qRec).length ≤ 6 * (H I + 1)) :
    ∃ st', Good (encodeSystem I) w p3 st st'
        (200000 * (H I + 1) * (Nat.log 2 (H I + 1) + 1) * Ex.nodeCost w) ∧
      st'.stk qAns = (ansAll I).flatten ∧ st'.stk qX = [] ∧ st'.stk qRec = [] ∧
      st'.stk qLs = [] ∧ st'.stk qLs2 = [] ∧ st'.stk qF2 = [] ∧ st'.stk qDl = [] ∧
      st'.stk qDl2 = [] ∧ st'.stk qDom = [] ∧ st'.stk qDom2 = [] ∧ st'.stk qAux = [] ∧
      (∀ q, q ≠ qLs → q ≠ qLs2 → q ≠ qF → q ≠ qF2 → q ≠ qDl → q ≠ qDl2 → q ≠ qDom →
        q ≠ qDom2 → q ≠ qAux → q ≠ qRec → q ≠ qJunk → q ≠ qAns → st'.stk q = st.stk q) ∧
      st'.env rW = I.numLocations ∧ st'.env rL = ℓ ∧ st'.env rL1 = ℓ + 1 ∧ st'.env rKk = k ∧
      st'.env rE = I.schemas.length ∧ st'.env rKL = k * ℓ ∧
      st'.env rCnt = (locRecs I).length ∧ st'.env rSB = (reqs I).length ∧
      st'.pos = H I ∧ st'.out = st.out ∧
      ∀ r, wReg r p3 = false → st'.env r = st.env r := by
  obtain ⟨s1, r1, h1X, h1R, g1, g2, g3, g4, g5, g6, g7, g8, hO1, e1W, e1L, e1L1, e1K, e1E, e1KL,
    e1C, e1SB, h1p, h1o, -, h1e⟩ := p3Gen_good I hw hk hE hS st hb hp hW hL hL1 hG hRecL
  have h1A : s1.stk qAns = [] := by
    rw [hO1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hAns]
  obtain ⟨s2, r2, h2A, h2X, h2S, h2p, h2o, h2e⟩ := p3Join_good I hw hk hE hS s1 h1X g3 g4
    g5 h1A e1L e1C e1SB
  have hall := r1.seq r2
  have hS2 : ∀ q, q ≠ qX → q ≠ qAns → q ≠ qJunk → s2.stk q = s1.stk q := h2S
  refine ⟨s2, hall.mono (p3_arith _ _ _), h2A, h2X, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [h2p, h1p], by rw [h2o, h1o],
    fun r hr => hall.env_of hr⟩
  · rw [hS2 _ (by decide) (by decide) (by decide), h1R]
  · rw [hS2 _ (by decide) (by decide) (by decide), g1]
  · rw [hS2 _ (by decide) (by decide) (by decide), g2]
  · rw [hS2 _ (by decide) (by decide) (by decide), g3]
  · rw [hS2 _ (by decide) (by decide) (by decide), g4]
  · rw [hS2 _ (by decide) (by decide) (by decide), g5]
  · rw [hS2 _ (by decide) (by decide) (by decide), g6]
  · rw [hS2 _ (by decide) (by decide) (by decide), g7]
  · rw [hS2 _ (by decide) (by decide) (by decide), g8]
  · intro q n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12
    rw [hS2 q n3 n12 n11, hO1 q n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11]
  · rw [h2e _ (by decide), e1W]
  · rw [h2e _ (by decide), e1L]
  · rw [h2e _ (by decide), e1L1]
  · rw [h2e _ (by decide), e1K]
  · rw [h2e _ (by decide), e1E]
  · rw [h2e _ (by decide), e1KL]
  · rw [h2e _ (by decide), e1C]
  · rw [h2e _ (by decide), e1SB]

end Lax119563Proofs.Compiler

end Compiler_P3

/-! ### Formerly `Lax119563Proofs.Compiler.PChain` -/

section Compiler_PChain

/-!
# The chain of passes `P0`–`P3`

`pre = p0; if rTriv then skip else (p1; if rE then (p1r; p2; p3) else skip)`.

* trivial system (`trivSys I`): `rTriv = 1`, all stacks empty, nothing emitted;
* nontrivial, `E = 0`: `p1` only (`p1r` needs `k ≤ H`, `p2`/`p3` need a schema);
* nontrivial, `E > 0`: all passes.

**`pre_good`**: from `NSt.zero`, under `16 (H + locBase + 1) ≤ 2^w`, with cost
`210000 (H + 1)(log₂(H + 1) + 1) · nodeCost w`; the end state is described by `ChainLoc`
(nontrivial), `ChainNoSch` (`E = 0`) and `ChainSch` (`E > 0`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

/-- The passes `P1'`, `P2`, `P3` (nontrivial systems with a schema). -/
def preSch : CStm CR CQ := .seq p1r (.seq p2 p3)

/-- The passes for a nontrivial system. -/
def preNT : CStm CR CQ := .seq p1 (.ite (rv rE) preSch .skip)

/-- **The passes `P0`–`P3`.** -/
def pre : CStm CR CQ := .seq p0 (.ite (rv rTriv) .skip preNT)

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- End state, nontrivial system. -/
def ChainLoc (st : NSt CR CQ) : Prop :=
  st.env rTriv = 0 ∧ st.env rW = I.numLocations ∧ st.env rL = ℓ ∧
    st.env rE = I.schemas.length ∧ st.stk qLoc = (locOffs I).reverse

/-- End state, nontrivial system without schemas. -/
def ChainNoSch (st : NSt CR CQ) : Prop :=
  st.env rOff = locOff I I.numLocations ∧ st.pos = schPos I ∧ ∀ q, q ≠ qLoc → st.stk q = []

/-- End state, system with a schema. -/
def ChainSch (st : NSt CR CQ) : Prop :=
  st.stk qAns = (ansAll I).flatten ∧ st.stk qSch = (schRecsUpTo I I.schemas.length).reverse ∧
    (∀ q, q ≠ qLoc → q ≠ qSch → q ≠ qAns → q ≠ qJunk → st.stk q = []) ∧
    st.env rLB = locBase I ∧ st.env rL1 = ℓ + 1 ∧ st.env rKk = k ∧ st.env rKL = k * ℓ ∧
    st.env rCnt = (locRecs I).length ∧ st.env rSB = (reqs I).length ∧ st.pos = H I

lemma pre_arith {N h lg c c' u : ℕ} (hc : c ≤ 2 * N) (hc' : c' ≤ 2 * N) (hu : u ≤ N) :
    200 * (h + 1) * N + (c + (500 * (h + 1) * N + (c' + (600 * (h + 1) * N +
      (2000 * (h + 1) * N + 200000 * (h + 1) * (lg + 1) * N))))) ≤
      210000 * (h + 1) * (lg + 1) * N ∧
    200 * (h + 1) * N + (c + (500 * (h + 1) * N + (c' + u))) ≤
      210000 * (h + 1) * (lg + 1) * N ∧
    200 * (h + 1) * N + (c + u) ≤ 210000 * (h + 1) * (lg + 1) * N := by
  have h1 : (h + 1) * N ≤ (h + 1) * (lg + 1) * N := by
    have := Nat.le_mul_of_pos_right (h + 1) (Nat.succ_pos lg)
    exact Nat.mul_le_mul_right _ this
  have h2 : N ≤ (h + 1) * N := Nat.le_mul_of_pos_left N (Nat.succ_pos h)
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

lemma condCost_rv (w : ℕ) (r : Fin CR) : condCost w (rv r) ≤ 2 * Ex.nodeCost w := by
  have := CStm.nodeCost_ge w
  have := CStm.unitCost_ge w
  simp only [condCost, Ex.size]; omega

lemma zero_bdd (w : ℕ) : (NSt.zero CR CQ).Bdd w :=
  ⟨fun _ => Nat.pos_of_ne_zero (by positivity), fun _ v hv => by simp [NSt.zero] at hv⟩

lemma exec_set_succ {b : CStm CR CQ} {r r' : Fin CR} (hne : r ≠ r') (hb : wReg r b = false)
    (hb' : wReg r' b = false) (x : List Bool) (st : NSt CR CQ) :
    (exec x (.seq (.set r (.add (rv r') (.const 1))) b) st).env r =
      (exec x (.seq (.set r (.add (rv r') (.const 1))) b) st).env r' + 1 := by
  simp only [CStm.exec]
  rw [exec_env_of b _ hb, exec_env_of b _ hb']
  simp [NSt.set, Function.update_of_ne hne.symm, Ex.eval]

/-- `p1` leaves `rL1 = rL + 1`. -/
lemma p1_rL1 (x : List Bool) (st : NSt CR CQ) :
    (exec x p1 st).env rL1 = (exec x p1 st).env rL + 1 := by
  have e : exec x p1 st = exec x (.seq (.set rL1 (.add (rv rL) (.const 1)))
      (.seq (rdNumS rW rP rT) (.seq (.set rJ (.const 0)) (.seq (.set rOff (.const 0))
        (.seq p1Loop (rdNumS rE rP rT))))))
      (exec x (rdNumS rL rP rT) (exec x (skipNumS rT) (exec x .rst st))) := by
    simp only [p1, CStm.exec]
  rw [e]
  exact exec_set_succ (by decide) (by decide) (by decide) _ _

set_option maxHeartbeats 4000000 in
/-- **The passes `P0`–`P3`** from the zero state. -/
theorem pre_good {w : ℕ} (hw : 2 ≤ w) (hk : 1 ≤ k) (hS : 16 * (H I + locBase I + 1) ≤ 2 ^ w) :
    ∃ st', Good (encodeSystem I) w pre (NSt.zero CR CQ) st'
        (210000 * (H I + 1) * (Nat.log 2 (H I + 1) + 1) * Ex.nodeCost w) ∧
      st'.out = [] ∧ st'.Bdd w ∧ st'.pos ≤ H I ∧
      (trivSys I → st'.env rTriv = 1 ∧ ∀ q, st'.stk q = []) ∧
      (¬ trivSys I → ChainLoc I st' ∧ (I.schemas = [] → ChainNoSch I st') ∧
        (I.schemas ≠ [] → ChainSch I st')) := by
  have hU := CStm.nodeCost_ge w
  have hc := condCost_rv w
  have h4 : 4 ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num : 0 < 2) hw)
  obtain ⟨s0, r0, h0s, h0o, h0t, h0t1⟩ := p0_good I hw (by omega) (NSt.zero CR CQ) rfl
  have hz0 : ∀ q, s0.stk q = [] := fun q => by rw [h0s]; rfl
  have hb0 := r0.bdd hw (zero_bdd w) (Nat.zero_le _)
  have hf0 : (rv rTriv).Fits w s0.env := by
    show s0.env rTriv < 2 ^ w; omega
  by_cases ht : trivSys I
  · have e1 : s0.env rTriv = 1 := h0t.mpr ht
    have r := r0.seq (Good.iteT (q := preNT) hf0 (by show s0.env rTriv ≠ 0; omega) Good.skip)
    exact ⟨s0, r.mono (pre_arith (hc rTriv) (hc rE) hU).2.2, h0o, hb0.1, hb0.2,
      fun _ => ⟨e1, hz0⟩, fun h => absurd ht h⟩
  have e1 : s0.env rTriv = 0 := by
    have := mt h0t.mp ht; omega
  have hℓ := ell_le_H I hk ht
  obtain ⟨s1, r1, h1s, h1o, h1p, h1W, h1L, h1E, h1Off⟩ := p1_good I hw (by omega) hℓ s0 hb0.2
  have hb1 := r1.bdd hw hb0.1 hb0.2
  have e1' : s1.env rTriv = 0 := by rw [r1.env_of (by decide), e1]
  have hf1 : (rv rE).Fits w s1.env := by
    show s1.env rE < 2 ^ w; have := E_le I; omega
  have hLoc1 : s1.stk qLoc = (locOffs I).reverse := by
    rw [h1s, Function.update_self, hz0, List.append_nil]
  have hT0 : (rv rTriv).eval s0.env = 0 := e1
  by_cases hE : I.schemas = []
  · have hE0 : (rv rE).eval s1.env = 0 := by show s1.env rE = 0; rw [h1E, hE]; rfl
    have r := r0.seq (Good.iteF (p := .skip) hf0 hT0
      (r1.seq (Good.iteF (p := preSch) hf1 hE0 Good.skip)))
    refine ⟨s1, r.mono (pre_arith (hc rTriv) (hc rE) hU).2.1, by rw [h1o, h0o]; rfl, hb1.1,
      hb1.2, fun h => absurd h ht, fun _ =>
        ⟨⟨e1', h1W, h1L, h1E, hLoc1⟩, fun _ => ⟨h1Off, h1p, fun q hq => ?_⟩,
          fun h => absurd hE h⟩⟩
    rw [h1s, Function.update_of_ne hq, hz0]
  have hEpos : (rv rE).eval s1.env ≠ 0 := by
    show s1.env rE ≠ 0; rw [h1E]; exact fun h => hE (List.length_eq_zero_iff.mp h)
  have hkH := k_le_H I hE
  have hL1 : s1.env rL1 = ℓ + 1 := by rw [← r1.2.1, p1_rL1, r1.2.1, h1L]
  obtain ⟨s2, r2, h2s, h2o, h2p, h2W, h2L1, h2K, h2C, h2e⟩ :=
    p1r_good I hw (by omega) hkH hℓ s1 hb1.2 h1W hL1
  have hb2 := r2.bdd hw hb1.1 hb1.2
  have h2L : s2.env rL = ℓ := by rw [h2e _ (by decide), h1L]
  have hz2 : ∀ q, q ≠ qLoc → q ≠ qRec → s2.stk q = [] := fun q a b => by
    rw [h2s, Function.update_of_ne b, h1s, Function.update_of_ne a, hz0]
  obtain ⟨s3, r3, h3LB, h3s, h3o, h3p, h3e⟩ := p2_good I hw hk hE hS s2 h2p h2K h2L h2L1
    (hz2 _ (by decide) (by decide)) (hz2 _ (by decide) (by decide))
  have hb3 := r3.bdd hw hb2.1 hb2.2
  have hz3 : ∀ q, q ≠ qLoc → q ≠ qRec → q ≠ qSch → s3.stk q = [] := fun q a b c => by
    rw [h3s, Function.update_of_ne c, hz2 q a b]
  have hRec3 : s3.stk qRec = (locRecs I).flatten.reverse := by
    rw [h3s, Function.update_of_ne (by decide), h2s, Function.update_self, h1s,
      Function.update_of_ne (by decide), hz0, List.append_nil]
  have hG : GenEmpty s3 := ⟨hz3 _ (by decide) (by decide) (by decide),
    hz3 _ (by decide) (by decide) (by decide), hz3 _ (by decide) (by decide) (by decide),
    hz3 _ (by decide) (by decide) (by decide), hz3 _ (by decide) (by decide) (by decide),
    hz3 _ (by decide) (by decide) (by decide), hz3 _ (by decide) (by decide) (by decide),
    hz3 _ (by decide) (by decide) (by decide), hz3 _ (by decide) (by decide) (by decide)⟩
  have hRecL : (s3.stk qRec).length ≤ 6 * (H I + 1) := by
    rw [hRec3, List.length_reverse, List.length_flatten]
    have : (locRecs I).map List.length = (locRecs I).map fun _ => ℓ + 6 :=
      List.map_congr_left fun m hm => length_of_mem_union I (List.mem_append_left _ hm)
    rw [this, sum_map_const]
    have := length_locRecs_mul_le I
    nlinarith
  obtain ⟨s4, r4, gA, gX, gR, gLs, gLs2, gF2, gDl, gDl2, gDom, gDom2, gAux, hO, e4W, e4L, e4L1,
    e4K, e4E, e4KL, e4C, e4SB, h4p, h4o, h4e⟩ := p3_good I hw hk hE (by omega) s3 hb3.1
    hb3.2 (by rw [h3e _ (by decide), h2W])
    (by rw [h3e _ (by decide), h2L]) (by rw [h3e _ (by decide), h2L1]) hG
    (hz3 _ (by decide) (by decide) (by decide)) hRecL
  have r := r0.seq (Good.iteF (p := .skip) hf0 hT0
    (r1.seq (Good.iteT (q := .skip) hf1 hEpos (r2.seq (r3.seq r4)))))
  have hb4 := r4.bdd hw hb3.1 hb3.2
  have h4Loc : s4.stk qLoc = (locOffs I).reverse := by
    rw [hO _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h3s,
      Function.update_of_ne (by decide), h2s, Function.update_of_ne (by decide), hLoc1]
  refine ⟨s4, r.mono (pre_arith (hc rTriv) (hc rE) hU).1, by rw [h4o, h3o, h2o, h1o, h0o]; rfl,
    hb4.1, hb4.2, fun h => absurd h ht, fun _ =>
      ⟨⟨?_, e4W, e4L, e4E, h4Loc⟩, fun h => absurd h hE, fun _ =>
        ⟨gA, ?_, ?_, by rw [h4e _ (by decide), h3LB], e4L1, e4K, e4KL, e4C, e4SB, h4p⟩⟩⟩
  · rw [h4e _ (by decide), h3e _ (by decide), h2e _ (by decide), e1']
  · rw [hO _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h3s,
      Function.update_self, hz2 _ (by decide) (by decide), List.append_nil]
  · intro q a b c d
    by_cases x1 : q = qX
    · rw [x1]; exact gX
    by_cases x2 : q = qRec
    · rw [x2]; exact gR
    by_cases x3 : q = qLs
    · rw [x3]; exact gLs
    by_cases x4 : q = qLs2
    · rw [x4]; exact gLs2
    by_cases x5 : q = qF2
    · rw [x5]; exact gF2
    by_cases x6 : q = qDl
    · rw [x6]; exact gDl
    by_cases x7 : q = qDl2
    · rw [x7]; exact gDl2
    by_cases x8 : q = qDom
    · rw [x8]; exact gDom
    by_cases x9 : q = qDom2
    · rw [x9]; exact gDom2
    by_cases x10 : q = qAux
    · rw [x10]; exact gAux
    rw [hO q x3 x4 x1 x5 x6 x7 x8 x9 x10 x2 d c]
    exact hz3 q a x2 b

end Lax119563Proofs.Compiler

end Compiler_PChain

/-! ### Formerly `Lax119563Proofs.Compiler.P4Round` -/

section Compiler_P4Round

/-!
# Pass `P4` (program): one round, with the schema edge part as a parameter

`p4Round SCH = p4Loc; (if E ≠ 0 then p4SzS; SCH); p4Emit`, where `SCH` is the schema edge
part, specified by `SchSpec` (from `SchPre`: push `gEdges I ε` via `EdgeEff`, keep `p4Keep`).
**`p4Round_good`**: from a round-start state (`P4Inv`), the output is extended by `gDesc I ε`
and `P4Inv` holds again (all stacks restored).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- One round of `P4`. -/
def p4Round (SCH : CStm CR CQ) : CStm CR CQ :=
  .seq p4Loc (.seq (.ite (rv rE) (.seq p4SzS SCH) .skip) p4Emit)

/-- The round-start states. -/
def P4Inv (w : ℕ) (st : NSt CR CQ) : Prop :=
  st.Bdd w ∧ st.pos ≤ H I ∧ st.env rTriv = 0 ∧ st.env rW = I.numLocations ∧ st.env rL = ℓ ∧
    st.env rE = I.schemas.length ∧
    (I.schemas ≠ [] → st.env rKk = k ∧ st.env rKL = k * ℓ ∧ st.env rLB = locBase I) ∧
    st.stk qAns = (ansAll I).flatten ∧ st.stk qSch = (schRecsUpTo I I.schemas.length).reverse ∧
    ∀ q, q ≠ qLoc → q ≠ qSch → q ≠ qAns → q ≠ qJunk → st.stk q = []

/-- The start states of the schema edge part. -/
def SchPre (ε w : ℕ) (st : NSt CR CQ) : Prop :=
  I.schemas ≠ [] ∧ st.Bdd w ∧ st.pos = H I ∧ st.env r4Eps = ε ∧ st.env r4M = 0 ∧
    st.env rTriv = 0 ∧ st.env rW = I.numLocations ∧ st.env rL = ℓ ∧ st.env rL1 = ℓ + 1 ∧
    st.env rE = I.schemas.length ∧ st.env rKk = k ∧ st.env rKL = k * ℓ ∧
    st.env rLB = locBase I ∧
    st.stk qAns = (ansAll I).flatten ∧ st.stk qSch = (schRecsUpTo I I.schemas.length).reverse ∧
    ∀ q, q ≠ qLoc → q ≠ qSch → q ≠ qAns → q ≠ qJunk → q ≠ qSzB → st.stk q = []

/-- The registers the schema edge part must keep. -/
def p4Keep : List (Fin CR) := [rTriv, rW, rL, rE, rKk, rKL, rLB, rNt]

/-- **The interface of the schema edge part** (cost `C`). -/
def SchSpec (w : ℕ) (SCH : CStm CR CQ) (C : ℕ) : Prop :=
  ∀ ε ≤ 1, ∀ st, SchPre I ε w st → ∃ st', Good (encodeSystem I) w SCH st st' C ∧
    EdgeEff st st' (gEdges I ε) ∧ ∀ r ∈ p4Keep, st'.env r = st.env r

lemma schAll_nil (h : I.schemas = []) : schAll I = [] := by
  have : List.finRange I.schemas.length = [] := List.eq_nil_of_length_eq_zero (by simp (config := { decide := true }) [h])
  rw [schAll, this]; rfl

lemma gEdges_nil (h : I.schemas = []) (ε : ℕ) : gEdges I ε = [] := by
  have : List.finRange I.schemas.length = [] := List.eq_nil_of_length_eq_zero (by simp (config := { decide := true }) [h])
  rw [gEdges, this]; rfl

lemma clsSizes_eq' : clsSizes I = schAll I ++ locAll I := clsSizes_eq I

lemma gDesc_eq_descOf (ε : ℕ) : gDesc I ε = descOf (clsSizes I) (gEdges I ε) := rfl

/-- The size measure of a round. -/
noncomputable def p4Z (ε : ℕ) : ℕ :=
  (schRecsUpTo I I.schemas.length).length + (clsSizes I).length + (clsSizes I).sum +
    (gEdges I ε).length

lemma p4Round_arith {N h Z a b L S M C : ℕ} (hN : 1 ≤ N) (h1 : a + b + L + M ≤ Z)
    (h2 : S ≤ Z) :
    800 * (h + 1) * N + (2 * N + (2000 * (h + a + b + 1) * N + C) +
      (L + S + 2 * M + 8) * (40 * N)) ≤ 4000 * (h + Z + 1) * N + C := by
  have := Nat.mul_le_mul_right N h1
  have := Nat.mul_le_mul_right N h2
  nlinarith

set_option maxHeartbeats 2000000 in
/-- **One round of `P4`.** -/
theorem p4Round_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hℓ : ℓ ≤ H I)
    (hk : 1 ≤ k) (hT : (clsSizes I).sum + 8 < 2 ^ w) {SCH : CStm CR CQ} {C : ℕ}
    (hSpec : SchSpec I w SCH C) {ε : ℕ} (hε1 : ε ≤ 1) (st : NSt CR CQ) (hI : P4Inv I w st)
    (hε : st.env r4Eps = ε) :
    ∃ st', Good (encodeSystem I) w (p4Round SCH) st st'
        (4000 * (H I + p4Z I ε + 1) * Ex.nodeCost w + C) ∧
      st'.out = st.out ++ gDesc I ε ∧ P4Inv I w st' := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hN1 : 1 ≤ Ex.nodeCost w := by omega
  obtain ⟨hb, hp, hTr, hW, hL, hE, hS, hAns, hSch, hemp⟩ := hI
  obtain ⟨s1, r1, h1s, h1p, h1o, h1N, h1M, h1L1⟩ :=
    p4Loc_good I hw hH hℓ st hb hp hW hL (hemp _ (by decide) (by decide) (by decide) (by decide))
  have hb1 := r1.bdd hw hb hp
  have hB0 : st.stk qSzB = [] := hemp _ (by decide) (by decide) (by decide) (by decide)
  have hE0 : st.stk q4E = [] := hemp _ (by decide) (by decide) (by decide) (by decide)
  have hA0 : st.stk qSzA = [] := hemp _ (by decide) (by decide) (by decide) (by decide)
  have hsumC : (clsSizes I).sum = locOff I I.numLocations + (schAll I).sum := by
    rw [clsSizes_eq', List.sum_append, locAll_sum]; ring
  have hlocS := locAll_sum I
  -- the frame shared by both cases: the final stacks are those of `st`
  suffices hmain : ∃ s3, Good (encodeSystem I) w (.ite (rv rE) (.seq p4SzS SCH) .skip) s1 s3
      (2 * Ex.nodeCost w + (2000 * (H I + (schRecsUpTo I I.schemas.length).length +
        (schAll I).sum + 1) * Ex.nodeCost w + C)) ∧
      s3.stk = Function.update (Function.update st.stk qSzB (clsSizes I)) q4E
        (pairsRev (gEdges I ε)) ∧
      s3.env rNt = (clsSizes I).sum ∧ s3.env r4M = (gEdges I ε).length ∧ s3.out = st.out ∧
      (∀ r ∈ p4Keep, r ≠ rNt → s3.env r = st.env r) by
    obtain ⟨s3, r3, h3s, h3N, h3M, h3o, h3k⟩ := hmain
    have hb3 := (r1.seq r3).bdd hw hb hp
    obtain ⟨s4, r4, h4o, h4s, h4p, h4e⟩ := p4Emit_good (x := encodeSystem I) hw s3 (clsSizes I)
      (gEdges I ε) hb3.1 hb3.2 (by rw [h3s]; simp (config := { decide := true }) [Function.update_of_ne (show qSzB ≠ q4E by decide)])
      (by rw [h3s]; simp) (by rw [h3s]; simp (config := { decide := true }) [Function.update_of_ne (show qSzA ≠ q4E by decide),
        Function.update_of_ne (show qSzA ≠ qSzB by decide), hA0]) h3N h3M
    have r := r1.seq (r3.seq r4)
    have hb4 := r.bdd hw hb hp
    have hs4 : s4.stk = st.stk := by
      rw [h4s, h3s]
      funext q
      by_cases h0 : q = q4E
      · subst h0; simp (config := { decide := true }) [hE0]
      by_cases h1 : q = qSzB
      · subst h1; simp (config := { decide := true }) [hB0]
      simp (config := { decide := true }) [Function.update_of_ne h0, Function.update_of_ne h1]
    have hk4 : ∀ r ∈ p4Keep, r ≠ rNt → s4.env r = st.env r := by
      intro r hr hn
      have hr' : r ≠ rT ∧ r ≠ rP ∧ r ≠ rJ ∧ r ≠ rA := by
        simp only [p4Keep, List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [h4e r hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2, h3k r hr hn]
    refine ⟨s4, r.mono ?_, by rw [h4o, h3o, gDesc_eq_descOf], ?_⟩
    · unfold p4Z
      have := p4Round_arith (N := Ex.nodeCost w) (h := H I) (Z := p4Z I ε)
        (a := (schRecsUpTo I I.schemas.length).length) (b := (schAll I).sum)
        (L := (clsSizes I).length) (S := (clsSizes I).sum) (M := (gEdges I ε).length)
        (C := C) hN1 (by unfold p4Z; omega) (by unfold p4Z; omega)
      unfold p4Z at this
      omega
    · refine ⟨hb4.1, hb4.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hk4 rTriv (by simp (config := { decide := true }) [p4Keep]) (by decide), hTr]
      · rw [hk4 rW (by simp (config := { decide := true }) [p4Keep]) (by decide), hW]
      · rw [hk4 rL (by simp (config := { decide := true }) [p4Keep]) (by decide), hL]
      · rw [hk4 rE (by simp (config := { decide := true }) [p4Keep]) (by decide), hE]
      · intro hne
        obtain ⟨a, b, c⟩ := hS hne
        exact ⟨by rw [hk4 rKk (by simp (config := { decide := true }) [p4Keep]) (by decide), a], by rw [hk4 rKL (by simp (config := { decide := true }) [p4Keep]) (by decide), b],
          by rw [hk4 rLB (by simp (config := { decide := true }) [p4Keep]) (by decide), c]⟩
      · rw [hs4, hAns]
      · rw [hs4, hSch]
      · intro q a b c d; rw [hs4]; exact hemp q a b c d
  -- the two cases
  have hs1 : s1.stk = Function.update st.stk qSzB (locAll I) := by rw [h1s, hB0, List.append_nil]
  have hfE : (rv rE : Ex CR).Fits w s1.env := hb1.1.1 rE
  have e1 : ∀ r ∈ p4Keep, r ≠ rNt → s1.env r = st.env r := by
    intro r hr hn
    simp only [p4Keep, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl hn | exact r1.env_of (by decide)
  by_cases hE' : I.schemas = []
  · have hc : (rv rE : Ex CR).eval s1.env = 0 := by
      show s1.env rE = 0; rw [r1.env_of (by decide), hE, hE']; rfl
    refine ⟨s1, (CStm.Good.iteF hfE hc CStm.Good.skip).mono ?_, ?_, ?_, ?_, h1o, ?_⟩
    · have : Ex.nodeCost w ≤ 2000 * (H I + (schRecsUpTo I I.schemas.length).length +
          (schAll I).sum + 1) * Ex.nodeCost w := Nat.le_mul_of_pos_left _ (by positivity)
      simp only [condCost, rv, Ex.size]; omega
    · rw [hs1, gEdges_nil I hE', clsSizes_eq', schAll_nil I hE']
      funext q
      by_cases h0 : q = q4E
      · subst h0; simp (config := { decide := true }) [hE0, pairsRev]
      · simp (config := { decide := true }) [Function.update_of_ne h0]
    · rw [h1N, hsumC, schAll_nil I hE']; rfl
    · rw [h1M, gEdges_nil I hE']; rfl
    · exact e1
  obtain ⟨hKk, hKL, hLB⟩ := hS hE'
  have hc : (rv rE : Ex CR).eval s1.env ≠ 0 := by
    show s1.env rE ≠ 0
    rw [r1.env_of (by decide), hE]; exact fun h => hE' (List.length_eq_zero_iff.mp h)
  obtain ⟨s2, r2, h2s, h2N, h2p, h2o⟩ := p4SzS_good I hw hH hk s1 hb1.1 h1p
    (by rw [r1.env_of (by decide), hE]) h1L1 (by rw [r1.env_of (by decide), hKk])
    (by rw [r1.stk_of (by decide), hSch])
    (by rw [r1.stk_of (by decide)]; exact hemp _ (by decide) (by decide) (by decide) (by decide))
    (by rw [hs1, Function.update_of_ne (by decide), hA0]) (by rw [h1N]; omega)
  have hb2 := (r1.seq r2).bdd hw hb hp
  have e2 : ∀ r, wReg r p4SzS = false → wReg r p4Loc = false → s2.env r = st.env r :=
    fun r a b => by rw [r2.env_of a, r1.env_of b]
  have hs2 : s2.stk = Function.update st.stk qSzB (clsSizes I) := by
    rw [h2s, hs1, clsSizes_eq']; simp
  have hpre : SchPre I ε w s2 := by
    refine ⟨hE', hb2.1, h2p, by rw [e2 _ (by decide) (by decide), hε],
      by rw [r2.env_of (by decide), h1M], by rw [e2 _ (by decide) (by decide), hTr],
      by rw [e2 _ (by decide) (by decide), hW], by rw [e2 _ (by decide) (by decide), hL],
      by rw [r2.env_of (by decide), h1L1], by rw [e2 _ (by decide) (by decide), hE],
      by rw [e2 _ (by decide) (by decide), hKk], by rw [e2 _ (by decide) (by decide), hKL],
      by rw [e2 _ (by decide) (by decide), hLB],
      by rw [hs2, Function.update_of_ne (by decide), hAns],
      by rw [hs2, Function.update_of_ne (by decide), hSch], fun q a b c d e => ?_⟩
    rw [hs2, Function.update_of_ne e]; exact hemp q a b c d
  obtain ⟨s3, r3, ⟨h3s, h3M, h3p, h3o⟩, h3k⟩ := hSpec ε hε1 s2 hpre
  refine ⟨s3, (CStm.Good.iteT hfE hc (r2.seq r3)).mono ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [condCost, rv, Ex.size]; nlinarith
  · rw [h3s, hs2]
    funext q
    by_cases h0 : q = q4E
    · subst h0; simp (config := { decide := true }) [hE0, Function.update_of_ne (show q4E ≠ qSzB by decide)]
    · simp (config := { decide := true }) [Function.update_of_ne h0]
  · rw [h3k rNt (by simp (config := { decide := true }) [p4Keep]), h2N, h1N, hsumC]
  · rw [h3M, r2.env_of (by decide), h1M]; simp
  · rw [h3o, h2o, h1o]
  · intro r hr hn
    rw [h3k r hr]
    simp only [p4Keep, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl hn | exact e2 _ (by decide) (by decide)

end Lax119563Proofs.Compiler

end Compiler_P4Round

/-! ### Formerly `Lax119563Proofs.Compiler.P4Main` -/

section Compiler_P4Main

/-!
# Pass `P4` (program): both rounds

`p4 SCH = r4Eps := 0; p4Round SCH; r4Eps := 1; p4Round SCH` (**`p4_good`**: output
`++ gDesc I 0 ++ gDesc I 1`), the start state from the chain (`p4Inv_of_chain`), the size
measure (`p4Z_le`) and the cost conversion for costs `K (H + S + 1) · nodeCost w`
(`cost_conv_lin`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- **Pass `P4`.** -/
def p4 (SCH : CStm CR CQ) : CStm CR CQ :=
  .seq (.set r4Eps (.const 0)) (.seq (p4Round SCH) (.seq (.set r4Eps (.const 1)) (p4Round SCH)))

lemma P4Inv_set {w : ℕ} (hw : 2 ≤ w) {st : NSt CR CQ} (hI : P4Inv I w st) {v : ℕ}
    (hv : v < 2 ^ w) : P4Inv I w (st.set r4Eps v) := by
  obtain ⟨hb, hp, a1, a2, a3, a4, a5, a6, a7, a8⟩ := hI
  refine ⟨⟨fun r => ?_, hb.2⟩, hp, ?_, ?_, ?_, ?_, ?_, a6, a7, a8⟩
  · by_cases h : r = r4Eps
    · subst h; simpa using hv
    · simpa [Function.update_of_ne h] using hb.1 r
  all_goals simp only [NSt.set_env, Function.update_of_ne (show rTriv ≠ r4Eps by decide),
    Function.update_of_ne (show rW ≠ r4Eps by decide), Function.update_of_ne (show rL ≠ r4Eps by decide),
    Function.update_of_ne (show rE ≠ r4Eps by decide), Function.update_of_ne (show rKk ≠ r4Eps by decide),
    Function.update_of_ne (show rKL ≠ r4Eps by decide), Function.update_of_ne (show rLB ≠ r4Eps by decide)]
  all_goals assumption

/-- **Pass `P4`**, given the schema edge part `SCH` (`SchSpec` with cost `C`). -/
theorem p4_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hℓ : ℓ ≤ H I)
    (hk : 1 ≤ k) (hT : (clsSizes I).sum + 8 < 2 ^ w) {SCH : CStm CR CQ} {C : ℕ}
    (hSpec : SchSpec I w SCH C) (st : NSt CR CQ) (hI : P4Inv I w st) :
    ∃ st', Good (encodeSystem I) w (p4 SCH) st st'
        (4000 * (H I + p4Z I 0 + 1) * Ex.nodeCost w + 4000 * (H I + p4Z I 1 + 1) *
          Ex.nodeCost w + 2 * C + 4 * Ex.nodeCost w) ∧
      st'.out = st.out ++ gDesc I 0 ++ gDesc I 1 ∧ P4Inv I w st' := by
  have hU := CStm.nodeCost_ge w
  have h2 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have r0 := Good.set (x := encodeSystem I) (w := w) (st := st) (r := r4Eps) (e := .const 0)
    (by simp only [Ex.Fits]; omega)
  have hI0 := P4Inv_set I hw hI (v := 0) (by omega)
  obtain ⟨s1, r1, h1o, hI1⟩ := p4Round_good I hw hH hℓ hk hT hSpec (ε := 0) (by omega) _ hI0
    (by simp (config := { decide := true }) [Ex.eval])
  have r2 := Good.set (x := encodeSystem I) (w := w) (st := s1) (r := r4Eps) (e := .const 1)
    (by simp only [Ex.Fits]; omega)
  have hI2 := P4Inv_set I hw hI1 (v := 1) h2
  obtain ⟨s3, r3, h3o, hI3⟩ := p4Round_good I hw hH hℓ hk hT hSpec (ε := 1) le_rfl _ hI2
    (by simp (config := { decide := true }) [Ex.eval])
  refine ⟨s3, (r0.seq (r1.seq (r2.seq r3))).mono ?_, ?_, hI3⟩
  · simp only [Ex.size]; omega
  · rw [h3o]; simp only [NSt.set_out]; rw [h1o]; simp (config := { decide := true }) [Ex.eval]

/-- **The start state of `P4`** from the end of the chain `P0`–`P3`. -/
lemma p4Inv_of_chain {w : ℕ} (st : NSt CR CQ) (hb : st.Bdd w) (hp : st.pos ≤ H I)
    (hL : ChainLoc I st)
    (hC : (I.schemas = [] ∧ ChainNoSch I st) ∨ (I.schemas ≠ [] ∧ ChainSch I st)) :
    P4Inv I w st := by
  obtain ⟨hTr, hW, hLl, hE, -⟩ := hL
  refine ⟨hb, hp, hTr, hW, hLl, hE, ?_, ?_, ?_, ?_⟩
  · intro hne
    rcases hC with ⟨h, -⟩ | ⟨-, hS⟩
    · exact absurd h hne
    · exact ⟨hS.2.2.2.2.2.1, hS.2.2.2.2.2.2.1, hS.2.2.2.1⟩
  · rcases hC with ⟨h, ⟨-, -, hz⟩⟩ | ⟨-, hS⟩
    · rw [hz _ (by decide)]
      have : List.finRange I.schemas.length = [] := List.eq_nil_of_length_eq_zero (by simp (config := { decide := true }) [h])
      simp (config := { decide := true }) [ansAll, this]
    · exact hS.1
  · rcases hC with ⟨h, ⟨-, -, hz⟩⟩ | ⟨-, hS⟩
    · rw [hz _ (by decide)]
      simp (config := { decide := true }) [schRecsUpTo, h]
    · exact hS.2.1
  · intro q a b c d
    rcases hC with ⟨-, ⟨-, -, hz⟩⟩ | ⟨-, hS⟩
    · exact hz q a
    · exact hS.2.2.1 q a b c d

/-! ## Sizes and the cost conversion -/

lemma length_le_sum_of_pos : ∀ l : List ℕ, (∀ v ∈ l, 1 ≤ v) → l.length ≤ l.sum
  | [], _ => le_rfl
  | a :: l, h => by
    have := length_le_sum_of_pos l (fun v hv => h v (List.mem_cons_of_mem a hv))
    have := h a (List.mem_cons_self ..)
    simp only [List.length_cons, List.sum_cons]; omega

lemma one_le_of_mem_schAll {v : ℕ} (hv : v ∈ schAll I) : 1 ≤ v := by
  simp only [schAll, List.mem_flatMap] at hv
  obtain ⟨e, -, hv⟩ := hv
  rw [schSizes_eq_szL] at hv
  simp only [szL, jlSizes, List.mem_append, List.mem_flatten, List.mem_replicate] at hv
  rcases hv with (((⟨l, ⟨-, rfl⟩, hl⟩ | ⟨-, rfl⟩) | ⟨l, ⟨-, rfl⟩, hl⟩) | ⟨-, rfl⟩) | ⟨-, rfl⟩
  all_goals first | omega | (split_ifs at hl <;> simp at hl <;> omega)

lemma one_le_of_mem_locAll {v : ℕ} (hv : v ∈ locAll I) : 1 ≤ v := by
  simp only [locAll, List.mem_flatMap, locSizes_eq_rep, List.mem_replicate] at hv
  obtain ⟨_, -, -, rfl⟩ := hv; omega

lemma length_clsSizes_le : (clsSizes I).length ≤ (ordL I).length := by
  rw [length_ordL]
  refine length_le_sum_of_pos _ fun v hv => ?_
  rw [clsSizes_eq', List.mem_append] at hv
  rcases hv with h | h
  · exact one_le_of_mem_schAll I h
  · exact one_le_of_mem_locAll I h

lemma length_schRecsUpTo_le (hk : 1 ≤ k) : (schRecsUpTo I I.schemas.length).length ≤ 4 * H I := by
  have h1 : (schRecsUpTo I I.schemas.length).length =
      ((List.finRange I.schemas.length).map fun e => (schRec I e).length).sum := by
    rw [schRecsUpTo, List.take_of_length_le (by simp), List.length_flatMap]
  have h2 : (schsDesc I).length =
      ((List.finRange I.schemas.length).map fun e => (schD I e).length).sum := by
    rw [schsDesc_eq, List.length_flatMap]
  have h3 : (schsDesc I).length ≤ H I := by
    have := length_sd_le I; rw [sd_eq] at this; simp at this; omega
  have h4 : ((List.finRange I.schemas.length).map fun e => (schRec I e).length).sum ≤
      ((List.finRange I.schemas.length).map fun e => 4 * (schD I e).length).sum := by
    refine List.sum_le_sum fun e _ => ?_
    have a := length_schemaDescription_ge I hk (sch I e)
    have b : 1 ≤ (schD I e).length := by
      rw [schD, schemaDescription_eq']; simp
    simp only [schRec, List.length_append, length_orsL, List.length_cons, List.length_nil]
    show ℓ + 3 ≤ 4 * (schemaDescription (sch I e)).length
    rw [schD] at b; omega
  rw [List.sum_map_mul_left] at h4
  omega

/-- **The size measure** of a round. -/
lemma p4Z_le (hk : 1 ≤ k) (ε : ℕ) : p4Z I ε ≤ 4 * H I + 5 * (ordL I).length := by
  have := length_schRecsUpTo_le I hk
  have := length_clsSizes_le I
  have := length_gEdges I (ε := ε)
  have := length_ordL I
  unfold p4Z; omega

/-- **Cost conversion** for costs linear in `H + S`. -/
lemma cost_conv_lin (K H S : ℕ) :
    K * (H + S + 1) * Ex.nodeCost (wordOf H S) ≤
      7744 * K * (H + S + 1) * (Nat.log 2 (H + S + 2) + 1) ^ 3 := by
  have hn := nodeCost_le_sq (a := 8) (L := Nat.log 2 (H + S + 2)) (w := wordOf H S) le_rfl
  set L := Nat.log 2 (H + S + 2)
  set N := Ex.nodeCost (wordOf H S)
  have h1 : (L + 1) ^ 2 ≤ (L + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  calc K * (H + S + 1) * N ≤ K * (H + S + 1) * (64 * (8 + 3) ^ 2 * (L + 1) ^ 2) :=
        Nat.mul_le_mul_left _ hn
    _ ≤ K * (H + S + 1) * (64 * (8 + 3) ^ 2 * (L + 1) ^ 3) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
    _ = 7744 * K * (H + S + 1) * (L + 1) ^ 3 := by ring

lemma p4_cost_arith {N h s Z0 Z1 C : ℕ} (h0 : Z0 ≤ 4 * h + 80 * s) (h1 : Z1 ≤ 4 * h + 80 * s) :
    4000 * (h + Z0 + 1) * N + 4000 * (h + Z1 + 1) * N + 2 * C + 4 * N ≤
      700000 * (h + s + 1) * N + 2 * C := by
  have a0 : (h + Z0 + 1) * N ≤ (5 * h + 80 * s + 1) * N := Nat.mul_le_mul_right _ (by omega)
  have a1 : (h + Z1 + 1) * N ≤ (5 * h + 80 * s + 1) * N := Nat.mul_le_mul_right _ (by omega)
  nlinarith

/-- **Pass `P4` after the chain** (word size `wordOf H S`): from the end state of the chain
`P0`–`P3` of a nontrivial system, `p4 SCH` appends `gDesc I 0 ++ gDesc I 1`, at cost
`700000 (H + S + 1) · nodeCost w + 2 C`. -/
theorem p4_good_chain (hk : 2 ≤ k) (ht : ¬ trivSys I) {SCH : CStm CR CQ} {C : ℕ}
    (hSpec : SchSpec I (wordOf (H I) (matrixSize I)) SCH C) (st : NSt CR CQ)
    (hb : st.Bdd (wordOf (H I) (matrixSize I))) (hp : st.pos ≤ H I) (hL : ChainLoc I st)
    (hC : (I.schemas = [] ∧ ChainNoSch I st) ∨ (I.schemas ≠ [] ∧ ChainSch I st)) :
    ∃ st', Good (encodeSystem I) (wordOf (H I) (matrixSize I)) (p4 SCH) st st'
        (700000 * (H I + matrixSize I + 1) * Ex.nodeCost (wordOf (H I) (matrixSize I)) +
          2 * C) ∧
      st'.out = st.out ++ gDesc I 0 ++ gDesc I 1 := by
  have hw := two_pow_word (H I) (matrixSize I)
  have hO := length_ordL_le I hk
  have hcl : (clsSizes I).sum = (ordL I).length := (length_ordL I).symm
  obtain ⟨st', r, ho, -⟩ := p4_good I (two_le_wordOf _ _) (by omega) (ell_le_H I (by omega) ht)
    (by omega) (by omega) hSpec st (p4Inv_of_chain I st hb hp hL hC)
  refine ⟨st', r.mono ?_, ho⟩
  have h0 := p4Z_le I (by omega) 0
  have h1 := p4Z_le I (by omega) 1
  exact p4_cost_arith (by omega) (by omega)

end Lax119563Proofs.Compiler

end Compiler_P4Main

/-! ### Formerly `Lax119563Proofs.Compiler.P4SchSpec2` -/

section Compiler_P4SchSpec2

/-!
# Pass `P4`, schema part: the schema loop and **`p4Sch_spec`**
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-! ## The schema loop -/

lemma sLp_arith {N φ h L E c : ℕ} (hφ : φ ≤ h + L) (hE : E ≤ h) (hc : c ≤ 4 * N) :
    5000 * N * φ + E * (5000 * N + c) + c ≤
      5000 * N * (h + L) + h * (5004 * N) + 4 * N := by
  have h1 : 5000 * N * φ ≤ 5000 * N * (h + L) := Nat.mul_le_mul_left _ hφ
  have h2 : E * (5000 * N + c) ≤ h * (5004 * N) := Nat.mul_le_mul hE (by omega)
  omega

set_option maxHeartbeats 4000000 in
/-- **The schema loop.** -/
lemma p4SLp_good {w : ℕ} (hw : 2 ≤ w) (ε : ZMod 2) (s0 : NSt CR CQ) (hF : BFix I w ε s0)
    (hE0 : s0.env rE = I.schemas.length) (hI0 : BInv I w ε s0 0 s0) :
    ∃ s', Good (encodeSystem I) w p4SLp s0 s'
        (5000 * Ex.nodeCost w * (H I + locBase I) + H I * (5004 * Ex.nodeCost w) +
          4 * Ex.nodeCost w) ∧
      BInv I w ε s0 I.schemas.length s' := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hEH := E_le I
  have hW16 := hF.2.2.2.1
  have hLB := locBase_le_length I
  obtain ⟨s', g, ⟨j, hI⟩, hc⟩ := Good.loop_var (x := encodeSystem I) (w := w)
    (e := .lt (rv rJ) (rv rE)) (body := p4Body) (fun s => ∃ j, BInv I w ε s0 j s)
    (fun s => I.schemas.length - s.env rJ) (fun s => (H I - s.pos) + (locBase I - s.env r4SB))
    (5000 * Ex.nodeCost w) (5000 * Ex.nodeCost w) (by
      rintro s ⟨j, hI⟩
      obtain ⟨hjE, eJ, hpos, eSB, -, -, -, -, -, -, -, -, -, -, -, -, -, hfr⟩ := id hI
      have eE : s.env rE = I.schemas.length := by rw [hfr _ (by decide), hE0]
      refine ⟨by simp only [Ex.Fits, rv, eJ, eE]; omega, fun hc => ?_⟩
      have hj : j < I.schemas.length := by
        by_contra h; apply hc; simp only [Ex.eval, rv, eJ, eE]; rw [if_neg h]
      obtain ⟨s', g, hI'⟩ := p4Body_good I hw ε s0 hF hj s hI
      obtain ⟨-, eJ', hpos', eSB', -⟩ := id hI'
      have h1 := schAt_succ I hj
      have h2 := schAt_le I (j + 1)
      have h3 := sBase_succ I hj
      have h4 := sBase_le I (j + 1)
      refine ⟨s', g.mono ?_, ⟨j + 1, hI'⟩, by rw [eJ', eJ]; omega, by
        rw [hpos', hpos, eSB', eSB]; omega⟩
      rw [hpos', hpos, eSB', eSB]
      have hd : H I - schAt I j + (locBase I - sBase I j) -
          (H I - schAt I (j + 1) + (locBase I - sBase I (j + 1))) =
          (encodeNats (schD I ⟨j, hj⟩)).length + schSize I ⟨j, hj⟩ := by omega
      rw [hd]; exact le_of_eq (by ring)) s0 ⟨0, hI0⟩
  obtain ⟨hjE, eJ, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hfr⟩ := id hI
  have eE : s'.env rE = I.schemas.length := by rw [hfr _ (by decide), hE0]
  have hjE' : j = I.schemas.length := by
    simp only [Ex.eval, rv, eJ, eE] at hc; split_ifs at hc with h <;> omega
  subst hjE'
  refine ⟨s', g.mono ?_, hI⟩
  have hc : condCost w (Ex.lt (rv rJ) (rv rE) : Ex CR) ≤ 4 * Ex.nodeCost w := by
    simp only [condCost, Ex.size, rv]; omega
  exact sLp_arith (by omega) (by omega) hc

/-! ## The answer words -/

lemma length_a1C (e : Fin I.schemas.length) (q : Coord k ℓ × ℕ) :
    (a1C I e q).length = 4 + 8 * tnN (Matrix.isTern (sch I e)) := by
  unfold a1C ans1 aU aV aW ansRec tnN
  cases Matrix.isTern (sch I e) <;> simp

lemma length_a2C (e : Fin I.schemas.length) (q : Coord k ℓ × ℕ) :
    (a2C I e q).length = 4 - 4 * tnN (Matrix.isTern (sch I e)) := by
  unfold a2C aU ansRec tnN
  cases Matrix.isTern (sch I e) <;> simp

lemma ansE_len (e : Fin I.schemas.length) :
    ((ansE I e).flatten).length = 4 * (arity (sch I e) * (coordList (dom I e)).length) := by
  rw [ansE_flatten, List.length_append, List.length_flatMap, List.length_flatMap]
  simp only [length_a1C, length_a2C, List.map_const', List.sum_replicate, List.length_zipIdx,
    smul_eq_mul]
  unfold arity tnN
  cases Matrix.isTern (sch I e) <;> simp <;> ring

lemma ansAll_len (hℓ : 1 ≤ ℓ) : (ansAll I).flatten.length ≤ 6 * H I := by
  have h1 := ansBase_le I I.schemas.length
  rw [← ansUp_all, ansUp, List.length_flatMap]
  have h2 : (((List.finRange I.schemas.length).take I.schemas.length).map
      fun e => ((ansE I e).flatten).length).sum = 4 * ansBase I I.schemas.length := by
    rw [ansBase, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro e _
    rw [ansE_len]
  rw [h2]
  have h3 : ansBase I I.schemas.length * 2 ≤ ansBase I I.schemas.length * (ℓ + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-! ## The specification -/

lemma spec_arith {N h L S a : ℕ} (hL : L ≤ 16 * S) (ha : a ≤ 6 * h) :
    1000 * (h + 1) * N + (5000 * N * (h + L) + h * (5004 * N) + 4 * N + (a + 1) * (10 * N)) ≤
      400000 * (h + S + 1) * N := by
  have h1 : N * L ≤ N * (16 * S) := Nat.mul_le_mul_left _ hL
  have h2 : a * N ≤ 6 * h * N := Nat.mul_le_mul_right _ ha
  nlinarith

lemma keep_notMem : ∀ r ∈ p4Keep, r ∉ bodyW ∧ r ∉ preW ∧ r ≠ rT ∧ r ≠ rP := by decide

set_option maxHeartbeats 8000000 in
/-- **The schema edge part of `P4` meets its interface.** -/
theorem p4Sch_spec (hk : 3 ≤ k) (hℓ : 1 ≤ ℓ) :
    SchSpec I (wordOf (H I) (matrixSize I)) p4Sch
      (400000 * (H I + matrixSize I + 1) * Ex.nodeCost (wordOf (H I) (matrixSize I))) := by
  intro ε hε st hst
  obtain ⟨hne, hbd, hpos, hEps, hM, hTriv, hW, hL, hL1, hE, hKk, hKL, hLB, hAns, hSch, hemp⟩ :=
    hst
  have hw : 2 ≤ wordOf (H I) (matrixSize I) := two_le_wordOf _ _
  have h2w := two_pow_word (H I) (matrixSize I)
  have hordL := length_ordL_le I (by omega : 2 ≤ k)
  have hLBl := locBase_le_length I
  have hW16 : 16 * (H I + (ordL I).length + 1) ≤ 2 ^ wordOf (H I) (matrixSize I) := by omega
  have hH : 4 * (H I + 1) ≤ 2 ^ wordOf (H I) (matrixSize I) := by omega
  have hz : (st.stk qSch).length ≤ 4 * H I := by
    rw [hSch, List.length_reverse]; exact length_schRecsUpTo_le I (by omega)
  obtain ⟨s0, g0, h0p, h0o, h0s, h0J, h0SB, h0PL, h0f⟩ :=
    p4SchPre_good I hw hH (by omega) hne st hbd (by omega) hW hL1 hKk hz
  have hεv : ((ε : ℕ) : ZMod 2).val = ε := val_natCast_lt (by omega)
  have hS2 : st.stk qS2 = [] := hemp _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hp0 : st.pos ≤ (encodeSystem I).length := by rw [hpos]
  have hb0 := (g0.bdd hw hbd hp0).1
  have h0o' : ∀ q, q ≠ qSch → q ≠ qS2 → s0.stk q = st.stk q := fun q h1 h2 => by
    rw [h0s, Function.update_of_ne h2, Function.update_of_ne h1]
  have hF : BFix I (wordOf (H I) (matrixSize I)) (ε : ZMod 2) s0 :=
    ⟨hne, by omega, hℓ, hW16, by rw [h0f _ (by decide), hL], by rw [h0f _ (by decide), hKk],
      by rw [h0f _ (by decide), hLB], by rw [h0f _ (by decide), hEps, hεv], h0PL,
      by rw [h0f _ (by decide), hM]⟩
  have hI0 : BInv I (wordOf (H I) (matrixSize I)) (ε : ZMod 2) s0 0 s0 := by
    refine ⟨by omega, h0J, by rw [h0p, schAt_zero], by rw [h0SB]; simp [sBase], ?_, ?_, ?_, ?_,
      by simp [edUp, pairsRev], ?_, ?_, ?_, ?_, fun _ _ => rfl,
      by rw [h0f _ (by decide), hM]; simp [edUp], rfl, hb0, fun _ _ => rfl⟩
    · rw [h0s, Function.update_self, hSch, hS2, List.reverse_reverse, List.append_nil,
        schRecsFrom_zero]
    · rw [h0s, Function.update_of_ne (by decide), Function.update_self]; simp [schRecsUpTo]
    · rw [h0o' _ (by decide) (by decide), hAns, ansFr_zero]
    · rw [h0o' _ (by decide) (by decide),
        hemp _ (by decide) (by decide) (by decide) (by decide) (by decide)]
      simp [ansUp]
    · rw [h0o' _ (by decide) (by decide),
        hemp _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [h0o' _ (by decide) (by decide),
        hemp _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [h0o' _ (by decide) (by decide),
        hemp _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [h0o' _ (by decide) (by decide),
        hemp _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  obtain ⟨s1, g1, hI1⟩ := p4SLp_good I hw (ε : ZMod 2) s0 hF (by rw [h0f _ (by decide), hE]) hI0
  obtain ⟨-, -, h1p, -, h1S2, h1Sch, h1Ans, h1A2, h14E, h1Rk, h1RkF, h1OF, h1OB, h1oth, h1M, h1o,
    hb1, h1f⟩ := hI1
  obtain ⟨s2, g2, h2s, h2p, h2o, h2f⟩ := moveAllS_good (x := encodeSystem I) hw (q := qA2)
    (q' := qAns) (t := rT) (f := rP) (by decide) (by decide) s1 hb1
  refine ⟨s2, (g0.seq (g1.seq g2)).mono ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [h1A2, List.length_reverse, ansUp_all]
    have := spec_arith (N := Ex.nodeCost (wordOf (H I) (matrixSize I))) (h := H I)
      (L := locBase I) (S := matrixSize I) (a := (ansAll I).flatten.length)
      (locBase_le I (by omega)) (ansAll_len I hℓ)
    linarith only [this]
  · rw [h2s]
    funext q
    by_cases hq1 : q = qAns
    · subst hq1
      rw [Function.update_self, Function.update_of_ne (by decide), h1A2, h1Ans, ansUp_all,
        ansFr_all, hAns]; simp
    rw [Function.update_of_ne hq1]
    by_cases hq2 : q = qA2
    · subst hq2
      rw [Function.update_self, Function.update_of_ne (by decide),
        hemp _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    rw [Function.update_of_ne hq2]
    by_cases hq3 : q = q4E
    · subst hq3
      rw [Function.update_self, h14E, edUp_all, h0o' _ (by decide) (by decide)]
    rw [Function.update_of_ne hq3]
    by_cases hq4 : q = qS2
    · subst hq4; rw [h1S2, schRecsFrom_all, hS2]
    by_cases hq5 : q = qSch
    · subst hq5; rw [h1Sch, hSch]
    by_cases hq6 : q = qRk
    · subst hq6; rw [h1Rk, hemp _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    by_cases hq7 : q = qRkF
    · subst hq7; rw [h1RkF, hemp _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    by_cases hq8 : q = qOrsF
    · subst hq8; rw [h1OF, hemp _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    by_cases hq9 : q = qOrsB
    · subst hq9; rw [h1OB, hemp _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    rw [h1oth q (by simp [bodyQ, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9]), h0o' q hq5 hq4]
  · rw [h2f _ (by decide) (by decide), h1M, edUp_all, hM, zero_add]
  · rw [h2p, h1p, schAt_all, hpos]
  · rw [h2o, h1o, h0o]
  · intro r hr
    obtain ⟨n1, n2, n3, n4⟩ := keep_notMem r hr
    rw [h2f r n3 n4, h1f r n1, h0f r n2]

end Lax119563Proofs.Compiler

end Compiler_P4SchSpec2

/-! ### Formerly `Lax119563Proofs.Compiler.Prog` -/

section Compiler_Prog

/-!
# The compiler program and the final assembly

`prog SCH = pre; if rTriv then emit 0,0,0,0 else p4 SCH`, parametric in the schema edge part
`SCH` of `P4` (interface `SchSpec`, `Compiler/P4Round`).

* **`prog_good`**: if `SCH` satisfies `SchSpec I (wordOf H S) SCH (K (H + S + 1) · nodeCost w)`
  for every system with `k ≥ 3`, `ℓ ≥ 1`, then `prog SCH` satisfies the hypotheses of
  `machine_of_program` with `a = 8`, `e = 3` and constant `7744 (2K + 910010)`;
* **`machine_clause_of_schSpec`**: the machine clause of the concept.
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix
open Lax119563.ColoredGraphs Lax119563.PebbleGame Lax119563.DeterministicTime
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Compiler

open CStm

/-- Emit a zero. -/
def emit0 : CStm CR CQ := .emit (.const 0)

/-- The output for a trivial system: `gDesc I 0 ++ gDesc I 1 = [0, 0, 0, 0]`. -/
def progTriv : CStm CR CQ := .seq emit0 (.seq emit0 (.seq emit0 emit0))

/-- **The compiler program**, given the schema edge part `SCH` of `P4`. -/
def prog (SCH : CStm CR CQ) : CStm CR CQ := .seq pre (.ite (rv rTriv) progTriv (p4 SCH))

lemma progTriv_good {x : List Bool} (w : ℕ) (st : NSt CR CQ) :
    Good x w progTriv st { st with out := st.out ++ [0, 0, 0, 0] } (8 * Ex.nodeCost w) := by
  have hU := CStm.nodeCost_ge w
  have hp : (0 : ℕ) < 2 ^ w := Nat.two_pow_pos w
  refine ⟨?_, ?_, ?_⟩
  · simp only [progTriv, emit0, CStm.Fits, Ex.Fits]; exact ⟨hp, hp, hp, hp⟩
  · simp [progTriv, emit0, CStm.exec, Ex.eval]
  · simp only [progTriv, emit0, CStm.cost, Ex.size]; omega

lemma prog_cost_arith {P N h lg Lc K A B c t : ℕ} (hP : 1 ≤ P)
    (hA : 210000 * (h + 1) * (lg + 1) * N ≤ A)
    (hB : (700010 + 2 * K) * P * N ≤ B)
    (hc : c ≤ 2 * N)
    (ht : t ≤ 700000 * P * N + 2 * (K * P * N) ∨ t ≤ 8 * N)
    (hA' : A ≤ 7744 * 210000 * P * Lc) (hB' : B ≤ 7744 * (700010 + 2 * K) * P * Lc) :
    210000 * (h + 1) * (lg + 1) * N + (c + t) ≤ 7744 * (2 * K + 910010) * P * Lc := by
  have hN : N ≤ P * N := Nat.le_mul_of_pos_left N hP
  have e1 : (700010 + 2 * K) * P * N = 700010 * (P * N) + 2 * (K * P * N) := by ring
  have e2 : 7744 * (2 * K + 910010) * P * Lc =
      7744 * 210000 * P * Lc + 7744 * (700010 + 2 * K) * P * Lc := by ring
  have : c + t ≤ B := by rcases ht with ht | ht <;> nlinarith
  omega

set_option maxHeartbeats 1000000 in
/-- **The compiler program**: the hypotheses of `machine_of_program` (`a = 8`, `e = 3`), given
a schema edge part with a uniform `SchSpec` of cost `K (H + S + 1) · nodeCost w`. -/
theorem prog_good {SCH : CStm CR CQ} {K : ℕ}
    (hSCH : ∀ k : ℕ, 3 ≤ k → ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ I : ImplicitParitySystem k ℓ,
      SchSpec I (wordOf (H I) (matrixSize I)) SCH
        (K * (H I + matrixSize I + 1) * Ex.nodeCost (wordOf (H I) (matrixSize I)))) :
    ∀ k : ℕ, 3 ≤ k → ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ I : ImplicitParitySystem k ℓ,
      let w := 8 * (Nat.log 2 (bitLength I + matrixSize I + 2) + 1)
      (prog SCH).Fits (encodeSystem I) w (NSt.zero CR CQ) ∧
      ((prog SCH).exec (encodeSystem I) (NSt.zero CR CQ)).out = gDesc I 0 ++ gDesc I 1 ∧
      (prog SCH).cost (encodeSystem I) w (NSt.zero CR CQ) ≤
        7744 * (2 * K + 910010) * (bitLength I + matrixSize I + 1) *
          (Nat.log 2 (bitLength I + matrixSize I + 2) + 1) ^ 3 := by
  intro k hk ℓ hℓ I
  show (prog SCH).Fits (encodeSystem I) (wordOf (H I) (matrixSize I)) (NSt.zero CR CQ) ∧
      ((prog SCH).exec (encodeSystem I) (NSt.zero CR CQ)).out = gDesc I 0 ++ gDesc I 1 ∧
      (prog SCH).cost (encodeSystem I) (wordOf (H I) (matrixSize I)) (NSt.zero CR CQ) ≤
        7744 * (2 * K + 910010) * (H I + matrixSize I + 1) *
          (Nat.log 2 (H I + matrixSize I + 2) + 1) ^ 3
  have hU := CStm.nodeCost_ge (wordOf (H I) (matrixSize I))
  have hA' := cost_conv 210000 (H I) (matrixSize I)
  have hB' := cost_conv_lin (700010 + 2 * K) (H I) (matrixSize I)
  have hc := condCost_rv (wordOf (H I) (matrixSize I)) rTriv
  obtain ⟨s, r, hout, hb, hp, htriv, hnt⟩ :=
    pre_good I (two_le_wordOf _ _) (by omega) (word_hS I (by omega))
  have hf : (rv rTriv : Ex CR).Fits (wordOf (H I) (matrixSize I)) s.env := hb.1 rTriv
  suffices h : ∃ s' t, Good (encodeSystem I) (wordOf (H I) (matrixSize I)) (prog SCH)
      (NSt.zero CR CQ) s' t ∧ s'.out = gDesc I 0 ++ gDesc I 1 ∧
      t ≤ 7744 * (2 * K + 910010) * (H I + matrixSize I + 1) *
          (Nat.log 2 (H I + matrixSize I + 2) + 1) ^ 3 by
    obtain ⟨s', t, ⟨hF, hE, hC⟩, ho, ht⟩ := h
    exact ⟨hF, by rw [hE, ho], hC.trans ht⟩
  by_cases ht : trivSys I
  · have e1 : s.env rTriv = 1 := (htriv ht).1
    have r' := r.seq (Good.iteT (q := p4 SCH) hf (by show s.env rTriv ≠ 0; omega)
      (progTriv_good _ s))
    refine ⟨_, _, r', ?_, prog_cost_arith (by omega) le_rfl le_rfl hc
      (Or.inr le_rfl) hA' hB'⟩
    show s.out ++ [0, 0, 0, 0] = _
    rw [hout, gDesc_triv I ht, gDesc_triv I ht]; rfl
  · obtain ⟨hL, hNo, hSch⟩ := hnt ht
    have hC : (I.schemas = [] ∧ ChainNoSch I s) ∨ (I.schemas ≠ [] ∧ ChainSch I s) := by
      by_cases hE : I.schemas = []
      · exact Or.inl ⟨hE, hNo hE⟩
      · exact Or.inr ⟨hE, hSch hE⟩
    obtain ⟨s', r4, ho⟩ := p4_good_chain I (by omega) ht (hSCH k hk ℓ hℓ I) s hb hp hL hC
    have r' := r.seq (Good.iteF (p := progTriv) hf (by show s.env rTriv = 0; exact hL.1) r4)
    refine ⟨_, _, r', by rw [ho, hout, List.nil_append], prog_cost_arith (by omega) le_rfl
      le_rfl hc (Or.inl le_rfl) hA' hB'⟩

/-- **The machine clause of the concept**, from a schema edge part with a uniform `SchSpec`. -/
theorem machine_clause_of_schSpec {SCH : CStm CR CQ} {K : ℕ}
    (hSCH : ∀ k : ℕ, 3 ≤ k → ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ I : ImplicitParitySystem k ℓ,
      SchSpec I (wordOf (H I) (matrixSize I)) SCH
        (K * (H I + matrixSize I + 1) * Ex.nodeCost (wordOf (H I) (matrixSize I)))) :
    ∃ M : Machine, Deterministic M ∧ ∃ C c : ℕ, ∀ k : ℕ, 3 ≤ k → ∀ ℓ : ℕ, 1 ≤ ℓ →
      ∀ I : ImplicitParitySystem k ℓ,
        ComputesWithin M (encodeSystem I) (encodeNats (gDesc I 0 ++ gDesc I 1))
          (C * (bitLength I + matrixSize I) *
            Nat.log 2 (bitLength I + matrixSize I + 2) ^ c) :=
  machine_of_program (prog SCH) le_rfl 8 _ 3 (by norm_num) (by norm_num) (prog_good hSCH)

end Lax119563Proofs.Compiler

end Compiler_Prog

/-! ### Formerly `Lax119563Proofs.Computability.SimDefs` -/

section Computability_SimDefs

/-!
# Simulating a machine by a structured statement: definitions

A deterministic machine `M` of `Lax489179.TuringMachine` is simulated step by step by a
structured statement (`Compiler.CStm`). Tape `j` of `M` is kept in two number stacks
`L j` (the cells left of the head, nearest first) and `R j` (the cells from the head on);
symbols are stored by their index, and popping an empty stack gives `0`, the blank. The
control state is kept in a register. A step pops the scanned symbols, looks up the
transition in a chain of conditionals over all pairs (state, scanned symbols), and applies
it; a step counter (`clk`) is incremented in every iteration.

Registers and stacks of the simulator are given by embeddings `ρ : Rg n ↪ Fin R` and
`κ : Sk n ↪ Fin Q` (`n` the number of tapes), so that the simulator can be placed into
larger statements.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler
open Lax489179.TuringMachine (Machine Config Instruction Move)

namespace Lax119563Proofs.Computability

/-- Registers of the simulator of a machine with `n` tapes. -/
inductive Rg (n : ℕ) : Type
  | inp | out | clk | st | halt | tmp | flg | pw
  | sc (j : Fin n)
  deriving DecidableEq, Fintype

/-- Stacks of the simulator of a machine with `n` tapes. -/
inductive Sk (n : ℕ) : Type
  | aux
  | L (j : Fin n)
  | R (j : Fin n)
  deriving DecidableEq, Fintype

/-! ## Expressions -/

/-- `[env r ≠ v]`. -/
def neqE {R : ℕ} (r : Fin R) (v : ℕ) : Ex R := .add (.lt (.var r) (.const v)) (.lt (.const v) (.var r))

/-- The sum of a list of expressions. -/
def sumE {R : ℕ} : List (Ex R) → Ex R
  | [] => .const 0
  | e :: es => .add e (sumE es)

/-- A list of statements in sequence. -/
def seqL {R Q : ℕ} : List (CStm R Q) → CStm R Q
  | [] => .skip
  | c :: cs => .seq c (seqL cs)

section Defs

variable {R Q : ℕ} (M : Machine)

/-- Lookup keys: a control state and the scanned symbols. -/
abbrev Key (M : Machine) := Fin (M.states + 1) × (Fin (M.tapes + 1) → Fin (M.symbols + 3))

/-- All keys. -/
noncomputable def keys : List (Key M) := (Finset.univ : Finset (Key M)).toList

variable (ρ : Rg (M.tapes + 1) ↪ Fin R) (κ : Sk (M.tapes + 1) ↪ Fin Q)

/-- The registers hold the key `p`. -/
def matchE (p : Key M) : Ex R :=
  .lt (sumE (neqE (ρ .st) p.1.val ::
    (List.finRange (M.tapes + 1)).map fun j => neqE (ρ (.sc j)) (p.2 j).val)) (.const 1)

/-- Write `a` on tape `j` and move by `m` (the scanned cell has been popped already). -/
def opT (j : Fin (M.tapes + 1)) (a : ℕ) : Move → CStm R Q
  | .stay => .push (κ (.R j)) (.const a)
  | .right => .push (κ (.L j)) (.const a)
  | .left => .seq (.pop (κ (.L j)) (ρ .tmp))
      (.seq (.push (κ (.R j)) (.const a)) (.push (κ (.R j)) (.var (ρ .tmp))))

/-- Pop the scanned symbol of tape `j`. -/
def popT (j : Fin (M.tapes + 1)) : CStm R Q := .pop (κ (.R j)) (ρ (.sc j))

/-- Push the scanned symbol of tape `j` back. -/
def pushT (j : Fin (M.tapes + 1)) : CStm R Q := .push (κ (.R j)) (.var (ρ (.sc j)))

/-- The statement for one transition. -/
def leaf (p : Key M) : CStm R Q :=
  match M.transition p.1 p.2 false with
  | .halt _ => .seq (.set (ρ .halt) (.const 1))
      (seqL ((List.finRange (M.tapes + 1)).map (pushT M ρ κ)))
  | .next q w m => .seq (.set (ρ .st) (.const q.val))
      (seqL ((List.finRange (M.tapes + 1)).map fun j => opT M ρ κ j (w j).val (m j)))

/-- The lookup chain. -/
def chain (l : List (Key M)) : CStm R Q :=
  l.foldr (fun p c => .ite (matchE M ρ p) (leaf M ρ κ p) c) .skip

/-- One iteration of the simulation loop. -/
noncomputable def body : CStm R Q :=
  .seq (seqL ((List.finRange (M.tapes + 1)).map (popT M ρ κ)))
    (.seq (chain M ρ κ (keys M)) (.set (ρ .clk) (.add (.var (ρ .clk)) (.const 1))))

/-- The loop condition: not halted. -/
def condE : Ex R := .lt (.var (ρ .halt)) (.const 1)

/-- The simulation loop, started in state `0` with the counter at `0`. -/
noncomputable def core : CStm R Q :=
  .seq (.set (ρ .halt) (.const 0)) (.seq (.set (ρ .st) (.const 0))
    (.seq (.set (ρ .clk) (.const 0)) (.loop (condE M ρ) (body M ρ κ))))

end Defs

/-! ## Evaluation of the expressions -/

section Eval

variable {R : ℕ}

lemma neqE_eval (env : Fin R → ℕ) (r : Fin R) (v : ℕ) :
    (neqE r v).eval env = if env r = v then 0 else 1 := by
  simp only [neqE, Ex.eval]
  by_cases h1 : env r < v <;> by_cases h2 : v < env r <;> by_cases h3 : env r = v <;>
    simp [h1, h2, h3] <;> omega

lemma neqE_size (r : Fin R) (v : ℕ) : (neqE r v).size = 7 := rfl

lemma sumE_eval (env : Fin R → ℕ) (es : List (Ex R)) :
    (sumE es).eval env = (es.map (Ex.eval env)).sum := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [sumE, Ex.eval, ih]

lemma sumE_size (es : List (Ex R)) : (sumE es).size = (es.map Ex.size).sum + es.length + 1 := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [sumE, Ex.size, ih]; ring

lemma sumE_fits {w : ℕ} (env : Fin R → ℕ) (es : List (Ex R)) (h0 : 0 < 2 ^ w)
    (hf : ∀ e ∈ es, e.Fits w env) (hs : (es.map (Ex.eval env)).sum < 2 ^ w) :
    (sumE es).Fits w env := by
  induction es with
  | nil => simp only [sumE, Ex.Fits]; exact h0
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons] at hs
    refine ⟨hf e (by simp), ih (fun e' he' => hf e' (by simp [he'])) (by omega), ?_⟩
    rw [sumE_eval]; exact hs

lemma neqE_le (env : Fin R → ℕ) (r : Fin R) (v : ℕ) : (neqE r v).eval env ≤ 1 := by
  rw [neqE_eval]; split_ifs <;> omega

lemma neqE_fits {w : ℕ} (env : Fin R → ℕ) (r : Fin R) (v : ℕ) (hr : env r < 2 ^ w)
    (hv : v < 2 ^ w) (h2 : 2 ≤ 2 ^ w) : (neqE r v).Fits w env := by
  have h1 := neqE_le env r v
  simp only [neqE, Ex.Fits, Ex.eval] at h1 ⊢
  exact ⟨⟨hr, hv⟩, ⟨hv, hr⟩, by omega⟩

lemma sum_map_eq_zero_iff {α : Type} (l : List α) (f : α → ℕ) :
    (l.map f).sum = 0 ↔ ∀ a ∈ l, f a = 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma sum_map_le_length {α : Type} (l : List α) (f : α → ℕ) (h : ∀ a ∈ l, f a ≤ 1) :
    (l.map f).sum ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := h a (by simp)
    have := ih (fun b hb => h b (by simp [hb]))
    omega

end Eval

section MatchEval

variable {R Q : ℕ} (M : Machine) (ρ : Rg (M.tapes + 1) ↪ Fin R)

lemma matchE_eval (env : Fin R → ℕ) (p : Key M) :
    (matchE M ρ p).eval env =
      if env (ρ .st) = p.1.val ∧ ∀ j, env (ρ (.sc j)) = (p.2 j).val then 1 else 0 := by
  simp only [matchE, Ex.eval, sumE_eval]
  have key : ((neqE (ρ .st) p.1.val :: (List.finRange (M.tapes + 1)).map fun j =>
      neqE (ρ (.sc j)) (p.2 j).val).map (Ex.eval env)).sum = 0 ↔
      env (ρ .st) = p.1.val ∧ ∀ j, env (ρ (.sc j)) = (p.2 j).val := by
    rw [sum_map_eq_zero_iff]
    simp only [List.mem_cons, List.mem_map, List.mem_finRange, true_and]
    constructor
    · intro h
      refine ⟨?_, fun j => ?_⟩
      · have := h _ (Or.inl rfl); rw [neqE_eval] at this; split_ifs at this with hh
        · exact hh
      · have := h _ (Or.inr ⟨j, rfl⟩); rw [neqE_eval] at this; split_ifs at this with hh
        · exact hh
    · rintro ⟨h1, h2⟩ e (rfl | ⟨j, rfl⟩)
      · rw [neqE_eval, if_pos h1]
      · rw [neqE_eval, if_pos (h2 j)]
  by_cases h : env (ρ .st) = p.1.val ∧ ∀ j, env (ρ (.sc j)) = (p.2 j).val
  · rw [if_pos h, if_pos (by rw [key.mpr h]; omega)]
  · rw [if_neg h, if_neg (by intro hlt; exact h (key.mp (by omega)))]

lemma matchE_size (p : Key M) : (matchE M ρ p).size = 8 * (M.tapes + 1) + 11 := by
  simp only [matchE, Ex.size, sumE_size, List.map_cons, List.map_map, List.sum_cons,
    List.length_cons, List.length_map, List.length_finRange]
  have : ((List.finRange (M.tapes + 1)).map (Ex.size ∘ fun j => neqE (ρ (.sc j)) (p.2 j).val)).sum
      = 7 * (M.tapes + 1) := by
    simp [Function.comp_def, neqE_size, List.sum_replicate, mul_comm]
  rw [this, neqE_size]; ring

/-- A bound for all small constants of the simulator. -/
def simB (M : Machine) : ℕ := M.states + M.symbols + M.tapes + 8

lemma matchE_fits {w : ℕ} (env : Fin R → ℕ) (p : Key M) (hB : simB M ≤ 2 ^ w)
    (hst : env (ρ .st) < 2 ^ w) (hsc : ∀ j, env (ρ (.sc j)) < 2 ^ w) :
    (matchE M ρ p).Fits w env := by
  have h2 : 2 ≤ 2 ^ w := by unfold simB at hB; omega
  have hp1 : p.1.val < 2 ^ w := by have := p.1.isLt; unfold simB at hB; omega
  have hp2 : ∀ j, (p.2 j).val < 2 ^ w := fun j => by
    have := (p.2 j).isLt; unfold simB at hB; omega
  have hsum : ((neqE (ρ .st) p.1.val :: (List.finRange (M.tapes + 1)).map fun j =>
      neqE (ρ (.sc j)) (p.2 j).val).map (Ex.eval env)).sum < 2 ^ w := by
    refine lt_of_le_of_lt (sum_map_le_length _ _ ?_) ?_
    · intro e he
      simp only [List.mem_cons, List.mem_map, List.mem_finRange, true_and] at he
      rcases he with rfl | ⟨j, rfl⟩ <;> exact neqE_le _ _ _
    · simp only [List.length_cons, List.length_map, List.length_finRange]
      unfold simB at hB; omega
  refine ⟨sumE_fits env _ (by omega) ?_ hsum, by simp only [Ex.Fits]; omega⟩
  intro e he
  simp only [List.mem_cons, List.mem_map, List.mem_finRange, true_and] at he
  rcases he with rfl | ⟨j, rfl⟩
  · exact neqE_fits env _ _ hst hp1 h2
  · exact neqE_fits env _ _ (hsc j) (hp2 j) h2

end MatchEval

end Lax119563Proofs.Computability

end Computability_SimDefs

/-! ### Formerly `Lax119563Proofs.Computability.SimTapes` -/

section Computability_SimTapes

/-!
# Simulating a machine: tapes as pairs of stacks

`RepT c j L R`: the stacks `L` and `R` represent tape `j` of the configuration `c` (cells left
of the head nearest first, and cells from the head on; missing entries are blank). The
effect of the per-tape statements (`popT`, `pushT`, `opT`) and of their sequences over all
tapes (`exec_seqL_tapes`, `good_seqL`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler
open Lax489179.TuringMachine (Machine Config Instruction Move)

namespace Lax119563Proofs.Computability

open CStm

/-! ## Representation of tapes -/

section Rep

variable (M : Machine)

/-- The stacks `L` and `R` represent tape `j` of `c`. -/
def RepT (c : Config M) (j : Fin (M.tapes + 1)) (L R : List ℕ) : Prop :=
  (∀ i : ℕ, (c.tape j (c.head j + i)).val = R.getD i 0) ∧
    ∀ i : ℕ, (c.tape j (c.head j - 1 - i)).val = L.getD i 0

variable {M}

lemma getD_lt_of_mem {l : List ℕ} {v B : ℕ} (hv : v ∈ l) (h : ∀ i, l.getD i 0 < B) : v < B := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  have := h i
  rwa [List.getD_eq_getElem _ _ hi] at this

lemma RepT.lt_L {c : Config M} {j : Fin (M.tapes + 1)} {L R : List ℕ} (h : RepT M c j L R)
    {v : ℕ} (hv : v ∈ L) : v < M.symbols + 3 :=
  getD_lt_of_mem hv fun i => by rw [← h.2 i]; exact Fin.isLt _

lemma RepT.headD {c : Config M} {j : Fin (M.tapes + 1)} {L R : List ℕ} (h : RepT M c j L R) :
    R.headD 0 = (c.tape j (c.head j)).val := by
  have := (h.1 0).symm
  simp only [Nat.cast_zero, add_zero] at this
  rw [← this]; cases R <;> rfl

/-- The new stacks after writing `a` and moving by `m` (the scanned cell popped from `R`). -/
def stepLR (a : ℕ) : Move → List ℕ → List ℕ → List ℕ × List ℕ
  | .stay, L, R => (L, a :: R)
  | .right, L, R => (a :: L, R)
  | .left, L, R => (L.tail, L.headD 0 :: a :: R)

lemma getD_tail (l : List ℕ) (i : ℕ) : l.tail.getD i 0 = l.getD (i + 1) 0 := by
  cases l <;> simp

lemma getD_zero_headD (l : List ℕ) : l.getD 0 0 = l.headD 0 := by
  cases l <;> simp

/-- One step on tape `j`: writing `a` and moving by `m`. -/
lemma RepT.step {c c' : Config M} {j : Fin (M.tapes + 1)} {L R : List ℕ} (h : RepT M c j L R)
    (a : Fin (M.symbols + 3)) (m : Move) (hh : c'.head j = c.head j + m.offset)
    (ht : c'.tape j = fun z => if z = c.head j then a else c.tape j z) :
    RepT M c' j (stepLR a.val m L R.tail).1 (stepLR a.val m L R.tail).2 := by
  obtain ⟨hR, hL⟩ := h
  unfold RepT
  cases m with
  | stay =>
    have hh' : c'.head j = c.head j := by simpa [Move.offset] using hh
    rw [hh', ht]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [stepLR]
      rcases i with _ | i
      · simp
      · rw [if_neg (by push_cast; omega), List.getD_cons_succ, getD_tail, ← hR]
    · simp only [stepLR]
      rw [if_neg (by omega), hL]
  | right =>
    have hh' : c'.head j = c.head j + 1 := by simpa [Move.offset] using hh
    rw [hh', ht]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [stepLR]
      rw [if_neg (by omega), getD_tail, ← hR]
      push_cast; ring_nf
    · simp only [stepLR]
      rcases i with _ | i
      · simp
      · rw [if_neg (by push_cast; omega), List.getD_cons_succ, ← hL]
        push_cast; ring_nf
  | left =>
    have hh' : c'.head j = c.head j + -1 := by simpa [Move.offset] using hh
    rw [hh', ht]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [stepLR]
      rcases i with _ | _ | i
      · rw [if_neg (by omega), List.getD_cons_zero, ← getD_zero_headD, ← hL]
        push_cast; ring_nf
      · simp
      · rw [if_neg (by push_cast; omega), List.getD_cons_succ, List.getD_cons_succ, getD_tail,
          ← hR]
        push_cast; ring_nf
    · simp only [stepLR]
      rw [if_neg (by omega), getD_tail, ← hL]
      push_cast; ring_nf

lemma getD_headD_tail (l : List ℕ) (i : ℕ) : (l.headD 0 :: l.tail).getD i 0 = l.getD i 0 := by
  cases l <;> cases i <;> simp

lemma stepLR_length (a : ℕ) (m : Move) (L R : List ℕ) :
    (stepLR a m L R).1.length ≤ L.length + 1 ∧ (stepLR a m L R).2.length ≤ R.length + 2 := by
  cases m <;> simp [stepLR] <;> omega

end Rep

/-! ## Sequences of per-tape statements -/

section Seq

variable {R Q n : ℕ} {x : List Bool} {w : ℕ}
variable (ρ : Rg n ↪ Fin R) (κ : Sk n ↪ Fin Q)

/-- The part of a state belonging to tape `j`. -/
def proj (st : NSt R Q) (j : Fin n) : List ℕ × List ℕ × ℕ :=
  (st.stk (κ (.L j)), st.stk (κ (.R j)), st.env (ρ (.sc j)))

/-- A per-tape statement with effect `E` on tape `j`. -/
def TapeOp (G : Fin n → CStm R Q) (E : Fin n → List ℕ × List ℕ × ℕ → List ℕ × List ℕ × ℕ) :
    Prop :=
  ∀ j (st : NSt R Q),
    proj ρ κ (exec x (G j) st) j = E j (proj ρ κ st j) ∧
    (∀ q, q ≠ κ (.L j) → q ≠ κ (.R j) → (exec x (G j) st).stk q = st.stk q) ∧
    (∀ r, r ≠ ρ .tmp → r ≠ ρ (.sc j) → (exec x (G j) st).env r = st.env r) ∧
    (exec x (G j) st).pos = st.pos ∧ (exec x (G j) st).out = st.out

lemma exec_seqL_cons (c : CStm R Q) (cs : List (CStm R Q)) (st : NSt R Q) :
    exec x (seqL (c :: cs)) st = exec x (seqL cs) (exec x c st) := rfl

lemma exec_seqL_tapes {G : Fin n → CStm R Q} {E : Fin n → List ℕ × List ℕ × ℕ → List ℕ × List ℕ × ℕ}
    (hG : TapeOp (x := x) ρ κ G E) :
    ∀ (l : List (Fin n)), l.Nodup → ∀ st : NSt R Q,
      (∀ j, proj ρ κ (exec x (seqL (l.map G)) st) j =
        if j ∈ l then E j (proj ρ κ st j) else proj ρ κ st j) ∧
      (∀ q, (∀ j ∈ l, q ≠ κ (.L j) ∧ q ≠ κ (.R j)) → (exec x (seqL (l.map G)) st).stk q = st.stk q) ∧
      (∀ r, r ≠ ρ .tmp → (∀ j ∈ l, r ≠ ρ (.sc j)) → (exec x (seqL (l.map G)) st).env r = st.env r) ∧
      (exec x (seqL (l.map G)) st).pos = st.pos ∧ (exec x (seqL (l.map G)) st).out = st.out
  | [], _, st => by simp [seqL, exec]
  | j₀ :: l, hnd, st => by
    have hj₀ : j₀ ∉ l := (List.nodup_cons.mp hnd).1
    obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ :=
      exec_seqL_tapes hG l (List.nodup_cons.mp hnd).2 (exec x (G j₀) st)
    obtain ⟨g1, g2, g3, g4, g5⟩ := hG j₀ st
    simp only [List.map_cons, exec_seqL_cons]
    refine ⟨fun j => ?_, fun q hq => ?_, fun r hr hr' => ?_, by rw [ih4, g4], by rw [ih5, g5]⟩
    · rw [ih1 j]
      by_cases hj : j = j₀
      · subst hj; simp [hj₀, g1]
      · have hp : proj ρ κ (exec x (G j₀) st) j = proj ρ κ st j := by
          simp only [proj]
          rw [g2 _ (by simpa using hj) (by simp), g2 _ (by simp) (by simpa using hj),
            g3 _ (by simp) (by simpa using hj)]
        by_cases hjl : j ∈ l
        · simp [hjl, hp]
        · simp [hjl, hj, hp]
    · rw [ih2 q (fun j hj => hq j (by simp [hj])), g2 q (hq j₀ (by simp)).1 (hq j₀ (by simp)).2]
    · rw [ih3 r hr (fun j hj => hr' j (by simp [hj])), g3 r hr (hr' j₀ (by simp))]

lemma good_seqL {ι : Type} {G : ι → CStm R Q} (Inv : NSt R Q → Prop) (C : ℕ)
    (hG : ∀ i st, Inv st → Good x w (G i) st (exec x (G i) st) C ∧ Inv (exec x (G i) st)) :
    ∀ (l : List ι) (st : NSt R Q), Inv st →
      Good x w (seqL (l.map G)) st (exec x (seqL (l.map G)) st) (l.length * C + unitCost w) ∧
        Inv (exec x (seqL (l.map G)) st)
  | [], st, h => ⟨(CStm.Good.skip (x := x) (w := w) (st := st)).mono (by simp), h⟩
  | i :: l, st, h => by
    obtain ⟨g, hi⟩ := hG i st h
    obtain ⟨g', hi'⟩ := good_seqL Inv C hG l _ hi
    refine ⟨(g.seq g').mono (by simp; ring_nf; omega), hi'⟩

/-! ## The per-tape statements -/

variable {M : Machine} (ρ : Rg (M.tapes + 1) ↪ Fin R) (κ : Sk (M.tapes + 1) ↪ Fin Q)

lemma popT_op : TapeOp (x := x) ρ κ (popT M ρ κ) fun _ p => (p.1, p.2.1.tail, p.2.1.headD 0) := by
  intro j st
  refine ⟨?_, fun q h1 h2 => ?_, fun r h1 h2 => ?_, rfl, rfl⟩
  · simp [proj, popT, exec, NSt.set, NSt.setS, Function.update_apply]
  · simp [popT, exec, NSt.set, NSt.setS, Function.update_apply, h2]
  · simp [popT, exec, NSt.set, NSt.setS, Function.update_apply, h2]

lemma pushT_op : TapeOp (x := x) ρ κ (pushT M ρ κ) fun _ p => (p.1, p.2.2 :: p.2.1, p.2.2) := by
  intro j st
  refine ⟨?_, fun q h1 h2 => ?_, fun r h1 h2 => ?_, rfl, rfl⟩
  · simp [proj, pushT, exec, NSt.set, NSt.setS, Function.update_apply, Ex.eval]
  · simp [pushT, exec, NSt.set, NSt.setS, Function.update_apply, h2]
  · simp [pushT, exec, NSt.set, NSt.setS, Function.update_apply]

lemma opT_op (a : Fin (M.tapes + 1) → ℕ) (m : Fin (M.tapes + 1) → Move) :
    TapeOp (x := x) ρ κ (fun j => opT M ρ κ j (a j) (m j))
      fun j p => ((stepLR (a j) (m j) p.1 p.2.1).1, (stepLR (a j) (m j) p.1 p.2.1).2, p.2.2) := by
  intro j st
  rcases hm : m j with _ | _ | _
  all_goals
    refine ⟨?_, fun q h1 h2 => ?_, fun r h1 h2 => ?_, ?_, ?_⟩
    · simp [proj, opT, hm, exec, NSt.set, NSt.setS, Function.update_apply, Ex.eval, stepLR]
    · simp [opT, hm, exec, NSt.set, NSt.setS, Function.update_apply, h1, h2]
    · simp [opT, hm, exec, NSt.set, NSt.setS, Function.update_apply, h1, h2]
    · simp [opT, hm, exec, NSt.set, NSt.setS]
    · simp [opT, hm, exec, NSt.set, NSt.setS]

end Seq

end Lax119563Proofs.Computability

end Computability_SimTapes

/-! ### Formerly `Lax119563Proofs.Computability.SimStep` -/

section Computability_SimStep

/-!
# Simulating a machine: one iteration

`Inv st c t B h`: the state `st` of the simulator represents the configuration `c` of `M`
after `t` iterations, with halting flag `h`; the tape stacks have lengths at most `t` (left)
and `B + 2 t` (right). One iteration of the loop body simulates one step of `M`
(`iter_step`), within `bodyCost M w`.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler
open Lax489179.TuringMachine (Machine Config Instruction Move)

namespace Lax119563Proofs.Computability

open CStm

variable {R Q : ℕ} {x : List Bool} {w : ℕ} {M : Machine}
variable (ρ : Rg (M.tapes + 1) ↪ Fin R) (κ : Sk (M.tapes + 1) ↪ Fin Q)

/-- The invariant of the simulation loop. -/
def Inv (st : NSt R Q) (c : Config M) (t B h : ℕ) : Prop :=
  st.env (ρ .st) = c.state.val ∧ st.env (ρ .halt) = h ∧ st.env (ρ .clk) = t ∧
    (∀ j, RepT M c j (st.stk (κ (.L j))) (st.stk (κ (.R j)))) ∧
    ∀ j, (st.stk (κ (.L j))).length ≤ t ∧ (st.stk (κ (.R j))).length ≤ B + 2 * t

variable (M) in
/-- The cost of one iteration. -/
noncomputable def bodyCost (w : ℕ) : ℕ :=
  ((keys M).length * (8 * (M.tapes + 1) + 12) + 10 * (M.tapes + 1) + 20) * Ex.nodeCost w

lemma chain_cons (p : Key M) (l : List (Key M)) :
    (chain M ρ κ (p :: l) : CStm R Q) = .ite (matchE M ρ p) (leaf M ρ κ p) (chain M ρ κ l) := rfl

lemma chain_good {l : List (Key M)} {p₀ : Key M} (hp : p₀ ∈ l) {st st' : NSt R Q} {T : ℕ}
    (hev : ∀ p, (matchE M ρ p).eval st.env = if p = p₀ then 1 else 0)
    (hf : ∀ p, (matchE M ρ p).Fits w st.env) (hl : Good x w (leaf M ρ κ p₀) st st' T) :
    Good x w (chain M ρ κ l) st st'
      (l.length * ((8 * (M.tapes + 1) + 11) * Ex.nodeCost w + 1) + T) := by
  induction l with
  | nil => simp at hp
  | cons p l ih =>
    rw [chain_cons]
    by_cases hpp : p = p₀
    · subst hpp
      refine (CStm.Good.iteT (hf p) (by rw [hev]; simp) hl).mono ?_
      simp only [condCost, matchE_size, List.length_cons]
      rw [add_one_mul]; exact Nat.add_le_add_right (Nat.le_add_left _ _) _
    · have hp' : p₀ ∈ l := by
        rcases List.mem_cons.mp hp with h | h
        · exact absurd h.symm hpp
        · exact h
      refine (CStm.Good.iteF (hf p) (by rw [hev, if_neg hpp]) (ih hp')).mono ?_
      simp only [condCost, matchE_size, List.length_cons]
      rw [add_one_mul]; linarith

lemma mem_keys (p : Key M) : p ∈ keys M := Finset.mem_toList.mpr (Finset.mem_univ _)

/-- Bounded left stacks. -/
def BndL (st : NSt R Q) : Prop := ∀ j, ∀ v ∈ st.stk (κ (.L j)), v < M.symbols + 3

lemma opT_good (hB : simB M ≤ 2 ^ w) (a : Fin (M.tapes + 1) → Fin (M.symbols + 3))
    (m : Fin (M.tapes + 1) → Move) (j : Fin (M.tapes + 1)) (st : NSt R Q) (hb : BndL κ st) :
    Good x w (opT M ρ κ j (a j).val (m j)) st (exec x (opT M ρ κ j (a j).val (m j)) st)
      (6 * Ex.nodeCost w) ∧ BndL κ (exec x (opT M ρ κ j (a j).val (m j)) st) := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have ha : (a j).val < 2 ^ w := by have := (a j).isLt; unfold simB at hB; omega
  obtain ⟨o1, o2, -⟩ := opT_op (x := x) ρ κ (fun j => (a j).val) m j st
  refine ⟨?_, fun j' v hv => ?_⟩
  · rcases hm : m j with _ | _ | _
    · simp only [opT]
      refine ((CStm.Good.pop _ _).seq ((CStm.Good.push ?_).seq (CStm.Good.push ?_))).mono ?_
      · simpa [Ex.Fits] using ha
      · simp only [Ex.Fits, NSt.setS_env, NSt.set_env, Function.update_self]
        rcases h : st.stk (κ (.L j)) with _ | ⟨v, l⟩
        · simp
        · have := hb j v (by simp [h]); simp; unfold simB at hB; omega
      · simp only [Ex.size]; omega
    · exact (CStm.Good.push (by simpa [Ex.Fits] using ha)).mono (by simp only [Ex.size]; omega)
    · exact (CStm.Good.push (by simpa [Ex.Fits] using ha)).mono (by simp only [Ex.size]; omega)
  · by_cases hj : j' = j
    · subst hj
      have h1 := congrArg Prod.fst o1
      simp only [proj] at h1
      rw [h1] at hv
      rcases hm : m j' with _ | _ | _ <;> simp only [hm, stepLR] at hv
      · exact hb j' v (List.mem_of_mem_tail hv)
      · exact hb j' v hv
      · rcases List.mem_cons.mp hv with rfl | hv
        · have := (a j').isLt; omega
        · exact hb j' v hv
    · rw [o2 _ (by simpa using hj) (by simp)] at hv
      exact hb j' v hv

lemma pushT_good (hB : simB M ≤ 2 ^ w) (j : Fin (M.tapes + 1)) (st : NSt R Q)
    (hb : ∀ j, st.env (ρ (.sc j)) < M.symbols + 3) :
    Good x w (pushT M ρ κ j) st (exec x (pushT M ρ κ j) st) (2 * Ex.nodeCost w) ∧
      ∀ j, (exec x (pushT M ρ κ j) st).env (ρ (.sc j)) < M.symbols + 3 := by
  have hU := Ex.unitCost_le_nodeCost w
  refine ⟨(CStm.Good.push ?_).mono ?_, fun j' => hb j'⟩
  · simp only [Ex.Fits]; have := hb j; unfold simB at hB; omega
  · simp only [Ex.size]; omega

lemma iter_step (hB : simB M ≤ 2 ^ w) {st : NSt R Q} {c : Config M} {t B : ℕ}
    (hI : Inv ρ κ st c t B 0) (hc : c.answer = none) (ht : t + 1 < 2 ^ w) :
    Good x w (body M ρ κ) st (exec x (body M ρ κ) st) (bodyCost M w) ∧
      Inv ρ κ (exec x (body M ρ κ) st) (Lax489179.TuringMachine.step M false c) (t + 1) B
        (if (Lax489179.TuringMachine.step M false c).answer.isSome then 1 else 0) := by
  obtain ⟨hst, hhalt, hclk, hrep, hlen⟩ := hI
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have hl : (List.finRange (M.tapes + 1)).Nodup := List.nodup_finRange _
  have hmem : ∀ j, j ∈ List.finRange (M.tapes + 1) := List.mem_finRange
  -- popping the scanned symbols
  set st1 := exec x (seqL ((List.finRange (M.tapes + 1)).map (popT M ρ κ))) st with hst1
  obtain ⟨p1, -, p3, p4, p5⟩ := exec_seqL_tapes (x := x) ρ κ (popT_op ρ κ) _ hl st
  have e1 : ∀ j, st1.stk (κ (.L j)) = st.stk (κ (.L j)) ∧
      st1.stk (κ (.R j)) = (st.stk (κ (.R j))).tail ∧
      st1.env (ρ (.sc j)) = (c.tape j (c.head j)).val := by
    intro j
    have := p1 j
    simp only [proj, hmem, if_true, Prod.mk.injEq] at this
    exact ⟨this.1, this.2.1, this.2.2.trans (hrep j).headD⟩
  have e1r : ∀ g : Rg (M.tapes + 1), (∀ j, g ≠ .sc j) → g ≠ .tmp → st1.env (ρ g) = st.env (ρ g) :=
    fun g hg ht => p3 _ (by simpa using ht) (fun j _ => by simpa using hg j)
  have g1 : Good x w (seqL ((List.finRange (M.tapes + 1)).map (popT M ρ κ))) st st1
      ((M.tapes + 1) * (unitCost w + 1) + unitCost w) := by
    have := good_seqL (x := x) (w := w) (G := popT M ρ κ) (fun _ => True) (unitCost w + 1)
      (fun j st _ => ⟨CStm.Good.pop _ _, trivial⟩) (List.finRange (M.tapes + 1)) st trivial
    simpa using this.1
  -- the key
  set p₀ : Key M := (c.state, fun j => c.tape j (c.head j)) with hp₀
  have est1 : st1.env (ρ .st) = c.state.val := by rw [e1r .st (by simp) (by simp), hst]
  have hev : ∀ p, (matchE M ρ p).eval st1.env = if p = p₀ then 1 else 0 := by
    intro p
    rw [matchE_eval]
    refine if_congr ⟨fun ⟨h1, h2⟩ => ?_, fun h => ?_⟩ rfl rfl
    · refine Prod.ext (Fin.ext (by rw [← h1, est1])) (funext fun j => Fin.ext ?_)
      rw [← h2 j, (e1 j).2.2]
    · subst h; exact ⟨est1, fun j => (e1 j).2.2⟩
  have hfits : ∀ p, (matchE M ρ p).Fits w st1.env := fun p =>
    matchE_fits M ρ _ p hB (by rw [est1]; have := c.state.isLt; unfold simB at hB; omega)
      (fun j => by rw [(e1 j).2.2]; have := (c.tape j (c.head j)).isLt; unfold simB at hB; omega)
  have hclk1 : st1.env (ρ .clk) = t := by rw [e1r .clk (by simp) (by simp), hclk]
  -- the leaf
  cases htr : M.transition c.state (fun j => c.tape j (c.head j)) false with
  | halt b =>
    have hleaf : (leaf M ρ κ p₀ : CStm R Q) = .seq (.set (ρ .halt) (.const 1))
        (seqL ((List.finRange (M.tapes + 1)).map (pushT M ρ κ))) := by
      simp only [leaf, hp₀]; rw [htr]
    set st2 := st1.set (ρ .halt) 1 with hst2
    set st3 := exec x (seqL ((List.finRange (M.tapes + 1)).map (pushT M ρ κ))) st2 with hst3
    obtain ⟨q1, -, q3, q4, q5⟩ := exec_seqL_tapes (x := x) ρ κ (pushT_op ρ κ) _ hl st2
    have hpush := good_seqL (x := x) (w := w) (G := pushT M ρ κ)
      (fun st => ∀ j, st.env (ρ (.sc j)) < M.symbols + 3) (2 * Ex.nodeCost w)
      (fun j st h => pushT_good ρ κ hB j st h) (List.finRange (M.tapes + 1)) st2
      (fun j => by
        simp only [hst2, NSt.set_env, Function.update_of_ne (by simp : ρ (.sc j) ≠ ρ .halt)]
        rw [(e1 j).2.2]; exact Fin.isLt _)
    have g2 : Good x w (leaf M ρ κ p₀) st1 st3 ((M.tapes + 3) * (2 * Ex.nodeCost w)) := by
      rw [hleaf]
      refine ((CStm.Good.set (by simp only [Ex.Fits]; omega)).seq hpush.1).mono ?_
      simp only [Ex.size, List.length_finRange]; nlinarith
    have g3 := chain_good ρ κ (mem_keys p₀) hev hfits g2
    have hclk3 : st3.env (ρ .clk) = t := by
      rw [q3 _ (by simp) (by simp)]; simp only [hst2, NSt.set_env]
      rw [Function.update_of_ne (by simp)]; exact hclk1
    have g4 : Good x w (.set (ρ .clk) (.add (.var (ρ .clk)) (.const 1))) st3
        (st3.set (ρ .clk) (t + 1)) (3 * Ex.nodeCost w + unitCost w) :=
      (CStm.Good.set (by simp only [Ex.Fits, Ex.eval, hclk3]; omega)).of_eq
        (by simp [Ex.eval, hclk3]) (by simp [Ex.size])
    have gb : Good x w (body M ρ κ) st (st3.set (ρ .clk) (t + 1)) _ := g1.seq (g3.seq g4)
    have hex : exec x (body M ρ κ) st = st3.set (ρ .clk) (t + 1) := gb.2.1
    refine ⟨?_, ?_⟩
    · rw [hex]; refine gb.mono ?_
      simp only [bodyCost]; nlinarith
    rw [hex]
    have hstep : Lax489179.TuringMachine.step M false c = { c with answer := some b } := by
      simp [Lax489179.TuringMachine.step, hc, htr]
    rw [hstep]
    refine ⟨?_, ?_, by simp, fun j => ?_, fun j => ?_⟩
    · simp only [NSt.set_env, Function.update_of_ne (by simp : ρ .st ≠ ρ .clk)]
      rw [q3 _ (by simp) (by simp)]
      simp only [hst2, NSt.set_env, Function.update_of_ne (by simp : ρ .st ≠ ρ .halt)]
      exact est1
    · simp only [NSt.set_env, Function.update_of_ne (by simp : ρ .halt ≠ ρ .clk), Option.isSome_some,
        if_true]
      rw [q3 _ (by simp) (by simp)]; simp [hst2]
    · have := q1 j
      simp only [proj, hmem, if_true, Prod.mk.injEq] at this
      simp only [NSt.set_stk]
      rw [this.1, this.2.1]
      simp only [hst2, NSt.set_stk, NSt.set_env, Function.update_of_ne (by simp : ρ (.sc j) ≠ ρ .halt)]
      rw [(e1 j).1, (e1 j).2.1, (e1 j).2.2]
      obtain ⟨r1, r2⟩ := hrep j
      refine ⟨fun i => ?_, fun i => r2 i⟩
      rw [← (hrep j).headD, getD_headD_tail]; exact r1 i
    · have := q1 j
      simp only [proj, hmem, if_true, Prod.mk.injEq] at this
      simp only [NSt.set_stk]
      rw [this.1, this.2.1]
      simp only [hst2, NSt.set_stk]
      rw [(e1 j).1, (e1 j).2.1]
      have := hlen j
      simp only [List.length_cons, List.length_tail]
      omega
  | next q' wr mv =>
    have hleaf : (leaf M ρ κ p₀ : CStm R Q) = .seq (.set (ρ .st) (.const q'.val))
        (seqL ((List.finRange (M.tapes + 1)).map fun j => opT M ρ κ j (wr j).val (mv j))) := by
      simp only [leaf, hp₀]; rw [htr]
    set st2 := st1.set (ρ .st) q'.val with hst2
    set st3 := exec x (seqL ((List.finRange (M.tapes + 1)).map
      fun j => opT M ρ κ j (wr j).val (mv j))) st2 with hst3
    obtain ⟨q1, -, q3, q4, q5⟩ := exec_seqL_tapes (x := x) ρ κ
      (opT_op ρ κ (fun j => (wr j).val) mv) _ hl st2
    have hop := good_seqL (x := x) (w := w) (G := fun j => opT M ρ κ j (wr j).val (mv j))
      (BndL κ) (6 * Ex.nodeCost w)
      (fun j st h => opT_good ρ κ hB wr mv j st h) (List.finRange (M.tapes + 1)) st2
      (fun j v hv => by
        simp only [hst2, NSt.set_stk] at hv
        rw [(e1 j).1] at hv
        exact (hrep j).lt_L hv)
    have hq' : q'.val < 2 ^ w := by have := q'.isLt; unfold simB at hB; omega
    have g2 : Good x w (leaf M ρ κ p₀) st1 st3 ((M.tapes + 3) * (6 * Ex.nodeCost w)) := by
      rw [hleaf]
      refine ((CStm.Good.set (by simp only [Ex.Fits]; omega)).seq hop.1).mono ?_
      simp only [Ex.size, List.length_finRange]; nlinarith
    have g3 := chain_good ρ κ (mem_keys p₀) hev hfits g2
    have hclk3 : st3.env (ρ .clk) = t := by
      rw [q3 _ (by simp) (by simp)]; simp only [hst2, NSt.set_env]
      rw [Function.update_of_ne (by simp)]; exact hclk1
    have g4 : Good x w (.set (ρ .clk) (.add (.var (ρ .clk)) (.const 1))) st3
        (st3.set (ρ .clk) (t + 1)) (3 * Ex.nodeCost w + unitCost w) :=
      (CStm.Good.set (by simp only [Ex.Fits, Ex.eval, hclk3]; omega)).of_eq
        (by simp [Ex.eval, hclk3]) (by simp [Ex.size])
    have gb : Good x w (body M ρ κ) st (st3.set (ρ .clk) (t + 1)) _ := g1.seq (g3.seq g4)
    have hex : exec x (body M ρ κ) st = st3.set (ρ .clk) (t + 1) := gb.2.1
    refine ⟨?_, ?_⟩
    · rw [hex]; refine gb.mono ?_
      simp only [bodyCost]; nlinarith
    rw [hex]
    have hstep : Lax489179.TuringMachine.step M false c =
        { state := q', head := fun j => c.head j + (mv j).offset,
          tape := fun j z => if z = c.head j then wr j else c.tape j z, answer := none } := by
      simp [Lax489179.TuringMachine.step, hc, htr]
    rw [hstep]
    refine ⟨?_, ?_, by simp, fun j => ?_, fun j => ?_⟩
    · simp only [NSt.set_env, Function.update_of_ne (by simp : ρ .st ≠ ρ .clk)]
      rw [q3 _ (by simp) (by simp)]
      simp [hst2]
    · simp only [NSt.set_env, Function.update_of_ne (by simp : ρ .halt ≠ ρ .clk),
        Option.isSome_none, Bool.false_eq_true, if_false]
      rw [q3 _ (by simp) (by simp)]
      simp only [hst2, NSt.set_env, Function.update_of_ne (by simp : ρ .halt ≠ ρ .st)]
      rw [e1r .halt (by simp) (by simp), hhalt]
    · have := q1 j
      simp only [proj, hmem, if_true, Prod.mk.injEq] at this
      simp only [NSt.set_stk]
      rw [this.1, this.2.1]
      simp only [hst2, NSt.set_stk]
      rw [(e1 j).1, (e1 j).2.1]
      exact (hrep j).step (wr j) (mv j) rfl rfl
    · have := q1 j
      simp only [proj, hmem, if_true, Prod.mk.injEq] at this
      simp only [NSt.set_stk]
      rw [this.1, this.2.1]
      simp only [hst2, NSt.set_stk]
      rw [(e1 j).1, (e1 j).2.1]
      have h1 := stepLR_length (wr j).val (mv j) (st.stk (κ (.L j))) (st.stk (κ (.R j))).tail
      have := hlen j
      simp only [List.length_tail] at h1
      omega

end Lax119563Proofs.Computability

end Computability_SimStep

/-! ### Formerly `Lax119563Proofs.Computability.SimLoop` -/

section Computability_SimLoop

/-!
# Simulating a machine: the loop

`haltTime M u` is the number of steps after which `M` halts on `u` (the least `t` with
`(runOn M u t).answer.isSome`, if any). Started with input `u` on the stack of tape `0`
(and the other tape stacks empty), the simulation loop `core` ends after `haltTime M u`
iterations, representing the halted configuration and with the counter `clk` at
`haltTime M u` (`core_good`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler
open Lax119563.DeterministicTime
open Lax489179.TuringMachine (Machine Config Instruction Move)

namespace Lax119563Proofs.Computability

open CStm

/-! ## Halting time -/

open Classical in
/-- The number of steps after which `M` halts on `u` (`0` if it does not halt). -/
noncomputable def haltTime (M : Machine) (u : List Bool) : ℕ :=
  if h : ∃ t, (runOn M u t).answer.isSome then Nat.find h else 0

section Halt

variable {M : Machine} {u : List Bool}

lemma haltTime_spec (h : ∃ t, (runOn M u t).answer.isSome) :
    (runOn M u (haltTime M u)).answer.isSome := by
  classical
  rw [haltTime, dif_pos h]; exact Nat.find_spec h

lemma haltTime_le {t : ℕ} (h : (runOn M u t).answer.isSome) : haltTime M u ≤ t := by
  classical
  rw [haltTime, dif_pos ⟨t, h⟩]; exact Nat.find_min' _ h

lemma haltTime_min (h : ∃ t, (runOn M u t).answer.isSome) {t : ℕ} (ht : t < haltTime M u) :
    (runOn M u t).answer = none := by
  classical
  rw [haltTime, dif_pos h] at ht
  have := Nat.find_min h ht
  simpa using this

/-- A machine computing `y` from `u` does so within `haltTime M u` steps. -/
lemma ComputesWithin.haltTime {y : List Bool} {t : ℕ} (h : ComputesWithin M u y t) :
    ComputesWithin M u y (haltTime M u) ∧ haltTime M u ≤ t := by
  have hle := haltTime_le h.1
  have e := Main.runOn_eq_of_le M u hle (haltTime_spec ⟨t, h.1⟩)
  refine ⟨?_, hle⟩
  unfold ComputesWithin HaltsWithin at h ⊢
  rw [← e]; exact h

end Halt

/-! ## The loop -/

/-- The stack symbol of an input bit. -/
def symOf (b : Bool) : ℕ := if b then 2 else 1

variable {R Q : ℕ} {x : List Bool} {w : ℕ} {M : Machine}
variable (ρ : Rg (M.tapes + 1) ↪ Fin R) (κ : Sk (M.tapes + 1) ↪ Fin Q)

variable (M) in
/-- The cost of the simulation loop for `s` steps. -/
noncomputable def coreCost (w s : ℕ) : ℕ := (s + 1) * (bodyCost M w + 10 * Ex.nodeCost w)

lemma repT_init (u : List Bool) (j : Fin (M.tapes + 1)) :
    RepT M (Lax489179.TuringMachine.init M u) j [] (if j = 0 then u.map symOf else []) := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · by_cases hj : j = 0
    · subst hj
      simp only [Lax489179.TuringMachine.init, zero_add, if_true]
      rw [if_pos ⟨trivial, by positivity⟩]
      simp only [Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_map]
      rcases u[i]? with _ | _ | _ <;> simp [symOf]
    · simp [Lax489179.TuringMachine.init, hj]
  · simp only [Lax489179.TuringMachine.init]
    rw [if_neg (by omega)]; simp

theorem core_good (hB : simB M ≤ 2 ^ w) (u : List Bool) (st : NSt R Q)
    (hL : ∀ j, st.stk (κ (.L j)) = [])
    (hR : ∀ j, st.stk (κ (.R j)) = if j = 0 then u.map symOf else [])
    (hh : ∃ t, (runOn M u t).answer.isSome) (hs : haltTime M u < 2 ^ w) :
    Good x w (core M ρ κ) st (exec x (core M ρ κ) st) (coreCost M w (haltTime M u)) ∧
      Inv ρ κ (exec x (core M ρ κ) st) (runOn M u (haltTime M u)) (haltTime M u) u.length 1 := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h2 : 2 ≤ 2 ^ w := by unfold simB at hB; omega
  set s := haltTime M u with hsdef
  set S0 := ((st.set (ρ .halt) 0).set (ρ .st) 0).set (ρ .clk) 0 with hS0
  have I0 : Inv ρ κ S0 (Lax489179.TuringMachine.init M u) 0 u.length 0 := by
    refine ⟨by simp [hS0, Lax489179.TuringMachine.init], by simp [hS0], by simp [hS0],
      fun j => ?_, fun j => ?_⟩
    · simp only [hS0, NSt.set_stk, hL, hR]; exact repT_init u j
    · simp only [hS0, NSt.set_stk, hL, hR]; split_ifs <;> simp
  set S : ℕ → NSt R Q := fun j => iter x (body M ρ κ) S0 j with hS
  have hsucc : ∀ j, S (j + 1) = exec x (body M ρ κ) (S j) := fun j => iter_succ _ _ _
  have hI : ∀ j ≤ s, Inv ρ κ (S j) (runOn M u j) j u.length (if j = s then 1 else 0) ∧
      (j < s → Good x w (body M ρ κ) (S j) (S (j + 1)) (bodyCost M w)) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hs0 : s ≠ 0 := by
        intro h0
        have := haltTime_spec hh
        rw [← hsdef, h0] at this
        simp [runOn, Lax489179.TuringMachine.run, Lax489179.TuringMachine.init] at this
      have e0 : (if (0 : ℕ) = s then 1 else 0) = 0 := if_neg (Ne.symm hs0)
      rw [e0]
      refine ⟨I0, fun _ => ?_⟩
      have := iter_step ρ κ (x := x) hB I0
        (by simp [Lax489179.TuringMachine.init]) (by omega)
      rw [hsucc]; exact this.1
    | succ j ih =>
      intro hj
      obtain ⟨Ij, -⟩ := ih (by omega)
      have hjs : j ≠ s := by omega
      rw [if_neg hjs] at Ij
      have hc := haltTime_min hh (show j < s by omega)
      have := iter_step ρ κ (x := x) hB Ij hc (by omega)
      rw [← Main.runOn_succ] at this
      have hans : (if (runOn M u (j + 1)).answer.isSome then 1 else 0) =
          (if j + 1 = s then 1 else 0) := by
        by_cases hjs' : j + 1 = s
        · rw [if_pos hjs', if_pos (by rw [hjs']; exact haltTime_spec hh)]
        · rw [if_neg hjs', haltTime_min hh (show j + 1 < s by omega)]; rfl
      rw [hans, ← hsucc] at this
      refine ⟨this.2, fun hj' => ?_⟩
      have := iter_step ρ κ (x := x) hB (by simpa [show j + 1 ≠ s by omega] using this.2)
        (haltTime_min hh hj') (by omega)
      rw [hsucc (j + 1)]; exact this.1
  have hloop := CStm.Good.loop (x := x) (w := w) (e := condE M ρ) (body := body M ρ κ) s S
    (fun _ => bodyCost M w)
    (fun j hj => by
      have := (hI j hj.le).1.2.1
      rw [if_neg (by omega)] at this
      simp [condE, Ex.eval, this])
    (by
      have := (hI s le_rfl).1.2.1
      rw [if_pos rfl] at this
      simp [condE, Ex.eval, this])
    (fun j hj => by
      have := (hI j hj).1.2.1
      simp only [condE, Ex.Fits, this]
      split_ifs <;> omega)
    (fun j hj => (hI j hj.le).2 hj)
  have gc : Good x w (core M ρ κ) st (S s) _ :=
    (CStm.Good.set (by simp [Ex.Fits])).seq ((CStm.Good.set (by simp [Ex.Fits])).seq
      ((CStm.Good.set (by simp [Ex.Fits])).seq hloop))
  refine ⟨?_, ?_⟩
  · rw [gc.2.1]
    refine gc.mono ?_
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, condCost, condE, Ex.size,
      coreCost]
    nlinarith
  · rw [gc.2.1]
    simpa using (hI s le_rfl).1

end Lax119563Proofs.Computability

end Computability_SimLoop

/-! ### Formerly `Lax119563Proofs.Computability.StackParse` -/

section Computability_StackParse

/-!
# Reading a number from a stack, writing a number onto a stack, clearing stacks

Stack routines used to load the input of a simulated machine and to read off its output:
* `skipZ q t`: pop until a nonzero entry (in `t`);
* `parseB q t o p`: having popped the first symbol of `encodeNat v` (stored with `symOf`),
  read `v` into `o` (`parseB_good`);
* `pushCode q t`: push the symbols of `encodeNat (t)` onto `q`, reversed (`pushCode_good`);
* `clrS q t f`: empty the stack `q` (`clrS_good`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler

namespace Lax119563Proofs.Computability

open CStm

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

/-! ## Lists -/

lemma eq_append_drop_of_getD {l m : List ℕ} (h : ∀ i, l.getD i 0 = m.getD i 0)
    (hm : m ≠ []) (hlast : m.getD (m.length - 1) 0 ≠ 0) : l = m ++ l.drop m.length := by
  have hlen : m.length ≤ l.length := by
    by_contra hc
    have := h (m.length - 1)
    rw [List.getD_eq_default _ _ (by omega)] at this
    exact hlast this.symm
  have ht : l.take m.length = m := by
    refine List.ext_getElem (by simp [hlen]) fun i h1 h2 => ?_
    have := h i
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ h2] at this
    simpa using this
  conv_lhs => rw [← List.take_append_drop m.length l, ht]

lemma headD_drop (l : List ℕ) (n : ℕ) : (l.drop n).headD 0 = l.getD n 0 := by
  induction l generalizing n with
  | nil => simp
  | cons a l ih => cases n <;> simp [ih]

lemma bits_eq_cons {k : ℕ} (hk : k ≠ 0) : k.bits = decide (k % 2 = 1) :: (k / 2).bits := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [Nat.bit0_bits n (by omega)]; congr 1
    · simp
    · congr 1; omega
  · rw [Nat.bit1_bits]; congr 1
    · simp [Nat.add_mod]
    · congr 1; omega

lemma bits_drop (k j : ℕ) : k.bits.drop j = (k / 2 ^ j).bits := by
  induction j generalizing k with
  | zero => simp
  | succ j ih =>
    rw [← List.drop_drop, ih]
    rcases Nat.eq_zero_or_pos (k / 2 ^ j) with h | h
    · rw [h, Nat.zero_bits]; simp [pow_succ, ← Nat.div_div_eq_div_mul, h]
    · rw [bits_eq_cons h.ne']
      simp [pow_succ, Nat.div_div_eq_div_mul]

/-- The stack symbols of a list of bits. -/
def syms (l : List Bool) : List ℕ := l.map symOf

lemma symOf_pos (b : Bool) : 0 < symOf b := by cases b <;> simp [symOf]
lemma symOf_le (b : Bool) : symOf b ≤ 2 := by cases b <;> simp [symOf]

/-! ## Skipping zeros -/

/-- `[1 < t]`. -/
def isT (t : Fin R) : Ex R := .lt (.const 1) (.var t)

/-- Pop until a nonzero entry, which is left in `t`. -/
def skipZ (q : Fin Q) (t : Fin R) : CStm R Q :=
  .seq (.pop q t) (.loop (.lt (.var t) (.const 1)) (.pop q t))

lemma skipZ_good (hw : 2 ≤ w) {q : Fin Q} {t : Fin R} (st : NSt R Q) (d a : ℕ)
    (rest : List ℕ) (ha : a ≠ 0) (haw : a < 2 ^ w)
    (hq : st.stk q = List.replicate d 0 ++ a :: rest) :
    Good x w (skipZ q t) st (exec x (skipZ q t) st) ((d + 2) * (6 * Ex.nodeCost w)) ∧
      (exec x (skipZ q t) st).stk q = rest ∧ (exec x (skipZ q t) st).env t = a := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h1 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  set l := List.replicate d 0 ++ a :: rest with hl
  set st1 := exec x (.pop q t : CStm R Q) st with hst1
  set S : ℕ → NSt R Q := fun j => iter x (.pop q t) st1 j with hS
  have hSj : ∀ j ≤ d, (S j).stk q = l.drop (j + 1) ∧ (S j).env t = l.getD j 0 := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨?_, ?_⟩ <;> simp only [S, iter_zero, hst1, exec, NSt.set_stk, NSt.setS_stk,
        Function.update_self, NSt.set_env, hq]
      · simp
      · rw [← headD_drop, List.drop_zero]
    | succ j ih =>
      intro hj
      obtain ⟨i1, i2⟩ := ih (by omega)
      rw [show S (j + 1) = exec x (.pop q t) (S j) from iter_succ _ _ _]
      simp only [exec, NSt.set_stk, NSt.setS_stk, Function.update_self, NSt.set_env,
        Function.update_self, i1]
      refine ⟨by simp, ?_⟩
      rw [headD_drop]
  have hval : ∀ j, j < d → l.getD j 0 = 0 := fun j hj => by
    rw [hl, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hj),
      List.getElem?_replicate]
    simp [hj]
  have hd : l.getD d 0 = a := by
    rw [hl, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp
  have hloop := CStm.Good.loop_const (x := x) (w := w) (e := .lt (.var t) (.const 1)) (body := .pop q t)
    d S (unitCost w + 1)
    (fun j hj => by
      rw [show (Ex.lt (.var t) (.const 1) : Ex R).eval (S j).env =
        if (S j).env t < 1 then 1 else 0 from rfl, (hSj j hj.le).2, hval j hj]; simp)
    (by
      rw [show (Ex.lt (.var t) (.const 1) : Ex R).eval (S d).env =
        if (S d).env t < 1 then 1 else 0 from rfl, (hSj d le_rfl).2, hd, if_neg (by omega)])
    (fun j hj => by
      simp only [Ex.Fits, (hSj j hj).2]
      refine ⟨?_, h1⟩
      rcases Nat.lt_or_ge j d with h | h
      · rw [hval j h]; omega
      · rw [show j = d by omega, hd]; exact haw)
    (fun j _ => by rw [show S (j + 1) = exec x (.pop q t) (S j) from iter_succ _ _ _];
                   exact CStm.Good.pop _ _)
  have g : Good x w (skipZ q t) st (S d) _ := (CStm.Good.pop q t).seq hloop
  rw [g.2.1]
  refine ⟨g.mono ?_, ?_, by rw [(hSj d le_rfl).2, hd]⟩
  · have : d * (unitCost w + 1 + (3 * Ex.nodeCost w + 1)) ≤ d * (6 * Ex.nodeCost w) :=
      Nat.mul_le_mul_left _ (by omega)
    simp only [condCost, Ex.size]; nlinarith
  · rw [(hSj d le_rfl).1, hl]
    clear hSj hval hd hloop g hS hl hq
    induction d with
    | zero => rfl
    | succ d ih => simpa [List.replicate_succ] using ih

/-! ## Parsing -/

/-- Read the digits of a number whose first symbol is in `t` (value into `o`, power of two
in `p`). -/
def parseB (q : Fin Q) (t o p : Fin R) : CStm R Q :=
  .loop (isT t) (seqL [.pop q t, .ite (isT t) (.set o (.add (.var o) (.var p))) .skip,
    .set p (.add (.var p) (.var p)), .pop q t])

lemma isT_eval (env : Fin R → ℕ) (t : Fin R) : (isT t).eval env = if 1 < env t then 1 else 0 := rfl

lemma isT_fits (hw : 2 ≤ w) {env : Fin R → ℕ} {t : Fin R} (h : env t ≤ 2) : (isT t).Fits w env := by
  have h4 : (4 : ℕ) ≤ 2 ^ w := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  simp only [isT, Ex.Fits]; omega

lemma syms_pairs_drop (ds : List Bool) {j : ℕ} (hj : j < ds.length) :
    syms (pairs (ds.drop j) ++ [false]) =
      2 :: symOf ds[j] :: syms (pairs (ds.drop (j + 1)) ++ [false]) := by
  rw [List.drop_eq_getElem_cons hj]
  simp only [syms, pairs_cons, List.map_cons, List.cons_append]
  rfl

lemma syms_head (ds : List Bool) (j : ℕ) :
    (syms (pairs (ds.drop j) ++ [false])).headD 0 = if j < ds.length then 2 else 1 := by
  by_cases hj : j < ds.length
  · rw [syms_pairs_drop ds hj, if_pos hj]; rfl
  · rw [List.drop_eq_nil_of_le (by omega), if_neg hj]; rfl

lemma parse_iter (hw : 2 ≤ w) {q : Fin Q} {t o p : Fin R} (hto : t ≠ o) (htp : t ≠ p)
    (hop : o ≠ p) (S : NSt R Q) (ds : List Bool) (rest : List ℕ) (hL : ds.length < w)
    (j : ℕ) (hj : j < ds.length)
    (h1 : S.stk q = (syms (pairs (ds.drop j) ++ [false])).tail ++ rest)
    (h3 : S.env o = Machines.valBits (ds.take j)) (h4 : S.env p = 2 ^ j) :
    let B : CStm R Q := seqL [.pop q t, .ite (isT t) (.set o (.add (.var o) (.var p))) .skip,
      .set p (.add (.var p) (.var p)), .pop q t]
    Good x w B S (exec x B S) (16 * Ex.nodeCost w) ∧
      (exec x B S).stk q = (syms (pairs (ds.drop (j + 1)) ++ [false])).tail ++ rest ∧
      (exec x B S).env t = (if j + 1 < ds.length then 2 else 1) ∧
      (exec x B S).env o = Machines.valBits (ds.take (j + 1)) ∧
      (exec x B S).env p = 2 ^ (j + 1) := by
  intro B
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have hpj : 2 ^ (j + 1) < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hpj' : 2 ^ j < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hvl : Machines.valBits (ds.take j) < 2 ^ j := by
    have := valBits_lt (ds.take j); rwa [List.length_take, min_eq_left hj.le] at this
  have hvt := valBits_take_succ ds hj
  set rest1 := syms (pairs (ds.drop (j + 1)) ++ [false]) with hr1
  have hne : rest1 ≠ [] := by simp [hr1, syms]
  have hq1 : S.stk q = symOf ds[j] :: (rest1 ++ rest) := by
    rw [h1, syms_pairs_drop ds hj]; rfl
  -- after the first pop
  set S1 : NSt R Q := (S.setS q (rest1 ++ rest)).set t (symOf ds[j]) with hS1
  have g1 : Good x w (.pop q t : CStm R Q) S S1 (unitCost w + 1) :=
    (CStm.Good.pop q t).of_eq (by rw [hq1]; rfl) le_rfl
  have hS1o : S1.env o = Machines.valBits (ds.take j) := by
    simp [hS1, Function.update_of_ne hto.symm, h3]
  have hS1p : S1.env p = 2 ^ j := by simp [hS1, Function.update_of_ne htp.symm, h4]
  have hS1t : S1.env t = symOf ds[j] := by simp [hS1]
  -- the conditional
  set S2 : NSt R Q := if ds[j] then S1.set o (Machines.valBits (ds.take j) + 2 ^ j) else S1
    with hS2
  have g2 : Good x w (.ite (isT t) (.set o (.add (.var o) (.var p))) .skip : CStm R Q) S1 S2
      (8 * Ex.nodeCost w) := by
    have hf : (isT t).Fits w S1.env := isT_fits hw (by rw [hS1t]; exact symOf_le _)
    cases hd : ds[j]
    · refine (CStm.Good.iteF hf (by rw [isT_eval, hS1t, hd]; simp [symOf]) CStm.Good.skip).of_eq
        (by simp [hS2, hd]) ?_
      simp only [condCost, isT, Ex.size]; omega
    · refine (CStm.Good.iteT hf (by rw [isT_eval, hS1t, hd]; simp [symOf]) (CStm.Good.set ?_)).of_eq
        (by simp [hS2, hd, Ex.eval, hS1o, hS1p]) ?_
      · simp only [Ex.Fits, Ex.eval, hS1o, hS1p]; refine ⟨by omega, hpj', ?_⟩
        rw [pow_succ] at hpj; omega
      · simp only [condCost, isT, Ex.size]; omega
  have hS2p : S2.env p = 2 ^ j := by
    by_cases hd : ds[j] <;> simp [hS2, hd, Function.update_of_ne hop.symm, hS1p]
  have hS2o : S2.env o = Machines.valBits (ds.take (j + 1)) := by
    rw [hvt]; by_cases hd : ds[j] <;> simp [hS2, hd, hS1o]
  have hS2q : S2.stk q = rest1 ++ rest := by by_cases hd : ds[j] <;> simp [hS2, hd, hS1]
  -- doubling
  have g3 : Good x w (.set p (.add (.var p) (.var p)) : CStm R Q) S2 (S2.set p (2 ^ (j + 1)))
      (3 * Ex.nodeCost w + unitCost w) := by
    refine (CStm.Good.set ?_).of_eq (by simp [Ex.eval, hS2p, pow_succ, mul_two]) (by simp [Ex.size])
    simp only [Ex.Fits, Ex.eval, hS2p]
    refine ⟨hpj', hpj', ?_⟩; rw [pow_succ] at hpj; omega
  -- the second pop
  have g4 := CStm.Good.pop (x := x) (w := w) (st := S2.set p (2 ^ (j + 1))) q t
  have g := g1.seq (g2.seq (g3.seq (g4.seq (CStm.Good.skip (x := x) (w := w)))))
  have hex : exec x B S = _ := g.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hex]; exact g.mono (by omega)
  all_goals rw [hex]
  · simp only [NSt.set_stk, NSt.setS_stk, Function.update_self, hS2q]
    obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil hne
    rw [hl]; rfl
  · simp only [NSt.set_env, Function.update_self, NSt.setS_stk, NSt.set_stk, hS2q]
    rw [← syms_head ds (j + 1), ← hr1]
    obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil hne
    rw [hl]; rfl
  · simp [Function.update_of_ne hto.symm, Function.update_of_ne hop, hS2o]
  · simp [Function.update_of_ne htp.symm]

lemma parseB_good (hw : 2 ≤ w) {q : Fin Q} {t o p : Fin R} (hto : t ≠ o) (htp : t ≠ p)
    (hop : o ≠ p) (st : NSt R Q) (ds : List Bool) (rest : List ℕ) (hL : ds.length < w)
    (hq : st.stk q = (syms (pairs ds ++ [false])).tail ++ rest)
    (ht : st.env t = if 0 < ds.length then 2 else 1) (ho : st.env o = 0) (hp : st.env p = 1) :
    Good x w (parseB q t o p) st (exec x (parseB q t o p) st)
        ((ds.length + 1) * (20 * Ex.nodeCost w)) ∧
      (exec x (parseB q t o p) st).env o = Machines.valBits ds ∧
      (exec x (parseB q t o p) st).stk q = rest := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have hpow : ∀ j ≤ ds.length, 2 ^ j < 2 ^ w := fun j hj =>
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  set B : CStm R Q := seqL [.pop q t, .ite (isT t) (.set o (.add (.var o) (.var p))) .skip,
    .set p (.add (.var p) (.var p)), .pop q t] with hB
  set S : ℕ → NSt R Q := fun j => iter x B st j with hS
  have hSj : ∀ j ≤ ds.length,
      (S j).stk q = (syms (pairs (ds.drop j) ++ [false])).tail ++ rest ∧
      (S j).env t = (if j < ds.length then 2 else 1) ∧
      (S j).env o = Machines.valBits (ds.take j) ∧ (S j).env p = 2 ^ j := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [hS, iter_zero, List.drop_zero, List.take_zero]
      exact ⟨hq, ht, by rw [ho]; rfl, by rw [hp]; rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨i1, -, i3, i4⟩ := ih (by omega)
      have := parse_iter (x := x) hw hto htp hop (S j) ds rest hL j (by omega) i1 i3 i4
      rw [show S (j + 1) = exec x B (S j) from iter_succ _ _ _]
      exact ⟨this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2⟩
  have hloop := CStm.Good.loop_const (x := x) (w := w) (e := isT t) (body := B) ds.length S
    (16 * Ex.nodeCost w)
    (fun j hj => by rw [isT_eval, (hSj j hj.le).2.1, if_pos hj]; simp)
    (by rw [isT_eval, (hSj _ le_rfl).2.1, if_neg (lt_irrefl _)]; simp)
    (fun j hj => isT_fits hw (by rw [(hSj j hj).2.1]; split_ifs <;> omega))
    (fun j hj => by
      obtain ⟨i1, -, i3, i4⟩ := hSj j hj.le
      have := parse_iter (x := x) hw hto htp hop (S j) ds rest hL j hj i1 i3 i4
      rw [show S (j + 1) = exec x B (S j) from iter_succ _ _ _]
      exact this.1)
  have hex : exec x (parseB q t o p) st = S ds.length := hloop.2.1
  refine ⟨?_, ?_, ?_⟩
  · rw [hex]; refine hloop.mono ?_
    simp only [condCost, isT, Ex.size]
    nlinarith
  · rw [hex, (hSj _ le_rfl).2.2.1, List.take_length]
  · rw [hex, (hSj _ le_rfl).1, List.drop_length]; rfl

end Lax119563Proofs.Computability

end Computability_StackParse

/-! ### Formerly `Lax119563Proofs.Computability.StackLoad` -/

section Computability_StackLoad

/-!
# Loading stacks and clearing them

* `pushBits q t`: push the symbols of `pairs (Nat.bits k)` onto `q` (reversed), where `k` is
  the value of `t` (`pushBits_good`);
* `readIn q t`: push the symbols of the remaining input onto `q` (reversed; `readIn_good`);
* `clrS q t f`: empty the stack `q` (`clrS_good`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler

namespace Lax119563Proofs.Computability

open CStm

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

lemma syms_pairs_take_succ (l : List Bool) (j : ℕ) (hj : j < l.length) :
    (syms (pairs (l.take (j + 1)))).reverse = symOf l[j] :: 2 :: (syms (pairs (l.take j))).reverse := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj]
  simp only [Option.toList_some, pairs_append, pairs_cons, pairs_nil, syms, List.map_append,
    List.reverse_append, List.map_cons, List.map_nil]
  rfl

lemma syms_take_succ (l : List Bool) (j : ℕ) (hj : j < l.length) :
    (syms (l.take (j + 1))).reverse = symOf l[j] :: (syms (l.take j)).reverse := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj]
  simp only [syms, List.map_append, List.reverse_append, Option.toList_some, List.map_cons,
    List.map_nil]
  rfl

/-! ## Pushing the digits of a number -/

/-- Push `2, symOf d` for the digits `d` of the value of `t` (least significant first). -/
def pushBits (q : Fin Q) (t : Fin R) : CStm R Q :=
  .loop (.var t) (seqL [.push q (.const 2), .push q (.add (.odd (.var t)) (.const 1)),
    .set t (.half (.var t))])

lemma symOf_decide (m : ℕ) : symOf (decide (m % 2 = 1)) = m % 2 + 1 := by
  rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [symOf, h]

lemma pushBits_good (hw : 2 ≤ w) {q : Fin Q} {t : Fin R} (st : NSt R Q) (k : ℕ)
    (ht : st.env t = k) (hk : k < 2 ^ w) :
    Good x w (pushBits q t) st (exec x (pushBits q t) st)
        ((k.bits.length + 1) * (14 * Ex.nodeCost w)) ∧
      (exec x (pushBits q t) st).stk q = (syms (pairs k.bits)).reverse ++ st.stk q ∧
      (exec x (pushBits q t) st).env t = 0 ∧
      ∀ r, r ≠ t → (exec x (pushBits q t) st).env r = st.env r := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  set B : CStm R Q := seqL [.push q (.const 2), .push q (.add (.odd (.var t)) (.const 1)),
    .set t (.half (.var t))] with hB
  set S : ℕ → NSt R Q := fun j => iter x B st j with hS
  set n := k.bits.length
  have hnz : ∀ j < n, k / 2 ^ j ≠ 0 := fun j hj h => by
    have := bits_drop k j
    rw [h, Nat.zero_bits, List.drop_eq_nil_iff] at this; omega
  have hbit : ∀ j (hj : j < n), symOf (k.bits[j]) = k / 2 ^ j % 2 + 1 := fun j hj => by
    have e := bits_drop k j
    rw [List.drop_eq_getElem_cons hj, bits_eq_cons (hnz j hj)] at e
    rw [(List.cons.inj e).1, symOf_decide]
  have hstep : ∀ (S' : NSt R Q) j (hj : j < n), S'.env t = k / 2 ^ j →
      Good x w B S' (exec x B S') (12 * Ex.nodeCost w) ∧
        (exec x B S').env t = k / 2 ^ (j + 1) ∧
        (exec x B S').stk q = symOf (k.bits[j]'hj) :: 2 :: S'.stk q ∧
        ∀ r, r ≠ t → (exec x B S').env r = S'.env r := by
    intro S' j hj hS'
    have hkj : k / 2 ^ j ≤ k := Nat.div_le_self _ _
    have g := (CStm.Good.push (x := x) (w := w) (st := S') (q := q) (e := .const 2)
      (show (2 : ℕ) < 2 ^ w by omega)).seq ((CStm.Good.push (q := q) (e := .add (.odd (.var t)) (.const 1))
        (by simp only [Ex.Fits, NSt.setS_env, Ex.eval, hS']; refine ⟨by omega, by omega, ?_⟩
            have := Nat.mod_lt (k / 2 ^ j) (show 2 > 0 by norm_num); omega)).seq
        ((CStm.Good.set (r := t) (e := .half (.var t)) (by simp [Ex.Fits, hS']; omega)).seq CStm.Good.skip))
    have hex : exec x B S' = _ := g.2.1
    refine ⟨?_, ?_, ?_, fun r hr => ?_⟩
    · rw [hex]; refine g.mono ?_; simp only [Ex.size]; omega
    · rw [hex]; simp [Ex.eval, hS', pow_succ, Nat.div_div_eq_div_mul]
    · rw [hex]; simp [Ex.eval, hS', hbit j hj]
    · rw [hex]; simp [Function.update_of_ne hr]
  have hSj : ∀ j ≤ n, (S j).env t = k / 2 ^ j ∧
      (S j).stk q = (syms (pairs (k.bits.take j))).reverse ++ st.stk q ∧
      ∀ r, r ≠ t → (S j).env r = st.env r := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨by simp [hS, iter_zero, ht], by simp [hS, iter_zero, syms], fun r _ => by
        simp [hS, iter_zero]⟩
    | succ j ih =>
      intro hj
      obtain ⟨i1, i2, i3⟩ := ih (by omega)
      obtain ⟨-, e1, e2, e3⟩ := hstep (S j) j (by omega) i1
      rw [show S (j + 1) = exec x B (S j) from iter_succ _ _ _]
      refine ⟨e1, ?_, fun r hr => by rw [e3 r hr, i3 r hr]⟩
      rw [e2, i2, syms_pairs_take_succ _ _ (by omega)]; rfl
  have hn : k / 2 ^ n = 0 := by
    have := bits_drop k n
    rw [List.drop_length] at this
    exact (Machines.bits_eq_nil_iff _).mp this.symm
  have hloop := CStm.Good.loop_const (x := x) (w := w) (e := .var t) (body := B) n S
    (12 * Ex.nodeCost w)
    (fun j hj => by simp [Ex.eval, (hSj j hj.le).1, hnz j hj])
    (by simp [Ex.eval, (hSj n le_rfl).1, hn])
    (fun j hj => by
      simp only [Ex.Fits, (hSj j hj).1]; exact lt_of_le_of_lt (Nat.div_le_self _ _) hk)
    (fun j hj => by
      rw [show S (j + 1) = exec x B (S j) from iter_succ _ _ _]
      exact (hstep (S j) j hj (hSj j hj.le).1).1)
  have hex : exec x (pushBits q t) st = S n := hloop.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hex]; refine hloop.mono ?_; simp only [condCost, Ex.size]; nlinarith
  · rw [hex, (hSj n le_rfl).2.1, List.take_length]
  · rw [hex, (hSj n le_rfl).1, hn]
  · rw [hex]; exact (hSj n le_rfl).2.2

/-! ## Reading the input -/

/-- Push the symbols of the input from the cursor on (reversed). -/
def readIn (q : Fin Q) (t : Fin R) : CStm R Q :=
  .seq (.rd t) (.loop (.var t) (.seq (.push q (.var t)) (.rd t)))

lemma inBit_eq (x : List Bool) (j : ℕ) :
    inBit x j = if h : j < x.length then symOf x[j] else 0 := by
  unfold inBit
  split_ifs with h
  · rw [List.drop_eq_getElem_cons h]; cases x[j] <;> rfl
  · rw [List.drop_eq_nil_of_le (by omega)]; rfl

lemma readIn_good (hw : 2 ≤ w) {q : Fin Q} {t : Fin R} (st : NSt R Q) (hpos : st.pos = 0) :
    Good x w (readIn q t) st (exec x (readIn q t) st) ((x.length + 1) * (8 * Ex.nodeCost w)) ∧
      (exec x (readIn q t) st).stk q = (syms x).reverse ++ st.stk q ∧
      (exec x (readIn q t) st).env t = 0 ∧
      (∀ r, r ≠ t → (exec x (readIn q t) st).env r = st.env r) ∧
      (exec x (readIn q t) st).pos = x.length := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  set B : CStm R Q := .seq (.push q (.var t)) (.rd t) with hB
  set st1 : NSt R Q := exec x (.rd t) st with hst1
  set S : ℕ → NSt R Q := fun j => iter x B st1 j with hS
  have hinb : ∀ j, inBit x j ≤ 2 := fun j => by
    rw [inBit_eq]; split_ifs
    · exact symOf_le _
    · omega
  have hSj : ∀ j ≤ x.length, (S j).env t = inBit x j ∧ (S j).pos = min (j + 1) x.length ∧
      (S j).stk q = (syms (x.take j)).reverse ++ st.stk q ∧
      ∀ r, r ≠ t → (S j).env r = st.env r := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [hS, iter_zero, hst1, exec, NSt.set_env, Function.update_self, hpos]
      refine ⟨by simp, by simp, by simp [syms], fun r hr => by simp [Function.update_of_ne hr]⟩
    | succ j ih =>
      intro hj
      obtain ⟨i1, i2, i3, i4⟩ := ih (by omega)
      rw [show S (j + 1) = exec x B (S j) from iter_succ _ _ _]
      simp only [hB, exec, NSt.set_env, Function.update_self, NSt.set_pos, NSt.setS_pos, i2,
        min_eq_left (show j + 1 ≤ x.length by omega)]
      refine ⟨by simp, by simp, ?_, fun r hr => by simp [Function.update_of_ne hr, i4 r hr]⟩
      simp only [NSt.set_stk, NSt.setS_stk, Function.update_self, Ex.eval, i1, i3, inBit_eq,
        dif_pos (show j < x.length by omega), syms_take_succ _ _ (show j < x.length by omega)]
      rfl
  have hloop := CStm.Good.loop_const (x := x) (w := w) (e := .var t) (body := B) x.length S
    (2 * Ex.nodeCost w + 2 * unitCost w)
    (fun j hj => by
      simp only [Ex.eval, (hSj j hj.le).1, inBit_eq, dif_pos hj]; exact (symOf_pos _).ne')
    (by simp only [Ex.eval, (hSj _ le_rfl).1, inBit_eq, dif_neg (lt_irrefl _)])
    (fun j hj => by simp only [Ex.Fits, (hSj j hj).1]; have := hinb j; omega)
    (fun j hj => by
      rw [show S (j + 1) = exec x B (S j) from iter_succ _ _ _]
      refine ((CStm.Good.push ?_).seq (CStm.Good.rd t)).mono (by simp [Ex.size]; omega)
      simp only [Ex.Fits, (hSj j hj.le).1]; have := hinb j; omega)
  have g : Good x w (readIn q t) st (S x.length) _ := (CStm.Good.rd t).seq hloop
  have hex : exec x (readIn q t) st = S x.length := g.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hex]; refine g.mono ?_; simp only [condCost, Ex.size]; nlinarith
  · rw [hex, (hSj _ le_rfl).2.2.1, List.take_length]
  · rw [hex, (hSj _ le_rfl).1, inBit_eq, dif_neg (lt_irrefl _)]
  · rw [hex]; exact (hSj _ le_rfl).2.2.2
  · rw [hex, (hSj _ le_rfl).2.1]; omega

/-! ## Clearing a stack -/

/-- Empty the stack `q`. -/
def clrS (q : Fin Q) (t f : Fin R) : CStm R Q :=
  .seq (.sne f q) (.loop (.var f) (.seq (.pop q t) (.sne f q)))

lemma clrS_good (hw : 2 ≤ w) {q : Fin Q} {t f : Fin R} (htf : t ≠ f) (st : NSt R Q) :
    Good x w (clrS q t f) st (exec x (clrS q t f) st)
        (((st.stk q).length + 1) * (8 * Ex.nodeCost w)) ∧
      (exec x (clrS q t f) st).stk q = [] ∧
      ∀ q', q' ≠ q → (exec x (clrS q t f) st).stk q' = st.stk q' := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h1 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  set l := st.stk q with hl
  set B : CStm R Q := .seq (.pop q t) (.sne f q) with hB
  set st1 : NSt R Q := exec x (.sne f q) st with hst1
  set S : ℕ → NSt R Q := fun j => iter x B st1 j with hS
  have hSj : ∀ j ≤ l.length, (S j).stk q = l.drop j ∧
      (S j).env f = if j < l.length then 1 else 0 := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [hS, iter_zero, hst1, exec, NSt.set_env, Function.update_self, NSt.set_stk,
        List.drop_zero, ← hl]
      refine ⟨by simp, ?_⟩
      cases l <;> simp
    | succ j ih =>
      intro hj
      obtain ⟨i1, -⟩ := ih (by omega)
      rw [show S (j + 1) = exec x B (S j) from iter_succ _ _ _]
      simp only [hB, exec, NSt.set_env, Function.update_self, NSt.set_stk, NSt.setS_stk, i1]
      refine ⟨by simp, ?_⟩
      simp only [List.tail_drop, List.isEmpty_iff, List.drop_eq_nil_iff]
      split_ifs <;> omega
  have hloop := CStm.Good.loop_const (x := x) (w := w) (e := .var f) (body := B) l.length S
    (unitCost w + 1 + (2 * unitCost w + 1))
    (fun j hj => by simp [Ex.eval, (hSj j hj.le).2, hj])
    (by simp [Ex.eval, (hSj _ le_rfl).2])
    (fun j hj => by simp only [Ex.Fits, (hSj j hj).2]; split_ifs <;> omega)
    (fun j hj => by
      rw [show S (j + 1) = exec x B (S j) from iter_succ _ _ _]
      exact (CStm.Good.pop q t).seq (CStm.Good.sne f q))
  have g : Good x w (clrS q t f) st (S l.length) _ := (CStm.Good.sne f q).seq hloop
  have hex : exec x (clrS q t f) st = S l.length := g.2.1
  refine ⟨?_, ?_, fun q' hq' => ?_⟩
  · rw [hex]; refine g.mono ?_; simp only [condCost, Ex.size]; nlinarith
  · rw [hex, (hSj _ le_rfl).1, List.drop_length]
  · exact exec_stk_of _ _ (by simp [clrS, wStk, Ne.symm hq'])

end Lax119563Proofs.Computability

end Computability_StackLoad

/-! ### Formerly `Lax119563Proofs.Computability.SimExtract` -/

section Computability_SimExtract

/-!
# Simulating a machine: reading off the output

`extract`: after the simulation loop, tape `0` of the halted machine holds `encodeNat v`
in the layout of an input; the stacks of tape `0` are joined, leading blanks are skipped,
and `v` is read into the register `out` (`extract_good`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler
open Lax489179.TuringMachine (Machine Config Instruction Move)

namespace Lax119563Proofs.Computability

open CStm

variable {R Q : ℕ} {x : List Bool} {w : ℕ} {M : Machine}
variable (ρ : Rg (M.tapes + 1) ↪ Fin R) (κ : Sk (M.tapes + 1) ↪ Fin Q)

variable (M) in
/-- Read the number on tape `0` into `out`. -/
def extract : CStm R Q :=
  seqL [moveAllS (κ (.L 0)) (κ (.R 0)) (ρ .tmp) (ρ .flg), skipZ (κ (.R 0)) (ρ .tmp),
    .set (ρ .out) (.const 0), .set (ρ .pw) (.const 1),
    parseB (κ (.R 0)) (ρ .tmp) (ρ .out) (ρ .pw)]

/-- The cost bound of `extract`. -/
def extractCost (w s a : ℕ) : ℕ := (a + 3 * s + 3) * (40 * Ex.nodeCost w)

lemma init_tape_zero (y : List Bool) (z : ℤ) :
    ((Lax489179.TuringMachine.init M y).tape 0 z).val =
      if 0 ≤ z then (syms y).getD z.toNat 0 else 0 := by
  simp only [Lax489179.TuringMachine.init, true_and]
  split_ifs with hz
  · simp only [syms, List.getD_eq_getElem?_getD, List.getElem?_map]
    rcases y[z.toNat]? with _ | _ | _ <;> rfl
  · rfl

lemma syms_encodeNat (v : ℕ) : syms (encodeNat v) = syms (pairs v.bits ++ [false]) := by
  rw [encodeNat_eq_pairs]

lemma extract_good (hw : 2 ≤ w) (st : NSt R Q) (hb : st.Bdd w) {c : Config M} {s a : ℕ}
    (hI : Inv ρ κ st c s a 1) (hh : (c.head 0).natAbs ≤ s) {v : ℕ}
    (hc : c.tape 0 = (Lax489179.TuringMachine.init M (encodeNat v)).tape 0)
    (hv : v.bits.length < w) :
    Good x w (extract M ρ κ) st (exec x (extract M ρ κ) st) (extractCost w s a) ∧
      (exec x (extract M ρ κ) st).env (ρ .out) = v ∧
      ((exec x (extract M ρ κ) st).stk (κ (.R 0))).length ≤ a + 3 * s ∧
      (exec x (extract M ρ κ) st).stk (κ (.L 0)) = [] ∧
      ∀ q, q ≠ κ (.L 0) → q ≠ κ (.R 0) → (exec x (extract M ρ κ) st).stk q = st.stk q := by
  obtain ⟨-, -, -, hrep, hlen⟩ := hI
  obtain ⟨hR0rep, hL0rep⟩ := hrep 0
  have hlen0 := hlen 0
  have h4 : (4 : ℕ) ≤ 2 ^ w := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h2 : 2 ≤ 2 ^ w := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  set L0 := st.stk (κ (.L 0)) with hL0
  set R0 := st.stk (κ (.R 0)) with hR0
  set y := encodeNat v with hy
  -- joining the stacks
  obtain ⟨st1, g1, e1stk, -, -, e1env⟩ := moveAllS_good (x := x) hw (q := κ (.L 0))
    (q' := κ (.R 0)) (t := ρ .tmp) (f := ρ .flg) (by simp) (by simp) st hb
  set l := L0.reverse ++ R0 with hl
  have hst1R : st1.stk (κ (.R 0)) = l := by rw [e1stk]; simp [hl, hL0, hR0]
  have hst1L : st1.stk (κ (.L 0)) = [] := by rw [e1stk]; simp
  set p := c.head 0 - L0.length with hp
  have hcells : ∀ i : ℕ, l.getD i 0 = (c.tape 0 (p + i)).val := by
    intro i
    rcases Nat.lt_or_ge i L0.length with hi | hi
    · rw [hl, List.getD_append _ _ _ _ (by simpa using hi), List.getD_reverse i hi,
        ← hL0rep]
      congr 2; omega
    · rw [hl, List.getD_append_right _ _ _ _ (by simpa using hi), List.length_reverse,
        ← hR0rep]
      congr 2; omega
  have hblank : ∀ i : ℕ, (c.tape 0 (p - 1 - i)).val = 0 := by
    intro i
    have := hL0rep (L0.length + i)
    rw [List.getD_eq_default _ _ (by omega)] at this
    have e : p - 1 - (i : ℤ) = c.head 0 - 1 - ((L0.length + i : ℕ) : ℤ) := by omega
    rw [e]; exact this
  have hyne : y ≠ [] := by simp [hy, encodeNat]
  have hy0 : (c.tape 0 0).val ≠ 0 := by
    rw [hc, init_tape_zero, if_pos le_rfl]
    obtain ⟨b, l', hb'⟩ := List.exists_cons_of_ne_nil hyne
    rw [hb']; simp [syms]; exact (symOf_pos b).ne'
  have hp0 : p ≤ 0 := by
    by_contra hpos
    have := hblank (p - 1).toNat
    rw [show p - 1 - ((p - 1).toNat : ℤ) = 0 by omega] at this
    exact hy0 this
  set d := (-p).toNat with hd
  have hdp : p = -(d : ℤ) := by omega
  have hm : ∀ i, l.getD i 0 = (List.replicate d 0 ++ syms y).getD i 0 := by
    intro i
    rw [hcells, hc, init_tape_zero]
    conv_rhs => rw [List.getD_eq_getElem?_getD]
    rcases Nat.lt_or_ge i d with hi | hi
    · rw [if_neg (by omega), List.getElem?_append_left (by simpa using hi),
        List.getElem?_replicate]
      simp [hi]
    · rw [if_pos (by omega), List.getElem?_append_right (by simpa using hi),
        List.length_replicate, ← List.getD_eq_getElem?_getD]
      congr 1; omega
  have hsyne : syms y ≠ [] := by simp [syms, hyne]
  have hlast : (List.replicate d 0 ++ syms y).getD
      ((List.replicate d 0 ++ syms y).length - 1) 0 ≠ 0 := by
    have hmeq : List.replicate d 0 ++ syms y =
        (List.replicate d 0 ++ syms (pairs v.bits)) ++ [1] := by
      simp [hy, encodeNat_eq_pairs, syms, symOf]
    rw [hmeq]; simp
  have hleq := eq_append_drop_of_getD hm (by simp [hsyne]) hlast
  set rest' := l.drop (List.replicate d 0 ++ syms y).length with hrest'
  obtain ⟨a0, tl, htl⟩ := List.exists_cons_of_ne_nil hsyne
  have ha0 : a0 = if 0 < v.bits.length then 2 else 1 := by
    have := syms_head v.bits 0
    rw [List.drop_zero, ← syms_encodeNat, ← hy, htl] at this
    exact this
  -- skipping the blanks
  have hst1R' : st1.stk (κ (.R 0)) = List.replicate d 0 ++ a0 :: (tl ++ rest') := by
    rw [hst1R, hleq, htl]; simp
  obtain ⟨g2, e2R, e2t⟩ := skipZ_good (x := x) (w := w) (t := ρ .tmp) hw st1 d a0 (tl ++ rest')
    (by rw [ha0]; split_ifs <;> omega) (by rw [ha0]; split_ifs <;> omega) hst1R'
  set st2 := exec x (skipZ (κ (.R 0)) (ρ .tmp)) st1 with hst2
  set st3 := (st2.set (ρ .out) 0).set (ρ .pw) 1 with hst3
  have g3a : Good x w (.set (ρ .out) (.const 0) : CStm R Q) st2 (st2.set (ρ .out) 0)
      (Ex.nodeCost w + unitCost w) :=
    (CStm.Good.set (by simp [Ex.Fits])).mono (by simp [Ex.size])
  have g3b : Good x w (.set (ρ .pw) (.const 1) : CStm R Q) (st2.set (ρ .out) 0) st3
      (Ex.nodeCost w + unitCost w) :=
    (CStm.Good.set (by simp [Ex.Fits]; omega)).mono (by simp [Ex.size])
  obtain ⟨g4, e4o, e4R⟩ := parseB_good (x := x) (q := κ (.R 0)) hw (t := ρ .tmp)
    (o := ρ .out) (p := ρ .pw) (by simp) (by simp) (by simp) st3 v.bits rest' hv
    (by
      simp only [hst3, NSt.set_stk, e2R]
      rw [← syms_encodeNat, ← hy, htl]; rfl)
    (by simp only [hst3, NSt.set_env]; rw [Function.update_of_ne (by simp),
          Function.update_of_ne (by simp), e2t, ha0])
    (by simp [hst3]) (by simp [hst3])
  set st4 := exec x (parseB (κ (.R 0)) (ρ .tmp) (ρ .out) (ρ .pw)) st3 with hst4
  have g : Good x w (extract M ρ κ) st st4 _ :=
    g1.seq (g2.seq (g3a.seq (g3b.seq (g4.seq CStm.Good.skip))))
  have hex : exec x (extract M ρ κ) st = st4 := g.2.1
  -- lengths
  have hlenl : l.length ≤ a + 3 * s := by
    simp only [hl, List.length_append, List.length_reverse]; omega
  have hylen : y.length ≤ l.length := by
    have := congrArg List.length hleq; simp [syms] at this; omega
  have hbits : v.bits.length ≤ y.length := by
    simp [hy, encodeNat_eq_pairs]; omega
  have hdle : d ≤ 2 * s := by omega
  refine ⟨?_, ?_, ?_, ?_, fun q hq1 hq2 => ?_⟩
  · rw [hex]; refine g.mono ?_
    simp only [extractCost]
    have hL := hlen0.1
    nlinarith
  · rw [hex, e4o, Machines.valBits_bits]
  · rw [hex, e4R, hrest', List.length_drop]; omega
  · rw [hex]
    have : st4.stk (κ (.L 0)) = st1.stk (κ (.L 0)) :=
      exec_stk_of _ _ (by simp [parseB, skipZ, seqL, wStk]) |>.trans
        (by simp only [hst3, NSt.set_stk]; exact exec_stk_of _ _ (by simp [skipZ, wStk]))
    rw [this, hst1L]
  · rw [hex]
    have h1 : st4.stk q = st1.stk q :=
      exec_stk_of _ _ (by simp [parseB, skipZ, seqL, wStk, Ne.symm hq2]) |>.trans
        (by simp only [hst3, NSt.set_stk]; exact exec_stk_of _ _ (by simp [skipZ, wStk, Ne.symm hq2]))
    rw [h1, e1stk, Function.update_of_ne hq2, Function.update_of_ne hq1]

end Lax119563Proofs.Computability

end Computability_SimExtract

/-! ### Formerly `Lax119563Proofs.Computability.SimFull` -/

section Computability_SimFull

/-!
# Simulating a machine by a structured statement

The complete simulators:
* `simNat M ρ κ`: runs `M` on `encodeNat k`, where `k` is the value of the register `inp`;
* `simIn M ρ κ`: runs `M` on the input `x` of the statement.

If `M` computes `encodeNat v`, they leave `v` in the register `out` and the halting time of
`M` in `clk`, empty all their stacks, and change no register outside the range of `ρ` and
no stack outside the range of `κ` (`simNat_good`, `simIn_good`). The cost is linear in the
halting time and the input length, with a factor depending on `M` and on the word size.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler
open Lax119563.DeterministicTime
open Lax489179.TuringMachine (Machine Config Instruction Move)

namespace Lax119563Proofs.Computability

open CStm

variable {R Q : ℕ} {x : List Bool} {w : ℕ} {M : Machine}
variable (ρ : Rg (M.tapes + 1) ↪ Fin R) (κ : Sk (M.tapes + 1) ↪ Fin Q)

/-! ## The statements -/

/-- All stacks of the simulator. -/
noncomputable def allSk (n : ℕ) : List (Sk n) := (Finset.univ : Finset (Sk n)).toList

lemma mem_allSk {n : ℕ} (g : Sk n) : g ∈ allSk n := Finset.mem_toList.mpr (Finset.mem_univ _)

variable (M) in
/-- Empty all stacks of the simulator. -/
noncomputable def clearAll : CStm R Q :=
  seqL ((allSk (M.tapes + 1)).map fun g => clrS (κ g) (ρ .tmp) (ρ .flg))

variable (M) in
/-- Load `encodeNat (inp)` onto the stack of tape `0`. -/
def loadNat : CStm R Q :=
  seqL [.set (ρ .tmp) (.var (ρ .inp)), pushBits (κ .aux) (ρ .tmp), .push (κ .aux) (.const 1),
    moveAllS (κ .aux) (κ (.R 0)) (ρ .tmp) (ρ .flg)]

variable (M) in
/-- Load the input onto the stack of tape `0`. -/
def loadIn : CStm R Q :=
  seqL [.rst, readIn (κ .aux) (ρ .tmp), moveAllS (κ .aux) (κ (.R 0)) (ρ .tmp) (ρ .flg)]

variable (M) in
/-- Simulation, output and cleanup. -/
noncomputable def simTail : CStm R Q := seqL [core M ρ κ, extract M ρ κ, clearAll M ρ κ]

variable (M) in
/-- **The simulator on a number**: run `M` on `encodeNat (inp)`. -/
noncomputable def simNat : CStm R Q := .seq (loadNat M ρ κ) (simTail M ρ κ)

variable (M) in
/-- **The simulator on the input**: run `M` on the input of the statement. -/
noncomputable def simIn : CStm R Q := .seq (loadIn M ρ κ) (simTail M ρ κ)

/-! ## Frames -/

section Frame

variable {r : Fin R} {q : Fin Q}

lemma wReg_seqL_map {α : Type} (f : α → CStm R Q) (l : List α)
    (h : ∀ a ∈ l, wReg r (f a) = false) : wReg r (seqL (l.map f)) = false := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, seqL, wReg, Bool.or_eq_false_iff]
    exact ⟨h a (by simp), ih fun b hb => h b (by simp [hb])⟩

lemma wStk_seqL_map {α : Type} (f : α → CStm R Q) (l : List α)
    (h : ∀ a ∈ l, wStk q (f a) = false) : wStk q (seqL (l.map f)) = false := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, seqL, wStk, Bool.or_eq_false_iff]
    exact ⟨h a (by simp), ih fun b hb => h b (by simp [hb])⟩

lemma wOut_seqL_map {α : Type} (f : α → CStm R Q) (l : List α)
    (h : ∀ a ∈ l, wOut (f a) = false) : wOut (seqL (l.map f)) = false := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, seqL, wOut, Bool.or_eq_false_iff]
    exact ⟨h a (by simp), ih fun b hb => h b (by simp [hb])⟩

lemma wPos_seqL_map {α : Type} (f : α → CStm R Q) (l : List α)
    (h : ∀ a ∈ l, wPos (f a) = false) : wPos (seqL (l.map f)) = false := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, seqL, wPos, Bool.or_eq_false_iff]
    exact ⟨h a (by simp), ih fun b hb => h b (by simp [hb])⟩

lemma wReg_chain (l : List (Key M)) (h : ∀ p, wReg r (leaf M ρ κ p : CStm R Q) = false) :
    wReg r (chain M ρ κ l : CStm R Q) = false := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [chain_cons]; simp [wReg, h p, ih]

lemma wStk_chain (l : List (Key M)) (h : ∀ p, wStk q (leaf M ρ κ p : CStm R Q) = false) :
    wStk q (chain M ρ κ l : CStm R Q) = false := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [chain_cons]; simp [wStk, h p, ih]

lemma wOut_chain (l : List (Key M)) (h : ∀ p, wOut (leaf M ρ κ p : CStm R Q) = false) :
    wOut (chain M ρ κ l : CStm R Q) = false := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [chain_cons]; simp [wOut, h p, ih]

lemma wPos_chain (l : List (Key M)) (h : ∀ p, wPos (leaf M ρ κ p : CStm R Q) = false) :
    wPos (chain M ρ κ l : CStm R Q) = false := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [chain_cons]; simp [wPos, h p, ih]

lemma wStk_core' (hq : ∀ j, κ (.L j) ≠ q ∧ κ (.R j) ≠ q) :
    wStk q (core M ρ κ : CStm R Q) = false := by
  have hleaf : ∀ p, wStk q (leaf M ρ κ p : CStm R Q) = false := by
    intro p
    unfold leaf
    split
    · simp only [wStk, Bool.or_eq_false_iff]
      exact ⟨trivial, wStk_seqL_map _ _ fun j _ => by simp [pushT, wStk, (hq _).2]⟩
    · simp only [wStk, Bool.or_eq_false_iff]
      refine ⟨trivial, wStk_seqL_map _ _ fun j _ => ?_⟩
      unfold opT; split <;> simp [wStk, (hq _).1, (hq _).2]
  simp only [core, body, wStk, Bool.or_eq_false_iff]
  exact ⟨trivial, trivial, trivial, wStk_seqL_map _ _ fun j _ => by simp [popT, wStk, (hq _).2],
    wStk_chain ρ κ _ hleaf, trivial⟩

variable (hr : ∀ g, ρ g ≠ r) (hq : ∀ g, κ g ≠ q)
include hr

lemma wReg_core : wReg r (core M ρ κ : CStm R Q) = false := by
  have hleaf : ∀ p, wReg r (leaf M ρ κ p : CStm R Q) = false := by
    intro p
    unfold leaf
    split
    · simp only [wReg, Bool.or_eq_false_iff, decide_eq_false_iff_not]
      exact ⟨hr _, wReg_seqL_map _ _ fun j _ => by simp [pushT, wReg]⟩
    · simp only [wReg, Bool.or_eq_false_iff, decide_eq_false_iff_not]
      refine ⟨hr _, wReg_seqL_map _ _ fun j _ => ?_⟩
      unfold opT; split <;> simp [wReg, hr]
  simp only [core, body, wReg, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  exact ⟨hr _, hr _, hr _, wReg_seqL_map _ _ fun j _ => by simp [popT, wReg, hr],
    wReg_chain ρ κ _ hleaf, hr _⟩

lemma wReg_tail : wReg r (simTail M ρ κ : CStm R Q) = false := by
  simp only [simTail, seqL, wReg, Bool.or_eq_false_iff]
  refine ⟨wReg_core ρ κ hr, ?_, ?_, trivial⟩
  · simp [extract, seqL, wReg, moveAllS, skipZ, parseB, hr]
  · exact wReg_seqL_map _ _ fun g _ => by simp [clrS, wReg, hr]

lemma wReg_simNat : wReg r (simNat M ρ κ : CStm R Q) = false := by
  simp only [simNat, wReg, Bool.or_eq_false_iff]
  refine ⟨?_, wReg_tail ρ κ hr⟩
  simp [loadNat, seqL, wReg, pushBits, moveAllS, hr]

lemma wReg_simIn : wReg r (simIn M ρ κ : CStm R Q) = false := by
  simp only [simIn, wReg, Bool.or_eq_false_iff]
  refine ⟨?_, wReg_tail ρ κ hr⟩
  simp [loadIn, seqL, wReg, readIn, moveAllS, hr]

omit hr
include hq

lemma wStk_tail : wStk q (simTail M ρ κ : CStm R Q) = false := by
  simp only [simTail, seqL, wStk, Bool.or_eq_false_iff]
  refine ⟨wStk_core' ρ κ fun j => ⟨hq _, hq _⟩, ?_, ?_, trivial⟩
  · simp [extract, seqL, wStk, moveAllS, skipZ, parseB, hq]
  · exact wStk_seqL_map _ _ fun g _ => by simp [clrS, wStk, hq]

lemma wStk_simNat : wStk q (simNat M ρ κ : CStm R Q) = false := by
  simp only [simNat, wStk, Bool.or_eq_false_iff]
  refine ⟨?_, wStk_tail ρ κ hq⟩
  simp [loadNat, seqL, wStk, pushBits, moveAllS, hq]

lemma wStk_simIn : wStk q (simIn M ρ κ : CStm R Q) = false := by
  simp only [simIn, wStk, Bool.or_eq_false_iff]
  refine ⟨?_, wStk_tail ρ κ hq⟩
  simp [loadIn, seqL, wStk, readIn, moveAllS, hq]

omit hq

lemma wOut_core : wOut (core M ρ κ : CStm R Q) = false := by
  have hleaf : ∀ p, wOut (leaf M ρ κ p : CStm R Q) = false := by
    intro p
    unfold leaf
    split
    · simp only [wOut, Bool.or_eq_false_iff]
      exact ⟨trivial, wOut_seqL_map _ _ fun j _ => rfl⟩
    · simp only [wOut, Bool.or_eq_false_iff]
      refine ⟨trivial, wOut_seqL_map _ _ fun j _ => ?_⟩
      unfold opT; split <;> rfl
  simp only [core, body, wOut, Bool.or_eq_false_iff]
  exact ⟨trivial, trivial, trivial, wOut_seqL_map _ _ fun j _ => rfl, wOut_chain ρ κ _ hleaf, trivial⟩

lemma wPos_core : wPos (core M ρ κ : CStm R Q) = false := by
  have hleaf : ∀ p, wPos (leaf M ρ κ p : CStm R Q) = false := by
    intro p
    unfold leaf
    split
    · simp only [wPos, Bool.or_eq_false_iff]
      exact ⟨trivial, wPos_seqL_map _ _ fun j _ => rfl⟩
    · simp only [wPos, Bool.or_eq_false_iff]
      refine ⟨trivial, wPos_seqL_map _ _ fun j _ => ?_⟩
      unfold opT; split <;> rfl
  simp only [core, body, wPos, Bool.or_eq_false_iff]
  exact ⟨trivial, trivial, trivial, wPos_seqL_map _ _ fun j _ => rfl, wPos_chain ρ κ _ hleaf, trivial⟩

lemma wOut_tail : wOut (simTail M ρ κ : CStm R Q) = false := by
  simp only [simTail, seqL, wOut, Bool.or_eq_false_iff]
  refine ⟨wOut_core ρ κ, by simp [extract, seqL, wOut, moveAllS, skipZ, parseB],
    wOut_seqL_map _ _ fun g _ => by simp [clrS, wOut], trivial⟩

lemma wPos_tail : wPos (simTail M ρ κ : CStm R Q) = false := by
  simp only [simTail, seqL, wPos, Bool.or_eq_false_iff]
  refine ⟨wPos_core ρ κ, by simp [extract, seqL, wPos, moveAllS, skipZ, parseB],
    wPos_seqL_map _ _ fun g _ => by simp [clrS, wPos], trivial⟩

lemma wOut_simNat : wOut (simNat M ρ κ : CStm R Q) = false := by
  simp only [simNat, wOut, Bool.or_eq_false_iff]
  exact ⟨by simp [loadNat, seqL, wOut, pushBits, moveAllS], wOut_tail ρ κ⟩

lemma wPos_simNat : wPos (simNat M ρ κ : CStm R Q) = false := by
  simp only [simNat, wPos, Bool.or_eq_false_iff]
  exact ⟨by simp [loadNat, seqL, wPos, pushBits, moveAllS], wPos_tail ρ κ⟩

lemma wOut_simIn : wOut (simIn M ρ κ : CStm R Q) = false := by
  simp only [simIn, wOut, Bool.or_eq_false_iff]
  exact ⟨by simp [loadIn, seqL, wOut, readIn, moveAllS], wOut_tail ρ κ⟩

end Frame

end Lax119563Proofs.Computability

end Computability_SimFull
