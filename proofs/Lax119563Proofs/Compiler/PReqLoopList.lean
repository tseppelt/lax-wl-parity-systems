import Lax119563Proofs.Compiler.PReqSch
import Lax119563Proofs.Compiler.PReqList
import Lax119563Proofs.Compiler.PSchLoop
import Lax119563Proofs.Compiler.PJoinFacts

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
