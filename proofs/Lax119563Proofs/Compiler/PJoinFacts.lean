import Lax119563Proofs.Compiler.PJoin
import Lax119563Proofs.Compiler.PReqList
import Lax119563Proofs.Compiler.OrderPos

/-!
# Pass `P3`: the list facts of the join

The union of the location records `locRecs I` and the requests `reqs I` satisfies the
hypotheses of `Join.scanF_eq` (keys of `ℓ + 2` words):
* `locRecs_eq`: `locRecs I` lists `locRecC I v c` (`v :: cdesc c ++ [0, off, labs, ι]`) for
  every location `v` and `c ∈ coordList (I.domain v)`;
* **`hG1`** (`locRec_unique`): a location record is determined by its key (`cdesc_injective`);
* **`hG2`** (`req_has_loc`): the key `u :: cdesc (π.apply c)` of every request is the key of a
  location record (`Schema.WellFormed`: `π.apply c ∈ I.domain u`);
* lengths `ℓ + 6` (`length_of_mem_union`), word bounds (`lt_of_mem_locRecs`,
  `lt_of_mem_reqs`), the number of requests (`length_reqs`, `ansBase_le_H`);
* **`p3_answers`**: for any permutation `L0` of `locRecs I ++ reqs I`, scanning
  `L0.mergeSort rle` and sorting the (reversed) answers by `rle` gives `ansAll I`, the answers
  in the order of `P4`: per schema (`ansE`), ternary: per column `U, V, W`; binary: all `V`,
  then all `U`; each answer is `ansRec I v c' s = [s, clsStart (coord v c') - locBase, labs,
  (initSeed I v c').val]` with `s` running through `0, 1, 2, …` (`map_head_ansAll`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-! ## Location records -/

lemma cdesc_injective : Function.Injective (cdesc : Coord k ℓ → List ℕ) := by
  rintro ⟨i, b⟩ ⟨i', b'⟩ h
  simp only [cdesc, List.cons.injEq] at h
  obtain ⟨h1, h2⟩ := h
  refine Prod.ext (Fin.ext h1) (funext fun t => ?_)
  have := congrArg (fun l => l[(t : ℕ)]?) h2
  simp [blockDescription] at this
  exact ZMod.val_injective _ this

/-- The location record of the coordinate `c` of `v`. -/
noncomputable def locRecC (v : Fin I.numLocations) (c : Coord k ℓ) : List ℕ :=
  (v : ℕ) :: cdesc c ++ [0, locOff I v + (coordList (I.domain v)).idxOf c * labsN I v,
    labsN I v, initNum (I.init v)]

lemma locRec_eq (v : Fin I.numLocations) {r : ℕ} (hr : r < (coordList (I.domain v)).length) :
    locRec I v r = locRecC I v (coordList (I.domain v))[r] := by
  have hn : (locNums I v).getD r 0 = coordNum (coordList (I.domain v))[r] := by
    rw [locNums_eq, List.getD_eq_getElem _ _ (by simpa using hr)]; simp
  rw [locRec, locRecC, hn, coordNumDescription_coordNum,
    List.Nodup.idxOf_getElem (nodup_coordList _)]
  rfl

lemma recsV_eq (v : Fin I.numLocations) :
    recsV I v = (coordList (I.domain v)).map (locRecC I v) := by
  refine List.ext_getElem (by simp [recsV]) fun r h1 h2 => ?_
  simp only [recsV, List.getElem_map]
  rw [List.getElem_range]
  exact locRec_eq I v (by simpa using h2)

lemma locRecs_eq : locRecs I =
    (List.finRange I.numLocations).flatMap fun v => (coordList (I.domain v)).map (locRecC I v) := by
  rw [locRecs]; exact congrArg (fun f => List.flatMap f _) (funext (recsV_eq I))

lemma mem_locRecs {m : List ℕ} :
    m ∈ locRecs I ↔ ∃ v, ∃ c ∈ I.domain v, m = locRecC I v c := by
  rw [locRecs_eq]
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_map, mem_coordList]
  constructor
  · rintro ⟨v, c, hc, rfl⟩; exact ⟨v, c, hc, rfl⟩
  · rintro ⟨v, c, hc, rfl⟩; exact ⟨v, c, hc, rfl⟩

lemma length_locRecC (v : Fin I.numLocations) (c : Coord k ℓ) :
    (locRecC I v c).length = ℓ + 6 := by
  simp [locRecC, length_cdesc]

lemma key_locRecC (v : Fin I.numLocations) (c : Coord k ℓ) :
    (locRecC I v c).take (ℓ + 2) = (v : ℕ) :: cdesc c := by
  rw [locRecC, List.cons_append, List.take_succ_cons,
    List.take_append_of_le_length (by simp [length_cdesc]),
    List.take_of_length_le (by simp [length_cdesc])]

lemma getD_rec (a : ℕ) (d : List ℕ) (x0 x1 x2 x3 i n : ℕ) (hn : n = d.length + 1 + i)
    (hi : i < 4) : (a :: d ++ [x0, x1, x2, x3]).getD n 0 = [x0, x1, x2, x3].getD i 0 := by
  rw [List.cons_append, hn, show d.length + 1 + i = (d.length + i) + 1 by omega]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by omega), show d.length + i - d.length = i by omega]

lemma isLoc_locRecC (v : Fin I.numLocations) (c : Coord k ℓ) :
    Join.isLoc (ℓ + 2) (locRecC I v c) = true := by
  have := getD_rec (v : ℕ) (cdesc c) 0 (locOff I v + (coordList (I.domain v)).idxOf c * labsN I v)
    (labsN I v) (initNum (I.init v)) 0 (ℓ + 2) (by simp [length_cdesc]) (by omega)
  simp only [Join.isLoc, locRecC, this]; rfl

/-! ## Requests -/

lemma length_reqRec (u : ℕ) (π : BlockPerm k ℓ) (c : Coord k ℓ) (s : ℕ) :
    (reqRec u π c s).length = ℓ + 6 := by
  simp [reqRec, length_cdesc]

lemma key_reqRec (u : ℕ) (π : BlockPerm k ℓ) (c : Coord k ℓ) (s : ℕ) :
    (reqRec u π c s).take (ℓ + 2) = u :: cdesc (π.apply c) := by
  rw [reqRec, List.cons_append, List.take_succ_cons,
    List.take_append_of_le_length (by simp [length_cdesc]),
    List.take_of_length_le (by simp [length_cdesc])]

lemma isLoc_reqRec (u : ℕ) (π : BlockPerm k ℓ) (c : Coord k ℓ) (s : ℕ) :
    Join.isLoc (ℓ + 2) (reqRec u π c s) = false := by
  have := getD_rec u (cdesc (π.apply c)) 1 s 0 0 0 (ℓ + 2) (by simp [length_cdesc]) (by omega)
  simp only [Join.isLoc, reqRec, this]; rfl

lemma mem_reqs {r : List ℕ} (hr : r ∈ reqs I) :
    ∃ e : Fin I.schemas.length, ∃ p ∈ (schLocs (sch I e)).zip (schPerms (sch I e)),
      ∃ c ∈ dom I e, ∃ s, r = reqRec p.1 p.2 c s := by
  simp only [reqs, reqsE, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hr
  obtain ⟨e, p, hp, q, hq, rfl⟩ := hr
  exact ⟨e, p.1, List.fst_mem_of_mem_zipIdx hp, q.1,
    mem_coordList.mp (List.fst_mem_of_mem_zipIdx hq), _, rfl⟩

/-- Well-formedness: the target of a column lies in the domain of the location. -/
lemma target_mem {W : ℕ} {dm : Fin W → Finset (Coord k ℓ)} {s : Schema k ℓ W}
    (hs : s.WellFormed dm) {p : ℕ × BlockPerm k ℓ} (hp : p ∈ (schLocs s).zip (schPerms s))
    {c : Coord k ℓ} (hc : c ∈ s.domain) : ∃ h : p.1 < W, p.2.apply c ∈ dm ⟨p.1, h⟩ := by
  cases s with
  | binary u v D σ τ =>
    simp only [schLocs, schPerms, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    obtain ⟨-, h1, h2⟩ := hs
    rcases hp with rfl | rfl
    · exact ⟨u.2, h1 (Finset.mem_image_of_mem _ hc)⟩
    · exact ⟨v.2, h2 (Finset.mem_image_of_mem _ hc)⟩
  | ternary u v w' D σ τ π =>
    simp only [schLocs, schPerms, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    obtain ⟨-, -, -, h1, h2, h3⟩ := hs
    rcases hp with rfl | rfl | rfl
    · exact ⟨u.2, h1 (Finset.mem_image_of_mem _ hc)⟩
    · exact ⟨v.2, h2 (Finset.mem_image_of_mem _ hc)⟩
    · exact ⟨w'.2, h3 (Finset.mem_image_of_mem _ hc)⟩

lemma wf_sch (e : Fin I.schemas.length) : (sch I e).WellFormed I.domain :=
  I.schema_wellFormed _ (List.get_mem _ _)

/-! ## The hypotheses of `Join.scanF_eq` -/

/-- The union of location records and requests. -/
noncomputable def union : List (List ℕ) := locRecs I ++ reqs I

lemma length_of_mem_union {r : List ℕ} (hr : r ∈ union I) : r.length = ℓ + 6 := by
  rcases List.mem_append.mp hr with h | h
  · obtain ⟨v, c, -, rfl⟩ := (mem_locRecs I).mp h; exact length_locRecC I v c
  · obtain ⟨e, p, -, c, -, s, rfl⟩ := mem_reqs I h; exact length_reqRec _ _ _ _

lemma isLoc_of_mem_union {r : List ℕ} (hr : r ∈ union I) :
    Join.isLoc (ℓ + 2) r = true ↔ r ∈ locRecs I := by
  constructor
  · intro hl
    rcases List.mem_append.mp hr with h | h
    · exact h
    · obtain ⟨e, p, -, c, -, s, rfl⟩ := mem_reqs I h
      rw [isLoc_reqRec] at hl; exact absurd hl (by simp)
  · intro h
    obtain ⟨v, c, -, rfl⟩ := (mem_locRecs I).mp h; exact isLoc_locRecC I v c

/-- **Keys are unique** among the location records. -/
lemma locRec_unique {m m' : List ℕ} (hm : m ∈ locRecs I) (hm' : m' ∈ locRecs I)
    (h : m.take (ℓ + 2) = m'.take (ℓ + 2)) : m = m' := by
  obtain ⟨v, c, -, rfl⟩ := (mem_locRecs I).mp hm
  obtain ⟨v', c', -, rfl⟩ := (mem_locRecs I).mp hm'
  rw [key_locRecC, key_locRecC, List.cons.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rw [Fin.ext h1, cdesc_injective h2]

open Classical in
/-- The location record with a given key. -/
noncomputable def gLoc (key : List ℕ) : List ℕ :=
  if h : ∃ m' ∈ locRecs I, m'.take (ℓ + 2) = key then h.choose else []

lemma gLoc_eq {m : List ℕ} (hm : m ∈ locRecs I) : gLoc I (m.take (ℓ + 2)) = m := by
  have h : ∃ m' ∈ locRecs I, m'.take (ℓ + 2) = m.take (ℓ + 2) := ⟨m, hm, rfl⟩
  rw [gLoc, dif_pos h]
  exact locRec_unique I h.choose_spec.1 hm h.choose_spec.2

/-- `hG1`. -/
lemma hG1 : ∀ m ∈ union I, Join.isLoc (ℓ + 2) m = true → gLoc I (m.take (ℓ + 2)) = m :=
  fun _ hm hl => gLoc_eq I ((isLoc_of_mem_union I hm).mp hl)

/-- The location record answering the request of column `c` of argument `p` of schema `e`. -/
lemma req_loc {e : Fin I.schemas.length} {p : ℕ × BlockPerm k ℓ}
    (hp : p ∈ (schLocs (sch I e)).zip (schPerms (sch I e))) {c : Coord k ℓ} (hc : c ∈ dom I e)
    (s : ℕ) : ∃ h : p.1 < I.numLocations, p.2.apply c ∈ I.domain ⟨p.1, h⟩ ∧
      gLoc I ((reqRec p.1 p.2 c s).take (ℓ + 2)) = locRecC I ⟨p.1, h⟩ (p.2.apply c) := by
  obtain ⟨h, hd⟩ := target_mem (wf_sch I e) hp hc
  refine ⟨h, hd, ?_⟩
  rw [key_reqRec, show p.1 :: cdesc (p.2.apply c) =
    (locRecC I ⟨p.1, h⟩ (p.2.apply c)).take (ℓ + 2) by rw [key_locRecC]]
  exact gLoc_eq I ((mem_locRecs I).mpr ⟨_, _, hd, rfl⟩)

/-- `hG2`. -/
lemma hG2 : ∀ r ∈ union I, Join.isLoc (ℓ + 2) r = false →
    ∃ m ∈ union I, Join.isLoc (ℓ + 2) m = true ∧ m.take (ℓ + 2) = r.take (ℓ + 2) := by
  intro r hr hl
  have hr' : r ∈ reqs I := by
    rcases List.mem_append.mp hr with h | h
    · rw [(isLoc_of_mem_union I hr).mpr h] at hl; exact absurd hl (by simp)
    · exact h
  obtain ⟨e, p, hp, c, hc, s, rfl⟩ := mem_reqs I hr'
  obtain ⟨h, hd, -⟩ := req_loc I hp hc s
  refine ⟨locRecC I ⟨p.1, h⟩ (p.2.apply c),
    List.mem_append_left _ ((mem_locRecs I).mpr ⟨_, _, hd, rfl⟩), isLoc_locRecC I _ _, ?_⟩
  rw [key_locRecC, key_reqRec]

/-! ## The answers -/

/-- The answer `[s, off, labs, seed]` for the coordinate `c'` of location `v`. -/
noncomputable def ansRec (v : Fin I.numLocations) (c' : Coord k ℓ) (s : ℕ) : List ℕ :=
  [s, clsStart I (Cls.coord v c') - locBase I, labsN I v, (initSeed I v c').val]

/-- `ansRec` for a location given as a number. -/
noncomputable def ansU (u : ℕ) (c' : Coord k ℓ) (s : ℕ) : List ℕ :=
  if h : u < I.numLocations then ansRec I ⟨u, h⟩ c' s else []

@[simp] lemma ansU_fin (v : Fin I.numLocations) (c' : Coord k ℓ) (s : ℕ) :
    ansU I v c' s = ansRec I v c' s := by
  simp [ansU, v.2]

lemma seedV_eq (v : Fin I.numLocations) (c' : Coord k ℓ) :
    seedV c'.1 (initNum (I.init v)) = (initSeed I v c').val := by
  unfold initSeed
  have v0 : (0 : ZMod 2).val = 0 := rfl
  have v1 : (1 : ZMod 2).val = 1 := rfl
  rcases h : I.init v with _ | b
  · by_cases hc : (c'.1 : ℕ) = 0 <;> simp [seedV, initNum, hc, v0]
  · have hb : b = 0 ∨ b = 1 := by fin_cases b; exacts [Or.inl rfl, Or.inr rfl]
    rcases hb with rfl | rfl <;> by_cases hc : (c'.1 : ℕ) = 0 <;> simp [seedV, initNum, hc, v0, v1]

lemma off_eq {v : Fin I.numLocations} {c' : Coord k ℓ} (hc : c' ∈ I.domain v) :
    locOff I v + (coordList (I.domain v)).idxOf c' * labsN I v =
      clsStart I (Cls.coord v c') - locBase I := by
  rw [clsStart_coord I hc, locStart_eq, labsN]; omega

/-- The answer computed by the scan for a request `r` (`Join.scanF_eq` with `gLoc`). -/
noncomputable def ansF (r : List ℕ) : List ℕ := jAns ℓ (jCur ℓ (gLoc I (r.take (ℓ + 2)))) r

lemma jAns_locRecC {v : Fin I.numLocations} {c' : Coord k ℓ} (hc : c' ∈ I.domain v)
    (u : ℕ) (π : BlockPerm k ℓ) (c : Coord k ℓ) (s : ℕ) :
    jAns ℓ (jCur ℓ (locRecC I v c')) (reqRec u π c s) = ansRec I v c' s := by
  have h3 := getD_rec (v : ℕ) (cdesc c') 0 (locOff I v + (coordList (I.domain v)).idxOf c' *
    labsN I v) (labsN I v) (initNum (I.init v)) 1 (ℓ + 3) (by simp [length_cdesc]) (by omega)
  have h4 := getD_rec (v : ℕ) (cdesc c') 0 (locOff I v + (coordList (I.domain v)).idxOf c' *
    labsN I v) (labsN I v) (initNum (I.init v)) 2 (ℓ + 4) (by simp [length_cdesc]) (by omega)
  have h5 := getD_rec (v : ℕ) (cdesc c') 0 (locOff I v + (coordList (I.domain v)).idxOf c' *
    labsN I v) (labsN I v) (initNum (I.init v)) 3 (ℓ + 5) (by simp [length_cdesc]) (by omega)
  have hr := getD_rec u (cdesc (π.apply c)) 1 s 0 0 1 (ℓ + 3) (by simp [length_cdesc]) (by omega)
  have h1 : (locRecC I v c').getD 1 0 = c'.1 := by simp [locRecC, cdesc]
  rw [jAns, jCur, h1]
  rw [locRecC, reqRec]
  rw [h3, h4, h5, hr]
  simp [ansRec, seedV_eq, off_eq I hc]

lemma ansF_req {e : Fin I.schemas.length} {p : ℕ × BlockPerm k ℓ}
    (hp : p ∈ (schLocs (sch I e)).zip (schPerms (sch I e))) {c : Coord k ℓ} (hc : c ∈ dom I e)
    (s : ℕ) : ansF I (reqRec p.1 p.2 c s) = ansU I p.1 (p.2.apply c) s := by
  obtain ⟨h, hd, hg⟩ := req_loc I hp hc s
  rw [ansF, hg, jAns_locRecC I hd, ansU, dif_pos h]

lemma length_ansF (r : List ℕ) : (ansF I r).length = 4 := rfl

lemma headD_ansF (r : List ℕ) : (ansF I r).headD 0 = r.getD (ℓ + 3) 0 := rfl

/-! ## The answers in the order of `P4` -/

/-- **The answers of schema `e` in the order of `P4`**: ternary: per column the answers for
`U, V, W`; binary: the answers for `V` (all columns), then for `U`. Sequence numbers
`ansBase I e, ansBase I e + 1, …`. -/
noncomputable def ansE (e : Fin I.schemas.length) : List (List ℕ) :=
  match sch I e with
  | .binary u v D σ τ =>
      (coordList D).zipIdx.map (fun q => ansRec I v (τ.apply q.1) (ansBase I e + q.2)) ++
      (coordList D).zipIdx.map
        (fun q => ansRec I u (σ.apply q.1) (ansBase I e + (coordList D).length + q.2))
  | .ternary u v w' D σ τ π =>
      (coordList D).zipIdx.flatMap fun q =>
        [ansRec I u (σ.apply q.1) (ansBase I e + 3 * q.2),
         ansRec I v (τ.apply q.1) (ansBase I e + 3 * q.2 + 1),
         ansRec I w' (π.apply q.1) (ansBase I e + 3 * q.2 + 2)]

/-- **All answers in the order of `P4`.** -/
noncomputable def ansAll : List (List ℕ) := (List.finRange I.schemas.length).flatMap (ansE I)

lemma perm3 {α β : Type*} (x y z : α → β) :
    ∀ l : List α, (l.map x ++ (l.map y ++ l.map z)).Perm (l.flatMap fun a => [x a, y a, z a])
  | [] => by simp
  | a :: t => by
    have ih := perm3 x y z t
    simp only [List.map_cons, List.flatMap_cons, List.cons_append, List.nil_append]
    refine List.Perm.cons _ ?_
    refine List.perm_middle.trans (List.Perm.cons _ ?_)
    rw [← List.append_assoc]
    refine List.perm_middle.trans (List.Perm.cons _ ?_)
    rw [List.append_assoc]
    exact ih

lemma map_reqsE_perm (e : Fin I.schemas.length) :
    ((reqsE I e).map (ansF I)).Perm (ansE I e) := by
  have hstep : (reqsE I e).map (ansF I) =
      ((schLocs (sch I e)).zip (schPerms (sch I e))).zipIdx.flatMap fun p =>
        (coordList (dom I e)).zipIdx.map fun q => ansU I p.1.1 (p.1.2.apply q.1)
          (ansBase I e + seqOff (Matrix.isTern (sch I e)) (coordList (dom I e)).length p.2 q.2) := by
    rw [reqsE, List.map_flatMap]
    refine List.flatMap_congr fun p hp => ?_
    rw [List.map_map]
    refine List.map_congr_left fun q hq => ?_
    exact ansF_req I (List.fst_mem_of_mem_zipIdx hp)
      (mem_coordList.mp (List.fst_mem_of_mem_zipIdx hq)) _
  rw [hstep]
  unfold ansE dom
  cases h : sch I e with
  | binary u v D σ τ =>
    simp only [schLocs, schPerms, List.zip_cons_cons, List.zip_nil_right, List.zipIdx_cons,
      List.zipIdx_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, Matrix.isTern,
      seqOff, Schema.domain, ansU_fin, Bool.false_eq_true, if_false, if_true]
    refine List.perm_append_comm.trans (List.Perm.of_eq ?_)
    congr 1
    refine List.map_congr_left fun q _ => ?_
    simp [add_assoc]
  | ternary u v w' D σ τ π =>
    simp only [schLocs, schPerms, List.zip_cons_cons, List.zip_nil_right, List.zipIdx_cons,
      List.zipIdx_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, Matrix.isTern,
      seqOff, Schema.domain, ansU_fin, if_true]
    refine List.Perm.trans (List.Perm.of_eq ?_) (perm3 _ _ _ _)
    simp [add_assoc]

lemma map_reqs_perm : ((reqs I).map (ansF I)).Perm (ansAll I) := by
  rw [reqs, List.map_flatMap]
  exact List.Perm.flatMap_left _ fun e _ => map_reqsE_perm I e

lemma length_reqs_eq : (reqs I).length = (ansAll I).length := by
  rw [← (map_reqs_perm I).length_eq, List.length_map]

/-! ## Sequence numbers -/

lemma map_zipIdx_add {α : Type*} (l : List α) (b : ℕ) :
    l.zipIdx.map (fun q => b + q.2) = List.range' b l.length := by
  have : l.zipIdx.map (fun q => b + q.2) = (l.zipIdx.map Prod.snd).map (b + ·) := by
    rw [List.map_map]; rfl
  rw [this, List.zipIdx_map_snd, List.map_add_range', add_zero]

lemma flatMap_zipIdx_three {α : Type*} (b : ℕ) : ∀ (l : List α) (i : ℕ),
    (l.zipIdx i).flatMap (fun q => [b + 3 * q.2, b + 3 * q.2 + 1, b + 3 * q.2 + 2]) =
      List.range' (b + 3 * i) (3 * l.length)
  | [], _ => by simp
  | a :: t, i => by
    rw [List.zipIdx_cons, List.flatMap_cons, flatMap_zipIdx_three b t (i + 1)]
    rw [show 3 * (a :: t).length = 3 * t.length + 1 + 1 + 1 by simp; ring]
    simp only [List.range'_succ, List.cons_append, List.nil_append]
    congr 3

lemma map_head_ansE (e : Fin I.schemas.length) :
    (ansE I e).map (·.headD 0) =
      List.range' (ansBase I e) (arity (sch I e) * (coordList (dom I e)).length) := by
  unfold ansE dom
  cases h : sch I e with
  | binary u v D σ τ =>
    simp only [List.map_append, List.map_map, Function.comp_def, ansRec, List.headD_cons,
      arity, Matrix.isTern, Schema.domain, Bool.false_eq_true, if_false]
    rw [map_zipIdx_add, map_zipIdx_add, List.range'_append_1]
    congr 1; ring
  | ternary u v w' D σ τ π =>
    simp only [List.map_flatMap, List.map_cons, List.map_nil, ansRec, List.headD_cons,
      arity, Matrix.isTern, Schema.domain, if_true]
    rw [flatMap_zipIdx_three, mul_zero, add_zero]

lemma ansBase_zero : ansBase I 0 = 0 := by simp [ansBase]

lemma ansBase_succ {j : ℕ} (hj : j < I.schemas.length) :
    ansBase I (j + 1) = ansBase I j +
      arity (sch I ⟨j, hj⟩) * (coordList (dom I ⟨j, hj⟩)).length := by
  rw [ansBase, List.take_add_one, List.getElem?_eq_getElem (by simpa using hj)]
  simp [ansBase]

lemma map_head_upTo : ∀ j, j ≤ I.schemas.length →
    (((List.finRange I.schemas.length).take j).flatMap (ansE I)).map (·.headD 0) =
      List.range' 0 (ansBase I j)
  | 0, _ => by simp [ansBase_zero]
  | j + 1, hj => by
    rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hj)]
    simp only [List.getElem_finRange, Option.toList_some, List.flatMap_append,
      List.flatMap_singleton, List.map_append, Fin.cast_mk]
    rw [map_head_upTo j (by omega), map_head_ansE, ansBase_succ I (by omega)]
    have := List.range'_append_1 (s := 0) (m := ansBase I j)
      (n := arity (sch I ⟨j, by omega⟩) * (coordList (dom I ⟨j, by omega⟩)).length)
    rw [zero_add] at this
    convert this using 2

/-- **The sequence numbers** of `ansAll I` are `0, 1, …, ansBase I E - 1`. -/
theorem map_head_ansAll :
    (ansAll I).map (·.headD 0) = List.range (ansBase I I.schemas.length) := by
  rw [ansAll, ← List.take_of_length_le (l := List.finRange _) (le_of_eq (List.length_finRange)),
    map_head_upTo I _ le_rfl, List.range_eq_range']

lemma length_of_mem_ansAll {a : List ℕ} (ha : a ∈ ansAll I) : a.length = 4 := by
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp ((map_reqs_perm I).mem_iff.mpr ha)
  exact length_ansF I r

lemma pairwise_ansAll : (ansAll I).Pairwise fun a b => CSort.rle a b = true := by
  have h := List.pairwise_lt_range (n := ansBase I I.schemas.length)
  rw [← map_head_ansAll, List.pairwise_map] at h
  refine h.imp_of_mem fun {a b} ha hb hab => ?_
  match a, b, length_of_mem_ansAll I ha, length_of_mem_ansAll I hb with
  | x :: as, y :: bs, _, _ =>
    simp only [List.headD_cons] at hab
    simp [CSort.rle, hab]

/-! ## The join -/

/-- **The answers of the join.** For any permutation `L0` of the location records and the
requests, the scan over `L0` sorted by `rle`, with its answers (pushed in reverse order) sorted
by `rle`, gives the answers in the order of `P4`. -/
theorem p3_answers (L0 : List (List ℕ)) (hp : L0.Perm (union I)) (c0 : ℕ × ℕ × ℕ) :
    (jScan ℓ c0 (L0.mergeSort CSort.rle)).reverse.mergeSort CSort.rle = ansAll I := by
  set S := L0.mergeSort CSort.rle
  have hS : S.Perm (union I) := (List.mergeSort_perm _ _).trans hp
  have hsorted : S.Pairwise fun a b => CSort.rle a b = true :=
    List.pairwise_mergeSort CSort.rle_trans (fun a b => by
      rcases CSort.rle_total a b with h | h <;> simp [h]) L0
  have hscan := Join.scanF_eq (ℓ + 2) (jCur ℓ) (jAns ℓ) (gLoc I) S
    (fun r hr => by rw [length_of_mem_union I (hS.mem_iff.mp hr)]; omega)
    (fun m hm hl => hG1 I m (hS.mem_iff.mp hm) hl)
    (fun r hr hl => by
      obtain ⟨m, hm, h1, h2⟩ := hG2 I r (hS.mem_iff.mp hr) hl
      exact ⟨m, hS.mem_iff.mpr hm, h1, h2⟩) hsorted c0
  have hfilt : (S.filter fun r => !Join.isLoc (ℓ + 2) r).Perm (reqs I) := by
    refine (hS.filter _).trans (List.Perm.of_eq ?_)
    rw [union, List.filter_append, List.filter_eq_nil_iff.mpr, List.filter_eq_self.mpr,
      List.nil_append]
    · intro r hr
      obtain ⟨e, p, -, c, -, s, rfl⟩ := mem_reqs I hr
      simp [isLoc_reqRec]
    · intro r hr
      obtain ⟨v, c, -, rfl⟩ := (mem_locRecs I).mp hr
      simp [isLoc_locRecC]
  have hperm : (jScan ℓ c0 S).reverse.Perm (ansAll I) := by
    refine (List.reverse_perm _).trans ?_
    rw [jScan, hscan]
    exact (hfilt.map (ansF I)).trans (map_reqs_perm I)
  exact (CSort.eq_sortedRecs hperm.symm (pairwise_ansAll I)).symm

end Lax119563Proofs.Compiler
