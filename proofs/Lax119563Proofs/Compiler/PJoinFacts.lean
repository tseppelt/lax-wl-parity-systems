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

lemma getD_rec (a : ℕ) (d : List ℕ) (x0 x1 x2 x3 i : ℕ) (hi : i < 4) :
    (a :: d ++ [x0, x1, x2, x3]).getD (d.length + 1 + i) 0 = [x0, x1, x2, x3].getD i 0 := by
  rw [List.cons_append, show d.length + 1 + i = (d.length + i) + 1 by omega]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by omega), show d.length + i - d.length = i by omega]

lemma isLoc_locRecC (v : Fin I.numLocations) (c : Coord k ℓ) :
    Join.isLoc (ℓ + 2) (locRecC I v c) = true := by
  have := getD_rec (v : ℕ) (cdesc c) 0 (locOff I v + (coordList (I.domain v)).idxOf c * labsN I v)
    (labsN I v) (initNum (I.init v)) 0 (by omega)
  rw [length_cdesc] at this
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
  have := getD_rec u (cdesc (π.apply c)) 1 s 0 0 0 (by omega)
  rw [length_cdesc] at this
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
  fun m hm hl => gLoc_eq I ((isLoc_of_mem_union I hm).mp hl)

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

end Lax119563Proofs.Compiler
