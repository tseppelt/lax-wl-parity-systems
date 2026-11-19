import Lax119563Proofs.Compiler.PJoin
import Lax119563Proofs.Compiler.PReqLoopList

/-!
# Pass `P3`: list facts used by the assembly

* `Join.mem_scanF_cases`: every answer of the scan is `ansOf c r` for a record `r` of the list
  and `c` the start data or the data of a record of the list;
* `Join.length_scanF`: the scan gives one answer per request;
* `length_locRec`, `length_reqRec`, `isLoc_locRec`, `isLoc_reqRec`: the union records have
  `ℓ + 6` words, tag `0` (locations) or `1` (requests);
* `p3Ans I`: the answers after the union sort, the scan and the sort by sequence number.
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

namespace Join

variable (K : ℕ) {α : Type*} (curOf : List ℕ → α) (ansOf : α → List ℕ → List ℕ)

lemma mem_scanF_cases : ∀ (c : α) (L : List (List ℕ)) (y : List ℕ),
    y ∈ scanF K curOf ansOf c L →
      ∃ r ∈ L, ∃ c', (c' = c ∨ ∃ m ∈ L, c' = curOf m) ∧ y = ansOf c' r
  | _, [], _, h => by simp [scanF] at h
  | c, x :: rs, y, h => by
    simp only [scanF] at h
    split_ifs at h with hx
    · obtain ⟨r, hr, c', hc', rfl⟩ := mem_scanF_cases (curOf x) rs y h
      refine ⟨r, List.mem_cons_of_mem _ hr, c', ?_, rfl⟩
      rcases hc' with rfl | ⟨m, hm, rfl⟩
      · exact Or.inr ⟨x, by simp, rfl⟩
      · exact Or.inr ⟨m, List.mem_cons_of_mem _ hm, rfl⟩
    · rcases List.mem_cons.mp h with rfl | h
      · exact ⟨x, by simp, c, Or.inl rfl, rfl⟩
      · obtain ⟨r, hr, c', hc', rfl⟩ := mem_scanF_cases c rs y h
        refine ⟨r, List.mem_cons_of_mem _ hr, c', ?_, rfl⟩
        rcases hc' with rfl | ⟨m, hm, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨m, List.mem_cons_of_mem _ hm, rfl⟩

lemma length_scanF : ∀ (c : α) (L : List (List ℕ)),
    (scanF K curOf ansOf c L).length = (L.filter fun r => !isLoc K r).length
  | _, [] => rfl
  | c, x :: rs => by
    simp only [scanF, List.filter_cons]
    split_ifs with hx <;> simp_all [length_scanF]

end Join

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

lemma length_locRec (v : Fin I.numLocations) (r : ℕ) : (locRec I v r).length = ℓ + 6 := by
  simp [locRec, length_cnd]

lemma length_reqRec (u : ℕ) (π : BlockPerm k ℓ) (c : Coord k ℓ) (s : ℕ) :
    (reqRec u π c s).length = ℓ + 6 := by
  simp [reqRec, length_cdesc]

lemma isLoc_locRec (v : Fin I.numLocations) (r : ℕ) : Join.isLoc (ℓ + 2) (locRec I v r) = true := by
  have h : locRec I v r = ((v : ℕ) :: coordNumDescription ℓ ((locNums I v).getD r 0)) ++
      [0, locOff I v + r * labsN I v, labsN I v, initNum (I.init v)] := rfl
  rw [Join.isLoc, h, List.getD_append_right _ _ _ _ (by simp [length_cnd])]
  simp [length_cnd]

lemma isLoc_reqRec (u : ℕ) (π : BlockPerm k ℓ) (c : Coord k ℓ) (s : ℕ) :
    Join.isLoc (ℓ + 2) (reqRec u π c s) = false := by
  have h : reqRec u π c s = (u :: cdesc (π.apply c)) ++ [1, s, 0, 0] := rfl
  rw [Join.isLoc, h, List.getD_append_right _ _ _ _ (by simp [length_cdesc])]
  simp [length_cdesc]

lemma mem_locRecs {m : List ℕ} (hm : m ∈ locRecs I) : ∃ v r, m = locRec I v r := by
  simp only [locRecs, recsV, List.mem_flatMap, List.mem_map] at hm
  obtain ⟨v, -, r, -, rfl⟩ := hm
  exact ⟨v, r, rfl⟩

lemma mem_reqs {m : List ℕ} (hm : m ∈ reqs I) : ∃ (u : ℕ) (π : BlockPerm k ℓ) (c : Coord k ℓ) (s : ℕ), m = reqRec u π c s := by
  simp only [reqs, reqsE, List.mem_flatMap, List.mem_map] at hm
  obtain ⟨e, -, p, -, q, -, rfl⟩ := hm
  exact ⟨_, _, _, _, rfl⟩

lemma length_union {m : List ℕ} (hm : m ∈ locRecs I ++ reqs I) : m.length = ℓ + 6 := by
  rcases List.mem_append.mp hm with h | h
  · obtain ⟨v, r, rfl⟩ := mem_locRecs I h; exact length_locRec I v r
  · obtain ⟨u, π, c, s, rfl⟩ := mem_reqs I h; exact length_reqRec u π c s

lemma filter_union :
    ((locRecs I ++ reqs I).filter fun r => !Join.isLoc (ℓ + 2) r).length = (reqs I).length := by
  rw [List.filter_append, List.length_append]
  have h1 : (locRecs I).filter (fun r => !Join.isLoc (ℓ + 2) r) = [] :=
    List.filter_eq_nil_iff.mpr fun m hm => by
      obtain ⟨v, r, rfl⟩ := mem_locRecs I hm; simp [isLoc_locRec]
  have h2 : (reqs I).filter (fun r => !Join.isLoc (ℓ + 2) r) = reqs I :=
    List.filter_eq_self.mpr fun m hm => by
      obtain ⟨u, π, c, s, rfl⟩ := mem_reqs I hm; simp [isLoc_reqRec]
  rw [h1, h2]; simp

lemma length_flatten_union :
    (locRecs I ++ reqs I).flatten.length = ((locRecs I).length + (reqs I).length) * (ℓ + 6) := by
  rw [List.length_flatten]
  have : (locRecs I ++ reqs I).map List.length = (locRecs I ++ reqs I).map fun _ => ℓ + 6 :=
    List.map_congr_left fun m hm => length_union I hm
  rw [this, sum_map_const, List.length_append]

lemma union_mul_le : ((locRecs I).length + (reqs I).length) * (ℓ + 1) ≤ 4 * H I := by
  have h1 := length_locRecs_mul_le I
  have h2 := length_reqs_mul_le I
  nlinarith

/-- The sorted union of the location records and the requests. -/
noncomputable def p3Union : List (List ℕ) := (locRecs I ++ reqs I).mergeSort CSort.rle

/-- The answers of the scan (in scan order, i.e. the order of the sorted union). -/
noncomputable def p3Scan : List (List ℕ) := jScan ℓ (0, 0, 0) (p3Union I)

/-- **The answers of `P3`**: sorted by `CSort.rle` (i.e. by sequence number first). -/
noncomputable def p3Ans : List (List ℕ) := (p3Scan I).reverse.mergeSort CSort.rle

lemma length_p3Scan : (p3Scan I).length = (reqs I).length := by
  rw [p3Scan, jScan, Join.length_scanF, ← filter_union I]
  exact ((List.mergeSort_perm _ _).filter _).length_eq

lemma mem_p3Union {m : List ℕ} : m ∈ p3Union I ↔ m ∈ locRecs I ++ reqs I :=
  (List.mergeSort_perm _ _).mem_iff

lemma length_p3Union : (p3Union I).length = (locRecs I).length + (reqs I).length := by
  rw [p3Union, List.length_mergeSort, List.length_append]

/-- The answers have four words, each bounded by the bound `B` of the union records. -/
lemma p3Scan_words {B : ℕ} (hB : ∀ m ∈ locRecs I ++ reqs I, ∀ v ∈ m, v ≤ B) (h1 : 1 ≤ B) :
    ∀ y ∈ p3Scan I, y.length = 4 ∧ ∀ z ∈ y, z ≤ B := by
  intro y hy
  obtain ⟨r, hr, c', hc', rfl⟩ := Join.mem_scanF_cases (ℓ + 2) (jCur ℓ) (jAns ℓ) _ _ y hy
  have hgd : ∀ m ∈ p3Union I, ∀ i, m.getD i 0 ≤ B := by
    intro m hm i
    rw [List.getD_eq_getElem?_getD]
    cases h : m[i]? with
    | none => simp
    | some v => exact hB m ((mem_p3Union I).mp hm) v (List.mem_of_getElem? h)
  refine ⟨rfl, ?_⟩
  have hc : c'.1 ≤ B ∧ c'.2.1 ≤ B ∧ c'.2.2 ≤ B := by
    rcases hc' with rfl | ⟨m, hm, rfl⟩
    · simp
    · exact ⟨hgd m hm _, hgd m hm _, (seedV_le _ _).trans h1⟩
  simp only [jAns, List.mem_cons, List.not_mem_nil, or_false]
  rintro z (rfl | rfl | rfl | rfl)
  · exact hgd r hr _
  · exact hc.1
  · exact hc.2.1
  · exact hc.2.2

lemma pairwise_p3Union : (p3Union I).Pairwise fun a b => CSort.rle a b = true :=
  List.pairwise_mergeSort (fun a b c h1 h2 => CSort.rle_trans a b c h1 h2)
    (fun a b => by rcases CSort.rle_total a b with h | h <;> simp [h]) _

/-- **The scan answers every request from its own location record** (`Join.scanF_eq`), given
the list facts `hG1` (a location record is determined by its key, via `g`) and `hG2` (every
request has a location record with its key). -/
theorem p3Scan_eq (g : List ℕ → List ℕ)
    (hG1 : ∀ m ∈ locRecs I, g (m.take (ℓ + 2)) = m)
    (hG2 : ∀ r ∈ reqs I, ∃ m ∈ locRecs I, m.take (ℓ + 2) = r.take (ℓ + 2)) :
    p3Scan I = ((p3Union I).filter fun r => !Join.isLoc (ℓ + 2) r).map
      fun r => jAns ℓ (jCur ℓ (g (r.take (ℓ + 2)))) r := by
  have hloc : ∀ m ∈ p3Union I, Join.isLoc (ℓ + 2) m = true → m ∈ locRecs I := by
    intro m hm hl
    rcases List.mem_append.mp ((mem_p3Union I).mp hm) with h | h
    · exact h
    · obtain ⟨u, π, c, s, rfl⟩ := mem_reqs I h; simp [isLoc_reqRec] at hl
  have hreq : ∀ m ∈ p3Union I, Join.isLoc (ℓ + 2) m = false → m ∈ reqs I := by
    intro m hm hl
    rcases List.mem_append.mp ((mem_p3Union I).mp hm) with h | h
    · obtain ⟨v, r, rfl⟩ := mem_locRecs I h; simp [isLoc_locRec] at hl
    · exact h
  refine Join.scanF_eq (ℓ + 2) (jCur ℓ) (jAns ℓ) g (p3Union I)
    (fun r hr => by rw [length_union I ((mem_p3Union I).mp hr)]; omega)
    (fun m hm hl => hG1 m (hloc m hm hl)) (fun r hr hl => ?_) (pairwise_p3Union I) _
  obtain ⟨m, hm, hk⟩ := hG2 r (hreq r hr hl)
  refine ⟨m, (mem_p3Union I).mpr (List.mem_append_left _ hm), ?_, hk⟩
  obtain ⟨v, r', rfl⟩ := mem_locRecs I hm
  exact isLoc_locRec I v r'

end Lax119563Proofs.Compiler
