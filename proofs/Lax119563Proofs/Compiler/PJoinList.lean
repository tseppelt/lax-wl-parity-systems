import Lax119563Proofs.Compiler.CSortList

/-!
# The join of pass `P3`: the list level

Records are lists `key ++ tag :: data` with a key of `K` words. *Location records* have tag
`0` (`isLoc`), *requests* a nonzero tag. After sorting the union of both kinds by `CSort.rle`,
every request is preceded by the location record with the same key, and no other location
record lies in between. So a single scan (`scanF`), which remembers the data `curOf m` of the
last location record `m` and answers each request `r` with `ansOf (curOf m) r`, answers every
request from its own location record (**`scanF_eq`**), without comparing keys.
-/

namespace Lax119563Proofs.Compiler.Join

open CSort

/-! ## The lexicographic order on records -/

lemma rle_append_same : ∀ (a s t : List ℕ), rle (a ++ s) (a ++ t) = rle s t
  | [], _, _ => rfl
  | x :: a, s, t => by simp [rle, rle_append_same a s t]

lemma rle_prefix : ∀ (a b s t : List ℕ), a.length = b.length →
    rle (a ++ s) (b ++ t) = true → rle a b = true
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | x :: a, y :: b, s, t, h, h' => by
    simp only [List.cons_append, rle, Bool.or_eq_true, decide_eq_true_eq,
      Bool.and_eq_true] at h' ⊢
    rcases h' with h' | ⟨rfl, h'⟩
    · left; exact h'
    · right; exact ⟨rfl, rle_prefix a b s t (by simpa using h) h'⟩

variable (K : ℕ)

/-- Location records have tag `0`. -/
def isLoc (r : List ℕ) : Bool := r.getD K 0 == 0

lemma split_rec {r : List ℕ} (h : K < r.length) :
    r = r.take K ++ (r.getD K 0 :: r.drop (K + 1)) := by
  rw [List.getD_eq_getElem _ _ h]
  conv_lhs => rw [← List.take_append_drop K r, List.drop_eq_getElem_cons h]

lemma rle_key {a b : List ℕ} (ha : K < a.length) (hb : K < b.length) (h : rle a b = true) :
    rle (a.take K) (b.take K) = true := by
  rw [split_rec K ha, split_rec K hb] at h
  exact rle_prefix _ _ _ _ (by simp; omega) h

/-- A record between two records with the same key has that key. -/
lemma key_between {m x r : List ℕ} (hm : K < m.length) (hx : K < x.length) (hr : K < r.length)
    (h₁ : rle m x = true) (h₂ : rle x r = true) (hk : m.take K = r.take K) :
    x.take K = m.take K := by
  have e1 := rle_key K hm hx h₁
  have e2 := rle_key K hx hr h₂
  rw [← hk] at e2
  exact rle_antisymm _ _ e2 e1

/-- A request is not below the location record with its key. -/
lemma not_rle_req_loc {x m : List ℕ} (hx : K < x.length) (hm : K < m.length)
    (hxl : isLoc K x = false) (hml : isLoc K m = true) (hk : x.take K = m.take K) :
    rle x m = false := by
  simp only [isLoc, beq_iff_eq, beq_eq_false_iff_ne, ne_eq] at hxl hml
  rw [split_rec K hx, split_rec K hm, hk, rle_append_same, hml]
  cases hx' : x.getD K 0 with
  | zero => exact absurd hx' hxl
  | succ n => simp [rle]

/-! ## The scan -/

variable {α : Type*} (curOf : List ℕ → α) (ansOf : α → List ℕ → List ℕ)

/-- The scan: location records set the current data, requests are answered with it. -/
def scanF : α → List (List ℕ) → List (List ℕ)
  | _, [] => []
  | c, r :: rs => if isLoc K r then scanF (curOf r) rs else ansOf c r :: scanF c rs

/-- The current data after scanning a list. -/
def curAfter : α → List (List ℕ) → α
  | c, [] => c
  | c, r :: rs => curAfter (if isLoc K r then curOf r else c) rs

lemma scanF_append_single (c : α) (L : List (List ℕ)) (r : List ℕ) :
    scanF K curOf ansOf c (L ++ [r]) = scanF K curOf ansOf c L ++
      (if isLoc K r then [] else [ansOf (curAfter K curOf c L) r]) := by
  induction L generalizing c with
  | nil => by_cases h : isLoc K r <;> simp [scanF, curAfter, h]
  | cons x L ih =>
    simp only [List.cons_append, scanF, curAfter]
    by_cases h : isLoc K x <;> simp only [h, if_true, if_false, Bool.false_eq_true] <;>
      rw [ih] <;> simp

lemma curAfter_append_single (c : α) (L : List (List ℕ)) (r : List ℕ) :
    curAfter K curOf c (L ++ [r]) =
      if isLoc K r then curOf r else curAfter K curOf c L := by
  induction L generalizing c with
  | nil => rfl
  | cons x L ih => simp only [List.cons_append, curAfter]; exact ih _

lemma curAfter_cases (c : α) (L : List (List ℕ)) :
    curAfter K curOf c L = c ∨ ∃ m ∈ L, curAfter K curOf c L = curOf m := by
  induction L generalizing c with
  | nil => left; rfl
  | cons x L ih =>
    simp only [curAfter]
    rcases ih (if isLoc K x then curOf x else c) with h | ⟨m, hm, h⟩
    · rw [h]; split_ifs
      · right; exact ⟨x, by simp, rfl⟩
      · left; rfl
    · right; exact ⟨m, by simp [hm], h⟩

/-- **The join by a scan.** In a sorted list of records in which location records are
determined by their keys (`g`) and every request has a location record with its key, the
scan answers every request `r` with the data of `g (key r)`. -/
theorem scanF_eq (g : List ℕ → List ℕ) (L0 : List (List ℕ))
    (hlen : ∀ r ∈ L0, K < r.length)
    (hG1 : ∀ m ∈ L0, isLoc K m = true → g (m.take K) = m)
    (hG2 : ∀ r ∈ L0, isLoc K r = false → ∃ m ∈ L0, isLoc K m = true ∧ m.take K = r.take K)
    (hs : L0.Pairwise fun a b => rle a b = true) (c0 : α) :
    scanF K curOf ansOf c0 L0 =
      (L0.filter fun r => !isLoc K r).map fun r => ansOf (curOf (g (r.take K))) r := by
  -- the matching location record of a request
  have hM : ∀ r ∈ L0, isLoc K r = false →
      g (r.take K) ∈ L0 ∧ isLoc K (g (r.take K)) = true ∧ (g (r.take K)).take K = r.take K := by
    intro r hr hrl
    obtain ⟨m, hm, hml, hk⟩ := hG2 r hr hrl
    rw [← hk, hG1 m hm hml]
    exact ⟨hm, hml, rfl⟩
  suffices H : ∀ (L : List (List ℕ)) (c : α), (∀ r ∈ L, r ∈ L0) →
      L.Pairwise (fun a b => rle a b = true) →
      (∀ r ∈ L, isLoc K r = false → g (r.take K) ∈ L ∨
        (c = curOf (g (r.take K)) ∧ ∀ y ∈ L, rle (g (r.take K)) y = true)) →
      scanF K curOf ansOf c L =
        (L.filter fun r => !isLoc K r).map fun r => ansOf (curOf (g (r.take K))) r by
    refine H L0 c0 (fun r hr => hr) hs (fun r hr hrl => Or.inl (hM r hr hrl).1)
  intro L
  induction L with
  | nil => intro c _ _ _; rfl
  | cons x rs ih =>
    intro c hsub hP hI
    have hx0 : x ∈ L0 := hsub x (by simp)
    have hsub' : ∀ r ∈ rs, r ∈ L0 := fun r hr => hsub r (by simp [hr])
    obtain ⟨hxrs, hP'⟩ := List.pairwise_cons.mp hP
    cases hxl : isLoc K x with
    | true =>
      rw [scanF, if_pos hxl, List.filter_cons_of_neg (by simp [hxl])]
      refine ih (curOf x) hsub' hP' fun r hr hrl => ?_
      have hr0 := hsub' r hr
      obtain ⟨hm0, hml, hk⟩ := hM r hr0 hrl
      rcases hI r (by simp [hr]) hrl with hm | ⟨-, hle⟩
      · rcases List.mem_cons.mp hm with he | he
        · right
          refine ⟨by rw [he], fun y hy => ?_⟩
          rw [he]; exact hxrs y hy
        · left; exact he
      · right
        have hkx := key_between K (hlen _ hm0) (hlen _ hx0) (hlen _ hr0)
          (hle x (by simp)) (hxrs r hr) hk
        have hxe : x = g (r.take K) := by rw [← hG1 x hx0 hxl, hkx, hk]
        exact ⟨by rw [← hxe], fun y hy => hle y (by simp [hy])⟩
    | false =>
      rw [scanF, if_neg (by simp [hxl]), List.filter_cons_of_pos (by simp [hxl]), List.map_cons]
      obtain ⟨hm0, hml, hk⟩ := hM x hx0 hxl
      have hc : c = curOf (g (x.take K)) := by
        rcases hI x (by simp) hxl with hm | ⟨hc, -⟩
        · exfalso
          rcases List.mem_cons.mp hm with he | he
          · rw [he] at hml; rw [hml] at hxl; exact Bool.noConfusion hxl
          · have h1 := hxrs _ he
            rw [not_rle_req_loc K (hlen _ hx0) (hlen _ hm0) hxl hml hk.symm] at h1
            exact Bool.noConfusion h1
        · exact hc
      rw [hc]
      congr 1
      rw [← hc]
      refine ih c hsub' hP' fun r hr hrl => ?_
      rcases hI r (by simp [hr]) hrl with hm | ⟨hc', hle⟩
      · rcases List.mem_cons.mp hm with he | he
        · exfalso
          have := (hM r (hsub' r hr) hrl).2.1
          rw [he, hxl] at this; exact Bool.noConfusion this
        · left; exact he
      · right; exact ⟨hc', fun y hy => hle y (by simp [hy])⟩

end Lax119563Proofs.Compiler.Join
