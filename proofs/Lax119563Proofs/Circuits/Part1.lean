import Lax119563.DeterministicTime
import Lax119563Proofs.Programs.Part1
import Mathlib

/-! ### Formerly `Lax119563Proofs.Compiler.CSortList` -/

section Compiler_CSortList

/-!
# Merge sort of records: the list level

Records are lists of naturals, compared lexicographically (`rle`, a linear order). The
stack program of `Compiler.CSort` sorts by bottom-up merge passes:

* `mrg d u v acc`: merge the record lists `u`, `v` (sorted descending for `ordD d`), always
  pushing the larger top record onto `acc` (`mrg_pairwise`, `mrg_perm`);
* `passX d r rs`: merge consecutive runs of `r` records pairwise; the runs of the result
  have length `2 r` and are sorted for the opposite direction (`passX_chunkSorted`);
* `sortedRecs rs = rs.mergeSort rle` is the unique sorted permutation (`eq_sortedRecs`).
-/

namespace Lax119563Proofs.Compiler.CSort

/-! ## The lexicographic order -/

/-- Lexicographic `≤` on lists of naturals. -/
def rle : List ℕ → List ℕ → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => decide (a < b) || (decide (a = b) && rle as bs)

lemma rle_total : ∀ a b : List ℕ, rle a b = true ∨ rle b a = true
  | [], _ => Or.inl rfl
  | _ :: _, [] => Or.inr rfl
  | a :: as, b :: bs => by
    rcases lt_trichotomy a b with h | rfl | h
    · left; simp [rle, h]
    · rcases rle_total as bs with h | h <;> simp [rle, h]
    · right; simp [rle, h]

lemma rle_trans : ∀ a b c : List ℕ, rle a b = true → rle b c = true → rle a c = true
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [rle] at h
  | _ :: _, _ :: _, [], _, h => by simp [rle] at h
  | a :: as, b :: bs, c :: cs, h₁, h₂ => by
    simp only [rle, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h₁ h₂ ⊢
    rcases h₁ with h₁ | ⟨rfl, h₁⟩ <;> rcases h₂ with h₂ | ⟨rfl, h₂⟩
    · left; omega
    · left; exact h₁
    · left; exact h₂
    · right; exact ⟨rfl, rle_trans as bs cs h₁ h₂⟩

lemma rle_antisymm : ∀ a b : List ℕ, rle a b = true → rle b a = true → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [rle] at h
  | _ :: _, [], h, _ => by simp [rle] at h
  | a :: as, b :: bs, h₁, h₂ => by
    simp only [rle, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h₁ h₂
    rcases h₁ with h₁ | ⟨rfl, h₁⟩
    · rcases h₂ with h₂ | ⟨rfl, _⟩ <;> omega
    · rcases h₂ with h₂ | ⟨_, h₂⟩
      · omega
      · rw [rle_antisymm as bs h₁ h₂]

/-! ## Word-by-word comparison -/

/-- The comparison state after one more pair of words: `0` equal so far, `1` less, `2`
greater. -/
def cmpStep (d a b : ℕ) : ℕ := if d = 0 then (if a < b then 1 else if b < a then 2 else 0) else d

/-- The comparison of two lists word by word, from the state `d`. -/
def cmpW : ℕ → List ℕ → List ℕ → ℕ
  | d, a :: as, b :: bs => cmpW (cmpStep d a b) as bs
  | d, _, _ => d

lemma cmpW_ne_zero : ∀ (d : ℕ) (as bs : List ℕ), d ≠ 0 → cmpW d as bs = d
  | d, a :: as, b :: bs, h => by
    rw [cmpW, cmpW_ne_zero _ as bs (by simp [cmpStep, h])]; simp [cmpStep, h]
  | _, [], _, _ => rfl
  | _, _ :: _, [], _ => rfl

lemma cmpW_take_succ (d : ℕ) : ∀ (as bs : List ℕ) (j : ℕ) (h₁ : j < as.length) (h₂ : j < bs.length),
    cmpW d (as.take (j + 1)) (bs.take (j + 1)) = cmpStep (cmpW d (as.take j) (bs.take j)) as[j] bs[j]
  | a :: as, b :: bs, 0, _, _ => by simp [cmpW]
  | a :: as, b :: bs, j + 1, h₁, h₂ => by
    simp only [List.take_succ_cons, cmpW, List.getElem_cons_succ]
    exact cmpW_take_succ _ as bs j (by simpa using h₁) (by simpa using h₂)

/-- For lists of equal length, `rle` is `cmpW ≠ 2`. -/
lemma rle_iff_cmpW : ∀ (as bs : List ℕ), as.length = bs.length →
    (rle as bs = true ↔ cmpW 0 as bs ≠ 2)
  | [], [], _ => by simp [rle, cmpW]
  | a :: as, b :: bs, h => by
    simp only [List.length_cons, add_left_inj] at h
    simp only [rle, cmpW, cmpStep, if_true, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
    rcases lt_trichotomy a b with hab | rfl | hab
    · simp [hab, cmpW_ne_zero]
    · simp [rle_iff_cmpW as bs h]
    · simp [hab, show ¬ a < b by omega, show a ≠ b by omega, cmpW_ne_zero]

/-! ## Merging -/

/-- The order of the merge direction: `rle` (`d = false`) or its flip (`d = true`). -/
def ordD (d : Bool) (a b : List ℕ) : Bool := if d then rle b a else rle a b

lemma ordD_total (d : Bool) (a b : List ℕ) : ordD d a b = true ∨ ordD d b a = true := by
  cases d <;> simp [ordD, rle_total]

lemma ordD_trans (d : Bool) (a b c : List ℕ) (h₁ : ordD d a b = true) (h₂ : ordD d b c = true) :
    ordD d a c = true := by
  cases d
  · exact rle_trans _ _ _ h₁ h₂
  · exact rle_trans _ _ _ h₂ h₁

lemma ordD_not (d : Bool) (a b : List ℕ) : ordD (!d) a b = ordD d b a := by
  cases d <;> rfl

/-- Merge from the larger ends: `u` and `v` are sorted descending, the larger top record is
pushed onto `acc`. -/
def mrg (d : Bool) : List (List ℕ) → List (List ℕ) → List (List ℕ) → List (List ℕ)
  | [], v, acc => v.reverse ++ acc
  | a :: u, [], acc => (a :: u).reverse ++ acc
  | a :: u, b :: v, acc =>
    if ordD d b a then mrg d u (b :: v) (a :: acc) else mrg d (a :: u) v (b :: acc)
termination_by u v => u.length + v.length

/-- One step of the merge. -/
def mrgStep (d : Bool) : List (List ℕ) × List (List ℕ) × List (List ℕ) →
    List (List ℕ) × List (List ℕ) × List (List ℕ)
  | ([], b :: v, acc) => ([], v, b :: acc)
  | (a :: u, [], acc) => (u, [], a :: acc)
  | (a :: u, b :: v, acc) => if ordD d b a then (u, b :: v, a :: acc) else (a :: u, v, b :: acc)
  | ([], [], acc) => ([], [], acc)

lemma mrg_step (d : Bool) (u v acc : List (List ℕ)) (h : u ≠ [] ∨ v ≠ []) :
    mrg d u v acc = mrg d (mrgStep d (u, v, acc)).1 (mrgStep d (u, v, acc)).2.1
      (mrgStep d (u, v, acc)).2.2 := by
  rcases u with _ | ⟨a, u⟩ <;> rcases v with _ | ⟨b, v⟩
  · simp at h
  · simp [mrg, mrgStep]
  · simp only [mrgStep, mrg]
    rcases u with _ | ⟨a', u⟩ <;> simp [mrg]
  · simp only [mrgStep]; rw [mrg]; split_ifs <;> rfl

lemma mrgStep_length (d : Bool) (u v acc : List (List ℕ)) (h : u ≠ [] ∨ v ≠ []) :
    (mrgStep d (u, v, acc)).1.length + (mrgStep d (u, v, acc)).2.1.length + 1 =
      u.length + v.length := by
  rcases u with _ | ⟨a, u⟩ <;> rcases v with _ | ⟨b, v⟩
  · simp at h
  · simp [mrgStep]
  · simp [mrgStep]
  · simp only [mrgStep]; split_ifs <;> simp <;> omega

lemma mrg_nil (d : Bool) (acc : List (List ℕ)) : mrg d [] [] acc = acc := by simp [mrg]

lemma mrg_perm (d : Bool) : ∀ (u v acc : List (List ℕ)), (mrg d u v acc).Perm (u ++ v ++ acc)
  | [], v, acc => by simp only [mrg, List.nil_append]; exact (List.reverse_perm _).append_right _
  | a :: u, [], acc => by
    simp only [mrg, List.append_nil]
    exact (List.reverse_perm _).append_right _
  | a :: u, b :: v, acc => by
    rw [mrg]
    split_ifs
    · refine (mrg_perm d u (b :: v) (a :: acc)).trans ?_
      exact List.perm_iff_count.mpr fun z => by simp [List.count_append, List.count_cons]; omega
    · refine (mrg_perm d (a :: u) v (b :: acc)).trans ?_
      exact List.perm_iff_count.mpr fun z => by simp [List.count_append, List.count_cons]; omega
termination_by u v => u.length + v.length

lemma mrg_length (d : Bool) (u v acc : List (List ℕ)) :
    (mrg d u v acc).length = u.length + v.length + acc.length := by
  rw [(mrg_perm d u v acc).length_eq]; simp; omega

/-- Merging descending lists gives an ascending list. -/
lemma mrg_pairwise (d : Bool) : ∀ (u v acc : List (List ℕ)),
    u.Pairwise (fun a b => ordD d b a = true) → v.Pairwise (fun a b => ordD d b a = true) →
    acc.Pairwise (fun a b => ordD d a b = true) → (∀ x ∈ u ++ v, ∀ y ∈ acc, ordD d x y = true) →
    (mrg d u v acc).Pairwise (fun a b => ordD d a b = true)
  | [], v, acc, _, hv, hacc, hx => by
    simp only [mrg]
    refine List.pairwise_append.mpr ⟨List.pairwise_reverse.mpr hv, hacc, ?_⟩
    intro a ha b hb; exact hx a (by simpa using ha) b hb
  | a :: u, [], acc, hu, _, hacc, hx => by
    simp only [mrg]
    refine List.pairwise_append.mpr ⟨List.pairwise_reverse.mpr hu, hacc, ?_⟩
    intro a' ha b hb; exact hx a' (by simp at ha ⊢; tauto) b hb
  | a :: u, b :: v, acc, hu, hv, hacc, hx => by
    rw [mrg]
    rw [List.pairwise_cons] at hu hv
    split_ifs with hba
    · refine mrg_pairwise d u (b :: v) (a :: acc) hu.2 (List.pairwise_cons.mpr hv) ?_ ?_
      · exact List.pairwise_cons.mpr ⟨fun y hy => hx a (by simp) y hy, hacc⟩
      · intro z hz y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · rcases List.mem_append.mp hz with hz | hz
          · exact hu.1 z hz
          · rcases List.mem_cons.mp hz with rfl | hz
            · exact hba
            · exact ordD_trans d _ _ _ (hv.1 z hz) hba
        · exact hx z (by simp at hz ⊢; tauto) y hy
    · have hab : ordD d a b = true := (ordD_total d b a).resolve_left hba
      refine mrg_pairwise d (a :: u) v (b :: acc) (List.pairwise_cons.mpr hu) hv.2 ?_ ?_
      · exact List.pairwise_cons.mpr ⟨fun y hy => hx b (by simp) y hy, hacc⟩
      · intro z hz y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · rcases List.mem_append.mp hz with hz | hz
          · rcases List.mem_cons.mp hz with rfl | hz
            · exact hab
            · exact ordD_trans d _ _ _ (hu.1 z hz) hab
          · exact hv.1 z hz
        · exact hx z (by simp at hz ⊢; tauto) y hy
termination_by u v => u.length + v.length

/-! ## Passes -/

/-- One merge pass with run length `r`: the merged pairs of runs, each reversed (as they are
after moving them back record by record). -/
def passX (d : Bool) (r : ℕ) (rs : List (List ℕ)) : List (List ℕ) :=
  if h : r = 0 ∨ rs = [] then rs else
    (mrg d (rs.take r).reverse ((rs.drop r).take r).reverse []).reverse ++
      passX d r (rs.drop (2 * r))
termination_by rs.length
decreasing_by
  simp only [not_or] at h
  have : rs.length ≠ 0 := by simpa using h.2
  simp; omega

lemma passX_nil (d : Bool) (r : ℕ) : passX d r [] = [] := by
  rw [passX]; simp

lemma passX_cons (d : Bool) {r : ℕ} (hr : r ≠ 0) {rs : List (List ℕ)} (hrs : rs ≠ []) :
    passX d r rs = (mrg d (rs.take r).reverse ((rs.drop r).take r).reverse []).reverse ++
      passX d r (rs.drop (2 * r)) := by
  rw [passX, dif_neg (by simp [hr, hrs])]

lemma drop_drop_two (r : ℕ) (rs : List (List ℕ)) : (rs.drop r).drop r = rs.drop (2 * r) := by
  rw [List.drop_drop]; congr 1; omega

lemma split_three (r : ℕ) (rs : List (List ℕ)) :
    rs = rs.take r ++ ((rs.drop r).take r ++ rs.drop (2 * r)) := by
  rw [← drop_drop_two, List.take_append_drop, List.take_append_drop]

lemma passX_perm (d : Bool) (r : ℕ) (rs : List (List ℕ)) : (passX d r rs).Perm rs := by
  induction' hn : rs.length using Nat.strong_induction_on with n ih generalizing rs
  by_cases h : r = 0 ∨ rs = []
  · rw [passX, dif_pos h]
  · simp only [not_or] at h
    rw [passX_cons d h.1 h.2]
    have hlt : (rs.drop (2 * r)).length < n := by
      have : rs.length ≠ 0 := by simpa using h.2
      simp; omega
    have ih' := ih _ hlt (rs.drop (2 * r)) rfl
    refine ((List.reverse_perm _).append ih').trans ?_
    refine ((mrg_perm _ _ _ _).append_right _).trans ?_
    conv_rhs => rw [split_three r rs]
    exact List.perm_iff_count.mpr fun z => by simp [List.count_append]

lemma passX_length (d : Bool) (r : ℕ) (rs : List (List ℕ)) : (passX d r rs).length = rs.length :=
  (passX_perm d r rs).length_eq

/-! ## Sorted runs -/

/-- The runs of length `r` (the last one possibly shorter) are sorted for `ord`. -/
def ChunkSorted (ord : List ℕ → List ℕ → Bool) (r : ℕ) (rs : List (List ℕ)) : Prop :=
  ∀ i, ((rs.drop (i * r)).take r).Pairwise (fun a b => ord a b = true)

lemma chunkSorted_one (ord : List ℕ → List ℕ → Bool) (rs : List (List ℕ)) :
    ChunkSorted ord 1 rs := by
  intro i
  rcases rs.drop (i * 1) with _ | ⟨a, l⟩ <;> simp

lemma chunkSorted_drop {ord : List ℕ → List ℕ → Bool} {r : ℕ} {rs : List (List ℕ)}
    (h : ChunkSorted ord r rs) (k : ℕ) : ChunkSorted ord r (rs.drop (k * r)) := by
  intro i
  rw [List.drop_drop, ← add_mul]
  exact h _

lemma pairwise_of_chunkSorted {ord : List ℕ → List ℕ → Bool} {r : ℕ} {rs : List (List ℕ)}
    (h : ChunkSorted ord r rs) (hl : rs.length ≤ r) :
    rs.Pairwise (fun a b => ord a b = true) := by
  have := h 0
  rwa [zero_mul, List.drop_zero, List.take_of_length_le hl] at this

lemma passX_chunkSorted (d : Bool) {r : ℕ} (hr : r ≠ 0) (rs : List (List ℕ))
    (h : ChunkSorted (ordD d) r rs) : ChunkSorted (ordD (!d)) (2 * r) (passX d r rs) := by
  induction' hn : rs.length using Nat.strong_induction_on with n ih generalizing rs
  by_cases hrs : rs = []
  · subst hrs; intro i; simp [passX_nil]
  rw [passX_cons d hr hrs]
  set u := (rs.take r).reverse
  set v := ((rs.drop r).take r).reverse
  set B := (mrg d u v []).reverse
  have hu : u.Pairwise (fun a b => ordD d b a = true) := by
    have := h 0
    simp only [zero_mul, List.drop_zero] at this
    exact List.pairwise_reverse.mpr this
  have hv : v.Pairwise (fun a b => ordD d b a = true) := by
    have := h 1
    simp only [one_mul] at this
    exact List.pairwise_reverse.mpr this
  have hB : B.Pairwise (fun a b => ordD (!d) a b = true) := by
    refine List.pairwise_reverse.mpr ?_
    simp only [ordD_not]
    exact mrg_pairwise d u v [] hu hv List.Pairwise.nil (by simp)
  have hBl : B.length = min r rs.length + min r (rs.length - r) := by
    simp [B, mrg_length, u, v]
  have hlt : (rs.drop (2 * r)).length < n := by
    have : rs.length ≠ 0 := by simpa using hrs
    simp; omega
  have ih' := ih _ hlt (rs.drop (2 * r)) (chunkSorted_drop h 2) rfl
  intro i
  rcases le_or_gt (2 * r) rs.length with hge | hlt2
  · have hB2 : B.length = 2 * r := by rw [hBl]; omega
    rcases i with _ | i
    · simp only [zero_mul, List.drop_zero]
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
      exact hB
    · rw [show (i + 1) * (2 * r) = B.length + i * (2 * r) by rw [hB2]; ring,
        ← List.drop_drop, List.drop_left]
      exact ih' i
  · have hrest : rs.drop (2 * r) = [] := List.drop_eq_nil_of_le hlt2.le
    rw [hrest, passX_nil, List.append_nil]
    rcases i with _ | i
    · simp only [zero_mul, List.drop_zero]
      rw [List.take_of_length_le (by omega)]
      exact hB
    · have h1 : 2 * r ≤ (i + 1) * (2 * r) := Nat.le_mul_of_pos_left _ (by omega)
      rw [List.drop_eq_nil_of_le (by rw [hBl]; omega)]
      simp

/-! ## The passes and the result -/

/-- The direction of pass `j`. -/
def dirOf (j : ℕ) : Bool := decide (j % 2 = 1)

lemma dirOf_succ (j : ℕ) : dirOf (j + 1) = !dirOf j := by
  unfold dirOf; rcases Nat.mod_two_eq_zero_or_one j with h | h <;> simp [h, Nat.add_mod]

/-- The records after `j` passes. -/
def passes (rs : List (List ℕ)) : ℕ → List (List ℕ)
  | 0 => rs
  | j + 1 => passX (dirOf j) (2 ^ j) (passes rs j)

lemma passes_perm (rs : List (List ℕ)) : ∀ j, (passes rs j).Perm rs
  | 0 => List.Perm.refl _
  | j + 1 => (passX_perm _ _ _).trans (passes_perm rs j)

lemma passes_chunkSorted (rs : List (List ℕ)) :
    ∀ j, ChunkSorted (ordD (dirOf j)) (2 ^ j) (passes rs j)
  | 0 => by show ChunkSorted _ (2 ^ 0) rs; simpa using chunkSorted_one (ordD (dirOf 0)) rs
  | j + 1 => by
    rw [dirOf_succ, pow_succ, mul_comm]
    exact passX_chunkSorted _ (by positivity) _ (passes_chunkSorted rs j)

/-- The final records: after `p` passes, reversed if the last direction was descending. -/
def finalRecs (rs : List (List ℕ)) (p : ℕ) : List (List ℕ) :=
  if dirOf p then (passes rs p).reverse else passes rs p

/-- The sorted records. -/
def sortedRecs (rs : List (List ℕ)) : List (List ℕ) := rs.mergeSort rle

/-- The unique sorted permutation. -/
lemma eq_sortedRecs {rs l : List (List ℕ)} (hp : l.Perm rs)
    (hs : l.Pairwise (fun a b => rle a b = true)) : l = sortedRecs rs := by
  refine List.Perm.eq_of_pairwise (fun a b _ _ h₁ h₂ => rle_antisymm a b h₁ h₂) hs
    (List.pairwise_mergeSort (rle_trans) (fun a b => by
      rcases rle_total a b with h | h <;> simp [h]) rs) (hp.trans (List.mergeSort_perm rs rle).symm)

/-- **The passes sort.** -/
theorem finalRecs_eq (rs : List (List ℕ)) {p : ℕ} (hp : rs.length ≤ 2 ^ p) :
    finalRecs rs p = sortedRecs rs := by
  have hs := pairwise_of_chunkSorted (passes_chunkSorted rs p)
    (by rw [(passes_perm rs p).length_eq]; exact hp)
  unfold finalRecs
  split_ifs with hd
  · refine eq_sortedRecs ((List.reverse_perm _).trans (passes_perm rs p)) ?_
    refine List.pairwise_reverse.mpr ?_
    simpa [ordD, hd] using hs
  · refine eq_sortedRecs (passes_perm rs p) ?_
    simpa [ordD, hd] using hs

end Lax119563Proofs.Compiler.CSort

end Compiler_CSortList

/-! ### Formerly `Lax119563Proofs.Compiler.PJoinList` -/

section Compiler_PJoinList

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

end Compiler_PJoinList

/-! ### Formerly `Lax119563Proofs.Circuits.Bits` -/

section Circuits_Bits

/-!
# Bit fields of natural numbers

Addresses are natural numbers. A *field* of an address is a block of consecutive bits; the
programs only test fields against constants and replace fields by constants (via an XOR with
a constant mask).
-/

namespace Lax119563Proofs.Circuits

/-- The field of `m` bits of `A` starting at bit `k`, as a number `< 2 ^ m`. -/
def field (A k m : ℕ) : ℕ := A / 2 ^ k % 2 ^ m

/-- Replace the field of `m` bits of `A` starting at bit `k` by `v` (for `v < 2 ^ m`). -/
def setBits (A k m v : ℕ) : ℕ := A ^^^ ((field A k m ^^^ v) <<< k)

lemma testBit_field (A k m t : ℕ) :
    (field A k m).testBit t = (decide (t < m) && A.testBit (t + k)) := by
  simp [field, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]

lemma field_lt (A k m : ℕ) : field A k m < 2 ^ m := Nat.mod_lt _ (by positivity)

/-- A field equals `q` iff the corresponding bits agree. -/
lemma field_eq_iff {A k m q : ℕ} (hq : q < 2 ^ m) :
    field A k m = q ↔ ∀ t < m, A.testBit (t + k) = q.testBit t := by
  constructor
  · rintro rfl t ht
    simp [testBit_field, ht]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro t
    rw [testBit_field]
    by_cases ht : t < m
    · simp [ht, h t ht]
    · have : q.testBit t = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num)
          (not_lt.mp ht)))
      simp [ht, this]

lemma testBit_setBits {A k m v : ℕ} (hv : v < 2 ^ m) (i : ℕ) :
    (setBits A k m v).testBit i =
      if k ≤ i ∧ i < k + m then v.testBit (i - k) else A.testBit i := by
  have hv' : ∀ t, m ≤ t → v.testBit t = false := fun t ht =>
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) ht))
  simp only [setBits, Nat.testBit_xor, Nat.testBit_shiftLeft, testBit_field]
  by_cases hk : k ≤ i
  · by_cases hm : i < k + m
    · have h1 : i - k < m := by omega
      have h2 : i - k + k = i := by omega
      simp [hk, hm, h1, h2]
    · have h1 : ¬ i - k < m := by omega
      simp [hk, hm, h1, hv' (i - k) (by omega)]
  · simp [hk]

lemma setBits_div {A k m v : ℕ} (hv : v < 2 ^ m) :
    setBits A k m v / 2 ^ (k + m) = A / 2 ^ (k + m) := by
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [Nat.testBit_div_two_pow, testBit_setBits hv]
  rw [if_neg (by omega)]

lemma setBits_mod {A k m v : ℕ} (hv : v < 2 ^ m) :
    setBits A k m v % 2 ^ k = A % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [Nat.testBit_mod_two_pow, testBit_setBits hv]
  by_cases ht : t < k
  · simp [ht, show ¬ (k ≤ t) by omega]
  · simp [ht]

lemma field_setBits {A k m v : ℕ} (hv : v < 2 ^ m) : field (setBits A k m v) k m = v := by
  apply (field_eq_iff hv).mpr
  intro t ht
  rw [testBit_setBits hv, if_pos (by omega)]
  congr 1
  omega

/-- The decomposition of a number into the part above a field, the field, and the part
below it. -/
lemma decomp (A k m : ℕ) :
    A = A / 2 ^ (k + m) * 2 ^ (k + m) + field A k m * 2 ^ k + A % 2 ^ k := by
  have h1 := Nat.div_add_mod A (2 ^ k)
  have h2 := Nat.div_add_mod (A / 2 ^ k) (2 ^ m)
  have h3 : A / 2 ^ k / 2 ^ m = A / 2 ^ (k + m) := by
    rw [Nat.div_div_eq_div_mul, ← pow_add]
  rw [h3] at h2
  have h4 : A = 2 ^ k * (2 ^ m * (A / 2 ^ (k + m)) + A / 2 ^ k % 2 ^ m) + A % 2 ^ k := by
    rw [h2]; exact h1.symm
  unfold field
  calc A = _ := h4
    _ = _ := by rw [pow_add]; ring

lemma mod_eq_field_add (A k m : ℕ) :
    A % 2 ^ (k + m) = field A k m * 2 ^ k + A % 2 ^ k := by
  have hlt : field A k m * 2 ^ k + A % 2 ^ k < 2 ^ (k + m) := by
    have h1 := field_lt A k m
    have h2 : A % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by positivity)
    have h3 : (field A k m + 1) * 2 ^ k ≤ 2 ^ m * 2 ^ k := Nat.mul_le_mul_right _ h1
    rw [pow_add]
    nlinarith
  conv_lhs => rw [decomp A k m]
  rw [add_assoc, Nat.mul_add_mod_of_lt hlt]

/-- A number is determined by the part above a field, the field, and the part below it. -/
lemma eq_of_decomp {A k m X v u : ℕ} (hv : v < 2 ^ m) (hu : u < 2 ^ k)
    (h : A = X * 2 ^ (k + m) + v * 2 ^ k + u) :
    A / 2 ^ (k + m) = X ∧ field A k m = v ∧ A % 2 ^ k = u := by
  have hlt : v * 2 ^ k + u < 2 ^ (k + m) := by
    rw [pow_add]
    have : v + 1 ≤ 2 ^ m := hv
    nlinarith
  have hA : A = u + 2 ^ k * (v + 2 ^ m * X) := by rw [h, pow_add]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [h, add_assoc, Nat.mul_comm X, Nat.mul_add_div (by positivity),
      Nat.div_eq_of_lt hlt, add_zero]
  · unfold field
    rw [hA, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hu, zero_add,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]
  · rw [hA, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu]

lemma setBits_lt {A k m v N : ℕ} (hv : v < 2 ^ m) (hA : A < 2 ^ N) (hkm : k + m ≤ N) :
    setBits A k m v < 2 ^ N := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_setBits hv, if_neg (by omega)]
  exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hA (Nat.pow_le_pow_right (by norm_num) hi))

end Lax119563Proofs.Circuits

namespace Lax119563Proofs.Circuits

lemma field_zero_eq_mod (A m : ℕ) : field A 0 m = A % 2 ^ m := by simp [field]

lemma field_setBits_of_disjoint {A k m v k' m' : ℕ} (hv : v < 2 ^ m)
    (h : k' + m' ≤ k ∨ k + m ≤ k') : field (setBits A k m v) k' m' = field A k' m' := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [testBit_field, testBit_field, testBit_setBits hv]
  by_cases ht : t < m'
  · rw [if_neg (by omega)]
  · simp [ht]

lemma setBits_div_of_le {A k m v N : ℕ} (hv : v < 2 ^ m) (h : k + m ≤ N) :
    setBits A k m v / 2 ^ N = A / 2 ^ N := by
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [Nat.testBit_div_two_pow, testBit_setBits hv]
  rw [if_neg (by omega)]

/-- Splitting off the top bit of a three-bit field. -/
lemma split_field3 (A k : ℕ) :
    A / 2 ^ (k + 2) = 2 * (A / 2 ^ (k + 3)) + field A k 3 / 4 ∧
      A % 2 ^ (k + 2) = field A k 3 % 4 * 2 ^ k + A % 2 ^ k := by
  have hd := decomp A k 3
  have hu : A % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by positivity)
  have h4 : field A k 3 % 4 < 2 ^ 2 := by
    have := Nat.mod_lt (field A k 3) (by norm_num : 4 > 0); simpa using this
  have key : A = (2 * (A / 2 ^ (k + 3)) + field A k 3 / 4) * 2 ^ (k + 2) +
      field A k 3 % 4 * 2 ^ k + A % 2 ^ k := by
    have e := Nat.div_add_mod (field A k 3) 4
    have p3 : 2 ^ (k + 3) = 2 ^ k * 8 := by rw [pow_add]; norm_num
    have p2 : 2 ^ (k + 2) = 2 ^ k * 4 := by rw [pow_add]; norm_num
    have e' : field A k 3 * 2 ^ k =
        4 * (field A k 3 / 4) * 2 ^ k + field A k 3 % 4 * 2 ^ k := by
      conv_lhs => rw [← e]
      ring
    rw [p3] at hd
    rw [p2, p3]
    conv_lhs => rw [hd, e']
    ring
  obtain ⟨h1, h2, h3⟩ := eq_of_decomp h4 hu key
  refine ⟨h1, ?_⟩
  rw [mod_eq_field_add A k 2, h2, h3]

end Lax119563Proofs.Circuits

end Circuits_Bits

/-! ### Formerly `Lax119563Proofs.Circuits.AddrProgram` -/

section Circuits_AddrProgram

/-!
# Programs over numeric addresses

The valuation `a` of `s` registers over `𝔽₂^ℓ` is identified with the number `addr a < 2^(s ℓ)`
whose bit `i ℓ + k` is bit `k` of register `i`. An *address program* is a list of commands
over an arbitrary type of locations whose guards are conjunctions of conditions on the
register values `field A (i ℓ) ℓ` and whose updates are XORs with constant masks. Given an
injective numbering of the locations, it compiles to a register program (with the identity
register permutation), and acceptance is preserved (`compile_accepts`).
-/

namespace Lax119563Proofs.Circuits

open Programs

/-- The number with bits `f 0, …, f (n - 1)`. -/
def ofBits : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | n + 1, f => Nat.bit (f 0) (ofBits n fun i => f (i + 1))

lemma testBit_ofBits (n : ℕ) (f : ℕ → Bool) (i : ℕ) :
    (ofBits n f).testBit i = (decide (i < n) && f i) := by
  induction n generalizing f i with
  | zero => simp [ofBits]
  | succ n ih =>
    cases i with
    | zero => simp [ofBits]
    | succ i => simp [ofBits, Nat.testBit_bit_succ, ih]

variable {s ℓ : ℕ}

/-- Bit `p` of the register valuation `a`, for `p < s * ℓ`. -/
def valBit (a : Fin s → Fin ℓ → ZMod 2) (p : ℕ) : Bool :=
  if h : p < s * ℓ then
    decide (a ⟨p / ℓ, Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])⟩
      ⟨p % ℓ, Nat.mod_lt _ (Nat.pos_of_ne_zero fun h0 => by simp [h0] at h)⟩ = 1)
  else false

/-- The address `∑ bit_p 2^p` of a valuation. -/
def addr (a : Fin s → Fin ℓ → ZMod 2) : ℕ := ofBits (s * ℓ) (valBit a)

/-- The numeric value of one register. -/
def regVal (v : Fin ℓ → ZMod 2) : ℕ :=
  ofBits ℓ fun k => if h : k < ℓ then decide (v ⟨k, h⟩ = 1) else false

lemma testBit_addr (a : Fin s → Fin ℓ → ZMod 2) (p : ℕ) :
    (addr a).testBit p = valBit a p := by
  rw [addr, testBit_ofBits]
  unfold valBit
  split_ifs with h <;> simp [h]

lemma field_addr (a : Fin s → Fin ℓ → ZMod 2) (i : Fin s) :
    field (addr a) (i * ℓ) ℓ = regVal (a i) := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [testBit_field, testBit_addr, regVal, testBit_ofBits]
  by_cases ht : t < ℓ
  · have hlt : t + i * ℓ < s * ℓ := by
      have := i.isLt
      nlinarith
    have hdiv : (t + i * ℓ) / ℓ = i := by
      rw [Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt ht, zero_add]
    have hmod : (t + i * ℓ) % ℓ = t := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
    simp only [valBit, dif_pos hlt, ht, decide_true, Bool.true_and]
    congr 3 <;> simp [hdiv, hmod]
  · simp [ht]

/-- The valuation whose address is `m` (bits beyond `s ℓ` are dropped). -/
def ofAddr (m : ℕ) : Fin s → Fin ℓ → ZMod 2 :=
  fun i k => if m.testBit (i * ℓ + k) then 1 else 0

lemma zmod2_add_eq_one (x y : ZMod 2) :
    decide (x + y = 1) = (decide (x = 1) ^^ decide (y = 1)) := by
  revert x y; decide

lemma addr_add_ofAddr (a : Fin s → Fin ℓ → ZMod 2) {m : ℕ} (hm : m < 2 ^ (s * ℓ)) :
    addr (fun i k => a i k + ofAddr m i k) = addr a ^^^ m := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_xor, testBit_addr, testBit_addr]
  by_cases hp : p < s * ℓ
  · have hℓ : 0 < ℓ := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hp
    have hp' : p / ℓ * ℓ + p % ℓ = p := by rw [Nat.mul_comm]; exact Nat.div_add_mod p ℓ
    simp only [valBit, dif_pos hp, ofAddr, hp', zmod2_add_eq_one]
    congr 1
    split_ifs <;> simp_all
  · have : m.testBit p = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num)
        (not_lt.mp hp)))
    simp [valBit, hp, this]

lemma addr_zero : addr (fun (_ : Fin s) (_ : Fin ℓ) => (0 : ZMod 2)) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [testBit_addr]
  unfold valBit
  split_ifs <;> simp

/-- A command of an address program over locations `L`. The guard `g i v` is a condition
on the value `v` of register `i`. -/
inductive ACmd (L : Type) (s : ℕ)
  | assign (src : L) (g : Fin s → ℕ → Bool) (mask : ℕ) (next : L)
  | fork (src : L) (g : Fin s → ℕ → Bool) (left right : L)

/-- The guard `g` holds at address `A`. -/
def Enabled (ℓ : ℕ) (g : Fin s → ℕ → Bool) (A : ℕ) : Prop :=
  ∀ i : Fin s, g i (field A (i * ℓ) ℓ) = true

/-- Acceptance of an address program with command list `cmds`, accepting location `acc` and
rejecting location `rej`. -/
inductive AAccepts {L : Type} (ℓ : ℕ) (cmds : List (ACmd L s)) (acc rej : L) : L → ℕ → Prop
  | accept (A : ℕ) : AAccepts ℓ cmds acc rej acc A
  | assign {p g m q A} : ACmd.assign p g m q ∈ cmds → p ≠ acc → p ≠ rej → Enabled ℓ g A →
      AAccepts ℓ cmds acc rej q (A ^^^ m) → AAccepts ℓ cmds acc rej p A
  | fork {p g q r A} : ACmd.fork p g q r ∈ cmds → p ≠ acc → p ≠ rej → Enabled ℓ g A →
      AAccepts ℓ cmds acc rej q A → AAccepts ℓ cmds acc rej r A →
      AAccepts ℓ cmds acc rej p A

/-- The register guard of an address guard. -/
def toGuard (g : Fin s → ℕ → Bool) : Guard s ℓ where
  sets i := Finset.univ.filter fun v => g i (regVal v) = true

/-- The register update XOR-ing the address with `m`. -/
def toUpdate (m : ℕ) : Update s ℓ where
  σ := 1
  δ := ofAddr m

/-- The register command of an address command. -/
def ACmd.toCmd {L : Type} {N : ℕ} (code : L → Fin N) : ACmd L s → Command s ℓ N
  | .assign p g m q => .assign (code p) (toGuard g) (toUpdate m) (code q)
  | .fork p g q r => .fork (code p) (toGuard g) (code q) (code r)

/-- Compile an address program to a register program, given an injective numbering of the
locations. -/
def compile {L : Type} (N : ℕ) (code : L → Fin N) (acc rej : L)
    (hne : code acc ≠ code rej) (cmds : List (ACmd L s)) : RegisterProgram s ℓ where
  numLocations := N
  accept := code acc
  reject := code rej
  accept_ne_reject := hne
  commands := cmds.map (ACmd.toCmd code)

lemma toGuard_holds (g : Fin s → ℕ → Bool) (a : Fin s → Fin ℓ → ZMod 2) :
    (toGuard g : Guard s ℓ).Holds a ↔ Enabled ℓ g (addr a) := by
  simp [Guard.Holds, toGuard, Enabled, field_addr]

lemma toUpdate_apply_addr (m : ℕ) (hm : m < 2 ^ (s * ℓ)) (a : Fin s → Fin ℓ → ZMod 2) :
    addr ((toUpdate m : Update s ℓ).apply a) = addr a ^^^ m := by
  rw [← addr_add_ofAddr a hm]
  rfl

/-- All masks of a command list are below `2 ^ (s ℓ)`. -/
def MasksBounded {L : Type} (s ℓ : ℕ) (cmds : List (ACmd L s)) : Prop :=
  ∀ p g m q, ACmd.assign p g m q ∈ cmds → m < 2 ^ (s * ℓ)

lemma compile_accepts_aux {L : Type} {N : ℕ} {code : L → Fin N}
    (hcode : Function.Injective code) {acc rej : L} (hne : code acc ≠ code rej)
    {cmds : List (ACmd L s)} (hmask : MasksBounded s ℓ cmds)
    (q : Fin (compile (ℓ := ℓ) N code acc rej hne cmds).numLocations)
    (a : Fin s → Fin ℓ → ZMod 2) (h : (compile (ℓ := ℓ) N code acc rej hne cmds).Accepts q a) :
    ∀ p, code p = q → AAccepts ℓ cmds acc rej p (addr a) := by
  induction h with
  | accept a =>
    intro p hq
    have : p = acc := hcode hq
    subst this
    exact AAccepts.accept _
  | assign hmem hpa hpr hg _ ih =>
    intro p hq
    obtain ⟨c, hc, hceq⟩ := List.mem_map.mp hmem
    cases c with
    | assign p' g' m' q' =>
      simp only [ACmd.toCmd] at hceq
      injection hceq with h1 h2 h3 h4
      subst h2 h3 h4
      have : p' = p := hcode (h1.trans hq.symm)
      subst this
      clear h1
      refine AAccepts.assign hc (fun h => hpa (by rw [← hq, h]; rfl))
        (fun h => hpr (by rw [← hq, h]; rfl)) ((toGuard_holds _ _).mp hg) ?_
      rw [← toUpdate_apply_addr m' (hmask _ _ _ _ hc)]
      exact ih q' rfl
    | fork => simp [ACmd.toCmd] at hceq
  | fork hmem hpa hpr hg _ _ ih₁ ih₂ =>
    intro p hq
    obtain ⟨c, hc, hceq⟩ := List.mem_map.mp hmem
    cases c with
    | assign => simp [ACmd.toCmd] at hceq
    | fork p' g' q' r' =>
      simp only [ACmd.toCmd] at hceq
      injection hceq with h1 h2 h3 h4
      subst h2 h3 h4
      have : p' = p := hcode (h1.trans hq.symm)
      subst this
      clear h1
      exact AAccepts.fork hc (fun h => hpa (by rw [← hq, h]; rfl))
        (fun h => hpr (by rw [← hq, h]; rfl)) ((toGuard_holds _ _).mp hg) (ih₁ q' rfl)
        (ih₂ r' rfl)

/-- Compilation preserves acceptance. -/
theorem compile_accepts {L : Type} {N : ℕ} {code : L → Fin N} (hcode : Function.Injective code)
    {acc rej : L} (hne : code acc ≠ code rej) {cmds : List (ACmd L s)}
    (hmask : MasksBounded s ℓ cmds) (p : L) (a : Fin s → Fin ℓ → ZMod 2) :
    (compile (ℓ := ℓ) N code acc rej hne cmds).Accepts (code p) a ↔
      AAccepts ℓ cmds acc rej p (addr a) := by
  constructor
  · intro h
    exact compile_accepts_aux hcode hne hmask _ a h p rfl
  · intro h
    generalize hA : addr a = A at h
    induction h generalizing a with
    | accept A => exact RegisterProgram.Accepts.accept _
    | assign hc hpa hpr hg _ ih =>
      subst hA
      refine RegisterProgram.Accepts.assign (List.mem_map.mpr ⟨_, hc, rfl⟩)
        (fun h => hpa (hcode h)) (fun h => hpr (hcode h)) ((toGuard_holds _ _).mpr hg) ?_
      exact ih _ (toUpdate_apply_addr _ (hmask _ _ _ _ hc) a)
    | fork hc hpa hpr hg _ _ ih₁ ih₂ =>
      subst hA
      exact RegisterProgram.Accepts.fork (List.mem_map.mpr ⟨_, hc, rfl⟩)
        (fun h => hpa (hcode h)) (fun h => hpr (hcode h)) ((toGuard_holds _ _).mpr hg)
        (ih₁ a rfl) (ih₂ a rfl)

end Lax119563Proofs.Circuits

namespace Lax119563Proofs.Circuits

/-! ## Field guards and field updates -/

variable {s : ℕ}

/-- The guard `field A k m = q`, split into conditions on the registers of width `ℓ`. -/
def fieldGuard (ℓ k m q : ℕ) : Fin s → ℕ → Bool :=
  fun i v => decide (∀ t < m, (k + t) / ℓ = i → v.testBit ((k + t) % ℓ) = q.testBit t)

lemma enabled_fieldGuard {ℓ k m q A : ℕ} (hℓ : 0 < ℓ) (hkm : k + m ≤ s * ℓ) (hq : q < 2 ^ m) :
    Enabled ℓ (fieldGuard (s := s) ℓ k m q) A ↔ field A k m = q := by
  rw [field_eq_iff hq]
  have key : ∀ t, (k + t) % ℓ + (k + t) / ℓ * ℓ = k + t := fun t => by
    rw [Nat.mul_comm]; exact Nat.mod_add_div _ _
  constructor
  · intro h t ht
    have hlt : (k + t) / ℓ < s := Nat.div_lt_of_lt_mul (by nlinarith)
    have := h ⟨_, hlt⟩
    simp only [fieldGuard, decide_eq_true_eq] at this
    have h2 := this t ht rfl
    rw [testBit_field, key] at h2
    simpa [Nat.mod_lt _ hℓ, Nat.add_comm t k] using h2
  · intro h i
    simp only [fieldGuard, decide_eq_true_eq]
    intro t ht hi
    rw [testBit_field, ← hi, key]
    simpa [Nat.mod_lt _ hℓ, Nat.add_comm k t] using h t ht

/-- The mask replacing a field with current value `q` by `v`. -/
def fieldMask (k q v : ℕ) : ℕ := (q ^^^ v) <<< k

lemma xor_fieldMask {A k m q v : ℕ} (h : field A k m = q) :
    A ^^^ fieldMask k q v = setBits A k m v := by
  rw [fieldMask, setBits, h]

lemma fieldMask_lt {k m q v N : ℕ} (hq : q < 2 ^ m) (hv : v < 2 ^ m) (hkm : k + m ≤ N) :
    fieldMask k q v < 2 ^ N := by
  rw [fieldMask, Nat.shiftLeft_eq]
  have h1 : q ^^^ v < 2 ^ m := Nat.xor_lt_two_pow hq hv
  calc (q ^^^ v) * 2 ^ k < 2 ^ m * 2 ^ k := Nat.mul_lt_mul_of_pos_right h1 (by positivity)
    _ = 2 ^ (k + m) := by rw [← pow_add, Nat.add_comm]
    _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hkm

end Lax119563Proofs.Circuits

end Circuits_AddrProgram

/-! ### Formerly `Lax119563Proofs.Circuits.MachineRun` -/

section Circuits_MachineRun

/-!
# Runs of multitape machines

Elementary facts about the deterministic runs `runOn M x t` of a `Lax489179` machine: one
more step is one application of `step`, heads move by at most one cell per step, a cell not
under the head keeps its symbol, halted configurations are fixed, and one step is a local
function of the extended state `(state, answer)` and the scanned symbols.
-/

namespace Lax119563Proofs.Circuits

open Lax489179.TuringMachine Lax119563.DeterministicTime

variable {M : Machine}

/-- Tape symbols. -/
abbrev Sym (M : Machine) := Fin (M.symbols + 3)
/-- Tapes. -/
abbrev Tape (M : Machine) := Fin (M.tapes + 1)
/-- Extended states: the control state together with the answer (`none` while running). -/
abbrev ExtState (M : Machine) := Fin (M.states + 1) × Option Bool
/-- Cell values: a symbol and the flag "the head is here". -/
abbrev CellVal (M : Machine) := Sym M × Bool

lemma run_succ_const (t : ℕ) (c : Config M) :
    run M (t + 1) (fun _ => false) c = step M false (run M t (fun _ => false) c) := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    change run M (t + 1) (fun _ => false) (step M false c) = _
    rw [ih]
    rfl

lemma runOn_succ (x : List Bool) (t : ℕ) :
    runOn M x (t + 1) = step M false (runOn M x t) :=
  run_succ_const t _

lemma runOn_zero (x : List Bool) : runOn M x 0 = init M x := rfl

lemma step_of_halted {c : Config M} (h : c.answer.isSome) : step M false c = c := by
  unfold step
  cases hc : c.answer with
  | none => simp [hc] at h
  | some b => rfl

lemma step_head (c : Config M) (ν : Tape M) :
    |(step M false c).head ν - c.head ν| ≤ 1 := by
  unfold step
  cases c.answer with
  | some b => simp
  | none =>
    simp only
    cases M.transition c.state (fun j => c.tape j (c.head j)) false with
    | halt b => simp
    | next q write move =>
      simp only [add_sub_cancel_left]
      cases move ν <;> simp [Move.offset]

lemma step_tape_of_ne (c : Config M) (ν : Tape M) (z : ℤ) (hz : c.head ν ≠ z) :
    (step M false c).tape ν z = c.tape ν z := by
  unfold step
  cases c.answer with
  | some b => rfl
  | none =>
    simp only
    cases M.transition c.state (fun j => c.tape j (c.head j)) false with
    | halt b => rfl
    | next q write move =>
      simp only
      rw [if_neg (Ne.symm hz)]

lemma runOn_head_dist (x : List Bool) (ν : Tape M) (t k : ℕ) :
    |(runOn M x (t + k)).head ν - (runOn M x t).head ν| ≤ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc, runOn_succ]
    have h := step_head (runOn M x (t + k)) ν
    calc |(step M false (runOn M x (t + k))).head ν - (runOn M x t).head ν|
        ≤ |(step M false (runOn M x (t + k))).head ν - (runOn M x (t + k)).head ν| +
          |(runOn M x (t + k)).head ν - (runOn M x t).head ν| := abs_sub_le _ _ _
      _ ≤ 1 + k := add_le_add h ih
      _ = ((k + 1 : ℕ) : ℤ) := by push_cast; ring

/-- Frame property: a cell that is never under the head keeps its symbol. -/
lemma runOn_tape_frame (x : List Bool) (ν : Tape M) (z : ℤ) (t k : ℕ)
    (h : ∀ i < k, (runOn M x (t + i)).head ν ≠ z) :
    (runOn M x (t + k)).tape ν z = (runOn M x t).tape ν z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, runOn_succ, step_tape_of_ne _ _ _ (h k (by omega))]
    exact ih fun i hi => h i (by omega)

lemma runOn_halted (x : List Bool) {t : ℕ} (h : (runOn M x t).answer.isSome) (k : ℕ) :
    runOn M x (t + k) = runOn M x t := by
  induction k with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc, runOn_succ, ih, step_of_halted h]

/-- The extended state of a configuration. -/
def cfgExt (c : Config M) : ExtState M := (c.state, c.answer)

/-- The extended state after one step, from the extended state and the scanned symbols. -/
def nextExt (p : ExtState M) (scan : Tape M → Sym M) : ExtState M :=
  match p.2 with
  | some _ => p
  | none =>
    match M.transition p.1 scan false with
    | .halt b => (p.1, some b)
    | .next q _ _ => (q, none)

/-- The value after one step of the cell at relative position `j` of tape `ν`, from the
extended state, the scanned symbols, the relative head position `h` of tape `ν`, and the old
value of the cell. -/
def nextCell (p : ExtState M) (scan : Tape M → Sym M) (ν : Tape M) (h j : ℤ)
    (old : CellVal M) : CellVal M :=
  match p.2 with
  | some _ => old
  | none =>
    match M.transition p.1 scan false with
    | .halt _ => old
    | .next _ write move => (if j = h then write ν else old.1, decide (j = h + (move ν).offset))

/-- The value of a cell in a configuration. -/
def cfgCell (c : Config M) (ν : Tape M) (z : ℤ) : CellVal M :=
  (c.tape ν z, decide (c.head ν = z))

lemma step_ext (c : Config M) :
    cfgExt (step M false c) = nextExt (cfgExt c) (fun ν => c.tape ν (c.head ν)) := by
  rcases c with ⟨st, hd, tp, ans⟩
  unfold step nextExt cfgExt
  cases ans with
  | some b => rfl
  | none =>
    simp only
    cases M.transition st (fun j => tp j (hd j)) false with
    | halt b => rfl
    | next q write move => rfl

lemma step_cell (c : Config M) (ν : Tape M) (o z : ℤ) :
    cfgCell (step M false c) ν z =
      nextCell (cfgExt c) (fun ν => c.tape ν (c.head ν)) ν (c.head ν - o) (z - o) (cfgCell c ν z) := by
  rcases c with ⟨st, hd, tp, ans⟩
  unfold step nextCell cfgExt cfgCell
  cases ans with
  | some b => rfl
  | none =>
    simp only
    cases M.transition st (fun j => tp j (hd j)) false with
    | halt b => rfl
    | next q write move =>
      simp only [sub_left_inj, Prod.mk.injEq]
      constructor
      · simp
      · have : (hd ν + (move ν).offset = z) ↔ (z - o = hd ν - o + (move ν).offset) := by
          constructor <;> intro h <;> linarith
        simp [this]

end Lax119563Proofs.Circuits

end Circuits_MachineRun

/-! ### Formerly `Lax119563Proofs.Circuits.MoveProgram` -/

section Circuits_MoveProgram

/-!
# Programs given by local moves

An address program is described by a list of *moves* at each location: replacing a bit field
with known current value (`step`), forking under a field test (`fork`), or moving under an
arbitrary register guard (`test`). Soundness and completeness of such a program with respect
to a semantic predicate `Sem` on configurations reduce to local conditions on the moves:
every move is sound for `Sem`, and every configuration satisfying `Sem` has a move that fires
into configurations satisfying `Sem` of smaller rank.
-/

namespace Lax119563Proofs.Circuits

variable {L : Type} {s : ℕ}

/-- A move at a location. -/
inductive Move (L : Type) (s : ℕ)
  /-- If `field A k m = q`, replace that field by `v` and go to `dst`. -/
  | step (k m q v : ℕ) (dst : L)
  /-- If `field A k m = q`, fork into `left` and `right`. -/
  | fork (k m q : ℕ) (left right : L)
  /-- If the register guard `g` holds, go to `dst`. -/
  | test (g : Fin s → ℕ → Bool) (dst : L)

/-- An unconditional jump. -/
def Move.goto (dst : L) : Move L s := .step 0 0 0 0 dst

/-- An unconditional fork. -/
def Move.fork' (left right : L) : Move L s := .fork 0 0 0 left right

/-- The address command of a move at `src`. -/
def Move.toACmd (ℓ : ℕ) (src : L) : Move L s → ACmd L s
  | .step k m q v dst => .assign src (fieldGuard ℓ k m q) (fieldMask k q v) dst
  | .fork k m q l r => .fork src (fieldGuard ℓ k m q) l r
  | .test g dst => .assign src g 0 dst

/-- The commands of all moves at the locations `locs`. -/
def progCmds (ℓ : ℕ) (locs : List L) (moves : L → List (Move L s)) : List (ACmd L s) :=
  locs.flatMap fun src => (moves src).map (Move.toACmd ℓ src)

/-- The fields of a move lie inside the low `B` bits of the address and its constants fit
into them. -/
def Move.WF (B : ℕ) : Move L s → Prop
  | .step k m q v _ => k + m ≤ B ∧ q < 2 ^ m ∧ v < 2 ^ m
  | .fork k m q _ _ => k + m ≤ B ∧ q < 2 ^ m
  | .test _ _ => True

/-- A move at `src` is sound for `Sem` on the addresses below `2 ^ B`. -/
def Move.Sound (ℓ B : ℕ) (Sem : L → ℕ → Prop) (src : L) : Move L s → Prop
  | .step k m q v dst => ∀ A, A < 2 ^ B → field A k m = q →
      Sem dst (setBits A k m v) → Sem src A
  | .fork k m q l r => ∀ A, A < 2 ^ B → field A k m = q → Sem l A → Sem r A → Sem src A
  | .test g dst => ∀ A, A < 2 ^ B → Enabled ℓ g A → Sem dst A → Sem src A

/-- A move at `src` fires at address `A` into configurations satisfying `Sem` of smaller rank. -/
def Move.Fires (ℓ : ℕ) (Sem : L → ℕ → Prop) (rank : L → ℕ → ℕ) (src : L) (A : ℕ) :
    Move L s → Prop
  | .step k m q v dst => field A k m = q ∧ Sem dst (setBits A k m v) ∧
      rank dst (setBits A k m v) < rank src A
  | .fork k m q l r => field A k m = q ∧ Sem l A ∧ Sem r A ∧ rank l A < rank src A ∧
      rank r A < rank src A
  | .test g dst => Enabled ℓ g A ∧ Sem dst A ∧ rank dst A < rank src A

lemma field_zero_width (A k : ℕ) : field A k 0 = 0 := by simp [field, Nat.mod_one]

lemma setBits_zero_width (A k : ℕ) : setBits A k 0 0 = A := by
  simp [setBits, field_zero_width]

lemma progCmds_masks {ℓ B : ℕ} (hB : B ≤ s * ℓ) {locs : List L} {moves : L → List (Move L s)}
    (hwf : ∀ src ∈ locs, ∀ mv ∈ moves src, mv.WF B) :
    MasksBounded s ℓ (progCmds ℓ locs moves) := by
  intro p g m q hc
  simp only [progCmds, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨src, hsrc, mv, hmv, heq⟩ := hc
  have hw := hwf src hsrc mv hmv
  cases mv with
  | step k m' q' v dst =>
    simp only [Move.toACmd, ACmd.assign.injEq] at heq
    obtain ⟨-, -, rfl, -⟩ := heq
    exact fieldMask_lt hw.2.1 hw.2.2 (hw.1.trans hB)
  | fork => simp [Move.toACmd] at heq
  | test g' dst =>
    simp only [Move.toACmd, ACmd.assign.injEq] at heq
    obtain ⟨-, -, rfl, -⟩ := heq
    positivity

section

variable {ℓ : ℕ} {locs : List L} {moves : L → List (Move L s)} {Sem : L → ℕ → Prop}
  {acc rej : L} {B : ℕ}

/-- Soundness from local soundness. -/
theorem progCmds_sound (hℓ : 0 < ℓ) (hB : B ≤ s * ℓ)
    (hwf : ∀ src ∈ locs, ∀ mv ∈ moves src, mv.WF B)
    (hs : ∀ src ∈ locs, ∀ mv ∈ moves src, mv.Sound ℓ B Sem src)
    (hacc : ∀ A, Sem acc A) {p : L} {A : ℕ}
    (h : AAccepts ℓ (progCmds ℓ locs moves) acc rej p A) (hA : A < 2 ^ B) :
    Sem p A := by
  induction h with
  | accept A => exact hacc A
  | @assign p g m q A hc _ _ hg _ ih =>
    simp only [progCmds, List.mem_flatMap, List.mem_map] at hc
    obtain ⟨src, hsrc, mv, hmv, heq⟩ := hc
    have hw := hwf src hsrc mv hmv
    have hso := hs src hsrc mv hmv
    cases mv with
    | step k m' q' v dst =>
      simp only [Move.toACmd, ACmd.assign.injEq] at heq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
      have hf : field A k m' = q' := (enabled_fieldGuard hℓ (hw.1.trans hB) hw.2.1).mp hg
      rw [xor_fieldMask hf] at ih
      exact hso A hA hf (ih (setBits_lt hw.2.2 hA hw.1))
    | fork => simp [Move.toACmd] at heq
    | test g' dst =>
      simp only [Move.toACmd, ACmd.assign.injEq] at heq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
      rw [Nat.xor_zero] at ih
      exact hso A hA hg (ih hA)
  | @fork p g q r A hc _ _ hg _ _ ih₁ ih₂ =>
    simp only [progCmds, List.mem_flatMap, List.mem_map] at hc
    obtain ⟨src, hsrc, mv, hmv, heq⟩ := hc
    have hw := hwf src hsrc mv hmv
    have hso := hs src hsrc mv hmv
    cases mv with
    | step => simp [Move.toACmd] at heq
    | fork k m' q' l r' =>
      simp only [Move.toACmd, ACmd.fork.injEq] at heq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
      exact hso A hA ((enabled_fieldGuard hℓ (hw.1.trans hB) hw.2).mp hg) (ih₁ hA) (ih₂ hA)
    | test => simp [Move.toACmd] at heq

/-- Completeness from local progress. -/
theorem progCmds_complete (hℓ : 0 < ℓ) (hB : B ≤ s * ℓ) (rank : L → ℕ → ℕ)
    (hmem : ∀ src, src ∈ locs)
    (hwf : ∀ src ∈ locs, ∀ mv ∈ moves src, mv.WF B)
    (hrej : ∀ A, ¬ Sem rej A)
    (hc : ∀ src A, A < 2 ^ B → Sem src A → src = acc ∨
      ∃ mv ∈ moves src, mv.Fires ℓ Sem rank src A) :
    ∀ src A, A < 2 ^ B → Sem src A → AAccepts ℓ (progCmds ℓ locs moves) acc rej src A := by
  suffices ∀ n, ∀ src A, rank src A = n → A < 2 ^ B → Sem src A →
      AAccepts ℓ (progCmds ℓ locs moves) acc rej src A from
    fun src A => this _ src A rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro src A hn hA hS
  rcases hc src A hA hS with rfl | ⟨mv, hmv, hf⟩
  · exact AAccepts.accept A
  by_cases hacc : src = acc
  · subst hacc; exact AAccepts.accept A
  have hrj : src ≠ rej := by rintro rfl; exact hrej A hS
  have hw := hwf src (hmem src) mv hmv
  have hcmd : Move.toACmd ℓ src mv ∈ progCmds ℓ locs moves :=
    List.mem_flatMap.mpr ⟨src, hmem src, List.mem_map.mpr ⟨mv, hmv, rfl⟩⟩
  cases mv with
  | step k m q v dst =>
    obtain ⟨hfq, hS', hr⟩ := hf
    refine AAccepts.assign hcmd hacc hrj ((enabled_fieldGuard hℓ (hw.1.trans hB) hw.2.1).mpr hfq) ?_
    rw [xor_fieldMask hfq]
    exact ih _ (hn ▸ hr) dst _ rfl (setBits_lt hw.2.2 hA hw.1) hS'
  | fork k m q l r =>
    obtain ⟨hfq, hl, hr, hrl, hrr⟩ := hf
    exact AAccepts.fork hcmd hacc hrj ((enabled_fieldGuard hℓ (hw.1.trans hB) hw.2).mpr hfq)
      (ih _ (hn ▸ hrl) l A rfl hA hl) (ih _ (hn ▸ hrr) r A rfl hA hr)
  | test g dst =>
    obtain ⟨hg, hS', hr⟩ := hf
    refine AAccepts.assign hcmd hacc hrj hg ?_
    rw [Nat.xor_zero]
    exact ih _ (hn ▸ hr) dst A rfl hA hS'

end

end Lax119563Proofs.Circuits

end Circuits_MoveProgram

/-! ### Formerly `Lax119563Proofs.Circuits.Windows` -/

section Circuits_Windows

/-!
# Recursive windows of a run

Fix a horizon `H`. A *call* at depth `d ≤ H` is a number `ω < 2 ^ d`; it covers the steps
`[ω 2^r, (ω + 1) 2^r)` with `r = H - d`, in two phases of `B = 2^(r-1)` steps if `r ≥ 1`
(`ptime d ω θ` is the start of phase `θ`, and `θ = 2` is the end of the call). Per tape it
owns a window of `4 * 2^r` cells starting at the offset `off d ω ν`. The root window starts at
`-2^H`; the window of the child `2 ω + θ` starts at block `sel d ω θ ν = min (β - 1) 4` of the
parent window, where `β = blk d ω θ ν` is the block of the head at the start of phase `θ`.

The invariant `rel_mem`: at the start of a call, the head lies in the middle half
`[2^r, 3 * 2^r)` of its window. All truth values of the verifier's claims are values of the
run at these times and window positions; the rules below relate them.
-/

namespace Lax119563Proofs.Circuits

open Lax489179.TuringMachine Lax119563.DeterministicTime

variable (M : Machine) (x : List Bool) (H : ℕ)

/-- The head position of tape `ν` after `t` steps. -/
def hd (t : ℕ) (ν : Tape M) : ℤ := (runOn M x t).head ν

/-- The start of phase `θ` of call `ω` at depth `d` (`θ = 2`: the end of the call). -/
def ptime (d ω θ : ℕ) : ℕ := ω * 2 ^ (H - d) + θ * 2 ^ (H - d) / 2

/-- The block size `2^(H - d - 1)` of a call at depth `d < H`. -/
def bsz (d : ℕ) : ℕ := 2 ^ (H - d - 1)

/-- The selected first block of the child window, for the head in block `β`. -/
def sel (β : ℕ) : ℕ := min (β - 1) 4

/-- The block of size `B` containing the relative position `R ≥ 0`. -/
def blkOf (R : ℤ) (B : ℕ) : ℕ := (R / (B : ℤ)).toNat

/-- The window offsets. -/
def off : ℕ → ℕ → Tape M → ℤ
  | 0, _, _ => -(2 ^ H : ℤ)
  | d + 1, ω, ν =>
    off d (ω / 2) ν +
      (sel (blkOf (hd M x (ptime H d (ω / 2) (ω % 2)) ν - off d (ω / 2) ν) (bsz H d)) : ℤ) *
        (bsz H d : ℤ)

/-- The head position relative to the window, at the start of phase `θ`. -/
def rel (d ω θ : ℕ) (ν : Tape M) : ℤ := hd M x (ptime H d ω θ) ν - off M x H d ω ν

/-- The block of the head at the start of phase `θ`. -/
def blk (d ω θ : ℕ) (ν : Tape M) : ℕ := blkOf (rel M x H d ω θ ν) (bsz H d)

/-- The value of the cell at window position `j` at the start of phase `θ`. -/
def cellT (d ω θ : ℕ) (ν : Tape M) (j : ℕ) : CellVal M :=
  cfgCell (runOn M x (ptime H d ω θ)) ν (off M x H d ω ν + j)

/-- The extended state at the start of phase `θ`. -/
def extT (d ω θ : ℕ) : ExtState M := cfgExt (runOn M x (ptime H d ω θ))

variable {M x H}

lemma off_succ (d ω : ℕ) (ν : Tape M) :
    off M x H (d + 1) ω ν = off M x H d (ω / 2) ν +
      (sel (blk M x H d (ω / 2) (ω % 2) ν) : ℤ) * (bsz H d : ℤ) := rfl

lemma pow_eq_two_mul_bsz {d : ℕ} (hdH : d < H) : 2 ^ (H - d) = 2 * bsz H d := by
  rw [bsz, ← pow_succ']
  congr 1
  omega

lemma bsz_succ (d : ℕ) : bsz H d = 2 ^ (H - (d + 1)) := by
  rw [bsz]; congr 1

lemma bsz_pos (d : ℕ) : 0 < bsz H d := by unfold bsz; positivity

lemma ptime_phase {d : ℕ} (hdH : d < H) (ω θ : ℕ) :
    ptime H d ω θ = ω * (2 * bsz H d) + θ * bsz H d := by
  rw [ptime, pow_eq_two_mul_bsz hdH]
  congr 1
  rw [Nat.mul_left_comm, Nat.mul_div_cancel_left _ (by norm_num)]

lemma ptime_child (d ω θ' : ℕ) (hdH : d < H) :
    ptime H (d + 1) ω θ' = ptime H d (ω / 2) (ω % 2) + θ' * bsz H d / 2 := by
  rw [ptime_phase hdH, ptime, ← bsz_succ]
  have := Nat.div_add_mod ω 2
  rw [← this]
  have h2 : (2 * (ω / 2) + ω % 2) / 2 = ω / 2 := by omega
  have h3 : (2 * (ω / 2) + ω % 2) % 2 = ω % 2 := by omega
  rw [h2, h3]
  ring

lemma ptime_child_zero (d ω : ℕ) (hdH : d < H) :
    ptime H (d + 1) ω 0 = ptime H d (ω / 2) (ω % 2) := by
  rw [ptime_child d ω 0 hdH]; simp

lemma ptime_child_end (d ω θ : ℕ) (hdH : d < H) :
    ptime H (d + 1) (2 * ω + θ) 2 = ptime H d ω (θ + 1) := by
  have hθ : θ < 2 ∨ 2 ≤ θ := by omega
  rw [ptime_child d _ 2 hdH, ptime_phase hdH, ptime_phase hdH]
  rcases Nat.even_or_odd' θ with ⟨k, rfl | rfl⟩
  · have h1 : (2 * ω + 2 * k) / 2 = ω + k := by omega
    have h2 : (2 * ω + 2 * k) % 2 = 0 := by omega
    rw [h1, h2, Nat.mul_div_cancel_left _ (by norm_num)]
    ring
  · have h1 : (2 * ω + (2 * k + 1)) / 2 = ω + k := by omega
    have h2 : (2 * ω + (2 * k + 1)) % 2 = 1 := by omega
    rw [h1, h2, Nat.mul_div_cancel_left _ (by norm_num)]
    ring

lemma off_child (d ω θ : ℕ) (hθ : θ < 2) (ν : Tape M) :
    off M x H (d + 1) (2 * ω + θ) ν =
      off M x H d ω ν + (sel (blk M x H d ω θ ν) : ℤ) * (bsz H d : ℤ) := by
  rw [off_succ]
  have h1 : (2 * ω + θ) / 2 = ω := by omega
  have h2 : (2 * ω + θ) % 2 = θ := by omega
  rw [h1, h2]

lemma hd_dist (t k : ℕ) (ν : Tape M) : |hd M x (t + k) ν - hd M x t ν| ≤ k :=
  runOn_head_dist x ν t k

/-- The block of a head position in `[B, 7B)` lies in `[1, 6]` and determines it. -/
lemma blk_spec_aux {R B : ℤ} (hB : 0 < B) (h1 : B ≤ R) (h2 : R < 7 * B) :
    1 ≤ R / B ∧ R / B ≤ 6 ∧ R / B * B ≤ R ∧ R < (R / B + 1) * B := by
  have e1 : R / B * B ≤ R := Int.ediv_mul_le R (ne_of_gt hB)
  have e2 : R < (R / B + 1) * B := by
    have := Int.emod_lt_of_pos R hB
    have := Int.emod_add_ediv_mul R B
    nlinarith
  refine ⟨?_, ?_, e1, e2⟩
  · by_contra h
    have : R / B ≤ 0 := by omega
    nlinarith
  · by_contra h
    have : 7 ≤ R / B := by omega
    nlinarith

lemma blk_eq {d ω θ : ℕ} {ν : Tape M} {β : ℕ}
    (h1 : (β : ℤ) * bsz H d ≤ rel M x H d ω θ ν) (h2 : rel M x H d ω θ ν < (β + 1) * bsz H d) :
    blk M x H d ω θ ν = β := by
  have hB : (0 : ℤ) < bsz H d := by exact_mod_cast bsz_pos d
  rw [blk, blkOf, (Int.ediv_eq_iff_of_pos hB).mpr ⟨h1, by linarith⟩]
  simp

lemma hd_zero (ν : Tape M) : hd M x 0 ν = 0 := rfl

lemma rel_phase {d ω θ : ℕ} (hdH : d < H) (_hθ : θ < 2) (ν : Tape M) :
    |rel M x H d ω θ ν - rel M x H d ω 0 ν| ≤ θ * bsz H d := by
  unfold rel
  rw [ptime_phase hdH ω θ, ptime_phase hdH ω 0]
  simp only [zero_mul, add_zero, sub_sub_sub_cancel_right]
  exact_mod_cast hd_dist _ _ ν

lemma rel_child (d ω : ℕ) (hdH : d < H) (ν : Tape M) :
    rel M x H (d + 1) ω 0 ν =
      rel M x H d (ω / 2) (ω % 2) ν - (sel (blk M x H d (ω / 2) (ω % 2) ν) : ℤ) * bsz H d := by
  unfold rel
  rw [ptime_child_zero d ω hdH, off_succ]
  ring

/-- Window facts in a phase, given the middle-half invariant at the start of the call. -/
lemma phase_facts {d ω θ : ℕ} (hdH : d < H) (hθ : θ < 2) (ν : Tape M)
    (hinv : (2 ^ (H - d) : ℤ) ≤ rel M x H d ω 0 ν ∧ rel M x H d ω 0 ν < 3 * 2 ^ (H - d)) :
    1 ≤ blk M x H d ω θ ν ∧ blk M x H d ω θ ν ≤ 6 ∧
      (blk M x H d ω θ ν : ℤ) * (bsz H d : ℤ) ≤ rel M x H d ω θ ν ∧
      rel M x H d ω θ ν < ((blk M x H d ω θ ν : ℤ) + 1) * (bsz H d : ℤ) ∧
      ((sel (blk M x H d ω θ ν) : ℤ) + 1) * (bsz H d : ℤ) ≤ rel M x H d ω θ ν ∧
      rel M x H d ω θ ν < ((sel (blk M x H d ω θ ν) : ℤ) + 3) * (bsz H d : ℤ) ∧
      sel (blk M x H d ω θ ν) ≤ 4 := by
  have hB : (0 : ℤ) < (bsz H d : ℤ) := by exact_mod_cast bsz_pos d
  have hpow : (2 ^ (H - d) : ℤ) = 2 * (bsz H d : ℤ) := by exact_mod_cast pow_eq_two_mul_bsz hdH
  have hph := rel_phase (x := x) hdH hθ ν (ω := ω)
  rw [hpow] at hinv
  have hθB : ((θ * bsz H d : ℕ) : ℤ) ≤ (bsz H d : ℤ) := by
    have : θ * bsz H d ≤ bsz H d := by
      have : θ ≤ 1 := by omega
      nlinarith
    exact_mod_cast this
  have hR := abs_le.mp (le_trans hph hθB)
  obtain ⟨b1, b6, e1, e2⟩ := blk_spec_aux hB (R := rel M x H d ω θ ν)
    (by linarith [hinv.1, hR.1]) (by linarith [hinv.2, hR.2])
  have hβ : (blk M x H d ω θ ν : ℤ) = rel M x H d ω θ ν / (bsz H d : ℤ) := by
    simp only [blk, blkOf]
    exact Int.toNat_of_nonneg (by omega)
  rw [← hβ] at b1 b6 e1 e2
  have hβ1 : 1 ≤ blk M x H d ω θ ν := by exact_mod_cast b1
  have hβ6 : blk M x H d ω θ ν ≤ 6 := by exact_mod_cast b6
  refine ⟨hβ1, hβ6, e1, e2, ?_⟩
  have key : ∀ n : ℕ, 1 ≤ n → n ≤ 6 → (n : ℤ) * (bsz H d : ℤ) ≤ rel M x H d ω θ ν →
      rel M x H d ω θ ν < (n + 1) * (bsz H d : ℤ) →
      ((sel n : ℤ) + 1) * (bsz H d : ℤ) ≤ rel M x H d ω θ ν ∧
        rel M x H d ω θ ν < ((sel n : ℤ) + 3) * (bsz H d : ℤ) ∧ sel n ≤ 4 := by
    intro n h1 h6 hl hu
    interval_cases n <;> simp [sel] <;> constructor <;> push_cast at hl hu ⊢ <;> linarith
  exact key _ hβ1 hβ6 e1 e2

/-- The middle-half invariant: at the start of a call, each head lies in the middle half of
its window. -/
theorem rel_mem : ∀ d, d ≤ H → ∀ ω, ω < 2 ^ d → ∀ ν : Tape M,
    (2 ^ (H - d) : ℤ) ≤ rel M x H d ω 0 ν ∧ rel M x H d ω 0 ν < 3 * 2 ^ (H - d) := by
  intro d
  induction d with
  | zero =>
    intro _ ω hω ν
    have : ω = 0 := by simpa using hω
    subst this
    simp only [rel, ptime, off, zero_mul, Nat.zero_div, add_zero, Nat.sub_zero]
    rw [hd_zero]
    constructor <;> linarith [pow_pos (by norm_num : (0 : ℤ) < 2) H]
  | succ d ih =>
    intro hdH ω hω ν
    have hdH : d < H := by omega
    have hω2 : ω / 2 < 2 ^ d := by rw [pow_succ] at hω; omega
    have hθ : ω % 2 < 2 := Nat.mod_lt _ (by norm_num)
    obtain ⟨-, -, -, -, l, u, -⟩ := phase_facts (x := x) hdH hθ ν (ih (by omega) _ hω2 ν)
    have hp : (2 : ℤ) ^ (H - (d + 1)) = (bsz H d : ℤ) := by rw [bsz_succ]; push_cast; rfl
    rw [rel_child d ω hdH, hp]
    constructor <;> nlinarith

lemma ptime_child_zero' (d ω θ : ℕ) (hdH : d < H) (hθ : θ < 2) :
    ptime H (d + 1) (2 * ω + θ) 0 = ptime H d ω θ := by
  rw [ptime_child_zero d _ hdH]
  congr 1 <;> omega

/-- Restore rule: the cells after a phase are the child's final cells inside the child
window, and unchanged outside of it. -/
theorem cellT_restore {d ω θ : ℕ} (hdH : d < H) (hω : ω < 2 ^ d) (hθ : θ < 2) (ν : Tape M)
    (j : ℕ) :
    cellT M x H d ω (θ + 1) ν j =
      if sel (blk M x H d ω θ ν) ≤ j / bsz H d ∧ j / bsz H d < sel (blk M x H d ω θ ν) + 4 then
        cellT M x H (d + 1) (2 * ω + θ) 2 ν
          ((j / bsz H d - sel (blk M x H d ω θ ν)) * bsz H d + j % bsz H d)
      else cellT M x H d ω θ ν j := by
  set w := sel (blk M x H d ω θ ν) with hw
  set B := bsz H d with hB
  have hBpos : 0 < B := bsz_pos d
  have hjB := Nat.div_add_mod' j B
  split_ifs with hin
  · unfold cellT
    rw [ptime_child_end d ω θ hdH, off_child d ω θ hθ]
    congr 1
    rw [← hw, ← hB]
    have : (((j / B - w) * B + j % B : ℕ) : ℤ) = (j : ℤ) - w * B := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hin.1]
      have : ((j / B : ℕ) : ℤ) * B + (j % B : ℕ) = j := by exact_mod_cast hjB
      linarith
    rw [this]; ring
  · obtain ⟨-, -, -, -, l, u, -⟩ := phase_facts (x := x) hdH hθ ν (rel_mem d hdH.le ω hω ν)
    rw [← hw, ← hB] at l u
    have hout : (j : ℤ) < w * B ∨ ((w : ℤ) + 4) * B ≤ j := by
      rcases not_and_or.mp hin with h | h
      · left
        have : j < w * B := by
          rw [not_le] at h
          exact (Nat.div_lt_iff_lt_mul hBpos).mp h
        exact_mod_cast this
      · right
        have : (w + 4) * B ≤ j := (Nat.le_div_iff_mul_le hBpos).mp (not_lt.mp h)
        exact_mod_cast this
    have t1 : ptime H d ω (θ + 1) = ptime H d ω θ + B := by
      rw [ptime_phase hdH, ptime_phase hdH]; ring
    have far : ∀ i ≤ B, hd M x (ptime H d ω θ + i) ν ≠ off M x H d ω ν + j := by
      intro i hi heq
      have hdist := abs_le.mp (hd_dist (x := x) (ptime H d ω θ) i ν)
      have hi' : (i : ℤ) ≤ B := by exact_mod_cast hi
      unfold rel at l u
      rcases hout with h | h <;> nlinarith
    unfold cellT cfgCell
    rw [t1]
    have htape := runOn_tape_frame x ν (off M x H d ω ν + j) (ptime H d ω θ) B
      (fun i hi => far i hi.le)
    rw [htape]
    have f1 := far B le_rfl
    have f0 := far 0 (Nat.zero_le _)
    simp only [add_zero] at f0
    simp only [Circuits.hd] at f1 f0
    simp [f1, f0]

/-- Gather rule: the cells of a child at its start are cells of the parent. -/
theorem cellT_gather {d ω θ : ℕ} (hdH : d < H) (hθ : θ < 2) (ν : Tape M) (j : ℕ) :
    cellT M x H (d + 1) (2 * ω + θ) 0 ν j =
      cellT M x H d ω θ ν (sel (blk M x H d ω θ ν) * bsz H d + j) := by
  unfold cellT
  rw [ptime_child_zero' d ω θ hdH hθ, off_child d ω θ hθ]
  push_cast
  ring_nf

theorem extT_up {d ω θ : ℕ} (hdH : d < H) (hθ : θ < 2) :
    extT M x H (d + 1) (2 * ω + θ) 0 = extT M x H d ω θ := by
  unfold extT
  rw [ptime_child_zero' d ω θ hdH hθ]

theorem extT_down {d ω θ : ℕ} (hdH : d < H) :
    extT M x H d ω (θ + 1) = extT M x H (d + 1) (2 * ω + θ) 2 := by
  unfold extT
  rw [ptime_child_end d ω θ hdH]

lemma ptime_base (ω θ : ℕ) : ptime H H ω θ = ω + θ / 2 := by
  simp [ptime]

/-- The scanned symbols at the start of a base call. -/
def scanT (M : Machine) (x : List Bool) (ω : ℕ) : Tape M → Sym M := fun ν => (runOn M x ω).tape ν (hd M x ω ν)

theorem extT_base (ω : ℕ) :
    extT M x H H ω 2 = nextExt (extT M x H H ω 0) (scanT M x ω) := by
  unfold extT
  rw [ptime_base, ptime_base, show ω + 2 / 2 = ω + 1 by norm_num, runOn_succ, step_ext]
  rfl

theorem cellT_base (ω : ℕ) (ν : Tape M) (j : ℕ) :
    cellT M x H H ω 2 ν j =
      nextCell (extT M x H H ω 0) (scanT M x ω) ν (rel M x H H ω 0 ν) j
        (cellT M x H H ω 0 ν j) := by
  unfold cellT extT rel
  rw [ptime_base, ptime_base, show ω + 2 / 2 = ω + 1 by norm_num, runOn_succ,
    step_cell _ ν (off M x H H ω ν)]
  simp only [add_sub_cancel_left, Nat.zero_div, add_zero]; rfl

theorem cellT_root (ν : Tape M) (j : ℕ) :
    cellT M x H 0 0 0 ν j = cfgCell (init M x) ν ((j : ℤ) - 2 ^ H) := by
  unfold cellT
  simp [ptime, off, runOn_zero]
  ring_nf

theorem extT_root : extT M x H 0 0 0 = (0, none) := by
  simp [extT, ptime, runOn_zero, cfgExt, init]

theorem extT_query : extT M x H 0 0 2 = cfgExt (runOn M x (2 ^ H)) := by
  simp [extT, ptime]

end Lax119563Proofs.Circuits

end Circuits_Windows

/-! ### Formerly `Lax119563Proofs.Circuits.Verifier` -/

section Circuits_Verifier

/-!
# The verifier program

The control locations and moves of the register program simulating a machine `M` on input
`x`, for the horizon `H` (later `H = s ℓ - 2`). The address `A` of a claim at depth `d` holds
the call `ω = A / 2^(H - d + 2)` and the window position `j = A % 2^(H - d + 2)`. For a call
at depth `d < H`, the bits `H - d - 1, H - d, H - d + 1` of `A` form the block number of `j`
(blocks of size `2^(H - d - 1)`); the top one of them is the phase bit of a child claim.

Locations:
* `cell d θ ν c`, `state d θ p`, `headIn d θ ν u`: the claims (see `Sem`);
* `headSet`, `restore`, `gather`: the field rewrites of the head test, the restore rule and
  the gather rule, after the head block `β` has been guessed;
* `baseCell`, `baseState`, `setJ`: the fork chains of the base calls;
* `query`, `accept`, `reject`.

The input enters only through the guards `hitGuard` (membership tables of register `0`).
-/

namespace Lax119563Proofs.Circuits

open Lax489179.TuringMachine Lax119563.DeterministicTime

/-- A guessed row of a base call: the extended state, the head positions (`1` or `2`, stored
as `0` or `1`) and the scanned symbols. -/
abbrev Row (M : Machine) := ExtState M × (Tape M → Fin 2) × (Tape M → Sym M)

/-- Control locations of the verifier. -/
inductive Loc (M : Machine) (H : ℕ) where
  | accept
  | reject
  | query
  | cell (d : Fin (H + 1)) (θ : Fin 3) (ν : Tape M) (c : CellVal M)
  | state (d : Fin (H + 1)) (θ : Fin 3) (p : ExtState M)
  | headIn (d : Fin (H + 1)) (θ : Fin 2) (ν : Tape M) (u : Fin (H + 1))
  | headSet (d : Fin (H + 1)) (θ : Fin 2) (ν : Tape M) (β : Fin 8)
  | restore (d : Fin (H + 1)) (θ : Fin 2) (ν : Tape M) (c : CellVal M) (β : Fin 8)
  | gather (d : Fin (H + 1)) (θ : Fin 2) (ν : Tape M) (c : CellVal M) (β : Fin 8)
  | baseCell (ν : Tape M) (ρ : Row M) (old : CellVal M) (k : Fin (M.tapes + 2))
  | baseState (ρ : Row M) (k : Fin (M.tapes + 2))
  | setJ (ν : Tape M) (h : Fin 4) (c : CellVal M)

/-! ## Enumerations -/

/-- All Booleans. -/
def allBool : List Bool := [false, true]
/-- All optional Booleans. -/
def allOptBool : List (Option Bool) := [none, some false, some true]
/-- All cell values. -/
def allCV (M : Machine) : List (CellVal M) := List.finRange _ ×ˢ allBool
/-- All extended states. -/
def allExt (M : Machine) : List (ExtState M) := List.finRange _ ×ˢ allOptBool
/-- All functions `Fin m → Fin n`. -/
def allFun (m n : ℕ) : List (Fin m → Fin n) := (List.finRange _).map finFunctionFinEquiv.symm
/-- All rows. -/
def allRows (M : Machine) : List (Row M) :=
  allExt M ×ˢ (allFun (M.tapes + 1) 2 ×ˢ allFun (M.tapes + 1) (M.symbols + 3))

@[simp] lemma mem_allBool (b : Bool) : b ∈ allBool := by cases b <;> simp [allBool]
@[simp] lemma mem_allOptBool (b : Option Bool) : b ∈ allOptBool := by
  rcases b with _ | _ | _ <;> simp [allOptBool]
@[simp] lemma mem_allCV {M : Machine} (c : CellVal M) : c ∈ allCV M := by
  obtain ⟨a, b⟩ := c
  simp [allCV, List.mem_product]
@[simp] lemma mem_allExt {M : Machine} (p : ExtState M) : p ∈ allExt M := by
  obtain ⟨a, b⟩ := p
  simp [allExt, List.mem_product]
@[simp] lemma mem_allFun {m n : ℕ} (f : Fin m → Fin n) : f ∈ allFun m n := by
  simp only [allFun, List.mem_map, List.mem_finRange, true_and]
  exact ⟨_, Equiv.symm_apply_apply _ _⟩
@[simp] lemma mem_allRows {M : Machine} (ρ : Row M) : ρ ∈ allRows M := by
  obtain ⟨a, b, c⟩ := ρ
  simp [allRows, List.mem_product]

section Defs

variable (M : Machine) (x : List Bool) (s ℓ H : ℕ)

/-- The start of the block field of a call at depth `d < H`. -/
def bpos (d : ℕ) : ℕ := H - d - 1

/-- The guard of a root cell at a position `T + u` with `u < 2^ℓ` (register `0` holds `u`,
the other registers agree with `T = 2^H`) whose initial value is `c`. -/
def hitGuard (ν : Tape M) (c : CellVal M) : Fin s → ℕ → Bool :=
  fun i v => if i.val = 0 then decide (cfgCell (init M x) ν (v : ℤ) = c)
    else decide (v = field (2 ^ H) (i * ℓ) ℓ)

/-- The guard of a root cell outside `[T, T + 2^ℓ)`: register `i₀ ≠ 0` differs from `T`. -/
def missGuard (i₀ : Fin s) : Fin s → ℕ → Bool :=
  fun i v => if i = i₀ then decide (v ≠ field (2 ^ H) (i * ℓ) ℓ) else true

variable {M H}

/-- Depth `d + 1` for `d < H`. -/
def dsucc (d : Fin (H + 1)) (h : d.val < H) : Fin (H + 1) := ⟨d.val + 1, by omega⟩

/-- Depth `d - 1`. -/
def dpred (d : Fin (H + 1)) : Fin (H + 1) := ⟨d.val - 1, by omega⟩

/-- The previous phase `θ - 1` for `θ ∈ {1, 2}`. -/
def ppred (θ : Fin 3) : Fin 2 := ⟨(θ.val - 1) % 2, Nat.mod_lt _ (by norm_num)⟩

variable (M H)

/-- The moves at each location. -/
def moves : Loc M H → List (Move (Loc M H) s)
  | .accept => []
  | .reject => []
  | .query =>
    ((allExt M).filter fun p => decide (p.2 = some true)).map fun p => .goto (.state 0 2 p)
  | .cell d θ ν c =>
    if θ.val = 0 then
      if d.val = 0 then
        .test (hitGuard M x s ℓ H ν c) .accept ::
          (if c = (0, false) then
            ((List.finRange s).filter fun i => decide (i.val ≠ 0)).map fun i =>
              .test (missGuard s ℓ H i) .accept
          else [])
      else
        (List.finRange 2).flatMap fun (θ' : Fin 2) => (List.finRange 8).map fun β =>
          .fork (bpos H (d.val - 1) + 2) 1 θ'.val (.headSet (dpred d) θ' ν β)
            (.gather (dpred d) θ' ν c β)
    else if h : d.val < H then
      (List.finRange 8).map fun β =>
        .fork' (.headSet d (ppred θ) ν β) (.restore d (ppred θ) ν c β)
    else if θ.val = 2 then
      (allRows M).flatMap fun ρ => (allCV M).flatMap fun old =>
        ((List.finRange 4).filter fun jj =>
          decide (nextCell ρ.1 ρ.2.2 ν ((ρ.2.1 ν).val + 1 : ℤ) (jj.val : ℤ) old = c)).map
          fun jj => .step 0 2 jj.val jj.val (.baseCell ν ρ old 0)
    else []
  | .state d θ p =>
    if θ.val = 0 then
      if d.val = 0 then
        (if p = (0, none) then [.goto .accept] else [])
      else
        (List.finRange 2).map fun (θ' : Fin 2) =>
          .step (bpos H (d.val - 1) + 2) 1 θ'.val θ'.val (.state (dpred d) θ'.castSucc p)
    else if h : d.val < H then
      (List.finRange 2).map fun (e : Fin 2) =>
        .step (bpos H d + 2) 1 e.val (ppred θ).val (.state (dsucc d h) 2 p)
    else if θ.val = 2 then
      ((allRows M).filter fun ρ => decide (nextExt ρ.1 ρ.2.2 = p)).map fun ρ =>
        .goto (.baseState ρ 0)
    else []
  | .headIn d θ ν u =>
    if u.val < H - d.val then
      if u.val = 0 then
        (List.finRange (M.symbols + 3)).map fun γ => .goto (.cell d θ.castSucc ν (γ, true))
      else
        (List.finRange 2).flatMap fun (e : Fin 2) => (List.finRange 2).map fun (e' : Fin 2) =>
          .step (u.val - 1) 1 e.val e'.val (.headIn d θ ν (dpred u))
    else []
  | .headSet d θ ν β =>
    if d.val < H then
      (List.finRange 8).map fun (q : Fin 8) =>
        .step (bpos H d) 3 q.val β.val (.headIn d θ ν ⟨bpos H d, by unfold bpos; omega⟩)
    else []
  | .restore d θ ν c β =>
    if h : d.val < H then
      (List.finRange 8).map fun (q : Fin 8) =>
        if sel β ≤ q.val ∧ q.val < sel β + 4 then
          .step (bpos H d) 3 q.val (4 * θ.val + (q.val - sel β)) (.cell (dsucc d h) 2 ν c)
        else .step (bpos H d) 3 q.val q.val (.cell d θ.castSucc ν c)
    else []
  | .gather d θ ν c β =>
    if d.val < H then
      (List.finRange 4).map fun (c' : Fin 4) =>
        .step (bpos H d) 3 (4 * θ.val + c'.val) (sel β + c'.val) (.cell d θ.castSucc ν c)
    else []
  | .baseCell ν ρ old k =>
    if h : k.val < M.tapes + 1 then
      [.fork' (.setJ ⟨k.val, h⟩ ⟨(ρ.2.1 ⟨k.val, h⟩).val + 1, by omega⟩ (ρ.2.2 ⟨k.val, h⟩, true))
        (.baseCell ν ρ old ⟨k.val + 1, by omega⟩)]
    else [.fork' (.state ⟨H, by omega⟩ 0 ρ.1) (.cell ⟨H, by omega⟩ 0 ν old)]
  | .baseState ρ k =>
    if h : k.val < M.tapes + 1 then
      [.fork' (.setJ ⟨k.val, h⟩ ⟨(ρ.2.1 ⟨k.val, h⟩).val + 1, by omega⟩ (ρ.2.2 ⟨k.val, h⟩, true))
        (.baseState ρ ⟨k.val + 1, by omega⟩)]
    else [.goto (.state ⟨H, by omega⟩ 0 ρ.1)]
  | .setJ ν h c =>
    (List.finRange 4).map fun (q : Fin 4) => .step 0 2 q.val h.val (.cell ⟨H, by omega⟩ 0 ν c)

end Defs

end Lax119563Proofs.Circuits

end Circuits_Verifier

/-! ### Formerly `Lax119563Proofs.Circuits.LocCode` -/

section Circuits_LocCode

/-!
# Numbering the locations

An explicit injective numbering `Loc.code : Loc M H → Fin (numLoc M H)` of the verifier's
locations with `numLoc M H = 16 * cM M ^ 3 * radix M H ^ 2`, `radix M H = H + 1 + cM M`: a
location is a tag `< 16` and five fields, written in mixed radix. Only the fields `1` and `4`
(the depths `d` and `u`) grow with `H`; the fields `2`, `3`, `5` are below the constant `cM M`.
So the number of locations is `O_M((H + 1)^2)`.
-/

namespace Lax119563Proofs.Circuits

open Lax489179.TuringMachine

variable {M : Machine} {H : ℕ}

/-- Two digits in radix `F`. -/
def pack (F a b : ℕ) : ℕ := a + F * b

lemma pack_inj {F a b a' b' : ℕ} (ha : a < F) (ha' : a' < F) (h : pack F a b = pack F a' b') :
    a = a' ∧ b = b' := by
  unfold pack at h
  have hF : 0 < F := by omega
  have h1 : (a + F * b) % F = (a' + F * b') % F := by rw [h]
  have h2 : (a + F * b) / F = (a' + F * b') / F := by rw [h]
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt ha'] at h1
  rw [Nat.add_mul_div_left _ _ hF, Nat.add_mul_div_left _ _ hF, Nat.div_eq_of_lt ha,
    Nat.div_eq_of_lt ha'] at h2
  omega

lemma pack_lt {F a b G : ℕ} (ha : a < F) (hb : b < G) : pack F a b < F * G := by
  unfold pack
  have : F * b + F ≤ F * G := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hb
  omega

/-- The number of an option of a Boolean. -/
def encOpt : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

lemma encOpt_lt (b : Option Bool) : encOpt b < 3 := by
  rcases b with _ | _ | _ <;> simp [encOpt]

lemma encOpt_inj {b b' : Option Bool} (h : encOpt b = encOpt b') : b = b' := by
  rcases b with _ | _ | _ <;> rcases b' with _ | _ | _ <;> simp_all [encOpt]

/-- The number of a cell value. -/
def encCV (c : CellVal M) : ℕ := pack 2 (if c.2 then 1 else 0) c.1.val

/-- The number of an extended state. -/
def encExt (p : ExtState M) : ℕ := pack 3 (encOpt p.2) p.1.val

/-- The number of a row. -/
def encRow (ρ : Row M) : ℕ :=
  pack (3 * (M.states + 1)) (encExt ρ.1)
    (pack (2 ^ (M.tapes + 1)) (finFunctionFinEquiv ρ.2.1).val (finFunctionFinEquiv ρ.2.2).val)

lemma encCV_lt (c : CellVal M) : encCV c < 2 * (M.symbols + 3) :=
  pack_lt (by split_ifs <;> omega) c.1.isLt

lemma encExt_lt (p : ExtState M) : encExt p < 3 * (M.states + 1) :=
  pack_lt (encOpt_lt _) p.1.isLt

/-- The number of rows. -/
def rowBound (M : Machine) : ℕ :=
  3 * (M.states + 1) * (2 ^ (M.tapes + 1) * (M.symbols + 3) ^ (M.tapes + 1))

lemma encRow_lt (ρ : Row M) : encRow ρ < rowBound M :=
  pack_lt (encExt_lt _) (pack_lt (finFunctionFinEquiv ρ.2.1).isLt
    (finFunctionFinEquiv ρ.2.2).isLt)

lemma encCV_inj {c c' : CellVal M} (h : encCV c = encCV c') : c = c' := by
  obtain ⟨h1, h2⟩ := pack_inj (by split_ifs <;> omega) (by split_ifs <;> omega) h
  refine Prod.ext (Fin.ext h2) ?_
  revert h1; cases c.2 <;> cases c'.2 <;> simp

lemma encExt_inj {p p' : ExtState M} (h : encExt p = encExt p') : p = p' := by
  obtain ⟨h1, h2⟩ := pack_inj (encOpt_lt _) (encOpt_lt _) h
  exact Prod.ext (Fin.ext h2) (encOpt_inj h1)

lemma encRow_inj {ρ ρ' : Row M} (h : encRow ρ = encRow ρ') : ρ = ρ' := by
  obtain ⟨h1, h2⟩ := pack_inj (encExt_lt _) (encExt_lt _) h
  obtain ⟨h3, h4⟩ := pack_inj (finFunctionFinEquiv ρ.2.1).isLt
    (finFunctionFinEquiv ρ'.2.1).isLt h2
  have e1 := encExt_inj h1
  have e2 := finFunctionFinEquiv.injective (Fin.ext h3)
  have e3 := finFunctionFinEquiv.injective (Fin.ext h4)
  obtain ⟨a, b, c⟩ := ρ
  obtain ⟨a', b', c'⟩ := ρ'
  simp_all

/-- The bound on all constant-size fields. -/
def cM (M : Machine) : ℕ := 9 + (M.tapes + 2) + 2 * (M.symbols + 3) + rowBound M

/-- The radix of the location numbers. -/
def radix (M : Machine) (H : ℕ) : ℕ := H + 1 + cM M

/-- The tag and five fields of a location. -/
def Loc.tuple : Loc M H → ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
  | .accept => (0, 0, 0, 0, 0, 0)
  | .reject => (1, 0, 0, 0, 0, 0)
  | .query => (2, 0, 0, 0, 0, 0)
  | .cell d θ ν c => (3, d, θ, ν, encCV c, 0)
  | .state d θ p => (4, d, θ, encExt p, 0, 0)
  | .headIn d θ ν u => (5, d, θ, ν, u, 0)
  | .headSet d θ ν β => (6, d, θ, ν, β, 0)
  | .restore d θ ν c β => (7, d, θ, ν, encCV c, β)
  | .gather d θ ν c β => (8, d, θ, ν, encCV c, β)
  | .baseCell ν ρ old k => (9, ν, encRow ρ, encCV old, k, 0)
  | .baseState ρ k => (10, encRow ρ, k, 0, 0, 0)
  | .setJ ν h c => (11, ν, h, encCV c, 0, 0)

lemma Loc.tuple_injective : Function.Injective (Loc.tuple (M := M) (H := H)) := by
  intro L L' h
  cases L <;> cases L' <;> simp only [Loc.tuple, Prod.mk.injEq] at h <;>
    (try omega) <;>
    (try simp only [Loc.cell.injEq, Loc.state.injEq, Loc.headIn.injEq, Loc.headSet.injEq,
      Loc.restore.injEq, Loc.gather.injEq, Loc.baseCell.injEq, Loc.baseState.injEq,
      Loc.setJ.injEq]) <;>
    (try exact ⟨Fin.ext h.2.1, Fin.ext h.2.2.1, Fin.ext h.2.2.2.1, encCV_inj h.2.2.2.2.1⟩) <;>
    (try exact ⟨Fin.ext h.2.1, Fin.ext h.2.2.1, encExt_inj h.2.2.2.1⟩) <;>
    (try exact ⟨Fin.ext h.2.1, Fin.ext h.2.2.1, Fin.ext h.2.2.2.1, Fin.ext h.2.2.2.2.1⟩) <;>
    (try exact ⟨Fin.ext h.2.1, Fin.ext h.2.2.1, Fin.ext h.2.2.2.1, encCV_inj h.2.2.2.2.1,
      Fin.ext h.2.2.2.2.2⟩) <;>
    (try exact ⟨Fin.ext h.2.1, encRow_inj h.2.2.1, encCV_inj h.2.2.2.1, Fin.ext h.2.2.2.2.1⟩) <;>
    (try exact ⟨encRow_inj h.2.1, Fin.ext h.2.2.1⟩) <;>
    (try exact ⟨Fin.ext h.2.1, Fin.ext h.2.2.1, encCV_inj h.2.2.2.1⟩)

lemma cM_pos : 0 < cM M := by unfold cM; omega

lemma cM_le_radix : cM M ≤ radix M H := by unfold radix; omega

/-- The fields `1` and `4` (the depths `d`, `u`) are below `radix M H`; the fields `2`, `3`, `5`
are constant-size, below `cM M`. -/
lemma Loc.tuple_lt (L : Loc M H) :
    L.tuple.1 < 16 ∧ L.tuple.2.1 < radix M H ∧ L.tuple.2.2.1 < cM M ∧
      L.tuple.2.2.2.1 < cM M ∧ L.tuple.2.2.2.2.1 < radix M H ∧
      L.tuple.2.2.2.2.2 < cM M := by
  have hcv : ∀ c : CellVal M, encCV c < cM M := fun c => by
    have := encCV_lt c; unfold cM; omega
  have hex : ∀ p : ExtState M, encExt p < cM M := fun p => by
    have := encExt_lt p
    have : 3 * (M.states + 1) ≤ rowBound M := by
      unfold rowBound
      exact Nat.le_mul_of_pos_right _ (by positivity)
    unfold cM; omega
  have hrw : ∀ ρ : Row M, encRow ρ < cM M := fun ρ => by
    have := encRow_lt ρ; unfold cM; omega
  have hd : ∀ d : Fin (H + 1), d.val < radix M H := fun d => by
    have := d.isLt; unfold radix; omega
  have hk : ∀ {m : ℕ} (k : Fin m), m ≤ 9 + (M.tapes + 2) → k.val < cM M := fun k hm => by
    have := k.isLt; unfold cM; omega
  have hR : ∀ {a : ℕ}, a < cM M → a < radix M H := fun h => lt_of_lt_of_le h cM_le_radix
  have h0 : 0 < cM M := cM_pos
  have h0' : 0 < radix M H := hR h0
  cases L <;> simp only [Loc.tuple] <;>
    refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | exact h0
    | exact h0'
    | exact hd _
    | exact hcv _
    | exact hex _
    | exact hrw _
    | exact hk _ (by omega)
    | exact hR (hcv _)
    | exact hR (hex _)
    | exact hR (hrw _)
    | exact hR (hk _ (by omega))

/-- The number of location codes: a tag below `16`, two depth digits below `radix M H` and
three constant-size digits below `cM M`. -/
def numLoc (M : Machine) (H : ℕ) : ℕ := 16 * (radix M H * (cM M * (cM M * (radix M H * cM M))))

lemma numLoc_eq : numLoc M H = 16 * cM M ^ 3 * radix M H ^ 2 := by
  unfold numLoc; ring

/-- The number of a location, in mixed radix `16, R, C, C, R, C` (`R = radix M H`,
`C = cM M`). -/
def Loc.code (L : Loc M H) : Fin (numLoc M H) :=
  ⟨pack 16 L.tuple.1 (pack (radix M H) L.tuple.2.1 (pack (cM M) L.tuple.2.2.1
    (pack (cM M) L.tuple.2.2.2.1 (pack (radix M H) L.tuple.2.2.2.2.1
      L.tuple.2.2.2.2.2)))), by
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := L.tuple_lt
    exact pack_lt h0 (pack_lt h1 (pack_lt h2 (pack_lt h3 (pack_lt h4 h5))))⟩

lemma Loc.code_injective : Function.Injective (Loc.code (M := M) (H := H)) := by
  intro L L' h
  have h' := congrArg Fin.val h
  simp only [Loc.code] at h'
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := L.tuple_lt
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := L'.tuple_lt
  obtain ⟨e0, h'⟩ := pack_inj a0 b0 h'
  obtain ⟨e1, h'⟩ := pack_inj a1 b1 h'
  obtain ⟨e2, h'⟩ := pack_inj a2 b2 h'
  obtain ⟨e3, h'⟩ := pack_inj a3 b3 h'
  obtain ⟨e4, e5⟩ := pack_inj a4 b4 h'
  apply Loc.tuple_injective
  ext <;> assumption

end Lax119563Proofs.Circuits

end Circuits_LocCode

/-! ### Formerly `Lax119563Proofs.Circuits.VerifierSem` -/

section Circuits_VerifierSem

/-!
# Meaning of the verifier's locations

`Sem L A` states what the configuration `(L, A)` asserts about the run: e.g. `cell d θ ν c`
at address `A` asserts that the cell at window position `cj d A` of tape `ν` of call
`cω d A` at the start of phase `θ` has value `c`. The program is shown to accept exactly the
configurations whose assertion is true (with `A < 2 ^ (H + 2)`). `rank` decreases along the
moves used in the completeness proof.
-/

namespace Lax119563Proofs.Circuits

open Lax489179.TuringMachine Lax119563.DeterministicTime

section Defs

variable (M : Machine) (x : List Bool) (H : ℕ)

/-- The call encoded in the address `A` of a claim at depth `d`. -/
def cω (d A : ℕ) : ℕ := A / 2 ^ (H - d + 2)

/-- The window position encoded in the address `A` of a claim at depth `d`. -/
def cj (d A : ℕ) : ℕ := A % 2 ^ (H - d + 2)

/-- The claim `cell d θ ν c` at address `A`. -/
def semCell (d θ : ℕ) (ν : Tape M) (c : CellVal M) (A : ℕ) : Prop :=
  (θ = 1 → d < H) ∧ cellT M x H d (cω H d A) θ ν (cj H d A) = c

/-- The claim `state d θ p` at address `A`. -/
def semState (d θ : ℕ) (p : ExtState M) (A : ℕ) : Prop :=
  (θ = 1 → d < H) ∧ extT M x H d (cω H d A) θ = p

/-- The claim `headIn d θ ν u` at address `A`: the head lies at a window position that agrees
with `cj d A` except possibly in the lowest `u` bits. -/
def semHead (d θ : ℕ) (ν : Tape M) (u A : ℕ) : Prop :=
  u < H - d ∧ ∃ y < 2 ^ u, rel M x H d (cω H d A) θ ν = (cj H d (setBits A 0 u y) : ℤ)

/-- The meaning of a configuration of the verifier. -/
def Sem : Loc M H → ℕ → Prop
  | .accept, _ => True
  | .reject, _ => False
  | .query, _ => (cfgExt (runOn M x (2 ^ H))).2 = some true
  | .cell d θ ν c, A => semCell M x H d θ ν c A
  | .state d θ p, A => semState M x H d θ p A
  | .headIn d θ ν u, A => semHead M x H d θ ν u A
  | .headSet d θ ν β, A => d.val < H ∧
      semHead M x H d θ ν (bpos H d) (setBits A (bpos H d) 3 β)
  | .restore d θ ν c β, A => d.val < H ∧
      if sel β ≤ field A (bpos H d) 3 ∧ field A (bpos H d) 3 < sel β + 4 then
        semCell M x H (d + 1) 2 ν c
          (setBits A (bpos H d) 3 (4 * θ.val + (field A (bpos H d) 3 - sel β)))
      else semCell M x H d θ ν c A
  | .gather d θ ν c β, A => d.val < H ∧ field A (bpos H d) 3 / 4 = θ.val ∧
      semCell M x H d θ ν c (setBits A (bpos H d) 3 (sel β + field A (bpos H d) 3 % 4))
  | .baseCell ν ρ old k, A =>
      (∀ i : Tape M, k.val ≤ i.val →
        semCell M x H H 0 i (ρ.2.2 i, true) (setBits A 0 2 ((ρ.2.1 i).val + 1))) ∧
      semState M x H H 0 ρ.1 A ∧ semCell M x H H 0 ν old A
  | .baseState ρ k, A =>
      (∀ i : Tape M, k.val ≤ i.val →
        semCell M x H H 0 i (ρ.2.2 i, true) (setBits A 0 2 ((ρ.2.1 i).val + 1))) ∧
      semState M x H H 0 ρ.1 A
  | .setJ ν h c, A => semCell M x H H 0 ν c (setBits A 0 2 h)

/-- Level weights of the rank. -/
def wG : ℕ := M.tapes + 4
/-- Base level of the phase-zero claims. -/
def wP : ℕ := wG M * (H + 2)
/-- Spacing of the depths among the phase-zero claims. -/
def wQ : ℕ := H + 4
/-- Multiplier of the time in the rank. -/
def wK : ℕ := wP M H + 2 * (H + 1) * wQ H

/-- The rank of a configuration: the time it refers to, then a level. -/
def rank : Loc M H → ℕ → ℕ
  | .accept, _ => 0
  | .reject, _ => 0
  | .query, _ => (2 ^ H + 1) * wK M H
  | .cell d θ _ _, A => ptime H d (cω H d A) θ * wK M H +
      (if θ.val = 0 then wP M H + 2 * d * wQ H else wG M * (H - d) + wG M - 1)
  | .state d θ _, A => ptime H d (cω H d A) θ * wK M H +
      (if θ.val = 0 then wP M H + 2 * d * wQ H else wG M * (H - d) + wG M - 1)
  | .headIn d θ _ u, A => ptime H d (cω H d A) θ * wK M H + wP M H + 2 * d * wQ H + 1 + u
  | .headSet d θ _ _, A => ptime H d (cω H d A) θ * wK M H + wP M H + 2 * d * wQ H + H + 2
  | .gather d θ _ _ _, A => ptime H d (cω H d A) θ * wK M H + wP M H + 2 * d * wQ H + H + 2
  | .restore d θ _ _ _, A => ptime H d (cω H d A) (θ + 1) * wK M H +
      (wG M * (H - d) + wG M - 2)
  | .baseCell _ _ _ k, A => ptime H H (cω H H A) 2 * wK M H + (M.tapes + 2 - k)
  | .baseState _ k, A => ptime H H (cω H H A) 2 * wK M H + (M.tapes + 2 - k)
  | .setJ _ _ _, A => ptime H H (cω H H A) 2 * wK M H

end Defs

/-! ## Address arithmetic -/

section Arith

variable {H : ℕ}

lemma cω_lt {d A : ℕ} (hd : d ≤ H) (hA : A < 2 ^ (H + 2)) : cω H d A < 2 ^ d := by
  unfold cω
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
  rwa [show d + (H - d + 2) = H + 2 by omega]

lemma cω_setBits {d A k m v : ℕ} (hv : v < 2 ^ m) (h : k + m ≤ H - d + 2) :
    cω H d (setBits A k m v) = cω H d A :=
  setBits_div_of_le hv h

lemma bpos_add_three {d : ℕ} (hd : d < H) : H - d + 2 = bpos H d + 3 := by
  unfold bpos; omega

lemma bpos_add_two {d : ℕ} (_hd : d < H) : H - (d + 1) + 2 = bpos H d + 2 := by
  unfold bpos; omega

lemma bsz_eq_bpos (d : ℕ) : bsz H d = 2 ^ bpos H d := rfl

lemma cj_eq {d : ℕ} (hd : d < H) (A : ℕ) :
    cj H d A = field A (bpos H d) 3 * 2 ^ bpos H d + A % 2 ^ bpos H d := by
  unfold cj
  rw [bpos_add_three hd, show bpos H d + 3 = bpos H d + 3 by rfl, mod_eq_field_add]

lemma cω_child {d : ℕ} (hd : d < H) (A : ℕ) :
    cω H (d + 1) A = 2 * cω H d A + field A (bpos H d) 3 / 4 := by
  unfold cω
  rw [bpos_add_two hd, bpos_add_three hd]
  exact (split_field3 A _).1

lemma cj_child {d : ℕ} (hd : d < H) (A : ℕ) :
    cj H (d + 1) A = field A (bpos H d) 3 % 4 * 2 ^ bpos H d + A % 2 ^ bpos H d := by
  unfold cj
  rw [bpos_add_two hd]
  exact (split_field3 A _).2

lemma field_top_bit (A k : ℕ) : field A (k + 2) 1 = field A k 3 / 4 := by
  unfold field
  rw [show (2 : ℕ) ^ 3 = 4 * 2 by norm_num, Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul]
  rw [pow_add]; norm_num

lemma setBits_self {A k m q : ℕ} (h : field A k m = q) : setBits A k m q = A := by
  rw [setBits, h, Nat.xor_self, Nat.zero_shiftLeft, Nat.xor_zero]

lemma cj_setBits_low {d : ℕ} (hd : d < H) {A' y : ℕ} (hy : y < 2 ^ bpos H d) :
    cj H d (setBits A' 0 (bpos H d) y) = field A' (bpos H d) 3 * 2 ^ bpos H d + y := by
  rw [cj_eq hd, field_setBits_of_disjoint hy (Or.inr (by simp)), ← field_zero_eq_mod,
    field_setBits hy]

/-- Merging a bit replacement into a low-bits replacement. -/
lemma setBits_merge {A n e y : ℕ} (he : e < 2 ^ 1) (hy : y < 2 ^ n) :
    setBits (setBits A n 1 e) 0 n y = setBits A 0 (n + 1) (setBits y n 1 e) := by
  have hy' : setBits y n 1 e < 2 ^ (n + 1) :=
    setBits_lt he (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) (by omega))) le_rfl
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_setBits hy, testBit_setBits hy', testBit_setBits he]
  by_cases h1 : i < n
  · rw [if_pos (by omega), if_pos (by omega), testBit_setBits he, if_neg (by omega)]
  · by_cases h2 : i = n
    · subst h2
      rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), testBit_setBits he,
        if_pos (by omega)]
      simp
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- Splitting a low-bits value into its top bit and the rest. -/
lemma split_low {n y : ℕ} (hy : y < 2 ^ (n + 1)) :
    setBits (y % 2 ^ n) n 1 (field y n 1) = y := by
  have hf : field y n 1 < 2 ^ 1 := field_lt _ _ _
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_setBits hf]
  split_ifs with h
  · rw [testBit_field, show i - n = 0 by omega]
    simp [show 0 + n = i by omega]
  · rw [Nat.testBit_mod_two_pow]
    by_cases h' : i < n
    · simp [h']
    · simp only [h', decide_false, Bool.false_and]
      exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hy
        (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

end Arith

end Lax119563Proofs.Circuits

end Circuits_VerifierSem

/-! ### Formerly `Lax119563Proofs.Circuits.VerifierLemmas` -/

section Circuits_VerifierLemmas

/-!
# Semantic rules of the verifier

The rules of `Windows` restated in terms of addresses: guessing the head block, restoring
after a phase, gathering the input of a child, moving state claims up and down the tree,
base calls, and the root input tests.
-/

namespace Lax119563Proofs.Circuits

open Lax489179.TuringMachine Lax119563.DeterministicTime

variable {M : Machine} {x : List Bool} {H : ℕ}

/-- The guessed head block `β` is correct iff the head test at block `β` holds. -/
lemma headBlock_iff {d θ A β : ℕ} (hd : d < H) (hA : A < 2 ^ (H + 2)) (hθ : θ < 2)
    (hβ : β < 2 ^ 3) (ν : Tape M) :
    semHead M x H d θ ν (bpos H d) (setBits A (bpos H d) 3 β) ↔
      blk M x H d (cω H d A) θ ν = β := by
  have hω : cω H d (setBits A (bpos H d) 3 β) = cω H d A :=
    cω_setBits hβ (by rw [bpos_add_three hd])
  have hB : (bsz H d : ℤ) = 2 ^ bpos H d := by rw [bsz_eq_bpos]; push_cast; rfl
  unfold semHead
  rw [hω]
  constructor
  · rintro ⟨-, y, hy, hrel⟩
    rw [cj_setBits_low hd hy, field_setBits hβ] at hrel
    apply blk_eq
    · rw [hrel, hB]; push_cast; linarith
    · rw [hrel, hB]; push_cast
      have : (y : ℤ) < 2 ^ bpos H d := by exact_mod_cast hy
      linarith
  · intro hblk
    obtain ⟨-, -, e1, e2, -⟩ := phase_facts (x := x) hd hθ ν
      (rel_mem d hd.le _ (cω_lt hd.le hA) ν)
    rw [hblk, hB] at e1 e2
    refine ⟨by unfold bpos; omega, (rel M x H d (cω H d A) θ ν - β * 2 ^ bpos H d).toNat, ?_, ?_⟩
    · have : rel M x H d (cω H d A) θ ν - β * 2 ^ bpos H d < 2 ^ bpos H d := by linarith
      have h2 : ((2 ^ bpos H d : ℕ) : ℤ) = 2 ^ bpos H d := by push_cast; rfl
      omega
    · rw [cj_setBits_low hd, field_setBits hβ]
      · push_cast
        rw [Int.toNat_of_nonneg (by linarith)]
        ring
      · have : rel M x H d (cω H d A) θ ν - β * 2 ^ bpos H d < 2 ^ bpos H d := by linarith
        have h2 : ((2 ^ bpos H d : ℕ) : ℤ) = 2 ^ bpos H d := by push_cast; rfl
        omega

lemma cj_div_bsz {d A : ℕ} (hd : d < H) : cj H d A / bsz H d = field A (bpos H d) 3 := by
  rw [cj_eq hd, bsz_eq_bpos, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt (Nat.mod_lt _ (by positivity)), zero_add]

lemma cj_mod_bsz {d A : ℕ} (hd : d < H) : cj H d A % bsz H d = A % 2 ^ bpos H d := by
  rw [cj_eq hd, bsz_eq_bpos, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_mod]

/-- The restore rule in terms of addresses. -/
lemma restore_iff {d θ A β : ℕ} (hd : d < H) (hA : A < 2 ^ (H + 2)) (hθ : θ < 2)
    (ν : Tape M) (c : CellVal M) (hβ : blk M x H d (cω H d A) θ ν = β) :
    (if sel β ≤ field A (bpos H d) 3 ∧ field A (bpos H d) 3 < sel β + 4 then
        semCell M x H (d + 1) 2 ν c
          (setBits A (bpos H d) 3 (4 * θ + (field A (bpos H d) 3 - sel β)))
      else semCell M x H d θ ν c A) ↔ semCell M x H d (θ + 1) ν c A := by
  have hres := cellT_restore (x := x) hd (cω_lt hd.le hA) hθ ν (cj H d A)
  rw [cj_div_bsz hd, cj_mod_bsz hd, hβ] at hres
  unfold semCell
  rw [hres]
  split_ifs with hin
  · set f := field A (bpos H d) 3
    have hv : 4 * θ + (f - sel β) < 2 ^ 3 := by norm_num; omega
    have h1 : cω H (d + 1) (setBits A (bpos H d) 3 (4 * θ + (f - sel β))) =
        2 * cω H d A + θ := by
      rw [cω_child hd, field_setBits hv, cω_setBits hv (by rw [bpos_add_three hd])]
      congr 1; omega
    have h2 : cj H (d + 1) (setBits A (bpos H d) 3 (4 * θ + (f - sel β))) =
        (f - sel β) * bsz H d + A % 2 ^ bpos H d := by
      rw [cj_child hd, field_setBits hv, setBits_mod hv, bsz_eq_bpos]
      congr 2; omega
    rw [h1, h2]
    simp [hd]
  · constructor <;> rintro ⟨-, h⟩ <;> exact ⟨fun _ => hd, h⟩

/-- The gather rule in terms of addresses. -/
lemma gather_iff {d θ A β : ℕ} (hd : d < H) (hθ : θ < 2) (ν : Tape M) (c : CellVal M)
    (hβ : blk M x H d (cω H d A) θ ν = β) (hf : field A (bpos H d) 3 / 4 = θ) :
    semCell M x H d θ ν c (setBits A (bpos H d) 3 (sel β + field A (bpos H d) 3 % 4)) ↔
      semCell M x H (d + 1) 0 ν c A := by
  subst hf
  have hsel : sel β ≤ 4 := min_le_right _ _
  have hv : sel β + field A (bpos H d) 3 % 4 < 2 ^ 3 := by
    have := Nat.mod_lt (field A (bpos H d) 3) (by norm_num : 4 > 0); norm_num; omega
  unfold semCell
  rw [cω_child hd, cj_child hd, cellT_gather hd (by omega), hβ,
    cω_setBits hv (by rw [bpos_add_three hd]), cj_eq hd, field_setBits hv, setBits_mod hv,
    bsz_eq_bpos]
  have : (sel β + field A (bpos H d) 3 % 4) * 2 ^ bpos H d + A % 2 ^ bpos H d =
      sel β * 2 ^ bpos H d + (field A (bpos H d) 3 % 4 * 2 ^ bpos H d + A % 2 ^ bpos H d) := by
    ring
  rw [this]
  constructor <;> rintro ⟨-, h⟩ <;> exact ⟨fun _ => by omega, h⟩

/-- A child state claim at phase `0` is the parent's state claim at the child's phase. -/
lemma stateUp_iff {d θ A : ℕ} (hd : d < H) (hθ : θ < 2) (p : ExtState M)
    (hf : field A (bpos H d + 2) 1 = θ) :
    semState M x H d θ p A ↔ semState M x H (d + 1) 0 p A := by
  rw [field_top_bit] at hf
  unfold semState
  rw [cω_child hd, hf, extT_up hd hθ]
  simp [hd]

/-- A state claim at phase `θ + 1` is the final state claim of child `θ`. -/
lemma stateDown_iff {d θ A : ℕ} (hd : d < H) (hθ : θ < 2) (p : ExtState M) :
    semState M x H (d + 1) 2 p (setBits A (bpos H d + 2) 1 θ) ↔
      semState M x H d (θ + 1) p A := by
  have hv : θ < 2 ^ 1 := by simpa using hθ
  unfold semState
  rw [cω_child hd, ← field_top_bit, field_setBits hv,
    cω_setBits hv (by rw [bpos_add_three hd])]
  try rw [← extT_down hd]
  try simp [hd]

/-! ## Base calls -/

lemma cω_base (A : ℕ) : cω H H A = A / 4 := by simp [cω]

lemma cj_base (A : ℕ) : cj H H A = A % 4 := by simp [cj]

/-- A head claim of a base call. -/
lemma baseHead_iff {A h : ℕ} (hh : h < 2 ^ 2) (ν : Tape M) (γ : Sym M) :
    semCell M x H H 0 ν (γ, true) (setBits A 0 2 h) ↔
      rel M x H H (A / 4) 0 ν = h ∧ scanT M x (A / 4) ν = γ := by
  have h1 : cω H H (setBits A 0 2 h) = A / 4 := by
    rw [cω_base, show (4 : ℕ) = 2 ^ (0 + 2) by norm_num, setBits_div hh]
  have h2 : cj H H (setBits A 0 2 h) = h := by
    rw [cj_base, show (4 : ℕ) = 2 ^ 2 by norm_num, ← field_zero_eq_mod, field_setBits hh]
  unfold semCell
  rw [h1, h2]
  have hc : cellT M x H H (A / 4) 0 ν h = ((runOn M x (A / 4)).tape ν
      (off M x H H (A / 4) ν + h), decide ((runOn M x (A / 4)).head ν =
        off M x H H (A / 4) ν + h)) := by
    simp [cellT, cfgCell, ptime_base]
  rw [hc]
  simp only [rel, scanT, hd, ptime_base, Nat.zero_div, add_zero, Prod.mk.injEq,
    decide_eq_true_eq]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨by rw [h2]; ring, by rw [h2]; exact h1⟩
  · rintro ⟨h1, h2⟩
    have : (runOn M x (A / 4)).head ν = off M x H H (A / 4) ν + h := by linarith
    exact ⟨by simp, by rw [← this]; exact h2, this⟩

/-! ## The root -/

lemma init_cell_outside {z : ℤ} (hz : z < 0 ∨ ((x.length : ℤ) ≤ z ∧ 0 < z)) (ν : Tape M) :
    cfgCell (init M x) ν z = (0, false) := by
  unfold cfgCell init
  simp only [Prod.mk.injEq]
  constructor
  · split_ifs with h
    · rcases hz with hz | ⟨hz1, -⟩
      · omega
      · have : x[z.toNat]? = none := List.getElem?_eq_none (by omega)
        rw [this]
    · rfl
  · simp only [decide_eq_false_iff_not]
    omega

/-- Agreement of the registers above register `0`. -/
lemma regs_agree_iff {s ℓ A T : ℕ} (hA : A < 2 ^ (s * ℓ)) (hT : T < 2 ^ (s * ℓ)) :
    (∀ i : Fin s, i.val ≠ 0 → field A (i * ℓ) ℓ = field T (i * ℓ) ℓ) ↔
      A / 2 ^ ℓ = T / 2 ^ ℓ := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro t
    rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
    by_cases ht : t + ℓ < s * ℓ
    · have hℓ : 0 < ℓ := by
        rcases Nat.eq_zero_or_pos ℓ with h0 | h0
        · subst h0; simp at ht
        · exact h0
      set i := (t + ℓ) / ℓ
      have hi : i < s := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      have hi0 : i ≠ 0 := by
        have : 1 ≤ i := (Nat.le_div_iff_mul_le hℓ).mpr (by omega)
        omega
      have key := congrArg (fun v => v.testBit ((t + ℓ) % ℓ)) (h ⟨i, hi⟩ hi0)
      simp only [testBit_field, Nat.mod_lt _ hℓ, decide_true, Bool.true_and] at key
      have e : (t + ℓ) % ℓ + i * ℓ = t + ℓ := Nat.mod_add_div' _ _
      rwa [e] at key
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hA (Nat.pow_le_pow_right (by norm_num)
        (by omega))), Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hT
          (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  · intro h i hi
    apply Nat.eq_of_testBit_eq
    intro t
    rw [testBit_field, testBit_field]
    by_cases ht : t < ℓ
    · simp only [ht, decide_true, Bool.true_and]
      have hle : ℓ ≤ t + i * ℓ := by
        have : 1 ≤ i.val := Nat.pos_of_ne_zero hi
        nlinarith
      have := congrArg (fun v => v.testBit (t + i * ℓ - ℓ)) h
      simp only [Nat.testBit_div_two_pow, Nat.sub_add_cancel hle] at this
      exact this
    · simp [ht]

end Lax119563Proofs.Circuits

end Circuits_VerifierLemmas

/-! ### Formerly `Lax119563Proofs.Circuits.VerifierSound` -/

section Circuits_VerifierSound

/-!
# Soundness of the verifier's moves

Every move of the verifier is well-formed (its fields lie inside the address) and sound for
`Sem`: if the targets' assertions hold, so does the source's.
-/

namespace Lax119563Proofs.Circuits

open Lax489179.TuringMachine Lax119563.DeterministicTime

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

@[simp] lemma dpred_val (d : Fin (H + 1)) : (dpred d).val = d.val - 1 := rfl
@[simp] lemma dsucc_val (d : Fin (H + 1)) (h : d.val < H) : (dsucc d h).val = d.val + 1 := rfl
lemma ppred_val {θ : Fin 3} (h : θ.val ≠ 0) : (ppred θ).val + 1 = θ.val := by
  have := θ.isLt
  simp only [ppred]
  omega

lemma moves_wf (L : Loc M H) :
    ∀ mv ∈ moves M x s ℓ H L, mv.WF (H + 2) := by
  have h8 : ∀ q : Fin 8, q.val < 2 ^ 3 := fun q => q.isLt
  have h4 : ∀ q : Fin 4, q.val < 2 ^ 2 := fun q => q.isLt
  have h2 : ∀ q : Fin 2, q.val < 2 ^ 1 := fun q => q.isLt
  cases L with
  | accept => simp [moves]
  | reject => simp [moves]
  | query => simp [moves, Move.goto, Move.WF]
  | cell d θ ν c =>
    intro mv hmv
    simp only [moves] at hmv
    split_ifs at hmv with h0 hd0 hc hdH h2'
    · rcases List.mem_cons.mp hmv with rfl | hmv
      · trivial
      · simp only [List.mem_map, List.mem_filter] at hmv
        obtain ⟨i, -, rfl⟩ := hmv; trivial
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmv
      subst hmv; trivial
    · simp only [List.mem_flatMap, List.mem_map] at hmv
      obtain ⟨θ', -, β, -, rfl⟩ := hmv
      refine ⟨?_, h2 θ'⟩
      unfold bpos; omega
    · simp only [List.mem_map] at hmv
      obtain ⟨β, -, rfl⟩ := hmv
      simp [Move.fork', Move.WF]
    · simp only [List.mem_flatMap, List.mem_map, List.mem_filter] at hmv
      obtain ⟨ρ, -, old, -, jj, -, rfl⟩ := hmv
      exact ⟨by omega, h4 jj, h4 jj⟩
    · simp at hmv
  | state d θ p =>
    intro mv hmv
    simp only [moves] at hmv
    split_ifs at hmv with h0 hd0 hp hdH h2'
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmv
      subst hmv; simp [Move.goto, Move.WF]
    · simp at hmv
    · simp only [List.mem_map] at hmv
      obtain ⟨θ', -, rfl⟩ := hmv
      refine ⟨?_, h2 θ', h2 θ'⟩
      unfold bpos; omega
    · simp only [List.mem_map] at hmv
      obtain ⟨e, -, rfl⟩ := hmv
      refine ⟨?_, h2 e, h2 _⟩
      unfold bpos; omega
    · simp only [List.mem_map, List.mem_filter] at hmv
      obtain ⟨ρ, -, rfl⟩ := hmv
      simp [Move.goto, Move.WF]
    · simp at hmv
  | headIn d θ ν u =>
    intro mv hmv
    simp only [moves] at hmv
    split_ifs at hmv with hu hu0
    · simp only [List.mem_map] at hmv
      obtain ⟨γ, -, rfl⟩ := hmv
      simp [Move.goto, Move.WF]
    · simp only [List.mem_flatMap, List.mem_map] at hmv
      obtain ⟨e, -, e', -, rfl⟩ := hmv
      exact ⟨by omega, h2 e, h2 e'⟩
    · simp at hmv
  | headSet d θ ν β =>
    intro mv hmv
    simp only [moves] at hmv
    split_ifs at hmv with hdH
    · simp only [List.mem_map] at hmv
      obtain ⟨q, -, rfl⟩ := hmv
      exact ⟨by unfold bpos; omega, h8 q, h8 β⟩
    · simp at hmv
  | restore d θ ν c β =>
    intro mv hmv
    simp only [moves] at hmv
    split_ifs at hmv with hdH
    · simp only [List.mem_map] at hmv
      obtain ⟨q, -, rfl⟩ := hmv
      split_ifs with hq
      · refine ⟨by unfold bpos; omega, h8 q, ?_⟩
        have := θ.isLt; norm_num; omega
      · exact ⟨by unfold bpos; omega, h8 q, h8 q⟩
    · simp at hmv
  | gather d θ ν c β =>
    intro mv hmv
    simp only [moves] at hmv
    split_ifs at hmv with hdH
    · simp only [List.mem_map] at hmv
      obtain ⟨c', -, rfl⟩ := hmv
      have := θ.isLt
      have := c'.isLt
      have : sel β ≤ 4 := min_le_right _ _
      exact ⟨by unfold bpos; omega, by norm_num; omega, by norm_num; omega⟩
    · simp at hmv
  | baseCell ν ρ old k =>
    intro mv hmv
    simp only [moves] at hmv
    split_ifs at hmv <;>
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmv
      subst hmv; simp [Move.fork', Move.WF]
  | baseState ρ k =>
    intro mv hmv
    simp only [moves] at hmv
    split_ifs at hmv <;>
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmv
      subst hmv; simp [Move.fork', Move.goto, Move.WF]
  | setJ ν h c =>
    intro mv hmv
    simp only [moves, List.mem_map] at hmv
    obtain ⟨q, -, rfl⟩ := hmv
    exact ⟨by omega, h4 q, h4 h⟩

/-! ## Base and root claims -/

lemma semCell_base0 (A : ℕ) (ν : Tape M) (c : CellVal M) :
    semCell M x H H 0 ν c A ↔ cellT M x H H (A / 4) 0 ν (A % 4) = c := by
  simp [semCell, cω_base, cj_base]

lemma semState_base0 (A : ℕ) (p : ExtState M) :
    semState M x H H 0 p A ↔ extT M x H H (A / 4) 0 = p := by
  simp [semState, cω_base]

lemma semCell_base2 (A : ℕ) (ν : Tape M) (c : CellVal M) :
    semCell M x H H 2 ν c A ↔
      nextCell (extT M x H H (A / 4) 0) (scanT M x (A / 4)) ν (rel M x H H (A / 4) 0 ν)
        ((A % 4 : ℕ) : ℤ) (cellT M x H H (A / 4) 0 ν (A % 4)) = c := by
  simp [semCell, cω_base, cj_base, cellT_base]

lemma semState_base2 (A : ℕ) (p : ExtState M) :
    semState M x H H 2 p A ↔ nextExt (extT M x H H (A / 4) 0) (scanT M x (A / 4)) = p := by
  simp [semState, cω_base, extT_base]

lemma baseRow_iff (A : ℕ) (ρ : Row M) :
    (∀ i : Tape M, semCell M x H H 0 i (ρ.2.2 i, true) (setBits A 0 2 ((ρ.2.1 i).val + 1))) ↔
      (∀ i, rel M x H H (A / 4) 0 i = (ρ.2.1 i).val + 1) ∧ scanT M x (A / 4) = ρ.2.2 := by
  have hh : ∀ i, (ρ.2.1 i).val + 1 < 2 ^ 2 := fun i => by have := (ρ.2.1 i).isLt; norm_num; omega
  simp only [fun i => baseHead_iff (x := x) (H := H) (A := A) (hh i) i (ρ.2.2 i)]
  constructor
  · intro h
    exact ⟨fun i => by exact_mod_cast (h i).1, funext fun i => (h i).2⟩
  · rintro ⟨h1, h2⟩ i
    exact ⟨by rw [h1 i]; push_cast; ring, by rw [h2]⟩

lemma semCell_root {A : ℕ} (hA : A < 2 ^ (H + 2)) (ν : Tape M) (c : CellVal M) :
    semCell M x H 0 0 ν c A ↔ cfgCell (init M x) ν ((A : ℤ) - 2 ^ H) = c := by
  have h1 : cω H 0 A = 0 := by simp [cω, Nat.div_eq_of_lt hA]
  have h2 : cj H 0 A = A := by simp [cj, Nat.mod_eq_of_lt hA]
  simp [semCell, h1, h2, cellT_root]

lemma root_hit {A : ℕ} (hℓH : ℓ ≤ H) (h : A / 2 ^ ℓ = 2 ^ H / 2 ^ ℓ) :
    (A : ℤ) - 2 ^ H = ((A % 2 ^ ℓ : ℕ) : ℤ) := by
  have hd : 2 ^ ℓ ∣ 2 ^ H := pow_dvd_pow 2 hℓH
  have e1 := Nat.div_add_mod A (2 ^ ℓ)
  have e2 := Nat.div_mul_cancel hd
  rw [h] at e1
  have : A = 2 ^ H + A % 2 ^ ℓ := by rw [Nat.mul_comm] at e1; omega
  have h3 : (A : ℤ) = 2 ^ H + ((A % 2 ^ ℓ : ℕ) : ℤ) := by exact_mod_cast this
  linarith

lemma root_miss {A : ℕ} (hℓH : ℓ ≤ H) (hx : x.length < 2 ^ ℓ)
    (h : A / 2 ^ ℓ ≠ 2 ^ H / 2 ^ ℓ) (ν : Tape M) :
    cfgCell (init M x) ν ((A : ℤ) - 2 ^ H) = (0, false) := by
  apply init_cell_outside
  by_contra hc
  push Not at hc
  apply h
  have hd : 2 ^ ℓ ∣ 2 ^ H := pow_dvd_pow 2 hℓH
  have hx' : ((x.length : ℕ) : ℤ) < 2 ^ ℓ := by exact_mod_cast hx
  have hpos : (0 : ℤ) < 2 ^ ℓ := by positivity
  -- `A - 2^H ∈ [0, 2^ℓ)`
  have hge : 2 ^ H ≤ A := by
    by_contra hlt
    push Not at hlt
    have : (A : ℤ) < 2 ^ H := by exact_mod_cast hlt
    linarith [hc.1]
  have hlt : A - 2 ^ H < 2 ^ ℓ := by
    by_contra hnot
    have h1 : 2 ^ ℓ ≤ A - 2 ^ H := by omega
    have h2 : ((2 ^ ℓ : ℕ) : ℤ) ≤ ((A - 2 ^ H : ℕ) : ℤ) := by exact_mod_cast h1
    push_cast [hge] at h2
    have := hc.2 (by linarith)
    linarith
  obtain ⟨k, hk⟩ := hd
  have : A = 2 ^ ℓ * k + (A - 2 ^ H) := by omega
  rw [hk, this, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hlt, add_zero,
    Nat.mul_div_cancel_left _ (by positivity)]

/-! ## Soundness of the moves -/

/-- Standing hypotheses on the parameters: the address has `s ℓ ≥ H + 2` bits (the claims use
the low `H + 2` of them), and the input fits into register `0`. -/
structure Params (x : List Bool) (s ℓ H : ℕ) : Prop where
  hH : H + 2 ≤ s * ℓ
  hℓ : 0 < ℓ
  hℓH : ℓ ≤ H
  hx : x.length < 2 ^ ℓ

lemma Params.addr_lt (_P : Params x s ℓ H) {A : ℕ} (hA : A < 2 ^ (H + 2)) : A < 2 ^ (H + 2) :=
  hA

lemma Params.lt_sl (P : Params x s ℓ H) {A : ℕ} (hA : A < 2 ^ (H + 2)) : A < 2 ^ (s * ℓ) :=
  lt_of_lt_of_le hA (Nat.pow_le_pow_right (by norm_num) P.hH)

lemma Params.s_pos (P : Params x s ℓ H) : 0 < s := by
  rcases Nat.eq_zero_or_pos s with h | h
  · have := P.hH; simp [h] at this
  · exact h

lemma Params.T_lt (P : Params x s ℓ H) : 2 ^ H < 2 ^ (s * ℓ) := by
  exact Nat.pow_lt_pow_right (by norm_num) (by have := P.hH; omega)

lemma sound_cell (P : Params x s ℓ H) (d : Fin (H + 1)) (θ : Fin 3) (ν : Tape M)
    (c : CellVal M) : ∀ mv ∈ moves M x s ℓ H (.cell d θ ν c),
      mv.Sound ℓ (H + 2) (Sem M x H) (.cell d θ ν c) := by
  intro mv hmv
  simp only [moves] at hmv
  split_ifs at hmv with h0 hd0 hc hdH h2'
  · -- root, with the miss tests
    rcases List.mem_cons.mp hmv with rfl | hmv
    · intro A hA hen _
      have e0 := hen ⟨0, P.s_pos⟩
      simp only [hitGuard, zero_mul, ↓reduceIte, decide_eq_true_eq, field_zero_eq_mod] at e0
      have eo : ∀ i : Fin s, i.val ≠ 0 → field A (i * ℓ) ℓ = field (2 ^ H) (i * ℓ) ℓ :=
        fun i hi => by simpa [hitGuard, hi] using hen i
      have hdiv := (regs_agree_iff (P.lt_sl hA) P.T_lt).mp eo
      show semCell M x H d θ ν c A
      rw [hd0, h0, semCell_root (P.addr_lt hA), root_hit P.hℓH hdiv, e0]
    · simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and,
        decide_eq_true_eq] at hmv
      obtain ⟨i₀, hi₀, rfl⟩ := hmv
      intro A hA hen _
      have e := hen i₀
      simp only [missGuard, ↓reduceIte, decide_eq_true_eq] at e
      have hdiv : A / 2 ^ ℓ ≠ 2 ^ H / 2 ^ ℓ := fun h =>
        e ((regs_agree_iff (P.lt_sl hA) P.T_lt).mpr h i₀ hi₀)
      show semCell M x H d θ ν c A
      rw [hd0, h0, semCell_root (P.addr_lt hA), root_miss P.hℓH P.hx hdiv, hc]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmv
    subst hmv
    intro A hA hen _
    have e0 := hen ⟨0, P.s_pos⟩
    simp only [hitGuard, zero_mul, ↓reduceIte, decide_eq_true_eq, field_zero_eq_mod] at e0
    have eo : ∀ i : Fin s, i.val ≠ 0 → field A (i * ℓ) ℓ = field (2 ^ H) (i * ℓ) ℓ :=
      fun i hi => by simpa [hitGuard, hi] using hen i
    have hdiv := (regs_agree_iff (P.lt_sl hA) P.T_lt).mp eo
    show semCell M x H d θ ν c A
    rw [hd0, h0, semCell_root (P.addr_lt hA), root_hit P.hℓH hdiv, e0]
  · -- gather from the parent
    simp only [List.mem_flatMap, List.mem_map] at hmv
    obtain ⟨θ', -, β, -, rfl⟩ := hmv
    intro A hA _ hS₁ hS₂
    have hdp : d.val - 1 < H := by omega
    obtain ⟨-, hh⟩ := hS₁
    obtain ⟨-, hf, hg⟩ := hS₂
    simp only [dpred_val] at hh hf hg
    have hblk := (headBlock_iff hdp (P.addr_lt hA) θ'.isLt β.isLt ν).mp hh
    have := (gather_iff hdp θ'.isLt ν c hblk hf).mp hg
    show semCell M x H d θ ν c A
    rwa [h0, show d.val = d.val - 1 + 1 by omega]
  · -- restore after a phase
    simp only [List.mem_map] at hmv
    obtain ⟨β, -, rfl⟩ := hmv
    intro A hA _ hS₁ hS₂
    obtain ⟨-, hh⟩ := hS₁
    obtain ⟨-, hr⟩ := hS₂
    have hblk := (headBlock_iff hdH (P.addr_lt hA) (ppred θ).isLt β.isLt ν).mp hh
    have := (restore_iff hdH (P.addr_lt hA) (ppred θ).isLt ν c hblk).mp hr
    show semCell M x H d θ ν c A
    rwa [ppred_val h0] at this
  · -- base call
    simp only [List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq] at hmv
    obtain ⟨ρ, -, old, -, jj, ⟨-, hnext⟩, rfl⟩ := hmv
    intro A hA hf hS
    rw [setBits_self hf] at hS
    obtain ⟨hrow, hst, hold⟩ := hS
    have hd : d.val = H := by omega
    have hθ : θ.val = 2 := by omega
    obtain ⟨hrel, hscan⟩ := (baseRow_iff A ρ).mp fun i => hrow i (Nat.zero_le _)
    rw [semState_base0] at hst
    have hj : A % 4 = jj.val := by rw [← hf, field_zero_eq_mod]; norm_num
    rw [semCell_base0, hj] at hold
    show semCell M x H d θ ν c A
    rw [hd, hθ, semCell_base2, hst, hscan, hrel ν, hj, hold]
    exact_mod_cast hnext
  · simp at hmv

lemma rel_of_cellT_flag {d ω θ : ℕ} {ν : Tape M} {j : ℕ} {γ : Sym M}
    (h : cellT M x H d ω θ ν j = (γ, true)) : rel M x H d ω θ ν = j := by
  unfold cellT cfgCell at h
  simp only [Prod.mk.injEq, decide_eq_true_eq] at h
  unfold rel hd
  rw [h.2]; ring

lemma moves_sound (P : Params x s ℓ H) (L : Loc M H) :
    ∀ mv ∈ moves M x s ℓ H L, mv.Sound ℓ (H + 2) (Sem M x H) L := by
  cases L with
  | accept => simp [moves]
  | reject => simp [moves]
  | query =>
    intro mv hmv
    simp only [moves, List.mem_map, List.mem_filter, decide_eq_true_eq] at hmv
    obtain ⟨p, ⟨-, hp⟩, rfl⟩ := hmv
    intro A hA _ hS
    rw [setBits_zero_width] at hS
    obtain ⟨-, hS⟩ := hS
    have h1 : cω H 0 A = 0 := by simp [cω, Nat.div_eq_of_lt (P.addr_lt hA)]
    change extT M x H 0 (cω H 0 A) 2 = p at hS
    rw [h1, extT_query] at hS
    show (cfgExt (runOn M x (2 ^ H))).2 = some true
    rw [hS, hp]
  | cell d θ ν c => exact sound_cell P d θ ν c
  | state d θ p =>
    intro mv hmv
    simp only [moves] at hmv
    split_ifs at hmv with h0 hd0 hp hdH h2'
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmv
      subst hmv
      intro A hA _ _
      have h1 : cω H 0 A = 0 := by simp [cω, Nat.div_eq_of_lt (P.addr_lt hA)]
      show semState M x H d θ p A
      unfold semState
      rw [hd0, h0, h1, extT_root, hp]
      simp
    · simp at hmv
    · simp only [List.mem_map] at hmv
      obtain ⟨θ', -, rfl⟩ := hmv
      intro A hA hf hS
      rw [setBits_self hf] at hS
      have hdp : d.val - 1 < H := by omega
      have := (stateUp_iff hdp θ'.isLt p hf).mp hS
      show semState M x H d θ p A
      rwa [h0, show d.val = d.val - 1 + 1 by omega]
    · simp only [List.mem_map] at hmv
      obtain ⟨e, -, rfl⟩ := hmv
      intro A hA _ hS
      have := (stateDown_iff hdH (ppred θ).isLt p).mp hS
      show semState M x H d θ p A
      rwa [ppred_val h0] at this
    · simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hmv
      obtain ⟨ρ, ⟨-, hnext⟩, rfl⟩ := hmv
      intro A hA _ hS
      rw [setBits_zero_width] at hS
      obtain ⟨hrow, hst⟩ := hS
      have hd : d.val = H := by omega
      have hθ : θ.val = 2 := by omega
      obtain ⟨-, hscan⟩ := (baseRow_iff A ρ).mp fun i => hrow i (Nat.zero_le _)
      rw [semState_base0] at hst
      show semState M x H d θ p A
      rw [hd, hθ, semState_base2, hst, hscan, hnext]
    · simp at hmv
  | headIn d θ ν u =>
    intro mv hmv
    simp only [moves] at hmv
    split_ifs at hmv with hu hu0
    · simp only [List.mem_map] at hmv
      obtain ⟨γ, -, rfl⟩ := hmv
      intro A hA _ hS
      rw [setBits_zero_width] at hS
      obtain ⟨-, hS⟩ := hS
      refine ⟨by omega, 0, by simp, ?_⟩
      rw [hu0, setBits_zero_width]
      exact rel_of_cellT_flag hS
    · simp only [List.mem_flatMap, List.mem_map] at hmv
      obtain ⟨e, -, e', -, rfl⟩ := hmv
      intro A hA _ hS
      obtain ⟨-, y', hy', hrel⟩ := hS
      have he' : e'.val < 2 ^ 1 := e'.isLt
      simp only [dpred_val] at hy' hrel
      rw [cω_setBits he' (by omega), setBits_merge he' hy',
        show u.val - 1 + 1 = u.val by omega] at hrel
      refine ⟨hu, _, ?_, hrel⟩
      have := setBits_lt (A := y') (N := u.val - 1 + 1) he'
        (lt_of_lt_of_le hy' (Nat.pow_le_pow_right (by norm_num) (by omega))) le_rfl
      rwa [show u.val - 1 + 1 = u.val by omega] at this
    · simp at hmv
  | headSet d θ ν β =>
    intro mv hmv
    simp only [moves] at hmv
    split_ifs at hmv with hdH
    · simp only [List.mem_map] at hmv
      obtain ⟨q, -, rfl⟩ := hmv
      intro A hA _ hS
      exact ⟨hdH, hS⟩
    · simp at hmv
  | restore d θ ν c β =>
    intro mv hmv
    simp only [moves] at hmv
    split_ifs at hmv with hdH
    · simp only [List.mem_map] at hmv
      obtain ⟨q, -, rfl⟩ := hmv
      split_ifs with hq
      · intro A hA hf hS
        refine ⟨hdH, ?_⟩
        rw [hf, if_pos hq]
        exact hS
      · intro A hA hf hS
        refine ⟨hdH, ?_⟩
        rw [setBits_self hf] at hS
        rw [hf, if_neg hq]
        exact hS
    · simp at hmv
  | gather d θ ν c β =>
    intro mv hmv
    simp only [moves] at hmv
    split_ifs at hmv with hdH
    · simp only [List.mem_map] at hmv
      obtain ⟨c', -, rfl⟩ := hmv
      intro A hA hf hS
      have := c'.isLt
      refine ⟨hdH, by rw [hf]; omega, ?_⟩
      rwa [hf, show (4 * θ.val + c'.val) % 4 = c'.val by omega]
    · simp at hmv
  | baseCell ν ρ old k =>
    intro mv hmv
    simp only [moves] at hmv
    split_ifs at hmv with hk
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmv
      subst hmv
      intro A hA _ hS₁ hS₂
      obtain ⟨hrow, hst, hold⟩ := hS₂
      refine ⟨fun i hi => ?_, hst, hold⟩
      rcases Nat.lt_or_ge k.val i.val with h | h
      · exact hrow i h
      · have : i = ⟨k.val, hk⟩ := Fin.ext (by simp; omega)
        subst this
        exact hS₁
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmv
      subst hmv
      intro A hA _ hS₁ hS₂
      exact ⟨fun i hi => absurd i.isLt (by omega), hS₁, hS₂⟩
  | baseState ρ k =>
    intro mv hmv
    simp only [moves] at hmv
    split_ifs at hmv with hk
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmv
      subst hmv
      intro A hA _ hS₁ hS₂
      obtain ⟨hrow, hst⟩ := hS₂
      refine ⟨fun i hi => ?_, hst⟩
      rcases Nat.lt_or_ge k.val i.val with h | h
      · exact hrow i h
      · have : i = ⟨k.val, hk⟩ := Fin.ext (by simp; omega)
        subst this
        exact hS₁
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmv
      subst hmv
      intro A hA _ hS
      rw [setBits_zero_width] at hS
      exact ⟨fun i hi => absurd i.isLt (by omega), hS⟩
  | setJ ν h c =>
    intro mv hmv
    simp only [moves, List.mem_map] at hmv
    obtain ⟨q, -, rfl⟩ := hmv
    intro A hA _ hS
    exact hS

end Lax119563Proofs.Circuits

end Circuits_VerifierSound

/-! ### Formerly `Lax119563Proofs.Circuits.VerifierComplete` -/

section Circuits_VerifierComplete

/-!
# Completeness of the verifier

Every true claim has a move firing into true claims of smaller rank.
-/

namespace Lax119563Proofs.Circuits

open Lax489179.TuringMachine Lax119563.DeterministicTime

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

/-! ## Rank arithmetic -/

lemma rk_lt_time {t t' a b K : ℕ} (h : t < t') (ha : a < K) : t * K + a < t' * K + b := by
  have : (t + 1) * K ≤ t' * K := Nat.mul_le_mul_right _ h
  nlinarith

lemma lvl0_lt {d : ℕ} (hd : d ≤ H) : wP M H + 2 * d * wQ H + H + 2 < wK M H := by
  simp only [wK, wP, wQ]
  nlinarith

lemma lvl1_lt_wP (d : ℕ) : wG M * (H - d) + wG M - 1 < wP M H := by
  simp only [wP, wG]
  have : H - d ≤ H := Nat.sub_le _ _
  have : (M.tapes + 4) * (H - d) ≤ (M.tapes + 4) * H := Nat.mul_le_mul_left _ this
  have : (M.tapes + 4) * (H + 2) = (M.tapes + 4) * H + 2 * (M.tapes + 4) := by ring
  omega

lemma wP_pos : 0 < wP M H := by simp only [wP, wG]; positivity

lemma ptime_lt_succ {d ω θ : ℕ} (hd : d < H) : ptime H d ω θ < ptime H d ω (θ + 1) := by
  rw [ptime_phase hd, ptime_phase hd]
  have := bsz_pos (H := H) d
  nlinarith

/-- The row of the true run of a base call. -/
noncomputable def trueRow (A : ℕ) : Row M :=
  (extT M x H H (A / 4) 0,
   fun i => ⟨((rel M x H H (A / 4) 0 i).toNat - 1) % 2, Nat.mod_lt _ (by norm_num)⟩,
   scanT M x (A / 4))

lemma trueRow_rows {A : ℕ} (hA : A < 2 ^ (H + 2)) :
    ∀ i : Tape M, semCell M x H H 0 i ((trueRow (x := x) (H := H) A).2.2 i, true)
      (setBits A 0 2 (((trueRow (x := x) (H := H) A).2.1 i).val + 1)) := by
  rw [baseRow_iff]
  refine ⟨fun i => ?_, rfl⟩
  have hω : A / 4 < 2 ^ H := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]
    rw [pow_add] at hA; simpa [Nat.mul_comm] using hA
  have := rel_mem (x := x) H le_rfl (A / 4) hω i
  simp only [Nat.sub_self, pow_zero] at this
  simp only [trueRow]
  have h1 : 1 ≤ (rel M x H H (A / 4) 0 i).toNat := by omega
  have h2 : (rel M x H H (A / 4) 0 i).toNat < 3 := by omega
  have : ((rel M x H H (A / 4) 0 i).toNat - 1) % 2 = (rel M x H H (A / 4) 0 i).toNat - 1 := by
    omega
  rw [this]
  omega

lemma blk_lt_eight {d ω θ : ℕ} (hd : d < H) (hω : ω < 2 ^ d) (hθ : θ < 2) (ν : Tape M) :
    blk M x H d ω θ ν < 8 := by
  have := (phase_facts (x := x) hd hθ ν (rel_mem d hd.le ω hω ν)).2.1
  omega

lemma complete_cell (P : Params x s ℓ H) (d : Fin (H + 1)) (θ : Fin 3) (ν : Tape M)
    (c : CellVal M) {A : ℕ} (hA : A < 2 ^ (H + 2)) (hS : Sem M x H (.cell d θ ν c) A) :
    ∃ mv ∈ moves M x s ℓ H (.cell d θ ν c),
      mv.Fires ℓ (Sem M x H) (rank M H) (.cell d θ ν c) A := by
  have hA2 := P.addr_lt hA
  change semCell M x H d θ ν c A at hS
  by_cases h0 : θ.val = 0
  · by_cases hd0 : d.val = 0
    · -- root input tests
      rw [hd0, h0, semCell_root hA2] at hS
      have hrk : rank M H .accept A < rank M H (.cell d θ ν c) A := by
        simp only [rank, h0, if_true]
        have := wP_pos (M := M) (H := H)
        omega
      by_cases hdiv : A / 2 ^ ℓ = 2 ^ H / 2 ^ ℓ
      · refine ⟨.test (hitGuard M x s ℓ H ν c) .accept, ?_, ?_, trivial, hrk⟩
        · simp [moves, h0, hd0]
        · intro i
          by_cases hi : i.val = 0
          · have : i = ⟨0, P.s_pos⟩ := Fin.ext hi
            subst this
            simp only [hitGuard, zero_mul, ↓reduceIte, decide_eq_true_eq, field_zero_eq_mod]
            rw [← root_hit P.hℓH hdiv, hS]
          · simp only [hitGuard, hi, ↓reduceIte, decide_eq_true_eq]
            exact (regs_agree_iff (P.lt_sl hA) P.T_lt).mpr hdiv i hi
      · have hc : c = (0, false) := by rw [← hS, root_miss P.hℓH P.hx hdiv]
        obtain ⟨i₀, hi₀, hne⟩ : ∃ i₀ : Fin s, i₀.val ≠ 0 ∧
            field A (i₀ * ℓ) ℓ ≠ field (2 ^ H) (i₀ * ℓ) ℓ := by
          by_contra hcon
          push Not at hcon
          exact hdiv ((regs_agree_iff (P.lt_sl hA) P.T_lt).mp hcon)
        refine ⟨.test (missGuard s ℓ H i₀) .accept, ?_, ?_, trivial, hrk⟩
        · simp only [moves, h0, hd0, ↓reduceIte, hc, List.mem_cons, List.mem_map,
            List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
          exact Or.inr ⟨i₀, hi₀, rfl⟩
        · intro i
          by_cases hi : i = i₀
          · subst hi; simpa [missGuard] using hne
          · simp [missGuard, hi]
    · -- gather from the parent
      have hdp : d.val - 1 < H := by omega
      have hdd : d.val = d.val - 1 + 1 := by omega
      set θ' : Fin 2 := ⟨field A (bpos H (d.val - 1) + 2) 1, field_lt _ _ _⟩ with hθ'
      have hω := cω_lt hdp.le hA2 (d := d.val - 1)
      set β : Fin 8 := ⟨blk M x H (d.val - 1) (cω H (d.val - 1) A) θ' ν,
        blk_lt_eight hdp hω θ'.isLt ν⟩
      have hc : cω H d A = 2 * cω H (d.val - 1) A + θ'.val := by
        have hc' : cω H (d.val - 1 + 1) A =
            2 * cω H (d.val - 1) A + field A (bpos H (d.val - 1) + 2) 1 := by
          rw [cω_child hdp, field_top_bit]
        conv_lhs => rw [hdd]
        exact hc'
      have hpt : ptime H d (2 * cω H (d.val - 1) A + θ'.val) 0 =
          ptime H (d.val - 1) (cω H (d.val - 1) A) θ' := by
        have := ptime_child_zero' (H := H) (d.val - 1) (cω H (d.val - 1) A) θ' hdp θ'.isLt
        rwa [← hdd] at this
      refine ⟨.fork (bpos H (d.val - 1) + 2) 1 θ' (.headSet (dpred d) θ' ν β)
        (.gather (dpred d) θ' ν c β), ?_, rfl, ?_, ?_, ?_, ?_⟩
      · simp only [moves, h0, hd0, ↓reduceIte, List.mem_flatMap, List.mem_map,
          List.mem_finRange, true_and]
        exact ⟨θ', β, rfl⟩
      · exact ⟨hdp, (headBlock_iff hdp hA2 θ'.isLt β.isLt ν).mpr rfl⟩
      · have hf : field A (bpos H (d.val - 1)) 3 / 4 = θ' := by
          rw [hθ', ← field_top_bit]
        refine ⟨hdp, hf, (gather_iff hdp θ'.isLt ν c rfl hf).mpr ?_⟩
        rw [← hdd, ← h0]; exact hS
      · simp only [rank, h0, ↓reduceIte, dpred_val]
        rw [hc, hpt]
        have key : 2 * (d.val - 1) * wQ H + H + 2 < 2 * d.val * wQ H := by
          obtain ⟨e, he⟩ : ∃ e, e = d.val - 1 := ⟨_, rfl⟩
          rw [← he, show d.val = e + 1 by omega]
          simp only [wQ]; nlinarith
        omega
      · simp only [rank, h0, ↓reduceIte, dpred_val]
        rw [hc, hpt]
        have key : 2 * (d.val - 1) * wQ H + H + 2 < 2 * d.val * wQ H := by
          obtain ⟨e, he⟩ : ∃ e, e = d.val - 1 := ⟨_, rfl⟩
          rw [← he, show d.val = e + 1 by omega]
          simp only [wQ]; nlinarith
        omega
  · by_cases hdH : d.val < H
    · -- restore after a phase
      have hω := cω_lt hdH.le hA2 (d := d.val)
      set β : Fin 8 := ⟨blk M x H d (cω H d A) (ppred θ) ν, blk_lt_eight hdH hω (ppred θ).isLt ν⟩
      have hθθ := ppred_val h0
      refine ⟨.fork' (.headSet d (ppred θ) ν β) (.restore d (ppred θ) ν c β), ?_, field_zero_width _ _,
        ?_, ?_, ?_, ?_⟩
      · simp only [moves, h0, ↓reduceIte, dif_pos hdH, List.mem_map, List.mem_finRange,
          true_and]
        exact ⟨β, rfl⟩
      · exact ⟨hdH, (headBlock_iff hdH hA2 (ppred θ).isLt β.isLt ν).mpr rfl⟩
      · refine ⟨hdH, (restore_iff hdH hA2 (ppred θ).isLt ν c rfl).mpr ?_⟩
        rw [hθθ]; exact hS
      · simp only [rank, h0, ↓reduceIte]
        rw [← hθθ]
        have h := rk_lt_time (b := wG M * (H - d) + wG M - 1)
          (ptime_lt_succ (ω := cω H d A) (θ := (ppred θ).val) hdH) (lvl0_lt (M := M) d.is_le)
        omega
      · simp only [rank, h0, ↓reduceIte]
        rw [← hθθ]
        have : 2 ≤ wG M := by simp [wG]
        omega
    · -- base call
      have hd : d.val = H := by omega
      have hθ2 : θ.val = 2 := by
        have := θ.isLt
        have h1 := hS.1
        by_contra h
        exact hdH (h1 (by omega))
      set ρ : Row M := trueRow (x := x) (H := H) A with hρ
      obtain ⟨hrel, -⟩ := (baseRow_iff A ρ).mp (trueRow_rows hA2)
      have hj : A % 4 < 4 := Nat.mod_lt _ (by norm_num)
      have hfj : field A 0 2 = A % 4 := by rw [field_zero_eq_mod]; norm_num
      rw [hd, hθ2, semCell_base2] at hS
      have h20 : ((2 : ℕ) = 0) ↔ False := by simp
      refine ⟨.step 0 2 (A % 4) (A % 4)
        (.baseCell ν ρ (cellT M x H H (A / 4) 0 ν (A % 4)) 0), ?_, hfj, ?_, ?_⟩
      · simp only [moves, ↓reduceIte, dif_neg hdH, hθ2, h20, if_false, List.mem_flatMap,
          List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
        refine ⟨ρ, mem_allRows _, _, mem_allCV _, ⟨A % 4, hj⟩, ?_, rfl⟩
        have := hrel ν
        simp only [hρ, trueRow] at this ⊢
        rw [← this]
        exact hS
      · rw [setBits_self hfj]
        exact ⟨fun i _ => trueRow_rows hA2 i, (semState_base0 A _).mpr rfl,
          (semCell_base0 A ν _).mpr rfl⟩
      · simp only [rank, h0, ↓reduceIte, hd, hθ2, h20, if_false, Nat.sub_self, mul_zero,
          zero_add, Fin.val_zero]
        rw [setBits_self hfj]
        simp only [wG]
        omega

lemma cellT_of_rel {d ω θ : ℕ} {ν : Tape M} {j : ℕ} (h : rel M x H d ω θ ν = j) :
    cellT M x H d ω θ ν j =
      ((runOn M x (ptime H d ω θ)).tape ν (off M x H d ω ν + j), true) := by
  unfold cellT cfgCell
  unfold rel hd at h
  simp only [Prod.mk.injEq, decide_eq_true_eq, true_and]
  linarith

lemma complete_state (P : Params x s ℓ H) (d : Fin (H + 1)) (θ : Fin 3) (p : ExtState M)
    {A : ℕ} (hA : A < 2 ^ (H + 2)) (hS : Sem M x H (.state d θ p) A) :
    ∃ mv ∈ moves M x s ℓ H (.state d θ p),
      mv.Fires ℓ (Sem M x H) (rank M H) (.state d θ p) A := by
  have hA2 := P.addr_lt hA
  change semState M x H d θ p A at hS
  by_cases h0 : θ.val = 0
  · by_cases hd0 : d.val = 0
    · have h1 : cω H 0 A = 0 := by simp [cω, Nat.div_eq_of_lt hA2]
      have hp : p = (0, none) := by
        have := hS.2; rw [hd0, h0, h1, extT_root] at this; exact this.symm
      refine ⟨.goto .accept, ?_, field_zero_width _ _, trivial, ?_⟩
      · simp [moves, h0, hd0, hp]
      · simp only [rank, h0, ↓reduceIte]
        have := wP_pos (M := M) (H := H)
        omega
    · have hdp : d.val - 1 < H := by omega
      have hdd : d.val = d.val - 1 + 1 := by omega
      set θ' : Fin 2 := ⟨field A (bpos H (d.val - 1) + 2) 1, field_lt _ _ _⟩ with hθ'
      have hc : cω H d A = 2 * cω H (d.val - 1) A + θ'.val := by
        have hc' : cω H (d.val - 1 + 1) A =
            2 * cω H (d.val - 1) A + field A (bpos H (d.val - 1) + 2) 1 := by
          rw [cω_child hdp, field_top_bit]
        conv_lhs => rw [hdd]
        exact hc'
      have hpt : ptime H d (2 * cω H (d.val - 1) A + θ'.val) 0 =
          ptime H (d.val - 1) (cω H (d.val - 1) A) θ' := by
        have := ptime_child_zero' (H := H) (d.val - 1) (cω H (d.val - 1) A) θ' hdp θ'.isLt
        rwa [← hdd] at this
      refine ⟨.step (bpos H (d.val - 1) + 2) 1 θ' θ' (.state (dpred d) θ'.castSucc p), ?_,
        rfl, ?_, ?_⟩
      · simp only [moves, h0, hd0, ↓reduceIte, List.mem_map, List.mem_finRange, true_and]
        exact ⟨θ', rfl⟩
      · rw [setBits_self rfl]
        change semState M x H (d.val - 1) θ' p A
        refine (stateUp_iff hdp θ'.isLt p rfl).mpr ?_
        rw [← hdd, ← h0]; exact hS
      · rw [setBits_self rfl]
        simp only [rank, h0, ↓reduceIte, dpred_val, Fin.val_castSucc]
        rw [hc, hpt]
        have key : 2 * (d.val - 1) * wQ H + H + 2 < 2 * d.val * wQ H := by
          obtain ⟨e, he⟩ : ∃ e, e = d.val - 1 := ⟨_, rfl⟩
          rw [← he, show d.val = e + 1 by omega]
          simp only [wQ]; nlinarith
        have := lvl1_lt_wP (M := M) (H := H) (d.val - 1)
        split_ifs <;> omega
  · by_cases hdH : d.val < H
    · have hθθ := ppred_val h0
      set e : Fin 2 := ⟨field A (bpos H d + 2) 1, field_lt _ _ _⟩
      have hv : (ppred θ).val < 2 ^ 1 := (ppred θ).isLt
      refine ⟨.step (bpos H d + 2) 1 e (ppred θ) (.state (dsucc d hdH) 2 p), ?_, rfl, ?_, ?_⟩
      · simp only [moves, h0, ↓reduceIte, dif_pos hdH, List.mem_map, List.mem_finRange,
          true_and]
        exact ⟨e, rfl⟩
      · change semState M x H (d.val + 1) 2 p _
        refine (stateDown_iff hdH (ppred θ).isLt p).mpr ?_
        rw [hθθ]; exact hS
      · have hc : cω H (d.val + 1) (setBits A (bpos H d + 2) 1 (ppred θ)) =
            2 * cω H d A + (ppred θ).val := by
          rw [cω_child hdH, ← field_top_bit, field_setBits hv,
            cω_setBits hv (by rw [bpos_add_three hdH])]
        have h2v : ((2 : Fin 3) : ℕ) = 2 := rfl
        simp only [rank, h0, ↓reduceIte, dsucc_val, h2v, OfNat.ofNat_ne_zero]
        change ptime H (d.val + 1) (cω H (d.val + 1) (setBits A (bpos H d + 2) 1 (ppred θ))) 2 *
          wK M H + _ < _
        rw [hc, ptime_child_end _ _ _ hdH, hθθ]
        have : wG M * (H - (d.val + 1)) + wG M ≤ wG M * (H - d.val) := by
          rw [show H - d.val = H - (d.val + 1) + 1 by omega]; ring_nf; omega
        have : 2 ≤ wG M := by simp [wG]
        omega
    · have hd : d.val = H := by omega
      have hθ2 : θ.val = 2 := by
        have := θ.isLt
        have h1 := hS.1
        by_contra h
        exact hdH (h1 (by omega))
      set ρ : Row M := trueRow (x := x) (H := H) A with hρ
      have h20 : ((2 : ℕ) = 0) ↔ False := by simp
      rw [hd, hθ2, semState_base2] at hS
      refine ⟨.goto (.baseState ρ 0), ?_, field_zero_width _ _, ?_, ?_⟩
      · simp only [moves, ↓reduceIte, dif_neg hdH, hθ2, h20, List.mem_map, List.mem_filter,
          decide_eq_true_eq]
        exact ⟨ρ, ⟨mem_allRows _, hS⟩, rfl⟩
      · rw [setBits_zero_width]
        exact ⟨fun i _ => trueRow_rows hA2 i, (semState_base0 A _).mpr rfl⟩
      · simp only [rank, ↓reduceIte, hd, hθ2, h20, Nat.sub_self, mul_zero, zero_add,
          Fin.val_zero]
        rw [setBits_zero_width]
        simp only [wG]
        omega

lemma complete_headIn (d : Fin (H + 1)) (θ : Fin 2) (ν : Tape M)
    (u : Fin (H + 1)) {A : ℕ} (hS : Sem M x H (.headIn d θ ν u) A) :
    ∃ mv ∈ moves M x s ℓ H (.headIn d θ ν u),
      mv.Fires ℓ (Sem M x H) (rank M H) (.headIn d θ ν u) A := by
  obtain ⟨hu, y, hy, hrel⟩ := (show semHead M x H d θ ν u A from hS)
  by_cases hu0 : u.val = 0
  · have hy0 : y = 0 := by rw [hu0] at hy; simpa using hy
    subst hy0
    rw [hu0, setBits_zero_width] at hrel
    set γ := (runOn M x (ptime H d (cω H d A) θ)).tape ν (off M x H d (cω H d A) ν + cj H d A)
    refine ⟨.goto (.cell d θ.castSucc ν (γ, true)), ?_, field_zero_width _ _, ?_, ?_⟩
    · have h0d : 0 < H - d.val := by omega
      simp only [moves, hu0, h0d, ↓reduceIte, List.mem_map, List.mem_finRange, true_and]
      exact ⟨γ, rfl⟩
    · rw [setBits_zero_width]
      refine ⟨fun _ => by omega, ?_⟩
      exact cellT_of_rel hrel
    · rw [setBits_zero_width]
      simp only [rank, Fin.val_castSucc]
      have := lvl1_lt_wP (M := M) (H := H) d
      split_ifs <;> omega
  · have hu1 : u.val - 1 + 1 = u.val := by omega
    set e : Fin 2 := ⟨field A (u.val - 1) 1, field_lt _ _ _⟩
    set e' : Fin 2 := ⟨field y (u.val - 1) 1, field_lt _ _ _⟩
    have he' : e'.val < 2 ^ 1 := e'.isLt
    have hω : cω H d (setBits A (u.val - 1) 1 e') = cω H d A := cω_setBits he' (by omega)
    refine ⟨.step (u.val - 1) 1 e e' (.headIn d θ ν (dpred u)), ?_, rfl, ?_, ?_⟩
    · simp only [moves, hu, hu0, ↓reduceIte, List.mem_flatMap, List.mem_map,
        List.mem_finRange, true_and]
      exact ⟨e, e', rfl⟩
    · refine ⟨by simp only [dpred_val]; omega, y % 2 ^ (u.val - 1),
        Nat.mod_lt _ (by positivity), ?_⟩
      simp only [dpred_val]
      rw [hω, setBits_merge he' (Nat.mod_lt _ (by positivity)), hu1]
      have hy' : y < 2 ^ (u.val - 1 + 1) := by rwa [hu1]
      rw [show (e' : ℕ) = field y (u.val - 1) 1 from rfl, split_low hy']
      exact hrel
    · simp only [rank, dpred_val]
      rw [hω]
      omega

lemma moves_complete (P : Params x s ℓ H) (L : Loc M H) {A : ℕ} (hA : A < 2 ^ (H + 2))
    (hS : Sem M x H L A) :
    L = .accept ∨ ∃ mv ∈ moves M x s ℓ H L, mv.Fires ℓ (Sem M x H) (rank M H) L A := by
  have hA2 := P.addr_lt hA
  cases L with
  | accept => exact Or.inl rfl
  | reject => exact hS.elim
  | query =>
    right
    have hS' : (cfgExt (runOn M x (2 ^ H))).2 = some true := hS
    have h1 : cω H 0 A = 0 := by simp [cω, Nat.div_eq_of_lt hA2]
    refine ⟨.goto (.state 0 2 (cfgExt (runOn M x (2 ^ H)))), ?_, field_zero_width _ _, ?_, ?_⟩
    · simp only [moves, List.mem_map, List.mem_filter, decide_eq_true_eq]
      exact ⟨_, ⟨mem_allExt _, hS'⟩, rfl⟩
    · rw [setBits_zero_width]
      refine ⟨by simp, ?_⟩
      change extT M x H 0 (cω H 0 A) 2 = _
      rw [h1, extT_query]
    · rw [setBits_zero_width]
      have h2v : ((2 : Fin 3) : ℕ) = 2 := rfl
      simp only [rank, h2v, OfNat.ofNat_ne_zero, ↓reduceIte, Fin.val_zero]
      change ptime H 0 (cω H 0 A) 2 * wK M H + _ < _
      rw [h1]
      have hp : ptime H 0 0 2 = 2 ^ H := by simp [ptime]
      rw [hp]
      have := lvl1_lt_wP (M := M) (H := H) 0
      have := lvl0_lt (M := M) (H := H) (d := 0) (Nat.zero_le _)
      nlinarith
  | cell d θ ν c => exact Or.inr (complete_cell P d θ ν c hA hS)
  | state d θ p => exact Or.inr (complete_state P d θ p hA hS)
  | headIn d θ ν u => exact Or.inr (complete_headIn d θ ν u hS)
  | headSet d θ ν β =>
    right
    obtain ⟨hdH, hh⟩ := hS
    have hk : bpos H d < H + 1 := by unfold bpos; omega
    refine ⟨.step (bpos H d) 3 (field A (bpos H d) 3) β (.headIn d θ ν ⟨bpos H d, hk⟩), ?_, rfl,
      hh, ?_⟩
    · simp only [moves, hdH, ↓reduceIte, List.mem_map, List.mem_finRange, true_and]
      exact ⟨⟨_, field_lt _ _ _⟩, rfl⟩
    · simp only [rank]
      rw [cω_setBits β.isLt (by rw [bpos_add_three hdH])]
      have : bpos H d ≤ H := by unfold bpos; omega
      omega
  | restore d θ ν c β =>
    right
    obtain ⟨hdH, hr⟩ := hS
    set q : Fin 8 := ⟨field A (bpos H d) 3, field_lt _ _ _⟩
    by_cases hin : sel β ≤ q.val ∧ q.val < sel β + 4
    · rw [if_pos hin] at hr
      have hv : 4 * θ.val + (q.val - sel β) < 2 ^ 3 := by have := θ.isLt; norm_num; omega
      refine ⟨.step (bpos H d) 3 q (4 * θ.val + (q.val - sel β)) (.cell (dsucc d hdH) 2 ν c),
        ?_, rfl, hr, ?_⟩
      · simp only [moves, dif_pos hdH, List.mem_map, List.mem_finRange, true_and]
        exact ⟨q, by simp [hin]⟩
      · have hc : cω H (d.val + 1) (setBits A (bpos H d) 3 (4 * θ.val + (q.val - sel β))) =
            2 * cω H d A + θ.val := by
          rw [cω_child hdH, field_setBits hv, cω_setBits hv (by rw [bpos_add_three hdH])]
          congr 1; omega
        have h2v : ((2 : Fin 3) : ℕ) = 2 := rfl
        simp only [rank, dsucc_val, h2v, OfNat.ofNat_ne_zero, ↓reduceIte]
        change ptime H (d.val + 1) (cω H (d.val + 1) (setBits A (bpos H d) 3
          (4 * θ.val + (q.val - sel β)))) 2 * wK M H + _ < _
        rw [hc, ptime_child_end _ _ _ hdH]
        have : wG M * (H - (d.val + 1)) + wG M ≤ wG M * (H - d.val) := by
          rw [show H - d.val = H - (d.val + 1) + 1 by omega]; ring_nf; omega
        have : 2 ≤ wG M := by simp [wG]
        omega
    · rw [if_neg hin] at hr
      refine ⟨.step (bpos H d) 3 q q (.cell d θ.castSucc ν c), ?_, rfl, ?_, ?_⟩
      · simp only [moves, dif_pos hdH, List.mem_map, List.mem_finRange, true_and]
        exact ⟨q, by simp [hin]⟩
      · rw [setBits_self rfl]; exact hr
      · rw [setBits_self rfl]
        simp only [rank, Fin.val_castSucc]
        have h := rk_lt_time (b := wG M * (H - d) + wG M - 2)
          (ptime_lt_succ (ω := cω H d A) (θ := θ.val) hdH) (lvl0_lt (M := M) d.is_le)
        have := lvl1_lt_wP (M := M) (H := H) d
        split_ifs <;> omega
  | gather d θ ν c β =>
    right
    obtain ⟨hdH, hf, hg⟩ := hS
    set c' : Fin 4 := ⟨field A (bpos H d) 3 % 4, Nat.mod_lt _ (by norm_num)⟩
    have hfq : field A (bpos H d) 3 = 4 * θ.val + c'.val := by
      have := Nat.div_add_mod (field A (bpos H d) 3) 4
      simp only [c']; omega
    have hv : sel β + c'.val < 2 ^ 3 := by
      have := c'.isLt; have : sel β ≤ 4 := min_le_right _ _; norm_num; omega
    refine ⟨.step (bpos H d) 3 (4 * θ.val + c'.val) (sel β + c'.val) (.cell d θ.castSucc ν c),
      ?_, hfq, hg, ?_⟩
    · simp only [moves, hdH, ↓reduceIte, List.mem_map, List.mem_finRange, true_and]
      exact ⟨c', rfl⟩
    · simp only [rank, Fin.val_castSucc]
      rw [cω_setBits hv (by rw [bpos_add_three hdH])]
      have := lvl1_lt_wP (M := M) (H := H) d
      split_ifs <;> omega
  | baseCell ν ρ old k =>
    right
    obtain ⟨hrow, hst, hold⟩ := hS
    by_cases hk : k.val < M.tapes + 1
    · refine ⟨.fork' (.setJ ⟨k.val, hk⟩ ⟨(ρ.2.1 ⟨k.val, hk⟩).val + 1, by omega⟩
          (ρ.2.2 ⟨k.val, hk⟩, true)) (.baseCell ν ρ old ⟨k.val + 1, by omega⟩), ?_,
          field_zero_width _ _, hrow _ le_rfl, ⟨fun i hi => hrow i (by simp at hi; omega),
          hst, hold⟩, ?_, ?_⟩
      · simp [moves, hk, Move.fork']
      · simp only [rank]; omega
      · simp only [rank]; omega
    · refine ⟨.fork' (.state ⟨H, by omega⟩ 0 ρ.1) (.cell ⟨H, by omega⟩ 0 ν old), ?_,
          field_zero_width _ _, hst, hold, ?_, ?_⟩
      · simp [moves, hk, Move.fork']
      · simp only [rank, Fin.val_zero, ↓reduceIte]
        have h := lvl0_lt (M := M) (H := H) (d := H) le_rfl
        have hp : ptime H H (cω H H A) 0 < ptime H H (cω H H A) 2 := by
          rw [ptime_base, ptime_base]; omega
        have := rk_lt_time (b := 0) hp (show wP M H + 2 * H * wQ H < wK M H by omega)
        omega
      · simp only [rank, Fin.val_zero, ↓reduceIte]
        have h := lvl0_lt (M := M) (H := H) (d := H) le_rfl
        have hp : ptime H H (cω H H A) 0 < ptime H H (cω H H A) 2 := by
          rw [ptime_base, ptime_base]; omega
        have := rk_lt_time (b := 0) hp (show wP M H + 2 * H * wQ H < wK M H by omega)
        omega
  | baseState ρ k =>
    right
    obtain ⟨hrow, hst⟩ := hS
    by_cases hk : k.val < M.tapes + 1
    · refine ⟨.fork' (.setJ ⟨k.val, hk⟩ ⟨(ρ.2.1 ⟨k.val, hk⟩).val + 1, by omega⟩
          (ρ.2.2 ⟨k.val, hk⟩, true)) (.baseState ρ ⟨k.val + 1, by omega⟩), ?_,
          field_zero_width _ _, hrow _ le_rfl, ⟨fun i hi => hrow i (by simp at hi; omega),
          hst⟩, ?_, ?_⟩
      · simp [moves, hk, Move.fork']
      · simp only [rank]; omega
      · simp only [rank]; omega
    · refine ⟨.goto (.state ⟨H, by omega⟩ 0 ρ.1), ?_, field_zero_width _ _, ?_, ?_⟩
      · simp [moves, hk, Move.goto]
      · rw [setBits_zero_width]; exact hst
      · rw [setBits_zero_width]
        simp only [rank, Fin.val_zero, ↓reduceIte]
        have h := lvl0_lt (M := M) (H := H) (d := H) le_rfl
        have hp : ptime H H (cω H H A) 0 < ptime H H (cω H H A) 2 := by
          rw [ptime_base, ptime_base]; omega
        have := rk_lt_time (b := 0) hp (show wP M H + 2 * H * wQ H < wK M H by omega)
        omega
  | setJ ν h c =>
    right
    have hh : h.val < 2 ^ 2 := h.isLt
    refine ⟨.step 0 2 (field A 0 2) h (.cell ⟨H, by omega⟩ 0 ν c), ?_, rfl, hS, ?_⟩
    · simp only [moves, List.mem_map, List.mem_finRange, true_and]
      exact ⟨⟨_, field_lt _ _ _⟩, rfl⟩
    · simp only [rank, Fin.val_zero, ↓reduceIte]
      rw [cω_setBits hh (by omega)]
      have h := lvl0_lt (M := M) (H := H) (d := H) le_rfl
      have hp : ptime H H (cω H H A) 0 < ptime H H (cω H H A) 2 := by
        rw [ptime_base, ptime_base]; omega
      have := rk_lt_time (b := 0) hp (show wP M H + 2 * H * wQ H < wK M H by omega)
      omega

end Lax119563Proofs.Circuits

namespace Lax119563Proofs.Circuits

open Lax489179.TuringMachine

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

/-- The verifier accepts exactly the configurations whose assertion is true. -/
theorem verifier_accepts_iff (P : Params x s ℓ H) {locs : List (Loc M H)}
    (hlocs : ∀ L, L ∈ locs) (L : Loc M H) {A : ℕ} (hA : A < 2 ^ (H + 2)) :
    AAccepts ℓ (progCmds ℓ locs (moves M x s ℓ H)) .accept .reject L A ↔ Sem M x H L A := by
  constructor
  · intro h
    exact progCmds_sound P.hℓ P.hH (fun src _ => moves_wf src)
      (fun src _ => moves_sound P src) (fun A => show Sem M x H .accept A from trivial) h hA
  · intro hS
    exact progCmds_complete P.hℓ P.hH (rank M H) hlocs
      (fun src _ => moves_wf src) (fun _ h => h)
      (fun src _ hA hS => moves_complete P src hA hS) L A hA hS

end Lax119563Proofs.Circuits

end Circuits_VerifierComplete

/-! ### Formerly `Lax119563Proofs.Circuits.TimeSimulation` -/

section Circuits_TimeSimulation

/-!
# Facts about the time-simulation program

Facts about the locations and moves of the register program simulating a machine run
(`Circuits/MoveProgram`, `Circuits/Verifier`), used by the packed representation: the codes
of the accepting and rejecting locations differ (`code_accept_ne_reject`), an answer of the
run decides acceptance (`accepts_iff_answer`), and the number of moves at a location is
bounded (`moves_length_le'`, with `movBound0` away from the root cells counted by
`Loc.rootCount`).
-/

namespace Lax119563Proofs.Circuits

open Lax489179.TuringMachine Lax119563.DeterministicTime Programs

variable {M : Machine} {H : ℕ}

instance : DecidableEq (Loc M H) := fun a b =>
  decidable_of_iff (a.code = b.code) Loc.code_injective.eq_iff

lemma code_accept_ne_reject : (Loc.accept : Loc M H).code ≠ Loc.reject.code := fun h => by
  have := Loc.code_injective h
  cases this

/-! ## Correctness -/

lemma accepts_iff_answer {x : List Bool} {T : ℕ} (hT : (runOn M x T).answer.isSome) :
    Accepts M x ↔ (runOn M x T).answer = some true := by
  constructor
  · rintro ⟨t, ht⟩
    rcases le_or_gt t T with h | h
    · have hh : (runOn M x t).answer.isSome := by rw [ht]; rfl
      have := runOn_halted x hh (T - t)
      rw [Nat.add_sub_cancel' h] at this
      rw [this]; exact ht
    · have := runOn_halted x hT (t - T)
      rw [Nat.add_sub_cancel' h.le] at this
      rw [← this]; exact ht
  · intro h; exact ⟨T, h⟩

/-! ## Size bounds -/

lemma length_flatMap_le {α β : Type} {l : List α} {f : α → List β} {k : ℕ}
    (h : ∀ a ∈ l, (f a).length ≤ k) : (l.flatMap f).length ≤ l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := h a (by simp)
    have := ih fun b hb => h b (by simp [hb])
    nlinarith

/-- A bound on the number of moves at a location other than the root cells `cell 0 0 ν c`. -/
def movBound0 (M : Machine) : ℕ := 16 + 8 * (M.symbols + 3) * rowBound M

/-- `1` at the root cells `cell 0 0 ν c` (which carry the `s - 1` tests `missGuard`), else `0`. -/
def Loc.rootCount : Loc M H → ℕ
  | .cell d θ _ _ => if θ.val = 0 ∧ d.val = 0 then 1 else 0
  | _ => 0

lemma Loc.rootCount_le_one (L : Loc M H) : L.rootCount ≤ 1 := by
  cases L <;> simp only [Loc.rootCount] <;> (try split_ifs) <;> omega

lemma length_allRows : (allRows M).length = rowBound M := by
  simp [allRows, allExt, allFun, allOptBool, List.length_product, rowBound]
  ring

lemma moves_length_le' (x : List Bool) (s ℓ : ℕ) (L : Loc M H) :
    (moves M x s ℓ H L).length ≤ movBound0 M + L.rootCount * s := by
  have hR : 3 * (M.states + 1) ≤ rowBound M := by
    unfold rowBound; exact Nat.le_mul_of_pos_right _ (by positivity)
  have hR1 : 1 ≤ rowBound M := le_trans (by omega) hR
  have hS : M.symbols + 3 ≤ 8 * (M.symbols + 3) * rowBound M := by nlinarith
  have hRS : rowBound M ≤ 8 * (M.symbols + 3) * rowBound M := by nlinarith
  have hE : (allExt M).length = 3 * (M.states + 1) := by
    simp [allExt, allOptBool, List.length_product]; ring
  unfold movBound0
  cases L with
  | accept => simp [moves, Loc.rootCount]
  | reject => simp [moves, Loc.rootCount]
  | query =>
    simp only [Loc.rootCount, zero_mul, add_zero]
    simp only [moves, List.length_map]
    have := List.length_filter_le (fun p : ExtState M => decide (p.2 = some true)) (allExt M)
    omega
  | cell d θ ν c =>
    simp only [Loc.rootCount]
    by_cases hr : θ.val = 0 ∧ d.val = 0
    · rw [if_pos hr, one_mul]
      simp only [moves, if_pos hr.1, if_pos hr.2]
      split_ifs
      · simp only [List.length_cons, List.length_map]
        have := List.length_filter_le (fun i : Fin s => decide (i.val ≠ 0)) (List.finRange s)
        simp only [List.length_finRange] at this
        omega
      · simp; omega
    rw [if_neg hr, zero_mul, add_zero]
    simp only [moves]
    split_ifs
    · exact absurd ⟨‹_›, ‹_›⟩ hr
    · exact absurd ⟨‹_›, ‹_›⟩ hr
    · (simp [List.length_flatMap] <;> omega)
    · (simp <;> omega)
    · have : ((allRows M).flatMap fun ρ => (allCV M).flatMap fun old =>
          ((List.finRange 4).filter fun jj =>
            decide (nextCell ρ.1 ρ.2.2 ν ((ρ.2.1 ν).val + 1 : ℤ) (jj.val : ℤ) old = c)).map
            fun jj => (Move.step 0 2 jj.val jj.val (.baseCell ν ρ old 0) : Move (Loc M H) s)).length
          ≤ (allRows M).length * ((allCV M).length * 4) := by
        apply length_flatMap_le
        intro ρ _
        apply length_flatMap_le
        intro old _
        simp only [List.length_map]
        exact le_trans (List.length_filter_le _ _) (by simp)
      have hcv : (allCV M).length = 2 * (M.symbols + 3) := by
        simp [allCV, allBool, List.length_product]; ring
      rw [length_allRows, hcv] at this
      nlinarith
    · (simp <;> omega)
  | state d θ p =>
    simp only [Loc.rootCount, zero_mul, add_zero]
    simp only [moves]
    split_ifs
    · (simp <;> omega)
    · (simp <;> omega)
    · (simp <;> omega)
    · (simp <;> omega)
    · simp only [List.length_map]
      have := List.length_filter_le (fun ρ : Row M => decide (nextExt ρ.1 ρ.2.2 = p)) (allRows M)
      rw [length_allRows] at this
      nlinarith
    · (simp <;> omega)
  | headIn d θ ν u =>
    simp only [Loc.rootCount, zero_mul, add_zero]
    simp only [moves]
    split_ifs
    · simp only [List.length_map, List.length_finRange]; omega
    · (simp [List.length_flatMap] <;> omega)
    · (simp <;> omega)
  | headSet d θ ν β => simp only [Loc.rootCount, zero_mul, add_zero]; simp only [moves]; split_ifs <;> (simp <;> omega)
  | restore d θ ν c β => simp only [Loc.rootCount, zero_mul, add_zero]; simp only [moves]; split_ifs <;> (simp <;> omega)
  | gather d θ ν c β => simp only [Loc.rootCount, zero_mul, add_zero]; simp only [moves]; split_ifs <;> (simp <;> omega)
  | baseCell ν ρ old k => simp only [Loc.rootCount, zero_mul, add_zero]; simp only [moves]; split_ifs <;> (simp <;> omega)
  | baseState ρ k => simp only [Loc.rootCount, zero_mul, add_zero]; simp only [moves]; split_ifs <;> (simp <;> omega)
  | setJ ν h c => simp [moves, Loc.rootCount]; omega

end Lax119563Proofs.Circuits

end Circuits_TimeSimulation
