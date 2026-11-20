import Mathlib

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
