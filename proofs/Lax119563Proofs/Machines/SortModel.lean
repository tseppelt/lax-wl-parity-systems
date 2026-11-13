import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Log
import Lax119563Proofs.Machines.Numbers

/-!
# Bottom-up merge sort: the list model

Records are bit strings ordered lexicographically with `false < true` and a proper prefix
smaller (`recLE`, a total order). The tape algorithm of `Sort` performs bottom-up merge sort
on runs: `mergePass` merges the runs pairwise (`deal` splits them into the runs at even and
odd positions), and `sortRuns` repeats this until at most one run is left. This file proves
that the result is `List.mergeSort` with respect to `recLE`, and bounds the number of passes.
-/

namespace Lax119563Proofs.Machines

/-! ## The order on records -/

/-- Lexicographic order on bit strings (`false < true`, prefixes first). -/
def recLE : List Bool → List Bool → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: r, b :: s => if a = b then recLE r s else !a

@[simp] lemma recLE_nil_left (s : List Bool) : recLE [] s = true := rfl
@[simp] lemma recLE_cons_nil (a : Bool) (r : List Bool) : recLE (a :: r) [] = false := rfl
lemma recLE_cons_cons (a b : Bool) (r s : List Bool) :
    recLE (a :: r) (b :: s) = if a = b then recLE r s else !a := rfl

lemma recLE_append_left (c r s : List Bool) : recLE (c ++ r) (c ++ s) = recLE r s := by
  induction c with
  | nil => rfl
  | cons a c ih => simp [recLE_cons_cons, ih]

lemma recLE_refl (r : List Bool) : recLE r r = true := by
  induction r with
  | nil => rfl
  | cons a r ih => simp [recLE_cons_cons, ih]

lemma recLE_total (r s : List Bool) : (recLE r s || recLE s r) = true := by
  induction r generalizing s with
  | nil => simp
  | cons a r ih =>
    cases s with
    | nil => simp
    | cons b s =>
      simp only [recLE_cons_cons]
      by_cases hab : a = b
      · subst hab; simpa using ih s
      · rw [if_neg hab, if_neg (Ne.symm hab)]
        cases a <;> cases b <;> simp_all

lemma recLE_trans (r s u : List Bool) (h₁ : recLE r s = true) (h₂ : recLE s u = true) :
    recLE r u = true := by
  induction r generalizing s u with
  | nil => rfl
  | cons a r ih =>
    cases s with
    | nil => simp at h₁
    | cons b s =>
      cases u with
      | nil => simp at h₂
      | cons c u =>
        cases a <;> cases b <;> cases c <;> simp [recLE_cons_cons] at h₁ h₂ ⊢ <;>
          exact ih _ _ h₁ h₂

lemma recLE_antisymm (r s : List Bool) (h₁ : recLE r s = true) (h₂ : recLE s r = true) :
    r = s := by
  induction r generalizing s with
  | nil => cases s with
    | nil => rfl
    | cons b s => simp at h₂
  | cons a r ih =>
    cases s with
    | nil => simp at h₁
    | cons b s =>
      simp only [recLE_cons_cons] at h₁ h₂
      by_cases hab : a = b
      · subst hab; simp_all
        exact ih s h₁ h₂
      · rw [if_neg hab] at h₁; rw [if_neg (Ne.symm hab)] at h₂
        cases a <;> cases b <;> simp_all

/-! ## Passes -/

/-- Split a list into the elements at even and at odd positions. -/
def deal {α : Type} : List α → List α × List α
  | [] => ([], [])
  | [a] => ([a], [])
  | a :: b :: l => (a :: (deal l).1, b :: (deal l).2)

/-- Merge corresponding runs of two lists of runs (a missing run counts as empty). -/
def zipMerge : List (List (List Bool)) → List (List (List Bool)) → List (List (List Bool))
  | [], _ => []
  | rb :: B, [] => List.merge rb [] recLE :: zipMerge B []
  | rb :: B, rc :: C => List.merge rb rc recLE :: zipMerge B C

/-- One pass: merge the runs pairwise. -/
def mergePass (R : List (List (List Bool))) : List (List (List Bool)) :=
  zipMerge (deal R).1 (deal R).2

lemma deal_length {α : Type} (l : List α) :
    (deal l).1.length = (l.length + 1) / 2 ∧ (deal l).2.length = l.length / 2 := by
  induction l using deal.induct with
  | case1 => simp [deal]
  | case2 a => simp [deal]
  | case3 a b l ih => simp [deal, ih.1, ih.2]; omega

lemma zipMerge_length (B C : List (List (List Bool))) (h : C.length ≤ B.length) :
    (zipMerge B C).length = B.length := by
  induction B generalizing C with
  | nil => simp [zipMerge]
  | cons rb B ih =>
    cases C with
    | nil => simp [zipMerge, ih [] (by simp)]
    | cons rc C => simp at h; simp [zipMerge, ih C (by omega)]

lemma mergePass_length (R : List (List (List Bool))) :
    (mergePass R).length = (R.length + 1) / 2 := by
  rw [mergePass, zipMerge_length _ _ (by rw [(deal_length R).1, (deal_length R).2]; omega),
    (deal_length R).1]

lemma deal_perm {α : Type} (l : List α) : ((deal l).1 ++ (deal l).2).Perm l := by
  induction l using deal.induct with
  | case1 => simp [deal]
  | case2 a => simp [deal]
  | case3 a b l ih =>
    simp only [deal, List.cons_append]
    refine List.Perm.cons a ?_
    refine (List.perm_middle).trans (List.Perm.cons b ih)

lemma zipMerge_flatten_perm (B C : List (List (List Bool))) (h : C.length ≤ B.length) :
    (zipMerge B C).flatten.Perm (B.flatten ++ C.flatten) := by
  induction B generalizing C with
  | nil => cases C <;> simp_all [zipMerge]
  | cons rb B ih =>
    cases C with
    | nil =>
      have h1 := List.merge_perm_append (xs := rb) (ys := []) (le := recLE)
      have h2 := ih [] (by simp)
      simp only [zipMerge, List.flatten_cons, List.flatten_nil, List.append_nil] at h1 h2 ⊢
      exact List.Perm.append h1 h2
    | cons rc C =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at h
      have h1 := List.merge_perm_append (xs := rb) (ys := rc) (le := recLE)
      have h2 := ih C h
      simp only [zipMerge, List.flatten_cons]
      rw [List.perm_iff_count] at h1 h2 ⊢
      intro a
      have := h1 a; have := h2 a
      simp only [List.count_append] at *
      omega

lemma mergePass_flatten_perm (R : List (List (List Bool))) :
    (mergePass R).flatten.Perm R.flatten := by
  refine (zipMerge_flatten_perm _ _ ?_).trans ?_
  · rw [(deal_length R).1, (deal_length R).2]; omega
  · rw [← List.flatten_append]; exact (deal_perm R).flatten

/-- Every run is sorted. -/
def RunsSorted (R : List (List (List Bool))) : Prop :=
  ∀ r ∈ R, r.Pairwise fun a b => recLE a b = true

lemma pairwise_merge_recLE {r s : List (List Bool)} (hr : r.Pairwise fun a b => recLE a b = true)
    (hs : s.Pairwise fun a b => recLE a b = true) :
    (List.merge r s recLE).Pairwise fun a b => recLE a b = true :=
  List.pairwise_merge (le := recLE) (fun a b c h₁ h₂ => recLE_trans a b c h₁ h₂)
    (fun a b => recLE_total a b) r s hr hs

lemma zipMerge_sorted (B C : List (List (List Bool))) (hB : RunsSorted B) (hC : RunsSorted C) :
    RunsSorted (zipMerge B C) := by
  induction B generalizing C with
  | nil => simp [zipMerge, RunsSorted]
  | cons rb B ih =>
    cases C with
    | nil =>
      intro r hr
      simp only [zipMerge, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact pairwise_merge_recLE (hB rb (by simp)) (by simp)
      · exact ih [] (fun r hr => hB r (by simp [hr])) (by simp [RunsSorted]) r hr
    | cons rc C =>
      intro r hr
      simp only [zipMerge, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact pairwise_merge_recLE (hB rb (by simp)) (hC rc (by simp))
      · exact ih C (fun r hr => hB r (by simp [hr])) (fun r hr => hC r (by simp [hr])) r hr

lemma mergePass_sorted (R : List (List (List Bool))) (hR : RunsSorted R) :
    RunsSorted (mergePass R) := by
  have hmem : ∀ r, r ∈ (deal R).1 ++ (deal R).2 → r ∈ R := fun r hr => (deal_perm R).mem_iff.mp hr
  exact zipMerge_sorted _ _ (fun r hr => hR r (hmem r (by simp [hr])))
    (fun r hr => hR r (hmem r (by simp [hr])))

/-- Repeat merge passes until at most one run is left. -/
def sortRuns (R : List (List (List Bool))) : List (List (List Bool)) :=
  if h : R.length ≤ 1 then R else sortRuns (mergePass R)
termination_by R.length
decreasing_by rw [mergePass_length]; omega

lemma sortRuns_spec (R : List (List (List Bool))) (hR : RunsSorted R) :
    (sortRuns R).length ≤ 1 ∧ RunsSorted (sortRuns R) ∧ (sortRuns R).flatten.Perm R.flatten := by
  induction R using sortRuns.induct with
  | case1 R h =>
    rw [sortRuns, dif_pos h]
    exact ⟨h, hR, List.Perm.refl _⟩
  | case2 R h ih =>
    rw [sortRuns, dif_neg h]
    obtain ⟨h₁, h₂, h₃⟩ := ih (mergePass_sorted R hR)
    exact ⟨h₁, h₂, h₃.trans (mergePass_flatten_perm R)⟩

/-- The model of the tape sort: singleton runs, then merge passes. -/
def sortRecs (rs : List (List Bool)) : List (List Bool) :=
  (sortRuns (rs.map fun r => [r])).flatten

theorem sortRecs_eq (rs : List (List Bool)) : sortRecs rs = rs.mergeSort recLE := by
  have hR : RunsSorted (rs.map fun r => [r]) := by
    intro r hr; simp only [List.mem_map] at hr; obtain ⟨a, -, rfl⟩ := hr; simp
  obtain ⟨h₁, h₂, h₃⟩ := sortRuns_spec _ hR
  have hflat : ∀ l : List (List Bool), (l.map fun r => [r]).flatten = l := by
    intro l; induction l <;> simp_all
  rw [hflat] at h₃
  refine List.Perm.eq_of_pairwise (le := fun a b => recLE a b = true)
    (fun a b _ _ h h' => recLE_antisymm a b h h') ?_ ?_ (h₃.trans (List.mergeSort_perm rs recLE).symm)
  · unfold sortRecs
    generalize sortRuns (rs.map fun r => [r]) = S at h₁ h₂
    match S, h₁ with
    | [], _ => simp
    | [r], _ => simpa using h₂ r (by simp)
  · exact List.pairwise_mergeSort (le := recLE) (fun a b c h₁ h₂ => recLE_trans a b c h₁ h₂)
      (fun a b => recLE_total a b) rs

/-- The number of merge passes. -/
def numPasses (R : List (List (List Bool))) : ℕ :=
  if h : R.length ≤ 1 then 0 else numPasses (mergePass R) + 1
termination_by R.length
decreasing_by rw [mergePass_length]; omega

lemma numPasses_le (R : List (List (List Bool))) : numPasses R ≤ Nat.clog 2 R.length := by
  induction R using numPasses.induct with
  | case1 R h => rw [numPasses, dif_pos h]; exact Nat.zero_le _
  | case2 R h ih =>
    rw [numPasses, dif_neg h, Nat.clog_of_two_le (by norm_num) (by omega)]
    rw [mergePass_length] at ih
    exact Nat.add_le_add_right ih 1

end Lax119563Proofs.Machines
