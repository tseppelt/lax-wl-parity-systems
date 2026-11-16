import Mathlib.Data.List.Pairwise
import Mathlib.Order.Basic

/-!
# Indices as counts

In a list whose keys strictly increase, the index of an entry is the number of entries with
a smaller key (`length_filter_lt_getElem`). This turns the position of a command (or schema)
in the enumeration order into a count, which a generator computes with `Gn.count`.
-/

namespace Lax119563Proofs.Reduction

variable {α : Type*}

/-- Lexicographic order on pairs of naturals, as a Boolean. -/
def lexLt (p q : ℕ × ℕ) : Bool := decide (p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2))

lemma lexLt_trans {p q r : ℕ × ℕ} (h₁ : lexLt p q = true) (h₂ : lexLt q r = true) :
    lexLt p r = true := by
  simp only [lexLt, decide_eq_true_eq] at *
  omega

lemma lexLt_irrefl (p : ℕ × ℕ) : lexLt p p = false := by
  simp [lexLt]

lemma lexLt_asymm {p q : ℕ × ℕ} (h : lexLt p q = true) : lexLt q p = false := by
  simp only [lexLt, decide_eq_true_eq, decide_eq_false_iff_not] at *
  omega

/-- **Index = count.** If the keys strictly increase, the number of entries with a key below
the key of entry `i` is `i`. -/
lemma length_filter_lt_getElem (key : α → ℕ × ℕ) :
    ∀ (l : List α), l.Pairwise (fun a b => lexLt (key a) (key b) = true) →
      ∀ (i : ℕ) (hi : i < l.length),
        (l.filter fun a => lexLt (key a) (key l[i])).length = i
  | [], _, i, hi => by simp at hi
  | a :: l, h, i, hi => by
    rw [List.pairwise_cons] at h
    rcases i with _ | i
    · simp only [List.getElem_cons_zero, List.filter_cons, lexLt_irrefl, Bool.false_eq_true,
        if_false]
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro b hb hlt
      have := h.1 b hb
      rw [lexLt_asymm this] at hlt
      exact absurd hlt (by simp)
    · have hi' : i < l.length := by simpa using hi
      simp only [List.getElem_cons_succ, List.filter_cons]
      rw [if_pos (h.1 _ (List.getElem_mem hi')), List.length_cons,
        length_filter_lt_getElem key l h.2 i hi']

end Lax119563Proofs.Reduction
