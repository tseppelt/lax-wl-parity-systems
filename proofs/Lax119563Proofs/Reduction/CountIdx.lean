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

lemma lexLt_irrefl (p : ℕ × ℕ) : lexLt p p = false := by
  simp [lexLt]

lemma lexLt_asymm {p q : ℕ × ℕ} (h : lexLt p q = true) : lexLt q p = false := by
  simp only [lexLt, decide_eq_true_eq, decide_eq_false_iff_not] at *
  omega

end Lax119563Proofs.Reduction
