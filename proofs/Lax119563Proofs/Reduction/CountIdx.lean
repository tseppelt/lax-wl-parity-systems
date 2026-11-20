import Mathlib.Data.List.Pairwise
import Mathlib.Order.Basic

/-!
# The lexicographic order on keys

`lexLt`: the strict lexicographic order on pairs of numbers (irreflexive and asymmetric), used
for the keys of the command and schema stacks.
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
