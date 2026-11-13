import Lax119563Proofs.Hierarchy.Padding
import Lax119563Proofs.Hierarchy.Locality

/-!
# Reduction of the hierarchy theorem to a coarse hierarchy

With padding (`pad_step`) and the linear case (`lin`), the translational argument reduces the
time hierarchy theorem to the statement that for every `b` some `DTIME(n^B)` is not contained
in `DTIME(n^b)`.
-/

open Lax119563.DeterministicTime

namespace Lax119563Proofs.Hierarchy

/-- A coarse hierarchy: for every exponent `b` some polynomial class escapes `DTIME(n^b)`. -/
def CoarseHierarchy : Prop := ∀ b : ℕ, ∃ B : ℕ, ∃ L, DT L (B : ℝ) ∧ ¬ DT L (b : ℝ)

theorem time_hierarchy_of_coarse (coarse : CoarseHierarchy) (s : ℕ) (hs : 1 ≤ s) (a : ℝ)
    (ha : a < s) :
    ∃ L : Set (List Bool),
      DecidableInTime L (fun n => (n : ℝ) ^ s) ∧ ¬ DecidableInTime L (fun n => (n : ℝ) ^ a) :=
  hierarchy_of pad_step coarse lin s hs a ha

end Lax119563Proofs.Hierarchy
