import Lax119563.TimeHierarchy
import Lax119563Proofs.Hierarchy.Part1

/-!
# The deterministic time hierarchy theorem
-/

open Lax119563.DeterministicTime

namespace Lax119563Proofs.Hierarchy

/--
---
conclusion: Lax119563.TimeHierarchy.time_hierarchy
---
The proof uses translation (padding) to reduce the claim to a coarse hierarchy:
`DTIME(n^{3b+3})` is not contained in `DTIME(n^b)`. The coarse hierarchy follows from a
diagonal argument. A universal stack program simulates the machine whose code is a prefix of
the input, with polynomial overhead, under a clock of `n^{3b+3}` steps. The case `s = 1` is
handled directly: a machine running in time `o(n)` cannot read the last input bit.
-/
theorem time_hierarchy (s : ℕ) (hs : 1 ≤ s) (a : ℝ) (ha : a < s) :
    ∃ L : Set (List Bool),
      DecidableInTime L (fun n => (n : ℝ) ^ s) ∧ ¬ DecidableInTime L (fun n => (n : ℝ) ^ a) :=
  time_hierarchy_of_coarse coarseHierarchy s hs a ha

end Lax119563Proofs.Hierarchy
