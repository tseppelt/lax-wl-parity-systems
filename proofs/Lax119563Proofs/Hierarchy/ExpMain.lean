import Lax119563.ExponentialTimeHierarchy
import Lax119563Proofs.Hierarchy.ExpDiag

/-!
# The deterministic time hierarchy theorem for exponential time
-/

open Lax119563.DeterministicTime

namespace Lax119563Proofs.Hierarchy

/--
---
conclusion: Lax119563.ExponentialTimeHierarchy.exp_time_hierarchy
---
A diagonal argument. The diagonal machine computes a clock of `2^n` units on inputs of length
`n` by doubling a unary counter `n` times (in time `O(2^n)`), and runs the universal stack
program under this clock; the universal program answers the negation of the machine whose code
is a prefix of the input. So the diagonal language is in `DTIME(2^n)`. The universal program
has cubic overhead: simulating `T` steps on inputs of length `n` costs `O(n^2 T^3)` (with a
constant depending on the simulated machine). A machine running within `C 2^{n/4} + C` steps is
thus simulated within `O(n^2 2^{3n/4}) ≤ 2^n` steps on long inputs `code M ++ 0^k`, where the
diagonal machine answers differently.
-/
theorem exp_time_hierarchy :
    ∃ L : Set (List Bool),
      DecidableInTime L (fun n => (2 : ℝ) ^ (n : ℝ)) ∧
        ¬ DecidableInTime L (fun n => (2 : ℝ) ^ ((n : ℝ) / 4)) :=
  ⟨diagExpLang, diagExp_dt, diagExp_not_dt⟩

end Lax119563Proofs.Hierarchy
