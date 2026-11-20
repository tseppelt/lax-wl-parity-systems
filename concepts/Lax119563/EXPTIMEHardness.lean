import Lax429075.Reductions
import Lax119563.WLProblems

/-!
---
title: WL Distinguishing is EXPTIME-hard
type: theorem
---
**Theorem.** WL Distinguishing is $\mathsf{EXPTIME}$-hard under polynomial-time
many-one reductions: every language decided by a deterministic machine in time $2^{p(n)}$
reduces in polynomial time to WL Distinguishing.

The reduction builds the packed implicit parity system of a run of the machine and applies
the matrix compiler; the dimension grows with the input.

# Implementation notes
* $\mathsf{EXPTIME}$ is the archive's `Lax434930.ExponentialTime.EXPTIME` (single-tape
  machines), and polynomial-time many-one reductions are `Lax429075.Reductions.ManyOne`
  (multi-stack machines in polynomial time).
* The language is `Lax119563.WLProblems.WLDistinguishing`, with the dimension $k$ part of the
  input.
-/

open Lax434930.ExponentialTime Lax429075.Reductions
open Lax119563.WLProblems

namespace Lax119563.EXPTIMEHardness

/-- **EXPTIME-hardness.** Every language in EXPTIME reduces in polynomial time to WL
Distinguishing. -/
axiom wl_exptime_hard : ∀ L ∈ EXPTIME, ManyOne L WLDistinguishing

end Lax119563.EXPTIMEHardness
