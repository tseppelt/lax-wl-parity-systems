import Lax429075.Reductions
import Lax119563.WLProblems

/-!
---
title: WL Distinguishing is EXPTIME-complete and XP-complete
type: theorem
---
**Theorem.** $\textsc{WL Distinguishing}$ is $\mathsf{EXPTIME}$-complete under polynomial-time
many-one reductions. Parameterized by the dimension $k$, it is $\mathsf{XP}$-complete under
fpt-reductions.

* **Membership** (Immerman and Lander, cited): the standard WL algorithm runs in time
  $n^{O(k)}$ on graphs with $n$ vertices in total. If $k$ is at least the total number of
  vertices, an isomorphism test by enumeration decides the problem instead. This gives
  membership in $\mathsf{XP}$ and in $\mathsf{EXPTIME}$.
* **Hardness**: every language decided by a deterministic machine in time $2^{p(n)}$ reduces
  in polynomial time to $\textsc{WL Distinguishing}$, through the packed implicit parity
  system of a run of the machine and the matrix compiler, with a dimension that grows with
  the input. Every problem in $\mathsf{XP}$ fpt-reduces to it, with a dimension bounded by a
  computable function of the parameter.

# Implementation notes
* $\mathsf{EXPTIME}$ is the archive's `Lax434930.ExponentialTime.EXPTIME` (single-tape
  machines), and polynomial-time many-one reductions are `Lax429075.Reductions.ManyOne`
  (multi-stack machines in polynomial time).
* $\mathsf{XP}$ and fpt-reductions are those of `Lax119563.ParameterizedComplexity`, with
  deterministic multitape machines.
* The language and the parameterized problem are those of `Lax119563.WLProblems`.
* Both results are stated in the same way: membership, hardness (every member of the class
  reduces to the problem), and completeness as their conjunction. Membership is cited,
  hardness is proved.
-/

open Lax434930.ExponentialTime Lax429075.Reductions
open Lax119563.WLProblems Lax119563.ParameterizedComplexity

namespace Lax119563.WLComplexity

/-- **Membership in EXPTIME** (Immerman and Lander, cited). -/
axiom wl_mem_exptime : WLDistinguishing ∈ EXPTIME

/-- **Membership in XP** (Immerman and Lander, cited). -/
axiom wl_mem_xp : paramWLProblem ∈ XP

/-- **EXPTIME-hardness.** Every language in EXPTIME reduces in polynomial time to WL
Distinguishing. -/
axiom wl_exptime_hard : ∀ L ∈ EXPTIME, ManyOne L WLDistinguishing

/-- **XP-hardness.** Every problem in XP fpt-reduces to WL Distinguishing parameterized by the
dimension. -/
axiom wl_xp_hard : ∀ P ∈ XP, FptReduces P paramWLProblem

/-- **WL Distinguishing is EXPTIME-complete.** -/
axiom wl_exptime_complete :
    WLDistinguishing ∈ EXPTIME ∧ ∀ L ∈ EXPTIME, ManyOne L WLDistinguishing

/-- **WL Distinguishing parameterized by the dimension is XP-complete.** -/
axiom wl_xp_complete :
    paramWLProblem ∈ XP ∧ ∀ P ∈ XP, FptReduces P paramWLProblem

end Lax119563.WLComplexity
