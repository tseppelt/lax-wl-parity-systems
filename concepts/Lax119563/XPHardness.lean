import Lax119563.ParameterizedComplexity
import Lax119563.WLProblems

/-!
---
title: WL Distinguishing is XP-hard
type: theorem
---
**Theorem.** $\textsc{WL Distinguishing}$, parameterized by the dimension $k$, is
$\mathsf{XP}$-hard under fpt-reductions: every problem in $\mathsf{XP}$ fpt-reduces to it,
with a dimension bounded by a computable function of the parameter.

The reduction builds the packed implicit parity system of a run of a decider of the problem
and applies the matrix compiler.

# Implementation notes
* $\mathsf{XP}$ and fpt-reductions are those of `Lax119563.ParameterizedComplexity`, with
  deterministic multitape machines.
* The parameterized problem is `Lax119563.WLProblems.paramWLProblem`.
-/

open Lax119563.WLProblems Lax119563.ParameterizedComplexity

namespace Lax119563.XPHardness

/-- **XP-hardness.** Every problem in XP fpt-reduces to WL Distinguishing parameterized by the
dimension. -/
axiom wl_xp_hard : ∀ P ∈ XP, FptReduces P paramWLProblem

end Lax119563.XPHardness
