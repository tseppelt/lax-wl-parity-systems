/-!
# Plan for the counter (iteration number lower bound)

Goal: `Lax119563.IterationNumber.iteration_number_lower_bound`, assuming the concept axioms
`Lax119563.RowSpaceCompiler.rowspace_compiler` and the game characterization
(`Lax119563.GameCharacterization`).

## Design

* `Bits.lean`: `k = K + 1` blocks; data position `p = i + K t` is bit `t` of block `i < K`
  (row by row). Counter value `val a = ∑_p a_p 2^p`. Shift `δ_j` flips data positions `≤ j`
  (checksum completed). `val_add_shift`: on arrays with data prefix `1^j 0`, adding `δ_j`
  increments the value.
* `System.lean`: the domain `𝔠'_j = dom K ℓ j` of coordinates compatible with the prefix
  `1^j 0` (data blocks: bits at positions `≤ j`; checksum: rows entirely below `j` have bit
  `K`). `supp_subset_dom_iff`: the addresses supported in `𝔠'_j` are exactly those with data
  prefix `1^j 0`.
* `Construction.lean`: locations `0` (main, full domain), `1` (`z₀`, domain `supp 0`),
  `2` (`z₁`, domain `supp t`), `3 + 2j`, `4 + 2j` (private, domain `𝔠'_j`). Schemas indexed
  by `Bool ⊕ (Fin m × Fin 3)`, all binary; well-formedness and pairwise intersection (the
  location pairs are distinct 2-sets).
* `Propagation.lean`: generic unit-propagation facts (monotonicity, propagation along a binary
  equation, potential bound, conflict round of a system with a conflict).
* `Rounds.lean`: `counter K ℓ`, `counter_conflictRound`: `τ` finite and `≥ 2^{ℓK}`.
  Lower bound by the potential `3 val(a) + {1,2,3}`; finiteness by induction on the value
  (decrement at the first one bit).
* `Size.lean`: `sizeParameter_le`: `rowSpaceSize (counter K ℓ) ≤ C_K 2^ℓ` via fixed rows
  (`FixedRows`), the card bound `(K+1) 2^{ℓ-r}` and the rank bound `K + 1 + (ℓ - r)` (columns
  in the span of `K+1` block vectors and `ℓ - r` unit vectors), and
  `∑_j 2^{ℓ - ⌊j/K⌋} ≤ K 2^{ℓ+1}`.
* `Stabilize.lean`: crude stabilization: if `k`-WL distinguishes `G, H` then it does so after
  at most `|G|^k + |H|^k` rounds (count color classes on the disjoint union of tuples).
* `Main.lean`: assembly. `n = |V(G₀)|`; equal sizes from Duplicator surviving `0` rounds;
  `τ ≤ r + k` for each distinguishing round `r`; `n ≤ C C_K 2^ℓ`; `n ≥ n₀` from crude
  stabilization with `ℓ = 2 n₀^k + 2K + 3`.

## Status

All files complete and sorry-free; the concept statement is proven in `Main.lean`.
-/
