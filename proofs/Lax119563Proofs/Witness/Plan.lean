/-!
# Witness lower bound: plan and status

Goal: `Lax119563.WitnessLowerBound.witness_lower_bound`, assuming the concept statements
`RowSpaceCompiler.rowspace_compiler` and `GameCharacterization` (both used as axioms here).

## Design

* `Stabilize`: the joint color partition of the `k`-tuples of `G` and `H` refines and, once
  stable, stays stable; hence a `k`-WL distinction happens within `|V(G)|^k + |V(H)|^k` rounds
  (`exists_distinguishesAfter_le`). Self-contained, no axioms.
* `Derivation`: generic parity-system facts: weight lower bounds on derivation/contradiction
  trees (`lt_of_hasContradictionWithin`), facts of round `r` have derivation trees with
  `< 2^(r+1)` nodes, `conflictRound = Nat.find`.
* `Relay`, `RelaySystem`: the relay counter `relay k ℓ`. Deviation from the paper: the counter
  counts *down* (domain `𝔠'_j` = data bits `0^j 1 *`), so the fixed bits in the first
  `j/(k-1)` rows are zero and the checksum rows vanish on `𝔠'_j` (easy rank bound).
  Locations indexed via `locEquiv : Fin 3 ⊕ (Fin m × Fin 3) ≃ Fin (3 + 3m)`.
* `Counter`: counter values, `cval_decP` (`T_j` decrements), `exists_allowed` (lowest set bit).
* `RelayTree`: the weight argument of Lemma oneway-tree-size ⇒ every contradiction tree has
  `> 2^(2^m - 1)` nodes (`relay_tree_bound`). Only needs `N(T_j a) = N(a) - 1`.
* `RelayConflict`: forward propagation ⇒ conflict in round `1 + 3(2^m - 1)`.
* `RelaySize`: `sizeParameter (relay k ℓ) ≤ sizeConst k · 2^ℓ` via rank factorization
  through the nonzero rows and a geometric sum.
* `Main`: assembly. `n → ∞` (not derivable from the compiler's upper size bound alone) comes
  from `τ ≥ 2^m - 2` (a conflict at round `τ` gives a contradiction tree with `< 2^(τ+2)`
  nodes) together with `exists_distinguishesAfter_le` and the game characterization.
  `G₀.n = G₁.n` from Duplicator surviving `0` rounds.

## Status

See the commit log; all files are intended sorry-free.
-/
