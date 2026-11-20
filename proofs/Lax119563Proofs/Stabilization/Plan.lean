/-!
# Stabilization bound: plan and status

Goal: discharge `Lax119563.Stabilization.stabilization_bound` (Döring–Neuen, arXiv:2609.17364):
for `k ≥ 2` there is `C` with: `k`-WL stabilizes on every colored graph with `n` vertices after
some `r ≤ C n^(k-1)` rounds. No concept change: a proof in this package with
`conclusion: Lax119563.Stabilization.stabilization_bound`; the axiom set must stay background-only.

Paper references below: §4–6 of the arXiv version (local copy in `iteration-number/`, not in git).

## Deviations from the paper (all only change constants)

* **No Paz theorem.** Claim 5.16 uses `CX^{≤⌊n²/2⌋} = ⟨X⟩`. We use the trivial bound
  `X^{n²} = ⟨X⟩` (powers of a subspace containing `1` grow until they stabilize, dimension
  `≤ n²`). Costs `+1` in Claim 5.16.
* **No Wedderburn–Artin / unitary block form (Thm 2.1).** We work in `End(E)`, `E` a finite
  dimensional complex inner product space, star = adjoint. For the `*`-subalgebra `A = ⟨V_s⟩`:
  `E` is a semisimple `A`-module (orthogonal complements of invariant subspaces are invariant);
  decompose `E` into simple `A`-submodules `W_1, …, W_m` (`IsSemisimpleModule.
  exists_sSupIndep_sSup_simples_eq_top`); restriction `A → Π_j End(W_j)` is an injective unital
  `⋆`-algebra hom. All copies are kept (`Σ_j dim W_j = n`, no multiplicities `α_i`); the
  recursion only needs `Σ ≤ n`.
* **Corner property via Jacobson density** (`Module.Finite.toModuleEnd_moduleEnd_surjective`,
  i.e. the bicommutant theorem): if `W` is a simple `A`-submodule with `2 dim W > n`, every
  `T` with `range T ≤ W`, `Wᗮ ≤ ker T` lies in `A`. Proof: every `A`-linear `b` preserves `W`
  (else `(1-P) b|_W : W ↪ Wᗮ` by Schur, impossible by dimension), `b*` is `A`-linear too so `b`
  preserves `Wᗮ`, and `b|_W` is a scalar (eigenvalue + Schur); hence `T` commutes with
  `End_A(E)`. Special case `W = ⊤`: an irreducible `A` is all of `End(E)` (Burnside), so
  `A ≠ ⊤ ⇒ dim W_j < n` for all `j`. This replaces `α_1 = 1, B_{β_1} ⊆ A` in Claim 5.17.
* **Weak chains instead of sets `M_i`.** An `A`-sequence is a sequence of subspaces
  `V_0 = ℂ1, V_i* = V_i, V_i V_i ≤ V_{i+1}` (no strictness); we count strict steps. This
  absorbs the de-duplication in §6 and the subsequence extraction in Claims 5.8/5.9.
* **Constants.** `h(n) := 10 n - 2⌈log₂ n⌉ - 9` replaces `C(n) ≤ 5n - 4`; the all-small case of
  the recursion uses a 2-way split (sums `≥ n/4` each) instead of the 3-way Claim 5.14.
  Resulting bounds: `≤ 10 n` strict steps in dimension 2; `r ≤ 13 n^(k-1)` overall.
* **§6 simplified.** Take `S = V^(k-2)` (all prefixes) instead of sorted prefixes, so Claim 6.7
  and Lemma A.1 are not needed (`n^(k-2) · 10 n` is already `O(n^(k-1))`).

## Modules (folder `Stabilization/`) and key statements

Ambient for the abstract part: `{A} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]`.

1. `Chains` (defs + generic facts, written first, shared by all tracks)
   ```
   structure IsChain (V : ℕ → Submodule ℂ A) (ℓ : ℕ) : Prop where
     zero : V 0 = ℂ ∙ (1 : A)
     star_mem : ∀ i ≤ ℓ, ∀ x ∈ V i, star x ∈ V i
     mul_le : ∀ i < ℓ, V i * V i ≤ V (i + 1)
   def strictSteps (V) (ℓ) : ℕ := ((Finset.range ℓ).filter fun i => V i ≠ V (i + 1)).card
   def ChainBound (A) (N : ℕ) : Prop := ∀ V ℓ, IsChain V ℓ → strictSteps V ℓ + 1 ≤ N
   ```
   Facts: `1 ∈ V i`, monotone; strict steps of a monotone submodule sequence `≤` finrank growth;
   `alg V := ⨆ k, V ^ k`; `V^k` monotone, stabilizes, `V ^ finrank A = alg V`;
   Obs 5.2 `V_s ^ (2^j) ≤ V_{s+j}`; star-closure of powers; `ChainBound` pulls back along
   injective unital `⋆`-alg homs; existence of a chain with maximal `strictSteps`;
   Obs 5.3 (maximal ⇒ `V ℓ = ⊤`, by appending `⊤`);
   Lemma 5.5 (maximal, `s < ℓ`, `alg V_s < alg V_{s+1}` ⇒ `V_s = alg V_s`) by the surgery
   `V_0..V_s, V_s^2, V_s^4, …, V_s^(2^r) = alg V_s, V_{s+r}, …, V_ℓ` (or truncated at
   `V_s^(2^r)` when `s + r > ℓ`), which has one more strict step.
2. `Products`: Lemma 5.7 `ChainBound A a → ChainBound B b → ChainBound (A × B) (a + b)`
   (projection `P_i`, kernel part `N_i`, `T_i = ℂ1 + π_B N_i`, rank–nullity on `V_i`; at most one
   index with `N` strict but `T` not strict, namely where `(0,1)` enters). Lemma 5.11:
   `ChainBound (Π i : Fin (m+1), B i) (Σ N i)` via `Π_{Fin (m+1)} ≃⋆ₐ B 0 × Π_{Fin m}`.
3. `Structure` (`E` fin-dim complex inner product space, `S : StarSubalgebra ℂ (E →ₗ[ℂ] E)`):
   * `IsSemisimpleModule S E`;
   * `mem_of_corner`: `W` simple `S`-submodule, `finrank E < 2 * finrank W`, `range T ≤ W`,
     `Wᗮ ≤ ker T` ⇒ `T ∈ S`; corollary `S ≠ ⊤ ⇒` no simple submodule equals `⊤`;
   * `exists_decomposition`: `∃ m (W : Fin m → Submodule ℂ E)`, each `W j` `S`-invariant,
     `S`-simple, `≠ ⊥`; `Σ j, finrank (W j) = finrank E`; an injective
     `ρ : S →⋆ₐ[ℂ] Π j, (W j →ₗ[ℂ] W j)` (restriction; star needs `S` star-closed).
4. `Corner`: Lemma 5.12, basis-free:
   `1 ∈ X`, `X` star-closed, `alg X = ⊤`, `0 < finrank W`, every corner `T` (as above) in `X`
   ⇒ `X ^ (2 * (n - finrank W)) = ⊤`. Via `H_t = span {a u | a ∈ X^t, u ∈ W}` (dims grow by
   ≥ 1 until `⊤`), rank-one maps `rankOne (a u) (b w) = a ∘ rankOne u w ∘ b*`, and
   `T = T P + P T (1-P) + (1-P) T (1-P)` with `P` the projection onto `H_{n-β-1}`.
5. `Recursion`: with `c = Nat.clog 2`, stated additively (no truncated subtraction):
   for `2 ≤ n`, a multiset `D` of dims in `[1, n)` with sum `n`:
   * some `2d > n`: `Σ_D (2c(d)+9) ≥ 2c(n) + 9 + 2 + c(n-d)`;
   * all `2d ≤ n`: `Σ_D (2c(d)+9) ≥ 2c(n) + 9 + 1 + c(n²)`.
6. `TwoDim`: Thm 5.15 by strong induction on `n = finrank E ≥ 1`:
   `ChainBound (E →ₗ[ℂ] E) N` with `N + 2 c(n) + 9 ≤ 10 n`. Take a maximal chain, `s` the last
   index with `alg V_s ≠ ⊤` (`s < ℓ` by Obs 5.3); chain `V_0..V_s` lives in `S = alg V_s`, so by
   3 + 2 + IH its strict steps are `< Σ_j h(d_j)`; after `s`: `V_{s+1+c(n²)} = ⊤` (Claim 5.16)
   and, if some `2 d_j > n`, `V_{s+2+c(n-d_j)} = ⊤` (Claim 5.17 from Lemma 5.5 + 3 + 4).
   Corollary `matrix_chainBound (n) : ChainBound (Matrix (Fin n) (Fin n) ℂ) (10 * n + 1)` via
   `LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun _ ℂ)`.
7. `Colorings` (WL side, independent of 2–6):
   * `color (r+1)` refines `color r`; compatible with equality (via `color 0 = atp`);
     shufflable for every `σ : Fin k → Fin k` (induction on `r`; for non-injective `σ` use a
     coordinate outside `range σ` for the substituted vertex);
   * `classSpace χ : Submodule ℂ (Matrix α α ℂ) := {M | ∀ a b c d, χ a b = χ c d → M a b = M c d}`;
     `1 ∈` (compat. eq.), star-closed (swap-shufflable), refinement ⇔ `≤`, equal spaces ⇒
     equal partitions (Lemmas 4.5–4.7);
   * Lemma 6.2 for the projections `χ^v_i (a, b) = color i (v, a, b)` (`k = m + 2`, tuples
     `Fin.snoc (Fin.snoc v a) b`): `classSpace χ^v_i * classSpace χ^v_i ≤ classSpace χ^v_{i+1}`
     (entry `(u,u')` of a product is a sum over the multiset in `color (i+1) (v,u,u')`);
   * Lemma 6.4 (extendable).
8. `HigherDim`: if `∀ i < r, ¬ StabilizesAfter k i G` then `r ≤ 10 n` (`k = 2`) resp.
   `r ≤ 2 + 3 (n^(k-2) - 1) + n^(k-2) · 10 n` (`k ≥ 3`): Claims 6.5, 6.6 and the count
   `r - 2 ≤ 3 |Ī| + Σ_v |I^v|`, with `|Ī| ≤ n^(k-2) - 1` (classes of `χ̄`) and `|I^v| ≤ 10 n`
   (chain `ℂ1, classSpace χ^v_0, classSpace χ^v_1, …` + `matrix_chainBound`).
9. `Main`: `stabilization_bound` with `C = 13`: take `r = C n^(k-1)`; if no `i ≤ r` is stable,
   `HigherDim` gives `r + 1 ≤ r`. (`n = 0`: no tuples, stable at `0`.)

## Work split

* Me: `Chains` definitions + statement stubs of 2–8 (with `sorry`), so tracks compile.
* Track A (algebra): 1, 2, 4, 5, 6. Track S (structure): 3. Track W (WL): 7, 8, 9.
  One worktree branch each (`proofs/stab-*`); merge into main when `lax build` is green.

## Status

Planned (2026-11-20); nothing implemented yet.

Track W (branch `proofs/stab-wl`): done. `Defs.lean` holds the shared definitions;
`Colorings` (items 7), `HigherDim` (8) and `Main` (9) are sorry-free; `Main.stabilization_bound`
(`C = 13`) depends on `sorryAx` only through `matrix_chainBound`. Deviations: the WL sequence
is used as an infinite sequence, so Claim 6.6 holds for every non-stable round and the count is
`r ≤ 3 |Ī over r + 2 rounds| + Σ_v |I^v| ≤ 3 n^(k-2) + 10 n^(k-1)` (no `r - 2`); shufflability
for non-injective `σ` via a coordinate outside `range σ`; Lemma 6.2 for arbitrary members of
`classSpace` (multiset transport from `UpperBound/Rounds`), not only class indicators.

Before submission: proof network check (`stabilization_bound` becomes proven; the witness
upper bound then rests on it), update the abstract ("stated as cited results" no longer applies
to the stabilization bound), remove this file.
-/
