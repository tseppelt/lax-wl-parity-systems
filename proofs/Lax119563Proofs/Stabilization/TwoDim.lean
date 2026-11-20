import Lax119563Proofs.Stabilization.Interface
import Lax119563Proofs.Stabilization.Products
import Lax119563Proofs.Stabilization.Corner
import Lax119563Proofs.Stabilization.Recursion

/-!
# The two-dimensional bound (Döring–Neuen, Theorem 5.15)

By strong induction on `n = finrank E ≥ 1`: `ChainBound (End E) N` with `N + recW n ≤ 10 n`,
`recW n = 2 ⌈log₂ n⌉ + 9`. For a chain `V` of length `ℓ` let `s` be the last index with
`alg (V s) ≠ ⊤` and `S = alg (V s)`; decompose `E` into `S`-simple blocks of dimensions
`d j < n`. Let `r` be minimal with `V s ^ 2 ^ r = S`. The chain `V 0, …, V s, V s ^ 2, …,
V s ^ 2 ^ r` lies in `S` and has `strictSteps V s + r` strict steps, so by Lemma 5.11 and the
induction hypothesis `strictSteps V s + r + 1 ≤ Σ N j`. After `s`:
* (all `2 d j ≤ n`) `V (s + 1 + c(n²)) = ⊤` (Claim 5.16, via `V ^ n² = alg V`);
* (some `2 d j > n`) the corner maps of `W j` lie in `S = V s ^ 2 ^ r ≤ V (s + r + 1) =: X`,
  so `X ^ (2 (n - d j)) = ⊤` (Lemma 5.12) and `V (s + r + 2 + c(n - d j)) = ⊤` (Claim 5.17).

The `r` squaring steps replace the surgery of Lemma 5.5 (no maximal chains are needed).
-/

open Module

set_option linter.unusedSectionVars false

namespace Lax119563Proofs.Stabilization

/-- If `ℂ 1` is everything, chains have no strict steps. -/
theorem chainBound_one_of_span_eq_top {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A]
    [StarModule ℂ A] (h : (ℂ ∙ (1 : A)) = ⊤) : ChainBound A 1 := by
  intro V ℓ hV
  suffices strictSteps V ℓ = 0 by omega
  rw [strictSteps_eq_sum]
  refine Finset.sum_eq_zero fun i hi => stepInd_eq_zero ?_
  have hi := Finset.mem_range.mp hi
  have a : V 0 ≤ V i := hV.mono (Nat.zero_le _) hi.le
  have b : V 0 ≤ V (i + 1) := hV.mono (Nat.zero_le _) hi
  rw [hV.zero, h, top_le_iff] at a b
  rw [a, b]

section Step

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem one_ne_zero_end (h : 1 ≤ finrank ℂ E) : (1 : E →ₗ[ℂ] E) ≠ 0 := by
  obtain ⟨x, hx⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℂ) (M := E)).mp (by omega)
  intro h1
  exact hx (by simpa using LinearMap.congr_fun h1 x)

theorem finrank_end : finrank ℂ (E →ₗ[ℂ] E) = finrank ℂ E * finrank ℂ E :=
  Module.finrank_linearMap ℂ ℂ E E

/-- The induction step of Theorem 5.15. -/
theorem chainBound_step (hn2 : 2 ≤ finrank ℂ E)
    (IH : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F],
      1 ≤ finrank ℂ F → finrank ℂ F < finrank ℂ E →
      ∃ N, ChainBound (F →ₗ[ℂ] F) N ∧ N + recW (finrank ℂ F) ≤ 10 * finrank ℂ F) :
    ChainBound (E →ₗ[ℂ] E) (10 * finrank ℂ E - recW (finrank ℂ E)) := by
  classical
  set n := finrank ℂ E with hn
  intro V ℓ hV
  have hfA : finrank ℂ (E →ₗ[ℂ] E) = n * n := finrank_end
  -- the last index `s` with `alg (V s) ≠ ⊤`
  have h0 : alg (V 0) ≠ ⊤ := by
    intro h
    have he : alg (V 0) = ℂ ∙ (1 : E →ₗ[ℂ] E) := by
      rw [← pow_eq_alg (V 0) (hV.one_mem 0 (Nat.zero_le _)) le_rfl, hV.zero,
        ← Submodule.one_eq_span, one_pow]
    rw [he] at h
    have := finrank_span_singleton (K := ℂ) (one_ne_zero_end (E := E) (by omega))
    rw [h, finrank_top, hfA] at this
    nlinarith
  set s := Nat.findGreatest (fun i => alg (V i) ≠ ⊤) ℓ with hs_def
  have hs : alg (V s) ≠ ⊤ := Nat.findGreatest_spec (P := fun i => alg (V i) ≠ ⊤)
    (Nat.zero_le ℓ) h0
  have hsℓ : s ≤ ℓ := Nat.findGreatest_le ℓ
  have hafter : ∀ i, s < i → i ≤ ℓ → alg (V i) = ⊤ := fun i h1 h2 =>
    not_not.mp (Nat.findGreatest_is_greatest h1 h2)
  have h1s : (1 : E →ₗ[ℂ] E) ∈ V s := hV.one_mem s hsℓ
  have hstar : StarClosed (V s) := hV.star_mem s hsℓ
  set S := algStar (V s) h1s hstar
  have hS : ∀ T : E →ₗ[ℂ] E, T ∈ S → T ∈ alg (V s) := fun T h => h
  have hSne : ∃ T : E →ₗ[ℂ] E, T ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hs (eq_top_iff.mpr fun T _ => hS T (hcon T))
  -- decomposition into simple blocks
  obtain ⟨m, W, hsimple, hsum, ρ, hρ⟩ := exists_decomposition S
  set d : Fin m → ℕ := fun j => finrank ℂ (W j) with hd
  have hd1 : ∀ j, 1 ≤ d j := fun j =>
    Nat.pos_of_ne_zero fun h => (hsimple j).1 (Submodule.finrank_eq_zero.mp h)
  have hdn : ∀ j, d j < n := by
    intro j
    refine lt_of_le_of_ne (Submodule.finrank_le _) fun h => ?_
    have htop : W j = ⊤ := Submodule.eq_top_of_finrank_eq h
    obtain ⟨T, hT⟩ := hSne
    refine hT (mem_of_corner S (W j) (hsimple j)
      (by have h' : finrank ℂ (W j) = n := h; omega) T
      (by rw [htop]; exact le_top) ?_)
    rw [htop, Submodule.top_orthogonal_eq_bot]; exact bot_le
  have hIH : ∀ j, ∃ N, ChainBound (W j →ₗ[ℂ] W j) N ∧ N + recW (d j) ≤ 10 * d j :=
    fun j => IH (W j) (hd1 j) (hdn j)
  choose Nj hNj hNj' using hIH
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun hm => ?_
    subst hm
    simp at hsum
    omega
  have hSb : ChainBound S (∑ j, Nj j) :=
    ChainBound.of_injective ρ hρ (chainBound_pi m' (fun j => W j →ₗ[ℂ] W j) Nj hNj)
  -- the squaring steps inside `S`
  have hexr : ∃ r, V s ^ (2 ^ r) = alg (V s) :=
    ⟨n * n, pow_eq_alg _ h1s (by rw [hfA]; exact Nat.lt_two_pow_self.le)⟩
  set r := Nat.find hexr
  have hr : V s ^ (2 ^ r) = alg (V s) := Nat.find_spec hexr
  have hrmin : ∀ j < r, V s ^ (2 ^ j) ≠ alg (V s) := fun j hj => Nat.find_min hexr hj
  have hbound1 : strictSteps V s + r + 1 ≤ ∑ j, Nj j := by
    have := (hV.isChain_sqExt hsℓ r).strictSteps_add_one_le_of_le S hSb fun i hi x hx => by
      show x ∈ alg (V s)
      rcases le_total i s with h | h
      · rw [sqExt_of_le h] at hx
        exact le_alg _ (hV.mono h hsℓ hx)
      · rw [sqExt_of_ge h] at hx
        exact pow_le_alg _ _ hx
    rwa [hV.strictSteps_sqExt hsℓ hrmin] at this
  -- the arithmetic
  have hsumd : (List.ofFn d).sum = n := by rw [List.sum_ofFn]; exact hsum
  have hmemd : ∀ x ∈ List.ofFn d, ∃ j, d j = x := fun x hx => List.mem_ofFn.mp hx
  have hrecW : ((List.ofFn d).map recW).sum = ∑ j, recW (d j) := by
    rw [List.map_ofFn, List.sum_ofFn]; rfl
  have hNsum : ∑ j, Nj j + ∑ j, recW (d j) ≤ 10 * n := by
    rw [← Finset.sum_add_distrib]
    calc ∑ j, (Nj j + recW (d j)) ≤ ∑ j, 10 * d j := Finset.sum_le_sum fun j _ => hNj' j
      _ = 10 * n := by rw [← Finset.mul_sum]; exact congrArg _ hsum
  by_cases hbig : ∃ j, n < 2 * d j
  · obtain ⟨j0, hj0⟩ := hbig
    have hrec := recursion_big (List.ofFn d) n (d j0) hsumd
      (List.mem_ofFn.mpr ⟨j0, rfl⟩) (hdn j0) hj0
    rw [hrecW] at hrec
    set c := Nat.clog 2 (n - d j0)
    have htop : s + r + 2 + c ≤ ℓ → V (s + r + 2 + c) = ⊤ := by
      intro ht
      set X := V (s + r + 1)
      have hX1 : (1 : E →ₗ[ℂ] E) ∈ X := hV.one_mem _ (by omega)
      have hXstar : StarClosed X := hV.star_mem _ (by omega)
      have halgX : alg X = ⊤ := by
        refine top_le_iff.mp ?_
        rw [← hafter (s + 1) (by omega) (by omega)]
        exact alg_mono (hV.mono (by omega) (by omega))
      have hcorner : ∀ T : E →ₗ[ℂ] E, LinearMap.range T ≤ W j0 → (W j0)ᗮ ≤ LinearMap.ker T →
          T ∈ X := by
        intro T hT hT'
        have hTS := hS T (mem_of_corner S (W j0) (hsimple j0) hj0 T hT hT')
        rw [← hr] at hTS
        exact hV.le_succ (by omega) (hV.pow_two_pow_le (by omega) hTS)
      have hXtop := corner_pow_eq_top X hX1 hXstar halgX (W j0) (hsimple j0).1 (hdn j0) hcorner
      have hle : 2 * (n - d j0) ≤ 2 ^ (1 + c) := by
        rw [pow_add, pow_one]
        exact Nat.mul_le_mul_left 2 (Nat.le_pow_clog (by norm_num) _)
      refine top_le_iff.mp ?_
      calc ⊤ = X ^ (2 * (n - d j0)) := hXtop.symm
        _ ≤ X ^ (2 ^ (1 + c)) := pow_le_pow_of_one_mem hX1 hle
        _ ≤ V (s + r + 1 + (1 + c)) := hV.pow_two_pow_le (by omega)
        _ = V (s + r + 2 + c) := by congr 1; omega
    have := hV.strictSteps_le_of_top (s := s) htop
    unfold recW at hrec hNsum ⊢
    omega
  · push Not at hbig
    have hrec := recursion_small (List.ofFn d) n hn2 hsumd fun x hx => by
      obtain ⟨j, rfl⟩ := hmemd x hx; exact hbig j
    rw [hrecW] at hrec
    set c := Nat.clog 2 (n * n)
    have htop : s + 1 + c ≤ ℓ → V (s + 1 + c) = ⊤ := by
      intro ht
      set X := V (s + 1)
      have hX1 : (1 : E →ₗ[ℂ] E) ∈ X := hV.one_mem _ (by omega)
      have halgX : alg X = ⊤ := hafter (s + 1) (by omega) (by omega)
      have hXtop : X ^ (n * n) = ⊤ := by rw [← halgX]; exact pow_eq_alg X hX1 hfA.le
      refine top_le_iff.mp ?_
      calc ⊤ = X ^ (n * n) := hXtop.symm
        _ ≤ X ^ (2 ^ c) := pow_le_pow_of_one_mem hX1 (Nat.le_pow_clog (by norm_num) _)
        _ ≤ V (s + 1 + c) := hV.pow_two_pow_le (by omega)
    have := hV.strictSteps_le_of_top (s := s) htop
    unfold recW at hrec hNsum ⊢
    omega

end Step

/-- **Theorem 5.15** (with constant 10): for every finite-dimensional complex inner product
space `E` of dimension `n ≥ 1`, weak chains in `End E` have fewer than `N` strict steps for
some `N` with `N + 2 ⌈log₂ n⌉ + 9 ≤ 10 n`. -/
theorem chainBound_end : ∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E], finrank ℂ E = n → 1 ≤ n →
    ∃ N, ChainBound (E →ₗ[ℂ] E) N ∧ N + 2 * Nat.clog 2 n + 9 ≤ 10 * n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro E _ _ _ hn hn1
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
  · refine ⟨1, chainBound_one_of_span_eq_top ?_, by simp⟩
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_singleton (one_ne_zero_end (E := E) (by omega)), finrank_end, hn]
  · refine ⟨10 * n - recW n, ?_, ?_⟩
    · subst hn
      exact chainBound_step hn2 fun F _ _ _ hF1 hFn => by
        obtain ⟨N, hN, hN'⟩ := IH _ hFn F rfl hF1
        exact ⟨N, hN, by unfold recW; omega⟩
    · have := clog_le_self n
      unfold recW; omega

/-- **Two-dimensional bound** for matrices (Theorem 5.15 with constant 10): every weak chain
in `M_n(ℂ)` has at most `10 n` strict steps. -/
theorem matrix_chainBound (n : ℕ) : ChainBound (Matrix (Fin n) (Fin n) ℂ) (10 * n + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine (chainBound_one_of_span_eq_top ?_).mono (by norm_num)
    exact Subsingleton.elim _ _
  · obtain ⟨N, hN, hN'⟩ := chainBound_end n (EuclideanSpace ℂ (Fin n)) finrank_euclideanSpace_fin hn
    refine (ChainBound.of_injective
      ((LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin n) ℂ)).symm :
        Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] _)
      (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin n) ℂ)).symm.injective hN).mono
      (by omega)

end Lax119563Proofs.Stabilization
