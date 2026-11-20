import Lax119563Proofs.Stabilization.Chains

/-!
# The corner lemma (Döring–Neuen, Lemma 5.12), basis-free

`X` a star-closed subspace of `End E` with `1 ∈ X` generating `End E`, `W ≠ ⊥` a subspace with
`dim W < n` such that every operator with range in `W` vanishing on `Wᗮ` lies in `X`. Then
`X ^ (2 (n - dim W)) = ⊤`.

Proof: the orbit spaces `H t = span {a u | a ∈ X ^ t, u ∈ W}` grow strictly until they are
`⊤`, so `dim H (k - 1) ≥ n - 1` and `H k = ⊤` for `k = n - dim W`. Rank-one maps
`rk v w = ⟪w, ·⟫ v` satisfy `rk (a u) (b u') = a * rk u u' * star b`, hence
`rk v w ∈ X ^ (p + 1 + q)` for `v ∈ H p`, `w ∈ H q`. Every operator is a sum of rank-one maps;
a rank-one map with one argument in `H (k - 1)` is in `X ^ (2 k)`, and the remaining direction
`Hᗮ = ℂ z` is handled via `rk z z = 1 - (1 - rk z z)`.
-/

open Module

set_option linter.unusedSectionVars false

noncomputable section

namespace Lax119563Proofs.Stabilization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-! ### Rank-one maps -/

/-- The rank-one map `x ↦ ⟪w, x⟫ v`. -/
def rk (v w : E) : E →ₗ[ℂ] E where
  toFun x := inner ℂ w x • v
  map_add' x y := by simp [add_smul]
  map_smul' c x := by simp [mul_smul]

@[simp] theorem rk_apply (v w x : E) : rk v w x = inner ℂ w x • v := rfl

theorem mul_rk (a : E →ₗ[ℂ] E) (v w : E) : a * rk v w = rk (a v) w := by
  ext x; simp

theorem rk_mul_star (v w : E) (b : E →ₗ[ℂ] E) : rk v w * star b = rk v (b w) := by
  ext x
  simp [LinearMap.star_eq_adjoint, LinearMap.adjoint_inner_right]

theorem rk_add_left (v v' w : E) : rk (v + v') w = rk v w + rk v' w := by
  ext x; simp [smul_add]

theorem rk_smul_left (c : ℂ) (v w : E) : rk (c • v) w = c • rk v w := by
  ext x; simp [smul_smul, mul_comm]

theorem rk_add_right (v w w' : E) : rk v (w + w') = rk v w + rk v w' := by
  ext x; simp [add_smul]

theorem rk_smul_right (c : ℂ) (v w : E) : rk v (c • w) = (starRingEnd ℂ c) • rk v w := by
  ext x; simp [smul_smul, mul_comm]

/-- `v ↦ rk v w` as a linear map. -/
def rkLeft (w : E) : E →ₗ[ℂ] (E →ₗ[ℂ] E) where
  toFun v := rk v w
  map_add' v v' := rk_add_left v v' w
  map_smul' c v := rk_smul_left c v w

/-- `w ↦ rk v w` as a conjugate-linear map. -/
def rkRight (v : E) : E →ₗ⋆[ℂ] (E →ₗ[ℂ] E) where
  toFun w := rk v w
  map_add' w w' := rk_add_right v w w'
  map_smul' c w := rk_smul_right c v w

/-- Every operator is a sum of rank-one maps. -/
theorem eq_sum_rk (T : E →ₗ[ℂ] E) :
    T = ∑ i, rk (T (stdOrthonormalBasis ℂ E i)) (stdOrthonormalBasis ℂ E i) := by
  ext x
  rw [LinearMap.sum_apply]
  conv_lhs => rw [← (stdOrthonormalBasis ℂ E).sum_repr' x]
  simp [map_sum, map_smul]

/-! ### Orbit spaces -/

/-- `H t = span {a u | a ∈ X ^ t, u ∈ W}`. -/
def orbit (X : Submodule ℂ (E →ₗ[ℂ] E)) (W : Submodule ℂ E) (t : ℕ) : Submodule ℂ E :=
  Submodule.span ℂ {v | ∃ a ∈ X ^ t, ∃ u ∈ W, a u = v}

variable {X : Submodule ℂ (E →ₗ[ℂ] E)} {W : Submodule ℂ E}

theorem mem_orbit_of {t : ℕ} {a : E →ₗ[ℂ] E} (ha : a ∈ X ^ t) {u : E} (hu : u ∈ W) :
    a u ∈ orbit X W t :=
  Submodule.subset_span ⟨a, ha, u, hu, rfl⟩

theorem orbit_map {p t : ℕ} {a : E →ₗ[ℂ] E} (ha : a ∈ X ^ p) {v : E} (hv : v ∈ orbit X W t) :
    a v ∈ orbit X W (p + t) := by
  have : orbit X W t ≤ (orbit X W (p + t)).comap a := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, hb, u, hu, rfl⟩
    show a (b u) ∈ orbit X W (p + t)
    rw [← Module.End.mul_apply]
    exact mem_orbit_of ((pow_add X p t).ge (Submodule.mul_mem_mul ha hb)) hu
  exact this hv

theorem le_orbit_zero : W ≤ orbit X W 0 := by
  intro u hu
  have : (1 : E →ₗ[ℂ] E) ∈ X ^ 0 :=
    (pow_zero X).ge ⟨1, map_one (algebraMap ℂ (E →ₗ[ℂ] E))⟩
  simpa using mem_orbit_of this hu

theorem orbit_le_succ (h1 : (1 : E →ₗ[ℂ] E) ∈ X) (t : ℕ) : orbit X W t ≤ orbit X W (t + 1) := by
  intro v hv
  have := orbit_map ((pow_one X).ge h1) hv
  rw [add_comm] at this
  simpa using this

theorem orbit_invariant {t : ℕ} (hst : orbit X W t = orbit X W (t + 1)) :
    ∀ p, ∀ a ∈ X ^ p, ∀ v ∈ orbit X W t, a v ∈ orbit X W t := by
  intro p
  induction p with
  | zero =>
    intro a ha v hv
    replace ha := (pow_zero X).le ha
    rw [Submodule.mem_one] at ha
    obtain ⟨c, rfl⟩ := ha
    simpa [Algebra.algebraMap_eq_smul_one] using Submodule.smul_mem _ c hv
  | succ p ih =>
    intro a ha v hv
    replace ha := (pow_succ' X p).le ha
    refine Submodule.mul_induction_on ha (fun b hb c hc => ?_) (fun x y hx hy => ?_)
    · rw [Module.End.mul_apply]
      have := orbit_map ((pow_one X).ge hb) (ih c hc v hv)
      rwa [add_comm, ← hst] at this
    · rw [LinearMap.add_apply]; exact add_mem hx hy

theorem le_orbit (h1 : (1 : E →ₗ[ℂ] E) ∈ X) : ∀ t, W ≤ orbit X W t
  | 0 => le_orbit_zero
  | t + 1 => (le_orbit h1 t).trans (orbit_le_succ h1 t)

theorem orbit_eq_top_of_stable (h1 : (1 : E →ₗ[ℂ] E) ∈ X) (halg : alg X = ⊤) (hW : W ≠ ⊥)
    {t : ℕ} (hst : orbit X W t = orbit X W (t + 1)) : orbit X W t = ⊤ := by
  have hall : ∀ a : E →ₗ[ℂ] E, ∀ v ∈ orbit X W t, a v ∈ orbit X W t := by
    intro a v hv
    have : a ∈ X ^ finrank ℂ (E →ₗ[ℂ] E) :=
      (pow_eq_alg X h1 le_rfl).ge (by rw [halg]; exact Submodule.mem_top)
    exact orbit_invariant hst _ a this v hv
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have huH : u ∈ orbit X W t := le_orbit h1 t hu
  have huu : inner ℂ u u ≠ 0 := inner_self_ne_zero.mpr hu0
  refine eq_top_iff.mpr fun y _ => ?_
  have := Submodule.smul_mem _ (inner ℂ u u)⁻¹ (hall (rk y u) u huH)
  rwa [rk_apply, smul_smul, inv_mul_cancel₀ huu, one_smul] at this

theorem finrank_orbit (h1 : (1 : E →ₗ[ℂ] E) ∈ X) (halg : alg X = ⊤) (hW : W ≠ ⊥) :
    ∀ t, min (finrank ℂ E) (finrank ℂ W + t) ≤ finrank ℂ (orbit X W t) := by
  intro t
  induction t with
  | zero => exact (min_le_right _ _).trans (Submodule.finrank_mono (le_orbit_zero))
  | succ t ih =>
    by_cases hst : orbit X W t = orbit X W (t + 1)
    · rw [← hst, orbit_eq_top_of_stable h1 halg hW hst, finrank_top]
      exact min_le_left _ _
    · have := Submodule.finrank_lt_finrank_of_lt
        (lt_of_le_of_ne (orbit_le_succ h1 t) hst)
      omega

/-! ### Rank-one maps in powers of `X` -/

theorem rk_mem_of_mem_orbit (hX : StarClosed X)
    (hcorner : ∀ T : E →ₗ[ℂ] E, LinearMap.range T ≤ W → Wᗮ ≤ LinearMap.ker T → T ∈ X)
    {p q : ℕ} {v w : E} (hv : v ∈ orbit X W p) (hw : w ∈ orbit X W q) :
    rk v w ∈ X ^ (p + 1 + q) := by
  -- generators
  have hgen : ∀ a ∈ X ^ p, ∀ u ∈ W, ∀ b ∈ X ^ q, ∀ u' ∈ W, rk (a u) (b u') ∈ X ^ (p + 1 + q) := by
    intro a ha u hu b hb u' hu'
    have hc : rk u u' ∈ X := by
      refine hcorner _ ?_ ?_
      · rintro _ ⟨x, rfl⟩
        exact Submodule.smul_mem _ _ hu
      · intro x hx
        simp [LinearMap.mem_ker, Submodule.inner_right_of_mem_orthogonal hu' hx]
    rw [← mul_rk, ← rk_mul_star, ← mul_assoc]
    exact (pow_add X (p + 1) q).ge (Submodule.mul_mem_mul
      ((pow_succ X p).ge (Submodule.mul_mem_mul ha hc)) ((hX.pow q) b hb))
  -- extend in `v`
  have hleft : ∀ b ∈ X ^ q, ∀ u' ∈ W, rk v (b u') ∈ X ^ (p + 1 + q) := by
    intro b hb u' hu'
    have : orbit X W p ≤ (X ^ (p + 1 + q)).comap (rkLeft (b u')) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨a, ha, u, hu, rfl⟩
      exact hgen a ha u hu b hb u' hu'
    exact this hv
  have : orbit X W q ≤ (X ^ (p + 1 + q)).comap (rkRight v) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, hb, u', hu', rfl⟩
    exact hleft b hb u' hu'
  exact this hw

/-! ### The corner lemma -/

/-- **Lemma 5.12.** -/
theorem corner_pow_eq_top (X : Submodule ℂ (E →ₗ[ℂ] E)) (h1 : (1 : E →ₗ[ℂ] E) ∈ X)
    (hX : StarClosed X) (halg : alg X = ⊤) (W : Submodule ℂ E) (hW : W ≠ ⊥)
    (hWn : finrank ℂ W < finrank ℂ E)
    (hcorner : ∀ T : E →ₗ[ℂ] E, LinearMap.range T ≤ W → Wᗮ ≤ LinearMap.ker T → T ∈ X) :
    X ^ (2 * (finrank ℂ E - finrank ℂ W)) = ⊤ := by
  set n := finrank ℂ E
  set k := n - finrank ℂ W with hk
  have hk1 : 1 ≤ k := by omega
  set H := orbit X W (k - 1) with hH
  set Y := X ^ (2 * k)
  have hHk : orbit X W k = ⊤ := by
    have := finrank_orbit h1 halg hW k
    exact Submodule.eq_top_of_finrank_eq
      (le_antisymm (Submodule.finrank_le _) (by omega))
  have hHdim : n - 1 ≤ finrank ℂ H := by
    have := finrank_orbit h1 halg hW (k - 1)
    rw [← hH] at this
    omega
  have hY1 : ∀ v ∈ H, ∀ w, rk v w ∈ Y := by
    intro v hv w
    have := rk_mem_of_mem_orbit hX hcorner hv (hHk ▸ Submodule.mem_top : w ∈ orbit X W k)
    rwa [show k - 1 + 1 + k = 2 * k by omega] at this
  have hY2 : ∀ v, ∀ w ∈ H, rk v w ∈ Y := by
    intro v w hw
    have := rk_mem_of_mem_orbit hX hcorner (hHk ▸ Submodule.mem_top : v ∈ orbit X W k) hw
    rwa [show k + 1 + (k - 1) = 2 * k by omega] at this
  have hsum : ∀ T : E →ₗ[ℂ] E, (∀ i, rk (T (stdOrthonormalBasis ℂ E i))
      (stdOrthonormalBasis ℂ E i) ∈ Y) → T ∈ Y := by
    intro T hT
    rw [eq_sum_rk T]
    exact Submodule.sum_mem _ fun i _ => hT i
  have hall : ∀ v w, rk v w ∈ Y := by
    by_cases hHtop : H = ⊤
    · intro v w; exact hY1 v (hHtop ▸ Submodule.mem_top) w
    have hperp : Hᗮ ≠ ⊥ := fun h => hHtop (Submodule.orthogonal_eq_bot_iff.mp h)
    obtain ⟨z0, hz0, hz00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp
    set z : E := ((‖z0‖⁻¹ : ℝ) : ℂ) • z0
    have hzH : z ∈ Hᗮ := Submodule.smul_mem _ _ hz0
    have hzz : inner ℂ z z = 1 := by
      rw [inner_self_eq_norm_sq_to_K]
      have : ‖z‖ = 1 := by
        simp only [z]
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz00)]
      simp [this]
    have hz0' : z ≠ 0 := fun h => by simp [h] at hzz
    have hspan : Hᗮ = ℂ ∙ z := by
      refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
      · exact (Submodule.span_singleton_le_iff_mem _ _).mpr hzH
      · rw [finrank_span_singleton hz0']
        have := Submodule.finrank_add_finrank_orthogonal H
        omega
    have hproj : ∀ v, v - inner ℂ z v • z ∈ H := by
      intro v
      rw [← Submodule.orthogonal_orthogonal H, Submodule.mem_orthogonal]
      intro u hu
      rw [hspan, Submodule.mem_span_singleton] at hu
      obtain ⟨c, rfl⟩ := hu
      rw [inner_smul_left, inner_sub_right, inner_smul_right, hzz]
      simp
    have hrkzz : rk z z ∈ Y := by
      have hQ : (1 - rk z z) ∈ Y := hsum _ fun i => hY1 _ (by
        simpa [sub_eq_add_neg] using hproj (stdOrthonormalBasis ℂ E i)) _
      have h1Y : (1 : E →ₗ[ℂ] E) ∈ Y := one_mem_pow h1 _
      simpa using sub_mem h1Y hQ
    intro v w
    have e1 : rk v w = rk (v - inner ℂ z v • z) w + inner ℂ z v • rk z w := by
      rw [← rk_smul_left, ← rk_add_left, sub_add_cancel]
    have e2 : rk z w = rk z (w - inner ℂ z w • z) + (starRingEnd ℂ (inner ℂ z w)) • rk z z := by
      rw [← rk_smul_right, ← rk_add_right, sub_add_cancel]
    rw [e1, e2]
    exact add_mem (hY1 _ (hproj v) _) (Submodule.smul_mem _ _
      (add_mem (hY2 _ _ (hproj w)) (Submodule.smul_mem _ _ hrkzz)))
  exact eq_top_iff.mpr fun T _ => hsum T fun i => hall _ _

end Lax119563Proofs.Stabilization

end
