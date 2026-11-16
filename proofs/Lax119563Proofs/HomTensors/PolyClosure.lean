import Mathlib

/-!
# Polynomial closure

Lemma `lem:polynomial-closure`: for a finite set `𝒢` of functions on a finite set `X` of size
`M`, every function that is constant on the classes of "agreeing on all of `𝒢`" is a linear
combination of products of at most `M - 1` elements of `𝒢`.

The span `P d` of the products of at most `d` elements forms an increasing chain that is
constant from the first `d` with `P (d+1) = P d` on; as `dim P 0 = 1` and `dim P d ≤ M`, the
chain is constant from `M - 1` on, so `P (M-1)` is closed under multiplication with `𝒢`, and
Lagrange-type interpolation products give all class indicators.
-/

namespace Lax119563Proofs.HomTensors

open Finset

variable {X : Type}

/-- Products of at most `d` elements of `𝒢`. -/
def prods (𝒢 : Set (X → ℚ)) (d : ℕ) : Set (X → ℚ) :=
  {f | ∃ l : List (X → ℚ), l.length ≤ d ∧ (∀ g ∈ l, g ∈ 𝒢) ∧ l.prod = f}

/-- The span of the products of at most `d` elements of `𝒢`. -/
noncomputable def polySpan (𝒢 : Set (X → ℚ)) (d : ℕ) : Submodule ℚ (X → ℚ) :=
  Submodule.span ℚ (prods 𝒢 d)

variable (𝒢 : Set (X → ℚ))

lemma polySpan_mono {d e : ℕ} (h : d ≤ e) : polySpan 𝒢 d ≤ polySpan 𝒢 e := by
  apply Submodule.span_mono
  rintro f ⟨l, hl, hg, rfl⟩
  exact ⟨l, hl.trans h, hg, rfl⟩

lemma one_mem_polySpan (d : ℕ) : (1 : X → ℚ) ∈ polySpan 𝒢 d :=
  Submodule.subset_span ⟨[], by simp, by simp, rfl⟩

lemma mul_mem_polySpan {g : X → ℚ} (hg : g ∈ 𝒢) {d : ℕ} {f : X → ℚ} (hf : f ∈ polySpan 𝒢 d) :
    g * f ∈ polySpan 𝒢 (d + 1) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨l, hl, hl', rfl⟩ := hf
    exact Submodule.subset_span ⟨g :: l, by simpa using hl, by
      rintro g' (_ | ⟨_, hg'⟩)
      · exact hg
      · exact hl' g' hg', rfl⟩
  | zero => simp
  | add f f' _ _ h h' => rw [mul_add]; exact Submodule.add_mem _ h h'
  | smul c f _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h

lemma polySpan_step {d : ℕ} (h : polySpan 𝒢 (d + 1) ≤ polySpan 𝒢 d) :
    polySpan 𝒢 (d + 2) ≤ polySpan 𝒢 (d + 1) := by
  apply Submodule.span_le.2
  rintro f ⟨l, hl, hg, rfl⟩
  cases l with
  | nil => exact one_mem_polySpan 𝒢 _
  | cons g l =>
    rw [List.prod_cons]
    apply mul_mem_polySpan 𝒢 (hg g (by simp))
    apply h
    exact Submodule.subset_span ⟨l, by simpa using hl, fun g' hg' => hg g' (by simp [hg']), rfl⟩

lemma polySpan_stable {d : ℕ} (h : polySpan 𝒢 (d + 1) ≤ polySpan 𝒢 d) (e : ℕ) :
    polySpan 𝒢 (d + e) ≤ polySpan 𝒢 d := by
  have step : ∀ e, polySpan 𝒢 (d + e + 1) ≤ polySpan 𝒢 (d + e) := by
    intro e
    induction e with
    | zero => simpa using h
    | succ e ih => exact polySpan_step 𝒢 ih
  induction e with
  | zero => simp
  | succ e ih => exact (step e).trans ih

lemma exists_polySpan_stable [Fintype X] [Nonempty X] :
    ∃ d, d + 1 ≤ Fintype.card X ∧ polySpan 𝒢 (d + 1) ≤ polySpan 𝒢 d := by
  by_contra hcon
  push Not at hcon
  have hlt : ∀ d, d + 1 ≤ Fintype.card X → polySpan 𝒢 d < polySpan 𝒢 (d + 1) :=
    fun d hd => lt_of_le_not_ge (polySpan_mono 𝒢 (Nat.le_succ d)) (hcon d hd)
  have hrank : ∀ d, d ≤ Fintype.card X → d + 1 ≤ Module.finrank ℚ (polySpan 𝒢 d) := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [zero_add, Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
      intro h0
      have := one_mem_polySpan 𝒢 0
      rw [h0, Submodule.mem_bot] at this
      exact one_ne_zero this
    | succ d ih =>
      intro hd
      have := Submodule.finrank_lt_finrank_of_lt (hlt d hd)
      have := ih (by omega)
      omega
  have h1 := hrank _ le_rfl
  have h2 := Submodule.finrank_le (polySpan 𝒢 (Fintype.card X))
  rw [Module.finrank_fintype_fun_eq_card] at h2
  omega

/-- The span `polySpan 𝒢 (|X| - 1)` is closed under multiplication with elements of `𝒢`. -/
lemma mul_mem_polySpan_top [Fintype X] {g : X → ℚ} (hg : g ∈ 𝒢) {f : X → ℚ}
    (hf : f ∈ polySpan 𝒢 (Fintype.card X - 1)) : g * f ∈ polySpan 𝒢 (Fintype.card X - 1) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · rw [Subsingleton.elim (g * f) 0]
    exact Submodule.zero_mem _
  obtain ⟨d, hd, hst⟩ := exists_polySpan_stable 𝒢
  have h := mul_mem_polySpan 𝒢 hg hf
  have hM : Fintype.card X - 1 + 1 = d + (Fintype.card X - d) := by omega
  rw [hM] at h
  exact polySpan_mono 𝒢 (by omega) (polySpan_stable 𝒢 hst _ h)

lemma prod_mul_mem {A : Submodule ℚ (X → ℚ)} {ι : Type} (s : Finset ι) (φ : ι → X → ℚ)
    (hφ : ∀ i ∈ s, ∀ f ∈ A, φ i * f ∈ A) : ∀ f ∈ A, (∏ i ∈ s, φ i) * f ∈ A := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    intro f hf
    rw [prod_insert ha, mul_assoc]
    exact hφ a (mem_insert_self a s) _
      (ih (fun i hi => hφ i (mem_insert_of_mem hi)) f hf)

/-- **Polynomial closure.** A function constant on the classes of agreement on the finite set
`𝒢` is a linear combination of products of at most `|X| - 1` elements of `𝒢`. -/
theorem mem_polySpan [Fintype X] (𝒢 : Finset (X → ℚ)) (f : X → ℚ)
    (hf : ∀ x y, (∀ g ∈ 𝒢, g x = g y) → f x = f y) :
    f ∈ polySpan (𝒢 : Set (X → ℚ)) (Fintype.card X - 1) := by
  classical
  set A := polySpan (𝒢 : Set (X → ℚ)) (Fintype.card X - 1)
  -- interpolation factors
  let φ : (X → ℚ) → X → X → X → ℚ := fun g x₀ x => (g x₀ - g x)⁻¹ • (g - fun _ => g x)
  have hφ : ∀ g ∈ 𝒢, ∀ x₀ x, ∀ f ∈ A, φ g x₀ x * f ∈ A := by
    intro g hg x₀ x f hf
    have : φ g x₀ x * f = (g x₀ - g x)⁻¹ • (g * f - g x • f) := by
      funext z
      simp [φ, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (mul_mem_polySpan_top _ hg hf)
      (Submodule.smul_mem _ _ hf))
  let e : X → X → ℚ := fun x₀ =>
    ∏ g ∈ 𝒢, ∏ x ∈ univ.filter (fun x => g x ≠ g x₀), φ g x₀ x
  have he_mem : ∀ x₀, e x₀ ∈ A := by
    intro x₀
    have := prod_mul_mem 𝒢 (fun g => ∏ x ∈ univ.filter (fun x => g x ≠ g x₀), φ g x₀ x)
      (fun g hg => prod_mul_mem _ _ (fun x _ => hφ g hg x₀ x)) 1
      (one_mem_polySpan _ _)
    simpa [e] using this
  have he_apply : ∀ x₀ z, e x₀ z = if ∀ g ∈ 𝒢, g z = g x₀ then 1 else 0 := by
    intro x₀ z
    simp only [e, Finset.prod_apply]
    split_ifs with h
    · refine Finset.prod_eq_one fun g hg => Finset.prod_eq_one fun x hx => ?_
      have hx : g x ≠ g x₀ := (Finset.mem_filter.1 hx).2
      simp only [φ, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, h g hg]
      exact inv_mul_cancel₀ (sub_ne_zero.2 hx.symm)
    · push Not at h
      obtain ⟨g, hg, hgz⟩ := h
      refine Finset.prod_eq_zero hg (Finset.prod_eq_zero (i := z) (by simp [hgz]) ?_)
      simp [φ]
  -- the class sizes
  let N : X → ℕ := fun z => (univ.filter fun y => ∀ g ∈ 𝒢, g y = g z).card
  have hf_eq : f = ∑ x₀, (f x₀ / N x₀) • e x₀ := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, he_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero]
    rw [← Finset.sum_filter]
    have hfil : (univ.filter fun x₀ : X => ∀ g ∈ 𝒢, g z = g x₀) =
        univ.filter fun y => ∀ g ∈ 𝒢, g y = g z := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h g hg => (h g hg).symm, fun h g hg => (h g hg).symm⟩
    have hterm : ∀ x₀ ∈ (univ.filter fun x₀ : X => ∀ g ∈ 𝒢, g z = g x₀),
        f x₀ / N x₀ = f z / N z := by
      intro x₀ hx₀
      have hx₀ := (Finset.mem_filter.1 hx₀).2
      rw [hf x₀ z fun g hg => (hx₀ g hg).symm]
      congr 2
      simp only [N]
      congr 1
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h g hg => (h g hg).trans (hx₀ g hg).symm,
        fun h g hg => (h g hg).trans (hx₀ g hg)⟩
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, hfil, nsmul_eq_mul]
    have hpos : (N z : ℚ) ≠ 0 := by
      have : 0 < N z := Finset.card_pos.2 ⟨z, by simp⟩
      exact_mod_cast this.ne'
    field_simp
    rfl
  rw [hf_eq]
  exact Submodule.sum_mem _ fun x₀ _ => Submodule.smul_mem _ _ (he_mem x₀)

end Lax119563Proofs.HomTensors
