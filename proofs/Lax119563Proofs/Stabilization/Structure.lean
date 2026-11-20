import Lax119563Proofs.Stabilization.Defs

/-!
# Stabilization bound: structure of `⋆`-subalgebras of `End(E)`

`E` is a finite dimensional complex inner product space, `S` a `⋆`-subalgebra of `End(E)`
(star = adjoint). We show

* `E` is a semisimple `S`-module (orthogonal complements of invariant subspaces are invariant);
* `mem_of_corner'`: if `W` is `S`-simple with `2 dim W > dim E`, every operator with range in `W`
  vanishing on `Wᗮ` lies in `S` (Jacobson density / bicommutant theorem);
* `exists_decomposition'`: `E` splits into `S`-simple subspaces, and restriction to them is an
  injective unital `⋆`-algebra homomorphism.
-/

open Module

namespace Lax119563Proofs.Stabilization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

section Basic

variable (S : StarSubalgebra ℂ (E →ₗ[ℂ] E))

instance isScalarTower_starSubalgebra : IsScalarTower ℂ S E :=
  ⟨fun _ _ _ => rfl⟩

theorem invariant_orthogonal {W : Submodule ℂ E} (hW : Invariant S W) : Invariant S Wᗮ := by
  intro a ha x hx
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [← LinearMap.adjoint_inner_left]
  exact (Submodule.mem_orthogonal _ _).1 hx _ (hW _ (star_mem ha) u hu)

/-- The `S`-submodule of `E` given by an `S`-invariant subspace. -/
def toSSubmodule (W : Submodule ℂ E) (hW : Invariant S W) : Submodule S E where
  carrier := W
  add_mem' := W.add_mem
  zero_mem' := W.zero_mem
  smul_mem' a _ hx := hW a a.2 _ hx

theorem restrictScalars_toSSubmodule (W : Submodule ℂ E) (hW : Invariant S W) :
    (toSSubmodule S W hW).restrictScalars ℂ = W := rfl

theorem invariant_restrictScalars (p : Submodule S E) : Invariant S (p.restrictScalars ℂ) :=
  fun a ha _ hx => p.smul_mem ⟨a, ha⟩ hx

instance isSemisimpleModule : IsSemisimpleModule S E := by
  refine (isSemisimpleModule_iff S E).2 ⟨fun p =>
    ⟨toSSubmodule S _ (invariant_orthogonal S (invariant_restrictScalars S p)), ?_⟩⟩
  rw [← Submodule.isCompl_restrictScalars_iff ℂ, restrictScalars_toSSubmodule]
  exact Submodule.isCompl_orthogonal (K := p.restrictScalars ℂ)

end Basic

section Corner

variable {S : StarSubalgebra ℂ (E →ₗ[ℂ] E)}

/-- A map commuting with `S` preserves every big `S`-simple subspace. -/
theorem preserves_of_commute {W : Submodule ℂ E} (hW : IsSimpleFor S W)
    (h2 : finrank ℂ E < 2 * finrank ℂ W) (b : E →ₗ[ℂ] E) (hb : ∀ a ∈ S, b * a = a * b) :
    ∀ x ∈ W, b x ∈ W := by
  let U : Submodule ℂ E := W ⊓ W.comap b
  have hU : Invariant S U := by
    rintro a ha x ⟨hxW, hxb⟩
    refine ⟨hW.2.1 a ha x hxW, ?_⟩
    have h := LinearMap.congr_fun (hb a ha) x
    simp only [Module.End.mul_apply] at h
    show b (a x) ∈ W
    rw [h]
    exact hW.2.1 a ha _ hxb
  rcases hW.2.2 U inf_le_left hU with h | h
  · exfalso
    let f : W →ₗ[ℂ] E ⧸ W := W.mkQ ∘ₗ b ∘ₗ W.subtype
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro w hw
      have hwU : (w : E) ∈ U := ⟨w.2, (Submodule.Quotient.mk_eq_zero W).1 hw⟩
      rw [h] at hwU
      exact Subtype.ext ((Submodule.mem_bot ℂ).1 hwU)
    have h1 := LinearMap.finrank_le_finrank_of_injective hf
    have h3 := W.finrank_quotient_add_finrank
    omega
  · intro x hx
    have hxU : x ∈ U := h ▸ hx
    exact hxU.2

/-- A map commuting with `S` and preserving an `S`-simple subspace acts on it as a scalar. -/
theorem exists_scalar_of_commute {W : Submodule ℂ E} (hW : IsSimpleFor S W) (b : E →ₗ[ℂ] E)
    (hb : ∀ a ∈ S, b * a = a * b) (hbW : ∀ x ∈ W, b x ∈ W) :
    ∃ c : ℂ, ∀ x ∈ W, b x = c • x := by
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hW.1
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (b.restrict hbW)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  let U : Submodule ℂ E := W ⊓ Module.End.eigenspace b c
  have hU : Invariant S U := by
    rintro a ha x ⟨hxW, hxk⟩
    refine ⟨hW.2.1 a ha x hxW, ?_⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hxk ⊢
    have h := LinearMap.congr_fun (hb a ha) x
    simp only [Module.End.mul_apply] at h
    rw [h, hxk, map_smul]
  rcases hW.2.2 U inf_le_left hU with h | h
  · exfalso
    have hvU : (v : E) ∈ U := by
      refine ⟨v.2, ?_⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      exact congrArg Subtype.val hv.apply_eq_smul
    rw [h] at hvU
    exact hv.2 (Subtype.ext ((Submodule.mem_bot ℂ).1 hvU))
  · refine ⟨c, fun x hx => ?_⟩
    have hxU : x ∈ U := h ▸ hx
    exact Module.End.mem_eigenspace_iff.1 hxU.2

theorem star_commute {b : E →ₗ[ℂ] E} (hb : ∀ a ∈ S, b * a = a * b) :
    ∀ a ∈ S, star b * a = a * star b := by
  intro a ha
  have h := congrArg star (hb (star a) (star_mem ha))
  simp only [star_mul, star_star] at h
  exact h.symm

/-- **Corner lemma.** -/
theorem mem_of_corner' (S : StarSubalgebra ℂ (E →ₗ[ℂ] E)) (W : Submodule ℂ E)
    (hW : IsSimpleFor S W) (h2 : finrank ℂ E < 2 * finrank ℂ W) (T : E →ₗ[ℂ] E)
    (hT : LinearMap.range T ≤ W) (hT' : Wᗮ ≤ LinearMap.ker T) : T ∈ S := by
  classical
  -- every map commuting with `S` commutes with `T`
  have hcomm : ∀ b : E →ₗ[ℂ] E, (∀ a ∈ S, b * a = a * b) → ∀ x, T (b x) = b (T x) := by
    intro b hb x
    have hbW := preserves_of_commute hW h2 b hb
    have hbW' : ∀ y ∈ Wᗮ, b y ∈ Wᗮ := by
      intro y hy
      rw [Submodule.mem_orthogonal]
      intro u hu
      rw [← LinearMap.adjoint_inner_left]
      exact (Submodule.mem_orthogonal _ _).1 hy _
        (preserves_of_commute hW h2 (star b) (star_commute hb) u hu)
    obtain ⟨c, hc⟩ := exists_scalar_of_commute hW b hb hbW
    have hx : x ∈ W ⊔ Wᗮ := by
      rw [Submodule.sup_orthogonal_of_hasOrthogonalProjection]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    have hTz : T z = 0 := hT' hz
    have hTbz : T (b z) = 0 := hT' (hbW' z hz)
    have hTy : T y ∈ W := hT ⟨y, rfl⟩
    rw [map_add b, map_add T, map_add T, hTz, hTbz, hc y hy, map_smul, add_zero, add_zero, hc _ hTy]
  let f : Module.End (Module.End S E) E :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun b x => hcomm (b.restrictScalars ℂ)
        (fun a ha => LinearMap.ext fun y => b.map_smul ⟨a, ha⟩ y) x }
  let s : Finset E := Finset.univ.image (Module.finBasis ℂ E)
  obtain ⟨r, hr⟩ := jacobson_density f s
  have hTr : T = (r : E →ₗ[ℂ] E) :=
    (Module.finBasis ℂ E).ext fun i => hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  rw [hTr]
  exact r.2

end Corner

section Decomposition

/-- Restriction of `a ∈ S` to an `S`-invariant subspace commutes with taking adjoints. -/
theorem star_restrict {W : Submodule ℂ E} (a : E →ₗ[ℂ] E) (ha : ∀ x ∈ W, a x ∈ W)
    (ha' : ∀ x ∈ W, star a x ∈ W) : (star a).restrict ha' = star (a.restrict ha) := by
  change _ = LinearMap.adjoint _
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  simp only [Submodule.coe_inner, LinearMap.coe_restrict_apply]
  exact LinearMap.adjoint_inner_left a y x

/-- **Decomposition.** -/
theorem exists_decomposition' (S : StarSubalgebra ℂ (E →ₗ[ℂ] E)) :
    ∃ (m : ℕ) (W : Fin m → Submodule ℂ E), (∀ j, IsSimpleFor S (W j)) ∧
      ∑ j, finrank ℂ (W j) = finrank ℂ E ∧
      ∃ ρ : S →⋆ₐ[ℂ] ((j : Fin m) → (W j →ₗ[ℂ] W j)), Function.Injective ρ := by
  classical
  obtain ⟨s, hind, htop, hsimple⟩ := IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top S E
  have : IsNoetherian S E := isNoetherian_of_tower ℂ inferInstance
  have : Finite s := (WellFoundedGT.finite_of_sSupIndep hind).to_subtype
  obtain ⟨m, ⟨σ⟩⟩ := Finite.exists_equiv_fin s
  let p : Fin m → Submodule S E := fun j => (σ.symm j).1
  let W : Fin m → Submodule ℂ E := fun j => (p j).restrictScalars ℂ
  have hindS : iSupIndep p := ((sSupIndep_iff s).1 hind).comp σ.symm.injective
  have hindC : iSupIndep W := by
    intro j
    have h := (Submodule.disjoint_restrictScalars_iff (S := ℂ)).2 (hindS j)
    simp only [Submodule.restrictScalars_iSup] at h
    exact h
  have htopS : iSup p = ⊤ := by
    rw [← htop, sSup_eq_iSup']
    exact σ.symm.iSup_comp (g := fun x : s => (x : Submodule S E))
  have htopC : iSup W = ⊤ := by
    simp only [W, ← Submodule.restrictScalars_iSup, htopS, Submodule.restrictScalars_top]
  have hinv : ∀ j, Invariant S (W j) := fun j => invariant_restrictScalars S (p j)
  refine ⟨m, W, fun j => ?_, ?_, ?_⟩
  · have hat : IsAtom (p j) := (isSimpleModule_iff_isAtom).1 (hsimple _ (σ.symm j).2)
    refine ⟨?_, hinv j, fun U hU hUi => ?_⟩
    · simpa [W, Submodule.restrictScalars_eq_bot_iff] using hat.1
    · rcases (hat.le_iff).1 (show toSSubmodule S U hUi ≤ p j from hU) with h | h
      · left
        rw [← restrictScalars_toSSubmodule S U hUi, h, Submodule.restrictScalars_bot]
      · right
        rw [← restrictScalars_toSSubmodule S U hUi, h]
  · have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindC htopC
    rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hint).finrank_eq,
      Module.finrank_directSum]
  · let ρ : S →⋆ₐ[ℂ] ((j : Fin m) → (W j →ₗ[ℂ] W j)) :=
      { toFun := fun a j => (a : E →ₗ[ℂ] E).restrict (hinv j a a.2)
        map_one' := by ext j x; rfl
        map_mul' := by intro a b; ext j x; rfl
        map_zero' := by ext j x; rfl
        map_add' := by intro a b; ext j x; rfl
        commutes' := by intro c; ext j x; rfl
        map_star' := by
          intro a
          funext j
          exact star_restrict (a : E →ₗ[ℂ] E) _ _ }
    refine ⟨ρ, (injective_iff_map_eq_zero ρ).2 fun a ha => ?_⟩
    have hker : ∀ j, W j ≤ LinearMap.ker (a : E →ₗ[ℂ] E) := by
      intro j x hx
      have h := congrArg (fun f => ((f j ⟨x, hx⟩ : W j) : E)) ha
      exact h
    have h := iSup_le hker
    rw [htopC, top_le_iff, LinearMap.ker_eq_top] at h
    exact Subtype.ext h

end Decomposition

end Lax119563Proofs.Stabilization
