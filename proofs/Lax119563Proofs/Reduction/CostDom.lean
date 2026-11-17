import Lax119563Proofs.Reduction.CostSch
import Lax119563Proofs.Reduction.DomGen

/-!
# Fits and cost of the domain test

**`hasCost_violGen`**: on a context of length `d`, with a block index `iX` of class `P 0 0`,
linear `ℓX, HX, g1X, g2X` and arbitrary `vX, xbX, gkX, g3X` (all reading only the context),
the domain test has `HasCost Γ (violGen s d …) 0 1` (one loop over the field width `g2X`).
-/

namespace Lax119563Proofs.Reduction

open Xp Ty Gn

variable {Γ : List Ty}

lemma hasTy_mulCBig {a : Xp} {τ : Ty} (ha : HasTy Γ a τ) : ∀ c, HasTy Γ (mulC c a) .big
  | 0 => (hasTy_const 0).big
  | c + 1 => hasTy_addBig (hasTy_mulCBig ha c) ha

lemma hasTy_le {a b : Xp} {τa τb : Ty} (ha : HasTy Γ a τa) (hb : HasTy Γ b τb) :
    HasTy Γ (Xp.le a b) (P 0 0) := hasTy_not (hasTy_lt hb ha)

lemma hasTy_fieldX {iℓX ℓX HX : Xp} (hi : HasTy Γ iℓX (P 0 1)) (hℓ : HasTy Γ ℓX (P 0 1))
    (hH : HasTy Γ HX (P 0 1)) : HasTy Γ (fieldX iℓX ℓX HX) .big :=
  hasTy_xorM (hasTy_shr (hasTy_pow2 hH) hi) (hasTy_const 0) hℓ

lemma hasTy_fieldBadX {iℓX kX tX vX qX ℓX : Xp} {τv τq : Ty} (hi : HasTy Γ iℓX (P 0 1))
    (hk : HasTy Γ kX (P 0 1)) (ht : HasTy Γ tX (P 0 1)) (hv : HasTy Γ vX τv)
    (hq : HasTy Γ qX τq) (hℓ : HasTy Γ ℓX (P 0 1)) :
    HasTy Γ (fieldBadX iℓX kX tX vX qX ℓX) (P 0 0) := by
  have hkt : HasTy Γ (add kX tX) (P 0 1) := hasTy_add hk ht
  exact hasTy_and (hasTy_and (hasTy_le hi hkt) (hasTy_lt hkt (hasTy_add hi hℓ)))
    (hasTy_not (hasTy_eq (hasTy_odd (hasTy_shr (hasTy_shl hv hi) hkt))
      (hasTy_odd (hasTy_shr hq ht))))

/-- **Fits and cost of the domain test.** -/
theorem hasCost_violGen {s d : ℕ} (hd : Γ.length = d) {iX vX xbX gkX g1X g2X g3X ℓX HX : Xp}
    {τv τx τg τq : Ty} (hi : TyB Γ iX (P 0 0)) (hv : TyB Γ vX τv) (hx : HasTy Γ xbX τx)
    (hgk : HasTy Γ gkX τg) (hg1 : TyB Γ g1X (P 0 1)) (hg2 : HasTy Γ g2X (P 0 1))
    (hg3 : TyB Γ g3X τq) (hℓ : TyB Γ ℓX (P 0 1)) (hH : HasTy Γ HX (P 0 1)) :
    HasCost Γ (violGen s d iX vX xbX gkX g1X g2X g3X ℓX HX) 0 1 := by
  subst hd
  have hi1 : HasTy Γ iX (P 0 1) := hi.1.le ⟨le_rfl, by omega⟩
  have hiℓ : TyB Γ (mul ℓX iX) (P 0 1) :=
    ⟨by simpa using hasTy_mul hℓ.1 hi.1 hi1, Xp.bnd_mul hℓ.2 hi.2⟩
  have hf := hasTy_fieldX hiℓ.1 hℓ.1 hH
  have e0 : ∀ {Δ : List Ty}, HasCost Δ (emit (const 0)) 0 1 :=
    (hasCost_emit (hasTy_const 0)).mono le_rfl (by omega)
  -- the loop over the field
  have W : ∀ {a : Xp} {τ : Ty}, TyB Γ a τ → HasTy (Γ ++ [P 0 1, P 0 1]) a τ :=
    fun h => (h.weaken _).1
  have ht : HasTy (Γ ++ [P 0 1, P 0 1]) (var (Γ.length + 1)) (P 0 1) :=
    hasTy_var' (by rw [List.getD_append_right _ _ _ _ (by omega)]; simp)
  have hloop : HasCost Γ (.loop g2X (when (fieldBadX (mul ℓX iX) g1X (var (Γ.length + 1)) vX g3X
      ℓX) (emit (const 0)))) 0 1 :=
    (hasCost_loop hg2 (hasCost_when (hasTy_fieldBadX (W hiℓ) (W hg1) ht (W hv) (W hg3) (W hℓ))
      (hasCost_emit (hasTy_const 0)))).mono le_rfl (by omega)
  have hinit : HasTy Γ (initCVX g1X vX xbX) .big :=
    hasTy_addBig (hasTy_eq hv.1 (hasTy_const 0))
      (hasTy_mulCBig (hasTy_mulBBig hx (hasTy_eq hg1.1 (hasTy_const 0))
        ((hasTy_eq hg1.1 (hasTy_const 0)).le ⟨le_rfl, by omega⟩)) 2)
  refine hasCost_when (hasTy_not (hasTy_eq hi.1 (hasTy_const s))) ?_
  refine hasCost_ite (hasTy_eq hgk (hasTy_const 0)) hloop ?_
  refine hasCost_ite (hasTy_eq hgk (hasTy_const 1)) (hasCost_when (τ := P 0 0) ?_ e0) ?_
  · exact hasTy_not (hasTy_or (hasTy_and (hasTy_eq hi.1 (hasTy_const 0))
      (hasTy_eq hinit hg2)) (hasTy_and (hasTy_not (hasTy_eq hi.1 (hasTy_const 0)))
        (hasTy_eq hv.1 hf)))
  refine hasCost_ite (hasTy_eq hgk (hasTy_const 2)) (hasCost_when (τ := P 0 0) ?_ e0)
    (hasCost_when (hasTy_not (hasTy_eq hv.1 (hasTy_const 0))) e0)
  exact hasTy_not (hasTy_or (hasTy_not (hasTy_eq hi.1 hg1.1)) (hasTy_not (hasTy_eq hv.1 hf)))

end Lax119563Proofs.Reduction
