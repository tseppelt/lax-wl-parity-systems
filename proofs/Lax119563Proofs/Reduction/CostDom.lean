import Lax119563Proofs.Reduction.CostSch
import Lax119563Proofs.Reduction.DomGen

/-!
# Classes of the domain test expressions

Typing lemmas for the expressions of the domain test: `hasTy_mulCBig`, `hasTy_le`,
`hasTy_fieldX`, `hasTy_fieldBadX`.
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

end Lax119563Proofs.Reduction
