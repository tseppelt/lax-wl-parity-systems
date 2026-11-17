import Lax119563Proofs.Reduction.CostPrelude
import Lax119563Proofs.Reduction.CostDom

/-!
# Classes of the globals

`globTys`: the growth classes of the 18 globals of `globs` (levels `0 … 17`), as computed by
the prelude: `|x|` and `2^ℓ` are linear in `|x|` (`P 1 0`), `log₂ |x|, ℓ, H, R, NS` are linear
in `ℓ` (`P 0 1`), the location and command counts are polylogarithmic, `nOut` is `big`.

`Xp.minR a b` (the minimum, of the class of `b` whatever the class of `a`) is used by the
prelude to compute `2^ℓ` in class `P 1 0`.
-/

namespace Lax119563Proofs.Reduction

open Xp Ty

/-- The classes of the globals (levels `0 … 17`). -/
def globTys : List Ty :=
  [P 1 0, P 0 1, P 0 1, P 0 1, P 0 1, P 0 5, P 0 7, P 0 7, P 0 0, P 0 0, P 0 20, P 0 1,
    P 0 20, P 0 21, P 0 21, .big, P 0 7, P 1 0]

lemma length_globTys : globTys.length = 18 := rfl

namespace Xp

/-- The minimum of `a` and `b`. -/
def minR (a b : Xp) : Xp :=
  add (mulB a (lt a b) (const 1)) (mulB b (Xp.not (lt a b)) (const 1))

lemma eval_minR (a b : Xp) (ρ : List ℕ) : (minR a b).eval ρ = min (a.eval ρ) (b.eval ρ) := by
  simp only [minR, eval, Xp.not]
  by_cases h : a.eval ρ < b.eval ρ
  · simp [h, min_eq_left h.le]
  · simp [h, min_eq_right (by omega : b.eval ρ ≤ a.eval ρ)]

/-- An expression whose value is bounded by that of a typed expression has its class. -/
lemma HasTy.of_eval_le {τs : List Ty} {a b : Xp} {τa τ : Ty} (ha : HasTy τs a τa)
    (hb : HasTy τs b τ) (h : ∀ ρ, a.eval ρ ≤ b.eval ρ) : HasTy τs a τ := by
  intro K₀
  obtain ⟨Ka, hKa⟩ := ha K₀
  obtain ⟨Kb, hKb⟩ := hb K₀
  refine ⟨Ka + Kb, fun ℓ ρ hA => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hKa ℓ ρ hA
  obtain ⟨b1, -, -⟩ := hKb ℓ ρ hA
  exact ⟨le_trans (h ρ) (le_trans b1 (Ty.bnd_mono (by omega) ℓ τ)),
    Fits.mono (two_pow_mono (by omega)) _ a2, le_trans a3 (Nat.mul_le_mul_right _ (by omega))⟩

lemma hasTy_minR {τs : List Ty} {a b : Xp} {τa τb : Ty} (ha : HasTy τs a τa)
    (hb : HasTy τs b τb) : HasTy τs (minR a b) τb := by
  have h1 : HasTy τs (const 1) (P 0 1) := (hasTy_const 1).le ⟨le_rfl, by omega⟩
  have hc : HasTy τs (lt a b) (P 0 0) := hasTy_lt ha hb
  have hbig : HasTy τs (minR a b) .big :=
    hasTy_addBig (hasTy_mulBBig ha hc h1) (hasTy_mulBBig hb (hasTy_not hc) h1)
  exact HasTy.of_eval_le hbig hb fun ρ => by rw [eval_minR]; exact min_le_right _ _

end Xp

end Lax119563Proofs.Reduction
