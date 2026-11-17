import Lax119563Proofs.Reduction.CostPassBase

/-!
# Fits and cost of the colour pass

**`hasCost_colPass`**: on the globals (`globTys`, depth `18`), the colour pass has
`HasCost globTys (colPass M s 18) 1 21`.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Xp Ty Gn

variable {Γ : List Ty}

lemma tp_colX {s : ℕ} {FX iX vX : Xp} (hℓ : HasTy Γ gℓ (P 0 1)) (hF : Tp Γ FX) (hi : Tp Γ iX)
    (hv : Tp Γ vX) : Tp Γ (colX s FX iX vX) :=
  tp_add (tp_mulC (tp_add (tp_shl (tp_add hi (tp_mulC hF _)) hℓ) hv) 2) (tp_const 2)

lemma hasCost_colBody {s : ℕ} {validX FX iX vX : Xp} (hval : Tp Γ validX)
    (hc : Tp Γ (colX s FX iX vX)) : HasCost Γ (colBody s validX FX iX vX) 0 0 :=
  hasCost_ite' hval (hasCost_emit' hc) (hasCost_emit' (tp_const 1))

/-- The schema stack and the slot loops on top of `globTys`. -/
abbrev ΓcS : List Ty := globTys ++ schTys

lemma hasCost_violAt_c {s : ℕ} :
    HasCost (ΓcS ++ [P 0 0, P 0 0] ++ [P 1 0, P 1 0, P 0 0] ++ [P 0 0]) (violAt s 18 (18 + 37))
      0 1 :=
  hasCost_violGen rfl (by tvb) (by tvb) (hasTy_var _) (hasTy_var _) (by tvb) (hasTy_var_lin rfl)
    (by tvb) (by tvb) (hasTy_var' rfl)

lemma hasCost_violAt_cs {s : ℕ} :
    HasCost (ΓcS ++ [P 0 0, P 0 0] ++ [P 0 1, P 0 1] ++ [P 0 0, P 0 0] ++ [P 1 0, P 1 0, P 0 0] ++
      [P 0 0]) (violAt s 18 (18 + 41)) 0 1 :=
  hasCost_violGen rfl (by tvb) (by tvb) (hasTy_var _) (hasTy_var _) (by tvb) (hasTy_var_lin rfl)
    (by tvb) (by tvb) (hasTy_var' rfl)

lemma hasCost_schEnum_c {M : Machine} {s e d : ℕ} {body : Gn}
    (h : HasCost ΓcS body e d) :
    HasCost globTys (schEnum M s 18 gH gR gN gr gp0 gEc body) e (d + 12) :=
  hasCost_schEnum rfl (by tvb) (by tvb) ((show TyB globTys gN (P 0 5) by tvb).le ⟨le_rfl, by omega⟩)
    (by tvb) ((show TyB globTys gp0 (P 0 0) by tvb).le ⟨le_rfl, by omega⟩) (by tvb) h

lemma hasCost_colSch (M : Machine) (s : ℕ) {off validX : Xp}
    (hoff : Tp (ΓcS ++ [P 0 0, P 0 0] ++ [P 1 0, P 1 0, P 0 0] ++ [P 0 2] ++ [P 0 0, P 0 0]) off)
    (hval : Tp (ΓcS ++ [P 0 0, P 0 0] ++ [P 1 0, P 1 0, P 0 0] ++ [P 0 2] ++ [P 0 0, P 0 0])
      validX) :
    HasCost globTys (colSch M s 18 off validX) 1 13 := by
  unfold colSch
  refine hasCost_schEnum_c (hasCost_slotLoops (by tvb) hasCost_violAt_c ?_ le_rfl)
  exact (hasCost_colBody hval (tp_colX (hasTy_var' rfl) (tp_add hoff (tp_var _)) (tp_var _)
    (tp_var _))).mono le_rfl (Nat.zero_le _)

lemma hasCost_colStep (M : Machine) (s : ℕ) {off validX : Xp}
    (hoff : Tp (ΓcS ++ [P 0 0, P 0 0] ++ [P 0 1, P 0 1] ++ [P 0 0, P 0 0] ++
      [P 1 0, P 1 0, P 0 0] ++ [P 0 2] ++ [P 0 0, P 0 0]) off)
    (hval : Tp (ΓcS ++ [P 0 0, P 0 0] ++ [P 0 1, P 0 1] ++ [P 0 0, P 0 0] ++
      [P 1 0, P 1 0, P 0 0] ++ [P 0 2] ++ [P 0 0, P 0 0]) validX) :
    HasCost globTys (colStep M s 18 off validX) 1 14 := by
  unfold colStep
  refine hasCost_schEnum_c (hasCost_stepLoops (by tvb)
    (hasCost_slotLoops (by tvb) hasCost_violAt_cs ?_ le_rfl))
  refine (hasCost_colBody hval (tp_colX (hasTy_var' rfl) ?_ (tp_var _) (tp_var _))).mono le_rfl
    (Nat.zero_le _)
  exact tp_add hoff (tp_add (tp_mul (tp_var _) (hasTy_var' rfl))
    (tp_add (tp_mul (tp_var _) (hasTy_add (hasTy_lin_const s) (hasTy_var' rfl))) (tp_var _)))

lemma hasCost_colCoord (s : ℕ) : HasCost globTys (colCoord s 18) 1 21 := by
  unfold colCoord
  refine (hasCost_loop (τs := globTys) (hasTy_var' (i := 12) (τ := P 0 20) rfl) (e := 1) (d := 1)
    ?_).mono (by omega) (by omega)
  refine hasCost_slotLoops (by tvb) (hasCost_skip.mono (Nat.zero_le _) (by omega)) ?_ le_rfl
  refine (hasCost_colBody ?_ (tp_colX ?_ ?_ (tp_var _) (tp_var _))).mono le_rfl (Nat.zero_le _)
  · tp
  · exact hasTy_var' rfl
  · tp

/-- **Fits and cost of the colour pass.** -/
theorem hasCost_colPass (M : Machine) (s : ℕ) : HasCost globTys (colPass M s 18) 1 21 := by
  unfold colPass
  refine hasCost_seqL fun g hg => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  have hent : ∀ {Δ : List Ty} {j i v : ℕ}, Δ.getD j (P 0 0) = P 0 1 →
      Tp Δ (entX s (var j) (var i) (var v)) :=
    fun h => tp_entX (hasTy_var' h) (tp_var _) (tp_var _)
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hasCost_colStep M s (by tp) (tp_and (by tp) (hent rfl))).mono le_rfl (by omega)
  · exact (hasCost_colSch M s (by tp) (by tp)).mono le_rfl (by omega)
  · exact (hasCost_colSch M s (by tp) (by tp)).mono le_rfl (by omega)
  · exact hasCost_colCoord s
  · exact (hasCost_colSch M s (by tp) (by tp)).mono le_rfl (by omega)
  · exact (hasCost_colStep M s (by tp) (tp_and (tp_and (by tp) (hent rfl)) (by tp))).mono le_rfl
      (by omega)
  · exact (hasCost_colStep M s (by tp) (by tp)).mono le_rfl (by omega)

end Lax119563Proofs.Reduction
