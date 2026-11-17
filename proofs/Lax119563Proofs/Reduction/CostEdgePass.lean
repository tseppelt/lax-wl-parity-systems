import Lax119563Proofs.Reduction.CostColPass

/-!
# Fits and cost of the edge passes and of the description

The edge passes run on the globals and the count level (`globTys ++ [big]`, depth `19`):
`hasCost_edgePass`. **`Gn.hasCost_descGen`**: `HasCost globTys (descGen M s ε 18) 1 21`.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Xp Ty Gn

variable {Γ : List Ty}

lemma hasCost_pairGen {uX nX : Xp} (hu : Tp Γ uX) (hn : Tp Γ nX) :
    HasCost Γ (pairGen uX nX) 0 0 := hasCost_seq (hasCost_emit' hu) (hasCost_emit' hn)

lemma hasCost_plainGen {s : ℕ} {uX labX FX iX vX : Xp} (hu : Tp Γ uX)
    (hn : Tp Γ (numX s labX FX iX vX)) : HasCost Γ (plainGen s uX labX FX iX vX) 0 0 :=
  hasCost_pairGen hu hn

lemma hasCost_coordGen {s ε : ℕ} {uX wX iX vX rX : Xp}
    (hc : Tp Γ (Xp.or (Xp.not (Xp.or (Xp.eq wX gacc) (Xp.eq wX gdet)))
      (Xp.eq (effX ε wX iX rX) (const 0))))
    (hu : Tp Γ uX) (hn : Tp Γ (numX s (effX ε wX iX rX) (add (add gENS (mulC 2 gE)) wX) iX vX)) :
    HasCost Γ (coordGen s ε uX wX iX vX rX) 0 0 :=
  hasCost_when' hc (hasCost_pairGen hu hn)

/-- The globals and the count level. -/
abbrev Γe : List Ty := globTys ++ [.big]

abbrev ΓeS : List Ty := Γe ++ schTys

lemma hasCost_schEnum_e {M : Machine} {s e d : ℕ} {body : Gn}
    (h : HasCost ΓeS body e d) :
    HasCost Γe (schEnum M s 19 gH gR gN gr gp0 gEc body) e (d + 12) :=
  hasCost_schEnum rfl (by tvb) (by tvb) ((show TyB Γe gN (P 0 5) by tvb).le ⟨le_rfl, by omega⟩)
    (by tvb) ((show TyB Γe gp0 (P 0 0) by tvb).le ⟨le_rfl, by omega⟩) (by tvb) h

lemma hasCost_violAt_e {s : ℕ} :
    HasCost (ΓeS ++ [P 0 0, P 0 0] ++ [P 1 0, P 1 0, P 0 0] ++ [P 0 0]) (violAt s 19 (19 + 37))
      0 1 :=
  hasCost_violGen rfl (by tvb) (by tvb) (hasTy_var _) (hasTy_var _) (by tvb) (hasTy_var_lin rfl)
    (by tvb) (by tvb) (hasTy_var' rfl)

lemma hasCost_violAt_es {s : ℕ} :
    HasCost (ΓeS ++ [P 0 0, P 0 0] ++ [P 0 1, P 0 1] ++ [P 0 0, P 0 0] ++ [P 1 0, P 1 0, P 0 0] ++
      [P 0 0]) (violAt s 19 (19 + 41)) 0 1 :=
  hasCost_violGen rfl (by tvb) (by tvb) (hasTy_var _) (hasTy_var _) (by tvb) (hasTy_var_lin rfl)
    (by tvb) (by tvb) (hasTy_var' rfl)

lemma hasCost_edgeJunc (M : Machine) (s ε : ℕ) : HasCost Γe (edgeJunc M s ε 19) 1 13 := by
  unfold edgeJunc schSlots
  refine hasCost_schEnum_e (hasCost_slotLoops (by tvb) hasCost_violAt_e ?_ le_rfl)
  unfold edgeJuncBody
  refine (hasCost_ite' ?_ (hasCost_seqL fun g hg => ?_) (hasCost_skip)).mono le_rfl (by omega)
  · tp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · refine hasCost_coordGen ?_ ?_ ?_ <;> tp
  · refine hasCost_coordGen ?_ ?_ ?_ <;> tp
  · refine hasCost_plainGen ?_ ?_ <;> tp

lemma hasCost_edgeLink (M : Machine) (s ε : ℕ) : HasCost Γe (edgeLink M s ε 19) 1 15 := by
  unfold edgeLink schSlots
  refine hasCost_schEnum_e (hasCost_slotLoops (by tvb) hasCost_violAt_e ?_ (by omega))
  unfold edgeLinkBody
  refine hasCost_ite' ?_ (hasCost_seq ?_ ?_) (hasCost_skip.mono (Nat.zero_le _) (Nat.zero_le _))
  · tp
  · refine (hasCost_coordGen ?_ ?_ ?_).mono le_rfl (Nat.zero_le _) <;> tp
  have hp := hasCost_prevGen (Γ := ΓeS ++ [P 0 0, P 0 0] ++ [P 1 0, P 1 0, P 0 0] ++ [P 0 2] ++
    [P 0 0, P 0 0] ++ [P 0 0]) (s := s) (D := 19 + 37 + 9) rfl (by tvb) (σX := gNS) (by tvb)
    (iX := var (19 + 37 + 1)) (by tvb) (vX := var (19 + 37 + 3)) (by tvb)
  refine hasCost_count (τ := P 0 3) (hp.mono le_rfl (by omega)) hp.len ?_
  refine (hasCost_bindSub (e₀ := 0) (d₀ := 3) (e := 0) (d := 0) rfl (hasTy_var' rfl)
    (show _ < List.length _ by decide) (hasTy_const 1) trivial ?_).mono (by simp) (by simp)
  refine hasCost_plainGen ?_ ?_ <;> tp

lemma hasCost_edgeUpd (M : Machine) (s ε : ℕ) : HasCost Γe (edgeUpd M s ε 19) 1 16 := by
  unfold edgeUpd stepSlots
  refine hasCost_schEnum_e (hasCost_stepLoops (by tvb)
    (hasCost_slotLoops (by tvb) hasCost_violAt_es ?_ (by omega)))
  unfold edgeUpdBody
  refine hasCost_ite' ?_ (hasCost_seq ?_ ?_) (hasCost_skip.mono (Nat.zero_le _) (Nat.zero_le _))
  · refine tp_and ?_ (tp_entX ?_ ?_ ?_) <;> tp
  · have hℓ : TyB (ΓeS ++ [P 0 0, P 0 0] ++ [P 0 1, P 0 1] ++ [P 0 0, P 0 0] ++
        [P 1 0, P 1 0, P 0 0] ++ [P 0 2] ++ [P 0 0, P 0 0] ++ [P 0 0]) gℓ (P 0 1) := by tvb
    have hσ : TyB (ΓeS ++ [P 0 0, P 0 0] ++ [P 0 1, P 0 1] ++ [P 0 0, P 0 0] ++
        [P 1 0, P 1 0, P 0 0] ++ [P 0 2] ++ [P 0 0, P 0 0] ++ [P 0 0]) (stepX s (19 + 37)) .big :=
      ⟨hasTy_addBig (hasTy_mulBBig (hasTy_var _) (hasTy_add (hasTy_lin_const s) hℓ.1)
        (hasTy_add (hasTy_lin_const s) hℓ.1)) (hasTy_var _),
        bnd_stepX (by decide) (by decide)⟩
    have hp := hasCost_prevGen (s := s) (D := 19 + 41 + 9) rfl hℓ hσ
      (iX := var (19 + 41 + 1)) (by tvb) (vX := var (19 + 41 + 3)) (by tvb)
    refine hasCost_count (τ := P 0 3) (hp.mono le_rfl (by omega)) hp.len ?_
    refine hasCost_ite' ?_ (hasCost_ite' ?_ ?_ ?_) ?_
    · tp
    · tp
    · refine (hasCost_plainGen ?_ ?_).mono le_rfl (Nat.zero_le _) <;> tp
    · refine (hasCost_coordGen ?_ ?_ ?_).mono le_rfl (Nat.zero_le _) <;> tp
    · refine (hasCost_bindSub (e₀ := 0) (d₀ := 3) (e := 0) (d := 0) rfl (hasTy_var' rfl)
        (show _ < List.length _ by decide) (hasTy_const 1) trivial ?_).mono (by simp) (by simp)
      refine hasCost_plainGen ?_ ?_ <;> tp
  · refine (hasCost_seq (hasCost_plainGen ?_ ?_) (hasCost_plainGen ?_ ?_)).mono le_rfl
      (Nat.zero_le _) <;> tp

/-- **Fits and cost of the edge passes.** -/
theorem hasCost_edgePass (M : Machine) (s ε : ℕ) : HasCost Γe (edgePass M s ε 19) 1 16 := by
  unfold edgePass
  refine hasCost_seqL fun g hg => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact hasCost_edgeUpd M s ε
  · exact (hasCost_edgeJunc M s ε).mono le_rfl (by omega)
  · exact (hasCost_edgeLink M s ε).mono le_rfl (by omega)

lemma tysLe_count (τ : Ty) : TysLe (globTys ++ [τ]) Γe :=
  TysLe.append (TysLe.refl globTys) (List.Forall₂.cons (Ty.le_big τ) List.Forall₂.nil)

/-- **Fits and cost of the description of an output graph.** -/
theorem Gn.hasCost_descGen (M : Machine) (s ε : ℕ) :
    HasCost globTys (descGen M s ε 18) 1 21 := by
  unfold descGen
  have hE := hasCost_edgePass M s ε
  have h0 := hE.ctx (tysLe_count (P 0 0))
  refine hasCost_seqL fun g hg => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact (hasCost_emit (hasTy_var 15)).mono (Nat.zero_le _) (Nat.zero_le _)
  · exact hasCost_colPass M s
  · refine (hasCost_count (τ := P 1 (16 + 1)) h0 h0.len
      (hasCost_seq ((hasCost_emit (hasTy_half (hasTy_var 18))).mono (Nat.zero_le _)
        (Nat.zero_le _)) (hE.ctx (tysLe_count _)))).mono le_rfl (by omega)

end Lax119563Proofs.Reduction
