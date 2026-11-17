import Lax119563Proofs.Reduction.SysGen
import Lax119563Proofs.Reduction.CostPassBase

/-!
# Fits, cost and well-formedness of the system generator

**`hasCost_sysGen`**: `HasCost globTys (sysGen M s) 1 21`; **`wfx_sysGen`**.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Xp Ty Gn

variable {Γ : List Ty}

lemma hasCost_domLoops {s d : ℕ} {PX : Xp} {V body : Gn} (hP : TyB Γ PX (P 1 0))
    (hV : HasCost (Γ ++ [P 0 0, P 0 0] ++ [P 1 0, P 1 0, P 0 0] ++ [P 0 0]) V 0 1)
    (hb : HasCost (Γ ++ [P 0 0, P 0 0] ++ [P 1 0, P 1 0, P 0 0] ++ [P 0 2]) body 0 d)
    (hd : 1 ≤ d) :
    HasCost Γ (domLoops s PX V body) 1 d := by
  unfold domLoops
  have hc := hasCost_count (τ := P 0 2) (hV.mono le_rfl hd) hV.len hb
  have hx := hasCost_loopX (hP.weaken [P 0 0, P 0 0]).1 hc
  exact (hasCost_loop (hasTy_const (s + 1)) hx).mono (by simp) (by simp)

/-- The context of the schema body. -/
abbrev ΓS : List Ty := globTys ++ schTys

lemma length_ΓS : (ΓS).length = 51 := rfl

lemma hasCost_schEnum_c {M : Machine} {s e d : ℕ} {body : Gn}
    (h : HasCost ΓS body e d) :
    HasCost globTys (schEnum M s 14 gH gR gN gr gp0 gEc body) e (d + 12) :=
  hasCost_schEnum rfl (by tvb) (by tvb) ((show TyB globTys gN (P 0 5) by tvb).le ⟨le_rfl, by omega⟩)
    (by tvb) ((show TyB globTys gp0 (P 0 0) by tvb).le ⟨le_rfl, by omega⟩) (by tvb) h

lemma hasCost_violAt_d {s : ℕ} (τ : Ty) :
    HasCost (ΓS ++ [τ] ++ [P 0 0, P 0 0] ++ [P 1 0, P 1 0, P 0 0] ++ [P 0 0])
      (violAt s 14 (14 + 37 + 1)) 0 1 :=
  hasCost_violGen rfl ⟨hasTy_var _, by show _ < List.length _; simp [schTys, cmdTys, numTys, gdTys, recTys, globTys, digTys]⟩ ⟨hasTy_var _, by show _ < List.length _; simp [schTys, cmdTys, numTys, gdTys, recTys, globTys, digTys]⟩ (hasTy_var _) (hasTy_var _) ⟨hasTy_var _, by show _ < List.length _; simp [schTys, cmdTys, numTys, gdTys, recTys, globTys, digTys]⟩ (hasTy_var_lin rfl)
    ⟨hasTy_var _, by show _ < List.length _; simp [schTys, cmdTys, numTys, gdTys, recTys, globTys, digTys]⟩ ⟨hasTy_var _, by show _ < List.length _; simp [schTys, cmdTys, numTys, gdTys, recTys, globTys, digTys]⟩ (hasTy_var' rfl)

lemma hasCost_domGen (s : ℕ) : HasCost ΓS (domGen s 14 (14 + 37)) 1 1 := by
  unfold domGen
  have hd : HasCost (ΓS ++ [P 0 0]) (domLoops s gP (violAt s 14 (14 + 37 + 1))
      (domBody (14 + 37 + 1))) 1 1 := by
    refine hasCost_domLoops (by tvb) (hasCost_violAt_d _) ?_ le_rfl
    refine (hasCost_when' ?_ (hasCost_emit' ?_)).mono (Nat.zero_le _) (Nat.zero_le _) <;> tp
  refine hasCost_count hd hd.len ?_
  refine hasCost_seq ((hasCost_emit (hasTy_var _)).mono (Nat.zero_le _) (Nat.zero_le _)) ?_
  refine hasCost_domLoops (by tvb) (hasCost_violAt_d _) ?_ le_rfl
  unfold domBody' bitsGen
  refine hasCost_when' (by tp) (hasCost_seq ((hasCost_emit (hasTy_var _)).mono (Nat.zero_le _)
    (Nat.zero_le _)) ?_)
  exact (hasCost_loop (hasTy_var' rfl) (hasCost_emit' (by tp))).mono (by simp) (by simp)

lemma hasCost_permGen (s : ℕ) {mX : Xp} (hm : Tp (ΓS ++ [P 0 0, P 0 0] ++ [P 0 1, P 0 1]) mX) :
    HasCost ΓS (permGen s mX (14 + 37)) 0 1 := by
  unfold permGen bitsGen
  refine hasCost_seq ?_ ?_
  · exact (hasCost_loop (hasTy_const (s + 1)) (hasCost_emit (hasTy_var _))).mono (by simp)
      (by simp)
  · refine (hasCost_loop (hasTy_const (s + 1)) (hasCost_loop (hasTy_var' rfl)
      (hasCost_emit' ?_))).mono (by simp) (by simp)
    unfold shiftX fieldmX
    have hℓ : HasTy (ΓS ++ [P 0 0, P 0 0] ++ [P 0 1, P 0 1]) gℓ (P 0 1) := hasTy_var' rfl
    tp

lemma hasCost_schBody (s : ℕ) : HasCost ΓS (schBody s 14) 1 1 := by
  unfold schBody
  have hp : ∀ mX : Xp, Tp (ΓS ++ [P 0 0, P 0 0] ++ [P 0 1, P 0 1]) mX →
      HasCost ΓS (permGen s mX (14 + 37)) 1 1 := fun mX hm =>
    (hasCost_permGen s hm).mono (Nat.zero_le _) le_rfl
  have he : ∀ a : Xp, HasCost ΓS (emit a) 1 1 → HasCost ΓS (emit a) 1 1 := fun _ h => h
  refine hasCost_ite' (by tp) (hasCost_seqL fun g hg => ?_) (hasCost_seqL fun g hg => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact (hasCost_emit (hasTy_var _)).mono (Nat.zero_le _) (Nat.zero_le _)
      | exact (hasCost_emit (hasTy_const _)).mono (Nat.zero_le _) (Nat.zero_le _)
      | exact hasCost_domGen s
      | exact hp _ (tp_var _)
      | exact hp _ (tp_const _)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact (hasCost_emit (hasTy_var _)).mono (Nat.zero_le _) (Nat.zero_le _)
      | exact (hasCost_emit (hasTy_const _)).mono (Nat.zero_le _) (Nat.zero_le _)
      | exact hasCost_domGen s
      | exact hp _ (tp_var _)
      | exact hp _ (tp_const _)

lemma hasCost_locGen (s : ℕ) : HasCost globTys (locGen s 14) 1 21 := by
  unfold locGen
  refine (hasCost_loop (hasTy_var' (i := 11) (τ := P 0 20) rfl) (e := 1) (d := 1) ?_).mono
    (by omega) (by omega)
  refine hasCost_seqL fun g hg => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · refine (hasCost_emit' ?_).mono (Nat.zero_le _) (Nat.zero_le _)
    unfold initX; tp
  · refine (hasCost_emit' ?_).mono (Nat.zero_le _) (Nat.zero_le _)
    tp
  · unfold bitsGen
    refine (hasCost_loop (hasTy_const (s + 1)) (hasCost_loop (hasTy_var' rfl)
      (hasCost_seq ((hasCost_emit (hasTy_var _)).mono (Nat.zero_le _) (Nat.zero_le _))
        (hasCost_loop (hasTy_var' rfl) (hasCost_emit' (by tp)))))).mono (by simp) (by simp)

/-- **Fits and cost of the system generator.** -/
theorem hasCost_sysGen (M : Machine) (s : ℕ) : HasCost globTys (sysGen M s) 1 21 := by
  unfold sysGen
  refine hasCost_seqL fun g hg => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hasCost_emit (hasTy_const _)).mono (Nat.zero_le _) (Nat.zero_le _)
  · exact (hasCost_emit (hasTy_var _)).mono (Nat.zero_le _) (Nat.zero_le _)
  · exact (hasCost_emit (hasTy_var _)).mono (Nat.zero_le _) (Nat.zero_le _)
  · exact hasCost_locGen s
  · exact (hasCost_emit (hasTy_var _)).mono (Nat.zero_le _) (Nat.zero_le _)
  · exact (hasCost_schEnum_c (hasCost_schBody s)).mono le_rfl (by omega)

/-! ## Well-formedness -/

lemma noX_domBody (D : ℕ) : NoX (domBody D) := ⟨trivial, trivial⟩

lemma noX_domBody' (D : ℕ) : NoX (domBody' D) := ⟨⟨trivial, trivial⟩, trivial⟩

lemma wfx_domLoops (s : ℕ) (PX : Xp) {V body : Gn} (hV : NoX V) (hb : NoX body) :
    WFX (domLoops s PX V body) := ⟨⟨hV, hb⟩, wfx_of_noX (g := .count V body) ⟨hV, hb⟩⟩

lemma wfx_schBody (s b : ℕ) : WFX (schBody s b) := by
  have hd : WFX (domGen s b (b + 37)) :=
    cl_wfx.count (wfx_domLoops _ _ (noX_violAt ..) (noX_domBody _))
      (cl_wfx.seq trivial (wfx_domLoops _ _ (noX_violAt ..) (noX_domBody' _)))
  have hp : ∀ mX, WFX (permGen s mX (b + 37)) := fun _ => ⟨trivial, trivial⟩
  unfold schBody
  refine cl_wfx.ite _ (cl_wfx.seqL fun g hg => ?_) (cl_wfx.seqL fun g hg => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hd | exact hp _ | trivial
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hd | exact hp _ | trivial

/-- **The system generator is well formed.** -/
theorem wfx_sysGen (M : Machine) (s : ℕ) : WFX (sysGen M s) := by
  unfold sysGen
  refine cl_wfx.seqL fun g hg => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · trivial
  · trivial
  · trivial
  · exact cl_wfx.loop _ (cl_wfx.seqL fun g hg => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      · trivial
      · trivial
      · exact cl_wfx.loop _ (cl_wfx.loop _ ⟨trivial, trivial⟩))
  · trivial
  · exact cl_wfx.schEnum _ _ _ _ _ _ _ _ _ (wfx_schBody s 14)

end Lax119563Proofs.Reduction
