import Lax119563Proofs.Reduction.PkPre
import Lax119563Proofs.Reduction.CostSys

/-!
# Fits and cost of the packed enumerators

As `CostCmd`, `CostSch` for `cmdEnumP`, `cmdBodyP`, `schEnumP` (two-scale growth classes,
`CostTy`): **`hasCost_cmdEnumP`** (`d + 6`) and **`hasCost_schEnumP`** (`d + 12`), with the
number of blocks `SX` linear.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Xp Ty Gn

variable {M : Machine}

/-- The classes of the digits, differences and `rest` (levels `b, …, b + 12`). -/
def digTysP : List Ty := List.replicate 12 (P 0 1) ++ [P 0 5]

/-- The classes of the levels `b, …, b + 24` of the body of `cmdEnumP`. -/
def cmdTysP : List Ty := digTysP ++ [P 0 1, P 0 1] ++ [P 0 5] ++ P 0 1 :: recTys

lemma len_cmdTysP : cmdTysP.length = 25 := rfl

variable {Γ : List Ty}

lemma matchXP_ty {τs : List Ty} {HX RX : Xp} (hH : LinX τs HX) (hR : LinX τs RX) (K : SKind M) :
    TyB (τs ++ digTysP) (matchXP M τs.length HX RX K) (P 0 0) := by
  have hH' : LinX (τs ++ digTysP) HX := hH.weaken _
  have hR' : LinX (τs ++ digTysP) RX := hR.weaken _
  have v7 : LinX (τs ++ digTysP) (var (τs.length + 7)) := tyB_var _ rfl (by simp [digTysP])
  have v3 : LinX (τs ++ digTysP) (var (τs.length + 3)) := tyB_var _ rfl (by simp [digTysP])
  have v12 : TyB (τs ++ digTysP) (var (τs.length + 12)) (P 0 5) :=
    tyB_var _ rfl (by simp [digTysP])
  have hc := SLoc.codeX_tyB hR' hH' (SKind.sloc_ok v7 v3 K)
  have hv : ∃ τ, TyB (τs ++ digTysP) (validXP M τs.length HX K) τ := by
    cases K
    all_goals first
      | exact ⟨_, tyB_const 1⟩
      | exact ⟨_, tyB_lt v7 (linX_add_const hH' 1)⟩
      | exact ⟨_, tyB_and (tyB_lt v7 (linX_add_const hH' 1)) (tyB_lt v3 (linX_add_const hH' 1))⟩
  obtain ⟨τ, hv⟩ := hv
  have hm := tyB_mulC v12 16
  exact tyB_and (tyB_eq hc ⟨hasTy_add ((hasTy_const _).le ⟨le_rfl, by omega⟩) hm.1,
    trivial, hm.2⟩) hv

lemma hasCost_kindGenP {τs : List Ty} {SX HX RX : Xp} (hS : LinX τs SX) (hH : LinX τs HX)
    (hR : LinX τs RX) {body : Gn} {e d : ℕ} (hbody : HasCost (τs ++ cmdTysP) body e d)
    (K : SKind M) :
    HasCost (τs ++ digTysP) (kindGenP M τs.length SX HX RX body K) e (d + 1) := by
  set ΓL := τs ++ digTysP ++ [P 0 1, P 0 1] ++ [P 0 5] with hΓL
  have hHL : LinX ΓL HX := by
    rw [hΓL]; simpa using hH.weaken (digTysP ++ [P 0 1, P 0 1] ++ [P 0 5])
  have hRL : LinX ΓL RX := by
    rw [hΓL]; simpa using hR.weaken (digTysP ++ [P 0 1, P 0 1] ++ [P 0 5])
  have vL : ∀ j, j < 12 → LinX ΓL (var (τs.length + j)) := fun j hj => by
    have := tyB_var (Γ := τs) (digTysP ++ [P 0 1, P 0 1] ++ [P 0 5]) (j := j) (τ := P 0 1)
      (by simp only [digTysP]; interval_cases j <;> rfl) (by simp [digTysP]; omega)
    simpa [hΓL] using this
  have v14 : LinX ΓL (var (τs.length + 14)) := by
    have := tyB_var (Γ := τs) (digTysP ++ [P 0 1, P 0 1] ++ [P 0 5]) (j := 14) (τ := P 0 1)
      rfl (by simp [digTysP])
    simpa [hΓL] using this
  have hV : (rvP τs.length HX).Lin ΓL :=
    ⟨vL 7 (by omega), vL 3 (by omega), vL 8 (by omega), vL 9 (by omega), vL 10 (by omega),
      vL 11 (by omega), hHL⟩
  have hb1 : HasCost (ΓL ++ P 0 1 :: recTys) body e d := by
    simpa [hΓL, cmdTysP] using hbody
  have hb0 : HasCost (ΓL ++ P 0 0 :: recTys) body e d :=
    hb1.ctx (TysLe.append (TysLe.refl ΓL) (List.Forall₂.cons (show Ty.Le (P 0 0) (P 0 1) from ⟨le_rfl, Nat.zero_le _⟩)
      (TysLe.refl recTys)))
  have hbr : HasCost ΓL (Gn.brGen RX HX body (K.brs (s := 0) (rvP τs.length HX))) e d :=
    Gn.hasCost_brGen hRL hHL hb0 _ (SKind.brs_ok hV K)
  have hmiss : HasCost ΓL (missGen M τs.length HX RX body K) e d := by
    unfold missGen
    split_ifs
    · refine hasCost_when (hasTy_and (hasTy_not (hasTy_eq v14.1 (hasTy_const 0)))
        (hasTy_eq (vL 7 (by omega)).1 (hasTy_const 0))) ?_
      have hT : TyL (ΓL ++ []) (missRecX M τs.length HX RX) (P 0 1 :: recTys) := by
        refine tyL_of_forall₂ ?_ []
        simp only [missRecX, recTys]
        have hc := SLoc.codeX_tyB (M := M) hRL hHL (L := SLoc.accept) trivial
        exact .cons v14 (.cons (tyB_const 0) (.cons ((tyB_const 0).le (Ty.le_big _))
          (.cons hc (.cons ((tyB_const 0).le ⟨le_rfl, by omega⟩) (.cons (tyB_const 2)
          (.cons v14 (.cons (tyB_const 0) (.cons (tyB_const 0) .nil))))))))
      exact hasCost_bindL (by simpa using hT) hb1
    · exact hasCost_skip.mono (Nat.zero_le _) (Nat.zero_le _)
  have vC : TyB (τs ++ digTysP ++ [P 0 1, P 0 1]) ((K.sloc (var (τs.length + 7))
      (var (τs.length + 3))).codeX RX HX) (P 0 5) := by
    have w : ∀ j, j < 12 → LinX (τs ++ digTysP ++ [P 0 1, P 0 1]) (var (τs.length + j)) :=
      fun j hj => by
        have := tyB_var (Γ := τs) (digTysP ++ [P 0 1, P 0 1]) (j := j) (τ := P 0 1)
          (by simp only [digTysP]; interval_cases j <;> rfl) (by simp [digTysP]; omega)
        simpa using this
    exact SLoc.codeX_tyB ((hR.weaken _).weaken _) ((hH.weaken _).weaken _)
      (SKind.sloc_ok (w 7 (by omega)) (w 3 (by omega)) K)
  have hloopBody : HasCost (τs ++ digTysP ++ [P 0 1, P 0 1])
      (.bind ((K.sloc (var (τs.length + 7)) (var (τs.length + 3))).codeX RX HX)
        (.seq (Gn.when (eq (var (τs.length + 14)) (const 0))
          (Gn.brGen RX HX body (K.brs (s := 0) (rvP τs.length HX))))
          (missGen M τs.length HX RX body K))) e d :=
    hasCost_bind vC.1 (hasCost_seq (hasCost_when (hasTy_eq v14.1 (hasTy_const 0)) hbr) hmiss)
  have := hasCost_loop (hS.weaken digTysP).1 (by simpa using hloopBody)
  exact this.mono (by simp) (by omega)

lemma restXP_ty {τs : List Ty} {RX : Xp} (hR : LinX τs RX) :
    TyB (τs ++ List.replicate 12 (P 0 1)) (restXP (cM M) τs.length RX) (P 0 5) := by
  have hR' : LinX (τs ++ List.replicate 12 (P 0 1)) RX := hR.weaken _
  have v : ∀ j, j < 12 → LinX (τs ++ List.replicate 12 (P 0 1)) (var (τs.length + j)) :=
    fun j hj => tyB_var _ (by interval_cases j <;> rfl) (by simp [hj])
  have t4 := tyB_horner (v 3 (by omega)) (v 1 (by omega)) hR' le_rfl
  have t3 := tyB_hornerC (v 5 (by omega)) t4 (cM M * cM M) (by omega)
  exact (tyB_horner (v 7 (by omega)) t3 hR' (by omega)).le ⟨le_rfl, by omega⟩

/-- **Fits and cost of the packed command enumerator.** -/
theorem hasCost_cmdEnumP {τs : List Ty} {b : ℕ} (hb : τs.length = b) {SX HX RX : Xp}
    (hS : LinX τs SX) (hH : LinX τs HX) (hR : LinX τs RX) {body : Gn} {e d : ℕ}
    (hbody : HasCost (τs ++ cmdTysP) body e d) :
    HasCost τs (cmdEnumP M b SX HX RX body) e (d + 6) := by
  subst hb
  have hT : HasCost (τs ++ digTysP) (tupleGenP M τs.length SX HX RX body) e (d + 1) := by
    refine hasCost_seqL fun g hg => ?_
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hg
    exact Gn.hasCost_firstL (fun K _ => ⟨_, (matchXP_ty hH hR K).1⟩) fun K _ =>
      hasCost_kindGenP hS hH hR hbody K
  have h12 : HasCost (τs ++ List.replicate 12 (P 0 1)) (.bind (restXP (cM M) τs.length RX)
      (tupleGenP M τs.length SX HX RX body)) e (d + 1) :=
    hasCost_bind (restXP_ty (M := M) hR).1 (by simpa [digTysP] using hT)
  have vr : ∀ {k j : ℕ}, j < k → LinX (τs ++ List.replicate k (P 0 1)) (var (τs.length + j)) :=
    fun {k j} hj => tyB_var _ (by simp [hj]) (by simp [hj])
  have bd : ∀ {k : ℕ} {a : Xp} {τ : Ty}, TyB (τs ++ List.replicate k (P 0 1)) a τ →
      a.Bnd (τs.length + k) := fun h => by simpa using h.2
  have Hw : ∀ k, LinX (τs ++ List.replicate k (P 0 1)) HX := fun k => hH.weaken _
  have c1 : ∀ k, TyB (τs ++ List.replicate k (P 0 1)) (const 1) (P 0 0) := fun k => tyB_const 1
  have step : ∀ {k : ℕ} {x y : Xp} {τ : Ty} {g : Gn},
      LinX (τs ++ List.replicate k (P 0 1)) x → TyB (τs ++ List.replicate k (P 0 1)) y τ →
      HasCost (τs ++ List.replicate (k + 1) (P 0 1)) g e (d + 1) →
      HasCost (τs ++ List.replicate k (P 0 1)) (bindSub (τs.length + k) x y g) e (d + 1) := by
    intro k x y τ g hx hy hg
    have := hasCost_bindSub (τs := τs ++ List.replicate k (P 0 1)) (n := τs.length + k)
      (by simp) hx.1 (bd hx) hy.1 (bd hy)
      (by rw [List.append_assoc, ← List.replicate_succ']; exact hg)
    exact this.mono (by simp) (by omega)
  have h11 := step (k := 11) (linX_add_const (Hw 11) 2) (vr (by omega : 7 < 11)) h12
  have h10 := step (k := 10) (Hw 10) (linX_add_const (vr (by omega : 7 < 10)) 1) h11
  have h9 := step (k := 9) (vr (by omega : 3 < 9)) (c1 9) h10
  have h8 := step (k := 8) (vr (by omega : 7 < 8)) (c1 8) h9
  have R : ∀ l : List Ty, HasTy (τs ++ l) RX (P 0 1) := fun l => (hR.weaken l).1
  have g4 := hasCost_loop' (R [P 0 1, P 0 1, P 0 1, P 0 1, P 0 1, P 0 1]) h8
  have Cc : ∀ (c : ℕ) (l : List Ty), HasTy (τs ++ l) (const c) (P 0 1) := fun c l =>
    (hasTy_const _).le ⟨le_rfl, by omega⟩
  have g3 := hasCost_loop' (Cc (cM M * cM M) [P 0 1, P 0 1, P 0 1, P 0 1]) g4
  have g2 := hasCost_loop' (R [P 0 1, P 0 1]) g3
  have g1 := hasCost_loop' (Cc (cM M) []) g2
  rw [List.append_nil] at g1
  exact g1.mono (by simp) (by omega)

/-! ## The schema enumerator -/

/-- The classes of the levels `b, …, b + 36` of the body of `schEnumP`. -/
def schTysP : List Ty := cmdTysP ++ [P 0 7, P 0 7] ++ P 0 7 :: (numTys ++ gdTys)

theorem hasCost_cmdBodyP {τs : List Ty} {SX HX RX NX : Xp} (hS : LinX τs SX) (hH : LinX τs HX)
    (hR : LinX τs RX) (hN : TyB τs NX (P 0 7)) {body : Gn} {e d : ℕ}
    (hbody : HasCost (τs ++ schTysP) body e d) :
    HasCost (τs ++ cmdTysP) (cmdBodyP M τs.length SX HX RX NX body) e (d + 6) := by
  have hbd : HasCost (τs ++ schTysP) body e (d + 6) := hbody.mono le_rfl (by omega)
  have G1 : HasCost (τs ++ cmdTysP ++ [P 0 0])
      (cmdEnumP M (τs.length + 26) SX HX RX (when (beforeX τs.length (τs.length + 26))
        (emit (const 0)))) 0 6 :=
    hasCost_cmdEnumP (τs := τs ++ cmdTysP ++ [P 0 0]) (by simp [len_cmdTysP])
      ((hS.weaken cmdTysP).weaken [P 0 0]) ((hH.weaken cmdTysP).weaken [P 0 0])
      ((hR.weaken cmdTysP).weaken [P 0 0])
      (hasCost_when (hasTy_beforeX _ _) (hasCost_emit (hasTy_const 0)))
  have G2 : HasCost (τs ++ cmdTysP ++ [P 0 7] ++ [P 0 0])
      (cmdEnumP M (τs.length + 27) SX HX RX (when (beforeX τs.length (τs.length + 27))
        (ite (var (τs.length + 27 + 17)) (emitN 9) (emitN 4)))) 0 6 :=
    hasCost_cmdEnumP (τs := τs ++ cmdTysP ++ [P 0 7] ++ [P 0 0]) (by simp [len_cmdTysP])
      (((hS.weaken cmdTysP).weaken [P 0 7]).weaken [P 0 0])
      (((hH.weaken cmdTysP).weaken [P 0 7]).weaken [P 0 0])
      (((hR.weaken cmdTysP).weaken [P 0 7]).weaken [P 0 0])
      (hasCost_when (hasTy_beforeX _ _) (hasCost_ite (hasTy_var _) (hasCost_emitN 9)
        (hasCost_emitN 4)))
  set Γ := τs ++ (cmdTysP ++ [P 0 7, P 0 7]) with hΓ
  have hNw : TyB Γ NX (P 0 7) := hN.weaken _
  have v25 : TyB Γ (var (τs.length + 25)) (P 0 7) :=
    tyB_get rfl (by simp [len_cmdTysP]) (Ty.Le.refl _)
  have v26 : TyB Γ (var (τs.length + 26)) (P 0 7) :=
    tyB_get rfl (by simp [len_cmdTysP]) (Ty.Le.refl _)
  have v15 : TyB Γ (var (τs.length + 15)) (P 0 7) :=
    tyB_get rfl (by simp [len_cmdTysP]) ⟨le_rfl, by omega⟩
  have v19 : TyB Γ (var (τs.length + 19)) (P 0 7) :=
    tyB_get rfl (by simp [len_cmdTysP]) ⟨le_rfl, by omega⟩
  have v20 : TyB Γ (var (τs.length + 20)) (P 0 7) :=
    tyB_get rfl (by simp [len_cmdTysP]) ⟨le_rfl, by omega⟩
  have v18 : TyB Γ (var (τs.length + 18)) .big := tyB_get rfl (by simp [len_cmdTysP]) trivial
  have hslot : ∀ t, TyB Γ (slotX NX τs.length t) (P 0 7) := fun t =>
    ⟨hasTy_add hNw.1 (hasTy_add ((hasTy_const t).le ⟨le_rfl, by omega⟩) (hasTy_mulC v25.1 8)),
      hNw.2, trivial, Xp.bnd_mulC v25.2 8⟩
  have hgd : TyBs Γ (gdX τs.length) gdTys := by
    simp only [gdX, gdTys]
    exact .cons (tyB_get rfl (by simp [len_cmdTysP]) (Ty.Le.refl _))
      (.cons (tyB_get rfl (by simp [len_cmdTysP]) (Ty.Le.refl _))
      (.cons (tyB_get rfl (by simp [len_cmdTysP]) (Ty.Le.refl _))
      (.cons (tyB_get rfl (by simp [len_cmdTysP]) (Ty.Le.refl _)) .nil)))
  have hB : HasCost (Γ ++ P 0 7 :: (numTys ++ gdTys)) body e (d + 6) := by
    simpa [hΓ, schTysP] using hbd
  have hfork : ∀ l ∈ forkBlk NX τs.length, TyBs Γ l numTys := by
    intro l hl
    simp only [forkBlk, List.mem_append, List.mem_singleton] at hl
    rcases hl with (hl | hl) | rfl
    · exact gadgetX_ty v19 ((tyB_const 0).le (Ty.le_big _)) (hslot 0) (hslot 1) (hslot 2)
        (hslot 6) l hl
    · exact gadgetX_ty v20 ((tyB_const 0).le (Ty.le_big _)) (hslot 3) (hslot 4) (hslot 5)
        (hslot 7) l hl
    · exact .cons (tyB_const 1) (.cons (hslot 6) (.cons (hslot 7) (.cons v15
        (.cons ((tyB_const 0).le (Ty.le_big _)) .nil))))
  have hassign : ∀ l ∈ assignBlk NX τs.length, TyBs Γ l numTys :=
    gadgetX_ty v19 v18 (hslot 0) (hslot 1) (hslot 2) v15
  have G3 : HasCost Γ (ite (var (τs.length + 17))
      (blkGen (var (τs.length + 26)) (gdX τs.length) body (forkBlk NX τs.length))
      (blkGen (var (τs.length + 26)) (gdX τs.length) body (assignBlk NX τs.length))) e (d + 6) :=
    hasCost_ite (hasTy_var _) (hasCost_blkGen v26 hgd hfork hB)
      (hasCost_blkGen v26 hgd hassign hB)
  have G3' : HasCost (τs ++ cmdTysP ++ [P 0 7] ++ [P 0 7]) (ite (var (τs.length + 17))
      (blkGen (var (τs.length + 26)) (gdX τs.length) body (forkBlk NX τs.length))
      (blkGen (var (τs.length + 26)) (gdX τs.length) body (assignBlk NX τs.length))) e
        (d + 6) := by
    rw [List.append_assoc, List.append_assoc]; exact G3
  have C2 := hasCost_count (G2.mono (Nat.zero_le e) (by omega)) G2.len G3'
  exact hasCost_count (G1.mono (Nat.zero_le e) (by omega)) G1.len C2

theorem hasCost_detGenP {τs : List Ty} {NX rX p0X EcX : Xp} (hN : TyB τs NX (P 0 7))
    (hr : TyB τs rX (P 0 7)) (hp : TyB τs p0X (P 0 7)) (hE : TyB τs EcX (P 0 7))
    {body : Gn} {e d : ℕ} (hbody : HasCost (τs ++ schTysP) body e d) :
    HasCost τs (detGen NX rX p0X EcX body) e d := by
  set Γ := τs ++ List.replicate 27 (P 0 0) with hΓ
  have hdet : ∀ t, TyB Γ (detX NX rX t) (P 0 7) := fun t =>
    ⟨hasTy_add (hasTy_add (hN.weaken _).1 (hasTy_mulC (hr.weaken _).1 8))
      ((hasTy_const t).le ⟨le_rfl, by omega⟩),
      ⟨(hN.weaken _).2, Xp.bnd_mulC (hr.weaken _).2 8⟩, trivial⟩
  have hgd : TyBs Γ [const 3, const 0, const 0, const 0] gdTys :=
    .cons (tyB_const 3) (.cons (linX_const 0) (.cons (tyB_const 0) (.cons (tyB_const 0) .nil)))
  have hle : TysLe (Γ ++ P 0 7 :: (numTys ++ gdTys)) (τs ++ schTysP) := by
    rw [hΓ, List.append_assoc]
    refine TysLe.append (TysLe.refl τs) ?_
    simp [TysLe, schTysP, cmdTysP, digTysP, recTys, numTys, gdTys, List.replicate_succ, Ty.Le]
  refine hasCost_bindL (ts := List.replicate 27 (P 0 0)) (by simpa using tyL_zeros 27 τs) ?_
  exact hasCost_blkGen (hE.weaken _) hgd
    (gadgetX_ty (hp.weaken _) ((tyB_const 0).le (Ty.le_big _)) (hdet 0) (hdet 1) (hdet 2)
      (hdet 3))
    (hbody.ctx hle)

/-- **Fits and cost of the packed schema enumerator.** -/
theorem hasCost_schEnumP {τs : List Ty} {b : ℕ} (hb : τs.length = b)
    {SX HX RX NX rX p0X EcX : Xp} (hS : LinX τs SX)
    (hH : LinX τs HX) (hR : LinX τs RX) (hN : TyB τs NX (P 0 7)) (hr : TyB τs rX (P 0 7))
    (hp : TyB τs p0X (P 0 7)) (hE : TyB τs EcX (P 0 7)) {body : Gn} {e d : ℕ}
    (hbody : HasCost (τs ++ schTysP) body e d) :
    HasCost τs (schEnumP M b SX HX RX NX rX p0X EcX body) e (d + 12) := by
  subst hb
  exact hasCost_seq (hasCost_cmdEnumP rfl hS hH hR (hasCost_cmdBodyP hS hH hR hN hbody))
    ((hasCost_detGenP hN hr hp hE hbody).mono le_rfl (by omega))

end Lax119563Proofs.Reduction
