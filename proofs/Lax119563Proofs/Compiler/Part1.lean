import Lax119563Proofs.Circuits.Part1
import Lax119563Proofs.Hardness.Part1
import Lax119563Proofs.Reduction.Part1
import Lax119563Proofs.Reduction.Part2
import Lax119563Proofs.Reduction.Part3
import Lax119563Proofs.RowSpace.Part1

/-! ### Formerly `Lax119563Proofs.Reduction.PkCost` -/

section Reduction_PkCost

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

end Reduction_PkCost

/-! ### Formerly `Lax119563Proofs.Reduction.PkCostSys` -/

section Reduction_PkCostSys

/-!
# Fits, cost and well-formedness of the packed generator

* `globTysP`: the classes of the `19` globals (`|y|, n` and `2^ℓ` are `P 1 0`; `h, s, Λ, ℓ, H, R`
  are linear; the counts are polynomial in the linear scale).
* **`hasCost_sysGenP`**: `HasCost globTysP (sysGenP M) 1 15`;
* **`hasCost_midP`**: the part of the prelude after `|y|, n, h, s, Λ` has
  `HasCost [P 1 0, P 1 0, P 0 1, P 0 1, P 0 1] (midP M g) 1 D` for `HasCost globTysP g 1 D`;
* **`wfx_redGenP`**: the packed generator is well formed.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Xp Ty Gn

variable {M : Machine}

/-- The classes of the globals (levels `0 … 18`). -/
def globTysP : List Ty :=
  [P 1 0, P 1 0, P 0 1, P 0 1, P 0 1, P 0 1, P 0 1, P 0 1, P 0 1, P 0 1, P 0 2, P 0 7, P 0 7,
    P 0 0, P 0 0, P 0 20, P 0 7, P 0 7, P 1 0]

lemma length_globTysP : globTysP.length = 19 := rfl

variable {Γ : List Ty}

namespace Xp

lemma hasTy_minQ {a b : Xp} {τa τb : Ty} (ha : HasTy Γ a τa) (hb : HasTy Γ b τb) :
    HasTy Γ (minQ a b) τb := hasTy_minR ha hb

lemma hasTy_maxQ {a b : Xp} {e d : ℕ} (ha : HasTy Γ a (P e d)) (hb : HasTy Γ b (P e d)) :
    HasTy Γ (maxQ a b) (P e d) := by
  have h1 : HasTy Γ (const 1) (P 0 1) := (hasTy_const 1).le ⟨le_rfl, by omega⟩
  have hc : HasTy Γ (Xp.lt a b) (P 0 0) := hasTy_lt ha hb
  have hbig : HasTy Γ (maxQ a b) .big :=
    hasTy_addBig (hasTy_mulBBig ha (hasTy_not hc) h1) (hasTy_mulBBig hb hc h1)
  exact HasTy.of_eval_le hbig (hasTy_add ha hb) fun ρ => by
    rw [eval_maxQ, eval_add]; exact max_le (by omega) (by omega)

end Xp

/-! ## The domain test -/

/-- **Fits and cost of the domain test**: one loop over the field width `g2X`. -/
theorem hasCost_violGenP {d : ℕ} (hd : Γ.length = d) {sX iX iℓX vX xbX gkX g1X g2X g3X ℓX HX : Xp}
    {τs τv τx τg τq : Ty} (hs : HasTy Γ sX τs) (hi : TyB Γ iX (P 0 1)) (hiℓ : TyB Γ iℓX (P 0 1))
    (hv : TyB Γ vX τv) (hx : HasTy Γ xbX τx)
    (hgk : HasTy Γ gkX τg) (hg1 : TyB Γ g1X (P 0 1)) (hg2 : HasTy Γ g2X (P 0 1))
    (hg3 : TyB Γ g3X τq) (hℓ : TyB Γ ℓX (P 0 1)) (hH : HasTy Γ HX (P 0 1)) :
    HasCost Γ (violGenP d sX iX iℓX vX xbX gkX g1X g2X g3X ℓX HX) 0 1 := by
  subst hd
  have hf := hasTy_fieldX hiℓ.1 hℓ.1 hH
  have e0 : ∀ {Δ : List Ty}, HasCost Δ (emit (const 0)) 0 1 :=
    (hasCost_emit (hasTy_const 0)).mono le_rfl (by omega)
  have W : ∀ {a : Xp} {τ : Ty}, TyB Γ a τ → HasTy (Γ ++ [P 0 1, P 0 1]) a τ :=
    fun h => (h.weaken _).1
  have ht : HasTy (Γ ++ [P 0 1, P 0 1]) (var (Γ.length + 1)) (P 0 1) :=
    hasTy_var' (by rw [List.getD_append_right _ _ _ _ (by omega)]; simp)
  have hloop : HasCost Γ (.loop g2X (when (fieldBadX iℓX g1X (var (Γ.length + 1)) vX g3X
      ℓX) (emit (const 0)))) 0 1 :=
    (hasCost_loop hg2 (hasCost_when (hasTy_fieldBadX (W hiℓ) (W hg1) ht (W hv) (W hg3) (W hℓ))
      (hasCost_emit (hasTy_const 0)))).mono le_rfl (by omega)
  have hinit : HasTy Γ (initCVX g1X vX xbX) .big :=
    hasTy_addBig (hasTy_eq hv.1 (hasTy_const 0))
      (hasTy_mulCBig (hasTy_mulBBig hx (hasTy_eq hg1.1 (hasTy_const 0))
        ((hasTy_eq hg1.1 (hasTy_const 0)).le ⟨le_rfl, by omega⟩)) 2)
  refine hasCost_when (hasTy_not (hasTy_eq hi.1 hs)) ?_
  refine hasCost_ite (hasTy_eq hgk (hasTy_const 0)) hloop ?_
  refine hasCost_ite (hasTy_eq hgk (hasTy_const 1)) (hasCost_when (τ := P 0 0) ?_ e0) ?_
  · exact hasTy_not (hasTy_or (hasTy_and (hasTy_eq hi.1 (hasTy_const 0))
      (hasTy_eq hinit hg2)) (hasTy_and (hasTy_not (hasTy_eq hi.1 (hasTy_const 0)))
        (hasTy_eq hv.1 hf)))
  refine hasCost_ite (hasTy_eq hgk (hasTy_const 2)) (hasCost_when (τ := P 0 0) ?_ e0)
    (hasCost_when (hasTy_not (hasTy_eq hv.1 (hasTy_const 0))) e0)
  exact hasTy_not (hasTy_or (hasTy_not (hasTy_eq hi.1 hg1.1)) (hasTy_not (hasTy_eq hv.1 hf)))

/-! ## The domain loops -/

lemma hasCost_domLoopsP {D d : ℕ} (hD : Γ.length = D) {V body : Gn}
    (hS : HasTy Γ qS (P 0 1)) (hP : TyB Γ qP (P 1 0))
    (hV : HasCost (Γ ++ [P 0 1, P 0 1] ++ [P 1 0, P 1 0, P 0 0] ++ [P 1 0] ++ [P 0 0]) V 0 1)
    (hb : HasCost (Γ ++ [P 0 1, P 0 1] ++ [P 1 0, P 1 0, P 0 0] ++ [P 1 0] ++ [P 0 2]) body 0 d)
    (hd : 1 ≤ d) :
    HasCost Γ (Gn.domLoopsP D V body) 1 (d + 1) := by
  subst hD
  unfold Gn.domLoopsP
  have hc := hasCost_count (τ := P 0 2) (hV.mono le_rfl hd) hV.len hb
  have hk : HasTy (Γ ++ [P 0 1, P 0 1] ++ [P 1 0, P 1 0, P 0 0]) (var (Γ.length + 3)) (P 1 0) :=
    hasTy_var' (by rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]; simp)
  have hbind := hasCost_bind (hasTy_shr hk ((hasTy_const 4).le ⟨le_rfl, by omega⟩)) hc
  have hwhen := hasCost_when (hasTy_eq hk (hasTy_addBig (hasTy_shl (hasTy_shr hk
    ((hasTy_const 4).le ⟨le_rfl, by omega⟩)) ((hasTy_const 4).le ⟨le_rfl, by omega⟩))
    (hasTy_const 1))) hbind
  have hlim : HasTy (Γ ++ [P 0 1, P 0 1]) (mulC 16 qP) (P 1 0) :=
    hasTy_mulC (hP.weaken _).1 16
  have hx := hasCost_loopX hlim hwhen
  have hl := hasCost_loop (hasTy_add hS ((hasTy_const 1).le ⟨le_rfl, by omega⟩)) hx
  exact hl.mono (by simp) (by simp; omega)

/-! ## The schema body -/

/-- The context of the schema body. -/
abbrev ΓSP : List Ty := globTysP ++ schTysP

lemma length_schTysP : schTysP.length = 37 := rfl

/-- A variable of a concrete context with its class and bound. -/
macro "tvbP" : tactic => `(tactic| exact ⟨hasTy_var' rfl, by
  show _ < List.length _; simp [length_globTysP, length_schTysP]⟩)

lemma hasCost_violAtP_d (τ : Ty) :
    HasCost (ΓSP ++ [τ] ++ [P 0 1, P 0 1] ++ [P 1 0, P 1 0, P 0 0] ++ [P 1 0] ++ [P 0 0])
      (Gn.violAtP 19 (19 + 37 + 1)) 0 1 := by
  have hi : TyB (ΓSP ++ [τ] ++ [P 0 1, P 0 1] ++ [P 1 0, P 1 0, P 0 0] ++ [P 1 0] ++ [P 0 0])
      (var 58) (P 0 1) := by tvbP
  have hℓ : TyB (ΓSP ++ [τ] ++ [P 0 1, P 0 1] ++ [P 1 0, P 1 0, P 0 0] ++ [P 1 0] ++ [P 0 0])
      qℓ (P 0 1) := by tvbP
  have hΛ : TyB (ΓSP ++ [τ] ++ [P 0 1, P 0 1] ++ [P 1 0, P 1 0, P 0 0] ++ [P 1 0] ++ [P 0 0])
      qΛ (P 0 1) := by tvbP
  have hpos : TyB (ΓSP ++ [τ] ++ [P 0 1, P 0 1] ++ [P 1 0, P 1 0, P 0 0] ++ [P 1 0] ++ [P 0 0])
      (posX (var 58)) (P 0 1) :=
    ⟨Xp.hasTy_minQ (hasTy_mul hℓ.1 hi.1 hi.1) hΛ.1, bnd_minQ ⟨hℓ.2, hi.2, hi.2⟩ hΛ.2⟩
  have h61 : HasTy (ΓSP ++ [τ] ++ [P 0 1, P 0 1] ++ [P 1 0, P 1 0, P 0 0] ++ [P 1 0] ++ [P 0 0])
      (var 61) (P 0 0) := hasTy_var' rfl
  have hlt : HasTy (ΓSP ++ [τ] ++ [P 0 1, P 0 1] ++ [P 1 0, P 1 0, P 0 0] ++ [P 1 0] ++ [P 0 0])
      (Xp.lt (var 62) (var 1)) (P 0 0) := hasTy_lt (hasTy_var _) (hasTy_var _)
  have hxb := hasTy_mul h61 hlt (hlt.le ⟨le_rfl, by omega⟩)
  exact hasCost_violGenP rfl (hasTy_var _) hi hpos (by tvbP) hxb (hasTy_var _) (by tvbP)
    ((hasTy_var' rfl).le ⟨le_rfl, by omega⟩) (by tvbP) hℓ (hasTy_var' rfl)

lemma hasCost_domGenP : HasCost ΓSP (Gn.domGenP 19 (19 + 37)) 1 2 := by
  unfold Gn.domGenP
  have hS : ∀ τ, HasTy (ΓSP ++ [τ]) qS (P 0 1) := fun τ => hasTy_var' rfl
  have hP : ∀ τ, TyB (ΓSP ++ [τ]) qP (P 1 0) := fun τ => by tvbP
  have hd : HasCost (ΓSP ++ [P 0 0]) (Gn.domLoopsP (19 + 37 + 1) (Gn.violAtP 19 (19 + 37 + 1))
      (Gn.domBodyP (19 + 37 + 1))) 1 2 := by
    refine hasCost_domLoopsP rfl (hS _) (hP _) (hasCost_violAtP_d _) ?_ le_rfl
    refine (hasCost_when' ?_ (hasCost_emit' ?_)).mono (Nat.zero_le _) (Nat.zero_le _) <;> tp
  refine hasCost_count hd hd.len ?_
  refine hasCost_seq ((hasCost_emit (hasTy_var _)).mono (Nat.zero_le _) (Nat.zero_le _)) ?_
  refine hasCost_domLoopsP rfl (hS _) (hP _) (hasCost_violAtP_d _) ?_ le_rfl
  unfold Gn.domBodyP' Gn.bitsGenP
  refine hasCost_when' (by tp) (hasCost_seq ((hasCost_emit (hasTy_var _)).mono (Nat.zero_le _)
    (Nat.zero_le _)) ?_)
  exact (hasCost_loop (hasTy_var' rfl) (hasCost_emit' (by tp))).mono (by simp) (by simp)

lemma hasCost_permGenP {mX : Xp} (hm : Tp (ΓSP ++ [P 0 1, P 0 1] ++ [P 0 1, P 0 1]) mX)
    (hm' : Tp (ΓSP ++ [P 0 1, P 0 1] ++ [P 0 1, P 0 1] ++ [P 0 0] ++ [P 0 1, P 0 1]) mX) :
    HasCost ΓSP (Gn.permGenP mX (19 + 37)) 0 3 := by
  unfold Gn.permGenP
  have hS1 : ∀ l : List Ty, HasTy (ΓSP ++ l) (add qS (const 1)) (P 0 1) := fun l =>
    hasTy_add (hasTy_var' rfl) ((hasTy_const 1).le ⟨le_rfl, by omega⟩)
  refine hasCost_seq ?_ ?_
  · exact (hasCost_loop (hS1 []) (hasCost_emit (hasTy_var _))).mono (by simp) (by simp)
  · have hpos : ∀ (Δ : List Ty) (j : ℕ), Δ.getD j (P 0 0) = P 0 1 → Δ.getD 7 (P 0 0) = P 0 1 →
        Δ.getD 4 (P 0 0) = P 0 1 → HasTy Δ (posX (var j)) (P 0 1) := fun Δ j h1 h2 h3 =>
      Xp.hasTy_minQ (hasTy_mul (hasTy_var' h2) (hasTy_var' h1) (hasTy_var' h1)) (hasTy_var' h3)
    have hin : HasCost (ΓSP ++ [P 0 1, P 0 1] ++ [P 0 1, P 0 1]) (.ite (Xp.lt (var (56 + 1)) qS)
        (.emit (odd (shr mX (add (posX (var (56 + 1))) (var (56 + 3))))))
        (.count (.loop qS (when (odd (shr mX (add (posX (var (56 + 6))) (var (56 + 3)))))
            (.emit (const 0))))
          (.emit (odd (var (56 + 4)))))) 0 1 := by
      refine hasCost_ite (hasTy_lt (hasTy_var _) (hasTy_var _)) ?_ ?_
      · refine (hasCost_emit (hasTy_odd (hasTy_shr hm.ex.choose_spec
          (hasTy_add (hpos _ _ rfl rfl rfl) (hasTy_var' rfl))))).mono le_rfl (by omega)
      · have hl : HasCost (ΓSP ++ [P 0 1, P 0 1] ++ [P 0 1, P 0 1] ++ [P 0 0])
            (.loop qS (when (odd (shr mX (add (posX (var (56 + 6))) (var (56 + 3)))))
              (.emit (const 0)))) 0 1 :=
          (hasCost_loop (hasTy_var' rfl) (hasCost_when (hasTy_odd (hasTy_shr
            hm'.ex.choose_spec (hasTy_add (hpos _ _ rfl rfl rfl) (hasTy_var' rfl))))
            (hasCost_emit (hasTy_const 0)))).mono (by simp) (by simp)
        exact hasCost_count hl hl.len ((hasCost_emit (hasTy_odd (hasTy_var _))).mono le_rfl
          (by omega))
    exact (hasCost_loop (hS1 []) (hasCost_loop (hasTy_var' rfl) hin)).mono (by simp) (by simp)

lemma hasCost_schBodyP : HasCost ΓSP (Gn.schBodyP 19) 1 3 := by
  unfold Gn.schBodyP
  have hp : ∀ mX : Xp, Tp (ΓSP ++ [P 0 1, P 0 1] ++ [P 0 1, P 0 1]) mX →
      Tp (ΓSP ++ [P 0 1, P 0 1] ++ [P 0 1, P 0 1] ++ [P 0 0] ++ [P 0 1, P 0 1]) mX →
      HasCost ΓSP (Gn.permGenP mX (19 + 37)) 1 3 := fun mX hm hm' =>
    (hasCost_permGenP hm hm').mono (Nat.zero_le _) le_rfl
  have hdg : HasCost ΓSP (Gn.domGenP 19 (19 + 37)) 1 3 := hasCost_domGenP.mono le_rfl (by omega)
  refine hasCost_ite' (by tp) (hasCost_seqL fun g hg => ?_) (hasCost_seqL fun g hg => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact (hasCost_emit (hasTy_var _)).mono (Nat.zero_le _) (Nat.zero_le _)
      | exact (hasCost_emit (hasTy_const _)).mono (Nat.zero_le _) (Nat.zero_le _)
      | exact hdg
      | exact hp _ (tp_var _) (tp_var _)
      | exact hp _ (tp_const _) (tp_const _)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact (hasCost_emit (hasTy_var _)).mono (Nat.zero_le _) (Nat.zero_le _)
      | exact (hasCost_emit (hasTy_const _)).mono (Nat.zero_le _) (Nat.zero_le _)
      | exact hdg
      | exact hp _ (tp_var _) (tp_var _)
      | exact hp _ (tp_const _) (tp_const _)

/-! ## The system -/

lemma hasCost_locGenP : HasCost globTysP (Gn.locGenP 19) 1 9 := by
  unfold Gn.locGenP
  refine (hasCost_loop (hasTy_var' (i := 16) (τ := P 0 7) rfl) (e := 1) (d := 2) ?_).mono
    (by omega) (by omega)
  refine hasCost_seqL fun g hg => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · refine (hasCost_emit' ?_).mono (Nat.zero_le _) (Nat.zero_le _)
    unfold Gn.initXP; tp
  · refine (hasCost_emit (hasTy_mul (hasTy_var' (i := 18) rfl)
      (hasTy_add (hasTy_var' (i := 3) rfl) ((hasTy_const 1).le ⟨le_rfl, by omega⟩))
      (hasTy_add (hasTy_var' (i := 3) rfl) ((hasTy_const 1).le ⟨le_rfl, by omega⟩)))).mono
      (Nat.zero_le _) (Nat.zero_le _)
  · unfold Gn.bitsGenP
    refine (hasCost_loop (hasTy_add (hasTy_var' (i := 3) rfl)
      ((hasTy_const 1).le ⟨le_rfl, by omega⟩)) (hasCost_loop (hasTy_var' rfl)
      (hasCost_seq ((hasCost_emit (hasTy_var _)).mono (Nat.zero_le _) (Nat.zero_le _))
        (hasCost_loop (hasTy_var' rfl) (hasCost_emit' (by tp)))))).mono (by simp) (by simp)

/-- **Fits and cost of the packed system generator.** -/
theorem hasCost_sysGenP (M : Machine) : HasCost globTysP (Gn.sysGenP M) 1 15 := by
  unfold Gn.sysGenP
  refine hasCost_seqL fun g hg => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hasCost_emit (hasTy_addBig (hasTy_var _) (hasTy_const _))).mono (Nat.zero_le _)
      (Nat.zero_le _)
  · exact (hasCost_emit (hasTy_var _)).mono (Nat.zero_le _) (Nat.zero_le _)
  · exact (hasCost_emit (hasTy_var _)).mono (Nat.zero_le _) (Nat.zero_le _)
  · exact hasCost_locGenP.mono le_rfl (by omega)
  · exact (hasCost_emit (hasTy_var _)).mono (Nat.zero_le _) (Nat.zero_le _)
  · exact (hasCost_schEnumP (M := M) rfl (by tvbP) (by tvbP) (by tvbP)
      ((show TyB globTysP qN (P 0 2) by tvbP).le ⟨le_rfl, by omega⟩) (by tvbP)
      ((show TyB globTysP qp0 (P 0 0) by tvbP).le ⟨le_rfl, by omega⟩) (by tvbP)
      hasCost_schBodyP).mono le_rfl (by omega)

/-! ## The prelude -/

/-- The classes of `|y|, n, h, s, Λ`. -/
abbrev Γ5 : List Ty := [P 1 0, P 1 0, P 0 1, P 0 1, P 0 1]

/-- **Fits and cost of the prelude after `|y|, n, h, s, Λ`.** -/
theorem hasCost_midP (M : Machine) {D : ℕ} (hD : 12 ≤ D) {g : Gn}
    (hg : HasCost globTysP g 1 D) : HasCost Γ5 (Gn.midP M g) 1 D := by
  have lin : ∀ {Γ : List Ty} (c : ℕ), HasTy Γ (const c) (P 0 1) := fun c => hasTy_lin_const c
  have L : ∀ {Γ : List Ty} {i d d' : ℕ}, Γ.getD i (P 0 0) = P 0 d → d ≤ d' →
      HasTy Γ (var i) (P 0 d') := fun h hd => (hasTy_var' h).le ⟨le_rfl, hd⟩
  unfold Gn.midP
  -- level 5: log₂(n + 1)
  refine (hasCost_log (e₀ := 1) (d₀ := 0) (e := 1) (d := D)
    (hasTy_add (hasTy_var' rfl) ((hasTy_const 1).le ⟨by norm_num, le_rfl⟩)) ?_).mono
    (by simp) (by simp)
  -- level 6: q
  have hq : HasCost (Γ5 ++ [P 0 1] ++ [P 0 0]) (Gn.loop (add (var 2) (const 2))
      (Gn.when (Xp.le (mul (var 3) (add (var 8) (const 1))) (add (add (var 2) (const 1)) (var 3)))
        (Gn.emit (const 0)))) 0 1 := by
    refine (hasCost_loop (hasTy_add (hasTy_var' rfl) (lin 2)) (hasCost_when (τ := P 0 0) ?_
      (hasCost_emit (hasTy_const 0)))).mono (by simp) (by simp)
    exact hasTy_le (hasTy_mul (hasTy_var' rfl) (hasTy_add (hasTy_var' rfl) (lin 1))
      (hasTy_add (hasTy_var' rfl) (lin 1)))
      (hasTy_add (hasTy_add (hasTy_var' rfl) (lin 1)) (hasTy_var' rfl))
  have hql : HasLen (Γ5 ++ [P 0 1] ++ [P 0 0]) (Gn.loop (add (var 2) (const 2))
      (Gn.when (Xp.le (mul (var 3) (add (var 8) (const 1))) (add (add (var 2) (const 1)) (var 3)))
        (Gn.emit (const 0)))) (P 0 1) := by
    have := hasLen_loop (hasTy_add (hasTy_var' (τs := Γ5 ++ [P 0 1] ++ [P 0 0]) (i := 2) rfl)
      (lin 2)) (hasLen_when (Xp.le (mul (var 3) (add (var 8) (const 1)))
        (add (add (var 2) (const 1)) (var 3))) (hasLen_emit (τs := Γ5 ++ [P 0 1] ++ [P 0 0] ++ [P 0 1, P 0 1])
        (const 0)))
    simpa using this
  refine hasCost_count (τ := P 0 1) (hq.mono (by omega) (by omega)) hql ?_
  -- levels 7, 8, 9, 10: ℓ, H, R, N
  refine hasCost_bind (τ := P 0 1) (Xp.hasTy_maxQ (hasTy_add (hasTy_var' rfl) (lin 1))
    (hasTy_var' rfl)) ?_
  refine hasCost_bind (τ := P 0 1) (Xp.hasTy_maxQ (hasTy_var' rfl) (hasTy_var' rfl)) ?_
  refine hasCost_bind (τ := P 0 1) (hasTy_add (hasTy_var' rfl) (lin _)) ?_
  refine hasCost_bind (τ := P 0 2) ?_ ?_
  · have hR : HasTy (Γ5 ++ [P 0 1] ++ [P 0 1] ++ [P 0 1] ++ [P 0 1] ++ [P 0 1]) (var 9)
        (P 0 1) := hasTy_var' rfl
    exact hasTy_mulC (hasTy_mul hR hR hR) _
  -- level 11: r
  have hc11 := hasCost_cmdEnumP (M := M)
    (τs := Γ5 ++ [P 0 1] ++ [P 0 1] ++ [P 0 1] ++ [P 0 1] ++ [P 0 1] ++ [P 0 2] ++ [P 0 0])
    (b := 12) rfl (SX := qS) (HX := var 8) (RX := var 9) (by tvbP) (by tvbP) (by tvbP)
    (hasCost_emit (hasTy_const 0) : HasCost _ (emit (const 0)) 0 0)
  refine hasCost_count (hc11.mono (by omega) (by omega)) hc11.len ?_
  -- level 12: Ec
  have hc12 := hasCost_cmdEnumP (M := M)
    (τs := Γ5 ++ [P 0 1] ++ [P 0 1] ++ [P 0 1] ++ [P 0 1] ++ [P 0 1] ++ [P 0 2] ++
      [P 0 (0 + 6 + 1)] ++ [P 0 0])
    (b := 13) rfl (SX := qS) (HX := var 8) (RX := var 9) (by tvbP) (by tvbP) (by tvbP)
    (hasCost_ite (hasTy_var _) (hasCost_emitN 9) (hasCost_emitN 4) : HasCost _ (szBodyP 13) 0 0)
  refine hasCost_count (hc12.mono (by omega) (by omega)) hc12.len ?_
  -- levels 13, 14: codes
  refine hasCost_bind (τ := P 0 0) (hasTy_const 2) ?_
  refine hasCost_bind (τ := P 0 0) (hasTy_const 0) ?_
  -- level 15: E
  have hc15 := hasCost_schEnumP (M := M)
    (τs := Γ5 ++ [P 0 1] ++ [P 0 1] ++ [P 0 1] ++ [P 0 1] ++ [P 0 1] ++ [P 0 2] ++
      [P 0 (0 + 6 + 1)] ++ [P 0 (0 + 6 + 1)] ++ [P 0 0] ++ [P 0 0] ++ [P 0 0])
    (b := 16) rfl (SX := qS) (HX := qH) (RX := qR) (NX := qN) (rX := qr) (p0X := qp0)
    (EcX := qEc) (by tvbP) (by tvbP) (by tvbP)
    ((show TyB _ qN (P 0 2) by tvbP).le ⟨le_rfl, by norm_num⟩) (by tvbP)
    ((show TyB _ qp0 (P 0 0) by tvbP).le ⟨le_rfl, by norm_num⟩) (by tvbP)
    (hasCost_emit (hasTy_const 0) : HasCost _ (emit (const 0)) 0 0)
  refine hasCost_count (hc15.mono (by omega) (by omega))
    (hc15.len.le (show Ty.Le (P 0 (0 + 12 + 1)) (P 0 20) from ⟨le_rfl, by norm_num⟩)) ?_
  -- levels 16, 17, 18: W, det, 2^ℓ
  refine hasCost_bind (τ := P 0 7) ?_ ?_
  · exact hasTy_add (hasTy_add (L rfl (by norm_num)) (hasTy_mulC (L rfl le_rfl) _))
      ((hasTy_const _).le ⟨le_rfl, by norm_num⟩)
  refine hasCost_bind (τ := P 0 7) ?_ ?_
  · exact hasTy_add (hasTy_add (L rfl (by norm_num)) (hasTy_mulC (L rfl le_rfl) _))
      ((hasTy_const _).le ⟨le_rfl, by norm_num⟩)
  refine hasCost_bind (τ := P 1 0) (Xp.hasTy_minQ (hasTy_pow2 (hasTy_var' rfl))
    (hasTy_var' rfl)) ?_
  exact hg

/-! ## Well-formedness -/

namespace Gn

lemma noX_violGenP (d : ℕ) (sX iX iℓX vX xbX gkX g1X g2X g3X ℓX HX : Xp) :
    NoX (violGenP d sX iX iℓX vX xbX gkX g1X g2X g3X ℓX HX) := by
  unfold violGenP
  have e : NoX (.emit (const 0)) := trivial
  exact cl_noX.when _ (cl_noX.ite _ (cl_noX.loop _ (cl_noX.when _ e))
    (cl_noX.ite _ (cl_noX.when _ e) (cl_noX.ite _ (cl_noX.when _ e) (cl_noX.when _ e))))

lemma wfx_domLoopsP (D : ℕ) {V body : Gn} (hV : NoX V) (hb : NoX body) :
    WFX (domLoopsP D V body) :=
  ⟨cl_noX.when _ (cl_noX.bind _ ⟨hV, hb⟩), wfx_of_noX (g := .when _ (.bind _ (.count V body)))
    (cl_noX.when _ (cl_noX.bind _ ⟨hV, hb⟩))⟩

lemma Cl.cmdEnumP {P : Gn → Prop} (hP : Cl P) (M : Machine) (b : ℕ) (SX HX RX : Xp) {body : Gn}
    (hb : P body) : P (cmdEnumP M b SX HX RX body) := by
  unfold Lax119563Proofs.Reduction.cmdEnumP
  refine hP.loop _ (hP.loop _ (hP.loop _ (hP.loop _ ?_)))
  refine hP.bindSub _ _ _ (hP.bindSub _ _ _ (hP.bindSub _ _ _ (hP.bindSub _ _ _ ?_)))
  refine hP.bind _ (hP.seqL fun g hg => ?_)
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hg
  refine hP.firstL _ (fun K => hP.loop _ (hP.bind _ (hP.seq (hP.when _ (hP.brGen _ _ hb _)) ?_))) _
  unfold missGen
  split_ifs
  · exact hP.when _ (hP.bindL hb _)
  · exact hP.skip

lemma Cl.schEnumP {P : Gn → Prop} (hP : Cl P) (M : Machine) (b : ℕ)
    (SX HX RX NX rX p0X EcX : Xp) {body : Gn} (hb : P body) :
    P (schEnumP M b SX HX RX NX rX p0X EcX body) := by
  unfold Lax119563Proofs.Reduction.schEnumP cmdBodyP detGen
  refine hP.seq (hP.cmdEnumP _ _ _ _ _ (hP.count (hP.cmdEnumP _ _ _ _ _ (hP.when _ (hP.emit _)))
    (hP.count (hP.cmdEnumP _ _ _ _ _ (hP.when _ (hP.ite _ (hP.emitN 9) (hP.emitN 4))))
      (hP.ite _ (hP.blkGen _ _ hb _) (hP.blkGen _ _ hb _))))) ?_
  exact hP.bindL (hP.blkGen _ _ hb _) _

lemma wfx_schBodyP (b : ℕ) : WFX (schBodyP b) := by
  have hv : NoX (violAtP b (b + 37 + 1)) := noX_violGenP ..
  have hd : WFX (domGenP b (b + 37)) :=
    cl_wfx.count (wfx_domLoopsP _ hv (cl_noX.when _ (cl_noX.emit _)))
      (cl_wfx.seq trivial (wfx_domLoopsP _ hv (cl_noX.when _ (cl_noX.seq (cl_noX.emit _)
        (cl_noX.loop _ (cl_noX.emit _))))))
  have hp : ∀ mX, WFX (permGenP mX (b + 37)) := fun _ =>
    cl_wfx.seq (cl_wfx.loop _ (cl_wfx.emit _)) (cl_wfx.loop _ (cl_wfx.loop _ (cl_wfx.ite _
      (cl_wfx.emit _) (cl_wfx.count (cl_wfx.loop _ (cl_wfx.when _ (cl_wfx.emit _)))
        (cl_wfx.emit _)))))
  unfold schBodyP
  refine cl_wfx.ite _ (cl_wfx.seqL fun g hg => ?_) (cl_wfx.seqL fun g hg => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact hd | exact hp _ | trivial
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hd | exact hp _ | trivial

lemma wfx_sysGenP (M : Machine) : WFX (sysGenP M) := by
  unfold sysGenP
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
      · exact cl_wfx.loop _ (cl_wfx.loop _ ⟨trivial, cl_wfx.loop _ trivial⟩))
  · trivial
  · exact cl_wfx.schEnumP _ _ _ _ _ _ _ _ _ (wfx_schBodyP 19)

lemma wfx_midP (M : Machine) {g : Gn} (hg : WFX g) : WFX (midP M g) := by
  unfold midP
  refine cl_wfx.log _ (cl_wfx.count (cl_wfx.loop _ (cl_wfx.when _ (cl_wfx.emit _))) ?_)
  refine cl_wfx.bind _ <| cl_wfx.bind _ <| cl_wfx.bind _ <| cl_wfx.bind _ ?_
  refine cl_wfx.count (cl_wfx.cmdEnumP _ _ _ _ _ (cl_wfx.emit _)) ?_
  refine cl_wfx.count (cl_wfx.cmdEnumP _ _ _ _ _ (cl_wfx.ite _ (cl_wfx.emitN 9)
    (cl_wfx.emitN 4))) ?_
  refine cl_wfx.bind _ (cl_wfx.bind _ (cl_wfx.count (cl_wfx.schEnumP _ _ _ _ _ _ _ _ _
    (cl_wfx.emit _)) ?_))
  exact cl_wfx.bind _ <| cl_wfx.bind _ <| cl_wfx.bind _ hg

/-- **The packed generator is well formed.** -/
theorem wfx_redGenP (M : Machine) : WFX (redGenP M) := by
  unfold redGenP preludeP flagCount
  have hf : ∀ t d, WFX (Gn.loopX (var 0) (flagGen t d)) := fun t d =>
    ⟨cl_noX.when _ (cl_noX.emit _), cl_wfx.when _ (cl_wfx.emit _)⟩
  exact wfx_len (cl_wfx.count (hf _ _) (cl_wfx.count (hf _ _) (cl_wfx.count (hf _ _)
    (cl_wfx.bind _ (wfx_midP M (wfx_sysGenP M))))))

end Gn

end Lax119563Proofs.Reduction

end Reduction_PkCostSys

/-! ### Formerly `Lax119563Proofs.Reduction.PkMachine` -/

section Reduction_PkMachine

/-!
# The machine of the packed generator

**`redGenP_computesWithin`**: the machine of the packed generator computes
`encodeSystem (Iv M x s ℓ H)` (`ℓ = packedWidth |x| h s`, `H = pkHorizon |x| h s`) from the
preprocessed input `pkInput x h s` within `C 2^ℓ (h + 1)^c` steps, with `c` absolute.

The growth classes are taken at the scale `l = ℓ + log₂(h + 3) + 5` (so that the input length
`16 max(|x|, h, s, 2^⌈(h+2)/s⌉)` is at most `2^l`) and `L = (h + 3)^2 + l` (so that `h, s`,
`Λ = (h + 3)^2` and the bit positions `i ℓ` are linear). The first five steps of the prelude
(`|y|` and the counts `n, h, s` and `Λ`) are analysed directly.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp Ty Gn
open Lax119563.BinaryEncodings Lax119563.ImplicitSystemEncodings

variable {M : Machine}

/-- The scale of the analysis. -/
def scP (n h s : ℕ) : Sc :=
  ⟨pkWidth n h s + (Nat.log 2 (h + 3) + 5), (h + 3) ^ 2 + pkWidth n h s + (Nat.log 2 (h + 3) + 5),
    by omega⟩

/-! ## The flags -/

lemma len_flag (x : List Bool) (h s : ℕ) {ρ : List ℕ} (hρ0 : ρ.getD 0 0 = 16 * pkLen x.length h s)
    (hρl : 0 < ρ.length) (t : ℕ) (ht : t < 16) (j : ℕ)
    (hb : ∀ q, q < pkLen x.length h s → (((pkBlk (x.getD q false) (decide (q < x.length))
      (decide (q < h)) (decide (q < s)))[t]?).elim 0 (fun b => b.toNat + 1) = 2 ↔ q < j))
    (hjm : j ≤ pkLen x.length h s) :
    ((Gn.loopX (var 0) (flagGen t (ρ.length + 1))).out (pkInput x h s) (ρ ++ [0])).length = j := by
  have hlim : (var 0).eval (ρ ++ [0]) = 16 * pkLen x.length h s := by
    rw [eval_var, List.getD_append _ _ _ _ hρl, hρ0]
  simp only [Gn.out, hlim]
  exact count_flag x h s (σ := ρ ++ [0]) (by simp) t ht j hb hjm

lemma hasCost_flagLoop {τs : List Ty} (h0 : τs.getD 0 (P 0 0) = P 1 0) (t d : ℕ) :
    HasCost τs (Gn.loopX (var 0) (flagGen t d)) 1 0 := by
  have hb : HasCost (τs ++ [P 1 0, P 1 0, P 0 0]) (flagGen t d) 0 0 := by
    unfold flagGen isMod
    exact hasCost_when (τ := P 0 0)
      (hasTy_and (hasTy_eq (hasTy_var _) (hasTy_addBig (hasTy_shl (hasTy_shr (hasTy_var _)
        ((hasTy_const 4).le ⟨le_rfl, by omega⟩)) ((hasTy_const 4).le ⟨le_rfl, by omega⟩))
        (hasTy_const _))) (hasTy_eq (hasTy_var _) (hasTy_const 2)))
      (hasCost_emit (hasTy_const 0))
  have := hasCost_loopX (hasTy_var' h0) hb
  exact this.mono (by simp) (by simp)

lemma cost_flagCount (y : List Bool) (t d : ℕ) (g : Gn) (ρ : List ℕ) :
    (Gn.flagCount t d g).cost y ρ = 1 + (Gn.loopX (var 0) (flagGen t (d + 1))).cost y (ρ ++ [0]) +
      g.cost y (ρ ++ [((Gn.loopX (var 0) (flagGen t (d + 1))).out y (ρ ++ [0])).length]) := rfl

lemma fits_flagCount (y : List Bool) (t d : ℕ) (g : Gn) (ρ : List ℕ) (B : ℕ) :
    (Gn.flagCount t d g).Fits y B ρ ↔
      ((Gn.loopX (var 0) (flagGen t (d + 1))).out y (ρ ++ [0])).length < B ∧
      (Gn.loopX (var 0) (flagGen t (d + 1))).Fits y B (ρ ++ [0]) ∧
      g.Fits y B (ρ ++ [((Gn.loopX (var 0) (flagGen t (d + 1))).out y (ρ ++ [0])).length]) :=
  Iff.rfl

/-! ## Bounds on the scale -/

lemma pkLen_le {n h s : ℕ} (hn : n < 2 ^ pkWidth n h s) (hsh : s ≤ h + 2) :
    pkLen n h s ≤ 2 ^ pkWidth n h s + h + 2 := by
  have : 2 ^ ((h + 1 + s) / s) ≤ 2 ^ pkWidth n h s :=
    Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
  unfold pkLen; omega

lemma two_pow_scP {n h s : ℕ} :
    2 ^ (scP n h s).l = 2 ^ pkWidth n h s * (32 * 2 ^ Nat.log 2 (h + 3)) := by
  simp only [scP]; rw [pow_add, pow_add]; ring

lemma len_le_scP {n h s : ℕ} (hn : n < 2 ^ pkWidth n h s) (hsh : s ≤ h + 2) :
    16 * pkLen n h s ≤ 2 ^ (scP n h s).l := by
  rw [two_pow_scP]
  have h1 := pkLen_le hn hsh
  have h2 : h + 3 < 2 * 2 ^ Nat.log 2 (h + 3) := by
    have := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) (h + 3)
    rw [pow_succ] at this; omega
  have h3 : 1 ≤ 2 ^ pkWidth n h s := Nat.one_le_two_pow
  generalize 2 ^ pkWidth n h s = A at h1 h3
  generalize 2 ^ Nat.log 2 (h + 3) = B at h2
  nlinarith

lemma le_two_pow_L {n h s : ℕ} {v : ℕ} (hv : v ≤ 2 ^ (scP n h s).l) (K : ℕ) (hK : 1 ≤ K) :
    v < 2 ^ (K * ((scP n h s : ℕ) + 1)) := by
  have h1 := (scP n h s).le
  have : 2 ^ (scP n h s).l < 2 ^ (K * ((scP n h s : ℕ) + 1)) :=
    Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
  omega

lemma bnd_P_le {e d d' K : ℕ} (σ : Sc) (he : e ≤ 1) (hd : d ≤ d') :
    (P e d).bnd K σ ≤ K * (2 ^ σ.l * ((σ : ℕ) + 1) ^ d') := by
  simp only [Ty.bnd]
  have h1 : 2 ^ (e * σ.l) ≤ 2 ^ σ.l := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h2 : ((σ : ℕ) + 1) ^ d ≤ ((σ : ℕ) + 1) ^ d' := Nat.pow_le_pow_right (by omega) hd
  rw [← Nat.mul_assoc]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2

lemma auxX1 (a b : ℕ) : 1 ≤ 2 ^ a * (b + 1) ^ 16 :=
  Nat.one_le_iff_ne_zero.mpr (by positivity)

lemma auxX2 (a b : ℕ) : b + 1 ≤ 2 ^ a * (b + 1) ^ 16 :=
  calc b + 1 ≤ (b + 1) ^ 16 := Nat.le_self_pow (by norm_num) _
    _ ≤ 2 ^ a * (b + 1) ^ 16 := Nat.le_mul_of_pos_left _ (by positivity)

lemma auxX3 {v a : ℕ} (b : ℕ) (h : v ≤ 2 ^ a) : v ≤ 2 ^ a * (b + 1) ^ 16 :=
  le_trans h (Nat.le_mul_of_pos_right _ (by positivity))

/-- The expression of `Λ`. -/
abbrev ΛX : Xp := mul (add (var 2) (const 3)) (add (var 2) (const 3))

lemma hasTy_ΛX : HasTy [P 1 0, P 1 0, P 0 1, P 0 1] ΛX (P 0 2) := by
  have h := hasTy_add (τs := [P 1 0, P 1 0, P 0 1, P 0 1]) (hasTy_var' (i := 2) rfl)
    (hasTy_lin_const 3)
  simpa using hasTy_mul h h h

set_option maxHeartbeats 1000000 in
/-- **Fits and cost of the packed generator.** -/
theorem redGenP_cost (M : Machine) : ∃ K : ℕ, 1 ≤ K ∧ ∀ (x : List Bool) (h s : ℕ), 2 ≤ x.length →
    2 ≤ h → x.length ≤ 2 ^ h → 2 ≤ s → s ≤ h + 2 →
    (Gn.redGenP M).Fits (pkInput x h s) (2 ^ (K * ((scP x.length h s : ℕ) + 1))) [] ∧
    (Gn.redGenP M).cost (pkInput x h s) [] ≤
      K * 2 ^ (scP x.length h s).l * ((scP x.length h s : ℕ) + 1) ^ 16 := by
  obtain ⟨Km, hKm⟩ := hasCost_midP M (by norm_num : 12 ≤ 15) (hasCost_sysGenP M) 1
  obtain ⟨K1, hK1⟩ := hasCost_flagLoop (τs := [P 1 0, P 0 0]) rfl 3 2 1
  obtain ⟨K2, hK2⟩ := hasCost_flagLoop (τs := [P 1 0, P 1 0, P 0 0]) rfl 5 3 1
  obtain ⟨K3, hK3⟩ := hasCost_flagLoop (τs := [P 1 0, P 1 0, P 0 1, P 0 0]) rfl 10 4 1
  obtain ⟨KΛ, hKΛ⟩ := hasTy_ΛX 1
  refine ⟨Km + K1 + K2 + K3 + KΛ + 8, by omega, fun x h s hx hh hxh hs hsh => ?_⟩
  obtain ⟨hPar, hH⟩ := pk_params hx hh hxh hs
  set σ := scP x.length h s with hσ
  set y := pkInput x h s with hy
  set K := Km + K1 + K2 + K3 + KΛ + 8 with hK
  have hyl : y.length = 16 * pkLen x.length h s := length_pkInput x h s
  have hyσ : y.length ≤ 2 ^ σ.l := by rw [hyl]; exact len_le_scP hPar.hx hsh
  have hnm : x.length ≤ pkLen x.length h s := by unfold pkLen; omega
  have hhm : h ≤ pkLen x.length h s := by unfold pkLen; omega
  have hsm : s ≤ pkLen x.length h s := by unfold pkLen; omega
  have hL : (h + 3) ^ 2 ≤ (σ : ℕ) := by simp only [hσ, scP]; omega
  have hlL := σ.le
  -- the counts
  have hblk : ∀ (a b c d : Bool), ((pkBlk a b c d)[3]?.elim 0 (fun b => b.toNat + 1) = 2 ↔
      b = true) ∧ ((pkBlk a b c d)[5]?.elim 0 (fun b => b.toNat + 1) = 2 ↔ c = true) ∧
      ((pkBlk a b c d)[10]?.elim 0 (fun b => b.toNat + 1) = 2 ↔ d = true) := by
    intro a b c d; cases a <;> cases b <;> cases c <;> cases d <;> decide
  have l1 : ((Gn.loopX (var 0) (flagGen 3 2)).out y ([y.length] ++ [0])).length = x.length :=
    len_flag x h s (ρ := [y.length]) (by simp [hyl]) (by simp) 3 (by omega) x.length
      (fun q _ => by rw [(hblk _ _ _ _).1]; simp) hnm
  have l2 : ((Gn.loopX (var 0) (flagGen 5 3)).out y ([y.length, x.length] ++ [0])).length = h :=
    len_flag x h s (ρ := [y.length, x.length]) (by simp [hyl]) (by simp) 5 (by omega) h
      (fun q _ => by rw [(hblk _ _ _ _).2.1]; simp) hhm
  have l3 : ((Gn.loopX (var 0) (flagGen 10 4)).out y ([y.length, x.length, h] ++ [0])).length =
      s :=
    len_flag x h s (ρ := [y.length, x.length, h]) (by simp [hyl]) (by simp) 10 (by omega) s
      (fun q _ => by rw [(hblk _ _ _ _).2.2]; simp) hsm
  -- the classes of the stacks
  have b10 : ∀ v, v ≤ 2 ^ σ.l → v ≤ (Ty.P 1 0).bnd 1 σ := fun v hv => by
    simp only [Ty.bnd]; simpa using hv
  have b01 : ∀ v, v ≤ (σ : ℕ) + 1 → v ≤ (Ty.P 0 1).bnd 1 σ := fun v hv => by
    simp only [Ty.bnd]; simpa using hv
  have b00 : (0 : ℕ) ≤ (Ty.P 0 0).bnd 1 σ := Nat.zero_le _
  have hn2 : x.length ≤ 2 ^ σ.l := le_trans hnm (by omega)
  have hh2 : h ≤ 2 ^ σ.l := le_trans hhm (by omega)
  have hs2 : s ≤ 2 ^ σ.l := le_trans hsm (by omega)
  have A1 : Ag 1 σ [P 1 0, P 0 0] [y.length, 0] := .cons (b10 _ hyσ) (.cons b00 .nil)
  have A2 : Ag 1 σ [P 1 0, P 1 0, P 0 0] [y.length, x.length, 0] :=
    .cons (b10 _ hyσ) (.cons (b10 _ hn2) (.cons b00 .nil))
  have A3 : Ag 1 σ [P 1 0, P 1 0, P 0 1, P 0 0] [y.length, x.length, h, 0] :=
    .cons (b10 _ hyσ) (.cons (b10 _ hn2) (.cons (b01 _ (by nlinarith)) (.cons b00 .nil)))
  have A4 : Ag 1 σ [P 1 0, P 1 0, P 0 1, P 0 1] [y.length, x.length, h, s] :=
    .cons (b10 _ hyσ) (.cons (b10 _ hn2) (.cons (b01 _ (by nlinarith)) (.cons
      (b01 _ (by nlinarith)) .nil)))
  have eΛ : ΛX.eval [y.length, x.length, h, s] = (h + 3) * (h + 3) := by
    simp only [ΛX, eval_mul, eval_add, eval_var, eval_const]; rfl
  have A5 : Ag 1 σ Γ5 [y.length, x.length, h, s, (h + 3) * (h + 3)] :=
    .cons (b10 _ hyσ) (.cons (b10 _ hn2) (.cons (b01 _ (by nlinarith)) (.cons
      (b01 _ (by nlinarith)) (.cons (b01 _ (by nlinarith)) .nil))))
  obtain ⟨f1, c1⟩ := hK1 σ y _ hyσ A1
  obtain ⟨f2, c2⟩ := hK2 σ y _ hyσ A2
  obtain ⟨f3, c3⟩ := hK3 σ y _ hyσ A3
  obtain ⟨fΛ1, fΛ2, cΛ⟩ := hKΛ σ _ A4
  obtain ⟨fm, cm⟩ := hKm σ y _ hyσ A5
  have hK1 : 1 ≤ K := by omega
  constructor
  · -- fits
    rw [Gn.redGenP, Gn.preludeP]
    refine ⟨le_two_pow_L hyσ K hK1, ?_⟩
    rw [show [] ++ [y.length] = [y.length] from rfl, fits_flagCount, l1]
    refine ⟨le_two_pow_L hn2 K hK1, fits_up (by omega) f1, ?_⟩
    rw [show [y.length] ++ [x.length] = [y.length, x.length] from rfl, fits_flagCount, l2]
    refine ⟨le_two_pow_L hh2 K hK1, fits_up (by omega) f2, ?_⟩
    rw [show [y.length, x.length] ++ [h] = [y.length, x.length, h] from rfl, fits_flagCount, l3]
    refine ⟨le_two_pow_L hs2 K hK1, fits_up (by omega) f3, ?_⟩
    refine ⟨xfits_up (by omega) fΛ2, ?_⟩
    rw [show [y.length, x.length, h] ++ [s] = [y.length, x.length, h, s] from rfl, eΛ]
    exact fits_up (by omega) fm
  · -- cost
    rw [Gn.redGenP, Gn.preludeP]
    show y.length + 1 + (Gn.flagCount 3 1 _).cost y ([] ++ [y.length]) ≤ _
    rw [show [] ++ [y.length] = [y.length] from rfl, cost_flagCount, l1,
      show [y.length] ++ [x.length] = [y.length, x.length] from rfl, cost_flagCount, l2,
      show [y.length, x.length] ++ [h] = [y.length, x.length, h] from rfl, cost_flagCount, l3,
      show [y.length, x.length, h] ++ [s] = [y.length, x.length, h, s] from rfl]
    show y.length + 1 + (1 + _ + (1 + _ + (1 + _ + (ΛX.cost [y.length, x.length, h, s] +
      (Gn.midP M (Gn.sysGenP M)).cost y ([y.length, x.length, h, s] ++
        [ΛX.eval [y.length, x.length, h, s]]))))) ≤ _
    rw [eΛ]
    have d1 := bnd_P_le (K := K1) σ le_rfl (show 0 + 1 ≤ 16 by omega)
    have d2 := bnd_P_le (K := K2) σ le_rfl (show 0 + 1 ≤ 16 by omega)
    have d3 := bnd_P_le (K := K3) σ le_rfl (show 0 + 1 ≤ 16 by omega)
    have dm := bnd_P_le (K := Km) σ le_rfl (show 15 + 1 ≤ 16 by omega)
    have hX : 1 ≤ 2 ^ σ.l * ((σ : ℕ) + 1) ^ 16 := auxX1 _ _
    have hX2 : (σ : ℕ) + 1 ≤ 2 ^ σ.l * ((σ : ℕ) + 1) ^ 16 := auxX2 _ _
    have hX3 : y.length ≤ 2 ^ σ.l * ((σ : ℕ) + 1) ^ 16 := auxX3 _ hyσ
    have e : K * 2 ^ σ.l * ((σ : ℕ) + 1) ^ 16 = K * (2 ^ σ.l * ((σ : ℕ) + 1) ^ 16) := by ring
    rw [e]
    generalize 2 ^ σ.l * ((σ : ℕ) + 1) ^ 16 = X at hX hX2 hX3 d1 d2 d3 dm
    have dΛ : KΛ * ((σ : ℕ) + 1) ≤ KΛ * X := Nat.mul_le_mul_left _ hX2
    have eK : K * X = Km * X + K1 * X + K2 * X + K3 * X + KΛ * X + 8 * X := by rw [hK]; ring
    rw [eK]
    simp only [List.cons_append, List.nil_append, Nat.reduceAdd]
    omega

/-! ## The output is longer than the input -/

lemma length_le_encodeNatsP (l : List ℕ) : l.length ≤ (encodeNats l).length := by
  induction l with
  | nil => simp [encodeNats]
  | cons a l ih =>
    simp only [encodeNats, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    have : 1 ≤ (encodeNat a).length := by simp [encodeNat]
    omega

lemma two_pow_le_locBlock (s ℓ : ℕ) :
    2 ^ ℓ ≤ ((List.range (s + 1)).flatMap fun i =>
      (List.range (2 ^ ℓ)).flatMap fun w => i :: bitsL ℓ w).length := by
  rw [List.range_succ_eq_map, List.flatMap_cons, List.length_append]
  have : 2 ^ ℓ ≤ ((List.range (2 ^ ℓ)).flatMap fun w => 0 :: bitsL ℓ w).length := by
    rw [List.length_flatMap]
    have h : ∀ w ∈ List.range (2 ^ ℓ), 1 ≤ (0 :: bitsL ℓ w).length := fun w _ => by simp
    calc 2 ^ ℓ = ((List.range (2 ^ ℓ)).map fun _ => 1).sum := by simp
      _ ≤ _ := List.sum_le_sum h
  omega

lemma numLoc_ge (R C H : ℕ) (hR : H + 1 ≤ R) (hC : 1 ≤ C) :
    16 * ((H + 1) * (H + 1)) ≤ 16 * (R * (C * (C * (R * C)))) := by
  have h1 : (H + 1) * (H + 1) ≤ R * R := Nat.mul_le_mul hR hR
  have h2 : 1 ≤ C * C * C := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (by omega)) (by omega))
  have h3 : R * R ≤ R * R * (C * C * C) := Nat.le_mul_of_pos_right _ h2
  have e : R * (C * (C * (R * C))) = R * R * (C * C * C) := by ring
  rw [e]; omega

lemma len_le_descP {x : List Bool} {h s : ℕ} (hx : 2 ≤ x.length) (hh : 2 ≤ h)
    (hxh : x.length ≤ 2 ^ h) (hs : 2 ≤ s) (hsh : s ≤ h + 2) :
    16 * pkLen x.length h s ≤
      (systemDescription (Iv M x s (pkWidth x.length h s) (pkHorizon x.length h s))).length := by
  obtain ⟨hPar, hH⟩ := pk_params hx hh hxh hs
  set ℓ := pkWidth x.length h s with hℓ
  set H := pkHorizon x.length h s with hHd
  have hhH : h ≤ H := le_max_left _ _
  have hW : numLoc M H ≤ (Iv M x s ℓ H).numLocations := by rw [Iv_numLocations]; omega
  have hR : H + 1 ≤ radix M H := by unfold radix; omega
  have hC : 1 ≤ cM M := by unfold cM; omega
  have hN : 16 * ((H + 1) * (H + 1)) ≤ numLoc M H := by
    unfold numLoc; exact numLoc_ge _ _ _ hR hC
  have hloc : (Iv M x s ℓ H).numLocations * 2 ^ ℓ ≤
      ((List.finRange (Iv M x s ℓ H).numLocations).flatMap
        (fun v => initNum ((Iv M x s ℓ H).init v) ::
          domainDescription ((Iv M x s ℓ H).domain v))).length := by
    rw [locsDesc_IvP, List.length_flatMap]
    have h : ∀ v ∈ List.range (Iv M x s ℓ H).numLocations, 2 ^ ℓ ≤
        (((if v = (Loc.code (Loc.accept : Loc M H)).val then 1 else 0) +
          2 * (if v = numLoc M H + 8 * (verifierCmds' M x s ℓ H).length + 3 then 1 else 0)) ::
          ((s + 1) * 2 ^ ℓ) :: (List.range (s + 1)).flatMap fun i =>
            (List.range (2 ^ ℓ)).flatMap fun w => i :: bitsL ℓ w).length := fun v _ => by
      have := two_pow_le_locBlock s ℓ
      simp only [List.length_cons]; omega
    calc (Iv M x s ℓ H).numLocations * 2 ^ ℓ =
          ((List.range (Iv M x s ℓ H).numLocations).map fun _ => 2 ^ ℓ).sum := by simp
      _ ≤ _ := List.sum_le_sum h
  have hpk : pkLen x.length h s ≤ (H + 1) * (H + 1) * 2 ^ ℓ := by
    have h1 := pkLen_le hPar.hx hsh
    have h2 : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
    have h3 : h + 3 ≤ (H + 1) * (H + 1) := by nlinarith
    calc pkLen x.length h s ≤ 2 ^ ℓ + h + 2 := h1
      _ ≤ (h + 3) * 2 ^ ℓ := by nlinarith
      _ ≤ (H + 1) * (H + 1) * 2 ^ ℓ := Nat.mul_le_mul_right _ h3
  have hdesc : ((List.finRange (Iv M x s ℓ H).numLocations).flatMap
        (fun v => initNum ((Iv M x s ℓ H).init v) ::
          domainDescription ((Iv M x s ℓ H).domain v))).length ≤
      (systemDescription (Iv M x s ℓ H)).length := by
    unfold systemDescription
    simp only [List.length_append, List.length_cons]
    omega
  have hW2 : 16 * ((H + 1) * (H + 1)) * 2 ^ ℓ ≤ (Iv M x s ℓ H).numLocations * 2 ^ ℓ :=
    Nat.mul_le_mul_right _ (le_trans hN hW)
  calc 16 * pkLen x.length h s ≤ 16 * ((H + 1) * (H + 1) * 2 ^ ℓ) := Nat.mul_le_mul_left _ hpk
    _ = 16 * ((H + 1) * (H + 1)) * 2 ^ ℓ := by ring
    _ ≤ _ := le_trans hW2 (le_trans hloc hdesc)

/-! ## The machine -/

lemma scP_L_le {n h s : ℕ} (hℓ : pkWidth n h s ≤ h + 1) :
    (scP n h s : ℕ) + 1 ≤ 3 * (h + 3) ^ 2 := by
  have h1 : Nat.log 2 (h + 3) ≤ h + 3 := Nat.log_le_self 2 _
  show (h + 3) ^ 2 + pkWidth n h s + (Nat.log 2 (h + 3) + 5) + 1 ≤ 3 * (h + 3) ^ 2
  nlinarith

lemma two_pow_scP_le {n h s : ℕ} :
    2 ^ (scP n h s).l ≤ 32 * (h + 3) * 2 ^ pkWidth n h s := by
  rw [two_pow_scP]
  have : 2 ^ Nat.log 2 (h + 3) ≤ h + 3 := Nat.pow_log_le_self 2 (by omega)
  calc 2 ^ pkWidth n h s * (32 * 2 ^ Nat.log 2 (h + 3)) ≤ 2 ^ pkWidth n h s * (32 * (h + 3)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ this)
    _ = _ := by ring

lemma κ_boundP (w : ℕ) : κ w + 20 * (2 * w + 1) ≤ 2088 * (w + 3) ^ 2 := by
  simp only [κ, Ex.nodeCost, unitCost]; nlinarith

lemma w3_boundP {K L A w : ℕ} (hL : L + 1 ≤ 3 * A ^ 2) (hw : w = K * (L + 1) + 1)
    (hA : 1 ≤ A) : w + 3 ≤ 3 * (K + 2) * A ^ 2 := by
  have h1 : K * (L + 1) ≤ K * (3 * A ^ 2) := Nat.mul_le_mul_left _ hL
  have h2 : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ hA
  have e : 3 * (K + 2) * A ^ 2 = K * (3 * A ^ 2) + 6 * A ^ 2 := by ring
  rw [hw, e]; omega

lemma cost_boundP {K c A Q X L : ℕ} (hc : c ≤ K * X * (L + 1) ^ 16)
    (hX : X ≤ 32 * A * Q) (hL : L + 1 ≤ 3 * A ^ 2) : c ≤ K * 32 * 3 ^ 16 * Q * A ^ 33 := by
  calc c ≤ K * X * (L + 1) ^ 16 := hc
    _ ≤ K * (32 * A * Q) * (3 * A ^ 2) ^ 16 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hX) (Nat.pow_le_pow_left hL 16)
    _ = _ := by ring

/-- The arithmetic of the time bound. -/
lemma time_arithP {K c w T A Q X L : ℕ} (hc : c ≤ K * X * (L + 1) ^ 16)
    (hX : X ≤ 32 * A * Q) (hL : L + 1 ≤ 3 * A ^ 2) (hw : w = K * (L + 1) + 1) (hA : 1 ≤ A)
    (hQ : 1 ≤ Q) (hT : T ≤ (κ w + 20 * (2 * w + 1)) * c + 4) :
    T ≤ (2088 * (3 * (K + 2)) ^ 2 * (K * 32 * 3 ^ 16) + 4) * Q * A ^ 37 := by
  have hw3 := w3_boundP hL hw hA
  have h1 : κ w + 20 * (2 * w + 1) ≤ 2088 * (3 * (K + 2)) ^ 2 * A ^ 4 := by
    calc _ ≤ 2088 * (w + 3) ^ 2 := κ_boundP w
      _ ≤ 2088 * (3 * (K + 2) * A ^ 2) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw3 2)
      _ = _ := by ring
  have h2 := cost_boundP hc hX hL
  have h4 := Nat.mul_le_mul h1 h2
  have e : 2088 * (3 * (K + 2)) ^ 2 * A ^ 4 * (K * 32 * 3 ^ 16 * Q * A ^ 33) =
      2088 * (3 * (K + 2)) ^ 2 * (K * 32 * 3 ^ 16) * (Q * A ^ 37) := by ring
  rw [e] at h4
  have e2 : (2088 * (3 * (K + 2)) ^ 2 * (K * 32 * 3 ^ 16) + 4) * Q * A ^ 37 =
      2088 * (3 * (K + 2)) ^ 2 * (K * 32 * 3 ^ 16) * (Q * A ^ 37) + 4 * (Q * A ^ 37) := by ring
  rw [e2]
  have h5 : 1 ≤ Q * A ^ 37 := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by positivity))
  generalize 2088 * (3 * (K + 2)) ^ 2 * (K * 32 * 3 ^ 16) * (Q * A ^ 37) = Z at h4 ⊢
  generalize (κ w + 20 * (2 * w + 1)) * c = Y at hT h4
  omega

/-- **The machine of the packed generator.** -/
theorem redGenP_computesWithin (M : Machine) : ∃ C : ℕ, ∀ (x : List Bool) (h s : ℕ),
    2 ≤ x.length → 2 ≤ h → x.length ≤ 2 ^ h → 2 ≤ s → s ≤ h + 2 →
    ComputesWithin (Gn.machine (Gn.redGenP M).need (Gn.redGenP M)) (pkInput x h s)
      (encodeSystem (Iv M x s (pkWidth x.length h s) (pkHorizon x.length h s)))
      (C * 2 ^ pkWidth x.length h s * (h + 3) ^ 37) := by
  obtain ⟨K, hK1, hK⟩ := redGenP_cost M
  refine ⟨2088 * (3 * (K + 2)) ^ 2 * (K * 32 * 3 ^ 16) + 4, fun x h s hx hh hxh hs hsh => ?_⟩
  obtain ⟨hPar, hH⟩ := pk_params hx hh hxh hs
  obtain ⟨hF, hC⟩ := hK x h s hx hh hxh hs hsh
  set σ := scP x.length h s with hσ
  set y := pkInput x h s with hy
  set w := K * ((σ : ℕ) + 1) + 1 with hw
  have hout := out_redGenP (M := M) hx hh hxh hs hsh
  have hB : 2 * 2 ^ (K * ((σ : ℕ) + 1)) ≤ 2 ^ w := by rw [hw, pow_succ]; omega
  have hw2 : 2 ≤ w := by
    have : 1 ≤ K * ((σ : ℕ) + 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega)
      (by omega))
    omega
  have hlen : y.length ≤ (encodeNats ((Gn.redGenP M).out y [])).length := by
    rw [hout, length_pkInput]
    exact le_trans (len_le_descP hx hh hxh hs hsh) (length_le_encodeNatsP _)
  have H := Gn.computesWithin hw2 hB le_rfl (Gn.wfx_redGenP M) hF hlen
  rw [hout] at H
  refine ComputesWithin.mono H ?_
  have henc : (encodeNats (systemDescription (Iv M x s (pkWidth x.length h s)
      (pkHorizon x.length h s)))).length ≤ (Gn.redGenP M).cost y [] * (2 * w + 1) := by
    rw [← hout]
    refine le_trans (length_encodeNats_le (w := w) fun v hv => ?_)
      (Nat.mul_le_mul_right _ (length_out_le_cost _ []))
    have hle : 2 ^ (K * ((σ : ℕ) + 1)) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact lt_of_lt_of_le (lt_of_mem_out _ hF v hv) hle
  rw [← hout] at henc ⊢
  refine time_arithP (c := (Gn.redGenP M).cost y []) (X := 2 ^ σ.l) (L := (σ : ℕ)) hC
    two_pow_scP_le (scP_L_le (le_trans hPar.hℓH hH)) hw (by omega) Nat.one_le_two_pow ?_
  have := Nat.mul_le_mul_left 20 henc
  have e : (κ w + 20 * (2 * w + 1)) * (Gn.redGenP M).cost y [] =
      κ w * (Gn.redGenP M).cost y [] + 20 * ((Gn.redGenP M).cost y [] * (2 * w + 1)) := by ring
  rw [e]
  omega

end Lax119563Proofs.Reduction

end Reduction_PkMachine

/-! ### Formerly `Lax119563Proofs.Compiler.Clauses` -/

section Compiler_Clauses

/-!
# The game and size clauses for reordered matrix graphs

For any reordering `L` of the vertex list of the matrix construction (a list with the same
entries as `vertexList I`), the graphs `reGraph I L ε` (vertex `i` is the `i`-th name of `L`,
adjacency `adjN I ε`, color the position of the first name of the class) satisfy the game,
size and edge clauses of the matrix compiler with the constants of `matrixGraph`
(`reGraph_spec`). This leaves the choice of the vertex order to the construction machine.

* `duplicatorSurvives_of_corr`: Duplicator's survival transfers along a correspondence
  (the transfer lemma `survivesFrom_transfer` is round by round);
* `reEquiv`: the renumbering between two orders, `reCorr`, `numEdges_reGraph`.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs
open Lax119563.PebbleGame Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

set_option linter.unnecessarySimpa false

/-- **Round-bounded transfer.** Duplicator survives `r` rounds on corresponding pairs
simultaneously. -/
theorem duplicatorSurvives_of_corr {n n' m : ℕ} {P : JunkPair n} {Q : JunkPair n'}
    (C : Corr P Q) (r : ℕ) (h : DuplicatorSurvives m r P.G₀ P.G₁) :
    DuplicatorSurvives m r Q.G₀ Q.G₁ :=
  ⟨rfl, survivesFrom_transfer C r _ _
    (fun _ => ⟨fun _ _ h => (by simp at h), fun _ => Or.inl rfl⟩) h.2⟩

theorem duplicatorSurvives_iff_of_corr {n n' m : ℕ} {P : JunkPair n} {Q : JunkPair n'}
    (C : Corr P Q) (r : ℕ) :
    DuplicatorSurvives m r P.G₀ P.G₁ ↔ DuplicatorSurvives m r Q.G₀ Q.G₁ :=
  ⟨duplicatorSurvives_of_corr C r, duplicatorSurvives_of_corr C.symm r⟩

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The matrix graph `G_ε` with its vertices in the order of `L`. -/
abbrev reGraph (L : List (VName I)) (ε : ZMod 2) : ColoredGraph :=
  listGraph L (adjN I ε) (adjN_symm I ε) (adjN_irrefl I ε) Prod.fst

/-- The reordered graphs as a pair without junk. -/
noncomputable def rePair (L : List (VName I)) : JunkPair L.length where
  A₀ := (reGraph I L 0).graph
  A₁ := (reGraph I L 1).graph
  χ := (reGraph I L 0).color
  J := fun _ => False
  iso₀ := fun _ _ h => h.elim
  iso₁ := fun _ _ h => h.elim
  col := fun _ _ h => h.elim

variable {I}

/-- The renumbering between two duplicate-free orders of the same names. -/
noncomputable def reEquiv {L L' : List (VName I)} (hL : L.Nodup) (hL' : L'.Nodup)
    (hp : L.Perm L') : Fin L.length ≃ Fin L'.length :=
  (hL.getEquiv L).trans ((Equiv.subtypeEquivRight fun _ => hp.mem_iff).trans
    (hL'.getEquiv L').symm)

lemma reEquiv_get {L L' : List (VName I)} (hL : L.Nodup) (hL' : L'.Nodup) (hp : L.Perm L')
    (i : Fin L.length) : L'[(reEquiv hL hL' hp i : ℕ)] = L[(i : ℕ)] := by
  have h := (hL'.getEquiv L').apply_symm_apply
    ((Equiv.subtypeEquivRight fun _ => hp.mem_iff) (hL.getEquiv L i))
  have h' := congrArg Subtype.val h
  simpa [reEquiv, List.Nodup.getEquiv] using h'

/-- The correspondence between two orders. -/
noncomputable def reCorr {L L' : List (VName I)} (hL : L.Nodup) (hL' : L'.Nodup)
    (hp : L.Perm L') : Corr (rePair I L) (rePair I L') where
  f :=
    { toFun := fun u => ⟨reEquiv hL hL' hp u.1, not_false⟩
      invFun := fun v => ⟨(reEquiv hL hL' hp).symm v.1, not_false⟩
      left_inv := fun u => by simp
      right_inv := fun v => by simp }
  adj₀ u v := by
    show adjN I 0 L[(u.1 : ℕ)] L[(v.1 : ℕ)] ↔
      adjN I 0 L'[(reEquiv hL hL' hp u.1 : ℕ)] L'[(reEquiv hL hL' hp v.1 : ℕ)]
    rw [reEquiv_get, reEquiv_get]
  adj₁ u v := by
    show adjN I 1 L[(u.1 : ℕ)] L[(v.1 : ℕ)] ↔
      adjN I 1 L'[(reEquiv hL hL' hp u.1 : ℕ)] L'[(reEquiv hL hL' hp v.1 : ℕ)]
    rw [reEquiv_get, reEquiv_get]
  col u v := by
    show (reGraph I L 0).color u.1 = (reGraph I L 0).color v.1 ↔
      (reGraph I L' 0).color (reEquiv hL hL' hp u.1) =
        (reGraph I L' 0).color (reEquiv hL hL' hp v.1)
    rw [listGraph_color_eq_iff, listGraph_color_eq_iff, reEquiv_get, reEquiv_get]

/-- Reordering preserves the number of edges. -/
lemma numEdges_reGraph {L L' : List (VName I)} (hL : L.Nodup) (hL' : L'.Nodup)
    (hp : L.Perm L') (ε : ZMod 2) : (reGraph I L ε).numEdges = (reGraph I L' ε).numEdges := by
  let e : (reGraph I L ε).graph ≃g (reGraph I L' ε).graph :=
    { toEquiv := reEquiv hL hL' hp
      map_rel_iff' := by
        intro a b
        show adjN I ε L'[((reEquiv hL hL' hp) a : ℕ)] L'[((reEquiv hL hL' hp) b : ℕ)] ↔
          adjN I ε L[(a : ℕ)] L[(b : ℕ)]
        rw [reEquiv_get, reEquiv_get] }
  exact Nat.card_congr e.mapEdgeSet

/-- **The clauses for every reordering of the vertex list.** -/
theorem reGraph_spec (hk : 3 ≤ k) (L : List (VName I)) (hp : L.Perm (vertexList I)) :
    (∀ τ : ℕ, I.conflictRound = τ →
      SpoilerWinsWithin (k + 1) ((2 * k + stepConst k) * Λ I * (τ + 1))
        (reGraph I L 0) (reGraph I L 1)) ∧
    (∀ r : ℕ, (r : ℕ∞) + 1 ≤ I.conflictRound →
      DuplicatorSurvives (k + 1) r (reGraph I L 0) (reGraph I L 1)) ∧
    (reGraph I L 0).n + (reGraph I L 1).n ≤ 32 * matrixSize I ∧
    (reGraph I L 0).numEdges + (reGraph I L 1).numEdges ≤
      3 * ((reGraph I L 0).n + (reGraph I L 1).n) := by
  have hV := nodup_vertexList I
  have hL : L.Nodup := hp.nodup_iff.mpr hV
  have C := reCorr hV hL hp.symm
  have hlen : L.length = nV I := hp.length_eq
  have hnV : nV I = (vertexList I).length := rfl
  refine ⟨fun τ hτ hD => spoilerWins (by omega) hτ ((duplicatorSurvives_iff_of_corr C _).mpr hD),
    fun r hr => (duplicatorSurvives_iff_of_corr C r).mp
      (duplicatorSurvives (by omega) (not_hasConflict_of_lt I hr)), ?_, ?_⟩
  · show L.length + L.length ≤ 32 * matrixSize I
    have := card_vertexList_le (I := I) (by omega)
    omega
  · rw [numEdges_reGraph hL hV hp 0, numEdges_reGraph hL hV hp 1]
    have h0 : (reGraph I (vertexList I) 0).numEdges ≤ 3 * nV I := numEdges_le (I := I) 0
    have h1 : (reGraph I (vertexList I) 1).numEdges ≤ 3 * nV I := numEdges_le (I := I) 1
    show _ ≤ 3 * (L.length + L.length)
    omega

end Lax119563Proofs.Compiler

end Compiler_Clauses

/-! ### Formerly `Lax119563Proofs.Compiler.NLe` -/

section Compiler_NLe

/-!
# Runs of register programs with number stacks within a cost

* `NLe x w p st st' T`: `p` runs from `st` to `st'` within cost `T` (with the combinators of
  `Reduction.HLe`);
* `NSt.Bdd w st`: all registers and all stack entries are below `2 ^ w`, kept by runs
  (`NLe.bounded`);
* `HProg.toN`: the embedding of register programs without stacks (`HLe.toN`), so that the
  expression compiler `Reduction.Ex.code` can be reused.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

/-- `p` runs from `st` to `st'` within cost `T`. -/
def NLe (x : List Bool) (w : ℕ) (p : NProg R Q) (st st' : NSt R Q) (T : ℕ) : Prop :=
  ∃ t ≤ T, NRuns x w p st st' t

namespace NLe

variable {p q : NProg R Q} {st st' st₁ st₂ st₃ : NSt R Q} {T T' T₁ T₂ : ℕ}

lemma of_runs {t : ℕ} (h : NRuns x w p st st' t) : NLe x w p st st' t := ⟨t, le_rfl, h⟩

lemma mono (h : NLe x w p st st' T) (hT : T ≤ T') : NLe x w p st st' T' := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t, by omega, h⟩

lemma seq (h₁ : NLe x w p st₁ st₂ T₁) (h₂ : NLe x w q st₂ st₃ T₂) :
    NLe x w (.seq p q) st₁ st₃ (T₁ + T₂) := by
  obtain ⟨t₁, ht₁, h₁⟩ := h₁; obtain ⟨t₂, ht₂, h₂⟩ := h₂
  exact ⟨t₁ + t₂, by omega, .seq h₁ h₂⟩

lemma iteT {c} (hc : c st.view = true) (h : NLe x w p st st' T) :
    NLe x w (.ite c p q) st st' (T + 1) := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t + 1, by omega, .iteT hc h⟩

lemma iteF {c} (hc : c st.view = false) (h : NLe x w q st st' T) :
    NLe x w (.ite c p q) st st' (T + 1) := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t + 1, by omega, .iteF hc h⟩

lemma loopF {c} (hc : c st.view = false) : NLe x w (.loop c p) st st 1 := of_runs (.loopF hc)

lemma loopT {c} (hc : c st₁.view = true) (h₁ : NLe x w p st₁ st₂ T₁)
    (h₂ : NLe x w (.loop c p) st₂ st₃ T₂) : NLe x w (.loop c p) st₁ st₃ (T₁ + T₂ + 1) := by
  obtain ⟨t₁, ht₁, h₁⟩ := h₁; obtain ⟨t₂, ht₂, h₂⟩ := h₂
  exact ⟨t₁ + t₂ + 1, by omega, .loopT hc h₁ h₂⟩

end NLe

/-! ## Bounded states -/

/-- All registers and all stack entries are below `2 ^ w`. -/
def NSt.Bdd (w : ℕ) (st : NSt R Q) : Prop :=
  (∀ r, st.env r < 2 ^ w) ∧ ∀ q, ∀ v ∈ st.stk q, v < 2 ^ w

lemma NRuns.bounded {p : NProg R Q} {st st' : NSt R Q} {t : ℕ} (h : NRuns x w p st st' t)
    (hw : 2 ≤ w) (hb : st.Bdd w) : st'.Bdd w := by
  have h2 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have h4 : (4 : ℕ) ≤ 2 ^ w := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  induction h with
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hb)
  | iteT _ _ ih => exact ih hb
  | iteF _ _ ih => exact ih hb
  | loopF => exact hb
  | loopT _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ hb)
  | emit => exact hb
  | rst => exact hb
  | clr =>
    refine ⟨fun q => ?_, hb.2⟩; simp only [NSt.set_env, Function.update_apply]; split_ifs
    · positivity
    · exact hb.1 q
  | one h' =>
    refine ⟨fun q => ?_, hb.2⟩; simp only [NSt.set_env, Function.update_apply]; split_ifs
    · exact h'
    · exact hb.1 q
  | dbl h' =>
    refine ⟨fun q => ?_, hb.2⟩; simp only [NSt.set_env, Function.update_apply]; split_ifs
    · exact h'
    · exact hb.1 q
  | half h' =>
    refine ⟨fun q => ?_, hb.2⟩; simp only [NSt.set_env, Function.update_apply]; split_ifs
    · exact lt_of_le_of_lt (Nat.div_le_self _ _) h'
    · exact hb.1 q
  | copy _ h' =>
    refine ⟨fun q => ?_, hb.2⟩; simp only [NSt.set_env, Function.update_apply]; split_ifs
    · exact h'
    · exact hb.1 q
  | add _ h' =>
    refine ⟨fun q => ?_, hb.2⟩; simp only [NSt.set_env, Function.update_apply]; split_ifs
    · exact h'
    · exact hb.1 q
  | lt =>
    refine ⟨fun q => ?_, hb.2⟩; simp only [NSt.set_env, Function.update_apply]; split_ifs
    · omega
    · omega
    · exact hb.1 q
  | rd =>
    refine ⟨fun q => ?_, hb.2⟩; simp only [NSt.set_env, Function.update_apply]; split_ifs
    · exact lt_of_le_of_lt (inBit_le _ _) (by omega)
    · exact hb.1 q
  | @spush q r st h' =>
    refine ⟨hb.1, fun q' v hv => ?_⟩
    simp only [NSt.setS_stk, Function.update_apply] at hv
    split_ifs at hv with hq
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact h'
      · subst hq; exact hb.2 _ v hv
    · exact hb.2 q' v hv
  | @spop q r st v vs _ hs hv =>
    refine ⟨fun r' => ?_, fun q' u hu => ?_⟩
    · simp only [NSt.set_env, NSt.setS_env, Function.update_apply]; split_ifs
      · exact hv
      · exact hb.1 r'
    · simp only [NSt.set_stk, NSt.setS_stk, Function.update_apply] at hu
      split_ifs at hu with hq
      · subst hq; exact hb.2 _ u (by rw [hs]; exact List.mem_cons_of_mem _ hu)
      · exact hb.2 q' u hu

lemma NLe.bounded {p : NProg R Q} {st st' : NSt R Q} {T : ℕ} (h : NLe x w p st st' T)
    (hw : 2 ≤ w) (hb : st.Bdd w) : st'.Bdd w := by
  obtain ⟨t, -, h⟩ := h; exact h.bounded hw hb

lemma NLe.pos_le {p : NProg R Q} {st st' : NSt R Q} {T : ℕ} (h : NLe x w p st st' T)
    (hp : st.pos ≤ x.length) : st'.pos ≤ x.length := by
  obtain ⟨t, -, h⟩ := h; exact h.pos_le hp

/-! ## Embedding programs without stacks -/

/-- A program without stacks as a program with stacks. -/
def _root_.Lax119563Proofs.Reduction.HProg.toN : HProg R → NProg R Q
  | .clr r => .clr r
  | .one r => .one r
  | .dbl r => .dbl r
  | .half r => .half r
  | .copy r s => .copy r s
  | .add r s => .add r s
  | .lt f a b => .lt f a b
  | .emit r => .emit r
  | .rd r => .rd r
  | .rst => .rst
  | .seq p q => .seq p.toN q.toN
  | .ite c p q => .ite (fun v => c v.1) p.toN q.toN
  | .loop c p => .loop (fun v => c v.1) p.toN

/-- The register part of a state. -/
def NSt.toH (st : NSt R Q) : HSt R := ⟨st.env, st.pos, st.out⟩

/-- A register state with stacks. -/
def NSt.ofH (st : HSt R) (S : Fin Q → List ℕ) : NSt R Q := ⟨st.env, S, st.pos, st.out⟩

@[simp] lemma NSt.ofH_toH (st : NSt R Q) : NSt.ofH st.toH st.stk = st := rfl
@[simp] lemma NSt.toH_env (st : NSt R Q) : st.toH.env = st.env := rfl
@[simp] lemma NSt.toH_pos (st : NSt R Q) : st.toH.pos = st.pos := rfl
@[simp] lemma NSt.toH_out (st : NSt R Q) : st.toH.out = st.out := rfl
@[simp] lemma NSt.ofH_env (st : HSt R) (S : Fin Q → List ℕ) : (NSt.ofH st S).env = st.env := rfl
@[simp] lemma NSt.ofH_stk (st : HSt R) (S : Fin Q → List ℕ) : (NSt.ofH st S).stk = S := rfl
@[simp] lemma NSt.ofH_pos (st : HSt R) (S : Fin Q → List ℕ) : (NSt.ofH st S).pos = st.pos := rfl
@[simp] lemma NSt.ofH_out (st : HSt R) (S : Fin Q → List ℕ) : (NSt.ofH st S).out = st.out := rfl

lemma _root_.Lax119563Proofs.Reduction.HRuns.toN {p : HProg R} {st st' : HSt R} {t : ℕ} (h : HRuns x w p st st' t)
    (S : Fin Q → List ℕ) : NRuns x w p.toN (NSt.ofH st S) (NSt.ofH st' S) t := by
  induction h with
  | clr h => exact NRuns.clr (st := NSt.ofH _ S) h
  | one h => exact NRuns.one (st := NSt.ofH _ S) h
  | dbl h => exact NRuns.dbl (st := NSt.ofH _ S) h
  | half h => exact NRuns.half (st := NSt.ofH _ S) h
  | copy h1 h2 h3 => exact NRuns.copy (st := NSt.ofH _ S) h1 h2 h3
  | add h1 h2 => exact NRuns.add (st := NSt.ofH _ S) h1 h2
  | lt h1 h2 h3 h4 h5 h6 => exact NRuns.lt (st := NSt.ofH _ S) h1 h2 h3 h4 h5 h6
  | emit h => exact NRuns.emit (st := NSt.ofH _ S) h
  | rd h1 h2 => exact NRuns.rd (st := NSt.ofH _ S) h1 h2
  | rst h => exact NRuns.rst (st := NSt.ofH _ S) h
  | seq _ _ ih₁ ih₂ => exact NRuns.seq ih₁ ih₂
  | @iteT c _ _ _ _ _ hc _ ih => exact NRuns.iteT (c := fun v => c v.1) hc ih
  | @iteF c _ _ _ _ _ hc _ ih => exact NRuns.iteF (c := fun v => c v.1) hc ih
  | @loopF c _ _ hc => exact NRuns.loopF (c := fun v => c v.1) hc
  | @loopT c _ _ _ _ _ _ hc _ _ ih₁ ih₂ => exact NRuns.loopT (c := fun v => c v.1) hc ih₁ ih₂

lemma _root_.Lax119563Proofs.Reduction.HLe.toN {p : HProg R} {st : NSt R Q} {st' : HSt R} {T : ℕ} (h : HLe x w p st.toH st' T) :
    NLe x w p.toN st (NSt.ofH st' st.stk) T := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t, ht, h.toN st.stk⟩

lemma NSt.Bdd.toH {st : NSt R Q} (h : st.Bdd w) : st.toH.Bdd w := h.1

end Lax119563Proofs.Compiler

end Compiler_NLe

/-! ### Formerly `Lax119563Proofs.Compiler.CStm` -/

section Compiler_CStm

/-!
# Structured statements with number stacks

A layer above `NProg` with a total denotational semantics, so that the programs of the
compiler are proved correct by list mathematics.

Statements `CStm R Q` over user registers `Fin R` and number stacks `Fin Q`:
`skip`, `set r e`, `emit e`, `push q e`, `pop q r` (`r :=` the top of `q`, or `0` if `q` is
empty; pop), `sne r q` (`r := [q nonempty]`), `rd r` (`r :=` the input value at the cursor,
advance), `rst`, sequencing, `ite c p q` (`c ≠ 0`) and while loops `loop c body`.

`CStm.exec x c st` is the final state; a loop runs for the least number of iterations after
which its condition is `0` (and is the identity if there is none). `CStm.cost x w c st` is a
cost bound and `CStm.Fits x w c st` says that all expression values stay below `2 ^ w` and
that all loops terminate. `CStm.code R D c : NProg (R + D + 1) Q` compiles a statement with
`D + 1` scratch registers (`CStm.code_spec`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q D : ℕ} {x : List Bool} {w : ℕ}

/-- Structured statements. -/
inductive CStm (R Q : ℕ) where
  | skip
  | set (r : Fin R) (e : Ex R)
  | emit (e : Ex R)
  | push (q : Fin Q) (e : Ex R)
  | pop (q : Fin Q) (r : Fin R)
  | sne (r : Fin R) (q : Fin Q)
  | rd (r : Fin R)
  | rst
  | seq (p q : CStm R Q)
  | ite (c : Ex R) (p q : CStm R Q)
  | loop (c : Ex R) (body : CStm R Q)

namespace CStm

open Classical in
/-- The denotation. -/
noncomputable def exec (x : List Bool) : CStm R Q → NSt R Q → NSt R Q
  | skip, st => st
  | set r e, st => st.set r (e.eval st.env)
  | emit e, st => { st with out := st.out ++ [e.eval st.env] }
  | push q e, st => st.setS q (e.eval st.env :: st.stk q)
  | pop q r, st => (st.setS q (st.stk q).tail).set r ((st.stk q).headD 0)
  | sne r q, st => st.set r (if (st.stk q).isEmpty then 0 else 1)
  | rd r, st => { (st.set r (inBit x st.pos)) with pos := min (st.pos + 1) x.length }
  | rst, st => { st with pos := 0 }
  | seq p q, st => exec x q (exec x p st)
  | ite c p q, st => if c.eval st.env ≠ 0 then exec x p st else exec x q st
  | loop c body, st =>
    if h : ∃ n, c.eval ((exec x body)^[n] st).env = 0 then (exec x body)^[Nat.find h] st else st

/-- The `n`-th iterate of a loop body. -/
noncomputable abbrev iter (x : List Bool) (body : CStm R Q) (st : NSt R Q) (n : ℕ) : NSt R Q :=
  (exec x body)^[n] st

/-- The cost of evaluating the condition of a loop or conditional. -/
def condCost (w : ℕ) (c : Ex R) : ℕ := c.size * Ex.nodeCost w + 1

open Classical in
/-- A cost bound. -/
noncomputable def cost (x : List Bool) (w : ℕ) : CStm R Q → NSt R Q → ℕ
  | skip, _ => unitCost w
  | set _ e, _ => e.size * Ex.nodeCost w + unitCost w
  | emit e, _ => e.size * Ex.nodeCost w + unitCost w
  | push _ e, _ => e.size * Ex.nodeCost w + unitCost w
  | pop _ _, _ => unitCost w + 1
  | sne _ _, _ => 2 * unitCost w + 1
  | rd _, _ => unitCost w
  | rst, st => unitCost w * (st.pos + 1)
  | seq p q, st => cost x w p st + cost x w q (exec x p st)
  | ite c p q, st => condCost w c + (if c.eval st.env ≠ 0 then cost x w p st else cost x w q st)
  | loop c body, st =>
    if h : ∃ n, c.eval ((exec x body)^[n] st).env = 0 then
      ∑ j ∈ Finset.range (Nat.find h), (cost x w body ((exec x body)^[j] st) + condCost w c) +
        condCost w c
    else 0

/-- All values stay below `2 ^ w` and all loops terminate. -/
def Fits (x : List Bool) (w : ℕ) : CStm R Q → NSt R Q → Prop
  | skip, _ => True
  | set _ e, st => e.Fits w st.env
  | emit e, st => e.Fits w st.env
  | push _ e, st => e.Fits w st.env
  | pop _ _, _ => True
  | sne _ _, _ => True
  | rd _, _ => True
  | rst, _ => True
  | seq p q, st => Fits x w p st ∧ Fits x w q (exec x p st)
  | ite c p q, st => c.Fits w st.env ∧
      (if c.eval st.env ≠ 0 then Fits x w p st else Fits x w q st)
  | loop c body, st => ∃ n, c.eval ((exec x body)^[n] st).env = 0 ∧
      (∀ j < n, c.eval ((exec x body)^[j] st).env ≠ 0 ∧ Fits x w body ((exec x body)^[j] st)) ∧
      ∀ j ≤ n, c.Fits w ((exec x body)^[j] st).env

/-- The number of scratch registers needed. -/
def depth : CStm R Q → ℕ
  | skip => 1
  | set _ e => e.depth
  | emit e => e.depth
  | push _ e => e.depth
  | pop _ _ => 1
  | sne _ _ => 1
  | rd _ => 1
  | rst => 1
  | seq p q => max (depth p) (depth q)
  | ite c p q => max c.depth (max (depth p) (depth q))
  | loop c body => max c.depth (depth body)

/-- The condition of a compiled conditional or loop: scratch register `0` is nonzero. -/
def scTest (R D : ℕ) (Q : ℕ) : NView (R + D + 1) Q → Bool := fun v => (v.1 (sc R D 0)).isSome

/-- Compilation to `NProg` with scratch registers `R, …, R + D`. -/
def code (R D : ℕ) : CStm R Q → NProg (R + D + 1) Q
  | skip => .clr (sc R D 0)
  | set r e => .seq (HProg.toN (e.code R D 0)) (.copy (sc R D 0) (ur D r))
  | emit e => .seq (HProg.toN (e.code R D 0)) (.emit (sc R D 0))
  | push q e => .seq (HProg.toN (e.code R D 0)) (.spush q (sc R D 0))
  | pop q r => .ite (fun v => v.2 q) (.spop q (ur D r)) (.clr (ur D r))
  | sne r q => .ite (fun v => v.2 q) (.seq (.clr (ur D r)) (.one (ur D r))) (.clr (ur D r))
  | rd r => .rd (ur D r)
  | rst => .rst
  | seq p q => .seq (code R D p) (code R D q)
  | ite c p q => .seq (HProg.toN (c.code R D 0)) (.ite (scTest R D Q) (code R D p) (code R D q))
  | loop c body => .seq (HProg.toN (c.code R D 0))
      (.loop (scTest R D Q) (.seq (code R D body) (HProg.toN (c.code R D 0))))

/-! ## Loops -/

open Classical in
lemma exec_loop {c : Ex R} {body : CStm R Q} {st : NSt R Q} {n : ℕ}
    (hn : c.eval (iter x body st n).env = 0) (hlt : ∀ j < n, c.eval (iter x body st j).env ≠ 0) :
    exec x (loop c body) st = iter x body st n := by
  have h : ∃ n, c.eval ((exec x body)^[n] st).env = 0 := ⟨n, hn⟩
  have e : Nat.find h = n := (Nat.find_eq_iff h).mpr ⟨hn, fun j hj => hlt j hj⟩
  simp only [exec, dif_pos h, e]

open Classical in
lemma cost_loop {c : Ex R} {body : CStm R Q} {st : NSt R Q} {n : ℕ}
    (hn : c.eval (iter x body st n).env = 0) (hlt : ∀ j < n, c.eval (iter x body st j).env ≠ 0) :
    cost x w (loop c body) st =
      ∑ j ∈ Finset.range n, (cost x w body (iter x body st j) + condCost w c) + condCost w c := by
  have h : ∃ n, c.eval ((exec x body)^[n] st).env = 0 := ⟨n, hn⟩
  have e : Nat.find h = n := (Nat.find_eq_iff h).mpr ⟨hn, fun j hj => hlt j hj⟩
  simp only [cost, dif_pos h, e]

lemma iter_succ (body : CStm R Q) (st : NSt R Q) (n : ℕ) :
    iter x body st (n + 1) = exec x body (iter x body st n) :=
  Function.iterate_succ_apply' _ _ _

lemma iter_zero (body : CStm R Q) (st : NSt R Q) : iter x body st 0 = st := rfl

end CStm

/-! ## Correspondence between compiled and source states -/

/-- The compiled state `st` represents the source state `σ`. -/
def CCorr (D : ℕ) (st : NSt (R + D + 1) Q) (σ : NSt R Q) : Prop :=
  uenv D st.toH = σ.env ∧ st.stk = σ.stk ∧ st.pos = σ.pos ∧ st.out = σ.out

lemma uenv_set_ur' (st : NSt (R + D + 1) Q) (r : Fin R) (v : ℕ) :
    uenv D (st.set (ur D r) v).toH = Function.update (uenv D st.toH) r v :=
  uenv_set_ur st.toH r v

/-- Evaluating an expression into scratch register `0`. -/
lemma ex_code_N (hw : 2 ≤ w) (e : Ex R) (st : NSt (R + D + 1) Q) (hd : e.depth ≤ D)
    (hb : st.Bdd w) (hf : e.Fits w (uenv D st.toH)) :
    ∃ st₁ : NSt (R + D + 1) Q, NLe x w (HProg.toN (e.code R D 0)) st st₁ (e.size * Ex.nodeCost w) ∧
      st₁.env (sc R D 0) = e.eval (uenv D st.toH) ∧ uenv D st₁.toH = uenv D st.toH ∧
      st₁.stk = st.stk ∧ st₁.pos = st.pos ∧ st₁.out = st.out ∧ st₁.Bdd w := by
  obtain ⟨h₁, r₁, e₁⟩ := Ex.code_spec (x := x) hw e 0 st.toH (by omega) hb.toH hf
  have r₁' := r₁.toN (Q := Q) (st := st)
  refine ⟨_, r₁', e₁, Ex.code_uenv r₁, rfl, r₁.pos_eq (Ex.code_mv e 0),
    r₁.out_eq (Ex.code_em e 0), r₁'.bounded hw hb⟩

namespace CStm

/-- **Compilation of statements.** -/
theorem code_spec (hw : 2 ≤ w) : ∀ (c : CStm R Q) (σ : NSt R Q) (st : NSt (R + D + 1) Q),
    depth c ≤ D → Fits x w c σ → CCorr D st σ → st.Bdd w → st.pos ≤ x.length →
    ∃ st', NLe x w (code R D c) st st' (cost x w c σ) ∧ CCorr D st' (exec x c σ)
  | skip, σ, st, _, _, hc, hb, _ => by
    refine ⟨_, NLe.of_runs (NRuns.clr (hb.1 _)), ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := hc
    exact ⟨(uenv_set_sc st.toH 0 0).trans h1, h2, h3, h4⟩
  | set r e, σ, st, hd, hf, hc, hb, _ => by
    obtain ⟨h1, h2, h3, h4⟩ := hc
    obtain ⟨st₁, r₁, e₁, u₁, s₁, p₁, o₁, b₁⟩ :=
      ex_code_N (x := x) hw e st (by simpa [depth] using hd) hb (by rw [h1]; exact hf)
    refine ⟨_, r₁.seq (NLe.of_runs (NRuns.copy (sc_ne_ur r 0) (b₁.1 _) (b₁.1 _))), ?_, ?_, ?_, ?_⟩
    · rw [uenv_set_ur', u₁, e₁, h1]; rfl
    · simpa [exec] using s₁.trans h2
    · simpa [exec] using p₁.trans h3
    · simpa [exec] using o₁.trans h4
  | emit e, σ, st, hd, hf, hc, hb, _ => by
    obtain ⟨h1, h2, h3, h4⟩ := hc
    obtain ⟨st₁, r₁, e₁, u₁, s₁, p₁, o₁, b₁⟩ :=
      ex_code_N (x := x) hw e st (by simpa [depth] using hd) hb (by rw [h1]; exact hf)
    refine ⟨_, r₁.seq (NLe.of_runs (NRuns.emit (b₁.1 _))), ?_, ?_, ?_, ?_⟩
    · exact u₁.trans h1
    · simpa [exec] using s₁.trans h2
    · simpa [exec] using p₁.trans h3
    · simp [exec, o₁, h4, e₁, h1]
  | push q e, σ, st, hd, hf, hc, hb, _ => by
    obtain ⟨h1, h2, h3, h4⟩ := hc
    obtain ⟨st₁, r₁, e₁, u₁, s₁, p₁, o₁, b₁⟩ :=
      ex_code_N (x := x) hw e st (by simpa [depth] using hd) hb (by rw [h1]; exact hf)
    refine ⟨_, r₁.seq (NLe.of_runs (NRuns.spush (b₁.1 _))), ?_, ?_, ?_, ?_⟩
    · exact u₁.trans h1
    · simp [exec, s₁, h2, e₁, h1]
    · simpa [exec] using p₁.trans h3
    · simpa [exec] using o₁.trans h4
  | pop q r, σ, st, _, _, hc, hb, _ => by
    obtain ⟨h1, h2, h3, h4⟩ := hc
    rcases hq : st.stk q with _ | ⟨v, vs⟩
    · have hv : (fun v : NView (R + D + 1) Q => v.2 q) st.view = false := by
        simp [NSt.view, hq]
      refine ⟨_, (NLe.iteF hv (NLe.of_runs (NRuns.clr (hb.1 _)))).mono (by simp [cost]), ?_⟩
      have hσ : σ.stk q = [] := by rw [← h2, hq]
      refine ⟨?_, ?_, h3, h4⟩
      · rw [uenv_set_ur', h1]; simp [exec, hσ]
      · simp [exec, hσ, h2]
    · have hv : (fun v : NView (R + D + 1) Q => v.2 q) st.view = true := by
        simp [NSt.view, hq]
      have hvb : v < 2 ^ w := hb.2 q v (by rw [hq]; exact List.mem_cons_self ..)
      refine ⟨_, (NLe.iteT hv (NLe.of_runs (NRuns.spop (hb.1 _) hq hvb))).mono
        (by simp [cost]), ?_⟩
      have hσ : σ.stk q = v :: vs := by rw [← h2, hq]
      refine ⟨?_, ?_, h3, h4⟩
      · show uenv D ((st.setS q vs).set (ur D r) v).toH = _
        rw [uenv_set_ur']
        show Function.update (uenv D st.toH) r v = _
        rw [h1]; simp [exec, hσ]
      · simp [exec, hσ, h2]
  | sne r q, σ, st, _, _, hc, hb, _ => by
    obtain ⟨h1, h2, h3, h4⟩ := hc
    have h2w : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
    rcases hq : st.stk q with _ | ⟨v, vs⟩
    · have hv : (fun v : NView (R + D + 1) Q => v.2 q) st.view = false := by
        simp [NSt.view, hq]
      refine ⟨_, (NLe.iteF hv (NLe.of_runs (NRuns.clr (hb.1 _)))).mono
        (by simp only [cost]; omega), ?_⟩
      have hσ : σ.stk q = [] := by rw [← h2, hq]
      refine ⟨?_, h2, h3, h4⟩
      rw [uenv_set_ur', h1]; simp [exec, hσ]
    · have hv : (fun v : NView (R + D + 1) Q => v.2 q) st.view = true := by
        simp [NSt.view, hq]
      have r₁ := NLe.of_runs (x := x) (NRuns.clr (w := w) (r := ur D r) (st := st) (hb.1 _))
      have r₂ := NLe.of_runs (x := x) (NRuns.one (w := w) (r := ur D r)
        (st := st.set (ur D r) 0) (by simp; omega))
      refine ⟨_, (NLe.iteT hv (r₁.seq r₂)).mono (by simp only [cost]; omega), ?_⟩
      have hσ : σ.stk q = v :: vs := by rw [← h2, hq]
      refine ⟨?_, h2, h3, h4⟩
      show uenv D ((st.set (ur D r) 0).set (ur D r) (2 * (st.set (ur D r) 0).env (ur D r) + 1)).toH = _
      rw [uenv_set_ur', uenv_set_ur', h1]; simp [exec, hσ]
  | rd r, σ, st, _, _, hc, hb, hp => by
    obtain ⟨h1, h2, h3, h4⟩ := hc
    refine ⟨_, NLe.of_runs (NRuns.rd (hb.1 _) hp), ?_, ?_, ?_, ?_⟩
    · show uenv D (st.set (ur D r) (inBit x st.pos)).toH = _
      rw [uenv_set_ur', h1, h3]; rfl
    · simpa [exec] using h2
    · simp [exec, h3]
    · simpa [exec] using h4
  | rst, σ, st, _, _, hc, hb, hp => by
    obtain ⟨h1, h2, h3, h4⟩ := hc
    refine ⟨_, (NLe.of_runs (NRuns.rst hp)).mono (by simp [cost, h3]), h1, h2, rfl, h4⟩
  | seq p q, σ, st, hd, hf, hc, hb, hp => by
    simp only [depth, max_le_iff] at hd
    obtain ⟨st₁, r₁, c₁⟩ := code_spec hw p σ st hd.1 hf.1 hc hb hp
    obtain ⟨st₂, r₂, c₂⟩ := code_spec hw q _ st₁ hd.2 hf.2 c₁ (r₁.bounded hw hb) (r₁.pos_le hp)
    exact ⟨st₂, r₁.seq r₂, c₂⟩
  | ite c p q, σ, st, hd, hf, hc, hb, hp => by
    simp only [depth, max_le_iff] at hd
    obtain ⟨h1, h2, h3, h4⟩ := hc
    obtain ⟨st₁, r₁, e₁, u₁, s₁, p₁, o₁, b₁⟩ :=
      ex_code_N (x := x) hw c st hd.1 hb (by rw [h1]; exact hf.1)
    have c₁ : CCorr D st₁ σ := ⟨u₁.trans h1, s₁.trans h2, p₁.trans h3, o₁.trans h4⟩
    have hp₁ : st₁.pos ≤ x.length := by rw [p₁]; exact hp
    by_cases hcv : c.eval σ.env ≠ 0
    · have hf' : Fits x w p σ := by have := hf.2; rw [if_pos hcv] at this; exact this
      obtain ⟨st₂, r₂, c₂⟩ := code_spec hw p σ st₁ hd.2.1 hf' c₁ b₁ hp₁
      have hv : scTest R D Q st₁.view = true := by
        show (st₁.toH.view (sc R D 0)).isSome = true
        rw [HSt.view_isSome_iff]; simp only [NSt.toH_env]; rw [e₁, h1]; exact hcv
      refine ⟨st₂, (r₁.seq (NLe.iteT hv r₂)).mono ?_, ?_⟩
      · simp only [cost, condCost, if_pos hcv]; omega
      · simp only [exec, if_pos hcv]; exact c₂
    · have hf' : Fits x w q σ := by have := hf.2; rw [if_neg hcv] at this; exact this
      obtain ⟨st₂, r₂, c₂⟩ := code_spec hw q σ st₁ hd.2.2 hf' c₁ b₁ hp₁
      have hv : scTest R D Q st₁.view = false := by
        show (st₁.toH.view (sc R D 0)).isSome = false
        rw [← Bool.not_eq_true, HSt.view_isSome_iff]; simp only [NSt.toH_env]
        rw [e₁, h1]; exact hcv
      refine ⟨st₂, (r₁.seq (NLe.iteF hv r₂)).mono ?_, ?_⟩
      · simp only [cost, condCost, if_neg hcv]; omega
      · simp only [exec, if_neg hcv]; exact c₂
  | loop c body, σ, st, hd, hf, hc, hb, hp => by
    simp only [depth, max_le_iff] at hd
    obtain ⟨n, hn, hlt, hcf⟩ := hf
    rw [exec_loop hn (fun j hj => (hlt j hj).1), cost_loop hn (fun j hj => (hlt j hj).1)]
    set it := iter x body σ
    set P : NProg (R + D + 1) Q := .seq (code R D body) (HProg.toN (c.code R D 0))
    -- the loop from iteration `m` on
    have aux : ∀ d m (τ : NSt (R + D + 1) Q), m + d = n → CCorr D τ (it m) → τ.Bdd w →
        τ.pos ≤ x.length → τ.env (sc R D 0) = c.eval (it m).env →
        ∃ τ', NLe x w (.loop (scTest R D Q) P) τ τ'
          (∑ j ∈ Finset.Ico m n, (cost x w body (it j) + condCost w c) + 1) ∧
          CCorr D τ' (it n) := by
      intro d
      induction d with
      | zero =>
        intro m τ hm hτ _ _ he
        have : m = n := by omega
        subst this
        refine ⟨τ, (NLe.loopF ?_).mono (by simp), hτ⟩
        show (τ.toH.view (sc R D 0)).isSome = false
        rw [← Bool.not_eq_true, HSt.view_isSome_iff]; simp only [NSt.toH_env]
        rw [he]; simpa using hn
      | succ d ih =>
        intro m τ hm hτ hbτ hpτ he
        have hmn : m < n := by omega
        obtain ⟨τ₁, r₁, c₁⟩ := code_spec hw body (it m) τ hd.2 (hlt m hmn).2 hτ hbτ hpτ
        have hb₁ := r₁.bounded hw hbτ
        have hc₁ : c.Fits w (uenv D τ₁.toH) := by
          rw [c₁.1, ← iter_succ]; exact hcf (m + 1) (by omega)
        obtain ⟨τ₂, r₂, e₂, u₂, s₂, p₂, o₂, b₂⟩ := ex_code_N (x := x) hw c τ₁ hd.1 hb₁ hc₁
        have c₂ : CCorr D τ₂ (it (m + 1)) := by
          show CCorr D τ₂ (iter x body σ (m + 1))
          rw [iter_succ]
          exact ⟨u₂.trans c₁.1, s₂.trans c₁.2.1, p₂.trans c₁.2.2.1, o₂.trans c₁.2.2.2⟩
        have he₂ : τ₂.env (sc R D 0) = c.eval (it (m + 1)).env := by
          show _ = c.eval (iter x body σ (m + 1)).env
          rw [e₂, c₁.1, iter_succ]
        obtain ⟨τ', r', c'⟩ := ih (m + 1) τ₂ (by omega) c₂ b₂
          (by rw [p₂]; exact r₁.pos_le hpτ) he₂
        have hv : scTest R D Q τ.view = true := by
          show (τ.toH.view (sc R D 0)).isSome = true
          rw [HSt.view_isSome_iff]; simp only [NSt.toH_env]; rw [he]; exact (hlt m hmn).1
        refine ⟨τ', (NLe.loopT hv (r₁.seq r₂) r').mono ?_, c'⟩
        rw [Finset.sum_eq_sum_Ico_succ_bot hmn]
        simp only [condCost]; omega
    obtain ⟨h1, h2, h3, h4⟩ := hc
    obtain ⟨st₁, r₁, e₁, u₁, s₁, p₁, o₁, b₁⟩ :=
      ex_code_N (x := x) hw c st hd.1 hb (by rw [h1]; exact hcf 0 (Nat.zero_le _))
    obtain ⟨τ', r', c'⟩ := aux n 0 st₁ (by omega)
      ⟨u₁.trans h1, s₁.trans h2, p₁.trans h3, o₁.trans h4⟩ b₁ (by rw [p₁]; exact hp)
      (by rw [e₁, h1]; rfl)
    refine ⟨τ', (r₁.seq r').mono ?_, c'⟩
    rw [Finset.range_eq_Ico]; simp only [condCost]; omega

end CStm

end Lax119563Proofs.Compiler

end Compiler_CStm

/-! ### Formerly `Lax119563Proofs.Compiler.CLib` -/

section Compiler_CLib

/-!
# A calculus for structured statements

`CStm.Good x w c st st' T`: `c` fits (all values below `2 ^ w`, loops terminate), its
denotation maps `st` to `st'`, and its cost is at most `T`. Combinators for all statements;
loops are handled along a sequence of states (`Good.loop`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

namespace CStm

/-- `c` fits, maps `st` to `st'` and costs at most `T`. -/
def Good (x : List Bool) (w : ℕ) (c : CStm R Q) (st st' : NSt R Q) (T : ℕ) : Prop :=
  Fits x w c st ∧ exec x c st = st' ∧ cost x w c st ≤ T

namespace Good

variable {c p q : CStm R Q} {st st' st₁ st₂ st₃ : NSt R Q} {T T' T₁ T₂ : ℕ}

lemma mono (h : Good x w c st st' T) (hT : T ≤ T') : Good x w c st st' T' :=
  ⟨h.1, h.2.1, h.2.2.trans hT⟩

lemma of_eq (h : Good x w c st st₁ T) (hs : st₁ = st₂) (hT : T ≤ T') : Good x w c st st₂ T' :=
  hs ▸ h.mono hT

lemma skip : Good x w (skip : CStm R Q) st st (unitCost w) := ⟨trivial, rfl, le_rfl⟩

lemma set {r : Fin R} {e : Ex R} (h : e.Fits w st.env) :
    Good x w (set r e) st (st.set r (e.eval st.env)) (e.size * Ex.nodeCost w + unitCost w) :=
  ⟨h, rfl, le_rfl⟩

lemma emit {e : Ex R} (h : e.Fits w st.env) :
    Good x w (emit e) st { st with out := st.out ++ [e.eval st.env] }
      (e.size * Ex.nodeCost w + unitCost w) :=
  ⟨h, rfl, le_rfl⟩

lemma push {q : Fin Q} {e : Ex R} (h : e.Fits w st.env) :
    Good x w (push q e : CStm R Q) st (st.setS q (e.eval st.env :: st.stk q))
      (e.size * Ex.nodeCost w + unitCost w) :=
  ⟨h, rfl, le_rfl⟩

lemma pop (q : Fin Q) (r : Fin R) :
    Good x w (pop q r : CStm R Q) st ((st.setS q (st.stk q).tail).set r ((st.stk q).headD 0))
      (unitCost w + 1) :=
  ⟨trivial, rfl, le_rfl⟩

lemma sne (r : Fin R) (q : Fin Q) :
    Good x w (sne r q : CStm R Q) st (st.set r (if (st.stk q).isEmpty then 0 else 1))
      (2 * unitCost w + 1) :=
  ⟨trivial, rfl, le_rfl⟩

lemma rd (r : Fin R) :
    Good x w (rd r : CStm R Q) st
      { (st.set r (inBit x st.pos)) with pos := min (st.pos + 1) x.length } (unitCost w) :=
  ⟨trivial, rfl, le_rfl⟩

lemma rst : Good x w (rst : CStm R Q) st { st with pos := 0 } (unitCost w * (st.pos + 1)) :=
  ⟨trivial, rfl, le_rfl⟩

lemma seq (h₁ : Good x w p st₁ st₂ T₁) (h₂ : Good x w q st₂ st₃ T₂) :
    Good x w (.seq p q) st₁ st₃ (T₁ + T₂) := by
  obtain ⟨f₁, e₁, c₁⟩ := h₁
  obtain ⟨f₂, e₂, c₂⟩ := h₂
  subst e₁
  exact ⟨⟨f₁, f₂⟩, e₂, by simp only [cost]; omega⟩

lemma iteT {e : Ex R} (he : e.Fits w st.env) (hc : e.eval st.env ≠ 0)
    (h : Good x w p st st' T) : Good x w (.ite e p q) st st' (condCost w e + T) := by
  obtain ⟨f, ex, co⟩ := h
  refine ⟨⟨he, by rw [if_pos hc]; exact f⟩, by simp only [exec, if_pos hc]; exact ex, ?_⟩
  simp only [cost, if_pos hc]; omega

lemma iteF {e : Ex R} (he : e.Fits w st.env) (hc : e.eval st.env = 0)
    (h : Good x w q st st' T) : Good x w (.ite e p q) st st' (condCost w e + T) := by
  obtain ⟨f, ex, co⟩ := h
  have hc' : ¬ e.eval st.env ≠ 0 := by simpa using hc
  refine ⟨⟨he, by rw [if_neg hc']; exact f⟩, by simp only [exec, if_neg hc']; exact ex, ?_⟩
  simp only [cost, if_neg hc']; omega

/-- **Loops along a sequence of states.** -/
lemma loop {e : Ex R} {body : CStm R Q} (n : ℕ) (S : ℕ → NSt R Q) (C : ℕ → ℕ)
    (hc : ∀ j < n, e.eval (S j).env ≠ 0) (hn : e.eval (S n).env = 0)
    (hf : ∀ j ≤ n, e.Fits w (S j).env)
    (hb : ∀ j < n, Good x w body (S j) (S (j + 1)) (C j)) :
    Good x w (.loop e body) (S 0) (S n)
      (∑ j ∈ Finset.range n, (C j + condCost w e) + condCost w e) := by
  have hit : ∀ j ≤ n, iter x body (S 0) j = S j := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [iter_succ, ih (by omega), (hb j (by omega)).2.1]
  have hc' : ∀ j < n, e.eval (iter x body (S 0) j).env ≠ 0 := fun j hj => by
    rw [hit j hj.le]; exact hc j hj
  have hn' : e.eval (iter x body (S 0) n).env = 0 := by rw [hit n le_rfl]; exact hn
  refine ⟨⟨n, hn', fun j hj => ⟨hc' j hj, ?_⟩, fun j hj => ?_⟩, ?_, ?_⟩
  · have := hit j hj.le; simp only [iter] at this; rw [this]; exact (hb j hj).1
  · have := hit j hj; simp only [iter] at this; rw [this]; exact hf j hj
  · rw [exec_loop hn' hc', hit n le_rfl]
  · rw [cost_loop hn' hc']
    gcongr with j hj
    rw [hit j (Finset.mem_range.mp hj).le]
    exact (hb j (Finset.mem_range.mp hj)).2.2

/-- Loops with a uniform cost bound per iteration. -/
lemma loop_const {e : Ex R} {body : CStm R Q} (n : ℕ) (S : ℕ → NSt R Q) (C : ℕ)
    (hc : ∀ j < n, e.eval (S j).env ≠ 0) (hn : e.eval (S n).env = 0)
    (hf : ∀ j ≤ n, e.Fits w (S j).env)
    (hb : ∀ j < n, Good x w body (S j) (S (j + 1)) C) :
    Good x w (.loop e body) (S 0) (S n) (n * (C + condCost w e) + condCost w e) :=
  (loop n S (fun _ => C) hc hn hf hb).mono (by simp)

end Good

/-! ## Bounds are kept -/

/-- Fitting statements keep all registers and stack entries below `2 ^ w` and the cursor
within the input (via the compiled program). -/
lemma exec_bdd (hw : 2 ≤ w) {c : CStm R Q} {σ : NSt R Q} (hf : Fits x w c σ) (hb : σ.Bdd w)
    (hp : σ.pos ≤ x.length) : (exec x c σ).Bdd w ∧ (exec x c σ).pos ≤ x.length := by
  set st : NSt (R + c.depth + 1) Q :=
    ⟨fun i => if h : i.val < R then σ.env ⟨i.val, h⟩ else 0, σ.stk, σ.pos, σ.out⟩
  have hu : uenv c.depth st.toH = σ.env := by
    funext r; simp [uenv, st, ur]
  have hbs : st.Bdd w := by
    refine ⟨fun i => ?_, hb.2⟩
    simp only [st]; split_ifs
    · exact hb.1 _
    · exact Nat.pos_of_ne_zero (by positivity)
  obtain ⟨st', r', c'⟩ := code_spec (D := c.depth) hw c σ st le_rfl hf ⟨hu, rfl, rfl, rfl⟩
    hbs hp
  have hb' := r'.bounded hw hbs
  refine ⟨⟨fun r => ?_, fun q v hv => ?_⟩, ?_⟩
  · rw [← c'.1]; exact hb'.1 _
  · rw [← c'.2.1] at hv; exact hb'.2 q v hv
  · rw [← c'.2.2.1]; exact r'.pos_le (by simpa [st] using hp)

lemma Good.bdd (hw : 2 ≤ w) {c : CStm R Q} {σ σ' : NSt R Q} {T : ℕ} (h : Good x w c σ σ' T)
    (hb : σ.Bdd w) (hp : σ.pos ≤ x.length) : σ'.Bdd w ∧ σ'.pos ≤ x.length := by
  rw [← h.2.1]; exact exec_bdd hw h.1 hb hp

/-! ## Expression shorthands -/

/-- `[a ≠ 0]`-tests and register expressions. -/
abbrev rv (r : Fin R) : Ex R := .var r

end CStm

end Lax119563Proofs.Compiler

end Compiler_CLib

/-! ### Formerly `Lax119563Proofs.Compiler.CStack` -/

section Compiler_CStack

/-!
# Stack routines

* `moveAllS q q' t f`: pop all of `q` onto `q'` (reversing), with the scratch registers
  `t` (the moved value) and `f` (the loop flag); `moveAllS_good`.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

namespace CStm

/-- Pop all of `q` onto `q'`. -/
def moveAllS (q q' : Fin Q) (t f : Fin R) : CStm R Q :=
  .seq (.sne f q) (.loop (rv f) (.seq (.pop q t) (.seq (.push q' (rv t)) (.sne f q))))

lemma nodeCost_ge (w : ℕ) : unitCost w ≤ Ex.nodeCost w := Ex.unitCost_le_nodeCost w

lemma unitCost_ge (w : ℕ) : 64 ≤ unitCost w := by unfold unitCost; omega

/-- The state of `moveAllS` before iteration `j`. -/
def mvSt (st : NSt R Q) (q q' : Fin Q) (t f : Fin R) (j : ℕ) : NSt R Q :=
  ⟨Function.update (Function.update st.env t
      (if j = 0 then st.env t else (st.stk q).getD (j - 1) 0)) f
      (if j < (st.stk q).length then 1 else 0),
    Function.update (Function.update st.stk q ((st.stk q).drop j)) q'
      (((st.stk q).take j).reverse ++ st.stk q'),
    st.pos, st.out⟩

lemma moveAllS_good (hw : 2 ≤ w) {q q' : Fin Q} {t f : Fin R} (hq : q ≠ q') (htf : t ≠ f)
    (st : NSt R Q) (hb : st.Bdd w) :
    ∃ st' : NSt R Q, Good x w (moveAllS q q' t f) st st'
        (((st.stk q).length + 1) * (10 * Ex.nodeCost w)) ∧
      st'.stk = Function.update (Function.update st.stk q [])
        q' ((st.stk q).reverse ++ st.stk q') ∧
      st'.pos = st.pos ∧ st'.out = st.out ∧ ∀ r, r ≠ t → r ≠ f → st'.env r = st.env r := by
  have h2 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have hU := nodeCost_ge w
  have hU' := unitCost_ge w
  have hlb : ∀ v ∈ st.stk q, v < 2 ^ w := hb.2 q
  have hfq : ∀ j, (mvSt st q q' t f j).env f = if j < (st.stk q).length then 1 else 0 := by
    intro j; simp [mvSt]
  have hsq : ∀ j, (mvSt st q q' t f j).stk q = (st.stk q).drop j := by
    intro j; simp [mvSt, Function.update_of_ne hq]
  -- the body
  have hbody : ∀ j < (st.stk q).length,
      Good x w (.seq (.pop q t) (.seq (.push q' (rv t)) (.sne f q)))
        (mvSt st q q' t f j) (mvSt st q q' t f (j + 1)) (8 * Ex.nodeCost w) := by
    intro j hj
    have hd : (st.stk q).drop j = (st.stk q)[j] :: (st.stk q).drop (j + 1) :=
      List.drop_eq_getElem_cons hj
    refine ((Good.pop q t).seq ((Good.push ?_).seq (Good.sne f q))).of_eq ?_ ?_
    · simp only [rv, Ex.Fits, NSt.set_env, NSt.setS_env, Function.update_self]
      rw [hsq, hd]; exact hlb _ (List.getElem_mem _)
    · rw [hsq, hd]
      refine NSt.ext (funext fun r => ?_) (funext fun r => ?_) ?_ ?_
      · simp only [mvSt, NSt.set_env, NSt.setS_env, NSt.set_stk, NSt.setS_stk, rv, Ex.eval,
          Function.update_self, Function.update_of_ne hq, List.headD_cons, List.tail_cons,
          Function.update_of_ne hq.symm]
        by_cases hrf : r = f
        · subst hrf
          simp only [Function.update_self, List.isEmpty_iff, List.drop_eq_nil_iff]
          split_ifs <;> omega
        · by_cases hrt : r = t
          · subst hrt; simp [Function.update_of_ne hrf, Function.update_of_ne htf,
              List.getElem?_eq_getElem hj]
          · simp [Function.update_of_ne hrf, Function.update_of_ne hrt]
      · simp only [mvSt, NSt.set_env, NSt.setS_env, NSt.set_stk, NSt.setS_stk, rv, Ex.eval,
          Function.update_self, Function.update_of_ne htf.symm, List.headD_cons, List.tail_cons]
        by_cases hrq' : r = q'
        · subst hrq'
          simp only [Function.update_self, Function.update_of_ne hq.symm]
          rw [List.take_add_one, List.getElem?_eq_getElem hj, List.reverse_append]
          rfl
        · by_cases hrq : r = q
          · subst hrq; simp [Function.update_of_ne hq, Function.update_of_ne hrq']
          · simp [Function.update_of_ne hrq, Function.update_of_ne hrq']
      · simp [mvSt]
      · simp [mvSt]
    · simp only [rv, Ex.size]; omega
  have hloop := Good.loop_const (x := x) (w := w) (e := rv f) (st.stk q).length
    (mvSt st q q' t f) (8 * Ex.nodeCost w)
    (fun j hj => by simp [rv, Ex.eval, hfq, hj])
    (by simp [rv, Ex.eval, hfq])
    (fun j _ => by simp only [rv, Ex.Fits, hfq]; split_ifs <;> omega)
    hbody
  have hinit : Good x w (.sne f q) st (mvSt st q q' t f 0) (2 * unitCost w + 1) := by
    refine (Good.sne f q).of_eq ?_ le_rfl
    refine NSt.ext (funext fun r => ?_) (funext fun r => ?_) ?_ ?_
    · simp only [mvSt, NSt.set_env, if_true]
      by_cases hrf : r = f
      · subst hrf; simp only [Function.update_self]
        rcases h : st.stk q with _ | ⟨a, l⟩ <;> simp
      · by_cases hrt : r = t
        · subst hrt; simp [Function.update_of_ne hrf]
        · simp [Function.update_of_ne hrf, Function.update_of_ne hrt]
    · simp only [mvSt, NSt.set_stk, List.drop_zero, List.take_zero, List.reverse_nil,
        List.nil_append]
      by_cases hrq' : r = q'
      · subst hrq'; simp
      · by_cases hrq : r = q
        · subst hrq; simp [Function.update_of_ne hrq']
        · simp [Function.update_of_ne hrq, Function.update_of_ne hrq']
    · simp [mvSt]
    · simp [mvSt]
  refine ⟨mvSt st q q' t f (st.stk q).length, (hinit.seq hloop).mono ?_, ?_, rfl, rfl,
    fun r hrt hrf => ?_⟩
  · simp only [condCost, rv, Ex.size]; nlinarith
  · simp [mvSt]
  · simp [mvSt, Function.update_of_ne hrt, Function.update_of_ne hrf]

end CStm

end Lax119563Proofs.Compiler

end Compiler_CStack

/-! ### Formerly `Lax119563Proofs.Compiler.CParse` -/

section Compiler_CParse

/-!
# Parsing the input

The input is read through the cursor (`rd`: `0` at the end, `1` for `false`, `2` for
`true`). Numbers are self-delimiting (`encodeNat v = pairs (Nat.bits v) ++ [false]`).

* `rdNumS r p t`: read the next number into `r` (`p` holds the power of two, `t` the value
  read); `rdNumS_good`, for numbers with fewer than `w` binary digits.
* `skipNumS t`: skip the next number (any size); `skipNumS_good`.
* `rdNumsS q n i r p t`: push the next `n` numbers onto `q` (the last number read on top);
  `rdNumsS_good`.

All specifications give the final state explicitly.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

/-! ## Digit lists -/

lemma drop_pairs : ∀ (ds : List Bool) (j : ℕ), (pairs ds).drop (2 * j) = pairs (ds.drop j)
  | [], j => by simp
  | d :: ds, 0 => by simp
  | d :: ds, j + 1 => by
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, pairs_cons]
    simp only [List.drop_succ_cons, List.drop_succ_cons]
    exact drop_pairs ds j

lemma valBits_append_single : ∀ (l : List Bool) (d : Bool),
    Machines.valBits (l ++ [d]) = Machines.valBits l + d.toNat * 2 ^ l.length
  | [], d => by simp [Machines.valBits]
  | b :: l, d => by
    simp only [List.cons_append, Machines.valBits, valBits_append_single l d, List.length_cons,
      pow_succ]
    ring

lemma valBits_lt : ∀ l : List Bool, Machines.valBits l < 2 ^ l.length
  | [] => by simp [Machines.valBits]
  | b :: l => by
    have := valBits_lt l
    simp only [Machines.valBits, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

lemma valBits_take_succ (ds : List Bool) {j : ℕ} (hj : j < ds.length) :
    Machines.valBits (ds.take (j + 1)) = Machines.valBits (ds.take j) + ds[j].toNat * 2 ^ j := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj]
  simp only [Option.toList_some]
  rw [valBits_append_single, List.length_take, min_eq_left hj.le]

/-- Reading at an offset of the current position. -/
lemma drop_add (x : List Bool) (pos i : ℕ) : x.drop (pos + i) = (x.drop pos).drop i := by
  rw [List.drop_drop]

lemma inBit_pairs_marker {pos : ℕ} {ds : List Bool} {rest : List Bool}
    (h : x.drop pos = pairs ds ++ false :: rest) (j : ℕ) (hjL : j ≤ ds.length) :
    inBit x (pos + 2 * j) = if j < ds.length then 2 else 1 := by
  unfold inBit
  rw [drop_add, h, List.drop_append_of_le_length (by simp; omega), drop_pairs]
  split_ifs with hj
  · obtain ⟨a, l, e⟩ : ∃ a l, ds.drop j = a :: l := ⟨_, _, List.drop_eq_getElem_cons hj⟩
    rw [e, pairs_cons]; rfl
  · rw [List.drop_eq_nil_of_le (by omega)]; rfl

lemma inBit_pairs_digit {pos : ℕ} {ds : List Bool} {rest : List Bool}
    (h : x.drop pos = pairs ds ++ false :: rest) (j : ℕ) (hj : j < ds.length) :
    inBit x (pos + 2 * j + 1) = ds[j].toNat + 1 := by
  unfold inBit
  rw [show pos + 2 * j + 1 = pos + (2 * j + 1) by ring, drop_add, h, ← List.drop_drop,
    List.drop_append_of_le_length (by simp; omega), drop_pairs]
  have e : ds.drop j = ds[j] :: ds.drop (j + 1) := List.drop_eq_getElem_cons hj
  rw [e, pairs_cons]; rfl

lemma length_le_of_drop {pos : ℕ} {l : List Bool} (h : x.drop pos = l) (hl : l ≠ []) :
    pos + l.length = x.length := by
  have h1 := congrArg List.length h
  simp only [List.length_drop] at h1
  have : pos < x.length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by omega)] at h
    exact hl h.symm
  omega

lemma min_succ_eq {a n : ℕ} (h : a + 1 ≤ n) : min (a + 1) n = a + 1 := min_eq_left h

namespace CStm

/-! ## Reading a number -/

/-- `[1 < t]`: the value read is `true`. -/
abbrev isTrue (t : Fin R) : Ex R := .lt (.const 1) (rv t)

/-- Read the next number into `r`. -/
def rdNumS (r p t : Fin R) : CStm R Q :=
  .seq (.set r (.const 0)) (.seq (.set p (.const 1)) (.seq (.rd t)
    (.loop (isTrue t)
      (.seq (.rd t) (.seq (.ite (isTrue t) (.set r (.add (rv r) (rv p))) .skip)
        (.seq (.set p (.add (rv p) (rv p))) (.rd t)))))))

/-- The state of `rdNumS` before iteration `j` (digits `ds`). -/
def rnSt (st : NSt R Q) (r p t : Fin R) (ds : List Bool) (j : ℕ) : NSt R Q :=
  { st with
    env := Function.update (Function.update (Function.update st.env r
      (Machines.valBits (ds.take j))) p (2 ^ j)) t (if j < ds.length then 2 else 1)
    pos := st.pos + 2 * j + 1 }

lemma isTrue_eval (env : Fin R → ℕ) (t : Fin R) :
    (isTrue t).eval env = if 1 < env t then 1 else 0 := rfl

lemma isTrue_fits (hw : 2 ≤ w) {env : Fin R → ℕ} {t : Fin R} (h : env t ≤ 2) :
    (isTrue t).Fits w env := by
  have h4 : (4 : ℕ) ≤ 2 ^ w := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  simp only [isTrue, Ex.Fits, rv]; omega

lemma rdNumS_digits (hw : 2 ≤ w) {r p t : Fin R} (hrp : r ≠ p) (hrt : r ≠ t) (hpt : p ≠ t)
    (st : NSt R Q) (ds : List Bool) (rest : List Bool)
    (hx : x.drop st.pos = pairs ds ++ false :: rest) (hL : ds.length < w) :
    Good x w (rdNumS r p t : CStm R Q) st (rnSt st r p t ds ds.length)
      ((2 * ds.length + 2) * (20 * Ex.nodeCost w)) := by
  have hU := nodeCost_ge w
  have hU' := unitCost_ge w
  have h4 : (4 : ℕ) ≤ 2 ^ w := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  have hlen : st.pos + (2 * ds.length + 1 + rest.length) = x.length := by
    have := length_le_of_drop hx (by simp)
    simp [List.length_append, length_pairs] at this; omega
  have hpow : ∀ j ≤ ds.length, 2 ^ j < 2 ^ w := fun j hj =>
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  -- environments
  have envT : ∀ j, (rnSt st r p t ds j).env t = if j < ds.length then 2 else 1 := by
    intro j; simp [rnSt]
  have envP : ∀ j, (rnSt st r p t ds j).env p = 2 ^ j := by
    intro j; simp [rnSt, Function.update_of_ne hpt]
  have envR : ∀ j, (rnSt st r p t ds j).env r = Machines.valBits (ds.take j) := by
    intro j; simp [rnSt, Function.update_of_ne hrt, Function.update_of_ne hrp]
  -- the body
  have hbody : ∀ j < ds.length, Good x w
      (.seq (.rd t) (.seq (.ite (isTrue t) (.set r (.add (rv r) (rv p))) .skip)
        (.seq (.set p (.add (rv p) (rv p))) (.rd t))))
      (rnSt st r p t ds j) (rnSt st r p t ds (j + 1)) (14 * Ex.nodeCost w) := by
    intro j hj
    set S := rnSt st r p t ds j
    have hd := inBit_pairs_digit hx j hj
    have hm := inBit_pairs_marker hx (j + 1) (by omega)
    have hvl : Machines.valBits (ds.take j) < 2 ^ j := by
      have := valBits_lt (ds.take j); rwa [List.length_take, min_eq_left hj.le] at this
    have hp1 : 2 ^ (j + 1) < 2 ^ w := hpow (j + 1) (by omega)
    have hvt := valBits_take_succ ds hj
    -- after the first read
    set S₁ : NSt R Q := { (S.set t (inBit x S.pos)) with pos := min (S.pos + 1) x.length }
    have hS₁t : S₁.env t = ds[j].toNat + 1 := by
      simp only [S₁, NSt.set_env, Function.update_self, S, rnSt]; exact hd
    -- the conditional
    set S₂ : NSt R Q := if ds[j] then S₁.set r (S₁.env r + S₁.env p) else S₁
    have hite : Good x w (.ite (isTrue t) (.set r (.add (rv r) (rv p))) .skip) S₁ S₂
        (Ex.nodeCost w * 3 + 1 + (3 * Ex.nodeCost w + unitCost w)) := by
      have hf := isTrue_fits (w := w) hw (env := S₁.env) (t := t)
        (by rw [hS₁t]; cases ds[j] <;> simp)
      have hr1 : S₁.env r = Machines.valBits (ds.take j) := by
        simp only [S₁, NSt.set_env, Function.update_of_ne hrt]; exact envR j
      have hp1' : S₁.env p = 2 ^ j := by
        simp only [S₁, NSt.set_env, Function.update_of_ne hpt]; exact envP j
      cases hdj : ds[j]
      · have hc : (isTrue t).eval S₁.env = 0 := by
          rw [isTrue_eval, hS₁t, hdj]; simp
        refine (Good.iteF hf hc Good.skip).of_eq (by simp [S₂, hdj]) ?_
        simp only [condCost, isTrue, Ex.size, rv]; omega
      · have hc : (isTrue t).eval S₁.env ≠ 0 := by
          rw [isTrue_eval, hS₁t, hdj]; simp
        refine (Good.iteT hf hc (Good.set ?_)).of_eq (by simp [S₂, hdj, Ex.eval, rv]) ?_
        · simp only [Ex.Fits, Ex.eval, rv, hr1, hp1']
          have hj2 : 2 ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
          exact ⟨lt_trans hvl (hpow j hj.le), hpow j hj.le, by omega⟩
        · simp only [condCost, isTrue, Ex.size, rv]; omega
    have hS₂p : S₂.env p = 2 ^ j := by
      have : S₁.env p = 2 ^ j := by
        simp only [S₁, NSt.set_env, Function.update_of_ne hpt]; exact envP j
      by_cases hdj : ds[j] <;> simp [S₂, hdj, Function.update_of_ne hrp.symm, this]
    have hset : Good x w (.set p (.add (rv p) (rv p))) S₂ (S₂.set p (2 ^ j + 2 ^ j))
        (3 * Ex.nodeCost w + unitCost w) := by
      refine (Good.set ?_).of_eq (by simp [Ex.eval, rv, hS₂p]) (by simp [Ex.size, rv])
      simp only [Ex.Fits, Ex.eval, rv, hS₂p]
      have hj2 : 2 ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
      exact ⟨hpow j hj.le, hpow j hj.le, by omega⟩
    have hpos₂ : S₂.pos = st.pos + 2 * j + 2 := by
      have : S₁.pos = st.pos + 2 * j + 2 := by
        simp only [S₁, S, rnSt]; rw [min_succ_eq (by omega)]
      by_cases hdj : ds[j] <;> simp [S₂, hdj, this]
    have hrd2 := Good.rd (x := x) (w := w) (Q := Q) (st := S₂.set p (2 ^ j + 2 ^ j)) t
    refine ((Good.rd t).seq (hite.seq (hset.seq hrd2))).of_eq ?_ ?_
    · have hpos' : (S₂.set p (2 ^ j + 2 ^ j)).pos = st.pos + 2 * (j + 1) := by
        simp only [NSt.set_pos, hpos₂]; ring
      rw [hpos', hm, min_succ_eq (by omega)]
      refine NSt.ext (funext fun q => ?_) ?_ ?_ ?_
      · simp only [NSt.set_env, rnSt]
        by_cases hqt : q = t
        · subst hqt; simp
        · by_cases hqp : q = p
          · subst hqp; simp [Function.update_of_ne hpt, pow_succ, mul_two]
          · by_cases hqr : q = r
            · subst hqr
              simp only [Function.update_of_ne hqt, Function.update_of_ne hqp]
              by_cases hdj : ds[j]
              · simp [S₂, hdj, S₁, S, rnSt, hvt, Function.update_of_ne hrt,
                  Function.update_of_ne hrp, Function.update_of_ne hpt]
              · simp [S₂, hdj, S₁, S, rnSt, hvt, Function.update_of_ne hrt,
                  Function.update_of_ne hrp]
            · simp only [Function.update_of_ne hqt, Function.update_of_ne hqp,
                Function.update_of_ne hqr]
              by_cases hdj : ds[j]
              · simp [S₂, hdj, S₁, S, rnSt, Function.update_of_ne hqt,
                  Function.update_of_ne hqp, Function.update_of_ne hqr]
              · simp [S₂, hdj, S₁, S, rnSt, Function.update_of_ne hqt,
                  Function.update_of_ne hqp, Function.update_of_ne hqr]
      · by_cases hdj : ds[j] <;> simp [S₂, hdj, S₁, S, rnSt]
      · simp [rnSt]; try ring
      · by_cases hdj : ds[j] <;> simp [S₂, hdj, S₁, S, rnSt]
    · omega
  -- the loop
  have hloop := Good.loop_const (x := x) (w := w) (e := isTrue t) ds.length (rnSt st r p t ds)
    (14 * Ex.nodeCost w)
    (fun j hj => by rw [isTrue_eval, envT]; simp [hj])
    (by rw [isTrue_eval, envT]; simp)
    (fun j _ => isTrue_fits hw (by rw [envT]; split_ifs <;> omega))
    hbody
  -- initialization
  have h0 := inBit_pairs_marker hx 0 (Nat.zero_le _)
  set S₀ : NSt R Q := ((st.set r 0).set p 1)
  have hS₀ : { (S₀.set t (inBit x S₀.pos)) with pos := min (S₀.pos + 1) x.length } =
      rnSt st r p t ds 0 := by
      simp only [S₀, NSt.set_pos, Nat.mul_zero, Nat.add_zero] at h0 ⊢
      rw [h0, min_succ_eq (by omega)]
      refine NSt.ext (funext fun q => ?_) rfl (by simp [rnSt]) rfl
      simp only [NSt.set_env, rnSt, Ex.eval, List.take_zero, pow_zero]
      by_cases hqt : q = t
      · subst hqt; simp
      · by_cases hqp : q = p
        · subst hqp; simp [Function.update_of_ne hqt]
        · by_cases hqr : q = r
          · subst hqr; simp [Function.update_of_ne hqt, Function.update_of_ne hqp,
              Machines.valBits]
          · simp [Function.update_of_ne hqt, Function.update_of_ne hqp,
              Function.update_of_ne hqr]
  have h1 : (Ex.const 1 : Ex R).Fits w (st.set r 0).env := by
    simp only [Ex.Fits]; omega
  have hrd0 := Good.rd (x := x) (w := w) (st := S₀) t
  rw [hS₀] at hrd0
  refine ((Good.set (r := r) (st := st) (by simp [Ex.Fits])).seq
    ((Good.set (r := p) h1).seq (hrd0.seq hloop))).mono ?_
  simp only [condCost, isTrue, Ex.size, rv]
  nlinarith

/-- The state after reading the number `v`. -/
def rdNumFinal (st : NSt R Q) (r p t : Fin R) (v : ℕ) : NSt R Q :=
  { st with
    env := Function.update (Function.update (Function.update st.env r v) p
      (2 ^ (Nat.bits v).length)) t 1
    pos := st.pos + (encodeNat v).length }

lemma length_encodeNat (v : ℕ) : (encodeNat v).length = 2 * (Nat.bits v).length + 1 := by
  simp [encodeNat_eq_pairs]

/-- **Reading a number.** -/
lemma rdNumS_good (hw : 2 ≤ w) {r p t : Fin R} (hrp : r ≠ p) (hrt : r ≠ t) (hpt : p ≠ t)
    (st : NSt R Q) (v : ℕ) (rest : List Bool) (hx : x.drop st.pos = encodeNat v ++ rest)
    (hv : (Nat.bits v).length < w) :
    Good x w (rdNumS r p t : CStm R Q) st (rdNumFinal st r p t v)
      (((encodeNat v).length + 1) * (20 * Ex.nodeCost w)) := by
  have hx' : x.drop st.pos = pairs (Nat.bits v) ++ false :: rest := by
    rw [hx, encodeNat_eq_pairs]; simp
  refine (rdNumS_digits hw hrp hrt hpt st (Nat.bits v) rest hx' hv).of_eq ?_
    (by rw [length_encodeNat])
  simp only [rnSt, rdNumFinal, List.take_length, lt_irrefl, if_false, Machines.valBits_bits,
    length_encodeNat]
  simp only [Nat.add_assoc]

/-! ## Skipping a number -/

/-- Skip the next number. -/
def skipNumS (t : Fin R) : CStm R Q :=
  .seq (.rd t) (.loop (isTrue t) (.seq (.rd t) (.rd t)))

/-- The state after skipping the number `v`. -/
def skipNumFinal (st : NSt R Q) (t : Fin R) (v : ℕ) : NSt R Q :=
  { st with env := Function.update st.env t 1, pos := st.pos + (encodeNat v).length }

/-- The state of `skipNumS` before iteration `j`. -/
def skSt (st : NSt R Q) (t : Fin R) (ds : List Bool) (j : ℕ) : NSt R Q :=
  { st with env := Function.update st.env t (if j < ds.length then 2 else 1)
            pos := st.pos + 2 * j + 1 }

/-- **Skipping a number** (of any size). -/
lemma skipNumS_good (hw : 2 ≤ w) {t : Fin R} (st : NSt R Q) (v : ℕ) (rest : List Bool)
    (hx : x.drop st.pos = encodeNat v ++ rest) :
    Good x w (skipNumS t : CStm R Q) st (skipNumFinal st t v)
      (((encodeNat v).length + 1) * (4 * Ex.nodeCost w)) := by
  have hU := nodeCost_ge w
  have hU' := unitCost_ge w
  obtain ⟨ds, hds⟩ : ∃ ds, ds = Nat.bits v := ⟨_, rfl⟩
  have hx' : x.drop st.pos = pairs ds ++ false :: rest := by
    rw [hx, encodeNat_eq_pairs, ← hds]; simp
  have hlen : st.pos + (2 * ds.length + 1 + rest.length) = x.length := by
    have := length_le_of_drop hx' (by simp)
    simp [List.length_append, length_pairs] at this; omega
  set S : ℕ → NSt R Q := skSt st t ds
  have envT : ∀ j, (S j).env t = if j < ds.length then 2 else 1 := by intro j; simp [S, skSt]
  have hbody : ∀ j < ds.length, Good x w (.seq (.rd t) (.rd t)) (S j) (S (j + 1))
      (2 * unitCost w) := by
    intro j hj
    have hm := inBit_pairs_marker hx' (j + 1) (by omega)
    refine ((Good.rd t).seq (Good.rd t)).of_eq ?_ (by omega)
    have e1 : (S j).pos = st.pos + 2 * j + 1 := rfl
    simp only [NSt.set_pos, e1]
    rw [min_succ_eq (by omega), show st.pos + 2 * j + 1 + 1 = st.pos + 2 * (j + 1) by ring, hm,
      min_succ_eq (by omega)]
    refine NSt.ext (funext fun q => ?_) rfl rfl rfl
    by_cases hq : q = t
    · subst hq; simp [S, skSt]
    · simp [S, skSt, Function.update_of_ne hq]
  have hloop := Good.loop_const (x := x) (w := w) (e := isTrue t) ds.length S (2 * unitCost w)
    (fun j hj => by rw [isTrue_eval, envT]; simp [hj])
    (by rw [isTrue_eval, envT]; simp)
    (fun j _ => isTrue_fits hw (by rw [envT]; split_ifs <;> omega))
    hbody
  have h0 := inBit_pairs_marker hx' 0 (Nat.zero_le _)
  have hrd := Good.rd (x := x) (w := w) (st := st) (Q := Q) t
  have e0 : { (st.set t (inBit x st.pos)) with pos := min (st.pos + 1) x.length } = S 0 := by
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    rw [h0, min_succ_eq (by omega)]
    refine NSt.ext (funext fun q => ?_) rfl (by simp [S, skSt]) rfl
    by_cases hq : q = t
    · subst hq; simp [S, skSt]
    · simp [S, skSt, Function.update_of_ne hq]
  rw [e0] at hrd
  refine (hrd.seq hloop).of_eq ?_ ?_
  · refine NSt.ext (funext fun q => ?_) rfl ?_ rfl
    · by_cases hq : q = t
      · subst hq; simp [S, skSt, skipNumFinal]
      · simp [S, skSt, skipNumFinal, Function.update_of_ne hq]
    · simp [S, skSt, skipNumFinal, length_encodeNat, ← hds]; ring
  · simp only [condCost, isTrue, Ex.size, rv, length_encodeNat, ← hds]
    nlinarith

/-! ## Reading a list of numbers -/

/-- Push the next `n` numbers onto `q` (counter `i`, scratch `r p t`). -/
def rdNumsS (q : Fin Q) (n i r p t : Fin R) : CStm R Q :=
  .seq (.set i (.const 0)) (.loop (.lt (rv i) (rv n))
    (.seq (rdNumS r p t) (.seq (.push q (rv r)) (.set i (.add (rv i) (.const 1))))))

/-- The state of `rdNumsS` before iteration `j`. -/
def rnsSt (st : NSt R Q) (q : Fin Q) (i r p t : Fin R) (vs : List ℕ) : ℕ → NSt R Q
  | 0 => st.set i 0
  | j + 1 =>
    let s₁ := rdNumFinal (rnsSt st q i r p t vs j) r p t (vs.getD j 0)
    (s₁.setS q (vs.getD j 0 :: s₁.stk q)).set i (j + 1)

lemma encodeNats_take_succ (vs : List ℕ) {j : ℕ} (hj : j < vs.length) :
    encodeNats (vs.take (j + 1)) = encodeNats (vs.take j) ++ encodeNat vs[j] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj]
  simp only [encodeNats, Option.toList_some, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

lemma lt_of_bits_length {v w : ℕ} (h : (Nat.bits v).length < w) : v < 2 ^ w := by
  have := valBits_lt (Nat.bits v)
  rw [Machines.valBits_bits] at this
  exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) h.le)

lemma sum_getD_eq (f : ℕ → ℕ) : ∀ vs : List ℕ,
    ∑ j ∈ Finset.range vs.length, f (vs.getD j 0) = (vs.map f).sum
  | [] => by simp
  | v :: vs => by
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons,
      ← sum_getD_eq f vs]
    simp [add_comm]

lemma length_encodeNats_sum (vs : List ℕ) :
    (encodeNats vs).length = (vs.map fun v => (encodeNat v).length).sum := by
  simp [encodeNats, List.length_flatMap]

/-- **Reading a list of numbers.** -/
lemma rdNumsS_good (hw : 2 ≤ w) {q : Fin Q} {n i r p t : Fin R} (hin : i ≠ n) (hir : i ≠ r)
    (hip : i ≠ p) (hit : i ≠ t) (hnr : n ≠ r) (hnp : n ≠ p) (hnt : n ≠ t) (hrp : r ≠ p)
    (hrt : r ≠ t) (hpt : p ≠ t) (st : NSt R Q) (vs : List ℕ) (rest : List Bool)
    (hx : x.drop st.pos = encodeNats vs ++ rest) (hn : st.env n = vs.length)
    (hnw : vs.length < 2 ^ w) (hvs : ∀ v ∈ vs, (Nat.bits v).length < w) :
    Good x w (rdNumsS q n i r p t : CStm R Q) st (rnsSt st q i r p t vs vs.length)
        ((((encodeNats vs).length + 2 * vs.length + 1)) * (20 * Ex.nodeCost w)) ∧
      (rnsSt st q i r p t vs vs.length).stk =
        Function.update st.stk q (vs.reverse ++ st.stk q) ∧
      (rnsSt st q i r p t vs vs.length).pos = st.pos + (encodeNats vs).length ∧
      (rnsSt st q i r p t vs vs.length).out = st.out ∧
      ∀ r', r' ≠ i → r' ≠ r → r' ≠ p → r' ≠ t →
        (rnsSt st q i r p t vs vs.length).env r' = st.env r' := by
  have hU := nodeCost_ge w
  have hU' := unitCost_ge w
  set S := rnsSt st q i r p t vs
  -- invariants
  have inv : ∀ j ≤ vs.length,
      (S j).stk = Function.update st.stk q ((vs.take j).reverse ++ st.stk q) ∧
      (S j).pos = st.pos + (encodeNats (vs.take j)).length ∧ (S j).out = st.out ∧
      (S j).env i = j ∧
      ∀ r', r' ≠ i → r' ≠ r → r' ≠ p → r' ≠ t → (S j).env r' = st.env r' := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨by simp [S, rnsSt], by simp [S, rnsSt, encodeNats], rfl, by simp [S, rnsSt],
        fun r' h1 _ _ _ => by simp [S, rnsSt, Function.update_of_ne h1]⟩
    | succ j ih =>
      intro hj
      obtain ⟨i1, i2, i3, i4, i5⟩ := ih (by omega)
      have hg : vs.getD j 0 = vs[j] := List.getD_eq_getElem _ _ (by omega)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · show ((rdNumFinal (S j) r p t (vs.getD j 0)).setS q _).stk = _
        funext q'
        simp only [NSt.setS_stk, rdNumFinal]
        rw [i1, hg]
        by_cases hq : q' = q
        · subst hq
          rw [Function.update_self, Function.update_self, Function.update_self,
            List.take_add_one, List.getElem?_eq_getElem (show j < vs.length by omega),
            Option.toList_some, List.reverse_append, List.reverse_singleton, List.singleton_append,
            List.cons_append]
        · rw [Function.update_of_ne hq, Function.update_of_ne hq, Function.update_of_ne hq]
      · show (rdNumFinal (S j) r p t (vs.getD j 0)).pos = _
        simp only [rdNumFinal, i2, hg, encodeNats_take_succ vs (show j < vs.length by omega),
          List.length_append]; ring
      · show (rdNumFinal (S j) r p t (vs.getD j 0)).out = _
        simp [rdNumFinal, i3]
      · simp only [S, rnsSt, NSt.set_env, Function.update_self]
      · intro r' h1 h2 h3 h4
        simp only [S, rnsSt, NSt.set_env, NSt.setS_env, rdNumFinal, Function.update_of_ne h1,
          Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h4]
        exact i5 r' h1 h2 h3 h4
  have envN : ∀ j ≤ vs.length, (S j).env n = vs.length := fun j hj => by
    rw [(inv j hj).2.2.2.2 n hin.symm hnr hnp hnt, hn]
  have cmpE : ∀ j ≤ vs.length, (Ex.lt (rv i) (rv n) : Ex R).eval (S j).env =
      if j < vs.length then 1 else 0 := fun j hj => by
    simp [Ex.eval, rv, (inv j hj).2.2.2.1, envN j hj]
  -- the body
  set C : ℕ → ℕ := fun j => ((encodeNat (vs.getD j 0)).length + 1) * (20 * Ex.nodeCost w) +
    10 * Ex.nodeCost w
  have hbody : ∀ j < vs.length, Good x w
      (.seq (rdNumS r p t) (.seq (.push q (rv r)) (.set i (.add (rv i) (.const 1)))))
      (S j) (S (j + 1)) (C j) := by
    intro j hj
    obtain ⟨i1, i2, i3, i4, i5⟩ := inv j hj.le
    have hg : vs.getD j 0 = vs[j] := List.getD_eq_getElem _ _ hj
    have hvj := hvs _ (List.getElem_mem hj)
    have hxj : x.drop (S j).pos = encodeNat (vs.getD j 0) ++
        (encodeNats (vs.drop (j + 1)) ++ rest) := by
      have e : encodeNats vs = encodeNats (vs.take j) ++
          (encodeNat vs[j] ++ encodeNats (vs.drop (j + 1))) := by
        conv_lhs => rw [← List.take_append_drop j vs, List.drop_eq_getElem_cons hj]
        simp only [encodeNats, List.flatMap_append, List.flatMap_cons]
      rw [i2, drop_add, hx, e, List.append_assoc, List.drop_left, hg, List.append_assoc]
    have h1 := rdNumS_good (Q := Q) hw hrp hrt hpt (S j) (vs.getD j 0) _ hxj (by rw [hg]; exact hvj)
    set s₁ := rdNumFinal (S j) r p t (vs.getD j 0)
    have hr₁ : s₁.env r = vs.getD j 0 := by
      simp [s₁, rdNumFinal, Function.update_of_ne hrp, Function.update_of_ne hrt]
    have hi₁ : s₁.env i = j := by
      simp [s₁, rdNumFinal, Function.update_of_ne hir, Function.update_of_ne hip,
        Function.update_of_ne hit, i4]
    have hpush := Good.push (x := x) (w := w) (q := q) (e := rv r) (st := s₁)
      (by simp only [Ex.Fits, rv, hr₁, hg]; exact lt_of_bits_length hvj)
    have hset := Good.set (x := x) (w := w) (r := i) (e := Ex.add (rv i) (.const 1))
      (st := s₁.setS q ((rv r : Ex R).eval s₁.env :: s₁.stk q))
      (by
        have h2 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
        simp only [Ex.Fits, Ex.eval, rv, NSt.setS_env, hi₁]; omega)
    refine (h1.seq (hpush.seq hset)).of_eq ?_ ?_
    · show _ = (s₁.setS q (vs.getD j 0 :: s₁.stk q)).set i (j + 1)
      simp [Ex.eval, rv, hr₁, hi₁]
    · simp only [C, Ex.size, rv]; omega
  have hloop := Good.loop (x := x) (w := w) (e := Ex.lt (rv i) (rv n)) vs.length S C
    (fun j hj => by rw [cmpE j hj.le]; simp [hj])
    (by rw [cmpE _ le_rfl]; simp)
    (fun j hj => by
      simp only [Ex.Fits, rv, (inv j hj).2.2.2.1, envN j hj]; omega)
    hbody
  have hinit : Good x w (.set i (.const 0) : CStm R Q) st (S 0) (Ex.nodeCost w + unitCost w) :=
    (Good.set (by simp [Ex.Fits])).of_eq rfl (by simp [Ex.size])
  obtain ⟨i1, i2, i3, -, i5⟩ := inv _ le_rfl
  rw [List.take_of_length_le le_rfl] at i1 i2
  refine ⟨(hinit.seq hloop).mono ?_, i1, i2, i3, i5⟩
  -- the cost
  have hsum : ∑ j ∈ Finset.range vs.length, (C j + condCost w (Ex.lt (rv i) (rv n))) ≤
      ∑ j ∈ Finset.range vs.length,
        ((encodeNat (vs.getD j 0)).length + 2) * (20 * Ex.nodeCost w) := by
    apply Finset.sum_le_sum
    intro j _
    simp only [C, condCost, Ex.size, rv]; nlinarith
  have hsum' : ∑ j ∈ Finset.range vs.length,
      ((encodeNat (vs.getD j 0)).length + 2) * (20 * Ex.nodeCost w) =
      ((encodeNats vs).length + 2 * vs.length) * (20 * Ex.nodeCost w) := by
    rw [← Finset.sum_mul, Finset.sum_add_distrib, sum_getD_eq (fun v => (encodeNat v).length),
      length_encodeNats_sum, Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring
  simp only [condCost, Ex.size, rv] at hsum ⊢
  nlinarith

end CStm

end Lax119563Proofs.Compiler

end Compiler_CParse

/-! ### Formerly `Lax119563Proofs.Compiler.CSortLoop` -/

section Compiler_CSortLoop

/-!
# Loops with a variant

`Good.loop_var`: a loop whose body keeps an invariant, decreases a variant `μ` and costs at
most `K (φ s - φ s') + K₀` for a nonincreasing potential `φ` runs within
`K φ s + μ s (K₀ + condCost) + condCost`. Also `Good.loop_stop`, `Good.loop_cons`.

`moveN src dst cnt i t`: move the top `n` words of `src` onto `dst` (reversed), `n` the value
of `cnt` (`moveN_good`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

namespace CStm

namespace Good

lemma loop_stop {e : Ex R} {body : CStm R Q} {s : NSt R Q} (he : e.Fits w s.env)
    (h0 : e.eval s.env = 0) : Good x w (.loop e body) s s (condCost w e) :=
  (loop (body := body) 0 (fun _ => s) (fun _ => 0) (fun j hj => absurd hj (by omega)) h0
    (fun _ _ => he) (fun j hj => absurd hj (by omega))).mono (by simp)

lemma loop_cons {e : Ex R} {body : CStm R Q} {s s₁ s' : NSt R Q} {C T : ℕ}
    (he : e.Fits w s.env) (hc : e.eval s.env ≠ 0) (h₁ : Good x w body s s₁ C)
    (h₂ : Good x w (.loop e body) s₁ s' T) :
    Good x w (.loop e body) s s' (C + condCost w e + T) := by
  obtain ⟨⟨n, hn, hlt, hf⟩, hex, hco⟩ := h₂
  have hit : ∀ j, iter x body s (j + 1) = iter x body s₁ j := by
    intro j
    show (exec x body)^[j + 1] s = (exec x body)^[j] s₁
    rw [Function.iterate_succ_apply, h₁.2.1]
  have hn' : e.eval (iter x body s (n + 1)).env = 0 := by rw [hit]; exact hn
  have hlt' : ∀ j < n + 1, e.eval (iter x body s j).env ≠ 0 := by
    intro j hj
    rcases j with _ | j
    · exact hc
    · rw [hit]; exact (hlt j (by omega)).1
  refine ⟨⟨n + 1, hn', fun j hj => ⟨hlt' j hj, ?_⟩, fun j hj => ?_⟩, ?_, ?_⟩
  · rcases j with _ | j
    · exact h₁.1
    · have := hit j; simp only [iter] at this; rw [this]; exact (hlt j (by omega)).2
  · rcases j with _ | j
    · exact he
    · have := hit j; simp only [iter] at this; rw [this]; exact hf j (by omega)
  · rw [exec_loop hn' hlt', hit, ← hex, exec_loop hn (fun j hj => (hlt j hj).1)]
  · rw [cost_loop hn' hlt', Finset.sum_range_succ']
    rw [cost_loop hn (fun j hj => (hlt j hj).1)] at hco
    simp only [hit, iter_zero]
    have := h₁.2.2
    omega

/-- **Loops with a variant and a potential.** -/
lemma loop_var {e : Ex R} {body : CStm R Q} (Inv : NSt R Q → Prop) (μ φ : NSt R Q → ℕ)
    (K K₀ : ℕ)
    (hstep : ∀ s, Inv s → e.Fits w s.env ∧ (e.eval s.env ≠ 0 →
      ∃ s', Good x w body s s' (K * (φ s - φ s') + K₀) ∧ Inv s' ∧ μ s' < μ s ∧ φ s' ≤ φ s)) :
    ∀ s, Inv s → ∃ s', Good x w (.loop e body) s s'
      (K * φ s + μ s * (K₀ + condCost w e) + condCost w e) ∧ Inv s' ∧ e.eval s'.env = 0 := by
  intro s
  induction' hm : μ s using Nat.strong_induction_on with m ih generalizing s
  intro hI
  obtain ⟨hf, hst⟩ := hstep s hI
  by_cases hc : e.eval s.env = 0
  · exact ⟨s, (loop_stop hf hc).mono (by omega), hI, hc⟩
  · obtain ⟨s₁, h₁, hI₁, hμ, hφ⟩ := hst hc
    obtain ⟨s', h', hI', hc'⟩ := ih _ (by omega) s₁ rfl hI₁
    refine ⟨s', (loop_cons hf hc h₁ h').mono ?_, hI', hc'⟩
    have e1 : K * (φ s - φ s₁) + K * φ s₁ = K * φ s := by
      rw [← mul_add, Nat.sub_add_cancel hφ]
    have e2 : μ s₁ * (K₀ + condCost w e) + (K₀ + condCost w e) ≤ m * (K₀ + condCost w e) := by
      rw [← add_one_mul]; exact Nat.mul_le_mul_right _ (by omega)
    omega

end Good

/-! ## Moving words -/

/-- Move the top `cnt` words of `src` onto `dst` (counter `i`, value register `t`). -/
def moveN (src dst : Fin Q) (cnt i t : Fin R) : CStm R Q :=
  .seq (.set i (.const 0))
    (.loop (.lt (rv i) (rv cnt))
      (.seq (.pop src t) (.seq (.push dst (rv t)) (.set i (.add (rv i) (.const 1))))))

/-- The effect of a routine on the rest of the state: cursor, output and all registers
outside `regs` are kept. -/
def Frame (st st' : NSt R Q) (regs : List (Fin R)) : Prop :=
  st'.pos = st.pos ∧ st'.out = st.out ∧ ∀ r ∉ regs, st'.env r = st.env r

lemma Frame.refl (st : NSt R Q) (regs : List (Fin R)) : Frame st st regs :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

lemma Frame.trans {st₁ st₂ st₃ : NSt R Q} {regs : List (Fin R)} (h₁ : Frame st₁ st₂ regs)
    (h₂ : Frame st₂ st₃ regs) : Frame st₁ st₃ regs :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, fun r hr => (h₂.2.2 r hr).trans (h₁.2.2 r hr)⟩

lemma Frame.mono {st st' : NSt R Q} {regs regs' : List (Fin R)} (h : Frame st st' regs)
    (hs : regs ⊆ regs') : Frame st st' regs' :=
  ⟨h.1, h.2.1, fun r hr => h.2.2 r (fun h' => hr (hs h'))⟩

/-- The stacks after moving `n` words from `src` to `dst`. -/
def movedStk (S : Fin Q → List ℕ) (src dst : Fin Q) (n : ℕ) : Fin Q → List ℕ :=
  Function.update (Function.update S src ((S src).drop n)) dst (((S src).take n).reverse ++ S dst)

lemma movedStk_zero (S : Fin Q → List ℕ) (src dst : Fin Q) (h : src ≠ dst) :
    movedStk S src dst 0 = S := by
  funext q; unfold movedStk
  by_cases h1 : q = dst
  · subst h1; simp
  · by_cases h2 : q = src
    · subst h2; simp [Function.update_of_ne h1]
    · simp [Function.update_of_ne h1, Function.update_of_ne h2]

lemma movedStk_src (S : Fin Q → List ℕ) {src dst : Fin Q} (h : src ≠ dst) (n : ℕ) :
    movedStk S src dst n src = (S src).drop n := by
  simp [movedStk, Function.update_of_ne h]

lemma movedStk_dst (S : Fin Q → List ℕ) (src dst : Fin Q) (n : ℕ) :
    movedStk S src dst n dst = ((S src).take n).reverse ++ S dst := by
  simp [movedStk]

lemma movedStk_other (S : Fin Q → List ℕ) {src dst q : Fin Q} (h₁ : q ≠ src) (h₂ : q ≠ dst)
    (n : ℕ) : movedStk S src dst n q = S q := by
  simp [movedStk, Function.update_of_ne h₁, Function.update_of_ne h₂]

lemma moveN_good {src dst : Fin Q} {cnt i t : Fin R} (hsd : src ≠ dst) (hci : cnt ≠ i)
    (hct : cnt ≠ t) (hit : i ≠ t) (st : NSt R Q) {n : ℕ} (hn : st.env cnt = n)
    (hlen : n ≤ (st.stk src).length) (hw : n + 1 < 2 ^ w)
    (hb : ∀ v ∈ (st.stk src).take n, v < 2 ^ w) :
    ∃ st', Good x w (moveN src dst cnt i t) st st' ((n + 1) * (12 * Ex.nodeCost w)) ∧
      st'.stk = movedStk st.stk src dst n ∧ Frame st st' [i, t] := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  -- the loop invariant
  set Inv : NSt R Q → Prop := fun s => s.env i ≤ n ∧ s.env cnt = n ∧
    s.stk = movedStk st.stk src dst (s.env i) ∧ Frame st s [i, t]
  have hloop := Good.loop_var (x := x) (w := w) (e := .lt (rv i) (rv cnt))
    (body := .seq (.pop src t) (.seq (.push dst (rv t)) (.set i (.add (rv i) (.const 1)))))
    Inv (fun s => n - s.env i) (fun _ => 0) 0 (8 * Ex.nodeCost w) (by
      intro s ⟨hi, hc, hs, hf⟩
      refine ⟨⟨by simp only [rv, Ex.Fits]; omega, by simp only [rv, Ex.Fits]; omega⟩, ?_⟩
      intro hcond
      have hlt : s.env i < n := by simpa [rv, Ex.eval, hc] using hcond
      have hsrc : s.stk src = (st.stk src).drop (s.env i) := by rw [hs, movedStk_src _ hsd]
      have hd := List.drop_eq_getElem_cons (show s.env i < (st.stk src).length by omega)
      have hv : (st.stk src)[s.env i] < 2 ^ w :=
        hb _ (List.mem_take_iff_getElem.mpr ⟨s.env i, by simp; omega, rfl⟩)
      refine ⟨_, ((Good.pop src t).seq ((Good.push ?_).seq (Good.set ?_))).mono ?_, ?_,
        ?_, le_rfl⟩
      · simp only [rv, Ex.Fits, NSt.set_env, NSt.setS_env, Function.update_self, hsrc, hd,
          List.headD_cons]
        exact hv
      · simp only [rv, Ex.Fits, Ex.eval, NSt.set_env, NSt.setS_env, Function.update_of_ne hit,
          NSt.setS_env]
        refine ⟨?_, ?_, ?_⟩
        · exact lt_trans hlt (lt_trans (Nat.lt_succ_self n) hw)
        · exact lt_of_le_of_lt (Nat.le_add_left 1 n) hw
        · exact lt_of_le_of_lt (Nat.succ_le_succ hlt.le) hw
      · simp only [rv, Ex.size]; omega
      · simp only [Inv, rv, Ex.eval, NSt.set_env, NSt.setS_env, NSt.set_stk, NSt.setS_stk,
          Function.update_self, Function.update_of_ne hit, Function.update_of_ne hci,
          Function.update_of_ne hct]
        refine ⟨by omega, hc, ?_, ?_⟩
        · rw [hsrc, hd]
          funext q
          simp only [movedStk, List.headD_cons, List.tail_cons]
          by_cases h1 : q = dst
          · subst h1
            simp only [Function.update_self, Function.update_of_ne hsd.symm]
            have ht : (st.stk src).take (s.env i + 1) =
                (st.stk src).take (s.env i) ++ [(st.stk src)[s.env i]] := by
              rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]; rfl
            rw [hs, movedStk_dst, ht]
            simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
              List.singleton_append, List.cons_append, List.append_assoc]
          · by_cases h2 : q = src
            · subst h2; simp [Function.update_of_ne h1]
            · simp only [Function.update_of_ne h1, Function.update_of_ne h2]
              rw [hs, movedStk_other _ h2 h1]
        · refine ⟨hf.1, hf.2.1, fun r hr => ?_⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp only [NSt.set_env, NSt.setS_env, Function.update_of_ne hr.1,
            Function.update_of_ne hr.2]
          exact hf.2.2 r (by simp [hr.1, hr.2])
      · simp only [rv, Ex.eval, NSt.set_env, NSt.setS_env, Function.update_self, Function.update_of_ne hit]; omega)
  have h0 : Good x w (.set i (.const 0) : CStm R Q) st (st.set i 0) (Ex.nodeCost w + unitCost w) :=
    (Good.set (by simp only [Ex.Fits]; omega)).of_eq (by simp [Ex.eval]) (by simp [Ex.size])
  obtain ⟨s', h', ⟨hi', hc', hs', hf'⟩, hend⟩ := hloop (st.set i 0) ⟨by simp, by
    simp [Function.update_of_ne hci, hn], by simp [movedStk_zero _ _ _ hsd], ⟨rfl, rfl, fun r hr => by
      simp at hr; simp [Function.update_of_ne hr.1]⟩⟩
  have hin : s'.env i = n := by
    simp only [rv, Ex.eval, hc'] at hend; split_ifs at hend <;> omega
  refine ⟨s', (h0.seq h').mono ?_, by rw [hs', hin], hf'⟩
  simp only [condCost, rv, Ex.size, Nat.sub_zero, mul_zero, zero_add]
  rw [show st.set i 0 = st.set i 0 from rfl]
  simp only [NSt.set_env, Function.update_self, Nat.sub_zero]
  nlinarith

end CStm

end Lax119563Proofs.Compiler

end Compiler_CSortLoop

/-! ### Formerly `Lax119563Proofs.Compiler.CEmit` -/

section Compiler_CEmit

/-!
# Emitting a stack

* `emitAllS q t f`: pop all of `q`, emitting each value (`emitAllS_good`: the output is
  extended by the stack, top first).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

namespace CStm

/-- Pop all of `q`, emitting the values. -/
def emitAllS (q : Fin Q) (t f : Fin R) : CStm R Q :=
  .seq (.sne f q) (.loop (rv f) (.seq (.pop q t) (.seq (.emit (rv t)) (.sne f q))))

/-- The state of `emitAllS` before iteration `j`. -/
def emSt (st : NSt R Q) (q : Fin Q) (t f : Fin R) (j : ℕ) : NSt R Q :=
  ⟨Function.update (Function.update st.env t
      (if j = 0 then st.env t else (st.stk q).getD (j - 1) 0)) f
      (if j < (st.stk q).length then 1 else 0),
    Function.update st.stk q ((st.stk q).drop j), st.pos, st.out ++ (st.stk q).take j⟩

lemma emitAllS_good (hw : 2 ≤ w) {q : Fin Q} {t f : Fin R} (htf : t ≠ f)
    (st : NSt R Q) (hb : st.Bdd w) :
    ∃ st' : NSt R Q, Good x w (emitAllS q t f) st st'
        (((st.stk q).length + 1) * (10 * Ex.nodeCost w)) ∧
      st'.stk = Function.update st.stk q [] ∧
      st'.pos = st.pos ∧ st'.out = st.out ++ st.stk q ∧
      ∀ r, r ≠ t → r ≠ f → st'.env r = st.env r := by
  have h2 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have hU := nodeCost_ge w
  have hU' := unitCost_ge w
  have hlb : ∀ v ∈ st.stk q, v < 2 ^ w := hb.2 q
  have hfq : ∀ j, (emSt st q t f j).env f = if j < (st.stk q).length then 1 else 0 := by
    intro j; simp [emSt]
  have hsq : ∀ j, (emSt st q t f j).stk q = (st.stk q).drop j := by
    intro j; simp [emSt]
  have hbody : ∀ j < (st.stk q).length,
      Good x w (.seq (.pop q t) (.seq (.emit (rv t)) (.sne f q)))
        (emSt st q t f j) (emSt st q t f (j + 1)) (8 * Ex.nodeCost w) := by
    intro j hj
    have hd : (st.stk q).drop j = (st.stk q)[j] :: (st.stk q).drop (j + 1) :=
      List.drop_eq_getElem_cons hj
    refine ((Good.pop q t).seq ((Good.emit ?_).seq (Good.sne f q))).of_eq ?_ ?_
    · simp only [rv, Ex.Fits, NSt.set_env, NSt.setS_env, Function.update_self]
      rw [hsq, hd]; exact hlb _ (List.getElem_mem _)
    · rw [hsq, hd]
      refine NSt.ext (funext fun r => ?_) (funext fun r => ?_) ?_ ?_
      · simp only [emSt, NSt.set_env, NSt.setS_env, NSt.set_stk, NSt.setS_stk, rv, Ex.eval,
          Function.update_self, List.headD_cons, List.tail_cons]
        by_cases hrf : r = f
        · subst hrf
          simp only [Function.update_self, List.isEmpty_iff, List.drop_eq_nil_iff]
          split_ifs <;> omega
        · by_cases hrt : r = t
          · subst hrt; simp [Function.update_of_ne hrf, Function.update_of_ne htf,
              List.getElem?_eq_getElem hj]
          · simp [Function.update_of_ne hrf, Function.update_of_ne hrt]
      · simp only [emSt, NSt.set_stk, NSt.setS_stk, List.tail_cons]
        by_cases hrq : r = q
        · subst hrq; simp
        · simp [Function.update_of_ne hrq]
      · simp [emSt]
      · simp only [emSt, NSt.set_env, NSt.setS_env, NSt.set_stk, NSt.setS_stk, rv, Ex.eval,
          Function.update_self, List.headD_cons, NSt.set_out, NSt.setS_out]
        rw [List.take_add_one, List.getElem?_eq_getElem hj, List.append_assoc]
        rfl
    · simp only [rv, Ex.size]; omega
  have hloop := Good.loop_const (x := x) (w := w) (e := rv f) (st.stk q).length
    (emSt st q t f) (8 * Ex.nodeCost w)
    (fun j hj => by simp [rv, Ex.eval, hfq, hj])
    (by simp [rv, Ex.eval, hfq])
    (fun j _ => by simp only [rv, Ex.Fits, hfq]; split_ifs <;> omega)
    hbody
  have hinit : Good x w (.sne f q) st (emSt st q t f 0) (2 * unitCost w + 1) := by
    refine (Good.sne f q).of_eq ?_ le_rfl
    refine NSt.ext (funext fun r => ?_) (funext fun r => ?_) ?_ ?_
    · simp only [emSt, NSt.set_env, if_true]
      by_cases hrf : r = f
      · subst hrf; simp only [Function.update_self]
        rcases h : st.stk q with _ | ⟨a, l⟩ <;> simp
      · by_cases hrt : r = t
        · subst hrt; simp [Function.update_of_ne hrf]
        · simp [Function.update_of_ne hrf, Function.update_of_ne hrt]
    · simp only [emSt, NSt.set_stk, List.drop_zero]
      by_cases hrq : r = q
      · subst hrq; simp
      · simp [Function.update_of_ne hrq]
    · simp [emSt]
    · simp [emSt]
  refine ⟨emSt st q t f (st.stk q).length, (hinit.seq hloop).mono ?_, ?_, rfl, ?_,
    fun r hrt hrf => ?_⟩
  · simp only [condCost, rv, Ex.size]; nlinarith
  · simp [emSt]
  · simp [emSt]
  · simp [emSt, Function.update_of_ne hrt, Function.update_of_ne hrf]

end CStm

end Lax119563Proofs.Compiler

end Compiler_CEmit

/-! ### Formerly `Lax119563Proofs.Compiler.CFrame` -/

section Compiler_CFrame

/-!
# Syntactic frames of statements

`wReg r c`, `wStk q c`, `wOut c`, `wPos c`: whether the statement `c` contains an
instruction writing the register `r`, the stack `q`, the output, the cursor. If not, the
denotation keeps that part of the state (`exec_env_of`, `exec_stk_of`, `exec_out_of`,
`exec_pos_of`); for concrete programs the flags are computed by `decide`.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ} {x : List Bool}

namespace CStm

/-- `c` may write register `r`. -/
def wReg (r : Fin R) : CStm R Q → Bool
  | skip => false
  | set r' _ => decide (r' = r)
  | emit _ => false
  | push _ _ => false
  | pop _ r' => decide (r' = r)
  | sne r' _ => decide (r' = r)
  | rd r' => decide (r' = r)
  | rst => false
  | seq p q => wReg r p || wReg r q
  | ite _ p q => wReg r p || wReg r q
  | loop _ b => wReg r b

/-- `c` may write stack `q`. -/
def wStk (q : Fin Q) : CStm R Q → Bool
  | push q' _ => decide (q' = q)
  | pop q' _ => decide (q' = q)
  | seq p p' => wStk q p || wStk q p'
  | ite _ p p' => wStk q p || wStk q p'
  | loop _ b => wStk q b
  | _ => false

/-- `c` may emit. -/
def wOut : CStm R Q → Bool
  | emit _ => true
  | seq p q => wOut p || wOut q
  | ite _ p q => wOut p || wOut q
  | loop _ b => wOut b
  | _ => false

/-- `c` may move the cursor. -/
def wPos : CStm R Q → Bool
  | rd _ => true
  | rst => true
  | seq p q => wPos p || wPos q
  | ite _ p q => wPos p || wPos q
  | loop _ b => wPos b
  | _ => false

lemma iterate_pres {α β : Type*} {f : α → α} {g : α → β} (h : ∀ a, g (f a) = g a) :
    ∀ (n : ℕ) (a : α), g (f^[n] a) = g a
  | 0, _ => rfl
  | n + 1, a => by rw [Function.iterate_succ_apply, iterate_pres h n (f a), h]

open Classical in
lemma exec_loop_cases (c : Ex R) (b : CStm R Q) (st : NSt R Q) :
    ∃ n, exec x (loop c b) st = (exec x b)^[n] st := by
  simp only [exec]
  split
  · exact ⟨_, rfl⟩
  · exact ⟨0, rfl⟩

theorem exec_env_of {r : Fin R} : ∀ (c : CStm R Q) (st : NSt R Q), wReg r c = false →
    (exec x c st).env r = st.env r
  | skip, _, _ => rfl
  | set r' e, st, h => by
    simp only [wReg, decide_eq_false_iff_not] at h
    simp [exec, Function.update_of_ne (Ne.symm h)]
  | emit _, _, _ => rfl
  | push _ _, _, _ => rfl
  | pop q r', st, h => by
    simp only [wReg, decide_eq_false_iff_not] at h
    simp [exec, Function.update_of_ne (Ne.symm h)]
  | sne r' q, st, h => by
    simp only [wReg, decide_eq_false_iff_not] at h
    simp [exec, Function.update_of_ne (Ne.symm h)]
  | rd r', st, h => by
    simp only [wReg, decide_eq_false_iff_not] at h
    simp [exec, Function.update_of_ne (Ne.symm h)]
  | rst, _, _ => rfl
  | seq p q, st, h => by
    simp only [wReg, Bool.or_eq_false_iff] at h
    simp only [exec]; rw [exec_env_of q _ h.2, exec_env_of p _ h.1]
  | ite c p q, st, h => by
    simp only [wReg, Bool.or_eq_false_iff] at h
    simp only [exec]; split
    · exact exec_env_of p _ h.1
    · exact exec_env_of q _ h.2
  | loop c b, st, h => by
    obtain ⟨n, hn⟩ := exec_loop_cases (x := x) c b st
    rw [hn]
    exact iterate_pres (g := fun s : NSt R Q => s.env r) (fun a => exec_env_of b a h) n st

theorem exec_stk_of {q : Fin Q} : ∀ (c : CStm R Q) (st : NSt R Q), wStk q c = false →
    (exec x c st).stk q = st.stk q
  | skip, _, _ => rfl
  | set _ _, _, _ => rfl
  | emit _, _, _ => rfl
  | push q' e, st, h => by
    simp only [wStk, decide_eq_false_iff_not] at h
    simp [exec, Function.update_of_ne (Ne.symm h)]
  | pop q' r, st, h => by
    simp only [wStk, decide_eq_false_iff_not] at h
    simp [exec, Function.update_of_ne (Ne.symm h)]
  | sne _ _, _, _ => rfl
  | rd _, _, _ => rfl
  | rst, _, _ => rfl
  | seq p p', st, h => by
    simp only [wStk, Bool.or_eq_false_iff] at h
    simp only [exec]; rw [exec_stk_of p' _ h.2, exec_stk_of p _ h.1]
  | ite c p p', st, h => by
    simp only [wStk, Bool.or_eq_false_iff] at h
    simp only [exec]; split
    · exact exec_stk_of p _ h.1
    · exact exec_stk_of p' _ h.2
  | loop c b, st, h => by
    obtain ⟨n, hn⟩ := exec_loop_cases (x := x) c b st
    rw [hn]
    exact iterate_pres (g := fun s : NSt R Q => s.stk q) (fun a => exec_stk_of b a h) n st

theorem exec_out_of : ∀ (c : CStm R Q) (st : NSt R Q), wOut c = false →
    (exec x c st).out = st.out
  | skip, _, _ => rfl
  | set _ _, _, _ => rfl
  | emit _, _, h => by simp [wOut] at h
  | push _ _, _, _ => rfl
  | pop _ _, _, _ => rfl
  | sne _ _, _, _ => rfl
  | rd _, _, _ => rfl
  | rst, _, _ => rfl
  | seq p q, st, h => by
    simp only [wOut, Bool.or_eq_false_iff] at h
    simp only [exec]; rw [exec_out_of q _ h.2, exec_out_of p _ h.1]
  | ite c p q, st, h => by
    simp only [wOut, Bool.or_eq_false_iff] at h
    simp only [exec]; split
    · exact exec_out_of p _ h.1
    · exact exec_out_of q _ h.2
  | loop c b, st, h => by
    obtain ⟨n, hn⟩ := exec_loop_cases (x := x) c b st
    rw [hn]
    exact iterate_pres (g := fun s : NSt R Q => s.out) (fun a => exec_out_of b a h) n st

theorem exec_pos_of : ∀ (c : CStm R Q) (st : NSt R Q), wPos c = false →
    (exec x c st).pos = st.pos
  | skip, _, _ => rfl
  | set _ _, _, _ => rfl
  | emit _, _, _ => rfl
  | push _ _, _, _ => rfl
  | pop _ _, _, _ => rfl
  | sne _ _, _, _ => rfl
  | rd _, _, h => by simp [wPos] at h
  | rst, _, h => by simp [wPos] at h
  | seq p q, st, h => by
    simp only [wPos, Bool.or_eq_false_iff] at h
    simp only [exec]; rw [exec_pos_of q _ h.2, exec_pos_of p _ h.1]
  | ite c p q, st, h => by
    simp only [wPos, Bool.or_eq_false_iff] at h
    simp only [exec]; split
    · exact exec_pos_of p _ h.1
    · exact exec_pos_of q _ h.2
  | loop c b, st, h => by
    obtain ⟨n, hn⟩ := exec_loop_cases (x := x) c b st
    rw [hn]
    exact iterate_pres (g := fun s : NSt R Q => s.pos) (fun a => exec_pos_of b a h) n st

/-! ## Frames of `Good` statements -/

variable {w : ℕ} {c : CStm R Q} {st st' : NSt R Q} {T : ℕ}

lemma Good.env_of (h : Good x w c st st' T) {r : Fin R} (hr : wReg r c = false) :
    st'.env r = st.env r := by rw [← h.2.1]; exact exec_env_of c st hr

lemma Good.stk_of (h : Good x w c st st' T) {q : Fin Q} (hq : wStk q c = false) :
    st'.stk q = st.stk q := by rw [← h.2.1]; exact exec_stk_of c st hq

lemma Good.out_of (h : Good x w c st st' T) (ho : wOut c = false) : st'.out = st.out := by
  rw [← h.2.1]; exact exec_out_of c st ho

lemma Good.pos_of (h : Good x w c st st' T) (hp : wPos c = false) : st'.pos = st.pos := by
  rw [← h.2.1]; exact exec_pos_of c st hp

end CStm

end Lax119563Proofs.Compiler

end Compiler_CFrame

/-! ### Formerly `Lax119563Proofs.Compiler.CArith` -/

section Compiler_CArith

/-!
# Small arithmetic and stack routines

* `mulS dst a b j`: `dst := a · b` by repeated addition (`mulS_good`);
* `predS dst n`: `dst := n - 1` by counting (`predS_good`);
* `pushZS q n j`: push `n` zeros onto `q` (`pushZS_good`);
* `mvSumN src dst n j t acc`: move the top `n` words of `src` onto `dst` (reversed),
  adding them to `acc` (`mvSumN_good`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

namespace CStm

lemma set_set_same (st : NSt R Q) (r : Fin R) (u v : ℕ) :
    (st.set r u).set r v = st.set r v := by
  simp only [NSt.set, Function.update_idem]

/-! ## Multiplication -/

/-- `dst := a · b` (counter `j`). -/
def mulS (dst a b j : Fin R) : CStm R Q :=
  .seq (.set dst (.const 0)) (.seq (.set j (.const 0))
    (.loop (.lt (rv j) (rv b))
      (.seq (.set dst (.add (rv dst) (rv a))) (.set j (.add (rv j) (.const 1))))))

lemma mulS_good (hw : 2 ≤ w) {dst a b j : Fin R} (hda : dst ≠ a) (hdb : dst ≠ b) (hdj : dst ≠ j)
    (haj : a ≠ j) (hbj : b ≠ j) (st : NSt R Q) {A B : ℕ} (hA : st.env a = A)
    (hB : st.env b = B) (hAB : A * B < 2 ^ w) (hBw : B < 2 ^ w) :
    Good x w (mulS dst a b j) st ((st.set dst (A * B)).set j B)
      ((B + 1) * (12 * Ex.nodeCost w)) := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h1 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  set S : ℕ → NSt R Q := fun i => (st.set dst (A * i)).set j i with hS
  have eA : ∀ i, (S i).env a = A := fun i => by
    simp [S, Function.update_of_ne haj, Function.update_of_ne (Ne.symm hda), hA]
  have eB : ∀ i, (S i).env b = B := fun i => by
    simp [S, Function.update_of_ne hbj, Function.update_of_ne (Ne.symm hdb), hB]
  have eD : ∀ i, (S i).env dst = A * i := fun i => by
    simp [S, Function.update_of_ne hdj]
  have eJ : ∀ i, (S i).env j = i := fun i => by simp [S]
  have hloop := Good.loop_const (x := x) (w := w) (e := .lt (rv j) (rv b))
    (body := .seq (.set dst (.add (rv dst) (rv a))) (.set j (.add (rv j) (.const 1))))
    B S (8 * Ex.nodeCost w)
    (fun i hi => by simp only [Ex.eval, rv, eJ, eB, if_pos hi]; omega)
    (by simp only [Ex.eval, rv, eJ, eB]; simp)
    (fun i hi => by simp only [Ex.Fits, rv, eJ, eB]; omega)
    (fun i hi => by
      have hAi : A * (i + 1) ≤ A * B := Nat.mul_le_mul_left _ hi
      refine ((Good.set ?_).seq (Good.set ?_)).of_eq ?_ ?_
      · simp only [Ex.Fits, rv, eD, eA, Ex.eval]
        refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
      · simp only [Ex.Fits, rv, Ex.eval, NSt.set_env, Function.update_of_ne (Ne.symm hdj), eJ]
        omega
      · simp only [S]
        rcases st with ⟨env, stk, pos, out⟩
        simp only [NSt.set, Ex.eval, rv, NSt.mk.injEq, and_true]
        funext r
        simp only [Function.update_apply]
        split_ifs <;> simp_all <;> ring
      · simp only [Ex.size]; omega)
  have h0 := Good.set (x := x) (w := w) (r := dst) (e := .const 0) (st := st)
    (by simp only [Ex.Fits]; omega)
  have h0' := Good.set (x := x) (w := w) (r := j) (e := .const 0)
    (st := st.set dst ((Ex.const 0 : Ex R).eval st.env)) (by simp only [Ex.Fits]; omega)
  have hS0 : (st.set dst ((Ex.const 0 : Ex R).eval st.env)).set j
      ((Ex.const 0 : Ex R).eval (st.set dst ((Ex.const 0 : Ex R).eval st.env)).env) = S 0 := by
    simp [S, Ex.eval]
  rw [hS0] at h0'
  refine ((h0.seq (h0'.seq hloop)).mono ?_)
  simp only [condCost, Ex.size, rv]
  nlinarith

/-! ## Predecessor -/

/-- `dst := n - 1` (for `n ≥ 1`; `0` for `n = 0`). -/
def predS (dst n : Fin R) : CStm R Q :=
  .seq (.set dst (.const 0)) (.loop (.lt (.add (rv dst) (.const 1)) (rv n))
    (.set dst (.add (rv dst) (.const 1))))

lemma predS_good (hw : 2 ≤ w) {dst n : Fin R} (hdn : dst ≠ n) (st : NSt R Q) {N : ℕ}
    (hN : st.env n = N) (hNw : N + 1 < 2 ^ w) :
    Good x w (predS dst n) st (st.set dst (N - 1)) ((N + 1) * (12 * Ex.nodeCost w)) := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  set S : ℕ → NSt R Q := fun i => st.set dst i with hS
  have eD : ∀ i, (S i).env dst = i := fun i => by simp [S]
  have eN : ∀ i, (S i).env n = N := fun i => by simp [S, Function.update_of_ne (Ne.symm hdn), hN]
  have hloop := Good.loop_const (x := x) (w := w) (e := .lt (.add (rv dst) (.const 1)) (rv n))
    (body := .set dst (.add (rv dst) (.const 1))) (N - 1) S (4 * Ex.nodeCost w)
    (fun i hi => by simp only [Ex.eval, rv, eD, eN]; rw [if_pos (by omega)]; omega)
    (by simp only [Ex.eval, rv, eD, eN]; rw [if_neg (by omega)])
    (fun i hi => by simp only [Ex.Fits, Ex.eval, rv, eD, eN]; omega)
    (fun i hi => (Good.set (by simp only [Ex.Fits, Ex.eval, rv, eD]; omega)).of_eq
      (by simp only [Ex.eval, rv, eD, S, set_set_same]) (by simp only [Ex.size]; omega))
  refine (((Good.set (by simp only [Ex.Fits]; omega)).seq hloop).of_eq rfl ?_)
  simp only [condCost, Ex.size, rv]
  have : N - 1 ≤ N := Nat.sub_le N 1
  nlinarith

/-! ## Pushing zeros -/

/-- Push `n` zeros onto `q` (counter `j`). -/
def pushZS (q : Fin Q) (n j : Fin R) : CStm R Q :=
  .seq (.set j (.const 0)) (.loop (.lt (rv j) (rv n))
    (.seq (.push q (.const 0)) (.set j (.add (rv j) (.const 1)))))

lemma pushZS_good (hw : 2 ≤ w) {q : Fin Q} {n j : Fin R} (hnj : n ≠ j) (st : NSt R Q) {N : ℕ}
    (hN : st.env n = N) (hNw : N + 1 < 2 ^ w) :
    Good x w (pushZS q n j) st ((st.setS q (List.replicate N 0 ++ st.stk q)).set j N)
      ((N + 1) * (12 * Ex.nodeCost w)) := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  set S : ℕ → NSt R Q := fun i => (st.setS q (List.replicate i 0 ++ st.stk q)).set j i with hS
  have eJ : ∀ i, (S i).env j = i := fun i => by simp [S]
  have eN : ∀ i, (S i).env n = N := fun i => by simp [S, Function.update_of_ne hnj, hN]
  have hloop := Good.loop_const (x := x) (w := w) (e := .lt (rv j) (rv n))
    (body := .seq (.push q (.const 0)) (.set j (.add (rv j) (.const 1)))) N S
    (6 * Ex.nodeCost w)
    (fun i hi => by simp only [Ex.eval, rv, eJ, eN, if_pos hi]; omega)
    (by simp only [Ex.eval, rv, eJ, eN]; simp)
    (fun i hi => by simp only [Ex.Fits, rv, eJ, eN]; omega)
    (fun i hi => ((Good.push (by simp only [Ex.Fits]; omega)).seq
      (Good.set (by simp only [Ex.Fits, Ex.eval, rv, NSt.setS_env, eJ]; omega))).of_eq
      (by
        simp only [Ex.eval, rv, NSt.setS_env, eJ, S]
        simp only [NSt.set, NSt.setS, Function.update_idem, Function.update_self,
          List.replicate_succ, List.cons_append])
      (by simp only [Ex.size]; omega))
  have hS0 : st.set j ((Ex.const 0 : Ex R).eval st.env) = S 0 := by
    simp [S, Ex.eval, NSt.setS]
  have h0 := Good.set (x := x) (w := w) (r := j) (e := .const 0) (st := st)
    (by simp only [Ex.Fits]; omega)
  rw [hS0] at h0
  refine (h0.seq hloop).mono ?_
  simp only [condCost, Ex.size, rv]
  nlinarith

/-! ## Moving and summing -/

/-- Move the top `n` words of `src` onto `dst`, adding them to `acc`. -/
def mvSumN (src dst : Fin Q) (n j t acc : Fin R) : CStm R Q :=
  .seq (.set j (.const 0)) (.loop (.lt (rv j) (rv n))
    (.seq (.pop src t) (.seq (.push dst (rv t))
      (.seq (.set acc (.add (rv acc) (rv t))) (.set j (.add (rv j) (.const 1)))))))

lemma mvSumN_good (hw : 2 ≤ w) {src dst : Fin Q} {n j t acc : Fin R} (hsd : src ≠ dst)
    (hnj : n ≠ j) (hnt : n ≠ t) (hna : n ≠ acc) (hjt : j ≠ t) (hja : j ≠ acc) (hta : t ≠ acc)
    (st : NSt R Q) {N : ℕ} (hN : st.env n = N) (hlen : N ≤ (st.stk src).length)
    (hNw : N + 1 < 2 ^ w) (hsum : st.env acc + ((st.stk src).take N).sum < 2 ^ w) :
    ∃ st', Good x w (mvSumN src dst n j t acc) st st' ((N + 1) * (16 * Ex.nodeCost w)) ∧
      st'.stk = movedStk st.stk src dst N ∧
      st'.env acc = st.env acc + ((st.stk src).take N).sum ∧ Frame st st' [j, t, acc] := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  set A0 := st.env acc
  set L := st.stk src
  set Inv : NSt R Q → Prop := fun s => s.env j ≤ N ∧ s.env n = N ∧
    s.stk = movedStk st.stk src dst (s.env j) ∧ s.env acc = A0 + (L.take (s.env j)).sum ∧
    Frame st s [j, t, acc]
  have hloop := Good.loop_var (x := x) (w := w) (e := .lt (rv j) (rv n))
    (body := .seq (.pop src t) (.seq (.push dst (rv t))
      (.seq (.set acc (.add (rv acc) (rv t))) (.set j (.add (rv j) (.const 1))))))
    Inv (fun s => N - s.env j) (fun _ => 0) 0 (12 * Ex.nodeCost w) (by
      intro s ⟨hi, hn, hs, ha, hf⟩
      refine ⟨by simp only [Ex.Fits, rv, hn]; omega, fun hc => ?_⟩
      have hlt : s.env j < N := by simpa [rv, Ex.eval, hn] using hc
      obtain ⟨i, hi'⟩ : ∃ i, s.env j = i := ⟨_, rfl⟩
      rw [hi'] at hlt hs ha hi
      have hsrc : s.stk src = L.drop i := by rw [hs, movedStk_src _ hsd]
      have hd := List.drop_eq_getElem_cons (show i < L.length by omega)
      have hsplit : (L.take (i + 1)).sum = (L.take i).sum + L[i] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
          List.sum_append, List.sum_singleton]
      have hmono : (L.take (i + 1)).sum ≤ (L.take N).sum := by
        rw [← List.take_append_drop (i + 1) (L.take N), List.take_take,
          min_eq_left (by omega), List.sum_append]; omega
      have hhead : (s.stk src).headD 0 = L[i] := by rw [hsrc, hd]; rfl
      have htail : (s.stk src).tail = L.drop (i + 1) := by rw [hsrc, hd]; rfl
      set s1 := (s.setS src (s.stk src).tail).set t ((s.stk src).headD 0)
      have e1t : s1.env t = L[i] := by simp only [s1, NSt.set_env, Function.update_self]; exact hhead
      have e1a : s1.env acc = A0 + (L.take i).sum := by
        simp [s1, Function.update_of_ne hta.symm, ha]
      have e1j : s1.env j = i := by simp [s1, Function.update_of_ne hjt, hi']
      have e1n : s1.env n = N := by simp [s1, Function.update_of_ne hnt, hn]
      have e1s : s1.stk = Function.update s.stk src (L.drop (i + 1)) := by simp [s1, htail]
      set s2 := s1.setS dst ((rv t : Ex R).eval s1.env :: s1.stk dst)
      have e2 : s2.env = s1.env := rfl
      set s3 := s2.set acc ((Ex.add (rv acc) (rv t)).eval s2.env)
      have e3a : s3.env acc = A0 + (L.take (i + 1)).sum := by
        simp [s3, e2, Ex.eval, rv, e1a, e1t, hsplit]; ring
      have e3j : s3.env j = i := by simp [s3, Function.update_of_ne hja, e2, e1j]
      set s4 := s3.set j ((Ex.add (rv j) (.const 1)).eval s3.env)
      have e4j : s4.env j = i + 1 := by simp [s4, Ex.eval, rv, e3j]
      have e4 : ∀ r, r ≠ j → r ≠ acc → r ≠ t → s4.env r = s.env r := by
        intro r h1 h2 h3
        simp [s4, s3, e2, s1, Function.update_of_ne h1, Function.update_of_ne h2,
          Function.update_of_ne h3]
      refine ⟨s4, ((Good.pop src t).seq ((Good.push ?_).seq ((Good.set ?_).seq
        (Good.set ?_)))).mono ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, le_rfl⟩
      · show s1.env t < 2 ^ w
        rw [e1t]; omega
      · show s1.env acc < 2 ^ w ∧ s1.env t < 2 ^ w ∧ s1.env acc + s1.env t < 2 ^ w
        rw [e1t, e1a]; omega
      · show s3.env j < 2 ^ w ∧ 1 < 2 ^ w ∧ s3.env j + 1 < 2 ^ w
        rw [e3j]; omega
      · simp only [Ex.size, rv]; omega
      · rw [e4j]; omega
      · rw [e4 _ hnj hna hnt, hn]
      · rw [e4j]
        show Function.update s1.stk dst (s1.env t :: s1.stk dst) = _
        rw [e1t, e1s, hs]
        funext q
        unfold movedStk
        by_cases h1 : q = dst
        · subst h1
          simp only [Function.update_self, Function.update_of_ne hsd.symm]
          rw [show st.stk src = L from rfl, List.take_add_one,
            List.getElem?_eq_getElem (by omega)]
          simp only [List.reverse_append, Option.toList_some, List.reverse_cons,
            List.reverse_nil, List.nil_append, List.singleton_append, List.cons_append]
        · by_cases h2 : q = src
          · subst h2; simp [Function.update_of_ne h1]; rfl
          · simp [Function.update_of_ne h1, Function.update_of_ne h2]
      · rw [e4j]; simpa [s4, Function.update_of_ne hja.symm] using e3a
      · refine ⟨hf.1, hf.2.1, fun r hr => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [e4 r hr.1 hr.2.2 hr.2.1]
        exact hf.2.2 r (by simp [hr.1, hr.2.1, hr.2.2])
      · rw [e4j]; omega)
  have h0 := Good.set (x := x) (w := w) (r := j) (e := .const 0) (st := st)
    (by simp only [Ex.Fits]; omega)
  obtain ⟨s', h', ⟨hi', hn', hs', ha', hf'⟩, hend⟩ := hloop (st.set j (Ex.eval st.env (.const 0)))
    ⟨by simp [Ex.eval], by simp [Function.update_of_ne hnj, hN],
      by simp [Ex.eval, movedStk_zero _ _ _ hsd],
      by simp [Ex.eval, Function.update_of_ne (Ne.symm hja), A0],
      ⟨rfl, rfl, fun r hr => by
        simp at hr; simp [Function.update_of_ne hr.1]⟩⟩
  have hin : s'.env j = N := by
    simp only [rv, Ex.eval, hn'] at hend; split_ifs at hend <;> omega
  refine ⟨s', (h0.seq h').mono ?_, by rw [hs', hin], by rw [ha', hin], hf'⟩
  simp only [condCost, rv, Ex.size, Nat.sub_zero, mul_zero, zero_add, NSt.set_env,
    Function.update_self, Ex.eval]
  nlinarith

end CStm

end Lax119563Proofs.Compiler

end Compiler_CArith

/-! ### Formerly `Lax119563Proofs.Compiler.CSort` -/

section Compiler_CSort

/-!
# Merge sort of records on number stacks

Records are lists of `A` words; a list of records `rs` is stored on a stack as `rs.flatten`
(first record on top, words in order).

* `mvRec`: move the top record of a stack onto another, keeping its word order
  (`mvRec_good`);
* `mvRecsB`: move records one by one while a counter is below a limit and `done < nr`
  (`mvRecsB_good`); the record order is reversed.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

namespace CStm

/-- Proves `a ≠ b` for two entries of a duplicate-free list `hreg`. -/
macro "ndup" hreg:ident : tactic =>
  `(tactic| (intro h; subst h; simp at $hreg:ident))

/-! ## Moving one record -/

/-- Move the top `A` words of `src` onto `dst` keeping their order (via `tmp`). -/
def mvRec (src dst tmp : Fin Q) (A i t : Fin R) : CStm R Q :=
  .seq (moveN src tmp A i t) (moveN tmp dst A i t)

lemma mvRec_good {src dst tmp : Fin Q} {A i t : Fin R} (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (hsd : src ≠ dst) (hAi : A ≠ i) (hAt : A ≠ t) (hit : i ≠ t) (st : NSt R Q) {a : ℕ}
    (ha : st.env A = a) (hlen : a ≤ (st.stk src).length) (hw : a + 1 < 2 ^ w)
    (hb : ∀ v ∈ (st.stk src).take a, v < 2 ^ w) :
    ∃ st', Good x w (mvRec src dst tmp A i t) st st' (2 * ((a + 1) * (12 * Ex.nodeCost w))) ∧
      st'.stk = Function.update (Function.update st.stk src ((st.stk src).drop a)) dst
        ((st.stk src).take a ++ st.stk dst) ∧ Frame st st' [i, t] := by
  obtain ⟨s1, g1, k1, f1⟩ := moveN_good (x := x) hst hAi hAt hit st ha hlen hw hb
  have ha1 : s1.env A = a := (f1.2.2 A (by simp [hAi, hAt])).trans ha
  have hta : ((st.stk src).take a).length = a := by simp; omega
  have h1t : s1.stk tmp = ((st.stk src).take a).reverse ++ st.stk tmp := by
    rw [k1, movedStk_dst]
  obtain ⟨s2, g2, k2, f2⟩ := moveN_good (x := x) htd hAi hAt hit s1 ha1
    (by rw [h1t]; simp; omega) hw
    (by
      intro v hv
      rw [h1t, List.take_left' (by simpa using hta)] at hv
      exact hb v (List.mem_reverse.mp hv))
  refine ⟨s2, (g1.seq g2).mono (by omega), ?_, f1.trans f2⟩
  rw [k2]
  funext q
  unfold movedStk
  rw [h1t, List.drop_left' (by simpa using hta), List.take_left' (by simpa using hta),
    List.reverse_reverse]
  by_cases hqd : q = dst
  · subst hqd; simp [k1, movedStk_other _ hsd.symm htd.symm]
  · by_cases hqt : q = tmp
    · subst hqt; simp [Function.update_of_ne hqd, Function.update_of_ne hst.symm]
    · by_cases hqs : q = src
      · subst hqs; simp [Function.update_of_ne hqd, Function.update_of_ne hqt, k1,
          movedStk_src _ hst]
      · simp [Function.update_of_ne hqd, Function.update_of_ne hqt, Function.update_of_ne hqs,
          k1, movedStk_other _ hqs hqt]

/-! ## Moving several records -/

/-- Move records from `src` to `dst` while `k < lim` and `done < nr` (counting both). -/
def mvRecsB (src dst tmp : Fin Q) (A lim done nr k i t : Fin R) : CStm R Q :=
  .seq (.set k (.const 0))
    (.loop (.lt (.const 1) (.add (.lt (rv k) (rv lim)) (.lt (rv done) (rv nr))))
      (.seq (mvRec src dst tmp A i t)
        (.seq (.set k (.add (rv k) (.const 1))) (.set done (.add (rv done) (.const 1))))))

/-- The stacks after moving the first `j` records of `l`. -/
def recsStk (S : Fin Q → List ℕ) (src dst : Fin Q) (l : List (List ℕ)) (L : List ℕ) (j : ℕ) :
    Fin Q → List ℕ :=
  Function.update (Function.update S src ((l.drop j).flatten ++ L)) dst
    ((l.take j).reverse.flatten ++ S dst)

lemma flatten_drop_eq {l : List (List ℕ)} {j : ℕ} (hj : j < l.length) :
    (l.drop j).flatten = l[j] ++ (l.drop (j + 1)).flatten := by
  rw [List.drop_eq_getElem_cons hj, List.flatten_cons]

lemma recsStk_step (S : Fin Q → List ℕ) {src dst : Fin Q} (hsd : src ≠ dst)
    (l : List (List ℕ)) (L : List ℕ) {j : ℕ} (hj : j < l.length) :
    Function.update (Function.update (recsStk S src dst l L j) src
      ((l.drop (j + 1)).flatten ++ L)) dst (l[j] ++ recsStk S src dst l L j dst) =
      recsStk S src dst l L (j + 1) := by
  funext q
  unfold recsStk
  by_cases hqd : q = dst
  · subst hqd
    simp only [Function.update_self]
    have ht : l.take (j + 1) = l.take j ++ [l[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
    rw [ht, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.flatten_cons, List.append_assoc]
  · by_cases hqs : q = src
    · subst hqs; simp [Function.update_of_ne hqd]
    · simp [Function.update_of_ne hqd, Function.update_of_ne hqs]

lemma two_le_pow {w : ℕ} (hw : 2 ≤ w) : 4 ≤ 2 ^ w :=
  calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw

lemma mvRecsB_good (hw2 : 2 ≤ w) {src dst tmp : Fin Q} {A lim done nr k i t : Fin R}
    (hst : src ≠ tmp) (htd : tmp ≠ dst) (hsd : src ≠ dst)
    (hreg : [A, lim, done, nr, k, i, t].Nodup) (st : NSt R Q) (l : List (List ℕ))
    (L : List ℕ) {a rl n d0 : ℕ} (ha : st.env A = a) (hl : st.env lim = rl)
    (hn : st.env nr = n) (hd : st.env done = d0) (hd0 : d0 ≤ n)
    (hS : st.stk src = l.flatten ++ L) (hrec : ∀ y ∈ l, y.length = a ∧ ∀ v ∈ y, v < 2 ^ w)
    (hm : min rl (n - d0) ≤ l.length) (hw : a + 1 < 2 ^ w) (hwl : rl + 1 < 2 ^ w)
    (hwn : n + 1 < 2 ^ w) :
    ∃ st', Good x w (mvRecsB src dst tmp A lim done nr k i t) st st'
        ((min rl (n - d0) + 1) * (50 * ((a + 1) * Ex.nodeCost w))) ∧
      st'.stk = recsStk st.stk src dst l L (min rl (n - d0)) ∧
      st'.env done = d0 + min rl (n - d0) ∧ Frame st st' [k, done, i, t] := by
  have hAi : A ≠ i := by ndup hreg
  have hAt : A ≠ t := by ndup hreg
  have hit : i ≠ t := by ndup hreg
  have hkd : k ≠ done := by ndup hreg
  have hkl : k ≠ lim := by ndup hreg
  have hkn : k ≠ nr := by ndup hreg
  have hkA : k ≠ A := by ndup hreg
  have hdl : done ≠ lim := by ndup hreg
  have hdn : done ≠ nr := by ndup hreg
  have hdA : done ≠ A := by ndup hreg
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h4 := two_le_pow hw2
  set m := min rl (n - d0) with hmdef
  set Inv : NSt R Q → Prop := fun s => ∃ j ≤ m, s.env k = j ∧ s.env done = d0 + j ∧
    s.env lim = rl ∧ s.env nr = n ∧ s.env A = a ∧ s.stk = recsStk st.stk src dst l L j ∧
    Frame st s [k, done, i, t]
  set e : Ex R := .lt (.const 1) (.add (.lt (rv k) (rv lim)) (.lt (rv done) (rv nr)))
  have hev : ∀ s, Inv s → (e.eval s.env ≠ 0 ↔ s.env k < m) := by
    rintro s ⟨j, hj, hk, hdn', hl', hn', -⟩
    simp only [e, rv, Ex.eval, hk, hdn', hl', hn']
    constructor
    · intro h; split_ifs at h with h1 h2 h3 <;> omega
    · intro h; have h1 : j < rl := by omega
      have h2 : d0 + j < n := by omega
      simp [h1, h2]
  have hloop := Good.loop_var (x := x) (w := w) (e := e)
    (body := .seq (mvRec src dst tmp A i t)
        (.seq (.set k (.add (rv k) (.const 1))) (.set done (.add (rv done) (.const 1)))))
    Inv (fun s => m - s.env k) (fun _ => 0) 0 (32 * ((a + 1) * Ex.nodeCost w)) (by
      intro s hI
      obtain ⟨j, hj, hk, hdn', hl', hn', hA', hs, hf⟩ := hI
      refine ⟨?_, ?_⟩
      · simp only [e, rv, Ex.Fits, Ex.eval, hk, hdn', hl', hn']
        refine ⟨by omega, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_⟩
        split_ifs <;> omega
      intro hc
      have hjm : j < m := by rw [← hk]; exact (hev s ⟨j, hj, hk, hdn', hl', hn', hA', hs, hf⟩).mp hc
      have hjl : j < l.length := by omega
      have hrj := hrec _ (List.getElem_mem hjl)
      have hsrc : s.stk src = l[j] ++ ((l.drop (j + 1)).flatten ++ L) := by
        rw [hs]; simp [recsStk, Function.update_of_ne hsd, flatten_drop_eq hjl]
      obtain ⟨s1, g1, k1, f1⟩ := mvRec_good (x := x) hst htd hsd hAi hAt hit s hA'
        (by rw [hsrc]; simp; omega) hw
        (by rw [hsrc, List.take_left' hrj.1]; exact hrj.2)
      have e1 : ∀ r, r ≠ i → r ≠ t → s1.env r = s.env r := fun r h1 h2 =>
        f1.2.2 r (by simp [h1, h2])
      have hk1 : s1.env k = j := by rw [e1 k (by ndup hreg) (by ndup hreg), hk]
      have hd1 : s1.env done = d0 + j := by rw [e1 done (by ndup hreg) (by ndup hreg), hdn']
      have g2 : Good x w (.set k (.add (rv k) (.const 1)) : CStm R Q) s1 (s1.set k (j + 1))
          (3 * Ex.nodeCost w + unitCost w) :=
        (Good.set (by simp only [rv, Ex.Fits, Ex.eval, hk1]; omega)).of_eq
          (by simp [rv, Ex.eval, hk1]) (by simp [Ex.size])
      have g3 : Good x w (.set done (.add (rv done) (.const 1)) : CStm R Q) (s1.set k (j + 1))
          ((s1.set k (j + 1)).set done (d0 + j + 1)) (3 * Ex.nodeCost w + unitCost w) :=
        (Good.set (by simp only [rv, Ex.Fits, Ex.eval, NSt.set_env,
            Function.update_of_ne hkd.symm, hd1]; omega)).of_eq
          (by simp [rv, Ex.eval, Function.update_of_ne hkd.symm, hd1]) (by simp [Ex.size])
      refine ⟨_, (g1.seq (g2.seq g3)).mono (by nlinarith), ⟨j + 1, by omega, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_⟩, ?_, le_rfl⟩
      · simp [Function.update_of_ne hkd]
      · simp; omega
      · simp only [NSt.set_env, Function.update_of_ne hdl.symm, Function.update_of_ne hkl.symm]
        rw [e1 lim (by ndup hreg) (by ndup hreg), hl']
      · simp only [NSt.set_env, Function.update_of_ne hdn.symm, Function.update_of_ne hkn.symm]
        rw [e1 nr (by ndup hreg) (by ndup hreg), hn']
      · simp only [NSt.set_env, Function.update_of_ne hdA.symm, Function.update_of_ne hkA.symm]
        rw [e1 A hAi hAt, hA']
      · simp only [NSt.set_stk]
        rw [k1, hsrc, List.drop_left' hrj.1, List.take_left' hrj.1, hs]
        have := recsStk_step st.stk hsd l L hjl
        rw [hs] at hsrc
        convert this using 3
      · refine ⟨?_, ?_, fun r hr => ?_⟩
        · simp [f1.1, hf.1]
        · simp [f1.2.1, hf.2.1]
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp only [NSt.set_env, Function.update_of_ne hr.2.1, Function.update_of_ne hr.1]
          rw [e1 r hr.2.2.1 hr.2.2.2]
          exact hf.2.2 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])
      · simp [Function.update_of_ne hkd]; omega)
  have g0 : Good x w (.set k (.const 0) : CStm R Q) st (st.set k 0)
      (Ex.nodeCost w + unitCost w) :=
    (Good.set (by simp only [Ex.Fits]; omega)).of_eq (by simp [Ex.eval]) (by simp [Ex.size])
  obtain ⟨s', g', ⟨j, hj, hk, hdn', hl', hn', hA', hs, hf⟩, hend⟩ := hloop (st.set k 0)
    ⟨0, Nat.zero_le _, by simp, by simp [Function.update_of_ne hkd.symm, hd],
      by simp [Function.update_of_ne hkl.symm, hl], by simp [Function.update_of_ne hkn.symm, hn],
      by simp [Function.update_of_ne hkA.symm, ha],
      by
        funext q; unfold recsStk
        by_cases hqd : q = dst
        · subst hqd; simp
        · by_cases hqs : q = src
          · subst hqs; simp [Function.update_of_ne hqd, hS]
          · simp [Function.update_of_ne hqd, Function.update_of_ne hqs],
      ⟨rfl, rfl, fun r hr => by
        simp only [List.mem_cons, not_or] at hr; simp [Function.update_of_ne hr.1]⟩⟩
  have hjm : j = m := by
    have := (hev s' ⟨j, hj, hk, hdn', hl', hn', hA', hs, hf⟩)
    by_contra hne
    exact (this.mpr (by omega)) hend
  subst hjm
  refine ⟨s', (g0.seq g').mono ?_, hs, hdn', hf⟩
  simp only [condCost, e, rv, Ex.size, NSt.set_env, Function.update_self, Nat.sub_zero,
    mul_zero, zero_add]
  have hP : Ex.nodeCost w ≤ (a + 1) * Ex.nodeCost w := Nat.le_mul_of_pos_left _ (by omega)
  have h1 : m * Ex.nodeCost w ≤ m * ((a + 1) * Ex.nodeCost w) := Nat.mul_le_mul_left _ hP
  have h2 : m ≤ m * Ex.nodeCost w := Nat.le_mul_of_pos_right _ (by omega)
  nlinarith

/-! ## Comparing the top records of two stacks -/

lemma NSt.set_self' (s : NSt R Q) (r : Fin R) : s.set r (s.env r) = s := by
  cases s; simp [NSt.set]

/-- One step of the word-by-word comparison: `d := cmpStep d t1 t2`. -/
def cmpIte (d t1 t2 : Fin R) : CStm R Q :=
  .ite (rv d) .skip (.ite (.lt (rv t1) (rv t2)) (.set d (.const 1))
    (.ite (.lt (rv t2) (rv t1)) (.set d (.const 2)) .skip))

lemma cmpIte_good (hw2 : 2 ≤ w) {d t1 t2 : Fin R} (s : NSt R Q) (hd : s.env d < 2 ^ w)
    (h1 : s.env t1 < 2 ^ w) (h2 : s.env t2 < 2 ^ w) :
    Good x w (cmpIte d t1 t2 : CStm R Q) s
      (s.set d (CSort.cmpStep (s.env d) (s.env t1) (s.env t2))) (20 * Ex.nodeCost w) := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h4 := two_le_pow hw2
  by_cases hd0 : s.env d = 0
  · have hfd : (rv d : Ex R).Fits w s.env := hd
    by_cases hab : s.env t1 < s.env t2
    · refine (Good.iteF hfd (by simp [rv, Ex.eval, hd0]) (Good.iteT (e := .lt (rv t1) (rv t2)) (show (Ex.lt (rv t1) (rv t2) : Ex R).Fits w s.env from ⟨h1, h2⟩)
        (by simp [rv, Ex.eval, hab]) (Good.set (r := d) (e := .const 1)
          (by simp only [Ex.Fits]; omega)))).of_eq (by simp [CSort.cmpStep, hd0, hab, Ex.eval])
        (by simp only [condCost, rv, Ex.size]; omega)
    · by_cases hba : s.env t2 < s.env t1
      · refine (Good.iteF hfd (by simp [rv, Ex.eval, hd0]) (Good.iteF (e := .lt (rv t1) (rv t2)) (show (Ex.lt (rv t1) (rv t2) : Ex R).Fits w s.env from ⟨h1, h2⟩)
          (by simp [rv, Ex.eval, hab]) (Good.iteT (e := .lt (rv t2) (rv t1)) (show (Ex.lt (rv t2) (rv t1) : Ex R).Fits w s.env from ⟨h2, h1⟩) (by simp [rv, Ex.eval, hba])
            (Good.set (r := d) (e := .const 2) (by simp only [Ex.Fits]; omega))))).of_eq
          (by simp [CSort.cmpStep, hd0, hab, hba, Ex.eval])
          (by simp only [condCost, rv, Ex.size]; omega)
      · refine (Good.iteF hfd (by simp [rv, Ex.eval, hd0]) (Good.iteF (e := .lt (rv t1) (rv t2)) (show (Ex.lt (rv t1) (rv t2) : Ex R).Fits w s.env from ⟨h1, h2⟩)
          (by simp [rv, Ex.eval, hab]) (Good.iteF (e := .lt (rv t2) (rv t1)) (show (Ex.lt (rv t2) (rv t1) : Ex R).Fits w s.env from ⟨h2, h1⟩) (by simp [rv, Ex.eval, hba])
            Good.skip))).of_eq
          (by
            have : CSort.cmpStep (s.env d) (s.env t1) (s.env t2) = s.env d := by
              simp [CSort.cmpStep, hd0, hab, hba]
            rw [this, NSt.set_self'])
          (by simp only [condCost, rv, Ex.size]; omega)
  · refine (Good.iteT (e := rv d) hd (by simpa [rv, Ex.eval] using hd0) Good.skip).of_eq ?_
      (by simp only [condCost, rv, Ex.size]; omega)
    have : CSort.cmpStep (s.env d) (s.env t1) (s.env t2) = s.env d := by
      simp [CSort.cmpStep, hd0]
    rw [this, NSt.set_self']

lemma cmpW_le : ∀ (d : ℕ) (as bs : List ℕ), d ≤ 2 → CSort.cmpW d as bs ≤ 2
  | d, a :: as, b :: bs, h => by
    simp only [CSort.cmpW]
    exact cmpW_le _ as bs (by unfold CSort.cmpStep; split_ifs <;> omega)
  | _, [], _, h => h
  | _, _ :: _, [], h => h

/-- The body of the comparison loop. -/
def cmpBody (s1 s2 c1 c2 : Fin Q) (d kc t1 t2 : Fin R) : CStm R Q :=
  .seq (.pop s1 t1) (.seq (.pop s2 t2) (.seq (.push c1 (rv t1)) (.seq (.push c2 (rv t2))
    (.seq (cmpIte d t1 t2) (.set kc (.add (rv kc) (.const 1)))))))

/-- Compare the top records (of `A` words) of `s1` and `s2`: `d := cmpW 0 a₁ a₂`; both stacks
are restored (via `c1`, `c2`). -/
def cmpS (s1 s2 c1 c2 : Fin Q) (A d kc t1 t2 i t : Fin R) : CStm R Q :=
  .seq (.set d (.const 0)) (.seq (.set kc (.const 0))
    (.seq (.loop (.lt (rv kc) (rv A)) (cmpBody s1 s2 c1 c2 d kc t1 t2))
      (.seq (moveN c1 s1 A i t) (moveN c2 s2 A i t))))

/-- The stacks of the comparison after `j` words. -/
def cmpStk (S : Fin Q → List ℕ) (s1 s2 c1 c2 : Fin Q) (a1 a2 L1 L2 : List ℕ) (j : ℕ) :
    Fin Q → List ℕ :=
  Function.update (Function.update (Function.update (Function.update S s1 (a1.drop j ++ L1))
    s2 (a2.drop j ++ L2)) c1 ((a1.take j).reverse ++ S c1)) c2 ((a2.take j).reverse ++ S c2)

lemma take_succ_rev {l : List ℕ} {j : ℕ} (hj : j < l.length) :
    (l.take (j + 1)).reverse = l[j] :: (l.take j).reverse := by
  have ht : l.take (j + 1) = l.take j ++ [l[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
  rw [ht, List.reverse_append, List.reverse_singleton, List.singleton_append]

section CmpStk

variable {S : Fin Q → List ℕ} {s1 s2 c1 c2 : Fin Q} {a1 a2 L1 L2 : List ℕ} {j : ℕ}

lemma cmpStk_c2 : cmpStk S s1 s2 c1 c2 a1 a2 L1 L2 j c2 = (a2.take j).reverse ++ S c2 := by
  simp [cmpStk]

lemma cmpStk_c1 (h : c1 ≠ c2) :
    cmpStk S s1 s2 c1 c2 a1 a2 L1 L2 j c1 = (a1.take j).reverse ++ S c1 := by
  simp [cmpStk, Function.update_of_ne h]

lemma cmpStk_s2 (h1 : s2 ≠ c1) (h2 : s2 ≠ c2) :
    cmpStk S s1 s2 c1 c2 a1 a2 L1 L2 j s2 = a2.drop j ++ L2 := by
  simp [cmpStk, Function.update_of_ne h1, Function.update_of_ne h2]

lemma cmpStk_s1 (h0 : s1 ≠ s2) (h1 : s1 ≠ c1) (h2 : s1 ≠ c2) :
    cmpStk S s1 s2 c1 c2 a1 a2 L1 L2 j s1 = a1.drop j ++ L1 := by
  simp [cmpStk, Function.update_of_ne h0, Function.update_of_ne h1, Function.update_of_ne h2]

lemma cmpStk_other {q : Fin Q} (h0 : q ≠ s1) (h1 : q ≠ s2) (h2 : q ≠ c1) (h3 : q ≠ c2) :
    cmpStk S s1 s2 c1 c2 a1 a2 L1 L2 j q = S q := by
  simp [cmpStk, Function.update_of_ne h0, Function.update_of_ne h1, Function.update_of_ne h2,
    Function.update_of_ne h3]

end CmpStk

lemma cmpS_good (hw2 : 2 ≤ w) {s1 s2 c1 c2 : Fin Q} {A d kc t1 t2 i t : Fin R}
    (hstk : [s1, s2, c1, c2].Nodup) (hreg : [A, d, kc, t1, t2, i, t].Nodup)
    (st : NSt R Q) {a : ℕ} (a1 a2 L1 L2 : List ℕ) (ha : st.env A = a)
    (h1 : st.stk s1 = a1 ++ L1) (h2 : st.stk s2 = a2 ++ L2) (hl1 : a1.length = a)
    (hl2 : a2.length = a) (hb1 : ∀ v ∈ a1, v < 2 ^ w) (hb2 : ∀ v ∈ a2, v < 2 ^ w)
    (hw : a + 1 < 2 ^ w) :
    ∃ st', Good x w (cmpS s1 s2 c1 c2 A d kc t1 t2 i t) st st'
        ((a + 1) * (80 * Ex.nodeCost w)) ∧
      st'.stk = st.stk ∧ st'.env d = CSort.cmpW 0 a1 a2 ∧ Frame st st' [d, kc, t1, t2, i, t] := by
  have hs12 : s1 ≠ s2 := by ndup hstk
  have hs1c1 : s1 ≠ c1 := by ndup hstk
  have hs1c2 : s1 ≠ c2 := by ndup hstk
  have hs2c1 : s2 ≠ c1 := by ndup hstk
  have hs2c2 : s2 ≠ c2 := by ndup hstk
  have hc12 : c1 ≠ c2 := by ndup hstk
  have hAd : A ≠ d := by ndup hreg
  have hAk : A ≠ kc := by ndup hreg
  have hAi : A ≠ i := by ndup hreg
  have hAt : A ≠ t := by ndup hreg
  have hit : i ≠ t := by ndup hreg
  have hdk : d ≠ kc := by ndup hreg
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h4 := two_le_pow hw2
  set Inv : NSt R Q → Prop := fun s => ∃ j ≤ a, s.env kc = j ∧ s.env A = a ∧
    s.env d = CSort.cmpW 0 (a1.take j) (a2.take j) ∧ s.stk = cmpStk st.stk s1 s2 c1 c2 a1 a2 L1 L2 j ∧
    Frame st s [d, kc, t1, t2, i, t]
  have hloop := Good.loop_var (x := x) (w := w) (e := .lt (rv kc) (rv A))
    (body := cmpBody s1 s2 c1 c2 d kc t1 t2)
    Inv (fun s => a - s.env kc) (fun _ => 0) 0 (40 * Ex.nodeCost w) (by
      intro s hI
      obtain ⟨j, hj, hk, hA', hd', hs, hf⟩ := hI
      refine ⟨⟨by simp only [rv, Ex.Fits, hk]; omega, by simp only [rv, Ex.Fits, hA']; omega⟩, ?_⟩
      intro hc
      have hja : j < a := by
        simp only [rv, Ex.eval, hk, hA'] at hc; split_ifs at hc with h <;> omega
      have hj1 : j < a1.length := by omega
      have hj2 : j < a2.length := by omega
      have hs1 : s.stk s1 = a1[j] :: (a1.drop (j + 1) ++ L1) := by
        rw [hs, cmpStk_s1 hs12 hs1c1 hs1c2, List.drop_eq_getElem_cons hj1, List.cons_append]
      have hs2 : s.stk s2 = a2[j] :: (a2.drop (j + 1) ++ L2) := by
        rw [hs, cmpStk_s2 hs2c1 hs2c2, List.drop_eq_getElem_cons hj2, List.cons_append]
      have hv1 : a1[j] < 2 ^ w := hb1 _ (List.getElem_mem _)
      have hv2 : a2[j] < 2 ^ w := hb2 _ (List.getElem_mem _)
      have hdle : s.env d ≤ 2 := by rw [hd']; exact cmpW_le 0 _ _ (by omega)
      -- the states of the body
      set u1 := (s.setS s1 (a1.drop (j + 1) ++ L1)).set t1 a1[j]
      set u2 := (u1.setS s2 (a2.drop (j + 1) ++ L2)).set t2 a2[j]
      set u3 := u2.setS c1 (a1[j] :: u2.stk c1)
      set u4 := u3.setS c2 (a2[j] :: u3.stk c2)
      have ht1 : u4.env t1 = a1[j] := by
        simp [u4, u3, u2, u1, Function.update_of_ne (show t1 ≠ t2 by ndup hreg)]
      have ht2 : u4.env t2 = a2[j] := by simp [u4, u3, u2]
      have hd4 : u4.env d = s.env d := by
        simp [u4, u3, u2, u1, Function.update_of_ne (show d ≠ t2 by ndup hreg),
          Function.update_of_ne (show d ≠ t1 by ndup hreg)]
      have hk4 : u4.env kc = j := by
        simp [u4, u3, u2, u1, Function.update_of_ne (show kc ≠ t2 by ndup hreg),
          Function.update_of_ne (show kc ≠ t1 by ndup hreg), hk]
      set u5 := u4.set d (CSort.cmpStep (u4.env d) (u4.env t1) (u4.env t2))
      have gp1 : Good x w (.pop s1 t1 : CStm R Q) s u1 (unitCost w + 1) :=
        (Good.pop s1 t1).of_eq (by simp [u1, hs1]) le_rfl
      have gp2 : Good x w (.pop s2 t2 : CStm R Q) u1 u2 (unitCost w + 1) :=
        (Good.pop s2 t2).of_eq (by simp [u2, u1, Function.update_of_ne hs12.symm, hs2]) le_rfl
      have gq1 : Good x w (.push c1 (rv t1) : CStm R Q) u2 u3 (Ex.nodeCost w + unitCost w) :=
        (Good.push (by
          simp only [rv, Ex.Fits, u2, u1, NSt.set_env, NSt.setS_env,
            Function.update_of_ne (show t1 ≠ t2 by ndup hreg), Function.update_self]
          exact hv1)).of_eq
          (by simp [u3, u2, u1, rv, Ex.eval, Function.update_of_ne (show t1 ≠ t2 by ndup hreg)])
          (by simp [rv, Ex.size])
      have gq2 : Good x w (.push c2 (rv t2) : CStm R Q) u3 u4 (Ex.nodeCost w + unitCost w) :=
        (Good.push (by simp only [rv, Ex.Fits, u3, u2, NSt.set_env, NSt.setS_env,
          Function.update_self]; exact hv2)).of_eq
          (by simp [u4, u3, u2, rv, Ex.eval]) (by simp [rv, Ex.size])
      have gi : Good x w (cmpIte d t1 t2 : CStm R Q) u4 u5 (20 * Ex.nodeCost w) :=
        cmpIte_good hw2 u4 (by rw [hd4]; omega) (by rw [ht1]; exact hv1) (by rw [ht2]; exact hv2)
      have hk5 : u5.env kc = j := by
        simp only [u5, NSt.set_env, Function.update_of_ne hdk.symm]; exact hk4
      have gk : Good x w (.set kc (.add (rv kc) (.const 1)) : CStm R Q) u5 (u5.set kc (j + 1))
          (3 * Ex.nodeCost w + unitCost w) :=
        (Good.set (by simp only [rv, Ex.Fits, Ex.eval, hk5]; omega)).of_eq
          (by simp [rv, Ex.eval, hk5]) (by simp [Ex.size])
      refine ⟨_, (gp1.seq (gp2.seq (gq1.seq (gq2.seq (gi.seq gk))))).mono (by omega),
        ⟨j + 1, by omega, by simp, ?_, ?_, ?_, ?_⟩, ?_, le_rfl⟩
      · simp only [NSt.set_env, Function.update_of_ne hAk, u5, Function.update_of_ne hAd, u4,
          u3, u2, u1, NSt.setS_env, Function.update_of_ne (show A ≠ t2 by ndup hreg),
          Function.update_of_ne (show A ≠ t1 by ndup hreg)]
        exact hA'
      · simp only [NSt.set_env, Function.update_of_ne hdk, u5, Function.update_self]
        rw [hd4, ht1, ht2, hd', CSort.cmpW_take_succ 0 a1 a2 j hj1 hj2]
      · simp only [u5, u4, u3, u2, u1, NSt.set_stk, NSt.setS_stk]
        funext q
        by_cases hq2 : q = c2
        · subst hq2
          simp [Function.update_of_ne hs1c2.symm, Function.update_of_ne hs2c2.symm,
            Function.update_of_ne hc12.symm, hs, cmpStk_c2, take_succ_rev hj2]
        · by_cases hq1 : q = c1
          · subst hq1
            simp [Function.update_of_ne hs1c1.symm, Function.update_of_ne hs2c1.symm,
              Function.update_of_ne hc12, hs, cmpStk_c1 hc12, take_succ_rev hj1]
          · by_cases hqs2 : q = s2
            · subst hqs2
              simp [Function.update_of_ne hs2c1, Function.update_of_ne hs2c2,
                cmpStk_s2 hs2c1 hs2c2]
            · by_cases hqs1 : q = s1
              · subst hqs1
                simp [Function.update_of_ne hs1c1, Function.update_of_ne hs1c2,
                  Function.update_of_ne hs12, cmpStk_s1 hs12 hs1c1 hs1c2]
              · simp [Function.update_of_ne hq1, Function.update_of_ne hq2,
                  Function.update_of_ne hqs1, Function.update_of_ne hqs2, hs,
                  cmpStk_other hqs1 hqs2 hq1 hq2]
      · refine ⟨by simp [u5, u4, u3, u2, u1, hf.1], by simp [u5, u4, u3, u2, u1, hf.2.1],
          fun r hr => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [u5, u4, u3, u2, u1, NSt.set_env, NSt.setS_env, Function.update_of_ne hr.1,
          Function.update_of_ne hr.2.1, Function.update_of_ne hr.2.2.1,
          Function.update_of_ne hr.2.2.2.1]
        exact hf.2.2 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
          hr.2.2.2.2.2])
      · simp; omega)
  -- the initialization
  have g0 : Good x w (.set d (.const 0) : CStm R Q) st (st.set d 0)
      (Ex.nodeCost w + unitCost w) :=
    (Good.set (by simp only [Ex.Fits]; omega)).of_eq (by simp [Ex.eval]) (by simp [Ex.size])
  have g1 : Good x w (.set kc (.const 0) : CStm R Q) (st.set d 0) ((st.set d 0).set kc 0)
      (Ex.nodeCost w + unitCost w) :=
    (Good.set (by simp only [Ex.Fits]; omega)).of_eq (by simp [Ex.eval]) (by simp [Ex.size])
  have hC0 : cmpStk st.stk s1 s2 c1 c2 a1 a2 L1 L2 0 = st.stk := by
    funext q
    by_cases hq2 : q = c2
    · subst hq2; simp [cmpStk_c2]
    · by_cases hq1 : q = c1
      · subst hq1; simp [cmpStk_c1 hc12]
      · by_cases hqs2 : q = s2
        · subst hqs2; simp [cmpStk_s2 hs2c1 hs2c2, h2]
        · by_cases hqs1 : q = s1
          · subst hqs1; simp [cmpStk_s1 hs12 hs1c1 hs1c2, h1]
          · simp [cmpStk_other hqs1 hqs2 hq1 hq2]
  obtain ⟨s', g', ⟨j, hj, hk, hA', hd', hs, hf⟩, hend⟩ := hloop ((st.set d 0).set kc 0)
    ⟨0, Nat.zero_le _, by simp, by simp [Function.update_of_ne hAk, Function.update_of_ne hAd, ha],
      by simp [Function.update_of_ne hdk, CSort.cmpW], by simp [hC0],
      ⟨rfl, rfl, fun r hr => by
        simp only [List.mem_cons, not_or] at hr
        simp [Function.update_of_ne hr.1, Function.update_of_ne hr.2.1]⟩⟩
  have hja : j = a := by
    simp only [rv, Ex.eval, hk, hA'] at hend; split_ifs at hend with h <;> omega
  subst hja
  -- restore the stacks
  have hsc1 : s'.stk c1 = a1.reverse ++ st.stk c1 := by
    rw [hs, cmpStk_c1 hc12, List.take_of_length_le (by omega)]
  obtain ⟨m1, gm1, km1, fm1⟩ := moveN_good (x := x) hs1c1.symm hAi hAt hit s' hA'
    (by rw [hsc1]; simp; omega) hw
    (by
      intro v hv
      rw [hsc1, List.take_left' (by simpa using hl1)] at hv
      exact hb1 v (List.mem_reverse.mp hv))
  have hAm : m1.env A = j := (fm1.2.2 A (by simp [hAi, hAt])).trans hA'
  have hsc2 : m1.stk c2 = a2.reverse ++ st.stk c2 := by
    rw [km1, movedStk_other _ hc12.symm hs1c2.symm, hs, cmpStk_c2,
      List.take_of_length_le (by omega)]
  obtain ⟨m2, gm2, km2, fm2⟩ := moveN_good (x := x) hs2c2.symm hAi hAt hit m1 hAm
    (by rw [hsc2]; simp; omega) hw
    (by
      intro v hv
      rw [hsc2, List.take_left' (by simpa using hl2)] at hv
      exact hb2 v (List.mem_reverse.mp hv))
  refine ⟨m2, (g0.seq (g1.seq (g'.seq (gm1.seq gm2)))).mono ?_, ?_, ?_,
    hf.trans ((fm1.trans fm2).mono (by intro r hr; simp at hr ⊢; tauto))⟩
  · simp only [condCost, rv, Ex.size, NSt.set_env, Function.update_self, Nat.sub_zero,
      mul_zero, zero_add]
    have h2 : j ≤ j * Ex.nodeCost w := Nat.le_mul_of_pos_right _ (by omega)
    nlinarith
  · funext q
    rw [km2]
    by_cases hq2 : q = c2
    · subst hq2
      rw [movedStk_src _ hs2c2.symm, hsc2, List.drop_left' (by simpa using hl2)]
    · by_cases hqs2 : q = s2
      · subst hqs2
        rw [movedStk_dst, hsc2, List.take_left' (by simpa using hl2), List.reverse_reverse,
          km1, movedStk_other _ hs2c1 hs12.symm, hs, cmpStk_s2 hs2c1 hs2c2,
          List.drop_of_length_le (by omega), List.nil_append, h2]
      · rw [movedStk_other _ hq2 hqs2, km1]
        by_cases hq1 : q = c1
        · subst hq1
          rw [movedStk_src _ hs1c1.symm, hs, cmpStk_c1 hc12, List.take_of_length_le (by omega),
            List.drop_left' (by simpa using hl1)]
        · by_cases hqs1 : q = s1
          · subst hqs1
            rw [movedStk_dst, hs, cmpStk_c1 hc12, cmpStk_s1 hs12 hs1c1 hs1c2,
              List.take_of_length_le (l := a1) (by omega), List.take_left' (by simpa using hl1),
              List.reverse_reverse, List.drop_of_length_le (l := a1) (by omega), List.nil_append, h1]
          · rw [movedStk_other _ hq1 hqs1, hs, cmpStk_other hqs1 hqs2 hq1 hq2]
  · rw [fm2.2.2 d (by simp [show d ≠ i by ndup hreg, show d ≠ t by ndup hreg]),
      fm1.2.2 d (by simp [show d ≠ i by ndup hreg, show d ≠ t by ndup hreg]), hd',
      List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

/-! ## Merging two runs -/

/-- The stacks during a merge: `u`, `v` on `T1`, `T2`, the merged records `acc` on top of
`Y`. -/
def mrgStk (S : Fin Q → List ℕ) (T1 T2 Y : Fin Q) (u v acc : List (List ℕ)) : Fin Q → List ℕ :=
  Function.update (Function.update (Function.update S T1 u.flatten) T2 v.flatten) Y
    (acc.flatten ++ S Y)

section MrgStk

variable {S : Fin Q → List ℕ} {T1 T2 Y : Fin Q} {u v acc : List (List ℕ)}

lemma mrgStk_Y : mrgStk S T1 T2 Y u v acc Y = acc.flatten ++ S Y := by simp [mrgStk]

lemma mrgStk_T2 (h : T2 ≠ Y) : mrgStk S T1 T2 Y u v acc T2 = v.flatten := by
  simp [mrgStk, Function.update_of_ne h]

lemma mrgStk_T1 (h0 : T1 ≠ T2) (h1 : T1 ≠ Y) : mrgStk S T1 T2 Y u v acc T1 = u.flatten := by
  simp [mrgStk, Function.update_of_ne h0, Function.update_of_ne h1]

lemma mrgStk_other {q : Fin Q} (h0 : q ≠ T1) (h1 : q ≠ T2) (h2 : q ≠ Y) :
    mrgStk S T1 T2 Y u v acc q = S q := by
  simp [mrgStk, Function.update_of_ne h0, Function.update_of_ne h1, Function.update_of_ne h2]

lemma mrgStk_mv1 (h0 : T1 ≠ T2) (h1 : T1 ≠ Y) (h2 : T2 ≠ Y) {a0 : List ℕ}
    {u' : List (List ℕ)} :
    Function.update (Function.update (mrgStk S T1 T2 Y (a0 :: u') v acc) T1 u'.flatten) Y
      (a0 ++ mrgStk S T1 T2 Y (a0 :: u') v acc Y) = mrgStk S T1 T2 Y u' v (a0 :: acc) := by
  funext q
  by_cases hY : q = Y
  · subst hY; simp [mrgStk_Y]
  · by_cases hq1 : q = T1
    · subst hq1; simp [Function.update_of_ne hY, mrgStk_T1 h0 h1]
    · by_cases hq2 : q = T2
      · subst hq2; simp [Function.update_of_ne hY, Function.update_of_ne hq1, mrgStk_T2 h2]
      · simp [Function.update_of_ne hY, Function.update_of_ne hq1, mrgStk_other hq1 hq2 hY]

lemma mrgStk_mv2 (h0 : T1 ≠ T2) (h1 : T1 ≠ Y) (h2 : T2 ≠ Y) {b0 : List ℕ}
    {v' : List (List ℕ)} :
    Function.update (Function.update (mrgStk S T1 T2 Y u (b0 :: v') acc) T2 v'.flatten) Y
      (b0 ++ mrgStk S T1 T2 Y u (b0 :: v') acc Y) = mrgStk S T1 T2 Y u v' (b0 :: acc) := by
  funext q
  by_cases hY : q = Y
  · subst hY; simp [mrgStk_Y]
  · by_cases hq2 : q = T2
    · subst hq2; simp [Function.update_of_ne hY, mrgStk_T2 h2]
    · by_cases hq1 : q = T1
      · subst hq1; simp [Function.update_of_ne hY, Function.update_of_ne hq2, mrgStk_T1 h0 h1]
      · simp [Function.update_of_ne hY, Function.update_of_ne hq2, mrgStk_other hq1 hq2 hY]

end MrgStk

/-- Flags: `1` for a nonempty list. -/
def nef {α : Type} (l : List α) : ℕ := if l = [] then 0 else 1

lemma flatten_eq_nil_iff {l : List (List ℕ)} {a : ℕ} (ha : 1 ≤ a)
    (h : ∀ y ∈ l, y.length = a) : l.flatten = [] ↔ l = [] := by
  constructor
  · intro hl
    rcases l with _ | ⟨y, l⟩
    · rfl
    · have := h y (by simp)
      simp only [List.flatten_cons, List.append_eq_nil_iff] at hl
      rw [hl.1] at this; simp at this; omega
  · rintro rfl; rfl

section Merge

variable {T1 T2 Y tmp C1 C2 : Fin Q} {A dir c f1 f2 kc t1 t2 i t : Fin R}

lemma mrg_mv1 (hstk : [T1, T2, Y, tmp, C1, C2].Nodup) (hAi : A ≠ i) (hAt : A ≠ t) (hit : i ≠ t)
    (S : Fin Q → List ℕ) (s : NSt R Q) {a : ℕ} {a0 : List ℕ} {u v acc : List (List ℕ)}
    (hs : s.stk = mrgStk S T1 T2 Y (a0 :: u) v acc) (ha : s.env A = a) (hl : a0.length = a)
    (hb : ∀ z ∈ a0, z < 2 ^ w) (hw : a + 1 < 2 ^ w) :
    ∃ s', Good x w (mvRec T1 Y tmp A i t) s s' (2 * ((a + 1) * (12 * Ex.nodeCost w))) ∧
      s'.stk = mrgStk S T1 T2 Y u v (a0 :: acc) ∧ Frame s s' [i, t] := by
  have h0 : T1 ≠ T2 := by ndup hstk
  have h1 : T1 ≠ Y := by ndup hstk
  have h2 : T2 ≠ Y := by ndup hstk
  have hT : s.stk T1 = a0 ++ u.flatten := by rw [hs, mrgStk_T1 h0 h1, List.flatten_cons]
  obtain ⟨s', g, k, f⟩ := mvRec_good (x := x) (dst := Y) (tmp := tmp) (by ndup hstk)
    (by ndup hstk) h1 hAi hAt hit s ha (by rw [hT]; simp; omega) hw
    (by rw [hT, List.take_left' hl]; exact hb)
  refine ⟨s', g, ?_, f⟩
  rw [k, hT, List.drop_left' hl, List.take_left' hl, hs]
  exact mrgStk_mv1 h0 h1 h2

lemma mrg_mv2 (hstk : [T1, T2, Y, tmp, C1, C2].Nodup) (hAi : A ≠ i) (hAt : A ≠ t) (hit : i ≠ t)
    (S : Fin Q → List ℕ) (s : NSt R Q) {a : ℕ} {b0 : List ℕ} {u v acc : List (List ℕ)}
    (hs : s.stk = mrgStk S T1 T2 Y u (b0 :: v) acc) (ha : s.env A = a) (hl : b0.length = a)
    (hb : ∀ z ∈ b0, z < 2 ^ w) (hw : a + 1 < 2 ^ w) :
    ∃ s', Good x w (mvRec T2 Y tmp A i t) s s' (2 * ((a + 1) * (12 * Ex.nodeCost w))) ∧
      s'.stk = mrgStk S T1 T2 Y u v (b0 :: acc) ∧ Frame s s' [i, t] := by
  have h0 : T1 ≠ T2 := by ndup hstk
  have h1 : T1 ≠ Y := by ndup hstk
  have h2 : T2 ≠ Y := by ndup hstk
  have hT : s.stk T2 = b0 ++ v.flatten := by rw [hs, mrgStk_T2 h2, List.flatten_cons]
  obtain ⟨s', g, k, f⟩ := mvRec_good (x := x) (dst := Y) (tmp := tmp) (by ndup hstk)
    (by ndup hstk) h2 hAi hAt hit s ha (by rw [hT]; simp; omega) hw
    (by rw [hT, List.take_left' hl]; exact hb)
  refine ⟨s', g, ?_, f⟩
  rw [k, hT, List.drop_left' hl, List.take_left' hl, hs]
  exact mrgStk_mv2 h0 h1 h2

/-- The branching part of the merge body. -/
def mrgIteInner (T1 T2 Y tmp C1 C2 : Fin Q) (A dir c f1 f2 kc t1 t2 i t : Fin R) : CStm R Q :=
  .ite (rv f2)
    (.seq (.ite (rv dir) (cmpS T1 T2 C1 C2 A c kc t1 t2 i t) (cmpS T2 T1 C1 C2 A c kc t1 t2 i t))
      (.ite (.lt (rv c) (.const 2)) (mvRec T1 Y tmp A i t) (mvRec T2 Y tmp A i t)))
    (mvRec T1 Y tmp A i t)

/-- The branching part of the merge body. -/
def mrgIte (T1 T2 Y tmp C1 C2 : Fin Q) (A dir c f1 f2 kc t1 t2 i t : Fin R) : CStm R Q :=
  .ite (rv f1) (mrgIteInner T1 T2 Y tmp C1 C2 A dir c f1 f2 kc t1 t2 i t) (mvRec T2 Y tmp A i t)

lemma mrgIte_good (hw2 : 2 ≤ w) (hstk : [T1, T2, Y, tmp, C1, C2].Nodup)
    (hreg : [A, dir, c, f1, f2, kc, t1, t2, i, t].Nodup)
    (S : Fin Q → List ℕ) (d : Bool) (s : NSt R Q) {a : ℕ} (u v acc : List (List ℕ))
    (ha : s.env A = a) (hdir : s.env dir = if d then 1 else 0)
    (hs : s.stk = mrgStk S T1 T2 Y u v acc) (hf1 : s.env f1 = nef u) (hf2 : s.env f2 = nef v)
    (hrec : ∀ y ∈ u ++ v, y.length = a ∧ ∀ z ∈ y, z < 2 ^ w) (hw : a + 1 < 2 ^ w)
    (huv : u ≠ [] ∨ v ≠ []) :
    ∃ s', Good x w (mrgIte T1 T2 Y tmp C1 C2 A dir c f1 f2 kc t1 t2 i t) s s'
        (104 * Ex.nodeCost w * a + 120 * Ex.nodeCost w) ∧
      s'.stk = mrgStk S T1 T2 Y (CSort.mrgStep d (u, v, acc)).1 (CSort.mrgStep d (u, v, acc)).2.1
        (CSort.mrgStep d (u, v, acc)).2.2 ∧
      Frame s s' [c, kc, t1, t2, i, t] := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h4 := two_le_pow hw2
  have hAi : A ≠ i := by ndup hreg
  have hAt : A ≠ t := by ndup hreg
  have hit : i ≠ t := by ndup hreg
  have hsub : ∀ {r : List (Fin R)}, r ⊆ [c, kc, t1, t2, i, t] → ∀ {s₁ s₂ : NSt R Q},
      Frame s₁ s₂ r → Frame s₁ s₂ [c, kc, t1, t2, i, t] := fun h _ _ f => f.mono h
  have hf1v : (rv f1 : Ex R).Fits w s.env := by
    show s.env f1 < 2 ^ w; rw [hf1]; unfold nef; split_ifs <;> omega
  have hf2v : (rv f2 : Ex R).Fits w s.env := by
    show s.env f2 < 2 ^ w; rw [hf2]; unfold nef; split_ifs <;> omega
  rcases u with _ | ⟨a0, u⟩ <;> rcases v with _ | ⟨b0, v⟩
  · simp at huv
  · -- only `T2` is nonempty
    have hb := hrec b0 (by simp)
    obtain ⟨s', g, k, f⟩ := mrg_mv2 (x := x) hstk hAi hAt hit S s hs ha hb.1 hb.2 hw
    refine ⟨s', (Good.iteF hf1v (by simp [rv, Ex.eval, hf1, nef]) g).mono ?_, by simpa [CSort.mrgStep] using k,
      hsub (by intro r hr; simp at hr ⊢; tauto) f⟩
    simp only [condCost, rv, Ex.size]; nlinarith
  · -- only `T1` is nonempty
    have hb := hrec a0 (by simp)
    obtain ⟨s', g, k, f⟩ := mrg_mv1 (x := x) hstk hAi hAt hit S s hs ha hb.1 hb.2 hw
    refine ⟨s', (Good.iteT hf1v (by simp [rv, Ex.eval, hf1, nef])
      (Good.iteF hf2v (by simp [rv, Ex.eval, hf2, nef]) g)).mono ?_,
      by simpa [CSort.mrgStep] using k, hsub (by intro r hr; simp at hr ⊢; tauto) f⟩
    simp only [condCost, rv, Ex.size]; nlinarith
  · -- both nonempty: compare
    have ha0 := hrec a0 (by simp)
    have hb0 := hrec b0 (by simp)
    have hT1 : s.stk T1 = a0 ++ u.flatten := by
      rw [hs, mrgStk_T1 (by ndup hstk) (by ndup hstk), List.flatten_cons]
    have hT2 : s.stk T2 = b0 ++ v.flatten := by
      rw [hs, mrgStk_T2 (by ndup hstk), List.flatten_cons]
    have hcreg : [A, c, kc, t1, t2, i, t].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true] at hreg ⊢
      tauto
    -- the comparison
    obtain ⟨sc, gc, kc', ec, hc2le, fc⟩ : ∃ sc, Good x w (.ite (rv dir) (cmpS T1 T2 C1 C2 A c kc t1 t2 i t)
          (cmpS T2 T1 C1 C2 A c kc t1 t2 i t)) s sc (Ex.nodeCost w + 1 + (a + 1) * (80 * Ex.nodeCost w)) ∧
        sc.stk = s.stk ∧ (CSort.ordD d b0 a0 = true ↔ sc.env c < 2) ∧ sc.env c ≤ 2 ∧
        Frame s sc [c, kc, t1, t2, i, t] := by
      have hdv : (rv dir : Ex R).Fits w s.env := by
        show s.env dir < 2 ^ w; rw [hdir]; split_ifs <;> omega
      cases d
      · obtain ⟨sc, g, k, e, f⟩ := cmpS_good (x := x) hw2 (s1 := T2) (s2 := T1) (c1 := C1)
          (c2 := C2) (by
            have : [T2, T1, C1, C2].Perm [T1, T2, C1, C2] := List.Perm.swap _ _ _
            refine this.nodup_iff.mpr ?_
            have hsl : [T1, T2, C1, C2].Sublist [T1, T2, Y, tmp, C1, C2] := by simp
            exact hsl.nodup hstk) hcreg s b0 a0 v.flatten u.flatten ha hT2 hT1 hb0.1 ha0.1
          hb0.2 ha0.2 hw
        refine ⟨sc, (Good.iteF hdv (by simp [rv, Ex.eval, hdir]) g).mono (by
          simp only [condCost, rv, Ex.size]; omega), k, ?_, by rw [e]; exact cmpW_le 0 _ _ (by omega), f⟩
        rw [e, CSort.ordD, if_neg (by simp), CSort.rle_iff_cmpW b0 a0 (by rw [ha0.1, hb0.1])]
        have := cmpW_le 0 b0 a0 (by omega)
        omega
      · obtain ⟨sc, g, k, e, f⟩ := cmpS_good (x := x) hw2 (s1 := T1) (s2 := T2) (c1 := C1)
          (c2 := C2) (by
            have hsl : [T1, T2, C1, C2].Sublist [T1, T2, Y, tmp, C1, C2] := by simp
            exact hsl.nodup hstk) hcreg s a0 b0 u.flatten v.flatten ha hT1 hT2 ha0.1 hb0.1
          ha0.2 hb0.2 hw
        refine ⟨sc, (Good.iteT hdv (by simp [rv, Ex.eval, hdir]) g).mono (by
          simp only [condCost, rv, Ex.size]; omega), k, ?_, by rw [e]; exact cmpW_le 0 _ _ (by omega), f⟩
        rw [e, CSort.ordD, if_pos rfl, CSort.rle_iff_cmpW a0 b0 (by rw [ha0.1, hb0.1])]
        have := cmpW_le 0 a0 b0 (by omega)
        omega
    have hsc : sc.stk = mrgStk S T1 T2 Y (a0 :: u) (b0 :: v) acc := kc'.trans hs
    have hAc : sc.env A = a := by
      rw [fc.2.2 A (by simp [hAi, hAt, show A ≠ c by ndup hreg, show A ≠ kc by ndup hreg,
        show A ≠ t1 by ndup hreg, show A ≠ t2 by ndup hreg]), ha]
    have hcf : (Ex.lt (rv c) (.const 2) : Ex R).Fits w sc.env :=
      ⟨show sc.env c < 2 ^ w by omega, show 2 < 2 ^ w by omega⟩
    by_cases hord : CSort.ordD d b0 a0 = true
    · obtain ⟨s', g, k, f⟩ := mrg_mv1 (x := x) hstk hAi hAt hit S sc hsc hAc ha0.1 ha0.2 hw
      refine ⟨s', (Good.iteT hf1v (by simp [rv, Ex.eval, hf1, nef])
        (Good.iteT hf2v (by simp [rv, Ex.eval, hf2, nef])
          (gc.seq (Good.iteT hcf (show (if sc.env c < 2 then 1 else 0) ≠ 0 by rw [if_pos (ec.mp hord)]; decide) g)))).mono ?_, ?_,
        fc.trans (f.mono (regs' := [c, kc, t1, t2, i, t]) (by
          intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
          rcases hr with rfl | rfl <;> simp))⟩
      · simp only [condCost, rv, Ex.size]; ring_nf; omega
      · rw [k]; simp [CSort.mrgStep, hord]
    · have hc2 : ¬ sc.env c < 2 := fun h => hord (ec.mpr h)
      obtain ⟨s', g, k, f⟩ := mrg_mv2 (x := x) hstk hAi hAt hit S sc hsc hAc hb0.1 hb0.2 hw
      have hfr : Frame s s' [c, kc, t1, t2, i, t] :=
        fc.trans (f.mono (regs' := [c, kc, t1, t2, i, t]) (by
          intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
          rcases hr with rfl | rfl <;> simp))
      have hev : Ex.eval sc.env (Ex.lt (rv c) (.const 2)) = 0 := by
        show (if sc.env c < 2 then 1 else 0) = 0
        exact if_neg hc2
      have G := Good.iteT (p := mrgIteInner T1 T2 Y tmp C1 C2 A dir c f1 f2 kc t1 t2 i t)
        (q := mvRec T2 Y tmp A i t) hf1v (by simp [rv, Ex.eval, hf1, nef])
        (Good.iteT (q := mvRec T1 Y tmp A i t) hf2v (by simp [rv, Ex.eval, hf2, nef])
          (gc.seq (Good.iteF (p := mvRec T1 Y tmp A i t) hcf hev g)))
      refine ⟨s', G.mono ?_, ?_, hfr⟩
      · simp only [condCost, rv, Ex.size]; ring_nf; omega
      · rw [k]; simp [CSort.mrgStep, hord]

/-- The body of the merge loop. -/
def mrgBody (T1 T2 Y tmp C1 C2 : Fin Q) (A dir c f1 f2 kc t1 t2 i t : Fin R) : CStm R Q :=
  .seq (mrgIte T1 T2 Y tmp C1 C2 A dir c f1 f2 kc t1 t2 i t) (.seq (.sne f1 T1) (.sne f2 T2))

/-- Merge the runs on `T1` and `T2` onto `Y` (`CSort.mrg`, direction in `dir`). -/
def mrgS (T1 T2 Y tmp C1 C2 : Fin Q) (A dir c f1 f2 kc t1 t2 i t : Fin R) : CStm R Q :=
  .seq (.sne f1 T1) (.seq (.sne f2 T2)
    (.loop (.add (rv f1) (rv f2)) (mrgBody T1 T2 Y tmp C1 C2 A dir c f1 f2 kc t1 t2 i t)))

end Merge

end CStm

end Lax119563Proofs.Compiler

end Compiler_CSort
