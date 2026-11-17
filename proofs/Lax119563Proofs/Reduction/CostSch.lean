import Lax119563Proofs.Reduction.CostCmd
import Lax119563Proofs.Reduction.SchGen

/-!
# Fits and cost of the schema enumerator

**`hasCost_schEnum`**: with linear `HX, RX`, globals `NX, rX, p0X, EcX` in class `P 0 7`
(polylogarithmic), and a body with `HasCost (τs ++ schTys) body e d`, the schema enumerator
has `HasCost τs (schEnum M s b HX RX NX rX p0X EcX body) e (d + 12)` (the command enumerator
around the counting command enumerators of `cmdBody`). `schTys` are the classes of the levels
`b, …, b + 36` of the body (the command levels `cmdTys`, the counts `j, e₀` and the schema
index `P 0 7`, the record `[tern, u, v, en, msk]` with classes `numTys` and the guard
numbers with classes `gdTys`).
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Xp Ty Gn

variable {M : Machine} {s : ℕ}

/-- The classes of the five numbers of a schema. -/
def numTys : List Ty := [P 0 0, P 0 7, P 0 7, P 0 7, .big]

/-- The classes of the guard numbers. -/
def gdTys : List Ty := [P 0 0, P 0 1, P 0 0, P 0 0]

/-- The classes of the levels `b, …, b + 36` of the body of the schema enumerator. -/
def schTys : List Ty := cmdTys ++ [P 0 7, P 0 7] ++ P 0 7 :: (numTys ++ gdTys)

variable {Γ : List Ty}

/-- Typed lists of expressions. -/
abbrev TyBs (Γ : List Ty) (l : List Xp) (ts : List Ty) : Prop :=
  List.Forall₂ (fun a τ => TyB Γ a τ) l ts

lemma hasCost_blkGen {e0 : Xp} {gd : List Xp} {body : Gn} {blk : List (List Xp)} {e d : ℕ}
    (he0 : TyB Γ e0 (P 0 7)) (hgd : TyBs Γ gd gdTys) (hblk : ∀ l ∈ blk, TyBs Γ l numTys)
    (hbody : HasCost (Γ ++ P 0 7 :: (numTys ++ gdTys)) body e d) :
    HasCost Γ (blkGen e0 gd body blk) e d := by
  refine hasCost_seqL fun g hg => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
  have hm : p.1 ∈ blk := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hp)
  have h0 : TyB Γ (add e0 (const p.2)) (P 0 7) :=
    ⟨hasTy_add he0.1 ((hasTy_const _).le ⟨le_rfl, by omega⟩), he0.2, trivial⟩
  have hT : TyL (Γ ++ []) (add e0 (const p.2) :: (p.1 ++ gd)) (P 0 7 :: (numTys ++ gdTys)) :=
    tyL_of_forall₂ (.cons h0 (List.rel_append (hblk _ hm) hgd)) []
  exact hasCost_bindL (by simpa using hT) hbody

lemma gadgetX_ty {X msk A B Z Y : Xp} (hX : TyB Γ X (P 0 7)) (hm : TyB Γ msk .big)
    (hA : TyB Γ A (P 0 7)) (hB : TyB Γ B (P 0 7)) (hZ : TyB Γ Z (P 0 7))
    (hY : TyB Γ Y (P 0 7)) : ∀ l ∈ gadgetX X msk A B Z Y, TyBs Γ l numTys := by
  have c0 : TyB Γ (const 0) (P 0 0) := tyB_const 0
  have c1 : TyB Γ (const 1) (P 0 0) := tyB_const 1
  have cb : TyB Γ (const 0) .big := c0.le (Ty.le_big _)
  simp only [gadgetX, List.mem_cons, List.not_mem_nil, or_false]
  rintro l (rfl | rfl | rfl | rfl)
  · exact .cons c0 (.cons hX (.cons hA (.cons hA (.cons hm .nil))))
  · exact .cons c0 (.cons hX (.cons hB (.cons hB (.cons hm .nil))))
  · exact .cons c1 (.cons hA (.cons hB (.cons hZ (.cons cb .nil))))
  · exact .cons c0 (.cons hZ (.cons hY (.cons hY (.cons cb .nil))))

lemma tyL_zeros : ∀ (k : ℕ) (Γ : List Ty),
    TyL Γ (List.replicate k (const 0)) (List.replicate k (P 0 0))
  | 0, _ => trivial
  | k + 1, Γ => ⟨hasTy_const 0, tyL_zeros k _⟩

lemma tyB_get {τs l : List Ty} {j : ℕ} {τ τ' : Ty} (h : l.getD j (P 0 0) = τ) (hj : j < l.length)
    (hle : Ty.Le τ τ') : TyB (τs ++ l) (var (τs.length + j)) τ' := (tyB_var l h hj).le hle

lemma hasTy_beforeX (b b' : ℕ) : HasTy Γ (beforeX b b') (P 0 0) :=
  hasTy_or (hasTy_lt (hasTy_var _) (hasTy_var _))
    (hasTy_and (hasTy_eq (hasTy_var _) (hasTy_var _)) (hasTy_lt (hasTy_var _) (hasTy_var _)))

lemma hasCost_emitN (n : ℕ) : HasCost Γ (emitN n) 0 0 :=
  hasCost_seqL fun g hg => by
    rw [List.eq_of_mem_replicate hg]; exact hasCost_emit (hasTy_const 0)

lemma len_cmdTys : cmdTys.length = 25 := rfl

theorem hasCost_cmdBody {τs : List Ty} {HX RX NX : Xp} (hH : LinX τs HX) (hR : LinX τs RX)
    (hN : TyB τs NX (P 0 7)) {body : Gn} {e d : ℕ}
    (hbody : HasCost (τs ++ schTys) body e d) :
    HasCost (τs ++ cmdTys) (cmdBody M s τs.length HX RX NX body) e (d + 6) := by
  have hbd : HasCost (τs ++ schTys) body e (d + 6) := hbody.mono le_rfl (by omega)
  -- the first count: `j`
  have G1 : HasCost (τs ++ cmdTys ++ [P 0 0])
      (cmdEnum M s (τs.length + 26) HX RX (when (beforeX τs.length (τs.length + 26))
        (emit (const 0)))) 0 6 :=
    hasCost_cmdEnum (τs := τs ++ cmdTys ++ [P 0 0]) (by simp [len_cmdTys])
      ((hH.weaken cmdTys).weaken [P 0 0]) ((hR.weaken cmdTys).weaken [P 0 0])
      (hasCost_when (hasTy_beforeX _ _) (hasCost_emit (hasTy_const 0)))
  have G2 : HasCost (τs ++ cmdTys ++ [P 0 7] ++ [P 0 0])
      (cmdEnum M s (τs.length + 27) HX RX (when (beforeX τs.length (τs.length + 27))
        (ite (var (τs.length + 27 + 17)) (emitN 9) (emitN 4)))) 0 6 :=
    hasCost_cmdEnum (τs := τs ++ cmdTys ++ [P 0 7] ++ [P 0 0]) (by simp [len_cmdTys])
      (((hH.weaken cmdTys).weaken [P 0 7]).weaken [P 0 0])
      (((hR.weaken cmdTys).weaken [P 0 7]).weaken [P 0 0])
      (hasCost_when (hasTy_beforeX _ _) (hasCost_ite (hasTy_var _) (hasCost_emitN 9)
        (hasCost_emitN 4)))
  -- the blocks
  set Γ := τs ++ (cmdTys ++ [P 0 7, P 0 7]) with hΓ
  have hNw : TyB Γ NX (P 0 7) := hN.weaken _
  have v25 : TyB Γ (var (τs.length + 25)) (P 0 7) := tyB_get rfl (by simp [len_cmdTys]) (Ty.Le.refl _)
  have v26 : TyB Γ (var (τs.length + 26)) (P 0 7) := tyB_get rfl (by simp [len_cmdTys]) (Ty.Le.refl _)
  have v15 : TyB Γ (var (τs.length + 15)) (P 0 7) :=
    tyB_get rfl (by simp [len_cmdTys]) ⟨le_rfl, by omega⟩
  have v19 : TyB Γ (var (τs.length + 19)) (P 0 7) :=
    tyB_get rfl (by simp [len_cmdTys]) ⟨le_rfl, by omega⟩
  have v20 : TyB Γ (var (τs.length + 20)) (P 0 7) :=
    tyB_get rfl (by simp [len_cmdTys]) ⟨le_rfl, by omega⟩
  have v18 : TyB Γ (var (τs.length + 18)) .big := tyB_get rfl (by simp [len_cmdTys]) trivial
  have hslot : ∀ t, TyB Γ (slotX NX τs.length t) (P 0 7) := fun t =>
    ⟨hasTy_add hNw.1 (hasTy_add ((hasTy_const t).le ⟨le_rfl, by omega⟩) (hasTy_mulC v25.1 8)),
      hNw.2, trivial, Xp.bnd_mulC v25.2 8⟩
  have hgd : TyBs Γ (gdX τs.length) gdTys := by
    simp only [gdX, gdTys]
    exact .cons (tyB_get rfl (by simp [len_cmdTys]) (Ty.Le.refl _))
      (.cons (tyB_get rfl (by simp [len_cmdTys]) (Ty.Le.refl _))
      (.cons (tyB_get rfl (by simp [len_cmdTys]) (Ty.Le.refl _))
      (.cons (tyB_get rfl (by simp [len_cmdTys]) (Ty.Le.refl _)) .nil)))
  have hB : HasCost (Γ ++ P 0 7 :: (numTys ++ gdTys)) body e (d + 6) := by
    simpa [hΓ, schTys] using hbd
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
  have G3' : HasCost (τs ++ cmdTys ++ [P 0 7] ++ [P 0 7]) (ite (var (τs.length + 17))
      (blkGen (var (τs.length + 26)) (gdX τs.length) body (forkBlk NX τs.length))
      (blkGen (var (τs.length + 26)) (gdX τs.length) body (assignBlk NX τs.length))) e (d + 6) := by
    rw [List.append_assoc, List.append_assoc]; exact G3
  have C2 := hasCost_count (G2.mono (Nat.zero_le e) (by omega)) G2.len G3'
  exact hasCost_count (G1.mono (Nat.zero_le e) (by omega)) G1.len C2

theorem hasCost_detGen {τs : List Ty} {NX rX p0X EcX : Xp} (hN : TyB τs NX (P 0 7))
    (hr : TyB τs rX (P 0 7)) (hp : TyB τs p0X (P 0 7)) (hE : TyB τs EcX (P 0 7))
    {body : Gn} {e d : ℕ} (hbody : HasCost (τs ++ schTys) body e d) :
    HasCost τs (detGen NX rX p0X EcX body) e d := by
  set Γ := τs ++ List.replicate 27 (P 0 0) with hΓ
  have hdet : ∀ t, TyB Γ (detX NX rX t) (P 0 7) := fun t =>
    ⟨hasTy_add (hasTy_add (hN.weaken _).1 (hasTy_mulC (hr.weaken _).1 8))
      ((hasTy_const t).le ⟨le_rfl, by omega⟩),
      ⟨(hN.weaken _).2, Xp.bnd_mulC (hr.weaken _).2 8⟩, trivial⟩
  have hgd : TyBs Γ [const 3, const 0, const 0, const 0] gdTys :=
    .cons (tyB_const 3) (.cons (linX_const 0) (.cons (tyB_const 0) (.cons (tyB_const 0) .nil)))
  have hle : TysLe (Γ ++ P 0 7 :: (numTys ++ gdTys)) (τs ++ schTys) := by
    rw [hΓ, List.append_assoc]
    refine TysLe.append (TysLe.refl τs) ?_
    simp [TysLe, schTys, cmdTys, digTys, recTys, numTys, gdTys, List.replicate_succ, Ty.Le]
  refine hasCost_bindL (ts := List.replicate 27 (P 0 0)) (by simpa using tyL_zeros 27 τs) ?_
  exact hasCost_blkGen (hE.weaken _) hgd
    (gadgetX_ty (hp.weaken _) ((tyB_const 0).le (Ty.le_big _)) (hdet 0) (hdet 1) (hdet 2) (hdet 3))
    (hbody.ctx hle)

/-- **Fits and cost of the schema enumerator.** -/
theorem hasCost_schEnum {τs : List Ty} {b : ℕ} (hb : τs.length = b) {HX RX NX rX p0X EcX : Xp}
    (hH : LinX τs HX) (hR : LinX τs RX) (hN : TyB τs NX (P 0 7)) (hr : TyB τs rX (P 0 7))
    (hp : TyB τs p0X (P 0 7)) (hE : TyB τs EcX (P 0 7)) {body : Gn} {e d : ℕ}
    (hbody : HasCost (τs ++ schTys) body e d) :
    HasCost τs (schEnum M s b HX RX NX rX p0X EcX body) e (d + 12) := by
  subst hb
  exact hasCost_seq (hasCost_cmdEnum rfl hH hR (hasCost_cmdBody hH hR hN hbody))
    ((hasCost_detGen hN hr hp hE hbody).mono le_rfl (by omega))

end Lax119563Proofs.Reduction
