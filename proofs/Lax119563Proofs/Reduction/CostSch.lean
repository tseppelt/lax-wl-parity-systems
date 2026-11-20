import Lax119563Proofs.Reduction.CostCmd
import Lax119563Proofs.Reduction.SchGen

/-!
# Fits and cost of the schema generators

Classes `numTys` of the record `[tern, u, v, en, msk]` of a schema and `gdTys` of the guard
numbers; the cost of the block generator (`hasCost_blkGen`) and of emitting numbers
(`hasCost_emitN`), and the class of the key comparison `beforeX` (`hasTy_beforeX`).
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Xp Ty Gn

variable {M : Machine} {s : ℕ}

/-- The classes of the five numbers of a schema. -/
def numTys : List Ty := [P 0 0, P 0 7, P 0 7, P 0 7, .big]

/-- The classes of the guard numbers. -/
def gdTys : List Ty := [P 0 0, P 0 1, P 0 0, P 0 0]

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

end Lax119563Proofs.Reduction
