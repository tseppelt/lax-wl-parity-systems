import Lax119563Proofs.Reduction.CostGlob
import Lax119563Proofs.Reduction.PassBase

/-!
# Fits and cost of the system generator: tools

* `Tp Γ e`: `e` has *some* class (enough for emitted numbers and tests); rules `tp_*` and the
  tactic `tp`, which also closes the linear (`P 0 1`) side conditions of shifts and products
  for concrete contexts;
* the leaf tactics `tvb` (a variable read with its class and bound, for concrete contexts).
-/

namespace Lax119563Proofs.Reduction

open Xp Ty Gn

/-- Some class. -/
structure Tp (Γ : List Ty) (e : Xp) : Prop where
  intro ::
  ex : ∃ τ, HasTy Γ e τ

variable {Γ : List Ty}

lemma tp_var (i : ℕ) : Tp Γ (var i) := ⟨⟨_, hasTy_var i⟩⟩
lemma tp_const (c : ℕ) : Tp Γ (const c) := ⟨⟨_, hasTy_const c⟩⟩
lemma tp_add {a b : Xp} (ha : Tp Γ a) (hb : Tp Γ b) : Tp Γ (add a b) :=
  ⟨⟨_, hasTy_addBig ha.ex.choose_spec hb.ex.choose_spec⟩⟩
lemma tp_odd {a : Xp} (ha : Tp Γ a) : Tp Γ (odd a) := ⟨⟨_, hasTy_odd ha.ex.choose_spec⟩⟩
lemma tp_shl {a k : Xp} (ha : Tp Γ a) (hk : HasTy Γ k (P 0 1)) : Tp Γ (shl a k) :=
  ⟨⟨_, hasTy_shl ha.ex.choose_spec hk⟩⟩
lemma tp_shr {a k : Xp} (ha : Tp Γ a) (hk : HasTy Γ k (P 0 1)) : Tp Γ (shr a k) :=
  ⟨⟨_, hasTy_shr ha.ex.choose_spec hk⟩⟩
lemma hasTy_lin_const (c : ℕ) : HasTy Γ (const c) (P 0 1) :=
  (hasTy_const c).le ⟨le_rfl, Nat.zero_le _⟩
lemma tp_eq {a b : Xp} (ha : Tp Γ a) (hb : Tp Γ b) : Tp Γ (Xp.eq a b) :=
  ⟨⟨_, hasTy_eq ha.ex.choose_spec hb.ex.choose_spec⟩⟩
/-- Typing of the tests, numbers and linear side conditions (concrete contexts). -/
macro "tp" : tactic => `(tactic| repeat' (first
  | assumption
  | exact tp_var _
  | exact tp_const _
  | exact hasTy_var' rfl
  | exact hasTy_lin_const _
  | exact hasTy_var_lin rfl
  | apply tp_eq
  | apply tp_and
  | apply tp_or
  | apply tp_not
  | apply tp_mul
  | apply tp_add
  | apply tp_lt
  | apply tp_half
  | apply tp_odd
  | apply tp_shl
  | apply tp_shr
  | apply tp_xorM
  | apply tp_mulB
  | apply hasTy_lin_add
  | apply hasTy_lin_not
  | apply hasTy_lin_lt
  | apply hasTy_lin_mul0
  | apply tp_xfX
  | apply tp_mulC
  | apply hasTy_lin_mulC))

/-- A variable with its class and bound (concrete contexts). -/
macro "tvb" : tactic => `(tactic| exact ⟨hasTy_var _, by show _ < List.length _; decide⟩)

/-! ## Generators from `Tp` -/

lemma hasCost_emit' {a : Xp} (ha : Tp Γ a) : HasCost Γ (emit a) 0 0 :=
  hasCost_emit ha.ex.choose_spec

lemma hasCost_ite' {c : Xp} {g h : Gn} {e d : ℕ} (hc : Tp Γ c) (hg : HasCost Γ g e d)
    (hh : HasCost Γ h e d) : HasCost Γ (ite c g h) e d := hasCost_ite hc.ex.choose_spec hg hh

lemma hasCost_when' {c : Xp} {g : Gn} {e d : ℕ} (hc : Tp Γ c) (hg : HasCost Γ g e d) :
    HasCost Γ (when c g) e d := hasCost_when hc.ex.choose_spec hg

end Lax119563Proofs.Reduction
