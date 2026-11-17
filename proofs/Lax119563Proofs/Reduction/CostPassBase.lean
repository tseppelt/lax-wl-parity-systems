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
lemma tp_lt {a b : Xp} (ha : Tp Γ a) (hb : Tp Γ b) : Tp Γ (Xp.lt a b) :=
  ⟨⟨_, hasTy_lt ha.ex.choose_spec hb.ex.choose_spec⟩⟩
lemma tp_half {a : Xp} (ha : Tp Γ a) : Tp Γ (half a) := ⟨⟨_, hasTy_half ha.ex.choose_spec⟩⟩
lemma tp_odd {a : Xp} (ha : Tp Γ a) : Tp Γ (odd a) := ⟨⟨_, hasTy_odd ha.ex.choose_spec⟩⟩
lemma tp_mulB {a b k : Xp} (ha : Tp Γ a) (hb : Tp Γ b) (hk : HasTy Γ k (P 0 1)) :
    Tp Γ (mulB a b k) := ⟨⟨_, hasTy_mulBBig ha.ex.choose_spec hb.ex.choose_spec hk⟩⟩
lemma tp_mul {a b : Xp} (ha : Tp Γ a) (hk : HasTy Γ b (P 0 1)) : Tp Γ (mul a b) :=
  tp_mulB ha ⟨⟨_, hk⟩⟩ hk
lemma tp_shl {a k : Xp} (ha : Tp Γ a) (hk : HasTy Γ k (P 0 1)) : Tp Γ (shl a k) :=
  ⟨⟨_, hasTy_shl ha.ex.choose_spec hk⟩⟩
lemma tp_shr {a k : Xp} (ha : Tp Γ a) (hk : HasTy Γ k (P 0 1)) : Tp Γ (shr a k) :=
  ⟨⟨_, hasTy_shr ha.ex.choose_spec hk⟩⟩
lemma tp_xorM {a b k : Xp} (ha : Tp Γ a) (hb : Tp Γ b) (hk : HasTy Γ k (P 0 1)) :
    Tp Γ (xorM a b k) := ⟨⟨_, hasTy_xorM ha.ex.choose_spec hb.ex.choose_spec hk⟩⟩
lemma tp_mulC {a : Xp} (ha : Tp Γ a) (c : ℕ) : Tp Γ (mulC c a) :=
  ⟨⟨_, hasTy_mulCBig ha.ex.choose_spec c⟩⟩

lemma hasTy_lin_const (c : ℕ) : HasTy Γ (const c) (P 0 1) :=
  (hasTy_const c).le ⟨le_rfl, Nat.zero_le _⟩
lemma hasTy_lin_add {a b : Xp} (ha : HasTy Γ a (P 0 1)) (hb : HasTy Γ b (P 0 1)) :
    HasTy Γ (add a b) (P 0 1) := hasTy_add ha hb
lemma hasTy_lin_lt {a b : Xp} (ha : Tp Γ a) (hb : Tp Γ b) : HasTy Γ (Xp.lt a b) (P 0 1) :=
  (hasTy_lt ha.ex.choose_spec hb.ex.choose_spec).le ⟨le_rfl, Nat.zero_le _⟩
lemma hasTy_lin_not {a : Xp} (ha : Tp Γ a) : HasTy Γ (Xp.not a) (P 0 1) :=
  hasTy_lin_lt ha (tp_const 1)
lemma hasTy_lin_mul0 {a b : Xp} (ha : HasTy Γ a (P 0 0)) (hb : HasTy Γ b (P 0 1)) :
    HasTy Γ (mul a b) (P 0 1) := by simpa using hasTy_mul ha hb hb
lemma hasTy_lin_mulC {a : Xp} (ha : HasTy Γ a (P 0 1)) (c : ℕ) : HasTy Γ (mulC c a) (P 0 1) :=
  hasTy_mulC ha c

lemma tp_eq {a b : Xp} (ha : Tp Γ a) (hb : Tp Γ b) : Tp Γ (Xp.eq a b) :=
  ⟨⟨_, hasTy_eq ha.ex.choose_spec hb.ex.choose_spec⟩⟩
lemma tp_and {a b : Xp} (ha : Tp Γ a) (hb : Tp Γ b) : Tp Γ (Xp.and a b) :=
  ⟨⟨_, hasTy_and ha.ex.choose_spec hb.ex.choose_spec⟩⟩
lemma tp_or {a b : Xp} (ha : Tp Γ a) (hb : Tp Γ b) : Tp Γ (Xp.or a b) :=
  ⟨⟨_, hasTy_or ha.ex.choose_spec hb.ex.choose_spec⟩⟩
lemma tp_not {a : Xp} (ha : Tp Γ a) : Tp Γ (Xp.not a) := ⟨⟨_, hasTy_not ha.ex.choose_spec⟩⟩

lemma tp_xfX {mX : Xp} (hℓ : HasTy Γ gℓ (P 0 1)) (hm : Tp Γ mX) : ∀ k, Tp Γ (xfX mX k)
  | 0 => tp_const 0
  | k + 1 => tp_xorM (tp_xfX hℓ hm k) (tp_xorM (tp_shr hm (hasTy_mulC hℓ k)) (tp_const 0) hℓ) hℓ

lemma hasTy_var_lin {i : ℕ} (h : Γ.getD i (P 0 0) = P 0 0) : HasTy Γ (var i) (P 0 1) :=
  (hasTy_var' h).le ⟨le_rfl, Nat.zero_le _⟩

lemma tp_le {a b : Xp} (ha : Tp Γ a) (hb : Tp Γ b) : Tp Γ (Xp.le a b) :=
  tp_lt (tp_lt hb ha) (tp_const 1)

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

lemma HasCost.mono {g : Gn} {e d e' d' : ℕ} (h : HasCost Γ g e d) (he : e ≤ e') (hd : d ≤ d') :
    HasCost Γ g e' d' := h.mono he hd

lemma getD_top {D : ℕ} (us : List Ty) (hD : Γ.length = D) (j : ℕ) :
    (Γ ++ us).getD (D + j) (P 0 0) = us.getD j (P 0 0) := by
  subst hD
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

lemma TyB.tp {a : Xp} {τ : Ty} (h : TyB Γ a τ) : Tp Γ a := ⟨⟨τ, h.1⟩⟩

end Lax119563Proofs.Reduction
