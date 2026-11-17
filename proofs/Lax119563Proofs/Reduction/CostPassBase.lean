import Lax119563Proofs.Reduction.CostGlob
import Lax119563Proofs.Reduction.DescGen

/-!
# Fits and cost of the output passes: tools

* `Tp Γ e`: `e` has *some* class (enough for emitted numbers and tests); rules `tp_*` and the
  tactic `tp`, which also closes the linear (`P 0 1`) side conditions of shifts and products
  for concrete contexts;
* `hasCost_slotLoops`, `hasCost_stepLoops`, `hasCost_prevGen`: the loop skeletons;
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

/-! ## Loop skeletons -/

lemma hasCost_slotLoops {s d : ℕ} {PX : Xp} {V body : Gn} (hP : TyB Γ PX (P 1 0))
    (hV : HasCost (Γ ++ [P 0 0, P 0 0] ++ [P 1 0, P 1 0, P 0 0] ++ [P 0 0]) V 0 1)
    (hb : HasCost (Γ ++ [P 0 0, P 0 0] ++ [P 1 0, P 1 0, P 0 0] ++ [P 0 2] ++ [P 0 0, P 0 0])
      body 0 d) (hd : 1 ≤ d) :
    HasCost Γ (slotLoops s PX V body) 1 d := by
  unfold slotLoops
  have h4 := hasCost_loop (τs := Γ ++ [P 0 0, P 0 0] ++ [P 1 0, P 1 0, P 0 0] ++ [P 0 2])
    (hasTy_const 4) hb
  have hc := hasCost_count (τ := P 0 2) (hV.mono le_rfl hd) hV.len (h4.mono (by simp) (by simp))
  have hx := hasCost_loopX (hP.weaken [P 0 0, P 0 0]).1 hc
  exact (hasCost_loop (hasTy_const (s + 1)) hx).mono (by simp) (by simp)

lemma hasCost_stepLoops {s e d : ℕ} {g : Gn} (hℓ : TyB Γ gℓ (P 0 1))
    (hg : HasCost (Γ ++ [P 0 0, P 0 0] ++ [P 0 1, P 0 1]) g e d) :
    HasCost Γ (stepLoops s g) e (d + 1) := by
  unfold stepLoops
  exact (hasCost_loop (hasTy_const (s + 2))
    (hasCost_loop (hasTy_add (hasTy_lin_const s) (hℓ.weaken _).1) hg)).mono (by simp) (by omega)

lemma getD_top {D : ℕ} (us : List Ty) (hD : Γ.length = D) (j : ℕ) :
    (Γ ++ us).getD (D + j) (P 0 0) = us.getD j (P 0 0) := by
  subst hD
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

lemma tp_stepX {s D : ℕ} (hℓ : HasTy Γ gℓ (P 0 1)) : Tp Γ (stepX s D) :=
  tp_add (tp_mul (tp_var _) (hasTy_add (hasTy_lin_const s) hℓ)) (tp_var _)

lemma tp_entX {s : ℕ} {jX iX vX : Xp} (hj : HasTy Γ jX (P 0 1)) (hi : Tp Γ iX) (hv : Tp Γ vX) :
    Tp Γ (entX s jX iX vX) :=
  tp_or (tp_and (tp_lt ⟨⟨_, hj⟩⟩ (tp_const s)) (tp_or (tp_eq hi ⟨⟨_, hj⟩⟩) (tp_eq hi (tp_const s))))
    (tp_and (tp_le (tp_const s) ⟨⟨_, hj⟩⟩) (tp_odd (tp_shr (tp_shl hv (hasTy_lin_const s)) hj)))

lemma TyB.tp {a : Xp} {τ : Ty} (h : TyB Γ a τ) : Tp Γ a := ⟨⟨τ, h.1⟩⟩

lemma hasCost_prevGen {s D : ℕ} (hD : Γ.length = D) {σX iX vX : Xp} {τσ τi τv : Ty}
    (hℓ : TyB Γ gℓ (P 0 1)) (hσ : TyB Γ σX τσ) (hi : TyB Γ iX τi) (hv : TyB Γ vX τv) :
    HasCost Γ (prevGen s D σX iX vX) 0 2 := by
  unfold prevGen
  refine hasCost_stepLoops hℓ ?_
  have W0 : ∀ {a : Xp} {τ : Ty}, TyB Γ a τ →
      TyB (Γ ++ [P 0 0, P 0 0] ++ [P 0 1, P 0 1]) a τ := fun h => (h.weaken _).weaken _
  have W1 : ∀ {a : Xp} {τ : Ty}, TyB Γ a τ →
      TyB (Γ ++ [P 0 0, P 0 0] ++ [P 0 1, P 0 1] ++ [P 0 0] ++ [P 0 0, P 0 0] ++ [P 0 1, P 0 1])
        a τ := fun h => (((W0 h).weaken _).weaken _).weaken _
  have hj : HasTy (Γ ++ [P 0 0, P 0 0] ++ [P 0 1, P 0 1] ++ [P 0 0] ++ [P 0 0, P 0 0] ++
      [P 0 1, P 0 1]) (var (D + 5 + 3)) (P 0 1) := by
    refine hasTy_var' ?_
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact getD_top _ hD 8
  have hinner : HasCost (Γ ++ [P 0 0, P 0 0] ++ [P 0 1, P 0 1] ++ [P 0 0])
      (stepLoops s (when (Xp.and (Xp.and (Xp.lt (stepX s (D + 5)) σX)
        (Xp.le (stepX s D) (stepX s (D + 5)))) (entX s (var (D + 5 + 3)) iX vX))
        (emit (const 0)))) 0 1 := by
    refine hasCost_stepLoops ((W0 hℓ).weaken _) (hasCost_when' ?_ (hasCost_emit' (tp_const 0)))
    have h1 := (W1 hℓ).1
    have h2 := (W1 hσ).tp
    have h3 := (W1 hi).tp
    have h4 := (W1 hv).tp
    have h5 : Tp _ (stepX s (D + 5)) := tp_stepX (D := D + 5) (s := s) h1
    have h6 : Tp _ (stepX s D) := tp_stepX (D := D) (s := s) h1
    have h7 := tp_entX (s := s) hj h3 h4
    exact tp_and (tp_and (tp_lt h5 h2) (tp_le h6 h5)) h7
  refine hasCost_count (τ := P 0 2) hinner hinner.len ?_
  refine (hasCost_when' ?_ (hasCost_emit' (tp_const 0))).mono le_rfl (Nat.zero_le _)
  have h1 := ((W0 hℓ).weaken [P 0 2]).1
  have h2 := ((W0 hσ).weaken [P 0 2]).tp
  have h6 : Tp _ (stepX s D) := tp_stepX (D := D) (s := s) h1
  exact tp_and (tp_lt h6 h2) (tp_not (tp_eq (tp_var _) (tp_const 0)))

end Lax119563Proofs.Reduction
