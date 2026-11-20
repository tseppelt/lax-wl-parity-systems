import Lax119563Proofs.Reduction.PkCost

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

/-- **Fits and cost of the domain test** (as `hasCost_violGen`). -/
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

lemma length_ΓSP : ΓSP.length = 56 := rfl

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
