import Lax119563Proofs.Reduction.CostWF
import Lax119563Proofs.Reduction.CostPassBase
import Lax119563Proofs.Reduction.CostGlob

/-!
# The prelude: computing the globals

`prelude M s C₀ g` pushes the 14 globals `globs M x s ℓ H` (for `ℓ = timeWidth C₀ |x|`,
`H = timeHorizon s C₀ |x|`) and runs `g` on them (**`out_prelude`**, for `s ≥ 2`):
`|x|` (`len`), `log₂ |x|` (`log`), `ℓ`, `H`, `R`, `N = 16 R^5` by expressions, the command
count `r` and the schema count `Ec` by counting runs of the command enumerator, the codes of
`query` (`2`) and `accept` (`0`), the number `E` of schemas by a counting run of the schema
enumerator, `W, det` by expressions and `2^ℓ` as
`min (2^ℓ) (2^(C₀+4) (|x| + 1))` (so that it is of class `P 1 0`).
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs

namespace Gn

/-- The size count body: `9` zeros for a fork, `4` for an assignment (record at `b + 17`). -/
def szBody (b : ℕ) : Gn := .ite (var (b + 17)) (emitN 9) (emitN 4)

/-- **The prelude.** -/
def prelude (M : Machine) (s C₀ : ℕ) (g : Gn) : Gn :=
  len <| log (var 0) <|
  bind (add (var 1) (const (C₀ + 4))) <|
  bind (add (mulC (s - 2) (var 2)) (mulC 2 (add (var 1) (const (C₀ + 3))))) <|
  bind (add (var 3) (const (1 + cM M))) <|
  bind (mulC 16 (mul (mul (mul (mul (var 4) (var 4)) (var 4)) (var 4)) (var 4))) <|
  count (cmdEnum M s 7 (var 3) (var 4) (emit (const 0))) <|
  count (cmdEnum M s 8 (var 3) (var 4) (szBody 8)) <|
  bind (const 2) <|
  bind (const 0) <|
  count (schEnum M s 11 gH gR gN gr gp0 gEc (emit (const 0))) <|
  bind (add (add (var 5) (mulC 8 (var 6))) (const 4)) <|
  bind (add (add (var 5) (mulC 8 (var 6))) (const 3)) <|
  bind (minR (pow2 (var 2)) (mulC (2 ^ (C₀ + 4)) (add (var 0) (const 1)))) g

end Gn

/-! ## Steps -/

section Steps

variable {x : List Bool} {G : List ℕ}

lemma take_succ_getD {k : ℕ} (hk : k < G.length) : G.take k ++ [G.getD k 0] = G.take (k + 1) := by
  rw [List.take_succ, List.getElem?_eq_getElem hk, List.getD_eq_getElem _ _ hk]
  rfl

lemma out_bind_step {k : ℕ} (hk : k < G.length) {e : Xp} {g : Gn}
    (he : e.eval (G.take k) = G.getD k 0) :
    (Gn.bind e g).out x (G.take k) = g.out x (G.take (k + 1)) := by
  simp only [Gn.out, he, take_succ_getD hk]

lemma out_count_step {k : ℕ} (hk : k < G.length) {g h : Gn}
    (hl : (g.out x (G.take k ++ [0])).length = G.getD k 0) :
    (Gn.count g h).out x (G.take k) = h.out x (G.take (k + 1)) := by
  simp only [Gn.out, hl, take_succ_getD hk]

lemma getD_take_lt {l : List ℕ} {i k : ℕ} (h : i < k) : (l.take k).getD i 0 = l.getD i 0 :=
  getD_take' h

lemma getD_take_app {l : List ℕ} {i k : ℕ} (h : i < k) (hk : k ≤ l.length) (a : ℕ) :
    (l.take k ++ [a]).getD i 0 = l.getD i 0 := by
  rw [List.getD_append _ _ _ _ (by simp; omega), getD_take' h]

end Steps

/-! ## Values -/

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

lemma Iv_numLocations :
    (Iv M x s ℓ H).numLocations = numLoc M H + (verifierCmds' M x s ℓ H).length * 8 + 4 := by
  have hc : (APv M x s ℓ H).commands.length = (verifierCmds' M x s ℓ H).length := by
    simp only [AP_commands]; exact List.length_map _
  show (APv M x s ℓ H).numLocations + (APv M x s ℓ H).commands.length * 8 + 4 = _
  rw [hc]
  rfl

lemma code_query_val : (Loc.code (Loc.query : Loc M H)).val = 2 := by
  simp [Loc.code, Loc.tuple, pack]

lemma code_accept_val : (Loc.code (Loc.accept : Loc M H)).val = 0 := by
  simp [Loc.code, Loc.tuple, pack]

lemma sum_map_forall₂ {α β : Type} {R : α → β → Prop} {f : α → ℕ} {g : β → ℕ} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → (∀ a b, R a b → f a = g b) →
      (l₁.map f).sum = (l₂.map g).sum
  | _, _, .nil, _ => rfl
  | _, _, .cons h t, hf => by
    simp only [List.map_cons, List.sum_cons, hf _ _ h, sum_map_forall₂ t hf]

lemma length_flatMap_emit {α : Type} (l : List α) (f : α → List ℕ) (hf : ∀ a, (f a).length = 1) :
    (l.flatMap f).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [hf a, ih]; omega

lemma two_pow_timeWidth_le (C₀ n : ℕ) : 2 ^ timeWidth C₀ n ≤ 2 ^ (C₀ + 4) * (n + 1) := by
  unfold timeWidth
  rw [show Nat.log 2 n + C₀ + 4 = (C₀ + 4) + Nat.log 2 n by omega, pow_add]
  refine Nat.mul_le_mul_left _ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (Nat.pow_log_le_self 2 hn.ne').trans (Nat.le_succ n)

lemma lt_two_pow_timeWidth (C₀ n : ℕ) : n < 2 ^ timeWidth C₀ n := by
  unfold timeWidth
  calc n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **The prelude computes the globals.** -/
theorem out_prelude {C₀ : ℕ} (hs : 2 ≤ s) (g : Gn) :
    (Gn.prelude M s C₀ g).out x [] =
      g.out x (globs M x s (timeWidth C₀ x.length) (timeHorizon s C₀ x.length)) := by
  set ℓ := timeWidth C₀ x.length with hℓ
  set H := timeHorizon s C₀ x.length with hH
  set G := globs M x s ℓ H with hG
  have hGl : G.length = 14 := length_globs
  have eG : ∀ i, G.getD i 0 = (globs M x s ℓ H).getD i 0 := fun _ => rfl
  -- levels 0, 1
  have h1 : (Gn.prelude M s C₀ g).out x [] = (Gn.prelude M s C₀ g).out x (G.take 0) := rfl
  rw [h1, Gn.prelude]
  have s0 : ∀ g' : Gn, (Gn.len g').out x (G.take 0) = g'.out x (G.take 1) := fun g' => by
    simp only [Gn.out]; rfl
  have s1 : ∀ g' : Gn, (Gn.log (var 0) g').out x (G.take 1) = g'.out x (G.take 2) := fun g' => by
    simp only [Gn.out]; rfl
  rw [s0, s1]
  -- level 2: ℓ
  rw [out_bind_step (by omega) (by
    simp only [eval_add, eval_var, eval_const, getD_take_lt (show 1 < 2 by omega)]
    simp only [hG, globs, List.getD_cons_succ, List.getD_cons_zero, hℓ, timeWidth]; omega)]
  -- level 3: H
  rw [out_bind_step (by omega) (by
    simp only [eval_add, eval_var, eval_const, eval_mulC, getD_take_lt (show 1 < 3 by omega),
      getD_take_lt (show 2 < 3 by omega)]
    simp only [hG, globs, List.getD_cons_succ, List.getD_cons_zero, hH, timeHorizon, ← hℓ]
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
    have : ℓ = Nat.log 2 x.length + C₀ + 4 := rfl
    rw [this]; simp only [Nat.add_sub_cancel]; ring_nf; omega)]
  -- level 4: R
  rw [out_bind_step (by omega) (by
    simp only [eval_add, eval_var, eval_const, getD_take_lt (show 3 < 4 by omega)]
    simp only [hG, globs, List.getD_cons_succ, List.getD_cons_zero, radix]; omega)]
  -- level 5: N
  rw [out_bind_step (by omega) (by
    simp only [eval_mul, eval_var, eval_mulC, getD_take_lt (show 4 < 5 by omega)]
    simp only [hG, globs, List.getD_cons_succ, List.getD_cons_zero, numLoc]; ring)]
  -- level 6: r
  have ev6 : ∀ i < 6, (G.take 6 ++ [0]).getD i 0 = G.getD i 0 := fun i hi =>
    getD_take_app hi (by omega) 0
  have eH6 : (var 3).eval (G.take 6 ++ [0]) = H := by
    simp only [eval_var, ev6 3 (by omega)]; rfl
  have eR6 : (var 4).eval (G.take 6 ++ [0]) = radix M H := by
    simp only [eval_var, ev6 4 (by omega)]; rfl
  have hl6 : (G.take 6 ++ [0]).length = 7 := by simp [hGl]
  rw [out_count_step (by omega) (by
    rw [out_cmdEnum' (M := M) (s := s) hl6 (show (var 3).Bnd 7 from show 3 < 7 by omega) (show (var 4).Bnd 7 from show 4 < 7 by omega) eH6 eR6,
      length_flatMap_emit _ _ (fun _ => rfl),
      (cmdStks_forall₂ hl6 (show (var 3).Bnd 7 from show 3 < 7 by omega) (show (var 4).Bnd 7 from show 4 < 7 by omega) eH6 eR6 ℓ).length_eq]
    rfl)]
  -- level 7: Ec
  have ev7 : ∀ i < 7, (G.take 7 ++ [0]).getD i 0 = G.getD i 0 := fun i hi =>
    getD_take_app hi (by omega) 0
  have eH7 : (var 3).eval (G.take 7 ++ [0]) = H := by
    simp only [eval_var, ev7 3 (by omega)]; rfl
  have eR7 : (var 4).eval (G.take 7 ++ [0]) = radix M H := by
    simp only [eval_var, ev7 4 (by omega)]; rfl
  have hl7 : (G.take 7 ++ [0]).length = 8 := by simp [hGl]
  rw [out_count_step (by omega) (by
    rw [out_cmdEnum' (M := M) (s := s) hl7 (show (var 3).Bnd 8 from show 3 < 8 by omega) (show (var 4).Bnd 8 from show 4 < 8 by omega) eH7 eR7,
      List.length_flatMap]
    have hF := cmdStks_forall₂ (x := x) (s := s) hl7 (show (var 3).Bnd 8 from show 3 < 8 by omega) (show (var 4).Bnd 8 from show 4 < 8 by omega) eH7 eR7 ℓ
    rw [sum_map_forall₂ (g := cmdSz) hF (fun τ cmd h => ?_)]
    · rfl
    · rw [← szAt_of_stkCmd h]
      unfold szAt
      simp only [Gn.szBody, Gn.out, eval_var]
      split <;> rename_i hc <;> simp only [ne_eq, hc, not_false_eq_true, not_true_eq_false,
        if_true, if_false, ite_true, ite_false, Decidable.not_not] <;> exact Gn.length_out_emitN _)]
  -- levels 8, 9: the codes of `query` and `accept`
  rw [out_bind_step (by omega) (by
    simp only [eval_const, hG, globs, List.getD_cons_succ, List.getD_cons_zero]
    exact code_query_val.symm)]
  rw [out_bind_step (by omega) (by
    simp only [eval_const, hG, globs, List.getD_cons_succ, List.getD_cons_zero]
    exact code_accept_val.symm)]
  -- level 10: E
  have ev10 : ∀ i < 10, (G.take 10 ++ [0]).getD i 0 = G.getD i 0 := fun i hi =>
    getD_take_app hi (by omega) 0
  have hl10 : (G.take 10 ++ [0]).length = 11 := by simp [hGl]
  have bnd : ∀ i < 11, (var i).Bnd 11 := fun i hi => show i < 11 from hi
  have hS := out_schEnum (M := M) (s := s) (x := x) (ℓ := ℓ) (H := H) hl10 (bnd 3 (by omega))
    (bnd 4 (by omega)) (by simp only [eval_var, ev10 3 (by omega)]; rfl)
    (by simp only [eval_var, ev10 4 (by omega)]; rfl) (bnd 5 (by omega))
    (by simp only [eval_var, ev10 5 (by omega)]; rfl) (bnd 6 (by omega))
    (by simp only [eval_var, ev10 6 (by omega)]; rfl) (bnd 8 (by omega))
    (by simp only [eval_var, ev10 8 (by omega)]; rfl) (bnd 7 (by omega))
    (by simp only [eval_var, ev10 7 (by omega)]; rfl) (Gn.emit (const 0))
  rw [out_count_step (by omega) (by
    rw [hS.2.2, length_flatMap_emit _ _ (fun _ => rfl), ← hS.1.length_eq]
    rw [hG]
    simp only [globs, List.getD_cons_succ, List.getD_cons_zero]
    exact (congrArg List.length (Iv_schemas (M := M) (x := x) (s := s) (ℓ := ℓ) (H := H))).symm)]
  -- level 11: W
  rw [out_bind_step (by omega) (by
    simp only [eval_add, eval_var, eval_const, eval_mulC, getD_take_lt (show 5 < 11 by omega),
      getD_take_lt (show 6 < 11 by omega)]
    simp only [hG, globs, List.getD_cons_succ, List.getD_cons_zero]
    rw [Iv_numLocations]; ring)]
  -- level 12: det
  rw [out_bind_step (by omega) (by
    simp only [eval_add, eval_var, eval_const, eval_mulC, getD_take_lt (show 5 < 12 by omega),
      getD_take_lt (show 6 < 12 by omega)]
    simp only [hG, globs, List.getD_cons_succ, List.getD_cons_zero])]
  -- level 13: 2^ℓ
  rw [out_bind_step (by omega) (by
    simp only [eval_minR, eval_pow2, eval_add, eval_var, eval_const, eval_mulC,
      getD_take_lt (show 2 < 13 by omega), getD_take_lt (show 0 < 13 by omega)]
    simp only [hG, globs, List.getD_cons_succ, List.getD_cons_zero]
    exact min_eq_left (two_pow_timeWidth_le C₀ x.length))]
  rw [List.take_of_length_le (by omega)]

/-! ## Fits, cost and well-formedness -/

open Ty Gn in
/-- **Fits and cost of the prelude.** -/
theorem Gn.hasCost_prelude (M : Machine) (s C₀ : ℕ) {D : ℕ} (hD : 12 ≤ D) {g : Gn}
    (hg : HasCost globTys g 1 D) : HasCost [] (Gn.prelude M s C₀ g) 1 D := by
  have lin : ∀ {Γ : List Ty} (c : ℕ), HasTy Γ (const c) (P 0 1) := fun c => hasTy_lin_const c
  have L : ∀ {Γ : List Ty} {i d d' : ℕ}, Γ.getD i (P 0 0) = P 0 d → d ≤ d' →
      HasTy Γ (var i) (P 0 d') := fun h hd => (hasTy_var' h).le ⟨le_rfl, hd⟩
  unfold Gn.prelude
  refine (hasCost_len (e := 1) (d := D) ?_).mono (by simp) le_rfl
  refine (hasCost_log (e₀ := 1) (d₀ := 0) (e := 1) (d := D) (hasTy_var' rfl) ?_).mono
    (by simp) (by simp)
  -- ℓ, H, R, N
  refine hasCost_bind (τ := P 0 1) ?_ ?_
  · exact hasTy_add (hasTy_var' rfl) (lin _)
  refine hasCost_bind (τ := P 0 1) ?_ ?_
  · exact hasTy_add (hasTy_mulC (hasTy_var' rfl) _) (hasTy_mulC (hasTy_add (hasTy_var' rfl) (lin _)) _)
  refine hasCost_bind (τ := P 0 1) ?_ ?_
  · exact hasTy_add (hasTy_var' rfl) (lin _)
  refine hasCost_bind (τ := P 0 5) ?_ ?_
  · have hR : HasTy ([] ++ [P 1 0] ++ [P 0 1] ++ [P 0 1] ++ [P 0 1] ++ [P 0 1]) (var 4) (P 0 1) :=
      hasTy_var' rfl
    simpa using hasTy_mulC (hasTy_mul (hasTy_mul (hasTy_mul (hasTy_mul hR hR hR) hR hR) hR hR)
      hR hR) 16
  -- r
  have hc6 := hasCost_cmdEnum (M := M) (s := s)
    (τs := [] ++ [P 1 0] ++ [P 0 1] ++ [P 0 1] ++ [P 0 1] ++ [P 0 1] ++ [P 0 5] ++ [P 0 0])
    (b := 7) rfl (HX := var 3) (RX := var 4) ⟨hasTy_var' rfl, by show _ < List.length _; decide⟩ ⟨hasTy_var' rfl, by show _ < List.length _; decide⟩
    (hasCost_emit (hasTy_const 0) : HasCost _ (emit (const 0)) 0 0)
  refine hasCost_count (hc6.mono (by omega) (by omega)) hc6.len ?_
  -- Ec
  have hc7 := hasCost_cmdEnum (M := M) (s := s)
    (τs := [] ++ [P 1 0] ++ [P 0 1] ++ [P 0 1] ++ [P 0 1] ++ [P 0 1] ++ [P 0 5] ++ [P 0 (0 + 6 + 1)]
      ++ [P 0 0])
    (b := 8) rfl (HX := var 3) (RX := var 4) ⟨hasTy_var' rfl, by show _ < List.length _; decide⟩ ⟨hasTy_var' rfl, by show _ < List.length _; decide⟩
    (hasCost_ite (hasTy_var _) (hasCost_emitN 9) (hasCost_emitN 4) : HasCost _ (szBody 8) 0 0)
  refine hasCost_count (hc7.mono (by omega) (by omega)) hc7.len ?_
  -- codes
  refine hasCost_bind (τ := P 0 0) (hasTy_const 2) ?_
  refine hasCost_bind (τ := P 0 0) (hasTy_const 0) ?_
  -- E
  have hc10 := hasCost_schEnum (M := M) (s := s)
    (τs := [] ++ [P 1 0] ++ [P 0 1] ++ [P 0 1] ++ [P 0 1] ++ [P 0 1] ++ [P 0 5] ++ [P 0 (0 + 6 + 1)]
      ++ [P 0 (0 + 6 + 1)] ++ [P 0 0] ++ [P 0 0] ++ [P 0 0])
    (b := 11) rfl (HX := gH) (RX := gR) (NX := gN) (rX := gr) (p0X := gp0) (EcX := gEc) ⟨hasTy_var' rfl, by show _ < List.length _; decide⟩ ⟨hasTy_var' rfl, by show _ < List.length _; decide⟩
    ⟨(hasTy_var' (τ := P 0 5) rfl).le (show Ty.Le (P 0 5) (P 0 7) from ⟨le_rfl, by norm_num⟩),
      by show _ < List.length _; decide⟩ ⟨hasTy_var' rfl, by show _ < List.length _; decide⟩
    ⟨(hasTy_var' (τ := P 0 0) rfl).le (show Ty.Le (P 0 0) (P 0 7) from ⟨le_rfl, by norm_num⟩),
      by show _ < List.length _; decide⟩ ⟨hasTy_var' rfl, by show _ < List.length _; decide⟩
    (hasCost_emit (hasTy_const 0) : HasCost _ (emit (const 0)) 0 0)
  refine hasCost_count (hc10.mono (by omega) (by omega)) (hc10.len.le (show Ty.Le (P 0 (0 + 12 + 1)) (P 0 20) from ⟨le_rfl, by norm_num⟩)) ?_
  -- W, det, 2^ℓ
  refine hasCost_bind (τ := P 0 20) ?_ ?_
  · exact hasTy_add (hasTy_add (L rfl (by norm_num)) (hasTy_mulC (L rfl (by norm_num)) _))
      ((hasTy_const _).le ⟨le_rfl, by norm_num⟩)
  refine hasCost_bind (τ := P 0 7) ?_ ?_
  · exact hasTy_add (hasTy_add (L rfl (by norm_num)) (hasTy_mulC (L rfl le_rfl) _))
      ((hasTy_const _).le ⟨le_rfl, by norm_num⟩)
  refine hasCost_bind (τ := P 1 0) ?_ ?_
  · exact hasTy_minR (hasTy_pow2 (hasTy_var' rfl))
      (hasTy_mulC (hasTy_add (hasTy_var' rfl) ((hasTy_const _).le ⟨by norm_num, le_rfl⟩)) _)
  exact hg

lemma Gn.wfx_len {g : Gn} (h : WFX g) : WFX (len g) := h

/-- The prelude is well formed if its body is. -/
theorem Gn.wfx_prelude (M : Machine) (s C₀ : ℕ) {g : Gn} (hg : WFX g) :
    WFX (Gn.prelude M s C₀ g) := by
  unfold Gn.prelude
  refine wfx_len (cl_wfx.log _ ?_)
  refine cl_wfx.bind _ <| cl_wfx.bind _ <| cl_wfx.bind _ <| cl_wfx.bind _ ?_
  refine cl_wfx.count (cl_wfx.cmdEnum _ _ _ _ _ trivial) ?_
  refine cl_wfx.count (cl_wfx.cmdEnum _ _ _ _ _ (cl_wfx.ite _ (cl_wfx.emitN 9) (cl_wfx.emitN 4))) ?_
  refine cl_wfx.bind _ (cl_wfx.bind _ (cl_wfx.count (cl_wfx.schEnum _ _ _ _ _ _ _ _ _ trivial) ?_))
  exact cl_wfx.bind _ <| cl_wfx.bind _ <| cl_wfx.bind _ hg

end Lax119563Proofs.Reduction
