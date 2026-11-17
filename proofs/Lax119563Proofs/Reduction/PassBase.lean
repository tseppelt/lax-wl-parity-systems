import Lax119563Proofs.Reduction.SlotList

/-!
# Infrastructure of the output passes

* `Iv M x s ℓ H`: the compiled code-ordered time program (as in `out_schEnum`);
* `globs`: the global values at the stack levels `0 … 16` (computed by the prelude), and
  `GlobOK` (the stack starts with them);
* `schCtx`: the schema enumerator as `(range E).flatMap` over contexts `SchCtx`;
* `slotLoops`: the loops over blocks `i ≤ s`, register values `v < 2^ℓ` (by `loopX`, so that
  `inBit x v` is available) and label numbers `t < 4`, with a count of the output of a test
  generator `V` (the domain violations) before the label loop (`out_slotLoops`);
* `entX`: the check row test `entB` as an expression.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs Lax119563Proofs.Matrix

/-! ## The system -/

/-- The code-ordered verifier program for the width `ℓ` and horizon `H`. -/
noncomputable abbrev APv (M : Machine) (x : List Bool) (s ℓ H : ℕ) : RegisterProgram s ℓ :=
  AP (ℓ := ℓ) (N := numLoc M H) Loc.code Loc.accept Loc.reject code_accept_ne_reject
    (verifierCmds' M x s ℓ H)

/-- Its compiled implicit parity system. -/
noncomputable def Iv (M : Machine) (x : List Bool) (s ℓ H : ℕ) :
    ImplicitParitySystem (s + 1) ℓ :=
  (APv M x s ℓ H).compile (Loc.query : Loc M H).code (fun _ _ => 0)

lemma Iv_schemas {M : Machine} {x : List Bool} {s ℓ H : ℕ} : (Iv M x s ℓ H).schemas =
    (APv M x s ℓ H).compiledSchemas (Loc.query : Loc M H).code (fun _ _ => 0) := rfl

/-! ## Globals -/

/-- The global values, at the stack levels `0 … 17` (`2^ℓ` at level `17`, so that the
`loopX` over register values has a limit of class `P 1 0`). -/
noncomputable def globs (M : Machine) (x : List Bool) (s ℓ H : ℕ) : List ℕ :=
  [x.length, Nat.log 2 x.length, ℓ, H, radix M H, numLoc M H, (verifierCmds' M x s ℓ H).length,
    ((verifierCmds' M x s ℓ H).map cmdSz).sum, (Loc.code (Loc.query : Loc M H)).val,
    (Loc.code (Loc.accept : Loc M H)).val, (Iv M x s ℓ H).schemas.length, numSteps (s + 1) ℓ,
    (Iv M x s ℓ H).numLocations, (Iv M x s ℓ H).schemas.length * numSteps (s + 1) ℓ,
    famCount (Iv M x s ℓ H), nOut (Iv M x s ℓ H),
    numLoc M H + 8 * (verifierCmds' M x s ℓ H).length + 3, 2 ^ ℓ]

/-- The stack starts with the globals. -/
def GlobOK (M : Machine) (x : List Bool) (s ℓ H : ℕ) (ρ : List ℕ) : Prop :=
  ρ.take 18 = globs M x s ℓ H

/-- Global expressions. -/
abbrev gℓ : Xp := var 2
abbrev gH : Xp := var 3
abbrev gR : Xp := var 4
abbrev gN : Xp := var 5
abbrev gr : Xp := var 6
abbrev gEc : Xp := var 7
abbrev gp0 : Xp := var 8
abbrev gacc : Xp := var 9
abbrev gE : Xp := var 10
abbrev gNS : Xp := var 11
abbrev gW : Xp := var 12
abbrev gENS : Xp := var 13
abbrev gFam : Xp := var 14
abbrev gnOut : Xp := var 15
abbrev gdet : Xp := var 16
abbrev gP : Xp := var 17

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

lemma length_globs : (globs M x s ℓ H).length = 18 := rfl

lemma GlobOK.le {ρ : List ℕ} (h : GlobOK M x s ℓ H ρ) : 18 ≤ ρ.length := by
  have := congrArg List.length h
  rw [List.length_take, length_globs] at this
  omega

lemma GlobOK.append {ρ : List ℕ} (h : GlobOK M x s ℓ H ρ) (l : List ℕ) :
    GlobOK M x s ℓ H (ρ ++ l) := by
  unfold GlobOK
  rw [List.take_append_of_le_length h.le]
  exact h

lemma GlobOK.getD {ρ : List ℕ} (h : GlobOK M x s ℓ H ρ) {k : ℕ} (hk : k < 18) :
    ρ.getD k 0 = (globs M x s ℓ H).getD k 0 := by
  rw [← h, getD_take' hk]

lemma GlobOK.var {ρ : List ℕ} (h : GlobOK M x s ℓ H ρ) {k : ℕ} (hk : k < 18) :
    (Xp.var k).eval ρ = (globs M x s ℓ H).getD k 0 := h.getD hk

section GlobEval

variable {ρ : List ℕ} (h : GlobOK M x s ℓ H ρ)
include h

lemma GlobOK.eℓ : gℓ.eval ρ = ℓ := by
  show (Xp.var _).eval ρ = _; rw [h.var (by omega)]; simp only [globs, List.getD_cons_succ, List.getD_cons_zero]
lemma GlobOK.eH : gH.eval ρ = H := by
  show (Xp.var _).eval ρ = _; rw [h.var (by omega)]; simp only [globs, List.getD_cons_succ, List.getD_cons_zero]
lemma GlobOK.eR : gR.eval ρ = radix M H := by
  show (Xp.var _).eval ρ = _; rw [h.var (by omega)]; simp only [globs, List.getD_cons_succ, List.getD_cons_zero]
lemma GlobOK.eN : gN.eval ρ = numLoc M H := by
  show (Xp.var _).eval ρ = _; rw [h.var (by omega)]; simp only [globs, List.getD_cons_succ, List.getD_cons_zero]
lemma GlobOK.er : gr.eval ρ = (verifierCmds' M x s ℓ H).length := by
  show (Xp.var _).eval ρ = _; rw [h.var (by omega)]; simp only [globs, List.getD_cons_succ, List.getD_cons_zero]
lemma GlobOK.eEc : gEc.eval ρ = ((verifierCmds' M x s ℓ H).map cmdSz).sum := by
  show (Xp.var _).eval ρ = _; rw [h.var (by omega)]; simp only [globs, List.getD_cons_succ, List.getD_cons_zero]
lemma GlobOK.ep0 : gp0.eval ρ = (Loc.code (Loc.query : Loc M H)).val := by
  show (Xp.var _).eval ρ = _; rw [h.var (by omega)]; simp only [globs, List.getD_cons_succ, List.getD_cons_zero]
lemma GlobOK.eacc : gacc.eval ρ = (Loc.code (Loc.accept : Loc M H)).val := by
  show (Xp.var _).eval ρ = _; rw [h.var (by omega)]; simp only [globs, List.getD_cons_succ, List.getD_cons_zero]
lemma GlobOK.eE : gE.eval ρ = (Iv M x s ℓ H).schemas.length := by
  show (Xp.var _).eval ρ = _; rw [h.var (by omega)]; simp only [globs, List.getD_cons_succ, List.getD_cons_zero]
lemma GlobOK.eNS : gNS.eval ρ = numSteps (s + 1) ℓ := by
  show (Xp.var _).eval ρ = _; rw [h.var (by omega)]; simp only [globs, List.getD_cons_succ, List.getD_cons_zero]
lemma GlobOK.eW : gW.eval ρ = (Iv M x s ℓ H).numLocations := by
  show (Xp.var _).eval ρ = _; rw [h.var (by omega)]; simp only [globs, List.getD_cons_succ, List.getD_cons_zero]
lemma GlobOK.eENS : gENS.eval ρ = (Iv M x s ℓ H).schemas.length * numSteps (s + 1) ℓ  := by
  show (Xp.var _).eval ρ = _; rw [h.var (by omega)]; simp only [globs, List.getD_cons_succ, List.getD_cons_zero]
lemma GlobOK.eFam : gFam.eval ρ = famCount (Iv M x s ℓ H) := by
  show (Xp.var _).eval ρ = _; rw [h.var (by omega)]; simp only [globs, List.getD_cons_succ, List.getD_cons_zero]
lemma GlobOK.enOut : gnOut.eval ρ = nOut (Iv M x s ℓ H) := by
  show (Xp.var _).eval ρ = _; rw [h.var (by omega)]; simp only [globs, List.getD_cons_succ, List.getD_cons_zero]
lemma GlobOK.edet : gdet.eval ρ = numLoc M H + 8 * (verifierCmds' M x s ℓ H).length + 3  := by
  show (Xp.var _).eval ρ = _; rw [h.var (by omega)]; simp only [globs, List.getD_cons_succ, List.getD_cons_zero]
lemma GlobOK.eP : gP.eval ρ = 2 ^ ℓ := by
  show (Xp.var _).eval ρ = _; rw [h.var (by omega)]; simp only [globs, List.getD_cons_succ, List.getD_cons_zero]

end GlobEval

lemma bnd_glob {k b : ℕ} (hk : k < 18) (hb : 18 ≤ b) : (Xp.var k).Bnd b :=
  show k < b by omega

/-! ## Stacks -/

lemma getD_app (τ l : List ℕ) (k : ℕ) : (τ ++ l).getD (τ.length + k) 0 = l.getD k 0 := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  congr 1; omega

lemma getD_app_lt {τ : List ℕ} (l : List ℕ) {k : ℕ} (hk : k < τ.length) :
    (τ ++ l).getD k 0 = τ.getD k 0 :=
  List.getD_append _ _ _ _ hk

/-! ## The schema enumerator as a loop over schema indices -/

/-- The context of the body of the schema enumerator for schema `e`. -/
def SchCtx (M : Machine) (x : List Bool) (s ℓ H b : ℕ) (ρ : List ℕ) (τ : List ℕ) (e : ℕ)
    (sc : Schema (s + 1) ℓ (Iv M x s ℓ H).numLocations) : Prop :=
  τ.length = b + 37 ∧ τ.take b = ρ ∧ τ.getD (b + 27) 0 = e ∧
    SchRec M x s ℓ H sc (τ.drop (b + 28))

lemma flatMap_eq_range {α β : Type} (l : List α) (d : α) (f : α → List β) :
    l.flatMap f = (List.range l.length).flatMap fun e => f (l.getD e d) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, ih, List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map]
    simp

lemma forall₂_getD {α β : Type} {R : α → β → Prop} (d : β) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ i (h₁ : i < l₁.length),
      R l₁[i] (l₂.getD i d)
  | _ :: _, _ :: _, List.Forall₂.cons h _, 0, _ => h
  | _ :: _, _ :: _, List.Forall₂.cons _ t, i + 1, h₁ => by
    simpa using forall₂_getD d t i (by simpa using h₁)

lemma getD_of_map_eq_range {α : Type} (f : α → ℕ) (d : α) {l : List α}
    (h : l.map f = List.range l.length) {i : ℕ} (hi : i < l.length) : f (l.getD i d) = i := by
  have := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, List.getElem?_range hi, List.getElem?_eq_getElem hi,
    Option.map_some, Option.some.injEq] at this
  rw [List.getD_eq_getElem _ _ hi]
  exact this

/-- **The schema enumerator**, indexed by schemas. -/
theorem schEnum_ctx {ρ : List ℕ} {b : ℕ} (hρ : ρ.length = b) (hG : GlobOK M x s ℓ H ρ) :
    ∃ T : ℕ → List ℕ, (∀ body : Gn, (schEnum M s b gH gR gN gr gp0 gEc body).out x ρ =
        (List.range (Iv M x s ℓ H).schemas.length).flatMap fun e => body.out x (T e)) ∧
      ∀ e (he : e < (Iv M x s ℓ H).schemas.length),
        SchCtx M x s ℓ H b ρ (T e) e (sch (Iv M x s ℓ H) ⟨e, he⟩) := by
  have hb : 18 ≤ b := hρ ▸ hG.le
  have hS := fun body => out_schEnum (M := M) (s := s) (x := x) (ℓ := ℓ) (H := H)
    hρ (bnd_glob (by omega) hb) (bnd_glob (by omega) hb) hG.eH hG.eR (bnd_glob (by omega) hb) hG.eN
    (bnd_glob (by omega) hb) hG.er (bnd_glob (by omega) hb) hG.ep0 (bnd_glob (by omega) hb) hG.eEc body
  obtain ⟨hF, hidx, -⟩ := hS Gn.skip
  have hlen := hF.length_eq
  refine ⟨fun e => (schStks M s b gH gR gN gr gp0 gEc x ρ ℓ H).getD e [], fun body => ?_,
    fun e he => ?_⟩
  · rw [(hS body).2.2, flatMap_eq_range _ [], ← hlen]
    rfl
  · have he' : e < (schStks M s b gH gR gN gr gp0 gEc x ρ ℓ H).length := by
      rw [← hlen]; exact he
    have hrel := forall₂_getD [] hF e he
    exact ⟨hrel.1, hrel.2.1, getD_of_map_eq_range _ [] hidx he', hrel.2.2⟩

/-! ## Slot loops -/

namespace Gn

/-- Loops over `i ≤ s`, `v < 2^ℓ` (with `inBit x v`; `PX` evaluates to `2^ℓ`), the count of
`V`, and `t < 4`. -/
def slotLoops (s : ℕ) (PX : Xp) (V body : Gn) : Gn :=
  .loop (const (s + 1)) (.loopX PX (.count V (.loop (const 4) body)))

end Gn

/-- The stack of the body of the slot loops. -/
def slotStk (s ℓ : ℕ) (x : List Bool) (τ : List ℕ) (V : Gn) (i v t : ℕ) : List ℕ :=
  τ ++ [s + 1, i, 2 ^ ℓ, v, inBit x v, (V.out x (τ ++ [s + 1, i, 2 ^ ℓ, v, inBit x v, 0])).length,
    4, t]

lemma out_slotLoops {τ : List ℕ} {PX : Xp} (hPb : PX.Bnd τ.length) (hP : PX.eval τ = 2 ^ ℓ)
    (V body : Gn) :
    (Gn.slotLoops s PX V body).out x τ =
      slotL s ℓ fun i v t => body.out x (slotStk s ℓ x τ V i v t) := by
  have key : ∀ l, PX.eval (τ ++ l) = 2 ^ ℓ := fun l => by rw [eval_append rfl l hPb, hP]
  simp only [Gn.slotLoops, Gn.out, slotL, eval_const, key, List.append_assoc,
    List.cons_append, List.nil_append, slotStk]

lemma slotStk_getD {τ : List ℕ} (V : Gn) (i v t : ℕ) :
    (slotStk s ℓ x τ V i v t).getD (τ.length + 1) 0 = i ∧
    (slotStk s ℓ x τ V i v t).getD (τ.length + 3) 0 = v ∧
    (slotStk s ℓ x τ V i v t).getD (τ.length + 4) 0 = inBit x v ∧
    (slotStk s ℓ x τ V i v t).getD (τ.length + 5) 0 =
      (V.out x (τ ++ [s + 1, i, 2 ^ ℓ, v, inBit x v, 0])).length ∧
    (slotStk s ℓ x τ V i v t).getD (τ.length + 7) 0 = t := by
  simp [slotStk]

lemma slotStk_lt {τ : List ℕ} (V : Gn) (i v t : ℕ) {k : ℕ} (hk : k < τ.length) :
    (slotStk s ℓ x τ V i v t).getD k 0 = τ.getD k 0 := getD_app_lt _ hk

lemma slotStk_length {τ : List ℕ} (V : Gn) (i v t : ℕ) :
    (slotStk s ℓ x τ V i v t).length = τ.length + 8 := by simp [slotStk]

/-! ## Check rows -/

/-- The test `entB s j i v` (`0`/`1`). -/
def entX (s : ℕ) (jX iX vX : Xp) : Xp :=
  or (and (lt jX (const s)) (or (eq iX jX) (eq iX (const s))))
    (and (le (const s) jX) (odd (shr (shl vX (const s)) jX)))

lemma eval_entX {ρ : List ℕ} (jX iX vX : Xp) :
    (entX s jX iX vX).eval ρ =
      if entB s (jX.eval ρ) (iX.eval ρ) (vX.eval ρ) = true then 1 else 0 := by
  have hodd : (odd (shr (shl vX (const s)) jX)).eval ρ =
      if (odd (shr (shl vX (const s)) jX)).eval ρ = 1 then 1 else 0 := by
    have : (odd (shr (shl vX (const s)) jX)).eval ρ < 2 := by simp only [eval_odd]; omega
    split_ifs <;> omega
  have hb : s ≤ jX.eval ρ → ((odd (shr (shl vX (const s)) jX)).eval ρ = 1 ↔
      (vX.eval ρ).testBit (jX.eval ρ - s) = true) := by
    intro hj
    simp only [eval_odd, eval_shr, eval_shl, eval_const]
    have e : jX.eval ρ = s + (jX.eval ρ - s) := by omega
    rw [e, shift_bit, testBit_eq_mod, ← e]
    simp
  rw [entX, eval_or' (eval_and' (eval_lt_eq _ _) (eval_or' (eval_eq' _ _) (eval_eq' _ _)))
      (eval_and' (eval_le _ _) hodd)]
  simp only [eval_const]
  unfold entB
  by_cases hj : jX.eval ρ < s
  · have : ¬ s ≤ jX.eval ρ := by omega
    simp [hj, this]
  · have h' := hb (by omega)
    simp only [hj, if_false, show s ≤ jX.eval ρ by omega, true_and, false_and, false_or, h']

end Lax119563Proofs.Reduction
