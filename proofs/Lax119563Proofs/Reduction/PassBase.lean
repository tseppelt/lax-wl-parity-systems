import Lax119563Proofs.Reduction.DomGen

/-!
# Infrastructure of the system generator

* `Iv M x s ℓ H`: the compiled code-ordered time program (as in `out_schEnum`);
* `globs`: the global values at the stack levels `0 … 13` (computed by the prelude), and
  `GlobOK` (the stack starts with them);
* `schEnum_ctx`: the schema enumerator as `(range E).flatMap` over contexts `SchCtx`;
* `violAt`: the domain test of the schema of a schema stack at a coordinate
  (`violAt_nil_iff`);
* `shiftX`: the shift `shiftVal s ℓ m i` of a permutation described by a mask.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs

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

/-- The global values, at the stack levels `0 … 13` (`2^ℓ` at level `13`, so that the
`loopX` over register values has a limit of class `P 1 0`). -/
noncomputable def globs (M : Machine) (x : List Bool) (s ℓ H : ℕ) : List ℕ :=
  [x.length, Nat.log 2 x.length, ℓ, H, radix M H, numLoc M H, (verifierCmds' M x s ℓ H).length,
    ((verifierCmds' M x s ℓ H).map cmdSz).sum, (Loc.code (Loc.query : Loc M H)).val,
    (Loc.code (Loc.accept : Loc M H)).val, (Iv M x s ℓ H).schemas.length,
    (Iv M x s ℓ H).numLocations, numLoc M H + 8 * (verifierCmds' M x s ℓ H).length + 3, 2 ^ ℓ]

/-- The stack starts with the globals. -/
def GlobOK (M : Machine) (x : List Bool) (s ℓ H : ℕ) (ρ : List ℕ) : Prop :=
  ρ.take 14 = globs M x s ℓ H

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
abbrev gW : Xp := var 11
abbrev gdet : Xp := var 12
abbrev gP : Xp := var 13

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

lemma length_globs : (globs M x s ℓ H).length = 14 := rfl

lemma GlobOK.le {ρ : List ℕ} (h : GlobOK M x s ℓ H ρ) : 14 ≤ ρ.length := by
  have := congrArg List.length h
  rw [List.length_take, length_globs] at this
  omega

lemma GlobOK.append {ρ : List ℕ} (h : GlobOK M x s ℓ H ρ) (l : List ℕ) :
    GlobOK M x s ℓ H (ρ ++ l) := by
  unfold GlobOK
  rw [List.take_append_of_le_length h.le]
  exact h

lemma GlobOK.getD {ρ : List ℕ} (h : GlobOK M x s ℓ H ρ) {k : ℕ} (hk : k < 14) :
    ρ.getD k 0 = (globs M x s ℓ H).getD k 0 := by
  rw [← h, getD_take' hk]

lemma GlobOK.var {ρ : List ℕ} (h : GlobOK M x s ℓ H ρ) {k : ℕ} (hk : k < 14) :
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
lemma GlobOK.eW : gW.eval ρ = (Iv M x s ℓ H).numLocations := by
  show (Xp.var _).eval ρ = _; rw [h.var (by omega)]; simp only [globs, List.getD_cons_succ, List.getD_cons_zero]
lemma GlobOK.edet : gdet.eval ρ = numLoc M H + 8 * (verifierCmds' M x s ℓ H).length + 3  := by
  show (Xp.var _).eval ρ = _; rw [h.var (by omega)]; simp only [globs, List.getD_cons_succ, List.getD_cons_zero]
lemma GlobOK.eP : gP.eval ρ = 2 ^ ℓ := by
  show (Xp.var _).eval ρ = _; rw [h.var (by omega)]; simp only [globs, List.getD_cons_succ, List.getD_cons_zero]

end GlobEval

lemma bnd_glob {k b : ℕ} (hk : k < 14) (hb : 14 ≤ b) : (Xp.var k).Bnd b :=
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
        SchCtx M x s ℓ H b ρ (T e) e (Iv M x s ℓ H).schemas[e] := by
  have hb : 14 ≤ b := hρ ▸ hG.le
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

/-! ## Register values of block coordinates -/

lemma regVal_toBlk {v : ℕ} (hv : v < 2 ^ ℓ) : Circuits.regVal (toBlk ℓ v) = v := by
  rw [toBlk, regVal_ofAddr]
  simp [Circuits.field, Nat.mod_eq_of_lt hv]

/-! ## The domain test -/

lemma GlobOK.of_take {ρ τ : List ℕ} {b : ℕ} (h : GlobOK M x s ℓ H ρ) (hρ : ρ.length = b)
    (ht : τ.take b = ρ) : GlobOK M x s ℓ H τ := by
  have hb := hρ ▸ h.le
  unfold GlobOK
  rw [← h, ← ht, List.take_take, Nat.min_eq_left hb]

/-- The domain violations of the schema of a schema stack (record at `b + 28 …`) at the
coordinate `(i, v)` of loops over `i ≤ s` and `v < 2^ℓ` (by `loopX`) entered at depth `d`
(stack `τ' ++ [s + 1, i, 2^ℓ, v, inBit x v, 0]`). -/
def violAt (s b d : ℕ) : Gn :=
  violGen s (d + 6) (var (d + 1)) (var (d + 3)) (var (d + 4)) (var (b + 33)) (var (b + 34))
    (var (b + 35)) (var (b + 36)) gℓ gH

lemma violAt_nil_iff {ρ τ τ' : List ℕ} {b d e : ℕ}
    {sc : Schema (s + 1) ℓ (Iv M x s ℓ H).numLocations}
    (hG : GlobOK M x s ℓ H ρ) (hρ : ρ.length = b) (hctx : SchCtx M x s ℓ H b ρ τ e sc)
    (hτ' : τ'.take (b + 37) = τ) (hd : τ'.length = d) (hbd : b + 37 ≤ d) (hℓ : 0 < ℓ)
    {i v : ℕ} (hi : i < s + 1) (hv : v < 2 ^ ℓ) :
    (violAt s b d).out x (τ' ++ [s + 1, i, 2 ^ ℓ, v, inBit x v, 0]) = [] ↔
      ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ) ∈ sc.domain := by
  have hb := hρ ▸ hG.le
  have hGτ : GlobOK M x s ℓ H τ := hG.of_take hρ hctx.2.1
  have hGτ' : GlobOK M x s ℓ H τ' := hGτ.of_take hctx.1 hτ'
  have hGσ := hGτ'.append [s + 1, i, 2 ^ ℓ, v, inBit x v, 0]
  subst hd
  refine violGen_nil_iff_mem (τ := τ) hctx.1 hctx.2.2.2 (by simp) ?_ (by omega) ?_ _ ?_ ?_ ?_
    hGσ.eℓ hGσ.eH hℓ
  · rw [List.take_append_of_le_length hbd, hτ']
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨show _ < _ by simp, show _ < _ by simp, show _ < _ by simp,
      bnd_glob (by omega) (by simp; omega), bnd_glob (by omega) (by simp; omega)⟩
  · simp
  · simp [regVal_toBlk hv]
  · simp [regVal_toBlk hv]

/-! ## The shift of a permutation described by a mask -/

/-- `field m k ℓ`. -/
def fieldmX (mX kX : Xp) : Xp := xorM (shr mX kX) (const 0) gℓ

/-- `xorFields ℓ k m`. -/
def xfX (mX : Xp) : ℕ → Xp
  | 0 => const 0
  | k + 1 => xorM (xfX mX k) (fieldmX mX (mulC k gℓ)) gℓ

/-- `shiftVal s ℓ m i`. -/
def shiftX (s : ℕ) (mX iX : Xp) : Xp :=
  add (mul (fieldmX mX (mul iX gℓ)) (lt iX (const s))) (mul (xfX mX s) (Xp.not (lt iX (const s))))

lemma field_lt' (m k ℓ : ℕ) : field m k ℓ < 2 ^ ℓ := Nat.mod_lt _ (by positivity)

lemma xorFields_lt (m : ℕ) : ∀ k, xorFields ℓ k m < 2 ^ ℓ
  | 0 => by simp [xorFields]
  | k + 1 => Nat.xor_lt_two_pow (xorFields_lt m k) (field_lt' _ _ _)

section Eval

variable {σ : List ℕ} (hG : GlobOK M x s ℓ H σ)
include hG

lemma eval_fieldmX (mX kX : Xp) : (fieldmX mX kX).eval σ = field (mX.eval σ) (kX.eval σ) ℓ := by
  simp [fieldmX, hG.eℓ, field]

lemma eval_xfX (mX : Xp) : ∀ k, (xfX mX k).eval σ = xorFields ℓ k (mX.eval σ)
  | 0 => rfl
  | k + 1 => by
    simp only [xfX, eval_xorM, eval_xfX mX k, eval_fieldmX hG, eval_mulC, hG.eℓ, xorFields]
    exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (xorFields_lt _ _) (field_lt' _ _ _))

lemma eval_shiftX (mX iX : Xp) :
    (shiftX s mX iX).eval σ = shiftVal s ℓ (mX.eval σ) (iX.eval σ) := by
  simp only [shiftX, eval_add, eval_mul, eval_fieldmX hG, eval_xfX hG, eval_lt_eq, eval_const,
    eval_not, hG.eℓ, shiftVal]
  by_cases h : iX.eval σ < s <;> simp [h, Nat.mul_comm]

end Eval

end Lax119563Proofs.Reduction
