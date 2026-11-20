import Lax119563Proofs.Reduction.PkSch
import Lax119563Proofs.Reduction.PassBase

/-!
# Infrastructure of the packed system generator

The generator of `PkSys` runs on `19` globals (levels `0 … 18`):
`|y|, n, h, s, Λ, log₂(n + 1), ⌈(h + 2)/s⌉, ℓ, H, R, N, r, Ec, p0, acc, E, W, det, 2^ℓ`
where `y` is the (preprocessed) input and `Λ ≥ (s + 1) ℓ` bounds the bit positions
`i ℓ + t` in an address. `GlobP` records the values read by the body.

* `schEnum_ctxP`: the schema enumerator `schEnumP` as a loop over schema indices;
* `violGenP`: the domain test `violGen` with the number `s` of data blocks and the
  bit position `i ℓ` of block `i` given by expressions (`violGenP_nil_iff_mem`);
* `xorFields_testBit`: the bits of the checksum shift as parities.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs

/-! ## Globals -/

abbrev qS : Xp := var 3
abbrev qΛ : Xp := var 4
abbrev qℓ : Xp := var 7
abbrev qH : Xp := var 8
abbrev qR : Xp := var 9
abbrev qN : Xp := var 10
abbrev qr : Xp := var 11
abbrev qEc : Xp := var 12
abbrev qp0 : Xp := var 13
abbrev qacc : Xp := var 14
abbrev qE : Xp := var 15
abbrev qW : Xp := var 16
abbrev qdet : Xp := var 17
abbrev qP : Xp := var 18

/-- The globals read by the body of the packed generator. -/
structure GlobP (M : Machine) (x : List Bool) (s ℓ H : ℕ) (ρ : List ℕ) : Prop where
  len : 19 ≤ ρ.length
  eS : ρ.getD 3 0 = s
  eΛ : (s + 1) * ℓ ≤ ρ.getD 4 0
  eℓ : ρ.getD 7 0 = ℓ
  eH : ρ.getD 8 0 = H
  eR : ρ.getD 9 0 = radix M H
  eN : ρ.getD 10 0 = numLoc M H
  er : ρ.getD 11 0 = (verifierCmds' M x s ℓ H).length
  eEc : ρ.getD 12 0 = ((verifierCmds' M x s ℓ H).map cmdSz).sum
  ep0 : ρ.getD 13 0 = (Loc.code (Loc.query : Loc M H)).val
  eacc : ρ.getD 14 0 = (Loc.code (Loc.accept : Loc M H)).val
  eE : ρ.getD 15 0 = (Iv M x s ℓ H).schemas.length
  eW : ρ.getD 16 0 = (Iv M x s ℓ H).numLocations
  edet : ρ.getD 17 0 = numLoc M H + 8 * (verifierCmds' M x s ℓ H).length + 3
  eP : ρ.getD 18 0 = 2 ^ ℓ

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

namespace GlobP

lemma of_prefix {ρ ρ' : List ℕ} (h : GlobP M x s ℓ H ρ) (hl : ρ.length ≤ ρ'.length)
    (hg : ∀ i < 19, ρ'.getD i 0 = ρ.getD i 0) : GlobP M x s ℓ H ρ' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨by omega, by rw [hg 3 (by omega)]; exact h1, by rw [hg 4 (by omega)]; exact h2,
    by rw [hg 7 (by omega)]; exact h3, by rw [hg 8 (by omega)]; exact h4,
    by rw [hg 9 (by omega)]; exact h5, by rw [hg 10 (by omega)]; exact h6,
    by rw [hg 11 (by omega)]; exact h7, by rw [hg 12 (by omega)]; exact h8,
    by rw [hg 13 (by omega)]; exact h9, by rw [hg 14 (by omega)]; exact h10,
    by rw [hg 15 (by omega)]; exact h11, by rw [hg 16 (by omega)]; exact h12,
    by rw [hg 17 (by omega)]; exact h13, by rw [hg 18 (by omega)]; exact h14⟩

lemma append {ρ : List ℕ} (h : GlobP M x s ℓ H ρ) (l : List ℕ) : GlobP M x s ℓ H (ρ ++ l) :=
  h.of_prefix (by simp) fun i hi => List.getD_append _ _ _ _ (by have := h.len; omega)

lemma of_take {ρ τ : List ℕ} {b : ℕ} (h : GlobP M x s ℓ H ρ) (hρ : ρ.length = b)
    (ht : τ.take b = ρ) : GlobP M x s ℓ H τ := by
  have hb := hρ ▸ h.len
  have hlen : ρ.length ≤ τ.length := by
    have := congrArg List.length ht; simp at this; omega
  refine h.of_prefix hlen fun i hi => ?_
  rw [← ht, getD_take' (by omega)]

variable {ρ : List ℕ} (h : GlobP M x s ℓ H ρ)
include h

lemma vS : qS.eval ρ = s := h.eS
lemma vℓ : qℓ.eval ρ = ℓ := h.eℓ
lemma vH : qH.eval ρ = H := h.eH
lemma vR : qR.eval ρ = radix M H := h.eR
lemma vN : qN.eval ρ = numLoc M H := h.eN
lemma vr : qr.eval ρ = (verifierCmds' M x s ℓ H).length := h.er
lemma vEc : qEc.eval ρ = ((verifierCmds' M x s ℓ H).map cmdSz).sum := h.eEc
lemma vp0 : qp0.eval ρ = (Loc.code (Loc.query : Loc M H)).val := h.ep0
lemma vacc : qacc.eval ρ = (Loc.code (Loc.accept : Loc M H)).val := h.eacc
lemma vE : qE.eval ρ = (Iv M x s ℓ H).schemas.length := h.eE
lemma vW : qW.eval ρ = (Iv M x s ℓ H).numLocations := h.eW
lemma vdet : qdet.eval ρ = numLoc M H + 8 * (verifierCmds' M x s ℓ H).length + 3 := h.edet
lemma vP : qP.eval ρ = 2 ^ ℓ := h.eP

end GlobP

lemma bnd_globP {k b : ℕ} (hk : k < 19) (hb : 19 ≤ b) : (Xp.var k).Bnd b :=
  show k < b by omega

/-! ## The schema enumerator as a loop over schema indices -/

/-- **The schema enumerator**, indexed by schemas. -/
theorem schEnum_ctxP {ρ : List ℕ} {b : ℕ} (hρ : ρ.length = b) (hG : GlobP M x s ℓ H ρ)
    (hs : 1 ≤ s) :
    ∃ T : ℕ → List ℕ, (∀ (body : Gn) (y : List Bool),
        (schEnumP M b qS qH qR qN qr qp0 qEc body).out y ρ =
          (List.range (Iv M x s ℓ H).schemas.length).flatMap fun e => body.out y (T e)) ∧
      ∀ e (he : e < (Iv M x s ℓ H).schemas.length),
        SchCtx M x s ℓ H b ρ (T e) e (Iv M x s ℓ H).schemas[e] := by
  have hb : 19 ≤ b := hρ ▸ hG.len
  have hS := fun (body : Gn) (y : List Bool) => out_schEnumP (M := M) (s := s) (x := x)
    (y := y) (ℓ := ℓ) (H := H) hρ (bnd_globP (by omega) hb) (bnd_globP (by omega) hb) hG.vH
    hG.vR (bnd_globP (by omega) hb) hG.vN (bnd_globP (by omega) hb) hG.vr
    (bnd_globP (by omega) hb) hG.vp0 (bnd_globP (by omega) hb) hG.vEc
    (bnd_globP (by omega) hb) hG.vS hs body
  obtain ⟨hF, hidx, -⟩ := hS Gn.skip []
  have hlen := hF.length_eq
  refine ⟨fun e => (schStksP M s b qH qR qN qr qp0 qEc x ρ ℓ H).getD e [], fun body y => ?_,
    fun e he => ?_⟩
  · rw [(hS body y).2.2, flatMap_eq_range _ [], ← hlen]
    rfl
  · have he' : e < (schStksP M s b qH qR qN qr qp0 qEc x ρ ℓ H).length := by
      rw [← hlen]; exact he
    have hrel := forall₂_getD [] hF e he
    exact ⟨hrel.1, hrel.2.1, getD_of_map_eq_range _ [] hidx he', hrel.2.2⟩

/-! ## The domain test -/

/-- **The domain violations** (at depth `d`), with the number of data blocks `sX` and the
bit position `iℓX` of block `iX`. -/
def violGenP (d : ℕ) (sX iX iℓX vX xbX gkX g1X g2X g3X ℓX HX : Xp) : Gn :=
  Gn.when (Xp.not (eq iX sX))
    (.ite (eq gkX (const 0))
      (.loop g2X (Gn.when (fieldBadX iℓX g1X (var (d + 1)) vX g3X ℓX) (.emit (const 0))))
      (.ite (eq gkX (const 1))
        (Gn.when (Xp.not (or (and (eq iX (const 0)) (eq (initCVX g1X vX xbX) g2X))
            (and (Xp.not (eq iX (const 0))) (eq vX (fieldX iℓX ℓX HX)))))
          (.emit (const 0)))
        (.ite (eq gkX (const 2))
          (Gn.when (Xp.not (or (Xp.not (eq iX g1X)) (Xp.not (eq vX (fieldX iℓX ℓX HX)))))
            (.emit (const 0)))
          (Gn.when (Xp.not (eq vX (const 0))) (.emit (const 0))))))

theorem violGenP_out_eq_nil_iff {y : List Bool} {τ : List ℕ} {d : ℕ}
    {sX iX iℓX vX xbX gkX g1X g2X g3X ℓX HX : Xp} (hτ : τ.length = d)
    (hb : ∀ e ∈ [iX, iℓX, vX, xbX, gkX, g1X, g2X, g3X, ℓX, HX], e.Bnd d)
    {i v gk g1 g2 g3 : ℕ} (hsX : sX.eval τ = s) (hi : iX.eval τ = i)
    (hiℓ : iℓX.eval τ = i * ℓ) (hv : vX.eval τ = v)
    (hxb : xbX.eval τ = inBit x v) (hgk : gkX.eval τ = gk) (hg1 : g1X.eval τ = g1)
    (hg2 : g2X.eval τ = g2) (hg3 : g3X.eval τ = g3) (hℓX : ℓX.eval τ = ℓ) (hHX : HX.eval τ = H)
    (hℓ : 0 < ℓ) :
    (violGenP d sX iX iℓX vX xbX gkX g1X g2X g3X ℓX HX).out y τ = [] ↔
      (i = s ∨ gEval x ℓ H [gk, g1, g2, g3] i v = true) := by
  have hfx : (fieldX iℓX ℓX HX).eval τ = field (2 ^ H) (i * ℓ) ℓ := by
    rw [eval_fieldX, hiℓ, hℓX, hHX]
  have hB : ∀ e ∈ [iX, iℓX, vX, xbX, gkX, g1X, g2X, g3X, ℓX, HX], e.Bnd d := hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hB
  obtain ⟨bi, biℓ, bv, -, -, bg1, -, bg3, bℓ, -⟩ := hB
  have hns : (Xp.not (eq iX sX)).eval τ = if ¬ i = s then 1 else 0 :=
    Xp.eval_not' (by rw [Xp.eval_eq, hi, hsX])
  have e0 : (eq gkX (const 0)).eval τ = if gk = 0 then 1 else 0 := by
    rw [Xp.eval_eq, hgk, Xp.eval_const]
  have e1 : (eq gkX (const 1)).eval τ = if gk = 1 then 1 else 0 := by
    rw [Xp.eval_eq, hgk, Xp.eval_const]
  have e2 : (eq gkX (const 2)).eval τ = if gk = 2 then 1 else 0 := by
    rw [Xp.eval_eq, hgk, Xp.eval_const]
  have hbad : ∀ t, (fieldBadX iℓX g1X (var (d + 1)) vX g3X ℓX).eval (τ ++ [g2, t]) =
      if (i * ℓ ≤ g1 + t ∧ g1 + t < i * ℓ + ℓ) ∧
        ¬ v * 2 ^ (i * ℓ) / 2 ^ (g1 + t) % 2 = g3 / 2 ^ t % 2 then 1 else 0 := by
    intro t
    have hev : ∀ e : Xp, e.Bnd d → e.eval (τ ++ [g2, t]) = e.eval τ :=
      fun e he => Xp.eval_append hτ _ he
    have ht' : (var (d + 1)).eval (τ ++ [g2, t]) = t := by
      simp only [Xp.eval_var]
      rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hτ]
    have hm : iℓX.eval (τ ++ [g2, t]) = i * ℓ := by rw [hev _ biℓ, hiℓ]
    have hk : (add g1X (var (d + 1))).eval (τ ++ [g2, t]) = g1 + t := by
      rw [Xp.eval_add, hev _ bg1, ht', hg1]
    refine Xp.eval_and' (Xp.eval_and' ?_ ?_) (Xp.eval_not' ?_)
    · rw [Xp.eval_le, hm, hk]
    · rw [Xp.eval_lt_eq, hk, Xp.eval_add, hm, hev _ bℓ, hℓX]
    · rw [Xp.eval_eq]
      simp only [Xp.eval_odd, Xp.eval_shr, Xp.eval_shl, hm, hk, ht', hev _ bv, hev _ bg3, hv, hg3]
  have hhit : (Xp.not (or (and (eq iX (const 0)) (eq (initCVX g1X vX xbX) g2X))
      (and (Xp.not (eq iX (const 0))) (eq vX (fieldX iℓX ℓX HX))))).eval τ =
      if ¬ ((i = 0 ∧ initCV x g1 v = g2) ∨ (¬ i = 0 ∧ v = field (2 ^ H) (i * ℓ) ℓ)) then 1
        else 0 :=
    Xp.eval_not' (Xp.eval_or' (Xp.eval_and' (by rw [Xp.eval_eq, hi, Xp.eval_const])
        (by rw [Xp.eval_eq, eval_initCVX hg1 hv hxb, hg2]))
      (Xp.eval_and' (Xp.eval_not' (by rw [Xp.eval_eq, hi, Xp.eval_const]))
        (by rw [Xp.eval_eq, hv, hfx])))
  have hmiss : (Xp.not (or (Xp.not (eq iX g1X)) (Xp.not (eq vX (fieldX iℓX ℓX HX))))).eval τ =
      if ¬ (¬ i = g1 ∨ ¬ v = field (2 ^ H) (i * ℓ) ℓ) then 1 else 0 :=
    Xp.eval_not' (Xp.eval_or' (Xp.eval_not' (by rw [Xp.eval_eq, hi, hg1]))
      (Xp.eval_not' (by rw [Xp.eval_eq, hv, hfx])))
  have hz : (Xp.not (eq vX (const 0))).eval τ = if ¬ v = 0 then 1 else 0 :=
    Xp.eval_not' (by rw [Xp.eval_eq, hv, Xp.eval_const])
  simp only [violGenP, Gn.out_when, Gn.out, hns, e0, e1, e2, hhit, hmiss, hz, hg2, hbad]
  by_cases his : i = s
  · simp [his]
  · rcases (show gk = 0 ∨ gk = 1 ∨ gk = 2 ∨ 3 ≤ gk by omega) with h0 | h1 | h2 | h3
    · subst h0
      simp only [his, gEval, List.getD_cons_zero, List.getD_cons_succ, fieldOK_iff hℓ]
      simp only [not_false_eq_true, if_true, ne_eq, one_ne_zero, false_or,
        List.flatMap_eq_nil_iff, List.mem_range, ite_eq_right_iff, reduceCtorEq, imp_false,
        Decidable.not_not, if_false]
      refine forall_congr' fun t => imp_congr_right fun _ => ?_
      rw [and_assoc]
    · subst h1
      have c0 : (if ¬i = s then 1 else 0) ≠ 0 := by simp [his]
      rw [if_pos c0, if_neg (by simp), if_pos (by simp)]
      have : gEval x ℓ H [1, g1, g2, g3] i v = (if i = 0 then decide (initCV x g1 v = g2)
          else decide (v = field (2 ^ H) (i * ℓ) ℓ)) := rfl
      rw [this]
      generalize field (2 ^ H) (i * ℓ) ℓ = F
      generalize initCV x g1 v = C
      by_cases hi0 : i = 0 <;> by_cases hc : C = g2 <;> by_cases hF : v = F <;>
        simp [his, hi0, hc, hF] <;> omega
    · subst h2
      have c0 : (if ¬i = s then 1 else 0) ≠ 0 := by simp [his]
      rw [if_pos c0, if_neg (by simp), if_neg (by simp), if_pos (by simp)]
      have : gEval x ℓ H [2, g1, g2, g3] i v =
          (if i = g1 then decide (v ≠ field (2 ^ H) (i * ℓ) ℓ) else true) := rfl
      rw [this]
      generalize field (2 ^ H) (i * ℓ) ℓ = F
      by_cases hig : i = g1 <;> by_cases hF : v = F <;> simp [his, hig, hF] <;> omega
    · have : gEval x ℓ H [gk, g1, g2, g3] i v = decide (v = 0) := by
        unfold gEval
        simp only [List.getD_cons_zero]
        rcases gk with _ | _ | _ | gk
        · omega
        · omega
        · omega
        · rfl
      rw [this]
      have g0 : gk ≠ 0 := by omega
      have g1' : gk ≠ 1 := by omega
      have g2' : gk ≠ 2 := by omega
      by_cases hv0 : v = 0 <;> simp [his, hv0, g0, g1', g2']

/-- **The domain test on a schema stack** (as `violGen_nil_iff_mem`). -/
theorem violGenP_nil_iff_mem {y : List Bool} {N b d : ℕ}
    {sc : Schema (s + 1) ℓ N} {τ σ : List ℕ}
    (hτ : τ.length = b + 37) (hrec : SchRec M x s ℓ H sc (τ.drop (b + 28)))
    (hσ : σ.length = d) (hστ : σ.take (b + 37) = τ) (hd : b + 37 ≤ d)
    {sX iX iℓX vX xbX ℓX HX : Xp} (hb : ∀ e ∈ [iX, iℓX, vX, xbX, ℓX, HX], e.Bnd d)
    (c : Coord (s + 1) ℓ) (hsX : sX.eval σ = s)
    (hi : iX.eval σ = c.1.val) (hiℓ : iℓX.eval σ = c.1.val * ℓ) (hv : vX.eval σ = regVal c.2)
    (hxb : xbX.eval σ = inBit x (regVal c.2)) (hℓX : ℓX.eval σ = ℓ) (hHX : HX.eval σ = H)
    (hℓ : 0 < ℓ) :
    (violGenP d sX iX iℓX vX xbX (var (b + 33)) (var (b + 34)) (var (b + 35)) (var (b + 36))
      ℓX HX).out y σ = [] ↔ c ∈ sc.domain := by
  have hg : ∀ k < 4, (var (b + 33 + k)).eval σ = ((τ.drop (b + 28)).drop 5).getD k 0 := by
    intro k hk
    rw [getD_drop', getD_drop', Xp.eval_var, ← hστ, getD_take' (by omega)]
    congr 1; omega
  have hl : ((τ.drop (b + 28)).drop 5).length = 4 := by simp [hτ]
  have h4 := eq_of_length_four hl
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  rw [violGenP_out_eq_nil_iff hσ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, show b + 33 < d by omega,
        show b + 34 < d by omega, show b + 35 < d by omega, show b + 36 < d by omega,
        hb.2.2.2.2.1, hb.2.2.2.2.2⟩)
    hsX hi hiℓ hv hxb (hg 0 (by omega)) (hg 1 (by omega)) (hg 2 (by omega)) (hg 3 (by omega))
    hℓX hHX hℓ, mem_domain_of_schRec hrec, ← h4]

/-! ## The checksum shift bit by bit -/

/-- The number of blocks `i < k` whose field has bit `t` set. -/
def cntBits (ℓ m t : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => cntBits ℓ m t k + (if m.testBit (k * ℓ + t) then 1 else 0)

lemma xorFields_testBit (m : ℕ) {t : ℕ} (ht : t < ℓ) :
    ∀ k, (xorFields ℓ k m).testBit t = decide (cntBits ℓ m t k % 2 = 1)
  | 0 => by simp [xorFields, cntBits]
  | k + 1 => by
    rw [xorFields, Nat.testBit_xor, xorFields_testBit m ht k, testBit_field, cntBits]
    simp only [ht, decide_true, Bool.true_and, Nat.add_comm t]
    by_cases hb : m.testBit (k * ℓ + t) <;> simp [hb, Nat.add_mod] <;>
      rcases Nat.mod_two_eq_zero_or_one (cntBits ℓ m t k) with h | h <;> simp [h]

lemma cntBits_eq (ℓ m t : ℕ) : ∀ k, cntBits ℓ m t k =
    ((List.range k).flatMap fun i => if m.testBit (i * ℓ + t) then [0] else []).length
  | 0 => rfl
  | k + 1 => by
    rw [cntBits, cntBits_eq ℓ m t k, List.range_succ, List.flatMap_append, List.length_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    split_ifs <;> simp

end Lax119563Proofs.Reduction
