import Lax119563Proofs.Reduction.HProg
import Lax119563Proofs.Reduction.HRoutines
import Lax119563Proofs.Reduction.HHeads

/-!
# Compiling register programs to stack programs and machines

Stack layout for `R` registers (`R + 7` stacks over `Fin 2`):
* `0`: the unread input `x[pos..]` (the input tape; its head is at `pos`),
* `1`: the read input `x[..pos]`, reversed,
* `2`: the output `encodeNats out`, reversed,
* `3, …, 6`: empty helpers,
* `7 + r`: register `r` (binary digits, least significant on top).

`compileH_runs`: every run of `HProg` is simulated within the same cost.
`HProg.computesWithin`: the machine `p.machine` runs `p`, then moves the output to tape `0`;
if `p` ends with the cursor at `0` and emitted the numbers `out` with
`|x| ≤ |encodeNats out|`, then the machine computes `encodeNats out` from `x`.
-/

open Function Lax119563.BinaryEncodings Lax119563.DeterministicTime

namespace Lax119563Proofs.Reduction

open Hierarchy Hierarchy.Prog Prog

variable {R : ℕ}

/-! ## Layout -/

/-- The input stack. -/
def sIo : Fin (R + 7) := ⟨0, by omega⟩
/-- The read input. -/
def sXl : Fin (R + 7) := ⟨1, by omega⟩
/-- The output. -/
def sOut : Fin (R + 7) := ⟨2, by omega⟩
/-- Helpers. -/
def sT0 : Fin (R + 7) := ⟨3, by omega⟩
/-- Helpers. -/
def sT1 : Fin (R + 7) := ⟨4, by omega⟩
/-- Helpers. -/
def sT2 : Fin (R + 7) := ⟨5, by omega⟩
/-- Helpers. -/
def sT3 : Fin (R + 7) := ⟨6, by omega⟩
/-- Registers. -/
def sReg (r : Fin R) : Fin (R + 7) := ⟨r.val + 7, by omega⟩

/-- The stacks representing a state. -/
def enc (x : List Bool) (st : HSt R) : Stacks (R + 7) 0 := fun i =>
  if h : 7 ≤ i.val then nst (st.env ⟨i.val - 7, by omega⟩)
  else if i.val = 0 then bs (x.drop st.pos)
  else if i.val = 1 then (bs (x.take st.pos)).reverse
  else if i.val = 2 then (bs (encodeNats st.out)).reverse
  else []

section Layout

variable (x : List Bool) (st : HSt R)

@[simp] lemma enc_reg (r : Fin R) : enc x st (sReg r) = nst (st.env r) := by
  simp [enc, sReg]
@[simp] lemma enc_io : enc x st sIo = bs (x.drop st.pos) := by simp [enc, sIo]
@[simp] lemma enc_xl : enc x st sXl = (bs (x.take st.pos)).reverse := by simp [enc, sXl]
@[simp] lemma enc_out : enc x st sOut = (bs (encodeNats st.out)).reverse := by simp [enc, sOut]
@[simp] lemma enc_t0 : enc x st sT0 = [] := by simp [enc, sT0]
@[simp] lemma enc_t1 : enc x st sT1 = [] := by simp [enc, sT1]
@[simp] lemma enc_t2 : enc x st sT2 = [] := by simp [enc, sT2]
@[simp] lemma enc_t3 : enc x st sT3 = [] := by simp [enc, sT3]

end Layout

/-- Proves distinctness of layout indices. -/
macro "dist" : tactic =>
  `(tactic| (simp only [ne_eq, Fin.ext_iff, sIo, sXl, sOut, sT0, sT1, sT2, sT3, sReg] at *; omega))

lemma sReg_ne {r s : Fin R} (h : r ≠ s) : sReg r ≠ sReg s := by
  intro e; apply h; ext; simp [sReg, Fin.ext_iff] at e; omega

lemma enc_set (x : List Bool) (st : HSt R) (r : Fin R) (v : ℕ) :
    update (enc x st) (sReg r) (nst v) = enc x (st.set r v) := by
  funext i
  by_cases hi : i = sReg r
  · subst hi; simp
  · rw [update_of_ne hi]
    unfold enc
    split_ifs with h7
    · congr 1
      simp only [HSt.set_env]
      rw [update_of_ne]
      intro e; apply hi; ext; simp [sReg, ← e]; omega
    all_goals rfl

lemma enc_emit (x : List Bool) (st : HSt R) (v : ℕ) :
    update (enc x st) sOut ((bs (encodeNat v)).reverse ++ enc x st sOut) =
      enc x { st with out := st.out ++ [v] } := by
  funext i
  by_cases hi : i = sOut
  · subst hi
    simp [encodeNats, bs_append]
  · rw [update_of_ne hi]
    unfold enc
    have : i.val ≠ 2 := fun e => hi (Fin.ext e)
    simp [this]

lemma enc_advance (x : List Bool) (st : HSt R) (hp : st.pos ≤ x.length) :
    update (update (enc x st) sIo (bs (x.drop st.pos).tail)) sXl
        (bs ((x.drop st.pos).take 1) ++ enc x st sXl) =
      enc x { st with pos := min (st.pos + 1) x.length } := by
  have h1 : (x.drop st.pos).tail = x.drop (min (st.pos + 1) x.length) := by
    rw [List.tail_drop]
    rcases Nat.lt_or_ge st.pos x.length with h | h
    · rw [min_eq_left (by omega)]
    · rw [min_eq_right (by omega), List.drop_eq_nil_of_le (by omega),
        List.drop_eq_nil_of_le (by omega)]
  have h2 : (bs (x.take (min (st.pos + 1) x.length))).reverse =
      bs ((x.drop st.pos).take 1) ++ (bs (x.take st.pos)).reverse := by
    rcases Nat.lt_or_ge st.pos x.length with h | h
    · rw [min_eq_left (by omega), List.take_add, bs_append, List.reverse_append]
      congr 1
      have : ((x.drop st.pos).take 1).length ≤ 1 := by simp
      rcases hl : (x.drop st.pos).take 1 with _ | ⟨a, _ | ⟨b, l⟩⟩
      · rfl
      · rfl
      · rw [hl] at this; simp at this
    · have e : st.pos = x.length := by omega
      rw [min_eq_right (by omega), e]
      simp
  have hxi : (sXl : Fin (R + 7)) ≠ sIo := by dist
  funext i
  by_cases ha : i = sXl
  · subst ha; rw [update_self]; simp [h2]
  · rw [update_of_ne ha]
    by_cases hb : i = sIo
    · subst hb; rw [update_self]; simp [h1]
    · rw [update_of_ne hb]
      have h0 : i.val ≠ 0 := fun e => hb (Fin.ext e)
      have h1' : i.val ≠ 1 := fun e => ha (Fin.ext e)
      unfold enc
      simp [h0, h1']

lemma enc_rst (x : List Bool) (st : HSt R) :
    update (update (enc x st) sXl []) sIo ((enc x st sXl).reverse ++ enc x st sIo) =
      enc x { st with pos := 0 } := by
  have hxi : (sXl : Fin (R + 7)) ≠ sIo := by dist
  funext i
  by_cases hb : i = sIo
  · subst hb; rw [update_self]; simp [← bs_append]
  · rw [update_of_ne hb]
    by_cases ha : i = sXl
    · subst ha; rw [update_self]; simp
    · rw [update_of_ne ha]
      have h0 : i.val ≠ 0 := fun e => hb (Fin.ext e)
      have h1' : i.val ≠ 1 := fun e => ha (Fin.ext e)
      unfold enc
      simp [h0, h1']

lemma inBit_eq (x : List Bool) (pos : ℕ) : inBit x pos = rdVal (x.drop pos) := rfl

/-! ## Compilation -/

/-- The stack program of a register program. -/
def compileH : HProg R → Hierarchy.Prog (R + 7) 0
  | .clr r => clear (sReg r)
  | .one r => hOne (sReg r)
  | .dbl r => hDbl (sReg r)
  | .half r => hHalf (sReg r)
  | .copy r s => hCopy (sReg r) (sReg s) sT0
  | .add r s => hAdd (sReg r) (sReg s) sT0 sT1 sT2
  | .lt f a b => hLt (sReg f) (sReg a) (sReg b) sT0 sT1 sT2 sT3
  | .emit r => hEmit (sReg r) sOut sT0 sT1
  | .rd r => hRd (sReg r) sXl sIo
  | .rst => moveAll sXl sIo
  | .seq p q => .seq (compileH p) (compileH q)
  | .ite c p q => .ite (fun t => c fun r => (t (sReg r)).map (· == 1)) (compileH p) (compileH q)
  | .loop c p => .loop (fun t => c fun r => (t (sReg r)).map (· == 1)) (compileH p)

lemma tops_enc (x : List Bool) (st : HSt R) :
    (fun r => (tops (enc x st) (sReg r)).map (· == 1)) = st.view := by
  funext r
  simp only [tops, enc_reg, HSt.view]
  exact head_nst _

/-! ### Avoiding the input stack -/

section Avoid

variable {K : ℕ}

lemma avoids_clear {i j : Fin K} (h : j ≠ i) : Avoids i (clear j : Hierarchy.Prog K 0) := h

lemma avoids_pushTopOf {i a b : Fin K} (h : b ≠ i) :
    ∀ as : List Sym, Avoids i (pushTopOf a b as : Hierarchy.Prog K 0)
  | [] => trivial
  | _ :: as => ⟨h, avoids_pushTopOf h as⟩

lemma avoids_moveOne {i a b : Fin K} (ha : a ≠ i) (hb : b ≠ i) :
    Avoids i (moveOne a b : Hierarchy.Prog K 0) := ⟨avoids_pushTopOf hb _, ha⟩

lemma avoids_moveAll {i a b : Fin K} (ha : a ≠ i) (hb : b ≠ i) :
    Avoids i (moveAll a b : Hierarchy.Prog K 0) := avoids_moveOne ha hb

lemma avoids_dupAll {i a b c : Fin K} (ha : a ≠ i) (hb : b ≠ i) (hc : c ≠ i) :
    Avoids i (dupAll a b c : Hierarchy.Prog K 0) :=
  ⟨avoids_pushTopOf hb _, avoids_pushTopOf hc _, ha⟩

lemma avoids_copyE {i a b c : Fin K} (ha : a ≠ i) (hb : b ≠ i) (hc : c ≠ i) :
    Avoids i (copyE a b c : Hierarchy.Prog K 0) :=
  ⟨avoids_moveAll ha hc, avoids_dupAll hc ha hb⟩

lemma avoids_bit1 {i j : Fin K} {f : Bool → Hierarchy.Prog K 0} (h : ∀ a, Avoids i (f a)) :
    Avoids i (bit1 j f) := ⟨h true, h false⟩

lemma avoids_bit2 {i j k : Fin K} {f : Bool → Bool → Hierarchy.Prog K 0}
    (h : ∀ a b, Avoids i (f a b)) : Avoids i (bit2 j k f) :=
  avoids_bit1 fun a => avoids_bit1 fun b => h a b

lemma avoids_bit3 {i j k l : Fin K} {f : Bool → Bool → Bool → Hierarchy.Prog K 0}
    (h : ∀ a b c, Avoids i (f a b c)) : Avoids i (bit3 j k l f) :=
  avoids_bit1 fun a => avoids_bit1 fun b => avoids_bit1 fun c => h a b c

end Avoid

/-- Primitive instructions not touching the input. -/
def HProg.isArith : HProg R → Bool
  | .clr _ | .one _ | .dbl _ | .half _ | .copy .. | .add .. | .lt .. | .emit _ => true
  | _ => false

lemma avoids_compile_prim (p : HProg R) (hp : p.isArith = true) :
    Avoids sIo (compileH p) := by
  have hr : ∀ r : Fin R, sReg r ≠ sIo := fun r => by dist
  have h0 : (sT0 : Fin (R + 7)) ≠ sIo := by dist
  have h1 : (sT1 : Fin (R + 7)) ≠ sIo := by dist
  have h2 : (sT2 : Fin (R + 7)) ≠ sIo := by dist
  have h3 : (sT3 : Fin (R + 7)) ≠ sIo := by dist
  have ho : (sOut : Fin (R + 7)) ≠ sIo := by dist
  cases p with
  | clr r => exact avoids_clear (hr r)
  | one r => exact hr r
  | dbl r => exact ⟨hr r, trivial⟩
  | half r => exact hr r
  | copy r s => exact ⟨avoids_clear (hr s), avoids_moveAll (hr r) h0, avoids_dupAll h0 (hr r) (hr s)⟩
  | add r s =>
    refine ⟨avoids_copyE (hr s) h1 h0, avoids_bit3 (j := sReg r) (k := sT1) (l := sT2)
      fun a b c => ?_, avoids_moveAll h0 (hr r)⟩
    refine ⟨hr r, h1, h2, h0, ?_⟩
    split_ifs
    · exact h2
    · trivial
  | lt f a b =>
    refine ⟨avoids_copyE (hr a) h1 h0, avoids_copyE (hr b) h2 h0,
      avoids_bit2 (j := sT1) (k := sT2) fun u v => ?_,
      avoids_clear (hr f), ⟨hr f, trivial⟩, h3⟩
    refine ⟨h1, h2, ?_⟩
    split_ifs <;> first | trivial | exact ⟨h3, h3⟩
  | emit r =>
    exact ⟨avoids_copyE (hr r) h1 h0, avoids_bit1 (j := sT1)
      (f := fun d => .seq (.pop sT1) (.seq (.push sOut 1) (.push sOut (sym d))))
      fun d => ⟨h1, ho, ho⟩, ho⟩
  | _ => simp [HProg.isArith] at hp

/-! ### Simulation -/

lemma unitCost_ge {w a : ℕ} (h : a ≤ 52 * w + 12) : a ≤ unitCost w := by
  unfold unitCost; omega

/-- **Simulation.** A run of `p` is a run of the compiled stack program within the same cost;
the head of the input tape follows the cursor. -/
theorem compileH_runs {x : List Bool} {w : ℕ} {p : HProg R} {st st' : HSt R} {t : ℕ}
    (h : HRuns x w p st st' t) (hpos : st.pos ≤ x.length) (hd : Fin (R + 7) → ℤ)
    (hhd : hd sIo = (st.pos : ℤ)) :
    ∃ hd' : Fin (R + 7) → ℤ, hd' sIo = (st'.pos : ℤ) ∧ RunsLeH (compileH p) (enc x st, hd) (enc x st', hd') t := by
  induction h generalizing hd with
  | @clr r st hv =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (clear_nst (sReg r) (enc_reg x st r))
      (avoids_compile_prim (.clr r) rfl) hd
    refine ⟨hd', by simp [e, hhd], h'.of_eq (by rw [enc_set]) ?_⟩
    have := length_nst_le hv
    exact unitCost_ge (by omega)
  | @one r st hv =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hOne_runs (sReg r) (enc_reg x st r))
      (avoids_compile_prim (.one r) rfl) hd
    exact ⟨hd', by simp [e, hhd], h'.of_eq (by rw [enc_set]) (unitCost_ge (by omega))⟩
  | @dbl r st hv =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hDbl_runs (sReg r) (enc_reg x st r))
      (avoids_compile_prim (.dbl r) rfl) hd
    exact ⟨hd', by simp [e, hhd], h'.of_eq (by rw [enc_set]) (unitCost_ge (by omega))⟩
  | @half r st hv =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hHalf_runs (sReg r) (enc_reg x st r))
      (avoids_compile_prim (.half r) rfl) hd
    exact ⟨hd', by simp [e, hhd], h'.of_eq (by rw [enc_set]) (unitCost_ge (by omega))⟩
  | @copy r s st hrs hr hs =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hCopy_runs (sReg_ne hrs) (by dist) (by dist)
      (enc_reg x st r) (enc_t0 x st)) (avoids_compile_prim (.copy r s) rfl) hd
    refine ⟨hd', by simp [e, hhd], h'.of_eq (by rw [enc_set]) ?_⟩
    have := length_nst_le hr
    have := length_nst_le hs
    simp only [enc_reg]
    exact unitCost_ge (by omega)
  | @add r s st hrs hv =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hAdd_runs (sReg_ne hrs) (by dist) (by dist) (by dist)
      (by dist) (by dist) (by dist) (by dist) (by dist) (by dist) (enc_reg x st r)
      (enc_reg x st s) (enc_t0 x st) (enc_t1 x st) (enc_t2 x st))
      (avoids_compile_prim (.add r s) rfl) hd
    refine ⟨hd', by simp [e, hhd], h'.of_eq (by rw [enc_set]) ?_⟩
    have := length_nst_le (show st.env s < 2 ^ w by omega)
    have := length_nst_le hv
    exact unitCost_ge (by omega)
  | @lt f a b st hfa hfb hab hf ha hb =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hLt_runs (sReg_ne hfa) (sReg_ne hfb) (by dist) (by dist)
      (by dist) (by dist) (sReg_ne hab) (by dist) (by dist) (by dist) (by dist) (by dist)
      (by dist) (by dist) (by dist) (by dist) (by dist) (by dist) (by dist) (by dist) (by dist)
      (enc_reg x st a) (enc_reg x st b) (enc_t0 x st) (enc_t1 x st) (enc_t2 x st)
      (enc_t3 x st)) (avoids_compile_prim (.lt f a b) rfl) hd
    refine ⟨hd', by simp [e, hhd], h'.of_eq (by rw [enc_set]) ?_⟩
    have := length_nst_le hf
    have := length_nst_le ha
    have := length_nst_le hb
    simp only [enc_reg]
    exact unitCost_ge (by omega)
  | @emit r st hv =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hEmit_runs (by dist) (by dist) (by dist) (by dist)
      (by dist) (by dist) (enc_reg x st r) (enc_t0 x st) (enc_t1 x st))
      (avoids_compile_prim (.emit r) rfl) hd
    refine ⟨hd', by simp [e, hhd], h'.of_eq (by rw [enc_emit]) ?_⟩
    have := length_nst_le hv
    exact unitCost_ge (by omega)
  | @rd r st hv hp =>
    have hA := hRdA_runs (r := sReg r) (xr := sIo) (by dist) (s := enc x st) (enc_io x st)
    rw [enc_set, ← inBit_eq] at hA
    obtain ⟨h₁, e₁, r₁⟩ := RunsLe.toH hA
      (show Avoids sIo (hRdA (sReg r) sIo : Hierarchy.Prog (R + 7) 0) from
        ⟨avoids_clear (by dist), ⟨(show sReg r ≠ sIo by dist), (show sReg r ≠ sIo by dist)⟩,
          (show sReg r ≠ sIo by dist), trivial⟩) hd
    have hio := enc_io x (st.set r (inBit x st.pos))
    simp only [HSt.set_pos] at hio
    have hlen := length_nst_le hv
    rcases hl : x.drop st.pos with _ | ⟨a, l⟩
    · have hpx : st.pos = x.length := by
        have := List.drop_eq_nil_iff.mp hl; omega
      have r₂ : RunsLeH (hRdB sXl sIo) (enc x (st.set r (inBit x st.pos)), h₁)
          (enc x (st.set r (inBit x st.pos)), h₁) 2 :=
        RunsLeH.iteF (by simp [tops, hio, hl]) ⟨1, le_rfl, .skip⟩
      refine ⟨h₁, by simp [e₁, hhd]; omega, (r₁.seq r₂).of_eq ?_ ?_⟩
      · congr 2
        ext <;> simp; omega
      · simp only [enc_reg]; exact unitCost_ge (by omega)
    · have r₂ := moveOne_runsH (show (sIo : Fin (R + 7)) ≠ sXl by dist) (m := 0)
        (s := enc x (st.set r (inBit x st.pos))) (hd := h₁) (a := sym a) (l := bs l)
        (by rw [hio, hl]; rfl)
      have r₂' := r₂.iteT (c := fun t => (t sIo).isSome) (q := skip) (by simp [tops, hio, hl])
      have hlt : st.pos < x.length := by
        by_contra hc; rw [List.drop_eq_nil_of_le (by omega)] at hl; cases hl
      refine ⟨update (update h₁ sIo (h₁ sIo + 1)) sXl (h₁ sXl - 1), ?_,
        (r₁.seq r₂').of_eq ?_ ?_⟩
      · rw [update_of_ne (show (sIo : Fin (R + 7)) ≠ sXl by dist), update_self, e₁, hhd]
        simp; omega
      · refine Prod.ext ?_ rfl
        have e := enc_advance x (st.set r (inBit x st.pos)) (by simpa using hp)
        simp only [HSt.set_pos, hl, List.tail_cons, List.take_succ_cons, List.take_zero,
          bs_cons, bs_nil, List.singleton_append] at e
        exact e
      · simp only [enc_reg]; exact unitCost_ge (by omega)
  | @rst st hp =>
    have h' := moveAll_runsH (show (sXl : Fin (R + 7)) ≠ sIo by dist) (m := 0)
      (enc x st sXl) (enc x st) hd rfl
    refine ⟨_, ?_, h'.of_eq (by rw [enc_rst]) ?_⟩
    · simp [hhd]; omega
    · simp only [enc_xl, List.length_reverse, length_bs, List.length_take, unitCost]
      have : min st.pos x.length = st.pos := by omega
      rw [this]; nlinarith
  | seq hr₁ _ ih₁ ih₂ =>
    obtain ⟨h₁, e₁, r₁⟩ := ih₁ hpos hd hhd
    obtain ⟨h₂, e₂, r₂⟩ := ih₂ (hr₁.pos_le hpos) h₁ e₁
    exact ⟨h₂, e₂, r₁.seq r₂⟩
  | iteT hc _ ih =>
    obtain ⟨h₁, e₁, r₁⟩ := ih hpos hd hhd
    exact ⟨h₁, e₁, r₁.iteT (by simp only [tops_enc]; exact hc)⟩
  | iteF hc _ ih =>
    obtain ⟨h₁, e₁, r₁⟩ := ih hpos hd hhd
    exact ⟨h₁, e₁, r₁.iteF (by simp only [tops_enc]; exact hc)⟩
  | loopF hc => exact ⟨hd, hhd, RunsLeH.loopF (by simp only [tops_enc]; exact hc)⟩
  | loopT hc hr₁ _ ih₁ ih₂ =>
    obtain ⟨h₁, e₁, r₁⟩ := ih₁ hpos hd hhd
    obtain ⟨h₂, e₂, r₂⟩ := ih₂ (hr₁.pos_le hpos) h₁ e₁
    exact ⟨h₂, e₂, RunsLeH.loopT (by simp only [tops_enc]; exact hc) r₁ r₂⟩

end Lax119563Proofs.Reduction
