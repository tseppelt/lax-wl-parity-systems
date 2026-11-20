import Lax119563Proofs.Compiler.NProg
import Lax119563Proofs.Compiler.NumStack
import Lax119563Proofs.Reduction.HCompile

/-!
# Compiling register programs with number stacks to stack programs

Copy-generalised from `Reduction.HCompile` (which is left unchanged). Stack layout for `R`
registers and `Q` number stacks (`R + Q + 7` stacks over `Fin 2`):
* `0`: the unread input `x[pos..]`, `1`: the read input reversed, `2`: the output reversed,
* `3, …, 6`: empty helpers, `7 + r`: register `r` (`nst`),
* `7 + R + q`: number stack `q`, holding `bs (encodeNats (st.stk q))`.

`compileN_runs`: every run of `NProg` is simulated within the same cost.
-/

open Function Lax119563.BinaryEncodings Lax119563.DeterministicTime

namespace Lax119563Proofs.Compiler

open Hierarchy Hierarchy.Prog Lax119563Proofs.Reduction Lax119563Proofs.Reduction.Prog

variable {R Q : ℕ}

/-! ## Layout -/

/-- The unread input. -/
def nIo : Fin (R + Q + 7) := ⟨0, by omega⟩
/-- The read input. -/
def nXl : Fin (R + Q + 7) := ⟨1, by omega⟩
/-- The output. -/
def nOut : Fin (R + Q + 7) := ⟨2, by omega⟩
/-- Helpers. -/
def nT0 : Fin (R + Q + 7) := ⟨3, by omega⟩
/-- Helpers. -/
def nT1 : Fin (R + Q + 7) := ⟨4, by omega⟩
/-- Helpers. -/
def nT2 : Fin (R + Q + 7) := ⟨5, by omega⟩
/-- Helpers. -/
def nT3 : Fin (R + Q + 7) := ⟨6, by omega⟩
/-- Registers. -/
def nReg (r : Fin R) : Fin (R + Q + 7) := ⟨r.val + 7, by omega⟩
/-- Number stacks. -/
def nStk (q : Fin Q) : Fin (R + Q + 7) := ⟨q.val + 7 + R, by omega⟩

/-- The stacks representing a state. -/
def encN (x : List Bool) (st : NSt R Q) : Stacks (R + Q + 7) 0 := fun i =>
  if h : 7 + R ≤ i.val then bs (encodeNats (st.stk ⟨i.val - 7 - R, by omega⟩))
  else if h' : 7 ≤ i.val then nst (st.env ⟨i.val - 7, by omega⟩)
  else if i.val = 0 then bs (x.drop st.pos)
  else if i.val = 1 then (bs (x.take st.pos)).reverse
  else if i.val = 2 then (bs (encodeNats st.out)).reverse
  else []

/-- Closes goals about the layout of `encN`. -/
macro "layout_tac" : tactic =>
  `(tactic| (unfold encN; split_ifs <;>
    first | rfl | omega | (congr 2; ext; (try simp only [Fin.val_mk]); omega) |
      (congr 3; ext; (try simp only [Fin.val_mk]); omega)))

section Layout

variable (x : List Bool) (st : NSt R Q)

@[simp] lemma encN_reg (r : Fin R) : encN x st (nReg r) = nst (st.env r) := by
  have e : ((nReg r : Fin (R + Q + 7)) : ℕ) = r.val + 7 := rfl
  have := r.isLt
  layout_tac
@[simp] lemma encN_stk (q : Fin Q) : encN x st (nStk q) = bs (encodeNats (st.stk q)) := by
  have e : ((nStk q : Fin (R + Q + 7)) : ℕ) = q.val + 7 + R := rfl
  layout_tac
@[simp] lemma encN_io : encN x st nIo = bs (x.drop st.pos) := by
  have e : ((nIo : Fin (R + Q + 7)) : ℕ) = 0 := rfl
  layout_tac
@[simp] lemma encN_xl : encN x st nXl = (bs (x.take st.pos)).reverse := by
  have e : ((nXl : Fin (R + Q + 7)) : ℕ) = 1 := rfl
  layout_tac
@[simp] lemma encN_out : encN x st nOut = (bs (encodeNats st.out)).reverse := by
  have e : ((nOut : Fin (R + Q + 7)) : ℕ) = 2 := rfl
  layout_tac
@[simp] lemma encN_t0 : encN x st nT0 = [] := by
  have e : ((nT0 : Fin (R + Q + 7)) : ℕ) = 3 := rfl
  layout_tac
@[simp] lemma encN_t1 : encN x st nT1 = [] := by
  have e : ((nT1 : Fin (R + Q + 7)) : ℕ) = 4 := rfl
  layout_tac
@[simp] lemma encN_t2 : encN x st nT2 = [] := by
  have e : ((nT2 : Fin (R + Q + 7)) : ℕ) = 5 := rfl
  layout_tac
@[simp] lemma encN_t3 : encN x st nT3 = [] := by
  have e : ((nT3 : Fin (R + Q + 7)) : ℕ) = 6 := rfl
  layout_tac

end Layout

/-- Proves distinctness of layout indices. -/
macro "ndist" : tactic =>
  `(tactic| (simp only [ne_eq, Fin.ext_iff, nIo, nXl, nOut, nT0, nT1, nT2, nT3, nReg, nStk] at *; omega))

lemma nReg_ne {r s : Fin R} (h : r ≠ s) : (nReg r : Fin (R + Q + 7)) ≠ nReg s := by
  intro e; apply h; ext; simp [nReg, Fin.ext_iff] at e; omega

lemma encN_set (x : List Bool) (st : NSt R Q) (r : Fin R) (v : ℕ) :
    update (encN x st) (nReg r) (nst v) = encN x (st.set r v) := by
  funext i
  by_cases hi : i = nReg r
  · subst hi; simp
  · rw [update_of_ne hi]
    unfold encN
    split_ifs with h7R h7
    · rfl
    · congr 1
      simp only [NSt.set_env]
      rw [update_of_ne]
      intro e; apply hi; ext; simp [nReg, ← e]; omega
    all_goals rfl

lemma encN_setS (x : List Bool) (st : NSt R Q) (q : Fin Q) (l : List ℕ) :
    update (encN x st) (nStk q) (bs (encodeNats l)) = encN x (st.setS q l) := by
  funext i
  by_cases hi : i = nStk q
  · subst hi; simp
  · rw [update_of_ne hi]
    unfold encN
    split_ifs with h7R h7
    · congr 2
      simp only [NSt.setS_stk]
      rw [update_of_ne]
      intro e; apply hi; ext; simp [nStk, ← e]; omega
    all_goals rfl

lemma encN_emit (x : List Bool) (st : NSt R Q) (v : ℕ) :
    update (encN x st) nOut ((bs (encodeNat v)).reverse ++ encN x st nOut) =
      encN x { st with out := st.out ++ [v] } := by
  funext i
  by_cases hi : i = nOut
  · subst hi
    simp [encodeNats, bs_append]
  · rw [update_of_ne hi]
    unfold encN
    have : i.val ≠ 2 := fun e => hi (Fin.ext e)
    simp [this]

lemma encN_advance (x : List Bool) (st : NSt R Q) (hp : st.pos ≤ x.length) :
    update (update (encN x st) nIo (bs (x.drop st.pos).tail)) nXl
        (bs ((x.drop st.pos).take 1) ++ encN x st nXl) =
      encN x { st with pos := min (st.pos + 1) x.length } := by
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
  have hxi : (nXl : Fin (R + Q + 7)) ≠ nIo := by ndist
  funext i
  by_cases ha : i = nXl
  · subst ha; rw [update_self]; simp [h2]
  · rw [update_of_ne ha]
    by_cases hb : i = nIo
    · subst hb; rw [update_self]; simp [h1]
    · rw [update_of_ne hb]
      have h0 : i.val ≠ 0 := fun e => hb (Fin.ext e)
      have h1' : i.val ≠ 1 := fun e => ha (Fin.ext e)
      unfold encN
      simp [h0, h1']

lemma encN_rst (x : List Bool) (st : NSt R Q) :
    update (update (encN x st) nXl []) nIo ((encN x st nXl).reverse ++ encN x st nIo) =
      encN x { st with pos := 0 } := by
  have hxi : (nXl : Fin (R + Q + 7)) ≠ nIo := by ndist
  funext i
  by_cases hb : i = nIo
  · subst hb; rw [update_self]; simp [← bs_append]
  · rw [update_of_ne hb]
    by_cases ha : i = nXl
    · subst ha; rw [update_self]; simp
    · rw [update_of_ne ha]
      have h0 : i.val ≠ 0 := fun e => hb (Fin.ext e)
      have h1' : i.val ≠ 1 := fun e => ha (Fin.ext e)
      unfold encN
      simp [h0, h1']

lemma inBit_eqN (x : List Bool) (pos : ℕ) : inBit x pos = rdVal (x.drop pos) := rfl

/-! ## Compilation -/

/-- The stack program of a register program. -/
def compileN : NProg R Q → Hierarchy.Prog (R + Q + 7) 0
  | .clr r => clear (nReg r)
  | .one r => hOne (nReg r)
  | .dbl r => hDbl (nReg r)
  | .half r => hHalf (nReg r)
  | .copy r s => hCopy (nReg r) (nReg s) nT0
  | .add r s => hAdd (nReg r) (nReg s) nT0 nT1 nT2
  | .lt f a b => hLt (nReg f) (nReg a) (nReg b) nT0 nT1 nT2 nT3
  | .emit r => hEmit (nReg r) nOut nT0 nT1
  | .rd r => hRd (nReg r) nXl nIo
  | .rst => moveAll nXl nIo
  | .spush q r => nsPush (nReg r) (nStk q) nT0
  | .spop q r => nsPop (nStk q) (nReg r) nT0
  | .seq p q => .seq (compileN p) (compileN q)
  | .ite c p q => .ite (fun t => c (fun r => (t (nReg r)).map (· == 1),
      fun q => (t (nStk q)).isSome)) (compileN p) (compileN q)
  | .loop c p => .loop (fun t => c (fun r => (t (nReg r)).map (· == 1),
      fun q => (t (nStk q)).isSome)) (compileN p)

lemma encodeNats_cons (v : ℕ) (l : List ℕ) :
    encodeNats (v :: l) = encodeNat v ++ encodeNats l := by simp [encodeNats]

lemma topsN_enc (x : List Bool) (st : NSt R Q) :
    ((fun r => (tops (encN x st) (nReg r)).map (· == 1)),
      (fun q => (tops (encN x st) (nStk q)).isSome)) = st.view := by
  refine Prod.ext ?_ ?_
  · funext r
    simp only [tops, encN_reg, NSt.view]
    exact head_nst _
  · funext q
    simp only [tops, encN_stk, NSt.view]
    cases h : st.stk q with
    | nil => simp [encodeNats]
    | cons v l => simp [encodeNats_cons, encodeNat, bs_append]

/-! ### Avoiding the input stack -/

section Avoid

variable {K : ℕ}

lemma avoids_clearN {i j : Fin K} (h : j ≠ i) : Avoids i (clear j : Hierarchy.Prog K 0) := h

lemma avoids_pushTopOfN {i a b : Fin K} (h : b ≠ i) :
    ∀ as : List Sym, Avoids i (pushTopOf a b as : Hierarchy.Prog K 0)
  | [] => trivial
  | _ :: as => ⟨h, avoids_pushTopOfN h as⟩

lemma avoids_moveOneN {i a b : Fin K} (ha : a ≠ i) (hb : b ≠ i) :
    Avoids i (moveOne a b : Hierarchy.Prog K 0) := ⟨avoids_pushTopOfN hb _, ha⟩

lemma avoids_moveAllN {i a b : Fin K} (ha : a ≠ i) (hb : b ≠ i) :
    Avoids i (moveAll a b : Hierarchy.Prog K 0) := avoids_moveOneN ha hb

lemma avoids_dupAllN {i a b c : Fin K} (ha : a ≠ i) (hb : b ≠ i) (hc : c ≠ i) :
    Avoids i (dupAll a b c : Hierarchy.Prog K 0) :=
  ⟨avoids_pushTopOfN hb _, avoids_pushTopOfN hc _, ha⟩

lemma avoids_copyEN {i a b c : Fin K} (ha : a ≠ i) (hb : b ≠ i) (hc : c ≠ i) :
    Avoids i (copyE a b c : Hierarchy.Prog K 0) :=
  ⟨avoids_moveAllN ha hc, avoids_dupAllN hc ha hb⟩

lemma avoids_bit1N {i j : Fin K} {f : Bool → Hierarchy.Prog K 0} (h : ∀ a, Avoids i (f a)) :
    Avoids i (bit1 j f) := ⟨h true, h false⟩

lemma avoids_bit2N {i j k : Fin K} {f : Bool → Bool → Hierarchy.Prog K 0}
    (h : ∀ a b, Avoids i (f a b)) : Avoids i (bit2 j k f) :=
  avoids_bit1N fun a => avoids_bit1N fun b => h a b

lemma avoids_bit3N {i j k l : Fin K} {f : Bool → Bool → Bool → Hierarchy.Prog K 0}
    (h : ∀ a b c, Avoids i (f a b c)) : Avoids i (bit3 j k l f) :=
  avoids_bit1N fun a => avoids_bit1N fun b => avoids_bit1N fun c => h a b c

end Avoid

/-- Primitive instructions not touching the input. -/
def NProg.isArith : NProg R Q → Bool
  | .clr _ | .one _ | .dbl _ | .half _ | .copy .. | .add .. | .lt .. | .emit _ => true
  | _ => false

lemma avoids_compile_primN (p : NProg R Q) (hp : p.isArith = true) :
    Avoids nIo (compileN p) := by
  have hr : ∀ r : Fin R, (nReg r : Fin (R + Q + 7)) ≠ nIo := fun r => by ndist
  have h0 : (nT0 : Fin (R + Q + 7)) ≠ nIo := by ndist
  have h1 : (nT1 : Fin (R + Q + 7)) ≠ nIo := by ndist
  have h2 : (nT2 : Fin (R + Q + 7)) ≠ nIo := by ndist
  have h3 : (nT3 : Fin (R + Q + 7)) ≠ nIo := by ndist
  have ho : (nOut : Fin (R + Q + 7)) ≠ nIo := by ndist
  cases p with
  | clr r => exact avoids_clearN (hr r)
  | one r => exact hr r
  | dbl r => exact ⟨hr r, trivial⟩
  | half r => exact hr r
  | copy r s => exact ⟨avoids_clearN (hr s), avoids_moveAllN (hr r) h0, avoids_dupAllN h0 (hr r) (hr s)⟩
  | add r s =>
    refine ⟨avoids_copyEN (hr s) h1 h0, avoids_bit3N (j := nReg r) (k := nT1) (l := nT2)
      fun a b c => ?_, avoids_moveAllN h0 (hr r)⟩
    refine ⟨hr r, h1, h2, h0, ?_⟩
    split_ifs
    · exact h2
    · trivial
  | lt f a b =>
    refine ⟨avoids_copyEN (hr a) h1 h0, avoids_copyEN (hr b) h2 h0,
      avoids_bit2N (j := nT1) (k := nT2) fun u v => ?_,
      avoids_clearN (hr f), ⟨hr f, trivial⟩, h3⟩
    refine ⟨h1, h2, ?_⟩
    split_ifs <;> first | trivial | exact ⟨h3, h3⟩
  | emit r =>
    exact ⟨avoids_copyEN (hr r) h1 h0, avoids_bit1N (j := nT1)
      (f := fun d => .seq (.pop nT1) (.seq (.push nOut 1) (.push nOut (sym d))))
      fun d => ⟨h1, ho, ho⟩, ho⟩
  | _ => simp [NProg.isArith] at hp

/-! ### Simulation -/

lemma unitCost_geN {w a : ℕ} (h : a ≤ 52 * w + 12) : a ≤ unitCost w := by
  unfold unitCost; omega

/-- **Simulation.** A run of `p` is a run of the compiled stack program within the same cost;
the head of the input tape follows the cursor. -/
theorem compileN_runs {x : List Bool} {w : ℕ} {p : NProg R Q} {st st' : NSt R Q} {t : ℕ}
    (h : NRuns x w p st st' t) (hpos : st.pos ≤ x.length) (hd : Fin (R + Q + 7) → ℤ)
    (hhd : hd nIo = (st.pos : ℤ)) :
    ∃ hd' : Fin (R + Q + 7) → ℤ, hd' nIo = (st'.pos : ℤ) ∧ RunsLeH (compileN p) (encN x st, hd) (encN x st', hd') t := by
  induction h generalizing hd with
  | @clr r st hv =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (clear_nst (nReg r) (encN_reg x st r))
      (avoids_compile_primN (.clr r) rfl) hd
    refine ⟨hd', by simp [e, hhd], h'.of_eq (by rw [encN_set]) ?_⟩
    have := length_nst_le hv
    exact unitCost_geN (by omega)
  | @one r st hv =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hOne_runs (nReg r) (encN_reg x st r))
      (avoids_compile_primN (.one r) rfl) hd
    exact ⟨hd', by simp [e, hhd], h'.of_eq (by rw [encN_set]) (unitCost_geN (by omega))⟩
  | @dbl r st hv =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hDbl_runs (nReg r) (encN_reg x st r))
      (avoids_compile_primN (.dbl r) rfl) hd
    exact ⟨hd', by simp [e, hhd], h'.of_eq (by rw [encN_set]) (unitCost_geN (by omega))⟩
  | @half r st hv =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hHalf_runs (nReg r) (encN_reg x st r))
      (avoids_compile_primN (.half r) rfl) hd
    exact ⟨hd', by simp [e, hhd], h'.of_eq (by rw [encN_set]) (unitCost_geN (by omega))⟩
  | @copy r s st hrs hr hs =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hCopy_runs (nReg_ne hrs) (by ndist) (by ndist)
      (encN_reg x st r) (encN_t0 x st)) (avoids_compile_primN (.copy r s) rfl) hd
    refine ⟨hd', by simp [e, hhd], h'.of_eq (by rw [encN_set]) ?_⟩
    have := length_nst_le hr
    have := length_nst_le hs
    simp only [encN_reg]
    exact unitCost_geN (by omega)
  | @add r s st hrs hv =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hAdd_runs (nReg_ne hrs) (by ndist) (by ndist) (by ndist)
      (by ndist) (by ndist) (by ndist) (by ndist) (by ndist) (by ndist) (encN_reg x st r)
      (encN_reg x st s) (encN_t0 x st) (encN_t1 x st) (encN_t2 x st))
      (avoids_compile_primN (.add r s) rfl) hd
    refine ⟨hd', by simp [e, hhd], h'.of_eq (by rw [encN_set]) ?_⟩
    have := length_nst_le (show st.env s < 2 ^ w by omega)
    have := length_nst_le hv
    exact unitCost_geN (by omega)
  | @lt f a b st hfa hfb hab hf ha hb =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hLt_runs (nReg_ne hfa) (nReg_ne hfb) (by ndist) (by ndist)
      (by ndist) (by ndist) (nReg_ne hab) (by ndist) (by ndist) (by ndist) (by ndist) (by ndist)
      (by ndist) (by ndist) (by ndist) (by ndist) (by ndist) (by ndist) (by ndist) (by ndist) (by ndist)
      (encN_reg x st a) (encN_reg x st b) (encN_t0 x st) (encN_t1 x st) (encN_t2 x st)
      (encN_t3 x st)) (avoids_compile_primN (.lt f a b) rfl) hd
    refine ⟨hd', by simp [e, hhd], h'.of_eq (by rw [encN_set]) ?_⟩
    have := length_nst_le hf
    have := length_nst_le ha
    have := length_nst_le hb
    simp only [encN_reg]
    exact unitCost_geN (by omega)
  | @emit r st hv =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hEmit_runs (by ndist) (by ndist) (by ndist) (by ndist)
      (by ndist) (by ndist) (encN_reg x st r) (encN_t0 x st) (encN_t1 x st))
      (avoids_compile_primN (.emit r) rfl) hd
    refine ⟨hd', by simp [e, hhd], h'.of_eq (by rw [encN_emit]) ?_⟩
    have := length_nst_le hv
    exact unitCost_geN (by omega)
  | @rd r st hv hp =>
    have hA := hRdA_runs (r := nReg r) (xr := nIo) (by ndist) (s := encN x st) (encN_io x st)
    rw [encN_set, ← inBit_eqN] at hA
    obtain ⟨h₁, e₁, r₁⟩ := RunsLe.toH hA
      (show Avoids nIo (hRdA (nReg r) nIo : Hierarchy.Prog (R + Q + 7) 0) from
        ⟨avoids_clearN (by ndist), ⟨(show nReg r ≠ nIo by ndist), (show nReg r ≠ nIo by ndist)⟩,
          (show nReg r ≠ nIo by ndist), trivial⟩) hd
    have hio := encN_io x (st.set r (inBit x st.pos))
    simp only [NSt.set_pos] at hio
    have hlen := length_nst_le hv
    rcases hl : x.drop st.pos with _ | ⟨a, l⟩
    · have hpx : st.pos = x.length := by
        have := List.drop_eq_nil_iff.mp hl; omega
      have r₂ : RunsLeH (hRdB nXl nIo) (encN x (st.set r (inBit x st.pos)), h₁)
          (encN x (st.set r (inBit x st.pos)), h₁) 2 :=
        RunsLeH.iteF (by simp [tops, hio, hl]) ⟨1, le_rfl, .skip⟩
      refine ⟨h₁, by simp [e₁, hhd]; omega, (r₁.seq r₂).of_eq ?_ ?_⟩
      · congr 2
        ext <;> simp; omega
      · simp only [encN_reg]; exact unitCost_geN (by omega)
    · have r₂ := moveOne_runsH (show (nIo : Fin (R + Q + 7)) ≠ nXl by ndist) (m := 0)
        (s := encN x (st.set r (inBit x st.pos))) (hd := h₁) (a := sym a) (l := bs l)
        (by rw [hio, hl]; rfl)
      have r₂' := r₂.iteT (c := fun t => (t nIo).isSome) (q := skip) (by simp [tops, hio, hl])
      have hlt : st.pos < x.length := by
        by_contra hc; rw [List.drop_eq_nil_of_le (by omega)] at hl; cases hl
      refine ⟨update (update h₁ nIo (h₁ nIo + 1)) nXl (h₁ nXl - 1), ?_,
        (r₁.seq r₂').of_eq ?_ ?_⟩
      · rw [update_of_ne (show (nIo : Fin (R + Q + 7)) ≠ nXl by ndist), update_self, e₁, hhd]
        simp; omega
      · refine Prod.ext ?_ rfl
        have e := encN_advance x (st.set r (inBit x st.pos)) (by simpa using hp)
        simp only [NSt.set_pos, hl, List.tail_cons, List.take_succ_cons, List.take_zero,
          bs_cons, bs_nil, List.singleton_append] at e
        exact e
      · simp only [encN_reg]; exact unitCost_geN (by omega)
  | @rst st hp =>
    have h' := moveAll_runsH (show (nXl : Fin (R + Q + 7)) ≠ nIo by ndist) (m := 0)
      (encN x st nXl) (encN x st) hd rfl
    refine ⟨_, ?_, h'.of_eq (by rw [encN_rst]) ?_⟩
    · simp [hhd]; omega
    · simp only [encN_xl, List.length_reverse, length_bs, List.length_take, unitCost]
      have : min st.pos x.length = st.pos := by omega
      rw [this]; nlinarith
  | @spush q r st hv =>
    have hio : ∀ q : Fin Q, (nStk q : Fin (R + Q + 7)) ≠ nIo := fun q => by ndist
    have hr : nReg r ≠ (nIo : Fin (R + Q + 7)) := by ndist
    have h0 : (nT0 : Fin (R + Q + 7)) ≠ nIo := by ndist
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (nsPush_runs (q := nStk q) (by ndist) (by ndist) (by ndist)
      (encN_reg x st r) (encN_t0 x st))
      (⟨avoids_moveAllN hr h0, hio q, ⟨h0, hr, hio q, hio q⟩, ⟨h0, hr, hio q, hio q⟩⟩) hd
    refine ⟨hd', by simp [e, hhd], h'.of_eq ?_ ?_⟩
    · rw [encN_stk, ← bs_append, ← encodeNats_cons, encN_setS]
    · have := length_nst_le hv
      simp only [nst, length_bs] at this
      exact unitCost_geN (by omega)
  | @spop q r st v vs hv hq hvw =>
    have hio : ∀ q : Fin Q, (nStk q : Fin (R + Q + 7)) ≠ nIo := fun q => by ndist
    have hr : nReg r ≠ (nIo : Fin (R + Q + 7)) := by ndist
    have h0 : (nT0 : Fin (R + Q + 7)) ≠ nIo := by ndist
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (nsPop_runs (q := nStk q) (r := nReg r) (by ndist)
      (by ndist) (by ndist) (v := v) (L := bs (encodeNats vs))
      (by rw [encN_stk, hq, encodeNats_cons, bs_append]) (encN_t0 x st))
      (⟨avoids_clearN hr, ⟨hio q, ⟨hio q, h0⟩, ⟨hio q, h0⟩⟩, hio q, avoids_moveAllN h0 hr⟩) hd
    refine ⟨hd', by simp [e, hhd], h'.of_eq ?_ ?_⟩
    · rw [encN_setS]
      have := encN_set x (st.setS q vs) r v
      simpa using this
    · have h1 := length_nst_le hv
      have h2 := length_nst_le hvw
      simp only [nst, length_bs] at h1 h2
      simp only [encN_reg, nst, length_bs]
      exact unitCost_geN (by omega)
  | seq hr₁ _ ih₁ ih₂ =>
    obtain ⟨h₁, e₁, r₁⟩ := ih₁ hpos hd hhd
    obtain ⟨h₂, e₂, r₂⟩ := ih₂ (hr₁.pos_le hpos) h₁ e₁
    exact ⟨h₂, e₂, r₁.seq r₂⟩
  | iteT hc _ ih =>
    obtain ⟨h₁, e₁, r₁⟩ := ih hpos hd hhd
    exact ⟨h₁, e₁, r₁.iteT (by simp only [topsN_enc]; exact hc)⟩
  | iteF hc _ ih =>
    obtain ⟨h₁, e₁, r₁⟩ := ih hpos hd hhd
    exact ⟨h₁, e₁, r₁.iteF (by simp only [topsN_enc]; exact hc)⟩
  | loopF hc => exact ⟨hd, hhd, RunsLeH.loopF (by simp only [topsN_enc]; exact hc)⟩
  | loopT hc hr₁ _ ih₁ ih₂ =>
    obtain ⟨h₁, e₁, r₁⟩ := ih₁ hpos hd hhd
    obtain ⟨h₂, e₂, r₂⟩ := ih₂ (hr₁.pos_le hpos) h₁ e₁
    exact ⟨h₂, e₂, RunsLeH.loopT (by simp only [topsN_enc]; exact hc) r₁ r₂⟩

end Lax119563Proofs.Compiler
