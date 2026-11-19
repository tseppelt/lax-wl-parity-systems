import Lax119563Proofs.Compiler.NLe

/-!
# Structured statements with number stacks

A layer above `NProg` with a total denotational semantics, so that the programs of the
compiler are proved correct by list mathematics.

Statements `CStm R Q` over user registers `Fin R` and number stacks `Fin Q`:
`skip`, `set r e`, `emit e`, `push q e`, `pop q r` (`r :=` the top of `q`, or `0` if `q` is
empty; pop), `sne r q` (`r := [q nonempty]`), `rd r` (`r :=` the input value at the cursor,
advance), `rst`, sequencing, `ite c p q` (`c ≠ 0`) and while loops `loop c body`.

`CStm.exec x c st` is the final state; a loop runs for the least number of iterations after
which its condition is `0` (and is the identity if there is none). `CStm.cost x w c st` is a
cost bound and `CStm.Fits x w c st` says that all expression values stay below `2 ^ w` and
that all loops terminate. `CStm.code R D c : NProg (R + D + 1) Q` compiles a statement with
`D + 1` scratch registers (`CStm.code_spec`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q D : ℕ} {x : List Bool} {w : ℕ}

/-- Structured statements. -/
inductive CStm (R Q : ℕ) where
  | skip
  | set (r : Fin R) (e : Ex R)
  | emit (e : Ex R)
  | push (q : Fin Q) (e : Ex R)
  | pop (q : Fin Q) (r : Fin R)
  | sne (r : Fin R) (q : Fin Q)
  | rd (r : Fin R)
  | rst
  | seq (p q : CStm R Q)
  | ite (c : Ex R) (p q : CStm R Q)
  | loop (c : Ex R) (body : CStm R Q)

namespace CStm

open Classical in
/-- The denotation. -/
noncomputable def exec (x : List Bool) : CStm R Q → NSt R Q → NSt R Q
  | skip, st => st
  | set r e, st => st.set r (e.eval st.env)
  | emit e, st => { st with out := st.out ++ [e.eval st.env] }
  | push q e, st => st.setS q (e.eval st.env :: st.stk q)
  | pop q r, st => (st.setS q (st.stk q).tail).set r ((st.stk q).headD 0)
  | sne r q, st => st.set r (if (st.stk q).isEmpty then 0 else 1)
  | rd r, st => { (st.set r (inBit x st.pos)) with pos := min (st.pos + 1) x.length }
  | rst, st => { st with pos := 0 }
  | seq p q, st => exec x q (exec x p st)
  | ite c p q, st => if c.eval st.env ≠ 0 then exec x p st else exec x q st
  | loop c body, st =>
    if h : ∃ n, c.eval ((exec x body)^[n] st).env = 0 then (exec x body)^[Nat.find h] st else st

/-- The `n`-th iterate of a loop body. -/
noncomputable abbrev iter (x : List Bool) (body : CStm R Q) (st : NSt R Q) (n : ℕ) : NSt R Q :=
  (exec x body)^[n] st

/-- The cost of evaluating the condition of a loop or conditional. -/
def condCost (w : ℕ) (c : Ex R) : ℕ := c.size * Ex.nodeCost w + 1

open Classical in
/-- A cost bound. -/
noncomputable def cost (x : List Bool) (w : ℕ) : CStm R Q → NSt R Q → ℕ
  | skip, _ => unitCost w
  | set _ e, _ => e.size * Ex.nodeCost w + unitCost w
  | emit e, _ => e.size * Ex.nodeCost w + unitCost w
  | push _ e, _ => e.size * Ex.nodeCost w + unitCost w
  | pop _ _, _ => unitCost w + 1
  | sne _ _, _ => 2 * unitCost w + 1
  | rd _, _ => unitCost w
  | rst, st => unitCost w * (st.pos + 1)
  | seq p q, st => cost x w p st + cost x w q (exec x p st)
  | ite c p q, st => condCost w c + (if c.eval st.env ≠ 0 then cost x w p st else cost x w q st)
  | loop c body, st =>
    if h : ∃ n, c.eval ((exec x body)^[n] st).env = 0 then
      ∑ j ∈ Finset.range (Nat.find h), (cost x w body ((exec x body)^[j] st) + condCost w c) +
        condCost w c
    else 0

/-- All values stay below `2 ^ w` and all loops terminate. -/
def Fits (x : List Bool) (w : ℕ) : CStm R Q → NSt R Q → Prop
  | skip, _ => True
  | set _ e, st => e.Fits w st.env
  | emit e, st => e.Fits w st.env
  | push _ e, st => e.Fits w st.env
  | pop _ _, _ => True
  | sne _ _, _ => True
  | rd _, _ => True
  | rst, _ => True
  | seq p q, st => Fits x w p st ∧ Fits x w q (exec x p st)
  | ite c p q, st => c.Fits w st.env ∧
      (if c.eval st.env ≠ 0 then Fits x w p st else Fits x w q st)
  | loop c body, st => ∃ n, c.eval ((exec x body)^[n] st).env = 0 ∧
      (∀ j < n, c.eval ((exec x body)^[j] st).env ≠ 0 ∧ Fits x w body ((exec x body)^[j] st)) ∧
      ∀ j ≤ n, c.Fits w ((exec x body)^[j] st).env

/-- The number of scratch registers needed. -/
def depth : CStm R Q → ℕ
  | skip => 1
  | set _ e => e.depth
  | emit e => e.depth
  | push _ e => e.depth
  | pop _ _ => 1
  | sne _ _ => 1
  | rd _ => 1
  | rst => 1
  | seq p q => max (depth p) (depth q)
  | ite c p q => max c.depth (max (depth p) (depth q))
  | loop c body => max c.depth (depth body)

/-- The condition of a compiled conditional or loop: scratch register `0` is nonzero. -/
def scTest (R D : ℕ) (Q : ℕ) : NView (R + D + 1) Q → Bool := fun v => (v.1 (sc R D 0)).isSome

/-- Compilation to `NProg` with scratch registers `R, …, R + D`. -/
def code (R D : ℕ) : CStm R Q → NProg (R + D + 1) Q
  | skip => .clr (sc R D 0)
  | set r e => .seq (HProg.toN (e.code R D 0)) (.copy (sc R D 0) (ur D r))
  | emit e => .seq (HProg.toN (e.code R D 0)) (.emit (sc R D 0))
  | push q e => .seq (HProg.toN (e.code R D 0)) (.spush q (sc R D 0))
  | pop q r => .ite (fun v => v.2 q) (.spop q (ur D r)) (.clr (ur D r))
  | sne r q => .ite (fun v => v.2 q) (.seq (.clr (ur D r)) (.one (ur D r))) (.clr (ur D r))
  | rd r => .rd (ur D r)
  | rst => .rst
  | seq p q => .seq (code R D p) (code R D q)
  | ite c p q => .seq (HProg.toN (c.code R D 0)) (.ite (scTest R D Q) (code R D p) (code R D q))
  | loop c body => .seq (HProg.toN (c.code R D 0))
      (.loop (scTest R D Q) (.seq (code R D body) (HProg.toN (c.code R D 0))))

/-! ## Loops -/

open Classical in
lemma exec_loop {c : Ex R} {body : CStm R Q} {st : NSt R Q} {n : ℕ}
    (hn : c.eval (iter x body st n).env = 0) (hlt : ∀ j < n, c.eval (iter x body st j).env ≠ 0) :
    exec x (loop c body) st = iter x body st n := by
  have h : ∃ n, c.eval ((exec x body)^[n] st).env = 0 := ⟨n, hn⟩
  have e : Nat.find h = n := (Nat.find_eq_iff h).mpr ⟨hn, fun j hj => hlt j hj⟩
  simp only [exec, dif_pos h, e]

open Classical in
lemma cost_loop {c : Ex R} {body : CStm R Q} {st : NSt R Q} {n : ℕ}
    (hn : c.eval (iter x body st n).env = 0) (hlt : ∀ j < n, c.eval (iter x body st j).env ≠ 0) :
    cost x w (loop c body) st =
      ∑ j ∈ Finset.range n, (cost x w body (iter x body st j) + condCost w c) + condCost w c := by
  have h : ∃ n, c.eval ((exec x body)^[n] st).env = 0 := ⟨n, hn⟩
  have e : Nat.find h = n := (Nat.find_eq_iff h).mpr ⟨hn, fun j hj => hlt j hj⟩
  simp only [cost, dif_pos h, e]

lemma iter_succ (body : CStm R Q) (st : NSt R Q) (n : ℕ) :
    iter x body st (n + 1) = exec x body (iter x body st n) :=
  Function.iterate_succ_apply' _ _ _

lemma iter_zero (body : CStm R Q) (st : NSt R Q) : iter x body st 0 = st := rfl

end CStm

/-! ## Correspondence between compiled and source states -/

/-- The compiled state `st` represents the source state `σ`. -/
def CCorr (D : ℕ) (st : NSt (R + D + 1) Q) (σ : NSt R Q) : Prop :=
  uenv D st.toH = σ.env ∧ st.stk = σ.stk ∧ st.pos = σ.pos ∧ st.out = σ.out

lemma uenv_set_ur' (st : NSt (R + D + 1) Q) (r : Fin R) (v : ℕ) :
    uenv D (st.set (ur D r) v).toH = Function.update (uenv D st.toH) r v :=
  uenv_set_ur st.toH r v

/-- Evaluating an expression into scratch register `0`. -/
lemma ex_code_N (hw : 2 ≤ w) (e : Ex R) (st : NSt (R + D + 1) Q) (hd : e.depth ≤ D)
    (hb : st.Bdd w) (hf : e.Fits w (uenv D st.toH)) :
    ∃ st₁ : NSt (R + D + 1) Q, NLe x w (HProg.toN (e.code R D 0)) st st₁ (e.size * Ex.nodeCost w) ∧
      st₁.env (sc R D 0) = e.eval (uenv D st.toH) ∧ uenv D st₁.toH = uenv D st.toH ∧
      st₁.stk = st.stk ∧ st₁.pos = st.pos ∧ st₁.out = st.out ∧ st₁.Bdd w := by
  obtain ⟨h₁, r₁, e₁⟩ := Ex.code_spec (x := x) hw e 0 st.toH (by omega) hb.toH hf
  have r₁' := r₁.toN (Q := Q) (st := st)
  refine ⟨_, r₁', e₁, Ex.code_uenv r₁, rfl, r₁.pos_eq (Ex.code_mv e 0),
    r₁.out_eq (Ex.code_em e 0), r₁'.bounded hw hb⟩

namespace CStm

/-- **Compilation of statements.** -/
theorem code_spec (hw : 2 ≤ w) : ∀ (c : CStm R Q) (σ : NSt R Q) (st : NSt (R + D + 1) Q),
    depth c ≤ D → Fits x w c σ → CCorr D st σ → st.Bdd w → st.pos ≤ x.length →
    ∃ st', NLe x w (code R D c) st st' (cost x w c σ) ∧ CCorr D st' (exec x c σ)
  | skip, σ, st, _, _, hc, hb, _ => by
    refine ⟨_, NLe.of_runs (NRuns.clr (hb.1 _)), ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := hc
    exact ⟨(uenv_set_sc st.toH 0 0).trans h1, h2, h3, h4⟩
  | set r e, σ, st, hd, hf, hc, hb, _ => by
    obtain ⟨h1, h2, h3, h4⟩ := hc
    obtain ⟨st₁, r₁, e₁, u₁, s₁, p₁, o₁, b₁⟩ :=
      ex_code_N (x := x) hw e st (by simpa [depth] using hd) hb (by rw [h1]; exact hf)
    refine ⟨_, r₁.seq (NLe.of_runs (NRuns.copy (sc_ne_ur r 0) (b₁.1 _) (b₁.1 _))), ?_, ?_, ?_, ?_⟩
    · rw [uenv_set_ur', u₁, e₁, h1]; rfl
    · simpa [exec] using s₁.trans h2
    · simpa [exec] using p₁.trans h3
    · simpa [exec] using o₁.trans h4
  | emit e, σ, st, hd, hf, hc, hb, _ => by
    obtain ⟨h1, h2, h3, h4⟩ := hc
    obtain ⟨st₁, r₁, e₁, u₁, s₁, p₁, o₁, b₁⟩ :=
      ex_code_N (x := x) hw e st (by simpa [depth] using hd) hb (by rw [h1]; exact hf)
    refine ⟨_, r₁.seq (NLe.of_runs (NRuns.emit (b₁.1 _))), ?_, ?_, ?_, ?_⟩
    · exact u₁.trans h1
    · simpa [exec] using s₁.trans h2
    · simpa [exec] using p₁.trans h3
    · simp [exec, o₁, h4, e₁, h1]
  | push q e, σ, st, hd, hf, hc, hb, _ => by
    obtain ⟨h1, h2, h3, h4⟩ := hc
    obtain ⟨st₁, r₁, e₁, u₁, s₁, p₁, o₁, b₁⟩ :=
      ex_code_N (x := x) hw e st (by simpa [depth] using hd) hb (by rw [h1]; exact hf)
    refine ⟨_, r₁.seq (NLe.of_runs (NRuns.spush (b₁.1 _))), ?_, ?_, ?_, ?_⟩
    · exact u₁.trans h1
    · simp [exec, s₁, h2, e₁, h1]
    · simpa [exec] using p₁.trans h3
    · simpa [exec] using o₁.trans h4
  | pop q r, σ, st, _, _, hc, hb, _ => by
    obtain ⟨h1, h2, h3, h4⟩ := hc
    rcases hq : st.stk q with _ | ⟨v, vs⟩
    · have hv : (fun v : NView (R + D + 1) Q => v.2 q) st.view = false := by
        simp [NSt.view, hq]
      refine ⟨_, (NLe.iteF hv (NLe.of_runs (NRuns.clr (hb.1 _)))).mono (by simp [cost]), ?_⟩
      have hσ : σ.stk q = [] := by rw [← h2, hq]
      refine ⟨?_, ?_, h3, h4⟩
      · rw [uenv_set_ur', h1]; simp [exec, hσ]
      · simp [exec, hσ, h2]
    · have hv : (fun v : NView (R + D + 1) Q => v.2 q) st.view = true := by
        simp [NSt.view, hq]
      have hvb : v < 2 ^ w := hb.2 q v (by rw [hq]; exact List.mem_cons_self ..)
      refine ⟨_, (NLe.iteT hv (NLe.of_runs (NRuns.spop (hb.1 _) hq hvb))).mono
        (by simp [cost]), ?_⟩
      have hσ : σ.stk q = v :: vs := by rw [← h2, hq]
      refine ⟨?_, ?_, h3, h4⟩
      · show uenv D ((st.setS q vs).set (ur D r) v).toH = _
        rw [uenv_set_ur']
        show Function.update (uenv D st.toH) r v = _
        rw [h1]; simp [exec, hσ]
      · simp [exec, hσ, h2]
  | sne r q, σ, st, _, _, hc, hb, _ => by
    obtain ⟨h1, h2, h3, h4⟩ := hc
    have h2w : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
    rcases hq : st.stk q with _ | ⟨v, vs⟩
    · have hv : (fun v : NView (R + D + 1) Q => v.2 q) st.view = false := by
        simp [NSt.view, hq]
      refine ⟨_, (NLe.iteF hv (NLe.of_runs (NRuns.clr (hb.1 _)))).mono
        (by simp only [cost]; omega), ?_⟩
      have hσ : σ.stk q = [] := by rw [← h2, hq]
      refine ⟨?_, h2, h3, h4⟩
      rw [uenv_set_ur', h1]; simp [exec, hσ]
    · have hv : (fun v : NView (R + D + 1) Q => v.2 q) st.view = true := by
        simp [NSt.view, hq]
      have r₁ := NLe.of_runs (x := x) (NRuns.clr (w := w) (r := ur D r) (st := st) (hb.1 _))
      have r₂ := NLe.of_runs (x := x) (NRuns.one (w := w) (r := ur D r)
        (st := st.set (ur D r) 0) (by simp; omega))
      refine ⟨_, (NLe.iteT hv (r₁.seq r₂)).mono (by simp only [cost]; omega), ?_⟩
      have hσ : σ.stk q = v :: vs := by rw [← h2, hq]
      refine ⟨?_, h2, h3, h4⟩
      show uenv D ((st.set (ur D r) 0).set (ur D r) (2 * (st.set (ur D r) 0).env (ur D r) + 1)).toH = _
      rw [uenv_set_ur', uenv_set_ur', h1]; simp [exec, hσ]
  | rd r, σ, st, _, _, hc, hb, hp => by
    obtain ⟨h1, h2, h3, h4⟩ := hc
    refine ⟨_, NLe.of_runs (NRuns.rd (hb.1 _) hp), ?_, ?_, ?_, ?_⟩
    · show uenv D (st.set (ur D r) (inBit x st.pos)).toH = _
      rw [uenv_set_ur', h1, h3]; rfl
    · simpa [exec] using h2
    · simp [exec, h3]
    · simpa [exec] using h4
  | rst, σ, st, _, _, hc, hb, hp => by
    obtain ⟨h1, h2, h3, h4⟩ := hc
    refine ⟨_, (NLe.of_runs (NRuns.rst hp)).mono (by simp [cost, h3]), h1, h2, rfl, h4⟩
  | seq p q, σ, st, hd, hf, hc, hb, hp => by
    simp only [depth, max_le_iff] at hd
    obtain ⟨st₁, r₁, c₁⟩ := code_spec hw p σ st hd.1 hf.1 hc hb hp
    obtain ⟨st₂, r₂, c₂⟩ := code_spec hw q _ st₁ hd.2 hf.2 c₁ (r₁.bounded hw hb) (r₁.pos_le hp)
    exact ⟨st₂, r₁.seq r₂, c₂⟩
  | ite c p q, σ, st, hd, hf, hc, hb, hp => by
    simp only [depth, max_le_iff] at hd
    obtain ⟨h1, h2, h3, h4⟩ := hc
    obtain ⟨st₁, r₁, e₁, u₁, s₁, p₁, o₁, b₁⟩ :=
      ex_code_N (x := x) hw c st hd.1 hb (by rw [h1]; exact hf.1)
    have c₁ : CCorr D st₁ σ := ⟨u₁.trans h1, s₁.trans h2, p₁.trans h3, o₁.trans h4⟩
    have hp₁ : st₁.pos ≤ x.length := by rw [p₁]; exact hp
    by_cases hcv : c.eval σ.env ≠ 0
    · have hf' : Fits x w p σ := by have := hf.2; rw [if_pos hcv] at this; exact this
      obtain ⟨st₂, r₂, c₂⟩ := code_spec hw p σ st₁ hd.2.1 hf' c₁ b₁ hp₁
      have hv : scTest R D Q st₁.view = true := by
        show (st₁.toH.view (sc R D 0)).isSome = true
        rw [HSt.view_isSome_iff]; simp only [NSt.toH_env]; rw [e₁, h1]; exact hcv
      refine ⟨st₂, (r₁.seq (NLe.iteT hv r₂)).mono ?_, ?_⟩
      · simp only [cost, condCost, if_pos hcv]; omega
      · simp only [exec, if_pos hcv]; exact c₂
    · have hf' : Fits x w q σ := by have := hf.2; rw [if_neg hcv] at this; exact this
      obtain ⟨st₂, r₂, c₂⟩ := code_spec hw q σ st₁ hd.2.2 hf' c₁ b₁ hp₁
      have hv : scTest R D Q st₁.view = false := by
        show (st₁.toH.view (sc R D 0)).isSome = false
        rw [← Bool.not_eq_true, HSt.view_isSome_iff]; simp only [NSt.toH_env]
        rw [e₁, h1]; exact hcv
      refine ⟨st₂, (r₁.seq (NLe.iteF hv r₂)).mono ?_, ?_⟩
      · simp only [cost, condCost, if_neg hcv]; omega
      · simp only [exec, if_neg hcv]; exact c₂
  | loop c body, σ, st, hd, hf, hc, hb, hp => by
    simp only [depth, max_le_iff] at hd
    obtain ⟨n, hn, hlt, hcf⟩ := hf
    rw [exec_loop hn (fun j hj => (hlt j hj).1), cost_loop hn (fun j hj => (hlt j hj).1)]
    set it := iter x body σ
    set P : NProg (R + D + 1) Q := .seq (code R D body) (HProg.toN (c.code R D 0))
    -- the loop from iteration `m` on
    have aux : ∀ d m (τ : NSt (R + D + 1) Q), m + d = n → CCorr D τ (it m) → τ.Bdd w →
        τ.pos ≤ x.length → τ.env (sc R D 0) = c.eval (it m).env →
        ∃ τ', NLe x w (.loop (scTest R D Q) P) τ τ'
          (∑ j ∈ Finset.Ico m n, (cost x w body (it j) + condCost w c) + 1) ∧
          CCorr D τ' (it n) := by
      intro d
      induction d with
      | zero =>
        intro m τ hm hτ _ _ he
        have : m = n := by omega
        subst this
        refine ⟨τ, (NLe.loopF ?_).mono (by simp), hτ⟩
        show (τ.toH.view (sc R D 0)).isSome = false
        rw [← Bool.not_eq_true, HSt.view_isSome_iff]; simp only [NSt.toH_env]
        rw [he]; simpa using hn
      | succ d ih =>
        intro m τ hm hτ hbτ hpτ he
        have hmn : m < n := by omega
        obtain ⟨τ₁, r₁, c₁⟩ := code_spec hw body (it m) τ hd.2 (hlt m hmn).2 hτ hbτ hpτ
        have hb₁ := r₁.bounded hw hbτ
        have hc₁ : c.Fits w (uenv D τ₁.toH) := by
          rw [c₁.1, ← iter_succ]; exact hcf (m + 1) (by omega)
        obtain ⟨τ₂, r₂, e₂, u₂, s₂, p₂, o₂, b₂⟩ := ex_code_N (x := x) hw c τ₁ hd.1 hb₁ hc₁
        have c₂ : CCorr D τ₂ (it (m + 1)) := by
          show CCorr D τ₂ (iter x body σ (m + 1))
          rw [iter_succ]
          exact ⟨u₂.trans c₁.1, s₂.trans c₁.2.1, p₂.trans c₁.2.2.1, o₂.trans c₁.2.2.2⟩
        have he₂ : τ₂.env (sc R D 0) = c.eval (it (m + 1)).env := by
          show _ = c.eval (iter x body σ (m + 1)).env
          rw [e₂, c₁.1, iter_succ]
        obtain ⟨τ', r', c'⟩ := ih (m + 1) τ₂ (by omega) c₂ b₂
          (by rw [p₂]; exact r₁.pos_le hpτ) he₂
        have hv : scTest R D Q τ.view = true := by
          show (τ.toH.view (sc R D 0)).isSome = true
          rw [HSt.view_isSome_iff]; simp only [NSt.toH_env]; rw [he]; exact (hlt m hmn).1
        refine ⟨τ', (NLe.loopT hv (r₁.seq r₂) r').mono ?_, c'⟩
        rw [Finset.sum_eq_sum_Ico_succ_bot hmn]
        simp only [condCost]; omega
    obtain ⟨h1, h2, h3, h4⟩ := hc
    obtain ⟨st₁, r₁, e₁, u₁, s₁, p₁, o₁, b₁⟩ :=
      ex_code_N (x := x) hw c st hd.1 hb (by rw [h1]; exact hcf 0 (Nat.zero_le _))
    obtain ⟨τ', r', c'⟩ := aux n 0 st₁ (by omega)
      ⟨u₁.trans h1, s₁.trans h2, p₁.trans h3, o₁.trans h4⟩ b₁ (by rw [p₁]; exact hp)
      (by rw [e₁, h1]; rfl)
    refine ⟨τ', (r₁.seq r').mono ?_, c'⟩
    rw [Finset.range_eq_Ico]; simp only [condCost]; omega

end CStm

end Lax119563Proofs.Compiler
