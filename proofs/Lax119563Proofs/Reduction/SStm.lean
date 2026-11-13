import Lax119563Proofs.Reduction.SProg

/-!
# Structured statements and their compilation

Statements `Stm R`: `skip`, `set r e`, `emit e`, sequencing, `ite c p q` (`c ≠ 0`), counting
loops `loop i lim body` (`i = 0, …, lim - 1`, the bound read once) and `loopX i lim xb body`,
which additionally sets `xb := x[i]` (bit `i` of the input, `0` beyond its end) at the start
of every iteration.

`Stm.exec x c env` is the final valuation and the emitted list; `Stm.cost x w c env` is a cost
bound and `Stm.Fits x w c env` says that all values stay below `2 ^ w`. `Stm.code R D c`
compiles a statement to `HProg (R + D + 1)`, and `Stm.code_spec` says that the compiled
program runs within `cost` and produces the denotation.
-/

namespace Lax119563Proofs.Reduction

variable {R D : ℕ} {x : List Bool} {w : ℕ}

/-! ## Counting loops with an invariant -/

lemma forUp_inv {N : ℕ} {i lim f t : Fin N} {body : HProg N} (hil : i ≠ lim) (hif : i ≠ f)
    (hit : i ≠ t) (hlf : lim ≠ f) (hlt : lim ≠ t) (hft : f ≠ t) (hw : 2 ≤ w) (L : ℕ)
    (hL : L + 1 < 2 ^ w) (hbi : body.wr i = false) (hbl : body.wr lim = false)
    (Inv : ℕ → HSt N → Prop) (C : ℕ → ℕ)
    (hstep : ∀ k < L, ∀ σ : HSt N, Inv k σ → σ.Bdd w → σ.env i = k → σ.env lim = L →
      ∃ σ', HLe x w body σ σ' (C k) ∧ ∀ τ : HSt N, τ.out = σ'.out → τ.pos = σ'.pos →
        (∀ q, q ≠ i → q ≠ f → q ≠ t → τ.env q = σ'.env q) → τ.env i = k + 1 → Inv (k + 1) τ)
    (st : HSt N) (hb : st.Bdd w) (hl : st.env lim = L)
    (h0 : ∀ τ : HSt N, τ.out = st.out → τ.pos = st.pos →
      (∀ q, q ≠ i → q ≠ f → q ≠ t → τ.env q = st.env q) → τ.env i = 0 → Inv 0 τ) :
    ∃ σ, HLe x w (HProg.forUp i lim f t body) st σ
      (∑ k ∈ Finset.range L, (C k + 4 * unitCost w + 1) + 2 * unitCost w + 1) ∧ Inv L σ := by
  have h2 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  set c : RView N → Bool := fun v => (v f).isSome
  set body' : HProg N := .seq body (.seq (HProg.inc i t) (.lt f i lim))
  have aux : ∀ m k (σ : HSt N), k + m = L → Inv k σ → σ.Bdd w → σ.env i = k →
      σ.env lim = L → σ.env f = ltFlag k L →
      ∃ σ', HLe x w (.loop c body') σ σ'
        (∑ j ∈ Finset.Ico k L, (C j + 4 * unitCost w + 1) + 1) ∧ Inv L σ' := by
    intro m
    induction m with
    | zero =>
      intro k σ hk hI _ _ _ hf
      have : k = L := by omega
      subst this
      refine ⟨σ, (HLe.loopF ?_).mono (by simp), hI⟩
      simp [c, HSt.view, hf, ltFlag]
    | succ m ih =>
      intro k σ hk hI hb' hi hl' hf
      have hkL : k < L := by omega
      obtain ⟨σ₁, h₁, hτ⟩ := hstep k hkL σ hI hb' hi hl'
      have hb₁ := h₁.bounded hw hb'
      have hi₁ : σ₁.env i = k := by rw [h₁.frame hbi, hi]
      have hl₁ : σ₁.env lim = L := by rw [h₁.frame hbl, hl']
      have hinc := inc_spec (x := x) hit (st := σ₁) (hb₁ t) (by omega)
      set σ₂ := (σ₁.set t 1).set i (σ₁.env i + 1)
      have hlt' : HLe x w (.lt f i lim) σ₂ (σ₂.set f (ltFlag (k + 1) L)) (unitCost w) := by
        have e : σ₂.set f (ltFlag (k + 1) L) =
            σ₂.set f (if σ₂.env i < σ₂.env lim then 1 else 0) := by
          simp [σ₂, HSt.set_env_ne _ hil.symm, HSt.set_env_ne _ hlt, hi₁, hl₁, ltFlag]
        rw [e]
        refine HLe.of_runs (HRuns.lt hif.symm hlf.symm hil ?_ ?_ ?_)
        · simp only [σ₂, HSt.set_env_ne _ hif.symm, HSt.set_env_ne _ hft]; exact hb₁ f
        · simp [σ₂]; omega
        · simp only [σ₂, HSt.set_env_ne _ hil.symm, HSt.set_env_ne _ hlt]; omega
      set σ₃ := σ₂.set f (ltFlag (k + 1) L)
      have hI₃ : Inv (k + 1) σ₃ := by
        apply hτ
        · rfl
        · rfl
        · intro q h1 h2 h3
          simp [σ₃, σ₂, HSt.set, Function.update_of_ne h1, Function.update_of_ne h2,
            Function.update_of_ne h3]
        · simp [σ₃, σ₂, Function.update_apply, hif, hi₁]
      have hb₃ : σ₃.Bdd w := (h₁.seq (hinc.seq hlt')).bounded hw hb'
      obtain ⟨σ', h', hI'⟩ := ih (k + 1) σ₃ (by omega) hI₃ hb₃
        (by simp [σ₃, σ₂, Function.update_apply, hif, hi₁])
        (by simp [σ₃, σ₂, Function.update_apply, hlf, hil.symm, hlt, hl₁])
        (by simp [σ₃])
      have hc : c σ.view = true := by
        simp only [c]; rw [HSt.view_isSome_iff, hf]; simp [ltFlag, hkL]
      refine ⟨σ', (HLe.loopT hc (h₁.seq (hinc.seq hlt')) h').mono ?_, hI'⟩
      rw [Finset.sum_eq_sum_Ico_succ_bot hkL]
      omega
  have hc1 : HLe x w (.clr i) st (st.set i 0) (unitCost w) := HLe.of_runs (HRuns.clr (hb i))
  have hc2 : HLe x w (.lt f i lim) (st.set i 0) ((st.set i 0).set f (ltFlag 0 L))
      (unitCost w) := by
    have e : (st.set i 0).set f (ltFlag 0 L) =
        (st.set i 0).set f (if (st.set i 0).env i < (st.set i 0).env lim then 1 else 0) := by
      simp [Function.update_apply, hil.symm, hl, ltFlag]
    rw [e]
    refine HLe.of_runs (HRuns.lt hif.symm hlf.symm hil ?_ ?_ ?_)
    · simp only [HSt.set_env_ne _ hif.symm]; exact hb f
    · simp
    · simp only [HSt.set_env_ne _ hil.symm]; exact hb lim
  set τ₀ := (st.set i 0).set f (ltFlag 0 L)
  have hI₀ : Inv 0 τ₀ := by
    apply h0
    · rfl
    · rfl
    · intro q h1 h2 _
      simp [τ₀, HSt.set, Function.update_of_ne h1, Function.update_of_ne h2]
    · simp [τ₀, Function.update_apply, hif]
  have hb₀ : τ₀.Bdd w := (hc1.seq hc2).bounded hw hb
  obtain ⟨σ, hσ, hI⟩ := aux L 0 τ₀ (by omega) hI₀ hb₀
    (by simp [τ₀, Function.update_apply, hif])
    (by simp [τ₀, Function.update_apply, hlf, hil.symm, hl])
    (by simp [τ₀])
  refine ⟨σ, (hc1.seq (hc2.seq hσ)).mono ?_, hI⟩
  rw [Finset.range_eq_Ico]
  omega

/-! ## Statements -/

/-- Statements over the user registers. -/
inductive Stm (R : ℕ) where
  | skip
  | set (r : Fin R) (e : Ex R)
  | emit (e : Ex R)
  | seq (p q : Stm R)
  | ite (c : Ex R) (p q : Stm R)
  | loop (i lim : Fin R) (body : Stm R)
  | loopX (i lim xb : Fin R) (body : Stm R)

/-- The first `k` iterations of a loop whose iteration `j` maps the valuation `e` to
`f j e` (final valuation, emitted list). -/
def runLoop (f : ℕ → (Fin R → ℕ) → (Fin R → ℕ) × List ℕ) :
    ℕ → (Fin R → ℕ) → (Fin R → ℕ) × List ℕ
  | 0, env => (env, [])
  | k + 1, env =>
    let a := runLoop f k env
    let b := f k a.1
    (b.1, a.2 ++ b.2)

namespace Stm

/-- The denotation: the final valuation and the emitted list. -/
def exec (x : List Bool) : Stm R → (Fin R → ℕ) → (Fin R → ℕ) × List ℕ
  | skip, env => (env, [])
  | set r e, env => (Function.update env r (e.eval env), [])
  | emit e, env => (env, [e.eval env])
  | seq p q, env =>
    let a := exec x p env
    let b := exec x q a.1
    (b.1, a.2 ++ b.2)
  | ite c p q, env => if c.eval env ≠ 0 then exec x p env else exec x q env
  | loop i lim body, env =>
    let a := runLoop (fun k e => exec x body (Function.update e i k)) (env lim) env
    (Function.update a.1 i (env lim), a.2)
  | loopX i lim xb body, env =>
    let a := runLoop (fun k e => exec x body
      (Function.update (Function.update e i k) xb (inBit x k))) (env lim) env
    (Function.update a.1 i (env lim), a.2)

/-- A cost bound. -/
def cost (x : List Bool) (w : ℕ) : Stm R → (Fin R → ℕ) → ℕ
  | skip, _ => unitCost w
  | set _ e, _ => e.size * Ex.nodeCost w + unitCost w
  | emit e, _ => e.size * Ex.nodeCost w + unitCost w
  | seq p q, env => cost x w p env + cost x w q (exec x p env).1
  | ite c p q, env => c.size * Ex.nodeCost w + 1 +
      (if c.eval env ≠ 0 then cost x w p env else cost x w q env)
  | loop i lim body, env =>
    ∑ k ∈ Finset.range (env lim), (cost x w body (Function.update
      (runLoop (fun k e => exec x body (Function.update e i k)) k env).1 i k) +
        4 * unitCost w + 1) + 2 * unitCost w + 1
  | loopX i lim xb body, env =>
    unitCost w + (∑ k ∈ Finset.range (env lim), (unitCost w + cost x w body
      (Function.update (Function.update (runLoop (fun k e => exec x body
        (Function.update (Function.update e i k) xb (inBit x k))) k env).1 i k) xb
          (inBit x k)) + 4 * unitCost w + 1) + 2 * unitCost w + 1) +
      unitCost w * (x.length + 1)

/-- All values stay below `2 ^ w`. -/
def Fits (x : List Bool) (w : ℕ) : Stm R → (Fin R → ℕ) → Prop
  | skip, _ => True
  | set _ e, env => e.Fits w env
  | emit e, env => e.Fits w env
  | seq p q, env => Fits x w p env ∧ Fits x w q (exec x p env).1
  | ite c p q, env => c.Fits w env ∧ (if c.eval env ≠ 0 then Fits x w p env else Fits x w q env)
  | loop i lim body, env => env lim + 1 < 2 ^ w ∧ ∀ k < env lim, Fits x w body
      (Function.update (runLoop (fun k e => exec x body (Function.update e i k)) k env).1 i k)
  | loopX i lim xb body, env => env lim + 1 < 2 ^ w ∧ ∀ k < env lim, Fits x w body
      (Function.update (Function.update (runLoop (fun k e => exec x body
        (Function.update (Function.update e i k) xb (inBit x k))) k env).1 i k) xb (inBit x k))

/-- The registers a statement may write. -/
def wr : Stm R → Fin R → Bool
  | skip, _ => false
  | set r _, q => decide (q = r)
  | emit _, _ => false
  | seq p p', q => wr p q || wr p' q
  | ite _ p p', q => wr p q || wr p' q
  | loop i _ body, q => decide (q = i) || wr body q
  | loopX i _ xb body, q => decide (q = i) || decide (q = xb) || wr body q

/-- The statement contains no `loopX`. -/
def noX : Stm R → Bool
  | seq p q => noX p && noX q
  | ite _ p q => noX p && noX q
  | loop _ _ body => noX body
  | loopX .. => false
  | _ => true

/-- Well-formedness: loops keep their counter and bound. -/
def WF : Stm R → Prop
  | seq p q => WF p ∧ WF q
  | ite _ p q => WF p ∧ WF q
  | loop i lim body => i ≠ lim ∧ wr body i = false ∧ wr body lim = false ∧ WF body
  | loopX i lim xb body => i ≠ lim ∧ xb ≠ i ∧ xb ≠ lim ∧ wr body i = false ∧
      wr body lim = false ∧ noX body = true ∧ WF body
  | _ => True

/-- The number of scratch registers needed. -/
def depth : Stm R → ℕ
  | skip => 1
  | set _ e => e.depth
  | emit e => e.depth
  | seq p q => max (depth p) (depth q)
  | ite c p q => max c.depth (max (depth p) (depth q))
  | loop _ _ body => max 2 (depth body)
  | loopX _ _ _ body => max 2 (depth body)

/-- Compilation to `HProg` with scratch registers `R, …, R + D`. -/
def code (R D : ℕ) : Stm R → HProg (R + D + 1)
  | skip => .clr (sc R D 0)
  | set r e => .seq (e.code R D 0) (.copy (sc R D 0) (ur D r))
  | emit e => .seq (e.code R D 0) (.emit (sc R D 0))
  | seq p q => .seq (code R D p) (code R D q)
  | ite c p q => .seq (c.code R D 0)
      (.ite (fun v => (v (sc R D 0)).isSome) (code R D p) (code R D q))
  | loop i lim body => HProg.forUp (ur D i) (ur D lim) (sc R D 0) (sc R D 1) (code R D body)
  | loopX i lim xb body => .seq .rst (.seq (HProg.forUp (ur D i) (ur D lim) (sc R D 0)
      (sc R D 1) (.seq (.rd (ur D xb)) (code R D body))) .rst)

lemma code_wr_ur : ∀ (c : Stm R) (r : Fin R), wr c r = false →
    (code R D c).wr (ur D r) = false
  | skip, r, _ => by simp [code, HProg.wr, ur_ne_sc]
  | set r' e, r, h => by
    simp only [wr, decide_eq_false_iff_not] at h
    simp [code, HProg.wr, Ex.code_wr_ur, ur_inj, h]
  | emit e, r, _ => by simp [code, HProg.wr, Ex.code_wr_ur]
  | seq p q, r, h => by
    simp only [wr, Bool.or_eq_false_iff] at h
    simp [code, HProg.wr, code_wr_ur p r h.1, code_wr_ur q r h.2]
  | ite c p q, r, h => by
    simp only [wr, Bool.or_eq_false_iff] at h
    simp [code, HProg.wr, Ex.code_wr_ur, code_wr_ur p r h.1, code_wr_ur q r h.2]
  | loop i lim body, r, h => by
    simp only [wr, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    simp [code, HProg.forUp, HProg.inc, HProg.wr, ur_inj, ur_ne_sc, h.1,
      code_wr_ur body r h.2]
  | loopX i lim xb body, r, h => by
    simp only [wr, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    simp [code, HProg.forUp, HProg.inc, HProg.wr, ur_inj, ur_ne_sc, h.1.1, h.1.2,
      code_wr_ur body r h.2]

lemma code_mv : ∀ c : Stm R, noX c = true → (code R D c).mv = false
  | skip, _ => rfl
  | set _ e, _ => by simp [code, HProg.mv, Ex.code_mv]
  | emit e, _ => by simp [code, HProg.mv, Ex.code_mv]
  | seq p q, h => by
    simp only [noX, Bool.and_eq_true] at h
    simp [code, HProg.mv, code_mv p h.1, code_mv q h.2]
  | ite c p q, h => by
    simp only [noX, Bool.and_eq_true] at h
    simp [code, HProg.mv, Ex.code_mv, code_mv p h.1, code_mv q h.2]
  | loop i lim body, h => by
    simp only [noX] at h
    simp [code, HProg.forUp, HProg.inc, HProg.mv, code_mv body h]
  | loopX .., h => by simp [noX] at h

end Stm

lemma uenv_set_sc (st : HSt (R + D + 1)) (k v : ℕ) :
    uenv D (st.set (sc R D k) v) = uenv D st := by
  funext r; simp [uenv, HSt.set_env_ne _ (ur_ne_sc r k)]

lemma uenv_set_ur (st : HSt (R + D + 1)) (r : Fin R) (v : ℕ) :
    uenv D (st.set (ur D r) v) = Function.update (uenv D st) r v := by
  funext q
  by_cases h : q = r
  · subst h; simp [uenv]
  · simp [uenv, Function.update_of_ne h, HSt.set_env_ne _ (fun e => h (ur_inj.mp e))]

lemma inBit_min (x : List Bool) (k : ℕ) : inBit x (min k x.length) = inBit x k := by
  unfold inBit
  rcases le_or_gt k x.length with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h.le, List.drop_eq_nil_of_le le_rfl, List.drop_eq_nil_of_le h.le]

lemma uenv_of_agree {σ τ : HSt (R + D + 1)} {i : Fin R} {v : ℕ}
    (h : ∀ q, q ≠ ur D i → q ≠ sc R D 0 → q ≠ sc R D 1 → τ.env q = σ.env q)
    (hi : τ.env (ur D i) = v) : uenv D τ = Function.update (uenv D σ) i v := by
  funext r
  by_cases hr : r = i
  · subst hr; simp [uenv, hi]
  · simp only [uenv, Function.update_of_ne hr]
    exact h _ (fun e => hr (ur_inj.mp e)) (ur_ne_sc r 0) (ur_ne_sc r 1)

namespace Stm

/-- **Compilation of statements.** -/
theorem code_spec (hw : 2 ≤ w) : ∀ (c : Stm R) (env : Fin R → ℕ) (st : HSt (R + D + 1)),
    WF c → depth c ≤ D → Fits x w c env → uenv D st = env → st.Bdd w → st.pos ≤ x.length →
    (noX c = true ∨ st.pos = 0) →
    ∃ st', HLe x w (code R D c) st st' (cost x w c env) ∧ uenv D st' = (exec x c env).1 ∧
      st'.out = st.out ++ (exec x c env).2 ∧ st'.pos = st.pos
  | skip, env, st, _, _, _, he, hb, _, _ => by
    refine ⟨_, HLe.of_runs (HRuns.clr (hb _)), ?_, by simp [exec], rfl⟩
    rw [uenv_set_sc, he]; rfl
  | set r e, env, st, _, hd, hf, he, hb, _, _ => by
    subst he
    obtain ⟨st₁, h₁, e₁⟩ := Ex.code_spec (x := x) hw e 0 st (by simpa [depth] using hd) hb hf
    have hb₁ := h₁.bounded hw hb
    refine ⟨_, h₁.seq (HLe.of_runs (HRuns.copy (sc_ne_ur r 0) (hb₁ _) (hb₁ _))), ?_, ?_, ?_⟩
    · rw [uenv_set_ur, Ex.code_uenv h₁, e₁]; rfl
    · rw [HSt.set_out, h₁.out_eq (Ex.code_em e 0)]; simp [exec]
    · rw [HSt.set_pos, h₁.pos_eq (Ex.code_mv e 0)]
  | emit e, env, st, _, hd, hf, he, hb, _, _ => by
    subst he
    obtain ⟨st₁, h₁, e₁⟩ := Ex.code_spec (x := x) hw e 0 st (by simpa [depth] using hd) hb hf
    have hb₁ := h₁.bounded hw hb
    refine ⟨_, h₁.seq (HLe.of_runs (HRuns.emit (hb₁ _))), ?_, ?_, ?_⟩
    · rw [← Ex.code_uenv h₁]; rfl
    · simp [exec, e₁, h₁.out_eq (Ex.code_em e 0)]
    · simp [h₁.pos_eq (Ex.code_mv e 0)]
  | seq p q, env, st, hwf, hd, hf, he, hb, hp, hx => by
    simp only [depth, max_le_iff] at hd
    simp only [noX, Bool.and_eq_true] at hx
    obtain ⟨st₁, h₁, u₁, o₁, p₁⟩ := code_spec hw p env st hwf.1 hd.1 hf.1 he hb hp
      (by tauto)
    obtain ⟨st₂, h₂, u₂, o₂, p₂⟩ := code_spec hw q _ st₁ hwf.2 hd.2 hf.2 u₁
      (h₁.bounded hw hb) (by omega) (by rcases hx with h | h; exacts [Or.inl h.2, Or.inr (by omega)])
    refine ⟨st₂, (h₁.seq h₂).mono le_rfl, u₂, ?_, by omega⟩
    rw [o₂, o₁]; simp [exec]
  | ite c p q, env, st, hwf, hd, hf, he, hb, hp, hx => by
    simp only [depth, max_le_iff] at hd
    simp only [noX, Bool.and_eq_true] at hx
    subst he
    obtain ⟨st₁, h₁, e₁⟩ := Ex.code_spec (x := x) hw c 0 st (by omega) hb hf.1
    have u₁ := Ex.code_uenv h₁
    have hb₁ := h₁.bounded hw hb
    have o₁ := h₁.out_eq (Ex.code_em c 0)
    have p₁ := h₁.pos_eq (Ex.code_mv c 0)
    by_cases hc : c.eval (uenv D st) ≠ 0
    · have hf' : Fits x w p (uenv D st) := by have := hf.2; rw [if_pos hc] at this; exact this
      obtain ⟨st₂, h₂, u₂, o₂, p₂⟩ := code_spec hw p _ st₁ hwf.1 hd.2.1 hf' u₁ hb₁
        (by omega) (by rcases hx with h | h; exacts [Or.inl h.1, Or.inr (by omega)])
      refine ⟨st₂, (h₁.seq (HLe.iteT (c := fun v => (v (sc R D 0)).isSome) ?_ h₂)).mono ?_,
        ?_, ?_, by omega⟩
      · rw [HSt.view_isSome_iff, e₁]; exact hc
      · simp only [cost, if_pos hc]; omega
      · simp only [exec, if_pos hc]; exact u₂
      · simp only [exec, if_pos hc]; rw [o₂, o₁]
    · have hf' : Fits x w q (uenv D st) := by have := hf.2; rw [if_neg hc] at this; exact this
      obtain ⟨st₂, h₂, u₂, o₂, p₂⟩ := code_spec hw q _ st₁ hwf.2 hd.2.2 hf' u₁ hb₁
        (by omega) (by rcases hx with h | h; exacts [Or.inl h.2, Or.inr (by omega)])
      refine ⟨st₂, (h₁.seq (HLe.iteF (c := fun v => (v (sc R D 0)).isSome) ?_ h₂)).mono ?_,
        ?_, ?_, by omega⟩
      · rw [← Bool.not_eq_true, HSt.view_isSome_iff, e₁]; exact hc
      · simp only [cost, if_neg hc]; omega
      · simp only [exec, if_neg hc]; exact u₂
      · simp only [exec, if_neg hc]; rw [o₂, o₁]
  | loop i lim body, env, st, hwf, hd, hf, he, hb, hp, hx => by
    obtain ⟨hil, hbi, hbl, hwb⟩ := hwf
    simp only [depth, max_le_iff] at hd
    simp only [noX] at hx
    have h01 : sc R D 0 ≠ sc R D 1 := sc_ne (by omega) (by omega)
    have hil' : ur D i ≠ ur D lim := fun e => hil (ur_inj.mp e)
    set F : ℕ → (Fin R → ℕ) → (Fin R → ℕ) × List ℕ :=
      fun k e => exec x body (Function.update e i k)
    obtain ⟨σ, hσ, hI⟩ := forUp_inv (x := x) (w := w) (body := code R D body) hil'
      (ur_ne_sc i 0) (ur_ne_sc i 1) (ur_ne_sc lim 0) (ur_ne_sc lim 1) h01 hw (env lim)
      hf.1 (code_wr_ur body i hbi) (code_wr_ur body lim hbl)
      (fun k σ => uenv D σ = Function.update (runLoop F k env).1 i k ∧
        σ.out = st.out ++ (runLoop F k env).2 ∧ σ.pos = st.pos)
      (fun k => cost x w body (Function.update (runLoop F k env).1 i k))
      (by
        intro k hk σ hI hbσ _ _
        obtain ⟨σ', h', u', o', p'⟩ := code_spec hw body _ σ hwb hd.2 (hf.2 k hk) hI.1 hbσ
          (by rw [hI.2.2]; exact hp) (by rcases hx with h | h; exacts [Or.inl h, Or.inr (by rw [hI.2.2]; exact h)])
        refine ⟨σ', h', fun τ ho hpo hag hi => ⟨?_, ?_, ?_⟩⟩
        · rw [uenv_of_agree hag hi, u']; rfl
        · rw [ho, o', hI.2.1]; simp [runLoop, F]
        · rw [hpo, p', hI.2.2])
      st hb (by rw [← he]; rfl)
      (by
        intro τ ho hpo hag hi
        refine ⟨?_, by simp [ho, runLoop], hpo⟩
        rw [uenv_of_agree hag hi, he]; rfl)
    exact ⟨σ, hσ, hI.1, hI.2.1, hI.2.2⟩
  | loopX i lim xb body, env, st, hwf, hd, hf, he, hb, hp, hx => by
    obtain ⟨hil, hxi, hxl, hbi, hbl, hnx, hwb⟩ := hwf
    simp only [depth, max_le_iff] at hd
    have hp0 : st.pos = 0 := by simpa [noX] using hx
    have h01 : sc R D 0 ≠ sc R D 1 := sc_ne (by omega) (by omega)
    have hil' : ur D i ≠ ur D lim := fun e => hil (ur_inj.mp e)
    set F : ℕ → (Fin R → ℕ) → (Fin R → ℕ) × List ℕ :=
      fun k e => exec x body (Function.update (Function.update e i k) xb (inBit x k))
    have hr₁ : HLe x w .rst st st (unitCost w) :=
      (HLe.of_runs (HRuns.rst (x := x) (w := w) hp)).of_eq (by ext <;> simp [hp0]) (by simp [hp0])
    have hrd : (HProg.seq (.rd (ur D xb)) (code R D body)).wr (ur D i) = false := by
      simp [HProg.wr, ur_inj, Ne.symm hxi, code_wr_ur body i hbi]
    have hrdl : (HProg.seq (.rd (ur D xb)) (code R D body)).wr (ur D lim) = false := by
      simp [HProg.wr, ur_inj, Ne.symm hxl, code_wr_ur body lim hbl]
    obtain ⟨σ, hσ, hI⟩ := forUp_inv (x := x) (w := w)
      (body := .seq (.rd (ur D xb)) (code R D body)) hil'
      (ur_ne_sc i 0) (ur_ne_sc i 1) (ur_ne_sc lim 0) (ur_ne_sc lim 1) h01 hw (env lim)
      hf.1 hrd hrdl
      (fun k σ => uenv D σ = Function.update (runLoop F k env).1 i k ∧
        σ.out = st.out ++ (runLoop F k env).2 ∧ σ.pos = min k x.length)
      (fun k => unitCost w + cost x w body (Function.update (Function.update
        (runLoop F k env).1 i k) xb (inBit x k)))
      (by
        intro k hk σ hI hbσ _ _
        have hpσ : σ.pos ≤ x.length := by rw [hI.2.2]; exact min_le_right _ _
        have hrun := HLe.of_runs (HRuns.rd (x := x) (r := ur D xb) (hbσ _) hpσ)
        set σ₁ : HSt (R + D + 1) := { (σ.set (ur D xb) (inBit x σ.pos)) with
          pos := min (σ.pos + 1) x.length }
        have hb₁ : σ₁.Bdd w := hrun.bounded hw hbσ
        have hu₁ : uenv D σ₁ = Function.update (Function.update (runLoop F k env).1 i k) xb
            (inBit x k) := by
          show uenv D (σ.set (ur D xb) (inBit x σ.pos)) = _
          rw [uenv_set_ur, hI.1, hI.2.2, inBit_min]
        obtain ⟨σ', h', u', o', p'⟩ := code_spec hw body _ σ₁ hwb hd.2 (hf.2 k hk) hu₁ hb₁
          (by simp [σ₁]) (Or.inl hnx)
        refine ⟨σ', hrun.seq h', fun τ ho hpo hag hi => ⟨?_, ?_, ?_⟩⟩
        · rw [uenv_of_agree hag hi, u']; rfl
        · rw [ho, o']; simp [σ₁, hI.2.1, runLoop, F]
        · rw [hpo, p']; simp only [σ₁, hI.2.2]; omega)
      st hb (by rw [← he]; rfl)
      (by
        intro τ ho hpo hag hi
        refine ⟨?_, by simp [ho, runLoop], by rw [hpo, hp0]; simp⟩
        rw [uenv_of_agree hag hi, he]; rfl)
    have hr₂ : HLe x w .rst σ { σ with pos := 0 } (unitCost w * (x.length + 1)) := by
      refine (HLe.of_runs (HRuns.rst (x := x) (w := w) ?_)).mono ?_
      · rw [hI.2.2]; exact min_le_right _ _
      · rw [hI.2.2]; exact Nat.mul_le_mul_left _ (by omega)
    refine ⟨{ σ with pos := 0 }, (hr₁.seq (hσ.seq hr₂)).mono (by simp only [cost, F]; omega), hI.1, hI.2.1, hp0.symm⟩

end Stm

end Lax119563Proofs.Reduction
