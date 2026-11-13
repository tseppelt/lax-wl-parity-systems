import Lax119563Proofs.Reduction.HFrame

/-!
# Structured programs with expressions

A layer above `HProg` with a total denotational semantics, so that the output and the cost of
the reduction program can be computed by equational reasoning instead of by runs.

* Expressions `Ex R` over user registers `Fin R`: variables, constants, `+`, `[a < b]`,
  `a / 2`, `a % 2`.
* Statements `Stm R`: `skip`, `set r e`, `emit e`, sequencing, `ite c p q` (`c ≠ 0`), and
  counting loops `loop i lim body` (`i = 0, …, lim - 1`, the bound read once) and
  `loopX i lim xb body`, which additionally sets `xb := x[i]` (bit `i` of the input, `0` beyond
  its end) at the start of every iteration.

`Stm.exec x c env` is the final register valuation and the emitted list; `Stm.cost x w c env`
is a cost bound and `Stm.Fits x w c env` says that all values stay below `2 ^ w`.
`Stm.code R D c : HProg (R + D + 1)` compiles a statement with `D + 1` scratch registers
(`Stm.code_spec`): it runs within `cost` and produces the denotation.
-/

namespace Lax119563Proofs.Reduction

variable {R D : ℕ} {x : List Bool} {w : ℕ}

/-! ## Registers -/

/-- User register `r` among `R + D + 1` registers. -/
def ur (D : ℕ) (r : Fin R) : Fin (R + D + 1) := ⟨r.val, by omega⟩

/-- Scratch register `k` (the registers `R, …, R + D`; indices beyond `D` are identified). -/
def sc (R D k : ℕ) : Fin (R + D + 1) := ⟨R + min k D, by omega⟩

lemma ur_ne_sc (r : Fin R) (k : ℕ) : ur D r ≠ sc R D k := by
  intro h; have := congrArg Fin.val h; simp only [ur, sc] at this; omega

lemma sc_ne_ur (r : Fin R) (k : ℕ) : sc R D k ≠ ur D r := (ur_ne_sc r k).symm

lemma sc_ne {k j : ℕ} (hk : k < D) (hkj : k < j) : sc R D k ≠ sc R D j := by
  intro h; have := congrArg Fin.val h; simp only [sc] at this; omega

lemma ur_inj {r q : Fin R} : ur D r = ur D q ↔ r = q := by
  constructor
  · intro h; exact Fin.ext (by simpa [ur] using congrArg Fin.val h)
  · rintro rfl; rfl

/-- The user registers of a state. -/
def uenv (D : ℕ) (st : HSt (R + D + 1)) : Fin R → ℕ := fun r => st.env (ur D r)

/-! ## Constants -/

/-- `r := c`. -/
def setK {N : ℕ} (r : Fin N) (c : ℕ) : HProg N :=
  if c = 0 then .clr r else .seq (setK r (c / 2)) (if c % 2 = 1 then .one r else .dbl r)
termination_by c
decreasing_by omega

lemma setK_wr {N : ℕ} (r q : Fin N) (c : ℕ) : (setK r c).wr q = true → q = r := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rw [setK]
    split_ifs with h1 h2
    · simp [HProg.wr]
    · simp only [HProg.wr, Bool.or_eq_true, decide_eq_true_eq]
      rintro (h | h)
      · exact ih _ (by omega) h
      · exact h
    · simp only [HProg.wr, Bool.or_eq_true, decide_eq_true_eq]
      rintro (h | h)
      · exact ih _ (by omega) h
      · exact h

lemma setK_em {N : ℕ} (r : Fin N) (c : ℕ) : (setK r c).em = false := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rw [setK]
    split_ifs with h1 h2
    · rfl
    · simp [HProg.em, ih _ (show c / 2 < c by omega)]
    · simp [HProg.em, ih _ (show c / 2 < c by omega)]

lemma setK_mv {N : ℕ} (r : Fin N) (c : ℕ) : (setK r c).mv = false := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rw [setK]
    split_ifs with h1 h2
    · rfl
    · simp [HProg.mv, ih _ (show c / 2 < c by omega)]
    · simp [HProg.mv, ih _ (show c / 2 < c by omega)]

lemma setK_spec {N : ℕ} (r : Fin N) : ∀ (m c : ℕ), c < 2 ^ m → m ≤ w → ∀ st : HSt N,
    st.env r < 2 ^ w → HLe x w (setK r c) st (st.set r c) ((m + 1) * unitCost w) := by
  intro m
  induction m with
  | zero =>
    intro c hc _ st hr
    have : c = 0 := by simpa using hc
    subst this
    rw [setK, if_pos rfl]
    exact (HLe.of_runs (HRuns.clr hr)).mono (by simp)
  | succ m ih =>
    intro c hc hm st hr
    rw [setK]
    split_ifs with h1 h2
    · subst h1; exact (HLe.of_runs (HRuns.clr hr)).mono (by nlinarith)
    · have h := ih (c / 2) (by rw [pow_succ] at hc; omega) (by omega) st hr
      have hlt : 2 * (st.set r (c / 2)).env r + 1 < 2 ^ w := by
        have : c < 2 ^ w := lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hm)
        simp; omega
      refine (h.seq (HLe.of_runs (HRuns.one hlt))).of_eq ?_ (by ring_nf; omega)
      simp only [HSt.set_env_self, HSt.set_set_same]
      congr 1; omega
    · have h := ih (c / 2) (by rw [pow_succ] at hc; omega) (by omega) st hr
      have hlt : 2 * (st.set r (c / 2)).env r < 2 ^ w := by
        have : c < 2 ^ w := lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hm)
        simp; omega
      refine (h.seq (HLe.of_runs (HRuns.dbl hlt))).of_eq ?_ (by ring_nf; omega)
      simp only [HSt.set_env_self, HSt.set_set_same]
      congr 1; omega

/-! ## Expressions -/

/-- Expressions over the user registers. -/
inductive Ex (R : ℕ) where
  | var (r : Fin R)
  | const (c : ℕ)
  | add (a b : Ex R)
  | lt (a b : Ex R)
  | half (a : Ex R)
  | odd (a : Ex R)

namespace Ex

/-- The value of an expression. -/
def eval (env : Fin R → ℕ) : Ex R → ℕ
  | var r => env r
  | const c => c
  | add a b => eval env a + eval env b
  | lt a b => if eval env a < eval env b then 1 else 0
  | half a => eval env a / 2
  | odd a => eval env a % 2

/-- The number of nodes. -/
def size : Ex R → ℕ
  | var _ => 1
  | const _ => 1
  | add a b => size a + size b + 1
  | lt a b => size a + size b + 1
  | half a => size a + 1
  | odd a => size a + 1

/-- The number of scratch registers used. -/
def depth : Ex R → ℕ
  | var _ => 1
  | const _ => 1
  | add a b => max (depth a) (depth b + 1)
  | lt a b => max 3 (max (depth a + 1) (depth b + 2))
  | half a => depth a
  | odd a => depth a

lemma one_le_depth : ∀ e : Ex R, 1 ≤ e.depth
  | var _ => le_rfl
  | const _ => le_rfl
  | add a _ => le_trans (one_le_depth a) (le_max_left _ _)
  | lt _ _ => le_trans (by norm_num) (le_max_left _ _)
  | half a => one_le_depth a
  | odd a => one_le_depth a

/-- All values computed while evaluating the expression are below `2 ^ w`. -/
def Fits (w : ℕ) (env : Fin R → ℕ) : Ex R → Prop
  | var r => env r < 2 ^ w
  | const c => c < 2 ^ w
  | add a b => Fits w env a ∧ Fits w env b ∧ eval env a + eval env b < 2 ^ w
  | lt a b => Fits w env a ∧ Fits w env b
  | half a => Fits w env a
  | odd a => Fits w env a

/-- Evaluate into scratch register `k`, using the scratch registers from `k` on. -/
def code (R D : ℕ) : ℕ → Ex R → HProg (R + D + 1)
  | k, var r => .copy (ur D r) (sc R D k)
  | k, const c => setK (sc R D k) c
  | k, add a b => .seq (code R D k a) (.seq (code R D (k + 1) b) (.add (sc R D k) (sc R D (k + 1))))
  | k, lt a b => .seq (code R D (k + 1) a)
      (.seq (code R D (k + 2) b) (.lt (sc R D k) (sc R D (k + 1)) (sc R D (k + 2))))
  | k, half a => .seq (code R D k a) (.half (sc R D k))
  | k, odd a => .seq (code R D k a)
      (.ite (fun v => v (sc R D k) == some true) (setK (sc R D k) 1) (.clr (sc R D k)))

lemma code_wr : ∀ (e : Ex R) (k : ℕ) (q : Fin (R + D + 1)), (code R D k e).wr q = true →
    ∃ j, k ≤ j ∧ q = sc R D j
  | var r, k, q, h => ⟨k, le_rfl, by simpa [code, HProg.wr] using h⟩
  | const c, k, q, h => ⟨k, le_rfl, setK_wr _ _ _ h⟩
  | add a b, k, q, h => by
    simp only [code, HProg.wr, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h | h
    · exact code_wr a k q h
    · obtain ⟨j, hj, rfl⟩ := code_wr b (k + 1) q h; exact ⟨j, by omega, rfl⟩
    · exact ⟨k, le_rfl, h⟩
  | lt a b, k, q, h => by
    simp only [code, HProg.wr, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h | h
    · obtain ⟨j, hj, rfl⟩ := code_wr a (k + 1) q h; exact ⟨j, by omega, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := code_wr b (k + 2) q h; exact ⟨j, by omega, rfl⟩
    · exact ⟨k, le_rfl, h⟩
  | half a, k, q, h => by
    simp only [code, HProg.wr, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · exact code_wr a k q h
    · exact ⟨k, le_rfl, h⟩
  | odd a, k, q, h => by
    simp only [code, HProg.wr, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h | h
    · exact code_wr a k q h
    · exact ⟨k, le_rfl, setK_wr _ _ _ h⟩
    · exact ⟨k, le_rfl, h⟩

lemma code_em : ∀ (e : Ex R) (k : ℕ), (code R D k e).em = false
  | var _, _ => rfl
  | const _, _ => setK_em _ _
  | add a b, k => by simp [code, HProg.em, code_em a, code_em b]
  | lt a b, k => by simp [code, HProg.em, code_em a, code_em b]
  | half a, k => by simp [code, HProg.em, code_em a]
  | odd a, k => by simp [code, HProg.em, code_em a, setK_em]

lemma code_mv : ∀ (e : Ex R) (k : ℕ), (code R D k e).mv = false
  | var _, _ => rfl
  | const _, _ => setK_mv _ _
  | add a b, k => by simp [code, HProg.mv, code_mv a, code_mv b]
  | lt a b, k => by simp [code, HProg.mv, code_mv a, code_mv b]
  | half a, k => by simp [code, HProg.mv, code_mv a]
  | odd a, k => by simp [code, HProg.mv, code_mv a, setK_mv]

lemma code_wr_ur (e : Ex R) (k : ℕ) (r : Fin R) : (code R D k e).wr (ur D r) = false := by
  cases h : (code R D k e).wr (ur D r)
  · rfl
  · obtain ⟨j, -, hj⟩ := code_wr e k _ h
    exact absurd hj (ur_ne_sc r j)

lemma code_uenv {e : Ex R} {k : ℕ} {st st' : HSt (R + D + 1)} {T : ℕ}
    (h : HLe x w (code R D k e) st st' T) : uenv D st' = uenv D st := by
  funext r; exact h.frame (code_wr_ur e k r)

lemma code_keep {e : Ex R} {k j : ℕ} (hj : j < D) (hjk : j < k) {st st' : HSt (R + D + 1)}
    {T : ℕ} (h : HLe x w (code R D k e) st st' T) : st'.env (sc R D j) = st.env (sc R D j) := by
  apply h.frame
  cases hw : (code R D k e).wr (sc R D j)
  · rfl
  · obtain ⟨i, hi, he⟩ := code_wr e k _ hw
    exact absurd he (sc_ne hj (by omega))

/-- The unit cost of an expression node. -/
def nodeCost (w : ℕ) : ℕ := (w + 3) * unitCost w

lemma unitCost_le_nodeCost (w : ℕ) : unitCost w ≤ nodeCost w := by
  unfold nodeCost; nlinarith

lemma code_spec (hw : 2 ≤ w) : ∀ (e : Ex R) (k : ℕ) (st : HSt (R + D + 1)),
    k + e.depth ≤ D → st.Bdd w → e.Fits w (uenv D st) →
    ∃ st', HLe x w (code R D k e) st st' (e.size * nodeCost w) ∧
      st'.env (sc R D k) = e.eval (uenv D st)
  | var r, k, st, hk, hb, hf => by
    refine ⟨_, (HLe.of_runs (HRuns.copy (ur_ne_sc r k) (hb _) (hb _))).mono ?_, by simp [eval, uenv]⟩
    simp [size, unitCost_le_nodeCost]
  | const c, k, st, hk, hb, hf => by
    refine ⟨_, (setK_spec (sc R D k) w c hf le_rfl st (hb _)).mono ?_, by simp [eval]⟩
    simp only [size, nodeCost, one_mul]; nlinarith
  | add a b, k, st, hk, hb, hf => by
    simp only [depth] at hk
    obtain ⟨hfa, hfb, hab⟩ := hf
    obtain ⟨st₁, h₁, e₁⟩ := code_spec hw a k st (by omega) hb hfa
    have u₁ := code_uenv h₁
    have hb₁ := h₁.bounded hw hb
    obtain ⟨st₂, h₂, e₂⟩ := code_spec hw b (k + 1) st₁ (by omega) hb₁ (by rw [u₁]; exact hfb)
    have u₂ := code_uenv h₂
    have k₂ := code_keep (j := k) (by have := one_le_depth b; omega) (by omega) h₂
    have hb₂ := h₂.bounded hw hb₁
    have hadd : st₂.env (sc R D k) + st₂.env (sc R D (k + 1)) < 2 ^ w := by
      rw [k₂, e₁, e₂, u₁]; exact hab
    refine ⟨_, (h₁.seq (h₂.seq (HLe.of_runs (HRuns.add
      (sc_ne (by have := one_le_depth b; omega) (by omega)) hadd)))).mono ?_, ?_⟩
    · simp only [size]; have := unitCost_le_nodeCost w; nlinarith
    · simp [k₂, e₁, e₂, u₁, eval]
  | lt a b, k, st, hk, hb, hf => by
    simp only [depth] at hk
    obtain ⟨hfa, hfb⟩ := hf
    obtain ⟨st₁, h₁, e₁⟩ := code_spec hw a (k + 1) st (by omega) hb hfa
    have u₁ := code_uenv h₁
    have hb₁ := h₁.bounded hw hb
    obtain ⟨st₂, h₂, e₂⟩ := code_spec hw b (k + 2) st₁ (by omega) hb₁ (by rw [u₁]; exact hfb)
    have u₂ := code_uenv h₂
    have k₂ := code_keep (j := k + 1) (by omega) (by omega) h₂
    have hb₂ := h₂.bounded hw hb₁
    refine ⟨_, (h₁.seq (h₂.seq (HLe.of_runs (HRuns.lt (sc_ne (by omega) (by omega))
      (sc_ne (by omega) (by omega)) (sc_ne (by omega) (by omega)) (hb₂ _) (hb₂ _)
      (hb₂ _))))).mono ?_, ?_⟩
    · simp only [size]; have := unitCost_le_nodeCost w; nlinarith
    · simp [k₂, e₁, e₂, u₁, eval]
  | half a, k, st, hk, hb, hf => by
    simp only [depth] at hk
    obtain ⟨st₁, h₁, e₁⟩ := code_spec hw a k st (by omega) hb hf
    have hb₁ := h₁.bounded hw hb
    refine ⟨_, (h₁.seq (HLe.of_runs (HRuns.half (hb₁ _)))).mono ?_, ?_⟩
    · simp only [size]; have := unitCost_le_nodeCost w; nlinarith
    · simp [e₁, eval]
  | odd a, k, st, hk, hb, hf => by
    simp only [depth] at hk
    obtain ⟨st₁, h₁, e₁⟩ := code_spec hw a k st (by omega) hb hf
    have hb₁ := h₁.bounded hw hb
    have h2 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
    have hU : 1 ≤ unitCost w := by unfold unitCost; omega
    by_cases hodd : st₁.env (sc R D k) % 2 = 1
    · have hc : (st₁.view (sc R D k) == some true) = true := by
        simp [HSt.view, hodd]; omega
      have h₂ := setK_spec (x := x) (sc R D k) 1 1 (by norm_num) (by omega) st₁ (hb₁ _)
      refine ⟨_, (h₁.seq (HLe.iteT (c := fun v => v (sc R D k) == some true)
        (q := .clr (sc R D k)) hc h₂)).mono ?_, ?_⟩
      · simp only [size, nodeCost]; nlinarith
      · simp [eval, ← e₁, hodd]
    · have hc : (st₁.view (sc R D k) == some true) = false := by
        simp [HSt.view]; omega
      refine ⟨_, (h₁.seq (HLe.iteF (c := fun v => v (sc R D k) == some true)
        (p := setK (sc R D k) 1) hc (HLe.of_runs (HRuns.clr (hb₁ _))))).mono ?_, ?_⟩
      · simp only [size, nodeCost]; nlinarith
      · simp [eval, ← e₁]; omega

end Ex

end Lax119563Proofs.Reduction
