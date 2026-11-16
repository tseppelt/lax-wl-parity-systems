import Lax119563Proofs.Reduction.XSpec

/-!
# Generators: a stack language with list semantics

`Gn`: generators over a stack of naturals, with a purely functional semantics
`Gn.out x g ρ : List ℕ` (the emitted list):
* `emit e`, `seq g h`, `ite c g h` (`c ≠ 0`), `bind e g` (push the value of `e`);
* `loop lim g`: for `k < L` (`L` the value of `lim`), run `g` with `L, k` pushed;
* `loopX lim g`: the same with `L, k, inBit x k` pushed;
* `len g` (push `|x|`), `log e g` (push `log₂ e`);
* `count g h`: push the length of the output of `g` (run with a `0` pushed) and run `h`.

`Gn.comp R m A d g : Stm (R + 1)` compiles at depth `d` (levels `i < d` in registers `i`); in
counting mode `m = some a` every emission increments register `a` instead; `A` lists the
levels used as counters (read as `0`). `Gn.spec`: the compiled statement is `Good`.
-/

namespace Lax119563Proofs.Reduction

variable {R : ℕ} {x : List Bool} {w : ℕ}

/-! ## Loops with per-iteration costs -/

namespace Stm

lemma good_loopInvT {N : ℕ} {i lim : Fin N} {body : Stm N} {env : Fin N → ℕ}
    (Inv : ℕ → (Fin N → ℕ) → Prop) (g : ℕ → List ℕ) (T : ℕ → ℕ)
    (hL : env lim + 1 < 2 ^ w) (h0 : Inv 0 env)
    (hs : ∀ k < env lim, ∀ e, Inv k e →
      Good x w body (Function.update e i k) (g k) (T k) ∧
        Inv (k + 1) (exec x body (Function.update e i k)).1) :
    Good x w (loop i lim body) env ((List.range (env lim)).flatMap g)
      (∑ k ∈ Finset.range (env lim), (T k + 4 * unitCost w + 1) + 2 * unitCost w + 1) ∧
    Inv (env lim) (runLoop (fun k e => exec x body (Function.update e i k)) (env lim) env).1 := by
  have HI := runLoop_inv (f := fun k e => exec x body (Function.update e i k)) (L := env lim)
    Inv h0 (fun k hk e he => (hs k hk e he).2)
  have H : ∀ k < env lim, Good x w body
      (Function.update (runLoop (fun k e => exec x body (Function.update e i k)) k env).1 i k)
      (g k) (T k) := fun k hk => (hs k hk _ (HI k hk.le)).1
  refine ⟨⟨⟨hL, fun k hk => (H k hk).fits⟩, ?_, ?_⟩, HI _ le_rfl⟩
  · simp only [exec]
    rw [runLoop_out]
    refine List.flatMap_congr fun k hk => ?_
    exact (H k (List.mem_range.mp hk)).out_eq
  · simp only [cost]
    have : ∑ k ∈ Finset.range (env lim), (cost x w body (Function.update
        (runLoop (fun k e => exec x body (Function.update e i k)) k env).1 i k) +
          4 * unitCost w + 1) ≤ ∑ k ∈ Finset.range (env lim), (T k + 4 * unitCost w + 1) :=
      Finset.sum_le_sum fun k hk => by have := (H k (Finset.mem_range.mp hk)).cost_le; omega
    omega

lemma good_loopXInvT {N : ℕ} {i lim xb : Fin N} {body : Stm N} {env : Fin N → ℕ}
    (Inv : ℕ → (Fin N → ℕ) → Prop) (g : ℕ → List ℕ) (T : ℕ → ℕ)
    (hL : env lim + 1 < 2 ^ w) (h0 : Inv 0 env)
    (hs : ∀ k < env lim, ∀ e, Inv k e →
      Good x w body (Function.update (Function.update e i k) xb (inBit x k)) (g k) (T k) ∧
        Inv (k + 1) (exec x body (Function.update (Function.update e i k) xb (inBit x k))).1) :
    Good x w (loopX i lim xb body) env ((List.range (env lim)).flatMap g)
      (unitCost w + (∑ k ∈ Finset.range (env lim), (unitCost w + T k + 4 * unitCost w + 1) +
        2 * unitCost w + 1) + unitCost w * (x.length + 1)) ∧
    Inv (env lim) (runLoop (fun k e => exec x body
      (Function.update (Function.update e i k) xb (inBit x k))) (env lim) env).1 := by
  have HI := runLoop_inv (f := fun k e => exec x body
    (Function.update (Function.update e i k) xb (inBit x k))) (L := env lim)
    Inv h0 (fun k hk e he => (hs k hk e he).2)
  have H : ∀ k < env lim, Good x w body
      (Function.update (Function.update (runLoop (fun k e => exec x body
        (Function.update (Function.update e i k) xb (inBit x k))) k env).1 i k) xb (inBit x k))
      (g k) (T k) := fun k hk => (hs k hk _ (HI k hk.le)).1
  refine ⟨⟨⟨hL, fun k hk => (H k hk).fits⟩, ?_, ?_⟩, HI _ le_rfl⟩
  · simp only [exec]
    rw [runLoop_out]
    refine List.flatMap_congr fun k hk => ?_
    exact (H k (List.mem_range.mp hk)).out_eq
  · simp only [cost]
    have : ∑ k ∈ Finset.range (env lim), (unitCost w + cost x w body
        (Function.update (Function.update (runLoop (fun k e => exec x body
          (Function.update (Function.update e i k) xb (inBit x k))) k env).1 i k) xb
            (inBit x k)) + 4 * unitCost w + 1) ≤
        ∑ k ∈ Finset.range (env lim), (unitCost w + T k + 4 * unitCost w + 1) :=
      Finset.sum_le_sum fun k hk => by have := (H k (Finset.mem_range.mp hk)).cost_le; omega
    omega

end Stm

/-! ## The logarithm routine -/

/-- `L := log₂ L` (using `u, v` and the counter `c`). -/
def logS {N : ℕ} (L u v c : Fin N) : Stm N :=
  .seq (.set u (.var L)) (.seq (.set L (.const 0)) (.seq (.set v (.var u))
    (.loop c u (.seq (.set v (.half (.var v)))
      (.ite (.var v) (.set L (.add (.var L) (.const 1))) .skip)))))

lemma log_step (E j : ℕ) :
    min (j + 1) (Nat.log 2 E) =
      if E / 2 ^ (j + 1) ≠ 0 then min j (Nat.log 2 E) + 1 else min j (Nat.log 2 E) := by
  split_ifs with h
  · have hE : E ≠ 0 := by rintro rfl; simp at h
    have : j + 1 ≤ Nat.log 2 E := (Nat.le_log_iff_pow_le (by norm_num) hE).mpr
      (by by_contra hc; exact h (Nat.div_eq_of_lt (by omega)))
    omega
  · have : Nat.log 2 E ≤ j := by
      by_contra hc
      rcases Nat.eq_zero_or_pos E with hE | hE
      · subst hE; simp at hc
      · have := (Nat.le_log_iff_pow_le (by norm_num) hE.ne').mp (show j + 1 ≤ Nat.log 2 E by omega)
        exact h (Nat.div_pos_iff.mpr ⟨by positivity, this⟩).ne'
    omega

lemma logS_spec {N : ℕ} {L u v c : Fin N} (hLu : L ≠ u) (hLv : L ≠ v) (hLc : L ≠ c)
    (huv : u ≠ v) (huc : u ≠ c) (hvc : v ≠ c) {env : Fin N → ℕ} {B : ℕ}
    (hB : 2 * B ≤ 2 ^ w) (hE : env L < B) :
    Good x w (logS L u v c) env [] (κ w * (env L + 2)) ∧
      (Stm.exec x (logS L u v c) env).1 L = Nat.log 2 (env L) ∧
      ∀ q, q ≠ L → q ≠ u → q ≠ v → q ≠ c → (Stm.exec x (logS L u v c) env).1 q = env q := by
  have K := Xp.κ_ge w
  obtain ⟨E, hEdef⟩ : ∃ E, env L = E := ⟨_, rfl⟩
  rw [hEdef] at hE ⊢
  set env₀ := Function.update (Function.update (Function.update env u E) L 0) v E with he₀
  have e0u : env₀ u = E := by
    rw [he₀, Function.update_of_ne huv, Function.update_of_ne hLu.symm, Function.update_self]
  have hx₀ : (Stm.exec x (Stm.seq (.set u (.var L)) (.seq (.set L (.const 0))
      (.set v (.var u)))) env).1 = env₀ := by
    simp only [exec_seq_fst, exec_set_fst, Ex.eval, he₀]
    rw [Function.update_of_ne hLu.symm, Function.update_self, hEdef]
  have g₀ : Good x w (Stm.seq (.set u (.var L)) (.seq (.set L (.const 0))
      (.set v (.var u)))) env [] (3 * (Ex.nodeCost w + unitCost w)) := by
    refine (Good.seq0 (Good.set ?_) (Good.seq0 (Good.set ?_) (Good.set ?_))).mono
      (by simp [Ex.size]; omega)
    · simp only [Ex.Fits, hEdef]; omega
    · simp only [Ex.Fits]; positivity
    · simp only [Ex.Fits, exec_set_fst, Ex.eval, Function.update_of_ne hLu.symm,
        Function.update_self, hEdef]; omega
  have H := Stm.good_loopInv (x := x) (w := w) (i := c) (lim := u)
    (body := .seq (.set v (.half (.var v)))
      (.ite (.var v) (.set L (.add (.var L) (.const 1))) .skip)) (env := env₀)
    (fun j e => e v = E / 2 ^ j ∧ e L = min j (Nat.log 2 E)) (fun _ => [])
    (6 * Ex.nodeCost w + 2 * unitCost w + 1) (by rw [e0u]; omega)
    ⟨by simp [he₀], by
      rw [he₀, Function.update_of_ne hLv, Function.update_self]; simp⟩ (by
      intro j hj e ⟨h1, h2⟩
      rw [e0u] at hj
      set e' := Function.update e c j with he'
      have e'v : e' v = E / 2 ^ j := by rw [he', Function.update_of_ne hvc, h1]
      have e'L : e' L = min j (Nat.log 2 E) := by rw [he', Function.update_of_ne hLc, h2]
      set e'' := Function.update e' v (e' v / 2) with he''
      have hv'' : e'' v = E / 2 ^ (j + 1) := by
        rw [he'', Function.update_self, e'v, Nat.div_div_eq_div_mul, pow_succ]
      have hL'' : e'' L = min j (Nat.log 2 E) := by rw [he'', Function.update_of_ne hLv, e'L]
      have hdiv : E / 2 ^ j ≤ E := Nat.div_le_self _ _
      have hdiv' : E / 2 ^ (j + 1) ≤ E := Nat.div_le_self _ _
      have hmin := min_le_left j (Nat.log 2 E)
      have g1 : Good x w (Stm.set v (.half (.var v))) e' [] (2 * Ex.nodeCost w + unitCost w) :=
        (Good.set (by simp only [Ex.Fits, e'v]; omega)).of_eq rfl (by simp [Ex.size])
      have hx1 : (Stm.exec x (Stm.set v (.half (.var v))) e').1 = e'' := by
        simp [exec_set_fst, Ex.eval, he'']
      by_cases hp : E / 2 ^ (j + 1) ≠ 0
      · have hc : (Ex.var v : Ex N).eval e'' ≠ 0 := by simpa [Ex.eval, hv''] using hp
        have g2 : Good x w (Stm.ite (.var v) (.set L (.add (.var L) (.const 1))) .skip) e'' []
            (1 * Ex.nodeCost w + 1 + (3 * Ex.nodeCost w + unitCost w)) :=
          Good.iteT (by simp only [Ex.Fits, hv'']; omega) hc
            ((Good.set (by simp only [Ex.Fits, Ex.eval, hL'']; omega)).of_eq rfl
              (by simp [Ex.size]))
        rw [← hx1] at g2
        refine ⟨(Good.seq0 g1 g2).mono (by omega), ?_, ?_⟩
        · have hc' : e'' v ≠ 0 := by rw [hv'']; exact hp
          simp only [exec_seq_fst, hx1]
          simp only [Stm.exec, Ex.eval, hc', ne_eq, not_false_eq_true, ite_true]
          rw [Function.update_of_ne hLv.symm, hv'']
        · have hc' : e'' v ≠ 0 := by rw [hv'']; exact hp
          simp only [exec_seq_fst, hx1]
          simp only [Stm.exec, Ex.eval, hc', ne_eq, not_false_eq_true, ite_true]
          rw [Function.update_self, hL'', log_step, if_pos hp]
      · have hc : (Ex.var v : Ex N).eval e'' = 0 := by simpa [Ex.eval, hv''] using hp
        have g2 : Good x w (Stm.ite (.var v) (.set L (.add (.var L) (.const 1))) .skip) e'' []
            (1 * Ex.nodeCost w + 1 + unitCost w) :=
          Good.iteF (by simp only [Ex.Fits, hv'']; omega) hc Good.skip
        rw [← hx1] at g2
        refine ⟨(Good.seq0 g1 g2).mono (by omega), ?_, ?_⟩
        · have hc' : e'' v = 0 := by rw [hv'']; simpa using hp
          simp only [exec_seq_fst, hx1]
          simp only [Stm.exec, Ex.eval, hc', ne_eq, not_true_eq_false, ite_false]
          omega
        · have hc' : e'' v = 0 := by rw [hv'']; simpa using hp
          simp only [exec_seq_fst, hx1]
          simp only [Stm.exec, Ex.eval, hc', ne_eq, not_true_eq_false, ite_false]
          rw [hL'', log_step, if_neg hp])
  rw [e0u] at H
  have hK1 : E * (6 * Ex.nodeCost w + 2 * unitCost w + 1 + 4 * unitCost w + 1) ≤ E * κ w :=
    Nat.mul_le_mul_left _ (by omega)
  have hrun : (Stm.exec x (logS L u v c) env).1 =
      (Stm.exec x (Stm.loop c u (.seq (.set v (.half (.var v)))
        (.ite (.var v) (.set L (.add (.var L) (.const 1))) .skip))) env₀).1 := by
    rw [← hx₀]; rfl
  have hloopG := H.1.of_eq (out' := []) (by simp) le_rfl
  have G1 : Good x w (Stm.set u (.var L)) env [] (Ex.nodeCost w + unitCost w) :=
    (Good.set (by simp only [Ex.Fits, hEdef]; omega)).of_eq rfl (by simp [Ex.size])
  have G2 : Good x w (Stm.set L (.const 0)) (Stm.exec x (Stm.set u (.var L)) env).1 []
      (Ex.nodeCost w + unitCost w) :=
    (Good.set (by simp only [Ex.Fits]; positivity)).of_eq rfl (by simp [Ex.size])
  have G3 : Good x w (Stm.set v (.var u)) (Stm.exec x (Stm.set L (.const 0))
      (Stm.exec x (Stm.set u (.var L)) env).1).1 [] (Ex.nodeCost w + unitCost w) :=
    (Good.set (by
      simp only [Ex.Fits, exec_set_fst, Ex.eval, Function.update_of_ne hLu.symm,
        Function.update_self, hEdef]; omega)).of_eq rfl (by simp [Ex.size])
  have hx₀' : (Stm.exec x (Stm.set v (.var u)) (Stm.exec x (Stm.set L (.const 0))
      (Stm.exec x (Stm.set u (.var L)) env).1).1).1 = env₀ := hx₀
  rw [← hx₀'] at hloopG
  refine ⟨?_, ?_, ?_⟩
  · exact (Good.seq0 G1 (Good.seq0 G2 (Good.seq0 G3 hloopG))).mono
      (by rw [show κ w * (E + 2) = E * κ w + 2 * κ w by ring]; omega)
  · rw [hrun, Stm.exec_loop_fst, Function.update_of_ne hLc, e0u, H.2.2]
    exact min_eq_right (Nat.log_le_self 2 E)
  · intro q q1 q2 q3 q4
    rw [hrun, Stm.exec_loop_fst, Function.update_of_ne q4]
    have hf := Stm.runLoop_frame (q := q) (f := fun k e => Stm.exec x
      (.seq (.set v (.half (.var v))) (.ite (.var v) (.set L (.add (.var L) (.const 1))) .skip))
        (Function.update e c k)) (fun k e => by
          rw [Stm.exec_frame _ _ q (by simp [Stm.wr, q1, q3]), Function.update_of_ne q4])
    rw [hf, he₀, Function.update_of_ne q3, Function.update_of_ne q1, Function.update_of_ne q2]

/-! ## Generators -/

/-- Generators. -/
inductive Gn where
  | skip
  | emit (e : Xp)
  | seq (g h : Gn)
  | ite (c : Xp) (g h : Gn)
  | bind (e : Xp) (g : Gn)
  | loop (lim : Xp) (g : Gn)
  | loopX (lim : Xp) (g : Gn)
  | len (g : Gn)
  | log (e : Xp) (g : Gn)
  | count (g h : Gn)

namespace Gn

/-- The emitted list. -/
def out (x : List Bool) : Gn → List ℕ → List ℕ
  | skip, _ => []
  | emit e, ρ => [e.eval ρ]
  | seq g h, ρ => g.out x ρ ++ h.out x ρ
  | ite c g h, ρ => if c.eval ρ ≠ 0 then g.out x ρ else h.out x ρ
  | bind e g, ρ => g.out x (ρ ++ [e.eval ρ])
  | loop lim g, ρ => (List.range (lim.eval ρ)).flatMap fun k => g.out x (ρ ++ [lim.eval ρ, k])
  | loopX lim g, ρ => (List.range (lim.eval ρ)).flatMap fun k =>
      g.out x (ρ ++ [lim.eval ρ, k, inBit x k])
  | len g, ρ => g.out x (ρ ++ [x.length])
  | log e g, ρ => g.out x (ρ ++ [Nat.log 2 (e.eval ρ)])
  | count g h, ρ => h.out x (ρ ++ [(g.out x (ρ ++ [0])).length])

/-- The number of registers used from the current depth on. -/
def need : Gn → ℕ
  | skip => 1
  | emit e => e.need
  | seq g h => max g.need h.need
  | ite c g h => max c.need (max g.need h.need)
  | bind e g => max e.need (g.need + 1)
  | loop lim g => max lim.need (max 2 (g.need + 2))
  | loopX lim g => max lim.need (max 3 (g.need + 3))
  | len g => max 1 (g.need + 1)
  | log e g => max e.need (max 4 (g.need + 1))
  | count g h => max 1 (max (g.need + 1) (h.need + 1))

/-- No `loopX` and no `len` (allowed in the body of a `loopX`). -/
def NoX : Gn → Prop
  | seq g h => NoX g ∧ NoX h
  | ite _ g h => NoX g ∧ NoX h
  | bind _ g => NoX g
  | loop _ g => NoX g
  | loopX _ _ => False
  | len _ => False
  | log _ g => NoX g
  | count g h => NoX g ∧ NoX h
  | _ => True

/-- All values stay below `B`. -/
def Fits (x : List Bool) (B : ℕ) : Gn → List ℕ → Prop
  | skip, _ => True
  | emit e, ρ => e.Fits B ρ
  | seq g h, ρ => g.Fits x B ρ ∧ h.Fits x B ρ
  | ite c g h, ρ => c.Fits B ρ ∧ (if c.eval ρ ≠ 0 then g.Fits x B ρ else h.Fits x B ρ)
  | bind e g, ρ => e.Fits B ρ ∧ g.Fits x B (ρ ++ [e.eval ρ])
  | loop lim g, ρ => lim.Fits B ρ ∧ ∀ k < lim.eval ρ, g.Fits x B (ρ ++ [lim.eval ρ, k])
  | loopX lim g, ρ => lim.Fits B ρ ∧
      ∀ k < lim.eval ρ, g.Fits x B (ρ ++ [lim.eval ρ, k, inBit x k])
  | len g, ρ => x.length < B ∧ g.Fits x B (ρ ++ [x.length])
  | log e g, ρ => e.Fits B ρ ∧ g.Fits x B (ρ ++ [Nat.log 2 (e.eval ρ)])
  | count g h, ρ => (g.out x (ρ ++ [0])).length < B ∧ g.Fits x B (ρ ++ [0]) ∧
      h.Fits x B (ρ ++ [(g.out x (ρ ++ [0])).length])

/-- The cost in units of `κ w`. -/
def cost (x : List Bool) : Gn → List ℕ → ℕ
  | skip, _ => 1
  | emit e, ρ => e.cost ρ + 1
  | seq g h, ρ => g.cost x ρ + h.cost x ρ
  | ite c g h, ρ => c.cost ρ + 1 + (if c.eval ρ ≠ 0 then g.cost x ρ else h.cost x ρ)
  | bind e g, ρ => e.cost ρ + g.cost x (ρ ++ [e.eval ρ])
  | loop lim g, ρ => lim.cost ρ + 1 +
      ∑ k ∈ Finset.range (lim.eval ρ), (g.cost x (ρ ++ [lim.eval ρ, k]) + 1)
  | loopX lim g, ρ => lim.cost ρ + 2 + x.length +
      ∑ k ∈ Finset.range (lim.eval ρ), (g.cost x (ρ ++ [lim.eval ρ, k, inBit x k]) + 1)
  | len g, ρ => x.length + 1 + g.cost x (ρ ++ [x.length])
  | log e g, ρ => e.cost ρ + e.eval ρ + 2 + g.cost x (ρ ++ [Nat.log 2 (e.eval ρ)])
  | count g h, ρ => 1 + g.cost x (ρ ++ [0]) + h.cost x (ρ ++ [(g.out x (ρ ++ [0])).length])

/-- The increment of the counter `a`. -/
def incr (R a : ℕ) : Stm (R + 1) := .set (rg R a) (.add (.var (rg R a)) (.const 1))

/-- Compilation at depth `d`, in mode `m` (`none`: emit; `some a`: count in register `a`),
with counter levels `A`. -/
def comp (R : ℕ) : Option ℕ → List ℕ → ℕ → Gn → Stm (R + 1)
  | _, _, _, skip => .skip
  | none, A, d, emit e => .seq (e.comp R d A d) (.emit (.var (rg R d)))
  | some a, _, _, emit _ => incr R a
  | m, A, d, seq g h => .seq (comp R m A d g) (comp R m A d h)
  | m, A, d, ite c g h => .seq (c.comp R d A d) (.ite (.var (rg R d)) (comp R m A d g)
      (comp R m A d h))
  | m, A, d, bind e g => .seq (e.comp R d A d) (comp R m A (d + 1) g)
  | m, A, d, loop lim g => .seq (lim.comp R d A d)
      (.loop (rg R (d + 1)) (rg R d) (comp R m A (d + 2) g))
  | m, A, d, loopX lim g => .seq (lim.comp R d A d)
      (.loopX (rg R (d + 1)) (rg R d) (rg R (d + 2)) (comp R m A (d + 3) g))
  | m, A, d, len g => .seq (.len (rg R d)) (comp R m A (d + 1) g)
  | m, A, d, log e g => .seq (e.comp R d A d)
      (.seq (logS (rg R d) (rg R (d + 1)) (rg R (d + 2)) (rg R (d + 3))) (comp R m A (d + 1) g))
  | m, A, d, count g h => .seq (.set (rg R d) (.const 0))
      (.seq (comp R (some d) (d :: A) (d + 1) g) (comp R m A (d + 1) h))

/-- The registers a compiled generator may write. -/
def Wr (R : ℕ) (m : Option ℕ) (d : ℕ) (q : Fin (R + 1)) : Prop :=
  Above R d q ∨ ∃ a, m = some a ∧ q = rg R a

lemma wr_mono {m : Option ℕ} {d d' : ℕ} (h : d ≤ d') {q : Fin (R + 1)} (hq : Wr R m d' q) :
    Wr R m d q := hq.imp (above_mono h) id

lemma wrIn_comp (g : Gn) : ∀ (m : Option ℕ) (A : List ℕ) (d : ℕ),
    WrIn (Wr R m d) (comp R m A d g) := by
  induction g with
  | skip => intro m A d; exact WrIn.skip
  | emit e =>
    intro m A d
    cases m with
    | none => exact ((Xp.wrIn_comp e d).mono fun _ h => Or.inl h).seq WrIn.emit
    | some a => exact WrIn.set (Or.inr ⟨a, rfl, rfl⟩)
  | seq g h ihg ihh => intro m A d; exact (ihg m A d).seq (ihh m A d)
  | ite c g h ihg ihh =>
    intro m A d
    exact ((Xp.wrIn_comp c d).mono fun _ h => Or.inl h).seq ((ihg m A d).ite (ihh m A d))
  | bind e g ih =>
    intro m A d
    exact ((Xp.wrIn_comp e d).mono fun _ h => Or.inl h).seq
      ((ih m A (d + 1)).mono fun _ => wr_mono (by omega))
  | loop lim g ih =>
    intro m A d
    exact ((Xp.wrIn_comp lim d).mono fun _ h => Or.inl h).seq
      (WrIn.loop (Or.inl (above_rg (by omega))) ((ih m A (d + 2)).mono fun _ => wr_mono (by omega)))
  | loopX lim g ih =>
    intro m A d
    exact ((Xp.wrIn_comp lim d).mono fun _ h => Or.inl h).seq
      (WrIn.loopX (Or.inl (above_rg (by omega))) (Or.inl (above_rg (by omega)))
        ((ih m A (d + 3)).mono fun _ => wr_mono (by omega)))
  | len g ih =>
    intro m A d
    exact (WrIn.len (Or.inl (above_rg le_rfl))).seq ((ih m A (d + 1)).mono fun _ => wr_mono (by omega))
  | log e g ih =>
    intro m A d
    refine ((Xp.wrIn_comp e d).mono fun _ h => Or.inl h).seq (WrIn.seq ?_
      ((ih m A (d + 1)).mono fun _ => wr_mono (by omega)))
    exact (WrIn.set (Or.inl (above_rg (by omega)))).seq ((WrIn.set (Or.inl (above_rg le_rfl))).seq
      ((WrIn.set (Or.inl (above_rg (by omega)))).seq (WrIn.loop (Or.inl (above_rg (by omega)))
        ((WrIn.set (Or.inl (above_rg (by omega)))).seq
          (WrIn.ite (WrIn.set (Or.inl (above_rg le_rfl))) WrIn.skip)))))
  | count g h ihg ihh =>
    intro m A d
    refine (WrIn.set (Or.inl (above_rg le_rfl))).seq (WrIn.seq ?_
      ((ihh m A (d + 1)).mono fun _ => wr_mono (by omega)))
    refine (ihg (some d) (d :: A) (d + 1)).mono fun q hq => ?_
    rcases hq with hq | ⟨a, ha, rfl⟩
    · exact Or.inl (above_mono (by omega) hq)
    · cases ha; exact Or.inl (above_rg le_rfl)

lemma comp_frame (g : Gn) {m : Option ℕ} {A : List ℕ} {d j : ℕ} (hj : j < d) (hjR : j < R)
    (hm : ∀ a, m = some a → a ≠ j) (hmR : ∀ a, m = some a → a < R)
    (env : Fin (R + 1) → ℕ) :
    (Stm.exec x (comp R m A d g) env).1 (rg R j) = env (rg R j) := by
  refine (wrIn_comp g m A d).frame ?_ env
  rintro (h | ⟨a, ha, he⟩)
  · exact not_above hj hjR h
  · exact hm a ha ((rg_inj (hmR a ha) hjR).mp he.symm)

end Gn

end Lax119563Proofs.Reduction
